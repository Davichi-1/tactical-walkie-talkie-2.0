'use strict';
/*
 * Comms-Hub X base server.
 *  - Serves the page (HTTPS, needed for the microphone) and relays WebRTC setup messages.
 *  - Accounts: sign up / sign in with hashed passwords and cookie sessions.
 *  - Counts users for you: open /admin and enter your ADMIN_KEY.
 * Voice itself goes straight between devices.
 *
 * Offline: run it on one computer; everyone joins over the same Wi-Fi.
 * Online : deploy it to a Node host (set NO_TLS=1 when the host already provides HTTPS).
 *
 * Environment variables
 *   PORT        default 3000
 *   NO_TLS=1    plain HTTP, for hosts/reverse proxies that already provide HTTPS
 *   AUTH=off    turn accounts off (open radio, no sign in)
 *   ADMIN_KEY   secret that unlocks /admin (dashboard stays off without it)
 *   DATA_DIR    where users are saved (default ./data). Use a persistent disk when deployed.
 *   TURN_URL / TURN_USER / TURN_PASS   optional relay for strict mobile networks
 */
const http = require('http');
const https = require('https');
const fs = require('fs');
const os = require('os');
const path = require('path');
const crypto = require('crypto');
const util = require('util');
const { WebSocketServer } = require('ws');

const scrypt = util.promisify(crypto.scrypt);
const PORT = parseInt(process.env.PORT, 10) || 3000;
const NO_TLS = process.env.NO_TLS === '1';
const AUTH_ON = process.env.AUTH !== 'off';
const ADMIN_KEY = process.env.ADMIN_KEY || '';
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const DB_FILE = path.join(DATA_DIR, 'db.json');
const MAX_UNITS = 10;
const SESSION_MS = 30 * 864e5;

const ICE = [{ urls: 'stun:stun.l.google.com:19302' }];
if (process.env.TURN_URL) ICE.push({ urls: process.env.TURN_URL, username: process.env.TURN_USER, credential: process.env.TURN_PASS });

const clean = (s, n) => String(s == null ? '' : s).trim().slice(0, n);
const cleanRoom = s => String(s == null ? '' : s).toLowerCase().replace(/[^a-z0-9]/g, '').slice(0, 10);
const clampCh = n => Math.min(10, Math.max(1, parseInt(n, 10) || 1));
const randomId = () => Math.random().toString(36).slice(2, 10);
const sha = s => crypto.createHash('sha256').update(s).digest('hex');

/* ====================== database (JSON file) ======================
   Fine for thousands of users. Move to Postgres/SQLite when you outgrow it. */
let db = { users: [], sessions: {}, stats: { peakOnline: 0, peakAt: null } };
let saveTimer = null;

function loadDb() {
    try { db = Object.assign(db, JSON.parse(fs.readFileSync(DB_FILE, 'utf8'))); } catch {}
    purgeSessions();
}
function flushDb() {
    clearTimeout(saveTimer);
    try {
        fs.mkdirSync(DATA_DIR, { recursive: true });
        fs.writeFileSync(DB_FILE + '.tmp', JSON.stringify(db));
        fs.renameSync(DB_FILE + '.tmp', DB_FILE);
    } catch (e) { console.error('Could not save users:', e.message); }
}
const saveDb = () => { clearTimeout(saveTimer); saveTimer = setTimeout(flushDb, 300); };
function purgeSessions() {
    const now = Date.now();
    Object.keys(db.sessions).forEach(k => { if (db.sessions[k].exp < now) delete db.sessions[k]; });
}

/* ====================== accounts ====================== */
async function hashPw(pw) {
    const salt = crypto.randomBytes(16).toString('hex');
    return { salt, hash: (await scrypt(pw, salt, 64)).toString('hex') };
}
async function checkPw(pw, u) {
    const h = await scrypt(pw, u.salt, 64);
    const b = Buffer.from(u.hash, 'hex');
    return h.length === b.length && crypto.timingSafeEqual(h, b);
}
const pubUser = u => ({ email: u.email, callsign: u.callsign, plan: u.plan });

function parseCookies(header) {
    const out = {};
    String(header || '').split(';').forEach(p => {
        const i = p.indexOf('=');
        if (i > 0) { try { out[p.slice(0, i).trim()] = decodeURIComponent(p.slice(i + 1).trim()); } catch {} }
    });
    return out;
}
function userFromReq(req) {
    const t = parseCookies(req.headers.cookie).wt_session;
    if (!t) return null;
    const s = db.sessions[sha(t)];
    if (!s || s.exp < Date.now()) return null;
    return db.users.find(u => u.id === s.uid) || null;
}
function newSession(uid) {
    const token = crypto.randomBytes(32).toString('hex');
    db.sessions[sha(token)] = { uid, exp: Date.now() + SESSION_MS };    // only the hash is stored
    return token;
}
function setCookie(res, req, token, maxAgeSec) {
    const secure = req.socket.encrypted || req.headers['x-forwarded-proto'] === 'https';
    res.setHeader('Set-Cookie', `wt_session=${token}; Path=/; HttpOnly; SameSite=Lax; Max-Age=${maxAgeSec}${secure ? '; Secure' : ''}`);
}
const clientIp = req => (NO_TLS && String(req.headers['x-forwarded-for'] || '').split(',')[0].trim()) || req.socket.remoteAddress || '?';

// failed-attempt limiter (brute-force protection)
const fails = new Map();
const locked = (key, max) => { const h = fails.get(key); return !!h && h.reset > Date.now() && h.n >= max; };
const addFail = (key, windowMs) => {
    const now = Date.now();
    let h = fails.get(key);
    if (!h || h.reset < now) h = { n: 0, reset: now + windowMs };
    h.n++; fails.set(key, h);
};

/* ====================== live counts ====================== */
const rooms = new Map();                 // room -> Map(id -> client)
const online = new Map();                // account id (or socket id) -> open sockets

function stats() {
    const now = Date.now();
    const perDay = {};
    for (let i = 13; i >= 0; i--) perDay[new Date(now - i * 864e5).toISOString().slice(0, 10)] = 0;
    db.users.forEach(u => { const k = new Date(u.createdAt).toISOString().slice(0, 10); if (k in perDay) perDay[k]++; });
    const today = new Date(now).toISOString().slice(0, 10);
    return {
        totalUsers: db.users.length,
        newToday: perDay[today] || 0,
        new7d: db.users.filter(u => now - u.createdAt < 7 * 864e5).length,
        active7d: db.users.filter(u => now - (u.lastSeen || 0) < 7 * 864e5).length,
        onlineNow: online.size,
        activeRooms: rooms.size,
        peakOnline: db.stats.peakOnline, peakAt: db.stats.peakAt,
        signupsPerDay: perDay,
        recent: db.users.slice(-50).reverse().map(u => ({ email: u.email, callsign: u.callsign, plan: u.plan, createdAt: u.createdAt, lastSeen: u.lastSeen }))
    };
}

/* ====================== HTTP ====================== */
function json(res, code, obj) {
    res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify(obj));
}
function readJson(req) {
    return new Promise(resolve => {
        let size = 0; const chunks = [];
        req.on('data', c => { size += c.length; if (size > 10240) { req.destroy(); resolve(null); } else chunks.push(c); });
        req.on('end', () => { try { resolve(JSON.parse(Buffer.concat(chunks).toString('utf8'))); } catch { resolve(null); } });
        req.on('error', () => resolve(null));
    });
}
function sendFile(res, name) {
    fs.readFile(path.join(__dirname, name), (err, data) => {
        if (err) { res.writeHead(500); return res.end(`${name} not found next to server.js`); }
        res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' });
        res.end(data);
    });
}

async function api(req, res, url) {
    const ip = clientIp(req);
    const post = req.method === 'POST';

    if (url === '/api/config' && req.method === 'GET') return json(res, 200, { auth: AUTH_ON });

    if (url === '/api/me' && req.method === 'GET') {
        const u = userFromReq(req);
        return u ? json(res, 200, { user: pubUser(u) }) : json(res, 401, { error: 'Not signed in' });
    }

    if (url === '/api/logout' && post) {
        const t = parseCookies(req.headers.cookie).wt_session;
        if (t) { delete db.sessions[sha(t)]; saveDb(); }
        setCookie(res, req, '', 0);
        return json(res, 200, { ok: true });
    }

    if (post && (url === '/api/signup' || url === '/api/login')) {
        if (!AUTH_ON) return json(res, 400, { error: 'Accounts are turned off on this server.' });
        if (!String(req.headers['content-type'] || '').startsWith('application/json')) return json(res, 415, { error: 'Bad request' });
        const body = await readJson(req);
        if (!body) return json(res, 400, { error: 'Bad request' });
        const email = clean(body.email, 254).toLowerCase();
        const pw = String(body.password == null ? '' : body.password);

        if (url === '/api/signup') {
            if (locked('s:' + ip, 30)) return json(res, 429, { error: 'Too many sign-ups from this network. Try again later.' });
            if (!/^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(email)) return json(res, 400, { error: 'Enter a valid email address.' });
            if (pw.length < 8 || pw.length > 128) return json(res, 400, { error: 'Password must be 8 to 128 characters.' });
            if (db.users.some(u => u.email === email)) return json(res, 409, { error: 'That email is already registered. Sign in instead.' });
            addFail('s:' + ip, 3600e3);
            const { salt, hash } = await hashPw(pw);
            if (db.users.some(u => u.email === email)) return json(res, 409, { error: 'That email is already registered. Sign in instead.' });
            const now = Date.now();
            const user = {
                id: crypto.randomBytes(8).toString('hex'), email,
                callsign: clean(body.callsign, 12) || email.split('@')[0].slice(0, 12),
                salt, hash, plan: 'free', createdAt: now, lastLogin: now, lastSeen: now
            };
            db.users.push(user);
            setCookie(res, req, newSession(user.id), SESSION_MS / 1000);
            saveDb();
            return json(res, 200, { user: pubUser(user) });
        }

        // login
        if (locked('e:' + email, 8) || locked('i:' + ip, 80)) return json(res, 429, { error: 'Too many attempts. Try again in a few minutes.' });
        const u = db.users.find(x => x.email === email);
        const ok = pw.length <= 128 && (u ? await checkPw(pw, u) : (await scrypt(pw, 'x'.repeat(32), 64), false));
        if (!ok) {
            addFail('e:' + email, 15 * 60e3); addFail('i:' + ip, 15 * 60e3);
            return json(res, 401, { error: 'Wrong email or password.' });
        }
        u.lastLogin = u.lastSeen = Date.now();
        setCookie(res, req, newSession(u.id), SESSION_MS / 1000);
        saveDb();
        return json(res, 200, { user: pubUser(u) });
    }

    if (url === '/api/admin/stats' && req.method === 'GET') {
        if (!ADMIN_KEY) return json(res, 503, { error: 'Dashboard is off. Set ADMIN_KEY on the server.' });
        if (locked('a:' + ip, 10)) return json(res, 429, { error: 'Too many wrong keys. Try again later.' });
        const given = String(req.headers['x-admin-key'] || '');
        if (!crypto.timingSafeEqual(Buffer.from(sha(given)), Buffer.from(sha(ADMIN_KEY)))) {
            addFail('a:' + ip, 15 * 60e3);
            return json(res, 401, { error: 'Wrong admin key.' });
        }
        return json(res, 200, stats());
    }

    json(res, 404, { error: 'Not found' });
}

function handler(req, res) {
    res.setHeader('X-Content-Type-Options', 'nosniff');
    res.setHeader('X-Frame-Options', 'DENY');
    res.setHeader('Referrer-Policy', 'no-referrer');
    const url = req.url.split('?')[0];
    if (url.startsWith('/api/')) return api(req, res, url).catch(err => { console.error(err); json(res, 500, { error: 'Server error' }); });
    if (url === '/' || url === '/index.html') return sendFile(res, 'index.html');
    if (url === '/admin') return sendFile(res, 'admin.html');
    if (url === '/healthz') { res.writeHead(200); return res.end('ok'); }
    res.writeHead(404); res.end('Not found');
}

/* ====================== TLS (self-signed, for offline use) ====================== */
function lanIps() {
    const rank = ip => (ip.startsWith('192.168.') ? 0 : ip.startsWith('10.') ? 1 : ip.startsWith('172.') ? 2 : 3);
    return Object.values(os.networkInterfaces()).flat()
        .filter(i => i && (i.family === 'IPv4' || i.family === 4) && !i.internal)
        .map(i => i.address)
        .sort((a, b) => rank(a) - rank(b));
}
async function makeTls(ips) {
    const file = path.join(__dirname, '.cert', 'cert.json');
    try {
        const c = JSON.parse(fs.readFileSync(file, 'utf8'));
        if (c.ips.join() === ips.join()) return { key: c.key, cert: c.cert };
    } catch {}
    const selfsigned = require('selfsigned');
    const altNames = [{ type: 2, value: 'localhost' }, { type: 7, ip: '127.0.0.1' }, ...ips.map(ip => ({ type: 7, ip }))];
    const pems = await selfsigned.generate([{ name: 'commonName', value: 'walkie-talkie.local' }], {
        days: 365, keySize: 2048, algorithm: 'sha256',
        extensions: [{ name: 'subjectAltName', altNames }]
    });
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, JSON.stringify({ ips, key: pems.private, cert: pems.cert }));
    return { key: pems.private, cert: pems.cert };
}

/* ====================== rooms (WebSocket) ====================== */
const pub = c => ({ id: c.id, callsign: c.callsign, channel: c.channel, talking: !!c.talking });
const send = (ws, msg) => { if (ws.readyState === 1) ws.send(JSON.stringify(msg)); };
const others = (members, exceptId, msg) => members.forEach(c => { if (c.id !== exceptId) send(c.ws, msg); });

function onConnection(ws, req) {
    let me = null;
    ws.alive = true;
    ws.on('pong', () => { ws.alive = true; });

    ws.on('message', raw => {
        let m;
        try { m = JSON.parse(raw); } catch { return; }
        if (!m || typeof m !== 'object') return;

        if (m.t === 'join' && !me) {
            const user = AUTH_ON ? userFromReq(req) : null;
            if (AUTH_ON && !user) { send(ws, { t: 'auth' }); return ws.close(); }
            const room = cleanRoom(m.room);
            if (room.length < 3) return send(ws, { t: 'error', msg: 'Room ID needs at least 3 letters or numbers' });
            const members = rooms.get(room) || new Map();
            if (members.size >= MAX_UNITS) return send(ws, { t: 'full' });

            me = { id: randomId(), room, ws, callsign: clean(m.callsign, 12) || (user && user.callsign) || 'UNIT', channel: clampCh(m.channel), talking: false };
            me.key = user ? user.id : me.id;
            send(ws, { t: 'joined', id: me.id, ice: ICE, peers: [...members.values()].map(pub) });
            others(members, me.id, { t: 'peer-join', peer: pub(me) });
            members.set(me.id, me);
            rooms.set(room, members);

            online.set(me.key, (online.get(me.key) || 0) + 1);
            if (online.size > db.stats.peakOnline) { db.stats.peakOnline = online.size; db.stats.peakAt = Date.now(); }
            if (user) { user.lastSeen = Date.now(); }
            saveDb();
            return;
        }
        if (!me) return;
        const members = rooms.get(me.room);
        if (!members) return;

        if (m.t === 'signal') {
            const to = members.get(m.to);
            if (to) send(to.ws, { t: 'signal', from: me.id, data: m.data });
        } else if (m.t === 'state') {
            if (m.channel !== undefined) me.channel = clampCh(m.channel);
            me.talking = !!m.talking;
            others(members, me.id, { t: 'state', id: me.id, channel: me.channel, talking: me.talking });
        }
    });

    ws.on('close', () => {
        if (!me) return;
        const left = (online.get(me.key) || 1) - 1;
        if (left > 0) online.set(me.key, left); else online.delete(me.key);
        const members = rooms.get(me.room);
        if (!members) return;
        members.delete(me.id);
        if (!members.size) rooms.delete(me.room);
        else others(members, null, { t: 'peer-leave', id: me.id });
    });
}

/* ====================== start ====================== */
async function main() {
    loadDb();
    const ips = lanIps();
    const server = NO_TLS ? http.createServer(handler) : https.createServer(await makeTls(ips), handler);
    const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 64 * 1024 });
    wss.on('connection', onConnection);

    setInterval(() => wss.clients.forEach(ws => {          // drop dead connections
        if (!ws.alive) return ws.terminate();
        ws.alive = false; ws.ping();
    }), 15000);
    setInterval(() => { purgeSessions(); saveDb(); }, 3600e3);
    ['SIGINT', 'SIGTERM'].forEach(s => process.on(s, () => { flushDb(); process.exit(0); }));

    server.on('error', err => {
        console.error(err.code === 'EADDRINUSE' ? `Port ${PORT} is busy. Close the other program or set PORT=3001.` : err);
        process.exit(1);
    });

    server.listen(PORT, '0.0.0.0', () => {
        const proto = NO_TLS ? 'http' : 'https';
        console.log('\n  COMMS-HUB X BASE IS RUNNING\n');
        console.log(`  Accounts : ${AUTH_ON ? `on (${db.users.length} saved in ${DATA_DIR})` : 'off (open radio)'}`);
        console.log(`  Dashboard: ${ADMIN_KEY ? '/admin (use your ADMIN_KEY)' : 'off. Set ADMIN_KEY to turn it on'}\n`);
        if (NO_TLS) { console.log(`  Listening on port ${PORT}\n`); return; }
        console.log('  Open this address on every device (same Wi-Fi or hotspot):\n');
        (ips.length ? ips : ['localhost']).forEach(ip => console.log(`    ${proto}://${ip}:${PORT}`));
        console.log('\n  First time on each device: tap Advanced, then Proceed. The certificate is self-signed.');
        console.log('  If a phone cannot open it, allow Node.js through the firewall (Private networks).\n');
        try { require('qrcode-terminal').generate(`${proto}://${ips[0] || 'localhost'}:${PORT}`, { small: true }); } catch {}
    });
}

main().catch(err => { console.error(err); process.exit(1); });
