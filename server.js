const { WebSocketServer } = require('ws');
const http = require('http');
const fs = require('fs');
const path = require('path');

const PORT = process.env.PORT || 3000;
const G = 1024;
const SZ = G * G;
const BASE_SZ = 20;
const TICK_HZ = 3;
const SIGHT = 20;
const CHUNK = 16;
const CW = G / CHUNK;

// ═══ UPGRADE CONFIG ═══
const UPGRADES = {
    baseSize: { costs: [50000, 150000, 500000], sizes: [24, 28, 32] },
    baseHp:   { costs: [50000, 200000, 600000], hps: [700, 1000, 1500] },
    maxEnergy:{ costs: [25000, 100000, 300000], vals: [40, 50, 65] },
    energyRegen:{ costs: [25000, 80000, 250000], rates: [6, 4, 3] },
};
const OUTPOST_COST = 500000;
const OUTPOST_SZ = 10;
const OUTPOST_HP = 200;
const NEW_BASE_COST = 200000;

const DEF_MAX_ENERGY = 30;
const DEF_ENERGY_RATE = 8;
const DEF_BASE_HP = 500;
const HP_REGEN_RATE = 10;
const CELL_DEATH_MONEY = 1;

const PATTERNS = {
    glNE:[[0,0],[1,0],[2,0],[2,-1],[1,-2]],glSW:[[0,0],[-1,0],[-2,0],[-2,1],[-1,2]],
    glSE:[[0,0],[1,0],[2,0],[2,1],[1,2]],glNW:[[0,0],[-1,0],[-2,0],[-2,-1],[-1,-2]],
    lwss:[[0,0],[1,0],[2,0],[3,0],[4,1],[4,3],[0,1],[0,3],[1,3]],
    rpent:[[1,0],[2,0],[0,1],[1,1],[1,2]],acorn:[[1,0],[3,1],[0,2],[1,2],[4,2],[5,2],[6,2]],
};
const patKeys = Object.keys(PATTERNS);

const gridOwner = new Uint16Array(SZ);
const trailOwner = new Uint16Array(SZ);
const ncount = new Uint8Array(SZ);
let activeSet = new Set();

const W = v => ((v % G) + G) % G;
const I = (x, y) => y * G + x;
const XY = i => [i % G, (i / G) | 0];

const allStructures = [];  // bases + outposts (all have same shape)
const saved = {};
const conns = new Map();
const chatHist = [];
const trailCounts = {};
const activeCounts = {};
let gen = 0, nextId = 1;
let pendingNewTrails = [];

function setCell(x, y, oid) {
    const i = I(x, y);
    const old = gridOwner[i];
    if (old === oid + 1) return;
    if (old > 0) activeCounts[old - 1] = Math.max(0, (activeCounts[old - 1] || 0) - 1);
    if (oid >= 0) { gridOwner[i] = oid + 1; activeSet.add(i); activeCounts[oid] = (activeCounts[oid] || 0) + 1; }
    else { gridOwner[i] = 0; activeSet.delete(i); }
}

function setTrail(i, oid) {
    const old = trailOwner[i];
    if (old > 0 && old !== oid + 1) trailCounts[old - 1] = Math.max(0, (trailCounts[old - 1] || 0) - 1);
    if (old !== oid + 1) { trailOwner[i] = oid + 1; trailCounts[oid] = (trailCounts[oid] || 0) + 1; pendingNewTrails.push(i); }
}

// ═══ STRUCTURE HELPERS ═══
// A "structure" is a base or outpost: { x, y, sz, ownerId, alive, hp, maxHp, isOutpost, ... }
function inStruct(x, y, s) { return s.alive && ((x - s.x + G) % G) < s.sz && ((y - s.y + G) % G) < s.sz; }
function findStruct(x, y) { for (const s of allStructures) if (inStruct(x, y, s)) return s; return null; }

function tdist(x1, y1, x2, y2) {
    let dx = Math.abs(x1 - x2), dy = Math.abs(y1 - y2);
    if (dx > G / 2) dx = G - dx; if (dy > G / 2) dy = G - dy;
    return Math.sqrt(dx * dx + dy * dy);
}

function findPos(sz) {
    sz = sz || BASE_SZ;
    let bx = 0, by = 0, bd = -1;
    for (let i = 0; i < 150; i++) {
        const x = (Math.random() * G) | 0, y = (Math.random() * G) | 0;
        let md = Infinity;
        for (const s of allStructures) if (s.alive)
            md = Math.min(md, tdist(x + sz / 2, y + sz / 2, s.x + s.sz / 2, s.y + s.sz / 2));
        if (md > bd) { bd = md; bx = x; by = y; }
    }
    return { x: bx, y: by };
}

function clearArea(bx, by, sz) {
    for (let dy = 0; dy < sz; dy++) for (let dx = 0; dx < sz; dx++) {
        const x = W(bx + dx), y = W(by + dy), i = I(x, y);
        if (gridOwner[i] > 0) setCell(x, y, -1);
        if (trailOwner[i] > 0) { trailCounts[trailOwner[i] - 1] = Math.max(0, (trailCounts[trailOwner[i] - 1] || 0) - 1); trailOwner[i] = 0; }
    }
}

// Get player's effective stats based on upgrades
function getStats(base) {
    const lvl = base.upgrades || {};
    const bsLvl = lvl.baseSize || 0;
    const hpLvl = lvl.baseHp || 0;
    const enLvl = lvl.maxEnergy || 0;
    const erLvl = lvl.energyRegen || 0;
    return {
        baseSz: bsLvl > 0 ? UPGRADES.baseSize.sizes[bsLvl - 1] : BASE_SZ,
        maxHp: hpLvl > 0 ? UPGRADES.baseHp.hps[hpLvl - 1] : DEF_BASE_HP,
        maxEnergy: enLvl > 0 ? UPGRADES.maxEnergy.vals[enLvl - 1] : DEF_MAX_ENERGY,
        energyRate: erLvl > 0 ? UPGRADES.energyRegen.rates[erLvl - 1] : DEF_ENERGY_RATE,
    };
}

// ═══ VISIBILITY ═══
function cellInSight(pid, cx, cy) {
    for (const s of allStructures) if (s.ownerId === pid && s.alive && inStruct(cx, cy, s)) return true;
    const oid = pid + 1;
    for (let dy = -SIGHT; dy <= SIGHT; dy++) for (let dx = -SIGHT; dx <= SIGHT; dx++) {
        if (dx * dx + dy * dy > SIGHT * SIGHT) continue;
        if (gridOwner[I(W(cx + dx), W(cy + dy))] === oid) return true;
    }
    for (const s of allStructures) if (s.alive && s.discoveredBy && s.discoveredBy.has(pid) && inStruct(cx, cy, s)) return true;
    return false;
}

function fogChunks(pid) {
    const vis = new Set();
    const oid = pid + 1, cr = Math.ceil(SIGHT / CHUNK) + 1;
    for (const s of allStructures) {
        if (!s.alive) continue;
        if (s.ownerId !== pid && !(s.discoveredBy && s.discoveredBy.has(pid))) continue;
        for (let y = s.y; y < s.y + s.sz + CHUNK; y += CHUNK)
            for (let x = s.x; x < s.x + s.sz + CHUNK; x += CHUNK)
                vis.add(((W(y) / CHUNK | 0) % CW) * CW + ((W(x) / CHUNK | 0) % CW));
    }
    for (const i of activeSet) {
        if (gridOwner[i] !== oid) continue;
        const [x, y] = XY(i);
        const ccx = (x / CHUNK | 0) % CW, ccy = (y / CHUNK | 0) % CW;
        for (let dy = -cr; dy <= cr; dy++) for (let dx = -cr; dx <= cr; dx++)
            vis.add(((ccy + dy + CW) % CW) * CW + ((ccx + dx + CW) % CW));
    }
    return vis;
}

// ═══ TICK ═══
function tick() {
    pendingNewTrails = [];
    const touched = [];

    const stale = [];
    for (const ci of activeSet) if (gridOwner[ci] === 0) stale.push(ci);
    for (const ci of stale) activeSet.delete(ci);

    for (const ci of activeSet) {
        const [x, y] = XY(ci);
        const s = findStruct(x, y);
        if (s && s.ownerId === gridOwner[ci] - 1 && s.paused) continue;
        for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
            if (!dx && !dy) continue;
            const ni = I(W(x + dx), W(y + dy));
            if (ncount[ni] === 0) touched.push(ni);
            ncount[ni]++;
        }
    }

    for (const ci of activeSet) {
        if (gridOwner[ci] === 0) continue;
        const [x, y] = XY(ci);
        const s = findStruct(x, y);
        if (s && s.ownerId === gridOwner[ci] - 1 && s.paused) continue;
        if (ncount[ci] === 0) touched.push(ci);
    }

    const births = [], deaths = [];
    for (let ti = 0; ti < touched.length; ti++) {
        const ci = touched[ti];
        const n = ncount[ci];
        const wasAlive = gridOwner[ci] > 0;
        const willLive = n === 3 || (n === 2 && wasAlive);

        if (willLive && !wasAlive) {
            const [x, y] = XY(ci);
            const oc = {};
            for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
                if (!dx && !dy) continue;
                const o = gridOwner[I(W(x + dx), W(y + dy))];
                if (o > 0) oc[o] = (oc[o] || 0) + 1;
            }
            let mx = 0, mo = 0; for (const o in oc) if (oc[o] > mx) { mx = oc[o]; mo = +o; }
            const owner = mo - 1;

            const hitS = findStruct(x, y);
            if (hitS && hitS.ownerId !== owner) {
                if (hitS.discoveredBy && !hitS.discoveredBy.has(owner)) {
                    hitS.discoveredBy.add(owner);
                    for (const [ws, cn] of conns) if (cn.pid === owner)
                        safeSend(ws, { type: 'discovered', baseName: hitS.name || 'Outpost', baseColor: hitS.color });
                }
                hitS.hp = Math.max(0, (hitS.hp) - 1);
                const ab = saved[Object.keys(saved).find(k => saved[k].ownerId === owner)];
                if (ab) ab.money = (ab.money || 0) + 1;
                continue;
            }
            if (hitS && hitS.ownerId === owner && hitS.paused) continue;
            births.push(ci, owner);
        } else if (!willLive && wasAlive) {
            const [x, y] = XY(ci);
            const s = findStruct(x, y);
            if (s && s.ownerId === gridOwner[ci] - 1 && s.paused) continue;
            deaths.push(ci, gridOwner[ci] - 1);
        }
    }

    for (let i = 0; i < deaths.length; i += 2) {
        const ci = deaths[i], oid = deaths[i + 1];
        setTrail(ci, oid);
        gridOwner[ci] = 0; activeSet.delete(ci);
        activeCounts[oid] = Math.max(0, (activeCounts[oid] || 0) - 1);
        const b = Object.values(saved).find(bb => bb.ownerId === oid);
        if (b) b.money = (b.money || 0) + CELL_DEATH_MONEY;
    }

    for (let i = 0; i < births.length; i += 2) {
        gridOwner[births[i]] = births[i + 1] + 1;
        activeSet.add(births[i]);
        activeCounts[births[i + 1]] = (activeCounts[births[i + 1]] || 0) + 1;
    }

    for (let i = 0; i < touched.length; i++) ncount[touched[i]] = 0;
    gen++;

    // Energy & HP regen per player
    for (const name in saved) {
        const b = saved[name];
        if (!b.alive) continue;
        const stats = getStats(b);
        if (gen % stats.energyRate === 0 && b.energy < stats.maxEnergy) b.energy++;
        if (gen % HP_REGEN_RATE === 0 && b.hp < stats.maxHp) b.hp++;
    }
    // Outpost HP regen
    for (const s of allStructures) {
        if (!s.alive || !s.isOutpost) continue;
        if (gen % HP_REGEN_RATE === 0 && s.hp < s.maxHp) s.hp++;
    }

    checkDestruction();
    broadcast();
}

// ═══ DESTRUCTION ═══
function checkDestruction() {
    for (const s of allStructures) {
        if (!s.alive || s.hp > 0) continue;
        s.alive = false;
        const att = {};
        for (let d = 0; d < s.sz; d++) {
            const outside = [I(W(s.x+d),W(s.y-1)),I(W(s.x+d),W(s.y+s.sz)),I(W(s.x-1),W(s.y+d)),I(W(s.x+s.sz),W(s.y+d))];
            for (const ei of outside) { const o = gridOwner[ei]; if (o > 0 && o-1 !== s.ownerId) att[o-1] = (att[o-1]||0)+1; }
        }
        let top = -1, topN = 0; for (const a in att) if (att[a] > topN) { topN = att[a]; top = +a; }
        if (top >= 0) { const ab = Object.values(saved).find(bb => bb.ownerId === top); if (ab) ab.basesDestroyed = (ab.basesDestroyed||0) + 1; }
        const label = s.isOutpost ? `${s.name}'s outpost` : s.name;
        for (const [ws] of conns) safeSend(ws, { type: 'baseDestroyed', baseName: label });
        console.log(`[DESTROYED] ${label}`);
    }
}

// ═══ PINGS ═══
function getPings(pid) {
    const oid = pid + 1, out = [];
    for (const ci of activeSet) {
        if (gridOwner[ci] !== oid || out.length >= 15) continue;
        const [mx, my] = XY(ci);
        for (let dy = -SIGHT; dy <= SIGHT && out.length < 15; dy++) for (let dx = -SIGHT; dx <= SIGHT; dx++) {
            if (dx * dx + dy * dy > SIGHT * SIGHT) continue;
            const ni = I(W(mx + dx), W(my + dy));
            const no = gridOwner[ni];
            if (no > 0 && no !== oid) { out.push({ x: W(mx + dx), y: W(my + dy), owner: no - 1 }); break; }
        }
    }
    return out;
}

// ═══ BINARY PACK ═══
function packCells(flat, type) {
    const count = (flat.length / 3) | 0;
    const buf = Buffer.alloc(9 + count * 6);
    buf.writeUInt8(type, 0); buf.writeUInt32LE(gen, 1); buf.writeUInt32LE(count, 5);
    for (let i = 0; i < count; i++) {
        buf.writeUInt16LE(flat[i * 3], 9 + i * 6);
        buf.writeUInt16LE(flat[i * 3 + 1], 9 + i * 6 + 2);
        buf.writeUInt16LE(flat[i * 3 + 2], 9 + i * 6 + 4);
    }
    return buf;
}

// ═══ BROADCAST ═══
function broadcast() {
    const disc = {};
    for (const s of allStructures) if (s.discoveredBy) for (const p of s.discoveredBy) if (p !== s.ownerId) disc[p] = (disc[p] || 0) + 1;
    const colors = {}, names = {};
    for (const s of allStructures) { colors[s.ownerId] = s.color; if (s.name) names[s.ownerId] = s.name; }
    const seenIds = new Set(); const ids = [];
    for (const s of allStructures) if (!seenIds.has(s.ownerId)) { seenIds.add(s.ownerId); ids.push(s.ownerId); }

    for (const [ws, cn] of conns) {
        if (ws.readyState !== 1) continue;
        const pid = cn.pid, vp = cn.viewport;
        const fog = fogChunks(pid);

        const visCells = [];
        for (const ci of activeSet) {
            const [x, y] = XY(ci);
            if (!fog.has((((y / CHUNK | 0) % CW) * CW) + ((x / CHUNK | 0) % CW))) continue;
            if (vp) { let dx = x - vp.cx, dy = y - vp.cy; if (dx > G/2) dx -= G; if (dx < -G/2) dx += G; if (dy > G/2) dy -= G; if (dy < -G/2) dy += G; if (Math.abs(dx) > vp.hw || Math.abs(dy) > vp.hh) continue; }
            visCells.push(x, y, gridOwner[ci] - 1);
        }

        const visTrails = [];
        for (const ci of pendingNewTrails) {
            const [x, y] = XY(ci);
            if (!fog.has((((y / CHUNK | 0) % CW) * CW) + ((x / CHUNK | 0) % CW))) continue;
            if (vp) { let dx = x - vp.cx, dy = y - vp.cy; if (dx > G/2) dx -= G; if (dx < -G/2) dx += G; if (dy > G/2) dy -= G; if (dy < -G/2) dy += G; if (Math.abs(dx) > vp.hw || Math.abs(dy) > vp.hh) continue; }
            visTrails.push(x, y, trailOwner[ci] - 1);
        }

        trySendBuf(ws, packCells(visCells, 1));
        if (visTrails.length) trySendBuf(ws, packCells(visTrails, 2));

        const visStructs = allStructures
            .filter(s => s.alive && (s.ownerId === pid || (s.discoveredBy && s.discoveredBy.has(pid))))
            .map(s => ({ x: s.x, y: s.y, sz: s.sz, ownerId: s.ownerId, paused: s.paused ? 1 : 0, hp: s.hp, maxHp: s.maxHp, isOutpost: s.isOutpost ? 1 : 0 }));

        const myBase = Object.values(saved).find(b => b.ownerId === pid);
        const stats = myBase ? getStats(myBase) : { maxEnergy: DEF_MAX_ENERGY, maxHp: DEF_BASE_HP, energyRate: DEF_ENERGY_RATE, baseSz: BASE_SZ };

        safeSend(ws, {
            type: 'update', generation: gen, bases: visStructs, pings: getPings(pid),
            scores: {
                active: ids.map(id => activeCounts[id] || 0),
                total: ids.map(id => (activeCounts[id] || 0) + (trailCounts[id] || 0)),
                discovery: ids.map(id => disc[id] || 0),
                destroyed: ids.map(id => { const b = Object.values(saved).find(bb => bb.ownerId === id); return b ? b.basesDestroyed || 0 : 0; }),
                ids,
            },
            myBasePaused: myBase ? (myBase.paused ? 1 : 0) : 1,
            myEnergy: myBase ? myBase.energy : 0,
            myMaxEnergy: stats.maxEnergy,
            myMoney: myBase ? (myBase.money || 0) : 0,
            myHp: myBase ? myBase.hp : 0,
            myMaxHp: stats.maxHp,
            myUpgrades: myBase ? (myBase.upgrades || {}) : {},
            online: conns.size,
            colors, names,
            upgradeCosts: UPGRADES,
            outpostCost: OUTPOST_COST,
            newBaseCost: NEW_BASE_COST,
        });
    }
}

function safeSend(ws, o) { try { if (ws.readyState === 1) ws.send(JSON.stringify(o)); } catch (e) {} }
function trySendBuf(ws, b) { try { if (ws.readyState === 1) ws.send(b); } catch (e) {} }

// ═══════════════════════════════════════
// RADIO SYSTEM — in-memory, no DB needed
// ═══════════════════════════════════════
const SUNO_KEY = process.env.SUNO_API_KEY || '';
const radioQueue = [];       // [{title, audio_url, image_url, duration}]
const radioPlayed = [];      // last 5 played
let radioState = { current: null, startedAt: null };
let radioAdvTimer = null;
const radioPending = new Map(); // taskId → requesterName
const radioQueued = new Set();  // taskId dedup

function radioSchedule(dur) {
    if (radioAdvTimer) clearTimeout(radioAdvTimer);
    if (!dur || dur <= 0) return;
    const elapsed = (Date.now() - radioState.startedAt) / 1000;
    const rem = Math.max(1000, (dur - elapsed + 2) * 1000);
    radioAdvTimer = setTimeout(radioNext, rem);
}

function radioNext() {
    if (radioAdvTimer) { clearTimeout(radioAdvTimer); radioAdvTimer = null; }
    if (radioState.current) radioPlayed.unshift(radioState.current);
    if (radioPlayed.length > 5) radioPlayed.pop();

    if (radioQueue.length > 0) {
        radioState = { current: radioQueue.shift(), startedAt: Date.now() };
    } else if (radioState.current) {
        radioState.startedAt = Date.now(); // repeat
    } else {
        radioState = { current: null, startedAt: null };
    }
    radioBroadcast();
    if (radioState.current && radioState.current.duration > 0) radioSchedule(radioState.current.duration);
}

function radioBroadcast() {
    for (const [ws] of conns) safeSend(ws, { type: 'radio', state: radioState, queue: radioQueue.map(s => s.title) });
}

function parseBody(req) {
    return new Promise((resolve) => {
        let body = '';
        req.on('data', c => { body += c; if (body.length > 1e6) req.destroy(); });
        req.on('end', () => { try { resolve(JSON.parse(body)); } catch(e) { resolve(null); } });
    });
}

// ═══ HTTP ═══
const server = http.createServer(async (req, res) => {
    // CORS headers for all
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET,POST,OPTIONS');
    res.setHeader('Access-Control-Allow-Headers', 'Content-Type');
    if (req.method === 'OPTIONS') { res.writeHead(200); res.end(); return; }

    if ((req.url === '/' || req.url === '/index.html') && req.method === 'GET') {
        res.writeHead(200, { 'Content-Type': 'text/html' });
        res.end(fs.readFileSync(path.join(__dirname, 'index.html')));
        return;
    }

    if (req.url === '/api/playback' && req.method === 'GET') {
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ state: radioState, queue: radioQueue.map(s => s.title) }));
        return;
    }

    if (req.url === '/api/generate' && req.method === 'POST') {
        if (!SUNO_KEY) { res.writeHead(500, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ error: 'No API key configured' })); return; }
        const body = await parseBody(req);
        if (!body || !body.prompt) { res.writeHead(400, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ error: 'prompt required' })); return; }
        try {
            const proto = req.headers['x-forwarded-proto'] || 'http';
            const host = req.headers['x-forwarded-host'] || req.headers.host;
            const cbUrl = `${proto}://${host}/api/suno-callback`;
            const r = await fetch('https://apibox.erweima.ai/api/v1/generate', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': `Bearer ${SUNO_KEY}` },
                body: JSON.stringify({
                    prompt: body.prompt, style: body.style || '', title: body.title || 'Untitled',
                    customMode: false, instrumental: false, model: 'V3_5', callBackUrl: cbUrl
                })
            });
            const data = await r.json();
            if (data.code === 200 && data.data?.taskId) {
                radioPending.set(data.data.taskId, body.requester || 'Someone');
                setTimeout(() => radioPending.delete(data.data.taskId), 600000);
                res.writeHead(200, { 'Content-Type': 'application/json' });
                res.end(JSON.stringify({ taskId: data.data.taskId }));
                // Notify all clients
                for (const [ws] of conns) safeSend(ws, { type: 'radioGenerating', title: body.title || body.prompt.substring(0, 40) });
            } else {
                res.writeHead(400, { 'Content-Type': 'application/json' });
                res.end(JSON.stringify({ error: data.msg || 'Generation failed' }));
            }
        } catch (e) { res.writeHead(500, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ error: 'Failed' })); }
        return;
    }

    if (req.url === '/api/suno-callback' && req.method === 'POST') {
        const body = await parseBody(req);
        try {
            const taskId = body?.data?.task_id;
            if (taskId && radioQueued.has(taskId)) { res.writeHead(200); res.end('ok'); return; }
            // Extract songs
            const dataPayload = body?.data?.data;
            if (dataPayload) {
                const list = Array.isArray(dataPayload) ? dataPayload : [dataPayload];
                for (const item of list) {
                    const audioUrl = item?.audio_url || item?.audioUrl || '';
                    if (audioUrl && audioUrl.startsWith('http')) {
                        const song = {
                            title: item.title || 'Untitled',
                            audio_url: audioUrl,
                            image_url: item.image_url || item.imageUrl || null,
                            duration: Math.round(item.duration || 0),
                            requester: radioPending.get(taskId) || 'Someone',
                        };
                        // Dedup
                        if (!radioQueue.some(s => s.audio_url === audioUrl) &&
                            radioState.current?.audio_url !== audioUrl) {
                            radioQueue.push(song);
                            console.log(`[RADIO] Queued: ${song.title}`);
                            for (const [ws] of conns) safeSend(ws, { type: 'radioQueued', title: song.title });
                            if (!radioState.current) radioNext();
                            else radioBroadcast();
                        } else if (song.duration > 0 && radioState.current && !radioState.current.duration) {
                            radioState.current.duration = song.duration;
                            radioSchedule(song.duration);
                        }
                        if (taskId) { radioQueued.add(taskId); setTimeout(() => radioQueued.delete(taskId), 600000); }
                        break; // just use first song
                    }
                }
            }
            if (taskId) radioPending.delete(taskId);
        } catch (e) { console.error('Radio callback error:', e.message); }
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ ok: true }));
        return;
    }

    res.writeHead(404); res.end();
});

// ═══ WS ═══
const wss = new WebSocketServer({ server });
wss.on('connection', ws => {
    let joined = false, base = null, pid = -1;
    ws.on('message', raw => {
        if (Buffer.isBuffer(raw) && raw[0] !== 123) return;
        let msg; try { msg = JSON.parse(raw.toString()); } catch (e) { return; }

        if (msg.type === 'viewport' && joined) {
            const cn = conns.get(ws); if (cn) cn.viewport = { cx: msg.cx, cy: msg.cy, hw: msg.hw, hh: msg.hh }; return;
        }

        if (!joined && msg.type === 'join') {
            joined = true;
            const name = (msg.name || 'Player').substring(0, 16), color = msg.color || '#4dabf7';
            let wasDestroyed = false;

            if (saved[name] && saved[name].alive) {
                base = saved[name]; base.color = color;
            } else if (saved[name] && !saved[name].alive) {
                wasDestroyed = true;
                const old = saved[name];
                const pos = findPos(BASE_SZ);
                base = { ...old, x: pos.x, y: pos.y, alive: true, paused: true, color,
                    hp: getStats(old).maxHp, energy: getStats(old).maxEnergy,
                    discoveredBy: new Set([old.ownerId]) };
                // Update sz in case of upgrades
                base.sz = getStats(base).baseSz;
                base.maxHp = getStats(base).maxHp;
                allStructures.push(base);
                saved[name] = base;
                clearArea(base.x, base.y, base.sz);
            } else {
                const id = nextId++;
                const pos = findPos(BASE_SZ);
                base = { id, x: pos.x, y: pos.y, sz: BASE_SZ, ownerId: id - 1, name, color,
                    discoveredBy: new Set([id - 1]), paused: true, isBot: false, alive: true,
                    energy: DEF_MAX_ENERGY, hp: DEF_BASE_HP, maxHp: DEF_BASE_HP, money: 0,
                    basesDestroyed: 0, upgrades: {}, isOutpost: false };
                allStructures.push(base);
                saved[name] = base;
                clearArea(base.x, base.y, base.sz);
            }

            pid = base.ownerId;
            conns.set(ws, { pid, base, viewport: { cx: base.x + base.sz / 2, cy: base.y + base.sz / 2, hw: 300, hh: 200 } });

            const taken = Object.values(saved).filter(b => b.alive && b.ownerId !== pid).map(b => b.color);
            const colors = {}, nms = {};
            for (const s of allStructures) { colors[s.ownerId] = s.color; if (s.name) nms[s.ownerId] = s.name; }

            safeSend(ws, {
                type: 'init', playerId: pid, gridSize: G, baseSize: base.sz, sightRadius: SIGHT,
                maxEnergy: getStats(base).maxEnergy, maxHp: getStats(base).maxHp,
                baseX: base.x, baseY: base.y, myColor: base.color,
                colors, names: nms, chatHistory: chatHist.slice(-50), takenColors: taken,
                wasDestroyed, upgradeCosts: UPGRADES, outpostCost: OUTPOST_COST, newBaseCost: NEW_BASE_COST,
                radio: { state: radioState, queue: radioQueue.map(s => s.title) },
            });
            console.log(`[JOIN] ${name} P${pid} — ${conns.size} online`);
            return;
        }
        if (!joined) return;

        if (msg.type === 'placeBatch') {
            if (!Array.isArray(msg.cells)) return;
            const stats = getStats(base);
            let used = 0;
            for (const c of msg.cells) {
                if (used > 200) break;
                const x = W(c.x), y = W(c.y), i = I(x, y);
                const hs = findStruct(x, y);
                if (hs && hs.ownerId !== pid) continue;
                if (hs && hs.ownerId === pid) {
                    if (gridOwner[i] === pid + 1) setCell(x, y, -1);
                    else if (gridOwner[i] === 0) setCell(x, y, pid);
                } else {
                    if (gridOwner[i] === pid + 1) { setCell(x, y, -1); base.energy = Math.min(stats.maxEnergy, base.energy + 1); }
                    else if (gridOwner[i] === 0 && base.energy > 0 && cellInSight(pid, x, y)) { setCell(x, y, pid); base.energy--; used++; }
                }
            }
            return;
        }

        if (msg.type === 'place') {
            const x = W(msg.x), y = W(msg.y), i = I(x, y);
            const hs = findStruct(x, y);
            if (hs && hs.ownerId !== pid) return;
            if (hs && hs.ownerId === pid) {
                if (gridOwner[i] === pid + 1) setCell(x, y, -1);
                else if (gridOwner[i] === 0) setCell(x, y, pid);
                return;
            }
            if (gridOwner[i] === pid + 1) { setCell(x, y, -1); return; }
            const stats = getStats(base);
            if (gridOwner[i] === 0 && base.energy > 0 && cellInSight(pid, x, y)) { setCell(x, y, pid); base.energy--; }
            return;
        }

        if (msg.type === 'toggleBase') { base.paused = !base.paused; return; }

        if (msg.type === 'clearBase') {
            for (let dy = 0; dy < base.sz; dy++) for (let dx = 0; dx < base.sz; dx++) {
                const x = W(base.x + dx), y = W(base.y + dy);
                if (gridOwner[I(x, y)] === pid + 1) setCell(x, y, -1);
            }
            return;
        }

        // ═══ UPGRADE ═══
        if (msg.type === 'upgrade') {
            const kind = msg.kind; // 'baseSize', 'baseHp', 'maxEnergy', 'energyRegen'
            if (!UPGRADES[kind]) return;
            const lvl = (base.upgrades[kind] || 0);
            if (lvl >= UPGRADES[kind].costs.length) return; // maxed
            const cost = UPGRADES[kind].costs[lvl];
            if ((base.money || 0) < cost) return;
            base.money -= cost;
            base.upgrades[kind] = lvl + 1;
            // Apply immediately
            const stats = getStats(base);
            if (kind === 'baseHp') { base.maxHp = stats.maxHp; base.hp = Math.min(base.hp, base.maxHp); }
            if (kind === 'baseSize') {
                const oldSz = base.sz;
                base.sz = stats.baseSz;
                clearArea(base.x, base.y, base.sz); // clear expanded area
            }
            if (kind === 'maxEnergy') base.energy = Math.min(base.energy, stats.maxEnergy);
            safeSend(ws, { type: 'upgraded', kind, level: base.upgrades[kind] });
            console.log(`[UPGRADE] ${base.name} upgraded ${kind} to level ${base.upgrades[kind]}`);
            return;
        }

        // ═══ BUY OUTPOST ═══
        if (msg.type === 'buyOutpost') {
            if ((base.money || 0) < OUTPOST_COST) return;
            const ox = W(msg.x), oy = W(msg.y);
            // Check all cells in area are explored (have trails from this player or active cells)
            let explored = true;
            for (let dy = 0; dy < OUTPOST_SZ && explored; dy++)
                for (let dx = 0; dx < OUTPOST_SZ && explored; dx++) {
                    const ci = I(W(ox + dx), W(oy + dy));
                    if (trailOwner[ci] !== pid + 1 && gridOwner[ci] !== pid + 1) explored = false;
                }
            if (!explored) { safeSend(ws, { type: 'error', msg: 'Area not fully explored by you' }); return; }
            // Check not overlapping existing structure
            for (let dy = 0; dy < OUTPOST_SZ; dy++)
                for (let dx = 0; dx < OUTPOST_SZ; dx++)
                    if (findStruct(W(ox + dx), W(oy + dy))) { safeSend(ws, { type: 'error', msg: 'Overlaps existing structure' }); return; }

            base.money -= OUTPOST_COST;
            const outpost = {
                id: nextId++, x: ox, y: oy, sz: OUTPOST_SZ, ownerId: pid,
                name: base.name, color: base.color,
                discoveredBy: new Set([pid]), paused: false, alive: true,
                hp: OUTPOST_HP, maxHp: OUTPOST_HP, isOutpost: true,
            };
            allStructures.push(outpost);
            clearArea(ox, oy, OUTPOST_SZ);
            safeSend(ws, { type: 'outpostPlaced' });
            console.log(`[OUTPOST] ${base.name} placed outpost at (${ox},${oy})`);
            return;
        }

        // ═══ BUY NEW BASE (when destroyed) ═══
        if (msg.type === 'buyBase') {
            if (base.alive) return;
            if ((base.money || 0) < NEW_BASE_COST) return;
            base.money -= NEW_BASE_COST;
            const pos = findPos(base.sz);
            base.x = pos.x; base.y = pos.y;
            base.alive = true; base.paused = true;
            base.hp = getStats(base).maxHp;
            base.discoveredBy = new Set([pid]);
            allStructures.push(base);
            clearArea(base.x, base.y, base.sz);
            safeSend(ws, { type: 'newBase', baseX: base.x, baseY: base.y });
            return;
        }

        if (msg.type === 'chat') {
            const text = (msg.text || '').substring(0, 200).trim(); if (!text) return;
            const m = { name: base.name, color: base.color, text, time: Date.now() };
            chatHist.push(m); if (chatHist.length > 100) chatHist.shift();
            for (const [w] of conns) safeSend(w, { type: 'chat', name: m.name, color: m.color, text: m.text });
            return;
        }
        if (msg.type === 'deleteOutpost') {
            const ox = msg.x, oy = msg.y;
            const op = allStructures.find(s => s.isOutpost && s.ownerId === pid && s.alive && s.x === ox && s.y === oy);
            if (!op) return;
            op.alive = false;
            // Clear cells inside
            for (let dy = 0; dy < op.sz; dy++) for (let dx = 0; dx < op.sz; dx++) {
                const x = W(op.x + dx), y = W(op.y + dy);
                if (gridOwner[I(x, y)] === pid + 1) setCell(x, y, -1);
            }
            safeSend(ws, { type: 'outpostDeleted' });
            console.log(`[OUTPOST DEL] ${base.name} deleted outpost at (${ox},${oy})`);
            return;
        }
        if (msg.type === 'radioSkip') { if (radioState.current) radioNext(); return; }
        if (msg.type === 'radioDuration') {
            if (radioState.current && msg.d > 0 && !radioState.current.duration) {
                radioState.current.duration = msg.d;
                radioSchedule(msg.d);
            }
            return;
        }
    });
    ws.on('close', () => { conns.delete(ws); });
});

setInterval(tick, 1000 / TICK_HZ);
server.listen(PORT, () => console.log(`DARK FOREST :${PORT} — ${G}×${G}`));
