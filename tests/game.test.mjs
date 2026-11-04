// End to end: two copies of index.html's script, each with a stub page, a fake audio context and
// the real modem, talking through a simulated room. Simulated players press ready, wait for
// DRAW and fire. Run: node --test tests/
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';

const root = new URL('../', import.meta.url);
const html = fs.readFileSync(new URL('index.html', root), 'utf8');
const pageScript = [...html.matchAll(/<script>([\s\S]*?)<\/script>/g)].pop()[1];
const modemSrc = fs.readFileSync(new URL('modem-worklet.js', root), 'utf8');

function rng(seed) {
  let a = seed >>> 0;
  return () => { a = a + 0x6d2b79f5 >>> 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; };
}

/* ---------- Virtual time: timers and audio blocks in one queue ---------- */
class World {
  constructor() { this.t = 0; this.timers = new Map(); this.nextId = 1; this.pages = []; }
  setTimeout(fn, ms = 0, every = null) { const id = this.nextId++; this.timers.set(id, { at: this.t + Math.max(0, ms) / 1000, fn, every }); return id; }
  clear(id) { this.timers.delete(id); }
  async runUntil(T, onStep) {
    for (;;) {
      let next = null, nt = Infinity;
      for (const [id, tm] of this.timers) if (tm.at < nt) { nt = tm.at; next = id; }
      let page = null, pt = Infinity;
      for (const p of this.pages) { const at = p.timeOf(p.frame); if (at < pt) { pt = at; page = p; } }
      const at = Math.min(nt, pt);
      if (at > T) { this.t = T; return; }
      this.t = at;
      if (pt <= nt) page.block();
      else {
        const tm = this.timers.get(next);
        if (tm.every != null) tm.at += Math.max(tm.every, 1) / 1000; else this.timers.delete(next);
        tm.fn();
      }
      await null; await null;                        // let promise callbacks run
      if (onStep) onStep();
    }
  }
}

/* ---------- A stub DOM, just enough for the page ---------- */
class El {
  constructor() {
    this.textContent = ''; this.innerHTML = ''; this.hidden = false; this.className = ''; this.disabled = false;
    this.dataset = {}; this.style = {}; this.listeners = {}; this.offsetWidth = 0;
    const set = new Set();
    this.classList = { add: c => set.add(c), remove: c => set.delete(c), contains: c => set.has(c), toggle: (c, on) => (on ?? !set.has(c)) ? set.add(c) : set.delete(c) };
  }
  get firstElementChild() { return this._child || (this._child = new El()); }
  addEventListener(k, f) { (this.listeners[k] ||= []).push(f); }
  closest() { return null; }
  appendChild() {} replaceChildren() {}
}

/* ---------- A page: its script, fake audio, and its modem in the room ---------- */
function makePage(world, name, { sr = 48000, ppm = 0, t0 = 0, outLat = 0.04, inLat = 0.03 } = {}) {
  const page = { name, sr, rate: sr * (1 + ppm * 1e-6), t0, outLat, inLat, frame: 0, out: [], core: null, draws: [], bangs: 0 };
  page.timeOf = f => page.t0 + f / page.rate;
  page.frameAt = t => (t - page.t0) * page.rate;
  const els = new Map(), $el = s => els.get(s) || (els.set(s, new El()), els.get(s));
  const docListeners = {};
  const document = { querySelector: $el, querySelectorAll: () => [], addEventListener: (k, f) => (docListeners[k] ||= []).push(f),
    createElement: () => new El(), body: new El(), head: new El(), visibilityState: 'visible', execCommand() {} };
  const node = (extra = {}) => ({ connect: x => x || node(), disconnect() {}, ...extra });
  const param = () => ({ value: 0, setValueAtTime() {}, exponentialRampToValueAtTime() {} });
  class FakeContext {
    constructor() { this.sampleRate = sr; this.state = 'running'; this.destination = node(); this.audioWorklet = { addModule: async () => {} }; }
    get currentTime() { return page.frame / sr; }
    resume() { return Promise.resolve(); } close() { return Promise.resolve(); }
    createBuffer(c, n) { return { getChannelData: () => new Float32Array(n) }; }
    createBufferSource() { return node({ buffer: null, start() {}, stop() {} }); }
    createGain() { return node({ gain: param() }); }
    createBiquadFilter() { return node({ type: '', frequency: param(), Q: param() }); }
    createMediaStreamSource() { return node(); }
    createOscillator() {
      const o = node({ type: '', frequency: { v: 0, setValueAtTime(v) { this.v = v; } }, stopped: false,
        start(t) { if (this.frequency.v === 1320 && !page.draws.some(d => Math.abs(d.t - t) < 0.3)) page.draws.push({ t, osc: this }); },
        stop(t) { if (t === undefined) this.stopped = true; } });   // stop() with no time = called off
      return o;
    }
  }
  class FakeWorkletNode {
    constructor(ctx) {
      const scope = {}; new Function('globalThis', modemSrc)(scope);
      this.port = { onmessage: null, postMessage: m => page.core.onMessage(m) };
      page.core = new scope.QDModem.ModemCore(sr, m => world.setTimeout(() => this.port.onmessage && this.port.onmessage({ data: m }), 0));
    }
    connect() {}
  }
  const stream = { getAudioTracks: () => [{ getSettings: () => ({ sampleRate: sr }), addEventListener() {} }], getTracks: () => [] };
  const modemScope = {}; new Function('globalThis', modemSrc)(modemScope);
  const window = { isSecureContext: true, AudioContext: FakeContext, AudioWorkletNode: FakeWorkletNode, QDModem: modemScope.QDModem,
    addEventListener() {} };
  const navigator = { mediaDevices: { getUserMedia: async () => stream }, vibrate() {}, audioSession: {}, clipboard: {} };
  const location = { href: 'https://example.test/', hash: '', search: '' };
  const api = new Function('document', 'window', 'navigator', 'location', 'history', 'performance', 'setTimeout', 'setInterval',
    'clearTimeout', 'clearInterval', 'AudioWorkletNode', 'requestAnimationFrame', 'cancelAnimationFrame',
    pageScript + `;return { actions, fire, sound,
      get state() { return state; }, get connected() { return connected; }, get pressedReady() { return pressedReady; },
      get last() { return last; }, get score() { return score; }, get round() { return round; }, get myOut() { return myOut; } };`)(
    document, window, navigator, location, { replaceState() {} }, { now: () => world.t * 1000 },
    (f, ms) => world.setTimeout(f, ms), (f, ms) => world.setTimeout(f, ms, ms), id => world.clear(id), id => world.clear(id),
    FakeWorkletNode, () => 0, () => {});
  page.api = api;
  page.block = () => {
    const B = 128, inp = new Float32Array(B), out = new Float32Array(B);
    for (let n = 0; n < B; n++) inp[n] = world.micSample(page, page.frame + n);
    if (page.core) page.core.process(inp, out, page.frame);
    for (let n = 0; n < B; n++) page.out.push(out[n]);
    page.frame += B;
  };
  world.pages.push(page);
  return page;
}

function readOut(p, pos) {
  const i0 = Math.floor(pos), a = 8;
  let s = 0;
  for (let i = i0 - a + 1; i <= i0 + a; i++) {
    if (i < 0 || i >= p.out.length) continue;
    const x = pos - i, w = x === 0 ? 1 : Math.sin(Math.PI * x) / (Math.PI * x) * Math.sin(Math.PI * x / a) / (Math.PI * x / a);
    s += p.out[i] * w;
  }
  return s;
}

function room(world, { dist = 2, gain = 0.01, own = 1, echoes = [{ ms: 12, db: -3 }, { ms: 25, db: -8 }], noise = 0.0005, seed = 1 } = {}) {
  const rand = rng(seed), gauss = () => Math.sqrt(-2 * Math.log(rand() + 1e-12)) * Math.cos(2 * Math.PI * rand());
  const d = dist / 343;
  const peer = [{ delay: d, gain }, ...echoes.map(e => ({ delay: d + e.ms / 1000, gain: gain * Math.pow(10, e.db / 20) }))];
  world.micSample = (p, f) => {
    const t = p.timeOf(f) - p.inLat;
    let x = noise * gauss();
    for (const s of world.pages) for (const path of s === p ? [{ delay: 0.0003, gain: own }] : peer) {
      const pos = s.frameAt(t - path.delay - s.outLat);
      if (pos > 0) x += path.gain * readOut(s, pos);
    }
    return x;
  };
  return d;
}

// Simulated players: press ready, wait for DRAW, fire after their reaction time; sometimes jump the gun.
function players(world, host, guest, plan) {
  const st = new Map();
  return () => {
    for (const p of [host, guest]) {
      const a = p.api, s = st.get(p) || {};
      st.set(p, s);
      if (!a.connected) continue;
      const n = a.score.me + a.score.them + (a.last && a.last.res === 'even' ? 1 : 0);
      if (a.state === 'lobby' && !a.pressedReady && !s.readyAt) s.readyAt = world.t + 1 + (p === host ? 0 : 0.4);
      if (s.readyAt && world.t >= s.readyAt) { s.readyAt = 0; a.actions.ready(); }
      const r = a.round, mine = plan(p === host ? 'host' : 'guest', r);
      if (a.state === 'armed' && mine.foulAt != null && s.fouled !== r && world.t >= s.armedAt + mine.foulAt) { s.fouled = r; a.fire(); }
      if (a.state === 'armed' && s.armedRound !== r) { s.armedRound = r; s.armedAt = world.t; }
      if (a.state === 'drawn' && s.drawnRound !== r) { s.drawnRound = r; s.fireAt = world.t + mine.react / 1000; }
      if (a.state === 'drawn' && s.fireAt && world.t >= s.fireAt) { s.fireAt = 0; a.fire(); }
    }
  };
}

test('two pages pair by sound and play five rounds; results agree; DRAW sounds leave the speakers together', async () => {
  const world = new World();
  const host = makePage(world, 'host', { outLat: 0.035, inLat: 0.02 });
  const guest = makePage(world, 'guest', { sr: 44100, ppm: 25, t0: 0.0213, outLat: 0.07, inLat: 0.04 });
  const d = room(world, { dist: 2 });

  // Round plans: reaction times (ms); in round 3 the guest jumps the gun.
  const plan = (who, r) => r === 3 && who === 'guest' ? { react: 300, foulAt: 1.0 }
    : { react: who === 'host' ? [290, 260, 340, 300, 250, 410][r % 6] : [240, 310, 280, 300, 330, 220][r % 6] };
  const drive = players(world, host, guest, plan);

  await world.runUntil(0.5);
  host.api.actions['sound-host']();
  await world.runUntil(2);
  guest.api.actions['sound-join']();
  await world.runUntil(12, drive);
  assert.ok(host.api.connected && guest.api.connected, `paired: host ${host.api.connected}, guest ${guest.api.connected}`);
  console.log(`paired at ~${world.t.toFixed(1)} s; guest round trip ${(guest.api.sound.rt / 44100 * 1000).toFixed(1)} ms (true ${((0.07 + 0.04) * 1000).toFixed(0)})`);

  // Each page's result per round, as it appears.
  const seen = { host: new Map(), guest: new Map() }, prev = {};
  await world.runUntil(150, () => {
    drive();
    if (process.env.TRACE) for (const p of [host, guest]) {      // TRACE=1: log every change of each page's state
      const a = p.api, s = `${a.state} r${a.round} ready:${a.pressedReady} tx:${a.sound.tx && JSON.parse(a.sound.tx).state} aborting:${a.sound.aborting}`;
      if (prev[p.name] !== s) { prev[p.name] = s; console.log(`${world.t.toFixed(2)} ${p.name.padEnd(5)} ${s}`); }
    }
    for (const p of [host, guest]) if (p.api.last && !seen[p.name].has(p.api.round)) seen[p.name].set(p.api.round, p.api.last);
  });
  const results = [...seen.host].filter(([r]) => seen.guest.has(r)).map(([round, h]) => ({ round, h, g: seen.guest.get(round) }));

  const opposite = { win: 'lose', lose: 'win', even: 'even', 'both-foul': 'both-foul' };
  for (const r of results) console.log(`round ${r.round}: host ${r.h.res} (${r.h.me.ms?.toFixed(0) ?? (r.h.me.foul ? 'foul' : '-')} ms) · guest ${r.g.res} (${r.g.me.ms?.toFixed(0) ?? (r.g.me.foul ? 'foul' : '-')} ms)`);
  console.log(`score host ${host.api.score.me}-${host.api.score.them}, guest ${guest.api.score.me}-${guest.api.score.them}`);
  assert.ok(results.length >= 5, `only ${results.length} rounds finished`);
  for (const r of results) assert.equal(r.g.res, opposite[r.h.res], `round ${r.round}: host ${r.h.res}, guest ${r.g.res}`);
  assert.equal(host.api.score.me, guest.api.score.them);
  assert.equal(host.api.score.them, guest.api.score.me);
  const r3 = results.find(r => r.round === 3);
  assert.ok(r3 && r3.h.res === 'win' && r3.g.me.foul, 'round 3: the guest fouled, the host wins');

  // DRAW sounds that played (not called off): emission time in real seconds, per phone.
  const emit = p => p.draws.filter(x => !x.osc.stopped).map(x => p.timeOf(x.t * p.sr) + p.outLat);
  const he = emit(host), ge = emit(guest), gaps = [];
  for (const t of he) { const m = ge.find(u => Math.abs(u - t) < 0.5); if (m != null) gaps.push((m - t - d) * 1000); }
  console.log('DRAW gap per round (guest - host - flight time, ms):', gaps.map(x => x.toFixed(1)).join(' '));
  assert.ok(gaps.length >= 4, `only ${gaps.length} paired DRAW sounds`);
  for (const g of gaps) assert.ok(Math.abs(g) <= 5, `DRAW gap ${g} ms`);
});
