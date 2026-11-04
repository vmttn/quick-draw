// Simulated-room tests for modem-worklet.js. Run: node --test tests/
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';

const src = fs.readFileSync(new URL('../modem-worklet.js', import.meta.url), 'utf8');
const scope = {};
new Function('globalThis', src)(scope);
const { ModemCore, PLANS, ST, encode, decode, P } = scope.QDModem;

/* ---------- A deterministic room ---------- */
function rng(seed) {
  let a = seed >>> 0;
  return () => { a = a + 0x6d2b79f5 >>> 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; };
}
const C = 343;

// A phone: a ModemCore plus its clock (start time, rate, drift) and audio latencies.
function phone(name, { sr = 48000, ppm = 0, t0 = 0, outLat = 0.040, inLat = 0.030 } = {}) {
  const msgs = [], txs = [];
  const core = new ModemCore(sr, m => msgs.push({ ...m, at: null }));
  const np = core.newPacket.bind(core);
  core.newPacket = f => { np(f); txs.push({ end: core.pkt.end, key: core.pkt.syms.slice(2).join(','), st: { ...core.st } }); };
  const rate = sr * (1 + ppm * 1e-6);      // true samples per real second
  return { name, core, sr, rate, t0, outLat, inLat, msgs, txs, out: [], frame: 0,
    timeOf: f => t0 + f / rate, frameAt: t => (t - t0) * rate };
}

// Windowed-sinc read of a phone's output at a fractional frame.
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

// Runs the phones for `seconds` of real time. paths[i][j]: list of {delay, gain} from phone i's speaker to phone j's mic.
function run(phones, paths, seconds, { noise = 0, seed = 1, onBlock } = {}) {
  const rand = rng(seed), gauss = () => Math.sqrt(-2 * Math.log(rand() + 1e-12)) * Math.cos(2 * Math.PI * rand());
  const B = 128;
  for (;;) {
    let p = null;
    for (const q of phones) if (!p || q.timeOf(q.frame) < p.timeOf(p.frame)) p = q;
    if (p.timeOf(p.frame) > seconds) break;
    const j = phones.indexOf(p), inp = new Float32Array(B), out = new Float32Array(B);
    for (let n = 0; n < B; n++) {
      const t = p.timeOf(p.frame + n) - p.inLat;          // when this mic sample was captured
      let x = noise ? noise * gauss() : 0;
      phones.forEach((s, i) => {
        for (const path of paths[i][j]) {
          const pos = s.frameAt(t - path.delay - s.outLat);
          if (pos > 0) x += path.gain * readOut(s, pos);
        }
      });
      inp[n] = x;
    }
    p.core.process(inp, out, p.frame);
    for (let n = 0; n < B; n++) p.out.push(out[n]);
    p.frame += B;
    if (onBlock) onBlock(p);
  }
}

function setup({ plan = 'quiet', dist = 3, gain = 0.01, own = 1, echoes = [], hostOpts = {}, guestOpts = {} } = {}) {
  const host = phone('host', hostOpts), guest = phone('guest', { t0: 0.0137, ...guestOpts });
  const pl = PLANS[plan];
  host.core.onMessage({ type: 'config', tx: pl.host, rx: [{ id: 'g', f0: pl.guest }, { id: 'h', f0: pl.host }] });
  guest.core.onMessage({ type: 'config', tx: pl.guest, rx: [{ id: 'h', f0: pl.host }, { id: 'g', f0: pl.guest }] });
  const d = dist / C, peer = [{ delay: d, gain }, ...echoes.map(e => ({ delay: d + e.ms / 1000, gain: gain * Math.pow(10, e.db / 20) }))];
  const self = [{ delay: 0.0003, gain: own }];
  return { host, guest, paths: [[self, peer], [peer, self]], d };
}
// Noise std for a given per-tone SNR (dB) at received tone amplitude a (rectangular 64 ms window, as the probe defines it).
const noiseFor = (a, snrDb, sr = 48000) => a * Math.sqrt(Math.round(P.FLAT * sr) / (4 * Math.pow(10, snrDb / 10)));
const packets = (p, band) => p.msgs.filter(m => m.type === 'packet' && m.band === band);

/* ---------- Tests ---------- */
test('encode/decode: round trip, repairs up to 4 doubtful symbols, rejects garbage', () => {
  const r = rng(5);
  for (let i = 0; i < 2000; i++) {
    const f = { sess: r() * 32 | 0, round: r() * 64 | 0, state: r() * 6 | 0, payload: r() * 8192 | 0 };
    const s = encode(f);
    assert.deepEqual(decode(s).f, f);
    // Corrupt 1-4 symbols; the receiver ranks them among its 6 least certain (faded symbols look weak).
    const bad = s.slice(), pos = [...Array(14).keys()].sort(() => r() - 0.5), n = 1 + (r() * 4 | 0);
    for (let k = 0; k < n; k++) bad[pos[k]] = (bad[pos[k]] + 1 + (r() * 15 | 0)) % 16;
    const ratio = Array(14).fill(0).map(() => 3 + 5 * r());
    pos.slice(0, 6).forEach((p, k) => { ratio[p] = k < n ? 1 + 0.5 * r() : 1.6 + r(); });
    assert.deepEqual(decode(bad, ratio).f, f);
  }
  // Noise: symbol ratios like those of the strongest of 16 random tones over the runner-up.
  const noiseRatio = () => { const e = Array.from({ length: 16 }, () => -Math.log(r() + 1e-12)).sort((a, b) => b - a); return e[0] / e[1]; };
  let fooled = 0;
  for (let i = 0; i < 20000; i++) {
    const junk = Array.from({ length: 14 }, () => r() * 16 | 0), ratio = junk.map(noiseRatio);
    if (decode(junk, ratio)) fooled++;
  }
  console.log(`random words accepted: ${fooled} / 20000`);
  assert.ok(fooled / 20000 < 0.0005);
});

// Packets sent by tx that rx decoded, with their timing errors (ms).
function score(tx, rx, band, d, until) {
  const sent = tx.txs.filter(t => tx.timeOf(t.end) + tx.outLat + d + 0.2 < until && tx.timeOf(t.end) > 1.5);
  const got = packets(rx, band), errs = [], good = [];
  for (const t of sent) {
    const truth = rx.frameAt(tx.timeOf(t.end) + tx.outLat + d + rx.inLat);
    const m = got.find(g => Math.abs(g.endFrame - truth) < rx.sr * 0.05);
    if (!m) continue;
    errs.push((m.endFrame - truth) / rx.sr * 1000);
    if (m.goodTiming) good.push((m.endFrame - truth) / rx.sr * 1000);
  }
  return { sent: sent.length, hit: errs.length, rate: errs.length / sent.length, good,
    exact: good.filter(e => Math.abs(e) <= 1.5).length / Math.max(good.length, 1) };
}

// The modem is reliable from about 18 dB per tone (see the sensitivity test for lower values).
test('quiet plan, echoes, 18 dB per tone, 48 vs 44.1 kHz with drift: delivery, timing, round trip', () => {
  const gain = 0.01, a = P.GAIN * gain;
  const env = setup({ dist: 3, gain, echoes: [{ ms: 12, db: -3 }, { ms: 25, db: -8 }],
    hostOpts: { sr: 48000, ppm: 20 }, guestOpts: { sr: 44100, ppm: -20, outLat: 0.060, inLat: 0.025 } });
  const { host, guest, paths, d } = env;
  host.core.onMessage({ type: 'state', sess: 7, state: ST.READY, round: 1, payload: 0 });
  guest.core.onMessage({ type: 'state', sess: 7, state: ST.IDLE, round: 1, payload: 1 });
  run([host, guest], paths, 40, { noise: noiseFor(a, 18), seed: 2 });

  for (const [tx, rx, band] of [[host, guest, 'h'], [guest, host, 'g']]) {
    const s = score(tx, rx, band, d, 40);
    // A weak chirp can lock on a strong echo (timing late by the echo's delay); the game takes the
    // median over repeated packets, so most single packets being exact is what matters.
    console.log(`${tx.name}->${rx.name}: ${s.hit}/${s.sent} packets, ${s.good.length} with good timing, ${Math.round(s.exact * 100)}% of those within 1.5 ms`);
    assert.ok(s.rate >= 0.95, `delivery ${s.rate}`);
    assert.ok(s.good.length >= 0.6 * s.hit, `only ${s.good.length} with good timing`);
    assert.ok(s.exact >= 0.8, `only ${s.exact} within 1.5 ms`);
  }
  for (const p of [host, guest]) {
    const self = p.msgs.filter(m => m.type === 'self').pop();
    assert.ok(self, `${p.name} measured no round trip`);
    const truth = (p.outLat + p.inLat + 0.0003) * p.rate;
    const err = (self.rtFrames - truth) / p.sr * 1000;
    console.log(`${p.name} round trip: ${(self.rtFrames / p.sr * 1000).toFixed(2)} ms (error ${err.toFixed(2)} ms)`);
    assert.ok(Math.abs(err) <= 1, `round trip error ${err} ms`);
  }
});

test('loud plan, 5 m, 18 dB per tone: delivery', () => {
  const gain = 0.006, a = P.GAIN * gain;
  const { host, guest, paths, d } = setup({ plan: 'loud', dist: 5, gain, echoes: [{ ms: 11, db: -4 }, { ms: 19, db: -9 }] });
  host.core.onMessage({ type: 'state', sess: 3, state: ST.HELLO, round: 0, payload: 0 });
  guest.core.onMessage({ type: 'state', sess: 3, state: ST.HELLO, round: 0, payload: 0 });
  run([host, guest], paths, 30, { noise: noiseFor(a, 18), seed: 3 });
  for (const [tx, rx, band] of [[host, guest, 'h'], [guest, host, 'g']]) {
    const s = score(tx, rx, band, d, 30);
    console.log(`loud ${tx.name}->${rx.name}: ${s.hit}/${s.sent}`);
    assert.ok(s.rate >= 0.95, `delivery ${s.hit}/${s.sent}`);
  }
});

test('sensitivity: delivery by SNR per tone (as sound-probe.html measures it), quiet plan, echoes', () => {
  const rows = [];
  for (const snr of [9, 12, 15, 18]) {
    const gain = 0.01, a = P.GAIN * gain;
    const { host, guest, paths, d } = setup({ dist: 3, gain, echoes: [{ ms: 12, db: -3 }, { ms: 25, db: -8 }] });
    host.core.onMessage({ type: 'state', sess: 7, state: ST.READY, round: 1, payload: 0 });
    run([host, guest], paths, 20, { noise: noiseFor(a, snr), seed: 20 + snr });
    const s = score(host, guest, 'h', d, 20);
    rows.push(`${snr} dB: ${Math.round(s.rate * 100)}% (${s.good.length}/${s.hit} good timing)`);
  }
  console.log('sensitivity  ' + rows.join(' · '));
  // Known weak spot: one strong echo whose delay makes neighbouring tones fade alternately
  // (delay ~ (2m+1) / (2 x 62.5 Hz): 8, 24 ms). Phones held still are the worst case; in a
  // hand, millimetres of movement shift the fades between repeats.
  const by = [];
  for (const ms of [3, 8, 12, 24]) {
    const gain = 0.01, a = P.GAIN * gain;
    const { host, guest, paths, d } = setup({ gain, echoes: [{ ms, db: -4 }] });
    host.core.onMessage({ type: 'state', sess: 7, state: ST.READY, round: 1, payload: 0 });
    run([host, guest], paths, 14, { noise: noiseFor(a, 15), seed: ms });
    by.push(`${ms} ms: ${Math.round(score(host, guest, 'h', d, 14).rate * 100)}%`);
  }
  console.log('one echo at -4 dB, 15 dB, still phones, by delay  ' + by.join(' · '));
});

test('DRAW alignment: guest schedules its DRAW so both sounds leave the speakers together', () => {
  const gain = 0.01, a = P.GAIN * gain;
  const { host, guest, paths, d } = setup({ dist: 3, gain, echoes: [{ ms: 12, db: -3 }],
    hostOpts: { outLat: 0.035, inLat: 0.020 }, guestOpts: { sr: 44100, outLat: 0.080, inLat: 0.045, ppm: 30 } });
  host.core.onMessage({ type: 'state', sess: 9, state: ST.READY, round: 4, payload: 0 });
  guest.core.onMessage({ type: 'state', sess: 9, state: ST.READY, round: 4, payload: 0 });
  let armed = false, drawAt;
  const errs = [];
  run([host, guest], paths, 16, { noise: noiseFor(a, 15), seed: 4, onBlock: p => {
    if (!armed && p === host && host.timeOf(host.frame) > 4) {      // arm with a draw 6 s ahead
      armed = true; drawAt = host.frame + 6 * host.sr;
      host.core.onMessage({ type: 'state', state: ST.ARMED, round: 5, drawAtFrame: drawAt });
    }
  } });
  const rt = guest.msgs.filter(m => m.type === 'self').pop().rtFrames;
  const est = [];                                                     // what index.html does: the earliest estimate so far
  for (const m of packets(guest, 'h').filter(m => m.state === ST.ARMED && m.payload > 0 && m.goodTiming)) {   // payload 0: heard after the DRAW
    est.push(m.endFrame - rt + m.payload * 0.002 * guest.sr);
    const G = Math.min(...est);
    const hostEmit = host.timeOf(drawAt) + host.outLat, guestEmit = guest.timeOf(G) + guest.outLat;
    errs.push((guestEmit - hostEmit - d) * 1000);
  }
  console.log('DRAW offset (ms, beyond flight time), as each ARMED packet arrives:', errs.map(e => e.toFixed(1)).join(' '));
  assert.ok(errs.length >= 3, `only ${errs.length} ARMED packets heard`);
  for (const e of errs) assert.ok(Math.abs(e) <= 3, `DRAW offset ${e} ms`);
});

// One 1.28 s packet, plus waiting for the current slot to end, plus one lost packet = 2.7 s.
test('state change reaches the peer within 2.8 s', () => {
  const gain = 0.01, a = P.GAIN * gain;
  const { host, guest, paths } = setup({ dist: 2, gain, echoes: [{ ms: 10, db: -5 }] });
  host.core.onMessage({ type: 'state', sess: 1, state: ST.IDLE, round: 0, payload: 0 });
  guest.core.onMessage({ type: 'state', sess: 1, state: ST.IDLE, round: 0, payload: 0 });
  const changes = [];
  let next = 2, r = 0;
  run([host, guest], paths, 60, { noise: noiseFor(a, 18), seed: 6, onBlock: p => {
    if (p === host && host.timeOf(host.frame) > next) {
      r = (r + 1) % 64; changes.push({ r, t: host.timeOf(host.frame) });
      host.core.onMessage({ type: 'state', state: ST.READY, round: r, payload: 0 });
      next += 2.3 + (r % 5) * 0.37;
    }
  } });
  const got = packets(guest, 'h');
  const lat = changes.filter(c => c.t < 57).map(c => {
    const m = got.find(g => g.round === c.r);
    return m ? guest.timeOf(m.endFrame) - c.t : Infinity;
  });
  lat.sort((x, y) => x - y);
  console.log(`latency s: median ${lat[lat.length >> 1].toFixed(2)}, max ${lat[lat.length - 1].toFixed(2)} over ${lat.length} changes`);
  assert.ok(lat[lat.length - 1] <= 2.8, `worst latency ${lat[lat.length - 1]} s`);
});

test('no false packets from noise alone', () => {
  const p = phone('lone');
  p.core.onMessage({ type: 'config', rx: [{ id: 'h', f0: PLANS.quiet.host }, { id: 'g', f0: PLANS.loud.host }] });
  const rand = rng(11), gauss = () => Math.sqrt(-2 * Math.log(rand() + 1e-12)) * Math.cos(2 * Math.PI * rand());
  const inp = new Float32Array(128), out = new Float32Array(128);
  for (let f = 0; f < 48000 * 300; f += 128) {
    for (let i = 0; i < 128; i++) inp[i] = 0.05 * gauss();
    p.core.process(inp, out, f);
  }
  const st = p.msgs.filter(m => m.type === 'stats').pop();
  console.log(`5 min of noise: ${st.cands} marker candidates, ${st.nochirp} without a chirp, ${st.bad} failed decodes, ${packets(p, 'h').length + packets(p, 'g').length} packets`);
  assert.equal(packets(p, 'h').length + packets(p, 'g').length, 0);
});
