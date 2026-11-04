'use strict';
/* =====================================================================
   Quick-Draw Duel sound modem (AudioWorklet).

   Two phones talk through speaker and microphone, each sending in its own
   band (frequency-division duplex) and repeating its latest game state in a
   loop. The idea of a state-repeating acoustic link between phones comes from
   Battle Drones' Sound Duel (simonw/battledrones, Apache-2.0); this modem is a
   much simpler one written for our tiny messages.

   Packet (16 slots of 80 ms, 1.28 s):
     slot 0      marker tone (tone 3): found by tone energy, starts a decode
     slot 1      chirp across the band: confirms the marker, and gives the
                 exact packet timing (first-arrival peak, so echoes don't bias it)
     slots 2-15  14 symbols, one of 16 tones each: 10 data + 4 Reed-Solomon parity
   Each slot: 8 ms fade in, 64 ms full level, 8 ms fade out.
   40 data bits: session 5, round 6, state 3, payload 13, CRC-13.

   Echoes make some tones fade (they add out of phase), and the fades stay put
   while the phones are still, so repeating doesn't help. The Reed-Solomon
   parity rebuilds up to 4 symbols, picked from the least certain ones.

   The values below are first guesses (not yet measured on phones); retune
   them here.
   ===================================================================== */
(function (G) {
  const P = {
    DF: 62.5,          // tone spacing (Hz)
    NT: 16,            // tones per band
    SLOT: 0.080,       // symbol slot (s)
    RAMP: 0.008,       // fade in / out (s)
    FLAT: 0.064,       // full-level part, the analysis window (s)
    TAPER: 0.125,      // analysis window: fraction tapered at each end (0.5 = Hann)
    HOP: 0.0025,       // marker search step (s)
    MARK: 3,           // marker tone
    REFS: [0, 6, 9, 15],  // tones compared against the marker tone
    DOM: 4,            // marker tone must be 4x (6 dB) above every reference tone
    MIN_RUN: 12,       // ... for at least 12 hops (30 ms); noise rarely holds that long, a marker holds ~25
    GAP: 4,            // hops a run may dip below that and still continue
    SEARCH: 0.012,     // chirp search range around the marker's timing (s)
    CHIRP_SNR: 4,      // chirp peak must be 4x the median of the search range (power); a loose check, the chirp is for timing
    GOOD_TIMING: 12,   // packets whose chirp peak is 12x the median report trustworthy timing (tq >= this)
    MIN_RATIO: 1.6,    // symbols not rebuilt by the code: best tone >= 1.6x the runner-up
    LEAD: 0.5,         // earliest chirp peak with at least this fraction of the largest power wins (direct path, not echo) ...
    LEAD_Q: 20,        // ... when the largest is 20x the median; below that, noise could pass as an early peak: take the largest
    FINE: 0.0015,      // final timing search around the chirp estimate (s)
    GAIN: 0.5,         // transmit level
    LAG_BUDGET: 12,    // fine-timing lags computed per audio callback (spreads the CPU load; a packet takes ~25 callbacks)
  };
  const PLANS = {
    quiet: { host: 15500, guest: 17000 },
    loud: { host: 5000, guest: 6500 },
  };
  // OUT_ACK: my result, and I have yours (results must outlive the next "ready" until the other phone has them).
  const ST = { HELLO: 0, IDLE: 1, READY: 2, ARMED: 3, OUT: 4, ABORT: 5, OUT_ACK: 6 };
  const WHITEN = [9, 3, 14, 5, 12, 1, 7, 10, 4, 15, 2, 11, 6, 13];
  const INFO = 10, CODE = 14, SLOTS = 2 + CODE, CHIRP = -1;
  const bandTop = f0 => f0 + (P.NT - 1) * P.DF;

  /* ---------- GF(16) and Reed-Solomon (14, 10), erasure decoding ---------- */
  const EXP = new Uint8Array(30), LOG = new Uint8Array(16);
  for (let i = 0, x = 1; i < 15; i++) { EXP[i] = EXP[i + 15] = x; LOG[x] = i; x <<= 1; if (x & 16) x ^= 0x13; }
  const mul = (a, b) => a && b ? EXP[LOG[a] + LOG[b]] : 0;
  const inv = a => EXP[(15 - LOG[a]) % 15];
  const pw = (j, i) => EXP[(j * i) % 15];       // (alpha^j)^i

  // Fills the positions in `era` so that the word is a codeword (roots alpha^1..alpha^4).
  // The equations not used to solve must also hold, which catches most wrong guesses.
  // Returns the filled word, or null.
  function rsFill(word, era) {
    const r = word.slice();
    for (const j of era) r[j] = 0;
    const S = [];
    for (let i = 1; i <= 4; i++) { let s = 0; for (let j = 0; j < CODE; j++) s ^= mul(r[j], pw(j, i)); S.push(s); }
    const e = era.length;
    if (e) {
      const A = [];                             // A[i][k] = alpha^(j_k * (i+1)), augmented with S[i]
      for (let i = 0; i < e; i++) A.push([...era.map(j => pw(j, i + 1)), S[i]]);
      for (let c = 0; c < e; c++) {
        let p = c; while (p < e && !A[p][c]) p++;
        if (p === e) return null;
        [A[c], A[p]] = [A[p], A[c]];
        const iv = inv(A[c][c]);
        for (let k = c; k <= e; k++) A[c][k] = mul(A[c][k], iv);
        for (let i = 0; i < e; i++) if (i !== c && A[i][c]) { const f = A[i][c]; for (let k = c; k <= e; k++) A[i][k] ^= mul(f, A[c][k]); }
      }
      era.forEach((j, k) => { r[j] = A[k][e]; });
    }
    for (let i = 1; i <= 4; i++) {             // full check
      let s = 0; for (let j = 0; j < CODE; j++) s ^= mul(r[j], pw(j, i));
      if (s) return null;
    }
    return r;
  }

  /* ---------- Bits ---------- */
  function crc13(v, n) {                      // CRC-13/BBC, polynomial 0x1CF5
    let c = 0;
    for (let i = n - 1; i >= 0; i--) {
      const b = ((v >>> i) & 1) ^ ((c >>> 12) & 1);
      c = (c << 1) & 0x1fff;
      if (b) c ^= 0x1cf5;
    }
    return c;
  }
  function encode(f) {                        // fields -> 14 symbols
    const v = ((f.sess & 31) << 22 | (f.round & 63) << 16 | (f.state & 7) << 13 | (f.payload & 8191)) >>> 0;
    const c = crc13(v, 27), bits = [];
    for (let i = 26; i >= 0; i--) bits.push((v >>> i) & 1);
    for (let i = 12; i >= 0; i--) bits.push((c >>> i) & 1);
    const word = [];
    for (let s = 0; s < INFO; s++) word.push(bits[4 * s] << 3 | bits[4 * s + 1] << 2 | bits[4 * s + 2] << 1 | bits[4 * s + 3]);
    const cw = rsFill([...word, 0, 0, 0, 0], [10, 11, 12, 13]);
    return cw.map((x, i) => x ^ WHITEN[i]);
  }
  function unpack(word) {                     // 10 info symbols -> fields, or null if the CRC fails
    let v = 0, c = 0;
    for (let s = 0; s < INFO; s++)
      for (let b = 3; b >= 0; b--) {
        const bit = (word[s] >>> b) & 1, i = 4 * s + (3 - b);
        if (i < 27) v = (v << 1 | bit) >>> 0; else c = c << 1 | bit;
      }
    if (crc13(v, 27) !== c) return null;
    return { sess: v >>> 22 & 31, round: v >>> 16 & 63, state: v >>> 13 & 7, payload: v & 8191 };
  }
  // Erasure patterns to try, as ranks in the least-certain-first order: none, the 1-3 least
  // certain, then every 4 of the 6 least certain.
  const TRIES = [[], [0], [0, 1], [0, 1, 2]];
  for (let a = 0; a < 6; a++) for (let b = a + 1; b < 6; b++) for (let c = b + 1; c < 6; c++) for (let d = c + 1; d < 6; d++) TRIES.push([a, b, c, d]);
  // syms: 14 received symbols. ratio (optional): per symbol, best tone power / runner-up.
  // Rebuilding 4 symbols uses up all the parity, so nothing checks the result but the CRC; then
  // the symbols kept must look like real tones (ratio >= MIN_RATIO), which noise rarely does.
  function decode(syms, ratio) {              // -> {f: fields, word} or null
    const r = syms.map((s, i) => s ^ WHITEN[i]);
    const order = ratio ? [...ratio.keys()].sort((p, q) => ratio[p] - ratio[q]) : [...Array(CODE).keys()];
    for (const t of TRIES) {
      const era = t.map(k => order[k]);
      if (ratio && era.length === 4 && ratio.some((x, i) => x < P.MIN_RATIO && !era.includes(i))) continue;
      const w = rsFill(r, era);
      if (!w) continue;
      const f = unpack(w);
      if (f) return { f, word: w.map((x, i) => x ^ WHITEN[i]) };
    }
    return null;
  }

  /* ---------- Geometry at a sample rate ---------- */
  function geometry(sr) {
    const S = P.SLOT * sr, R = Math.round(P.RAMP * sr), N = Math.round(P.FLAT * sr);
    const starts = [];
    for (let i = 0; i <= SLOTS; i++) starts.push(Math.round(i * S));
    // Tukey window (25% tapered): loses ~0.4 dB of SNR against a plain window (Hann loses 1.8),
    // while its leakage far from the tone stays low enough to ignore our own, much louder band.
    const win = new Float32Array(N), T = Math.max(1, Math.round(P.TAPER * N));
    for (let i = 0; i < N; i++) {
      const k = Math.min(i, N - 1 - i);
      win[i] = k < T ? 0.5 - 0.5 * Math.cos(Math.PI * (k + 0.5) / T) : 1;
    }
    return { sr, S, R, N, starts, win, hop: Math.round(P.HOP * sr) };
  }
  const SWEEP = (P.NT - 1) * P.DF / P.FLAT;    // chirp rate (Hz/s)
  function chirpPhase(f0, u) {                // u: seconds from the start of the full-level part
    return 2 * Math.PI * (f0 * u + SWEEP * u * u / 2);
  }

  /* ---------- One receiver (one band) ---------- */
  class Rx {
    constructor(core, id, f0, own) {
      Object.assign(this, { core, id, f0, own });
      const g = core.g, w = f => 2 * Math.cos(2 * Math.PI * f / g.sr);
      this.cMark = w(f0 + P.MARK * P.DF);
      this.cRefs = P.REFS.map(k => w(f0 + k * P.DF));
      this.cTones = Array.from({ length: P.NT }, (_, k) => w(f0 + k * P.DF));
      this.tr = new Float32Array(g.N); this.ti = new Float32Array(g.N);
      for (let n = 0; n < g.N; n++) { const ph = chirpPhase(f0, n / g.sr); this.tr[n] = Math.cos(ph); this.ti[n] = -Math.sin(ph); }
      // Dechirp: the chirp times its conjugate becomes a steady beat whose frequency gives the
      // chirp's offset (beat = -SWEEP * offset). Decimate by 4, Hann window, then a few DFT bins.
      this.n4 = Math.floor(g.N / 4);
      this.hann4 = new Float32Array(this.n4);
      for (let m = 0; m < this.n4; m++) this.hann4[m] = 0.5 - 0.5 * Math.cos(2 * Math.PI * (m + 0.5) / this.n4);
      const step = 0.5 / P.FLAT, bmax = SWEEP * P.SEARCH + 2 * step;
      this.beats = [];
      for (let b = -bmax; b <= bmax + 1e-9; b += step) this.beats.push(b);
      this.bc = this.beats.map(b => { const c = new Float32Array(this.n4), s = new Float32Array(this.n4);
        for (let m = 0; m < this.n4; m++) { const a = -2 * Math.PI * b * m * 4 / g.sr; c[m] = Math.cos(a); s[m] = Math.sin(a); } return [c, s]; });
      this.yr = new Float32Array(this.n4); this.yi = new Float32Array(this.n4);
      this.hj = 0; this.hH = new Float64Array(128); this.hE = new Float64Array(128);   // marker energy per hop
      this.run = null;
      this.edge = markerEdges(g, f0 + P.MARK * P.DF);
      this.cands = [];
      this.jobs = [];
      this.lastEnd = -Infinity;
    }
    // Marker search. While the marker tone dominates, hops form a "run". When the run ends, its
    // 50% energy crossings give the timing: the rising edge is steep (robust to noise) and comes
    // from the direct sound (echoes only stretch the falling edge). A run that is too long
    // (a data symbol equal to the marker tone right before or after it) yields two candidates.
    onHop(h, scratch) {                       // scratch = Hann-windowed samples of the window ending at h
      const e3 = goertzel(scratch, this.cMark);
      let rmax = 0;
      for (const c of this.cRefs) rmax = Math.max(rmax, goertzel(scratch, c));
      const j = ++this.hj;
      this.hH[j & 127] = h; this.hE[j & 127] = e3;
      if (e3 >= P.DOM * rmax) {
        if (!this.run) this.run = { j0: j, j1: j };
        else this.run.j1 = j;
        if (j - this.run.j0 > 100) this.run = null;           // a steady tone, not a marker
      } else if (this.run && j - this.run.j1 > P.GAP) {
        this.endRun(this.run); this.run = null;
      }
    }
    endRun({ j0, j1 }) {
      if (j1 - j0 + 1 < P.MIN_RUN) return;
      const H = j => this.hH[j & 127], E = j => this.hE[j & 127];
      let m = 0;
      for (let j = j0; j <= j1; j++) m = Math.max(m, E(j));
      const half = m / 2;
      let jr = j0; while (E(jr) < half) jr++;
      let jf = j1; while (E(jf) < half) jf--;
      const cross = (a, b) => H(a) + (half - E(a)) / (E(b) - E(a) || 1e-30) * (H(b) - H(a));
      const tRise = cross(jr - 1, jr) + this.edge.rise, tFall = cross(jf + 1, jf) - this.edge.fall;
      const g = this.core.g, add = t => { this.core.stats.cands++; this.cands.push({ t3: Math.round(t), delta: null, syms: [], ratio: [] }); };
      add(tRise);
      if (tFall - tRise > g.S / 2) add(tFall);
    }
    chirpCheck(tc0) {                         // returns {delta: the chirp's offset in samples (first arrival), q: peak / median}, or null
      const g = this.core.g, M = this.core.mask, ring = this.core.ring, n4 = this.n4, yr = this.yr, yi = this.yi;
      let idx = (tc0 - g.N) & M;
      for (let m = 0; m < n4; m++) {
        let r = 0, i = 0;
        for (let q = 0; q < 4; q++) { const n = 4 * m + q, x = ring[idx]; r += x * this.tr[n]; i += x * this.ti[n]; idx = (idx + 1) & M; }
        yr[m] = r * this.hann4[m]; yi[m] = i * this.hann4[m];
      }
      const pow = this.bc.map(([c, s]) => {
        let re = 0, im = 0;
        for (let m = 0; m < n4; m++) { re += yr[m] * c[m] - yi[m] * s[m]; im += yr[m] * s[m] + yi[m] * c[m]; }
        return re * re + im * im;
      });
      const sorted = [...pow].sort((a, b) => a - b), med = sorted[sorted.length >> 1], max = sorted[sorted.length - 1];
      if (max < P.CHIRP_SNR * med) return null;
      // Earliest arrival = highest beat frequency among the strong peaks.
      const floor = max >= P.LEAD_Q * med ? P.LEAD * max : max;
      for (let k = pow.length - 1; k >= 0; k--) {
        if (pow[k] < floor) continue;
        if ((k > 0 && pow[k - 1] > pow[k]) || (k < pow.length - 1 && pow[k + 1] > pow[k])) continue;
        let off = 0;
        if (k > 0 && k < pow.length - 1) {
          const y0 = Math.sqrt(pow[k - 1]), y1 = Math.sqrt(pow[k]), y2 = Math.sqrt(pow[k + 1]), den = y0 - 2 * y1 + y2;
          if (den < 0) off = 0.5 * (y0 - y2) / den;
        }
        const b = this.beats[k] + off * (this.beats[1] - this.beats[0]);
        return { delta: -b / SWEEP * g.sr, q: max / med };
      }
      return null;
    }
    service(written) {
      const g = this.core.g;
      for (let i = this.cands.length - 1; i >= 0; i--) {
        const cd = this.cands[i];
        if (cd.delta === null) {              // confirm with the chirp once it has arrived
          const tc0 = cd.t3 + g.starts[1];
          if (tc0 > written) continue;
          const ch = this.chirpCheck(tc0);
          if (!ch) { this.cands.splice(i, 1); this.core.stats.nochirp++; continue; }
          cd.delta = ch.delta; cd.tq = ch.q;
          cd.base = Math.round(cd.t3 + cd.delta);   // marker timing corrected by the chirp
        }
        while (cd.syms.length < CODE) {      // read symbols whose windows have arrived
          const end = cd.base + g.starts[cd.syms.length + 2];
          if (end > written) break;
          const x = this.core.windowed(end), E = this.cTones.map(c => goertzel(x, c));
          let k1 = 0;
          for (let k = 1; k < P.NT; k++) if (E[k] > E[k1]) k1 = k;
          let k2 = k1 === 0 ? 1 : 0;
          for (let k = 0; k < P.NT; k++) if (k !== k1 && E[k] > E[k2]) k2 = k;
          cd.syms.push(k1); cd.ratio.push(E[k1] / (E[k2] + 1e-30));
        }
        if (cd.syms.length < CODE) continue;
        this.cands.splice(i, 1);
        const d = decode(cd.syms, cd.ratio);
        if (!d) { this.core.stats.bad++; continue; }
        const c = cd.base + g.starts[1], F = Math.round(P.FINE * g.sr);
        this.jobs.push({ f: d.f, word: d.word, tq: cd.tq, from: c - F, lag: c - F, to: c + F, env: [] });
      }
    }
    work(budget) {                            // final timing: chirp correlation around the estimate, spread over callbacks
      const g = this.core.g;
      while (this.jobs.length && budget > 0) {
        const j = this.jobs[0];
        while (j.lag <= j.to && budget-- > 0) { j.env.push(this.corr(j.lag)); j.lag++; }
        if (j.lag <= j.to) return;
        this.jobs.shift();
        const env = j.env, m = Math.max(...env), i = env.indexOf(m);
        let off = 0;
        if (i > 0 && i < env.length - 1) {
          const y0 = env[i - 1], y1 = env[i], y2 = env[i + 1], den = y0 - 2 * y1 + y2;
          if (den < 0) off = 0.5 * (y0 - y2) / den;
        }
        const tc = j.from + i + off;
        const endFrame = tc + g.starts[SLOTS - 1] - g.starts[1];
        if (Math.abs(endFrame - this.lastEnd) < g.S / 2) continue;
        this.lastEnd = endFrame;
        this.core.stats.ok++;
        this.core.onPacket(this, j.f, j.word, endFrame, 2 * m / g.N, j.tq);
      }
    }
    corr(end) {                               // |complex correlation| with the chirp whose full-level part ends at `end`
      const core = this.core, N = core.g.N, M = core.mask, ring = core.ring, tr = this.tr, ti = this.ti;
      let re = 0, im = 0, idx = (end - N) & M;
      for (let n = 0; n < N; n++) { const x = ring[idx]; re += x * tr[n]; im += x * ti[n]; idx = (idx + 1) & M; }
      return Math.hypot(re, im);
    }
  }

  // Where a clean marker's energy curve crosses 50%, relative to the end of its full-level part:
  // returns {rise, fall} in samples (crossing to true end, true end to crossing).
  function markerEdges(g, f) {
    const { R, N, win, sr } = g, len = 2 * R + N, pad = N + R, x = new Float32Array(pad + len + pad);
    for (let i = 0; i < len; i++) {
      const env = i < R ? 0.5 - 0.5 * Math.cos(Math.PI * i / R) : i < R + N ? 1 : 0.5 + 0.5 * Math.cos(Math.PI * (i - R - N) / R);
      x[pad + i] = env * Math.sin(2 * Math.PI * f * (i - R) / sr);
    }
    const c = 2 * Math.cos(2 * Math.PI * f / sr), w = new Float32Array(N), pts = [];
    for (let h = N; h <= x.length; h += 4) {
      for (let i = 0; i < N; i++) w[i] = x[h - N + i] * win[i];
      pts.push([h, goertzel(w, c)]);
    }
    const m = Math.max(...pts.map(p => p[1])), end = pad + R + N;
    const a = pts.findIndex(p => p[1] >= m / 2), b = pts.length - 1 - [...pts].reverse().findIndex(p => p[1] >= m / 2);
    return { rise: end - pts[a][0], fall: pts[b][0] - end };
  }

  function goertzel(x, c) {                   // power at one frequency (c = 2 cos w)
    let s1 = 0, s2 = 0;
    for (let i = 0; i < x.length; i++) { const s0 = x[i] + c * s1 - s2; s2 = s1; s1 = s0; }
    return s1 * s1 + s2 * s2 - c * s1 * s2;
  }

  /* ---------- The modem ---------- */
  class ModemCore {
    constructor(sr, post) {
      this.g = geometry(sr);
      this.post = post;
      this.mask = (1 << 17) - 1;              // 2.7 s of input at 48 kHz: holds a whole packet
      this.ring = new Float32Array(this.mask + 1);
      this.scratch = new Float32Array(this.g.N);
      this.rx = [];
      this.txf0 = null; this.gain = P.GAIN;
      this.st = { sess: 0, state: ST.HELLO, round: 0, payload: 0, drawAtFrame: null };
      this.pkt = null; this.slot = 0; this.restart = false;
      this.txLog = []; this.rt = [];
      this.stats = { ok: 0, bad: 0, cands: 0, nochirp: 0, sq: 0, n: 0 };
      this.nextStats = sr;
    }
    onMessage(m) {
      if (m.type === 'config') {
        if ('tx' in m) { this.txf0 = m.tx; this.pkt = null; }
        if (m.rx) this.rx = m.rx.map(b => new Rx(this, b.id, b.f0, b.f0 === this.txf0));
        if (m.gain != null) this.gain = m.gain;
      } else if (m.type === 'state') {
        const { type, ...st } = m;
        Object.assign(this.st, st);
        this.restart = true;                  // send the new state from the next slot boundary
      }
    }
    windowed(end) {                           // Hann-windowed copy of the N samples before `end`
      const { N, win } = this.g, x = this.scratch, M = this.mask, ring = this.ring;
      let idx = (end - N) & M;
      for (let i = 0; i < N; i++) { x[i] = ring[idx] * win[i]; idx = (idx + 1) & M; }
      return x;
    }
    newPacket(f) {
      const g = this.g, st = this.st;
      this.restart = false; this.slot = 0;
      const end = f + g.starts[SLOTS - 1] + g.R + g.N;
      let payload = st.payload;
      if (st.state === ST.ARMED && st.drawAtFrame != null)
        payload = Math.max(0, Math.min(8191, Math.round((st.drawAtFrame - end) / g.sr * 500)));   // 2 ms steps
      const syms = encode({ sess: st.sess, round: st.round, state: st.state, payload });
      this.pkt = { start: f, syms: [P.MARK, CHIRP, ...syms], end };
      this.txLog.push({ end, key: syms.join(',') });
      if (this.txLog.length > 16) this.txLog.shift();
    }
    txSample(f) {
      if (this.txf0 == null) return 0;
      const g = this.g;
      if (!this.pkt) this.newPacket(f);
      let rel = f - this.pkt.start;
      if (rel >= g.starts[this.slot + 1]) {
        this.slot++;
        if (this.slot >= SLOTS || this.restart) { this.newPacket(f); rel = 0; }
      }
      const local = rel - g.starts[this.slot], { R, N } = g;
      let env;
      if (local < R) env = 0.5 - 0.5 * Math.cos(Math.PI * local / R);
      else if (local < R + N) env = 1;
      else if (local < 2 * R + N) env = 0.5 + 0.5 * Math.cos(Math.PI * (local - R - N) / R);
      else return 0;
      const u = (local - R) / g.sr, sym = this.pkt.syms[this.slot];
      const ph = sym === CHIRP ? chirpPhase(this.txf0, u) : 2 * Math.PI * (this.txf0 + sym * P.DF) * u;
      return this.gain * env * Math.sin(ph);
    }
    onPacket(rx, f, word, endFrame, level, tq) {
      if (rx.own) {                           // our own packet, heard by our own microphone: measure the round trip
        if (tq < P.GOOD_TIMING) return;
        const key = word.join(',');
        const t = this.txLog.filter(e => e.key === key && e.end <= endFrame + 1 && endFrame - e.end < 0.6 * this.g.sr).pop();
        if (!t) return;
        this.rt.push(endFrame - t.end);
        if (this.rt.length > 7) this.rt.shift();
        const s = [...this.rt].sort((a, b) => a - b);
        this.post({ type: 'self', rtFrames: s[s.length >> 1], n: this.rt.length });
        return;
      }
      this.post({ type: 'packet', band: rx.id, ...f, endFrame, level, tq, goodTiming: tq >= P.GOOD_TIMING });
    }
    process(inp, out, frame0) {
      const n = out.length, M = this.mask, hop = this.g.hop;
      for (let i = 0; i < n; i++) {
        const f = frame0 + i, x = inp ? inp[i] : 0;
        this.ring[f & M] = x;
        this.stats.sq += x * x; this.stats.n++;
        if ((f + 1) % hop === 0 && this.rx.length) {
          const w = this.windowed(f + 1);
          for (const r of this.rx) r.onHop(f + 1, w);
        }
        out[i] = this.txSample(f);
      }
      const written = frame0 + n;
      for (const r of this.rx) r.service(written);
      for (const r of this.rx) if (r.jobs.length) { r.work(P.LAG_BUDGET); break; }
      if (written >= this.nextStats) {
        this.nextStats = written + this.g.sr;
        const s = this.stats;
        this.post({ type: 'stats', ok: s.ok, bad: s.bad, cands: s.cands, nochirp: s.nochirp,
          rmsDb: 10 * Math.log10(s.sq / Math.max(s.n, 1) + 1e-12), frame: written });
        s.sq = 0; s.n = 0;
      }
    }
  }

  const api = { P, PLANS, ST, SLOTS, CODE, INFO, bandTop, crc13, encode, decode, rsFill, geometry, ModemCore };
  G.QDModem = api;

  if (typeof registerProcessor === 'function') {
    class QDModemProcessor extends AudioWorkletProcessor {
      constructor() {
        super();
        this.core = new ModemCore(sampleRate, m => this.port.postMessage(m));
        this.port.onmessage = e => this.core.onMessage(e.data);
      }
      process(inputs, outputs) {
        const inp = inputs[0] && inputs[0][0], out = outputs[0];
        if (!out || !out[0]) return true;
        this.core.process(inp || null, out[0], currentFrame);
        for (let c = 1; c < out.length; c++) out[c].set(out[0]);
        return true;
      }
    }
    registerProcessor('qd-modem', QDModemProcessor);
  }
})(typeof globalThis !== 'undefined' ? globalThis : this);
