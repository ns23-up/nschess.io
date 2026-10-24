const Chess = (function () {
  'use strict';
  // Piece codes: 1 pawn, 2 knight, 3 bishop, 4 rook, 5 queen, 6 king. White positive, black negative.
  // Squares: 0 = a8 ... 63 = h1 (row = idx >> 3 from the 8th rank down, col = idx & 7).
  const P = 1, N = 2, B = 3, R = 4, Q = 5, K = 6;
  const VAL = [0, 100, 320, 330, 500, 900, 0];
  const FILES = 'abcdefgh';
  const INF = 1000000, MATE = 100000;
  const sqName = (i) => FILES[i & 7] + (8 - (i >> 3));
  const sqIdx = (n) => (8 - Number(n[1])) * 8 + FILES.indexOf(n[0]);

  const KN = [[-2, -1], [-2, 1], [-1, -2], [-1, 2], [1, -2], [1, 2], [2, -1], [2, 1]];
  const KG = [[-1, -1], [-1, 0], [-1, 1], [0, -1], [0, 1], [1, -1], [1, 0], [1, 1]];
  const DG = [[-1, -1], [-1, 1], [1, -1], [1, 1]];
  const OR = [[-1, 0], [1, 0], [0, -1], [0, 1]];
  const RIGHTS_MASK = { 0: 8, 4: 12, 7: 4, 56: 2, 60: 3, 63: 1 };

  function initState() {
    const b = new Int8Array(64);
    const back = [R, N, B, Q, K, B, N, R];
    for (let i = 0; i < 8; i++) {
      b[i] = -back[i]; b[8 + i] = -P; b[48 + i] = P; b[56 + i] = back[i];
    }
    return { b, t: 1, c: 15, ep: -1, hm: 0, fm: 1 };
  }

  function fromFen(fen) {
    const parts = fen.split(' ');
    const b = new Int8Array(64);
    let i = 0;
    const map = { p: 1, n: 2, b: 3, r: 4, q: 5, k: 6 };
    for (const ch of parts[0]) {
      if (ch === '/') continue;
      if (ch >= '1' && ch <= '8') { i += Number(ch); continue; }
      const lower = ch.toLowerCase();
      b[i++] = ch === lower ? -map[lower] : map[lower];
    }
    let c = 0;
    const ca = parts[2] || '-';
    if (ca.includes('K')) c |= 1;
    if (ca.includes('Q')) c |= 2;
    if (ca.includes('k')) c |= 4;
    if (ca.includes('q')) c |= 8;
    return {
      b, t: parts[1] === 'b' ? -1 : 1, c,
      ep: !parts[3] || parts[3] === '-' ? -1 : sqIdx(parts[3]),
      hm: Number(parts[4] || 0), fm: Number(parts[5] || 1)
    };
  }

  function attacked(b, sq, by) {
    const r = sq >> 3, c = sq & 7;
    const pr = r + by;
    if (pr >= 0 && pr < 8) {
      if (c > 0 && b[pr * 8 + c - 1] === by * P) return true;
      if (c < 7 && b[pr * 8 + c + 1] === by * P) return true;
    }
    for (let i = 0; i < 8; i++) {
      const rr = r + KN[i][0], cc = c + KN[i][1];
      if (rr >= 0 && rr < 8 && cc >= 0 && cc < 8 && b[rr * 8 + cc] === by * N) return true;
    }
    for (let i = 0; i < 8; i++) {
      const rr = r + KG[i][0], cc = c + KG[i][1];
      if (rr >= 0 && rr < 8 && cc >= 0 && cc < 8 && b[rr * 8 + cc] === by * K) return true;
    }
    for (let i = 0; i < 4; i++) {
      const dr = DG[i][0], dc = DG[i][1];
      let rr = r + dr, cc = c + dc;
      while (rr >= 0 && rr < 8 && cc >= 0 && cc < 8) {
        const p = b[rr * 8 + cc];
        if (p !== 0) { if (p === by * B || p === by * Q) return true; break; }
        rr += dr; cc += dc;
      }
    }
    for (let i = 0; i < 4; i++) {
      const dr = OR[i][0], dc = OR[i][1];
      let rr = r + dr, cc = c + dc;
      while (rr >= 0 && rr < 8 && cc >= 0 && cc < 8) {
        const p = b[rr * 8 + cc];
        if (p !== 0) { if (p === by * R || p === by * Q) return true; break; }
        rr += dr; cc += dc;
      }
    }
    return false;
  }

  function kingSq(b, color) {
    const k = color * K;
    for (let i = 0; i < 64; i++) if (b[i] === k) return i;
    return -1;
  }

  function inCheck(s) { return attacked(s.b, kingSq(s.b, s.t), -s.t); }

  function pseudo(s, capsOnly) {
    const b = s.b, t = s.t, out = [];
    const promos = [Q, R, B, N];
    for (let f = 0; f < 64; f++) {
      const p = b[f];
      if (p === 0 || p * t < 0) continue;
      const a = p * t;
      const r = f >> 3, c = f & 7;
      if (a === P) {
        const dir = -t, nr = r + dir;
        if (nr < 0 || nr > 7) continue;
        const promoRow = t === 1 ? 0 : 7, startRow = t === 1 ? 6 : 1;
        if ((!capsOnly || nr === promoRow) && b[nr * 8 + c] === 0) {
          const to = nr * 8 + c;
          if (nr === promoRow) {
            for (const pp of promos) out.push({ f, t: to, p: pp, fl: 0 });
          } else {
            out.push({ f, t: to, p: 0, fl: 0 });
            if (r === startRow && b[(nr + dir) * 8 + c] === 0) out.push({ f, t: (nr + dir) * 8 + c, p: 0, fl: 'dbl' });
          }
        }
        for (let k = -1; k <= 1; k += 2) {
          const cc = c + k;
          if (cc < 0 || cc > 7) continue;
          const to = nr * 8 + cc, tp = b[to];
          if (tp !== 0 && tp * t < 0) {
            if (nr === promoRow) { for (const pp of promos) out.push({ f, t: to, p: pp, fl: 0 }); }
            else out.push({ f, t: to, p: 0, fl: 0 });
          } else if (tp === 0 && to === s.ep) {
            out.push({ f, t: to, p: 0, fl: 'ep' });
          }
        }
      } else if (a === N || a === K) {
        const dirs = a === N ? KN : KG;
        for (let i = 0; i < 8; i++) {
          const rr = r + dirs[i][0], cc = c + dirs[i][1];
          if (rr < 0 || rr > 7 || cc < 0 || cc > 7) continue;
          const to = rr * 8 + cc, tp = b[to];
          if (tp === 0) { if (!capsOnly) out.push({ f, t: to, p: 0, fl: 0 }); }
          else if (tp * t < 0) out.push({ f, t: to, p: 0, fl: 0 });
        }
        if (a === K && !capsOnly) {
          if (t === 1 && f === 60) {
            if ((s.c & 1) && b[61] === 0 && b[62] === 0 && b[63] === R &&
              !attacked(b, 60, -1) && !attacked(b, 61, -1) && !attacked(b, 62, -1))
              out.push({ f: 60, t: 62, p: 0, fl: 'K' });
            if ((s.c & 2) && b[59] === 0 && b[58] === 0 && b[57] === 0 && b[56] === R &&
              !attacked(b, 60, -1) && !attacked(b, 59, -1) && !attacked(b, 58, -1))
              out.push({ f: 60, t: 58, p: 0, fl: 'Q' });
          } else if (t === -1 && f === 4) {
            if ((s.c & 4) && b[5] === 0 && b[6] === 0 && b[7] === -R &&
              !attacked(b, 4, 1) && !attacked(b, 5, 1) && !attacked(b, 6, 1))
              out.push({ f: 4, t: 6, p: 0, fl: 'K' });
            if ((s.c & 8) && b[3] === 0 && b[2] === 0 && b[1] === 0 && b[0] === -R &&
              !attacked(b, 4, 1) && !attacked(b, 3, 1) && !attacked(b, 2, 1))
              out.push({ f: 4, t: 2, p: 0, fl: 'Q' });
          }
        }
      } else {
        const dirs = a === B ? DG : a === R ? OR : null;
        const lists = dirs ? [dirs] : [DG, OR];
        for (const list of lists) {
          for (let i = 0; i < 4; i++) {
            const dr = list[i][0], dc = list[i][1];
            let rr = r + dr, cc = c + dc;
            while (rr >= 0 && rr < 8 && cc >= 0 && cc < 8) {
              const to = rr * 8 + cc, tp = b[to];
              if (tp === 0) { if (!capsOnly) out.push({ f, t: to, p: 0, fl: 0 }); }
              else { if (tp * t < 0) out.push({ f, t: to, p: 0, fl: 0 }); break; }
              rr += dr; cc += dc;
            }
          }
        }
      }
    }
    return out;
  }

  function make(s, m) {
    const b = s.b.slice();
    const t = s.t, pc = b[m.f], ap = pc * t;
    const captured = b[m.t] !== 0 || m.fl === 'ep';
    b[m.t] = pc; b[m.f] = 0;
    let ep = -1, c = s.c;
    if (m.fl === 'ep') b[m.t + (t === 1 ? 8 : -8)] = 0;
    else if (m.fl === 'dbl') ep = (m.f + m.t) >> 1;
    if (m.p) b[m.t] = t * m.p;
    if (m.fl === 'K') {
      if (t === 1) { b[61] = b[63]; b[63] = 0; } else { b[5] = b[7]; b[7] = 0; }
    } else if (m.fl === 'Q') {
      if (t === 1) { b[59] = b[56]; b[56] = 0; } else { b[3] = b[0]; b[0] = 0; }
    }
    if (ap === K) c &= t === 1 ? ~3 : ~12;
    c &= ~(RIGHTS_MASK[m.f] || 0);
    c &= ~(RIGHTS_MASK[m.t] || 0);
    return { b, t: -t, c, ep, hm: (ap === P || captured) ? 0 : s.hm + 1, fm: s.fm + (t === -1 ? 1 : 0) };
  }

  function legal(s) {
    const ps = pseudo(s, false), out = [];
    for (const m of ps) {
      const ns = make(s, m);
      if (!attacked(ns.b, kingSq(ns.b, s.t), -s.t)) out.push(m);
    }
    return out;
  }

  function perft(s, d) {
    if (d === 0) return 1;
    const ms = legal(s);
    if (d === 1) return ms.length;
    let n = 0;
    for (const m of ms) n += perft(make(s, m), d - 1);
    return n;
  }

  // ---------- notation ----------
  const LET = { 2: 'N', 3: 'B', 4: 'R', 5: 'Q', 6: 'K' };
  function toSan(s, m, legalMoves) {
    const pc = Math.abs(s.b[m.f]);
    let out;
    if (m.fl === 'K') out = 'O-O';
    else if (m.fl === 'Q') out = 'O-O-O';
    else {
      const cap = s.b[m.t] !== 0 || m.fl === 'ep';
      if (pc === P) {
        out = cap ? FILES[m.f & 7] + 'x' + sqName(m.t) : sqName(m.t);
        if (m.p) out += '=' + LET[m.p];
      } else {
        out = LET[pc];
        const others = legalMoves.filter((o) => o.f !== m.f && o.t === m.t && Math.abs(s.b[o.f]) === pc);
        if (others.length) {
          const sameFile = others.some((o) => (o.f & 7) === (m.f & 7));
          const sameRank = others.some((o) => (o.f >> 3) === (m.f >> 3));
          if (!sameFile) out += FILES[m.f & 7];
          else if (!sameRank) out += 8 - (m.f >> 3);
          else out += sqName(m.f);
        }
        if (cap) out += 'x';
        out += sqName(m.t);
      }
    }
    const ns = make(s, m);
    if (inCheck(ns)) out += legal(ns).length ? '+' : '#';
    return out;
  }

  const PROMO_CH = { 5: 'q', 4: 'r', 3: 'b', 2: 'n' };
  function encode(m) { return sqName(m.f) + sqName(m.t) + (m.p ? PROMO_CH[m.p] : ''); }
  function decode(s, code) {
    if (typeof code !== 'string' || code.length < 4) return null;
    const f = sqIdx(code.slice(0, 2)), t = sqIdx(code.slice(2, 4));
    const pr = code[4] ? Number(Object.keys(PROMO_CH).find((k) => PROMO_CH[k] === code[4])) : 0;
    return legal(s).find((m) => m.f === f && m.t === t && (m.p || 0) === pr) || null;
  }

  // ---------- game status ----------
  function posKey(s) {
    let k = '';
    for (let i = 0; i < 64; i++) k += String.fromCharCode(s.b[i] + 70);
    return k + s.t + s.c + s.ep;
  }

  function insufficient(b) {
    let minors = 0;
    for (let i = 0; i < 64; i++) {
      const a = Math.abs(b[i]);
      if (a === P || a === R || a === Q) return false;
      if (a === N || a === B) minors++;
    }
    return minors <= 1;
  }

  function hasMatingMaterial(b, color) {
    let minors = 0;
    for (let i = 0; i < 64; i++) {
      const p = b[i];
      if (p * color <= 0) continue;
      const a = p * color;
      if (a === P || a === R || a === Q) return true;
      if (a === N || a === B) minors++;
    }
    return minors >= 2;
  }

  function status(s, keys) {
    const chk = inCheck(s);
    if (!legal(s).length) return chk ? { over: true, type: 'mate', winner: -s.t } : { over: true, type: 'stalemate' };
    if (insufficient(s.b)) return { over: true, type: 'insufficient' };
    if (s.hm >= 100) return { over: true, type: 'fifty' };
    const k = keys[keys.length - 1];
    let n = 0;
    for (const x of keys) if (x === k) n++;
    if (n >= 3) return { over: true, type: 'repetition' };
    return { over: false, check: chk };
  }

  // ---------- evaluation and search ----------
  const PST = {
    1: [0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 10, 10, 20, 30, 30, 20, 10, 10, 5, 5, 10, 25, 25, 10, 5, 5,
      0, 0, 0, 20, 20, 0, 0, 0, 5, -5, -10, 0, 0, -10, -5, 5, 5, 10, 10, -20, -20, 10, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0],
    2: [-50, -40, -30, -30, -30, -30, -40, -50, -40, -20, 0, 0, 0, 0, -20, -40, -30, 0, 10, 15, 15, 10, 0, -30, -30, 5, 15, 20, 20, 15, 5, -30,
      -30, 0, 15, 20, 20, 15, 0, -30, -30, 5, 10, 15, 15, 10, 5, -30, -40, -20, 0, 5, 5, 0, -20, -40, -50, -40, -30, -30, -30, -30, -40, -50],
    3: [-20, -10, -10, -10, -10, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 10, 10, 5, 0, -10, -10, 5, 5, 10, 10, 5, 5, -10,
      -10, 0, 10, 10, 10, 10, 0, -10, -10, 10, 10, 10, 10, 10, 10, -10, -10, 5, 0, 0, 0, 0, 5, -10, -20, -10, -10, -10, -10, -10, -10, -20],
    4: [0, 0, 0, 0, 0, 0, 0, 0, 5, 10, 10, 10, 10, 10, 10, 5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5,
      -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 5, 5, 0, 0, 0],
    5: [-20, -10, -10, -5, -5, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 5, 5, 5, 0, -10, -5, 0, 5, 5, 5, 5, 0, -5,
      0, 0, 5, 5, 5, 5, 0, -5, -10, 5, 5, 5, 5, 5, 0, -10, -10, 0, 5, 0, 0, 0, 0, -10, -20, -10, -10, -5, -5, -10, -10, -20]
  };
  const KING_MID = [-30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30,
    -30, -40, -40, -50, -50, -40, -40, -30, -20, -30, -30, -40, -40, -30, -30, -20, -10, -20, -20, -20, -20, -20, -20, -10,
    20, 20, 0, 0, 0, 0, 20, 20, 20, 30, 10, 0, 0, 10, 30, 20];
  const KING_END = [-50, -40, -30, -20, -20, -30, -40, -50, -30, -20, -10, 0, 0, -10, -20, -30, -30, -10, 20, 30, 30, 20, -10, -30,
    -30, -10, 30, 40, 40, 30, -10, -30, -30, -10, 30, 40, 40, 30, -10, -30, -30, -10, 20, 30, 30, 20, -10, -30,
    -30, -30, 0, 0, 0, 0, -30, -30, -50, -30, -30, -30, -30, -30, -30, -50];

  function evaluate(s) {
    const b = s.b;
    let nonPawn = 0;
    for (let i = 0; i < 64; i++) {
      const a = Math.abs(b[i]);
      if (a > P && a < K) nonPawn += VAL[a];
    }
    const endgame = nonPawn < 2400;
    let score = 0;
    for (let i = 0; i < 64; i++) {
      const p = b[i];
      if (p === 0) continue;
      const a = p > 0 ? p : -p;
      const idx = p > 0 ? i : i ^ 56;
      const pst = a === K ? (endgame ? KING_END[idx] : KING_MID[idx]) : PST[a][idx];
      score += (p > 0 ? 1 : -1) * (VAL[a] + pst);
    }
    return score * s.t + 8;
  }

  function orderMoves(b, ms, hist) {
    for (const m of ms) {
      const cap = b[m.t];
      let sc = 0;
      if (cap !== 0) sc = 10000 + 10 * VAL[Math.abs(cap)] - VAL[Math.abs(b[m.f])] / 10;
      else if (m.fl === 'ep') sc = 10000 + 1000;
      else if (hist) sc = hist[m.f * 64 + m.t];
      if (m.p) sc += 9000 + VAL[m.p];
      m.o = sc;
    }
    ms.sort((x, y) => y.o - x.o);
  }

  function qsearch(s, alpha, beta, ply, ctx) {
    if (ctx.stop) return 0;
    if ((++ctx.nodes & 2047) === 0 && Date.now() > ctx.deadline) { ctx.stop = true; return 0; }
    const stand = evaluate(s);
    if (ply > 14) return stand;
    if (stand >= beta) return stand;
    let best = stand;
    if (stand > alpha) alpha = stand;
    const ms = pseudo(s, true);
    orderMoves(s.b, ms, null);
    for (const m of ms) {
      const ns = make(s, m);
      if (attacked(ns.b, kingSq(ns.b, s.t), -s.t)) continue;
      const sc = -qsearch(ns, -beta, -alpha, ply + 1, ctx);
      if (ctx.stop) return 0;
      if (sc > best) best = sc;
      if (sc > alpha) alpha = sc;
      if (alpha >= beta) break;
    }
    return best;
  }

  function negamax(s, depth, alpha, beta, ply, ctx) {
    if (ctx.stop) return 0;
    if ((++ctx.nodes & 2047) === 0 && Date.now() > ctx.deadline) { ctx.stop = true; return 0; }
    const inChk = attacked(s.b, kingSq(s.b, s.t), -s.t);
    if (inChk && ply < 8) depth++;
    if (depth <= 0) return qsearch(s, alpha, beta, ply, ctx);
    if (s.hm >= 100) return 0;
    const ms = pseudo(s, false);
    orderMoves(s.b, ms, ctx.hist);
    let best = -INF, count = 0;
    for (const m of ms) {
      const ns = make(s, m);
      if (attacked(ns.b, kingSq(ns.b, s.t), -s.t)) continue;
      count++;
      const sc = -negamax(ns, depth - 1, -beta, -alpha, ply + 1, ctx);
      if (ctx.stop) return 0;
      if (sc > best) best = sc;
      if (sc > alpha) alpha = sc;
      if (alpha >= beta) {
        if (s.b[m.t] === 0) ctx.hist[m.f * 64 + m.t] += depth * depth;
        break;
      }
    }
    if (count === 0) return inChk ? -MATE + ply : 0;
    return best;
  }

  function shuffle(a) {
    for (let i = a.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      const x = a[i]; a[i] = a[j]; a[j] = x;
    }
    return a;
  }

  // opts: { depth, time (ms), noise (centipawns) }
  function bestMove(s, opts) {
    const ms = legal(s);
    if (!ms.length) return null;
    if (ms.length === 1) return ms[0];
    const ctx = { nodes: 0, stop: false, deadline: Date.now() + opts.time, hist: new Int32Array(4096) };
    shuffle(ms);
    orderMoves(s.b, ms, ctx.hist);
    let best = ms[0];
    for (let d = 1; d <= opts.depth; d++) {
      let alpha = -INF, curBest = null, curScore = -INF;
      for (const m of ms) {
        const ns = make(s, m);
        let sc;
        if (opts.noise > 0) {
          sc = -negamax(ns, d - 1, -INF, INF, 1, ctx);
          if (ctx.stop) break;
          sc += (Math.random() - 0.5) * 2 * opts.noise;
        } else {
          sc = -negamax(ns, d - 1, -INF, -alpha, 1, ctx);
          if (ctx.stop) break;
        }
        if (sc > curScore) { curScore = sc; curBest = m; }
        if (sc > alpha) alpha = sc;
      }
      if (ctx.stop) break;
      best = curBest;
      const i = ms.indexOf(curBest);
      ms.splice(i, 1); ms.unshift(curBest);
      if (curScore > MATE - 100) break;
    }
    return { f: best.f, t: best.t, p: best.p, fl: best.fl };
  }

  return {
    P, N, B, R, Q, K, VAL, sqName, sqIdx, initState, fromFen, attacked, kingSq, inCheck, pseudo, make, legal, perft,
    toSan, encode, decode, posKey, insufficient, hasMatingMaterial, status, evaluate, bestMove
  };
})();
if (typeof module !== 'undefined') module.exports = Chess;
