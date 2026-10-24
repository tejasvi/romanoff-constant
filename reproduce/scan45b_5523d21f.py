"""Float-only scoping scan for the 45a unconditional bound (mu = 0), with class (b) tails (orders T0+1..T1, no primality proofs).
Base = orbits of BASE_ELL; added primes enter as exact option sums (none: weight p - o_p; class j mod o_p: weight 1 each), which
is the CRT sum over k mod p (rotation argument).  Y = CAP kap sum_{g | PER} B_g sum_{a mod g} |U cap (a + gZ)|^2.
Usage: scan45b.py FAC300.json FAC1200.json BASE_ELL FIXED_ADD CANDS   (comma lists; FIXED_ADD always added, CANDS one at a time)"""
import json, math, sys, time
import numpy as np

t0 = time.time()
def log(m): print(f"{m} ({time.time()-t0:.0f}s)", flush=True)
fac = json.load(open(sys.argv[1])); facb = json.load(open(sys.argv[2]))
def ints(s): return [int(x) for x in s.split(",")] if s else []
BASE, FIXED, CANDS = ints(sys.argv[3]), ints(sys.argv[4]), ints(sys.argv[5])
LMAX, T1 = 3_000_000, 1200
CAP, C0, LOG2, R0UP = 8.0, 0.66016181584686958, 0.6931471805599453, 1.93656

def pdiv(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return out
prim = []
for ts, fl in fac.items():
    t = int(ts)
    for p, e in fl:
        p = int(p); o = t
        for q in pdiv(t):
            while o % q == 0 and pow(2, o // q, p) == 1: o //= q
        if o == t: prim.append((p, t))
ordm = dict(prim)
T0 = max(int(t) for t in fac)
Mt = {}
for t in range(T0 + 1, T1 + 1):
    for q, e in facb[str(t)]:
        q = int(q)
        if math.gcd(q, t) != 1 or q >= 10 ** 100: continue
        if pow(2, t, q) == 1 and all(pow(2, t // r, q) != 1 for r in pdiv(t)): Mt.setdefault(t, []).append(q)
Ft = {t: sum(1.0 / (q - 2) for q in qs) for t, qs in Mt.items()}

def dp(plist):
    W = {1: 1.0}; dropped = 0.0
    for p, t in plist:
        f = 1.0 / (p - 2); new = dict(W)
        for L, w in W.items():
            L2 = L * t // math.gcd(L, t)
            if L2 > LMAX: dropped += w * f; continue
            new[L2] = new.get(L2, 0.0) + w * f
        W = new
    return W, dropped
W2, _ = dp(sorted(prim))
L2a = np.array(list(W2.keys()), dtype=np.int64); w2a = np.array(list(W2.values()))
R0a = float(np.sum(w2a / L2a))
R0b = sum(F * float(np.sum(w2a / (L2a // np.gcd(L2a, t) * t))) for t, F in Ft.items())
R0tail = R0UP - R0a - R0b
log(f"class (a) {len(prim)} primes R0_a {R0a:.9f}; class (b) {sum(len(v) for v in Mt.values())} primes R0_b {R0b:.9f}; tail {R0tail:.4e}")

_dpc = {}
def coeffs(ELL, PER):
    """B_g for g | PER with Teff(c) = sum_{g | PER, g | c} B_g."""
    key = tuple(sorted(ELL))
    if key not in _dpc:
        pt = sorted((p, t) for p, t in prim if p not in ELL)
        W, dropped = dp(pt)
        prodall = 1.0
        for p, t in pt: prodall *= 1 + 1.0 / (p - 2)
        _dpc[key] = (np.array(list(W.keys()), dtype=np.int64), np.array(list(W.values())), dropped * prodall)
    LT, wT, dprod = _dpc[key]
    divs = [g for g in range(1, PER + 1) if PER % g == 0]
    B = {g: 0.0 for g in divs}
    gp = np.gcd(LT, PER)
    for g in divs: B[g] += float(np.sum((wT * gp / LT)[gp == g]))
    Fsum = 0.0
    for t, F in Ft.items():
        Fsum += F
        Lp = LT // np.gcd(LT, t) * t; gq = np.gcd(Lp, PER); vals = wT * gq / Lp
        for g in divs: B[g] += F * float(vals[gq == g].sum())
    B[1] += dprod * PER / LMAX * (1 + Fsum)
    for g in divs:
        phi = sum(1 for a in range(1, g + 1) if math.gcd(a, g) == 1)
        B[g] += phi * R0tail
    return B

def lcm(a, b): return a * b // math.gcd(a, b)

def base_orbits(ELL):
    PER = 1
    for p in ELL: PER = lcm(PER, ordm[p])
    FULL = (1 << PER) - 1
    pat = {0: 1}
    for p in ELL:
        o = ordm[p]; pw = {pow(2, r, p): r for r in range(o)}; opts = {}
        for k in range(p):
            m = 0
            if k in pw:
                for r in range(pw[k], PER, o): m |= 1 << r
            opts[m] = opts.get(m, 0) + 1
        new = {}
        for ex, cnt in pat.items():
            for m, c in opts.items(): new[ex | m] = new.get(ex | m, 0) + cnt * c
        pat = new
    items = [(FULL & ~ex, c) for ex, c in pat.items() if FULL & ~ex]
    def canon(m):
        best = m; x = m
        for s in range(1, PER):
            x = ((x << 1) | (x >> (PER - 1))) & FULL
            if x < best: best = x
        return best
    d = {}
    for m, c in items:
        k = canon(m); d[k] = d.get(k, 0) + c
    X = np.array([[(m >> r) & 1 for r in range(PER)] for m in d], dtype=np.float64)
    cnt = np.array(list(d.values()), dtype=np.float64)
    log(f"base ELL={ELL} PER={PER} patterns={len(pat)} orbits={len(d)}")
    return PER, X, cnt

def expand(X, w, PER0, p, PER):
    """lift rows to PER and expand by the k mod p options."""
    o = ordm[p]
    Xl = np.tile(X, (1, PER // PER0))
    rows = [Xl]; ws = [w * (p - o)]
    for j in range(o):
        Xj = Xl.copy(); Xj[:, j::o] = 0
        rows.append(Xj); ws.append(w.copy())
    Xn = np.vstack(rows); wn = np.concatenate(ws)
    keep = Xn.sum(axis=1) > 0
    return Xn[keep], wn[keep]

def bound(ELL, PER, X, w):
    B = coeffs(ELL, PER)
    ell = 1; phil = 1; Pl = 1.0
    for p in ELL: ell *= p; phil *= p - 1; Pl *= (p - 1) / (p - 2)
    kap = C0 * Pl / (PER * LOG2); norm = (ell / phil) / (PER * LOG2)
    tot = 0.0
    for i in range(0, X.shape[0], 50000):
        Xc = X[i:i + 50000]; n = Xc.shape[0]
        s = Xc.sum(axis=1)
        Q = np.zeros(n)
        for g, b in B.items():
            cnts = Xc.reshape(n, PER // g, g).sum(axis=1)
            Q += b * (cnts * cnts).sum(axis=1)
        D = 1 + CAP * kap * Q / s
        j = np.floor(D)
        tot += float(np.dot(w[i:i + 50000], s * (2 * j + 1 - D) / (j * (j + 1))))
    return norm / ell * tot

PER0, X0, w0 = base_orbits(BASE)
ELL = list(BASE); PER = PER0; X, w = X0, w0
log(f"bound BASE = {bound(ELL, PER, X, w):.9f}")
for p in FIXED:
    PERn = lcm(PER, ordm[p])
    X, w = expand(X, w, PER, p, PERn); PER = PERn; ELL = ELL + [p]
    log(f"bound +{p} (PER {PER}, rows {len(w)}) = {bound(ELL, PER, X, w):.9f}")
b0 = bound(ELL, PER, X, w)
for p in CANDS:
    PERn = lcm(PER, ordm[p])
    bl = bound(ELL, PERn, np.tile(X, (1, PERn // PER)), w) if PERn != PER else b0
    Xn, wn = expand(X, w, PER, p, PERn)
    b1 = bound(ELL + [p], PERn, Xn, wn)
    log(f"cand +{p} (ord {ordm[p]}, PER {PERn}, rows {len(wn)}): {b1:.9f}  gain {b1 - b0:+.3e}  (lifted-only {bl - b0:+.3e})")
