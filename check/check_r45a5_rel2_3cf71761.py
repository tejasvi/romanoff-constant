"""Exact checker v2 for the Romanov (Tao page 45a) combined lower-bound certificate (format r45a-v2).

Adversary LP (min sum_u w_u z_u), columns y[u,c] in [0, ymax], alpha[g] in [0, R0tail], Y[u] in [0, sum_c ymax[u,c]], z[u] in [0,1]:
  cap[u,c]: -y[u,c] + sum_{g|c} CAP*kap*n_u(c)*g*alpha_g >= -CAP*kap*n_u(c)*T(c)
  bud[c]:   -sum_u d_u y[u,c] + sum_{g|c} C1*kap*N(c)*g*alpha_g >= -C1*kap*N(c)*T(c),   N(c) = sum_u d_u n_u(c)
  tail:     -sum_g alpha_g >= -R0tail
  sum[u]:   sum_c y[u,c] - Y[u] >= 0
  epi[u,j]: z[u] + Y[u]/(s_u j (j+1)) >= 2/(j+1)          (any integer j >= 1)
w_u = norm * d_u * s_u, d_u = (#classes k mod ell in orbit u)/ell.  For any u >= 0: min >= u.b + sum_cols min(r*lo, r*hi).
Everything except the external constants in params is recomputed here (factorizations with primality proofs, tail
bounds in arb, residue patterns, orbits).  Usage: check_r45a5_rel2.py FAC.json CERT.json [LMAX] [FACBIG.json T1] [--tails-out TAILS.json]
v5: CORRECTED tail. Classes of squarefree m: (a) all primes of order <= T0 (DP, as before); (b) exactly one prime q from
M = {proven primes with T0 < ord_q(2) <= T1, q < 10^100} and the rest of order <= T0; (c) everything else.
T(c) <= T_a(c) + T_b(c) + gcd(c, PER) * (R0_up - R0_a - R0_b): T_b is computed (upper bound) from M, and R0_b (lower bound)
is the same class summed with 1/o_m. Floats are used for the class-(b) sums: positive terms, relative margin 1e-9.
v4: Lagrangian evaluation. Only the budget multipliers mu(c) >= 0 are read from the certificate; for each orbit the inner
minimum over its box is computed exactly (convex piecewise-linear in Y = sum_c y_c; greedy fill by increasing mu).
Bound = sum_u min_{0<=y<=ymax} [w_u phi(1 + Y/s_u) + d_u sum_c mu_c y_c] - sum_c mu_c C1 kap N(c) Teff(c)  (crude tail mode).
v3: optional R0_s extension by single factors q of Phi_t(2), T0 < t <= T1 (no primality needed: a composite counted as
one prime undercounts, so the lower bound stays valid); evaluated in float64 with a 1e-9 relative downward margin
(positive terms only; the rounding error of each sum of n terms is at most (n+3) 2^-53 relative)."""
import json, sys, math, time
from fractions import Fraction as Fr
from flint import fmpz, fmpz_poly, arb, fmpq, ctx
ctx.prec = 256

if not __debug__:
    sys.exit("refusing to run under python -O: every check must execute")
def req(cond, *msg):
    if not cond:
        print("FAIL: check failed:", *msg, flush=True)
        sys.exit(1)
CLAIM = None
if "--claim" in sys.argv:
    _i = sys.argv.index("--claim"); CLAIM = sys.argv[_i + 1]; del sys.argv[_i:_i + 2]
t_start = time.time()
def log(msg): print(f"{msg} ({time.time()-t_start:.0f}s)", flush=True)
fac = json.load(open(sys.argv[1])); cert = json.load(open(sys.argv[2]))
req(cert.get("format") == "r45a-v2")
CRUDE = cert.get("tail_mode", "alpha") == "crude"   # crude: tau(c) <= gcd(c, PER) * R0tail for every c (no alpha)
FACBIG = sys.argv[4] if len(sys.argv) > 5 else None; T1 = int(sys.argv[5]) if len(sys.argv) > 5 else 0
LMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 3_000_000
par = cert["params"]
ELL = [int(p) for p in par["ELL"]]
CAP = Fr(par["CAP"]); C1 = Fr(par["C1"]); C0up = Fr(par["C0_up"])
log2lo = Fr(par["log2_low"]); log2hi = Fr(par["log2_up"]); R0up = Fr(par["R0_up"])
# rel2 guards (referee r1): every external constant is bounded on BOTH sides, ELL is a set of distinct odd primes
req(Fr(8) <= CAP <= Fr(100) and Fr(67814, 10000) <= C1 <= Fr(100), "CAP/C1 out of range")
req(Fr(66016181584686958, 10**17) <= C0up <= Fr(1), "C0_up must be >= 0.66016181584686958 > C0 = 0.6601618158468695739...")
req(Fr(6931471805599453, 10**16) <= log2lo <= Fr(693147180559945309, 10**18), "log2_low must lie in [0.6931471805599453, 0.693147180559945309]")
req(Fr(693147180559945310, 10**18) <= log2hi <= Fr(6931471805599454, 10**16), "log2_up must lie in [0.693147180559945310, 0.6931471805599454]")
req(Fr(193656, 100000) <= R0up <= Fr(2), "R0_up must lie in [1.93656, 2]")
req(len(ELL) == len(set(ELL)) and all(p > 2 and fmpz(p).is_prime() for p in ELL), "ELL must be distinct odd primes")
print(f"[0] params: ELL={ELL} CAP={CAP} C1={C1} C0_up={C0up} log2 in [{log2lo}, {log2hi}] R0_up={R0up} "
      f"tail_mode={cert.get('tail_mode', 'alpha')} LMAX={LMAX} FACBIG={'yes, T1=' + str(T1) if FACBIG else 'no'}", flush=True)

# 1. factorizations of Phi_t(2), t <= T0 -> all primes with ord_p(2) <= T0
def pdiv(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return out
T0 = max(int(t) for t in fac)
req(sorted(int(t) for t in fac) == list(range(1, T0 + 1)))
prim = []
for ts, fl in fac.items():
    t = int(ts); v = fmpz(fmpz_poly.cyclotomic(t)(2)); prod = fmpz(1)
    for p, e in fl:
        req(fmpz(p).is_prime(), (t, p)); prod *= fmpz(p) ** int(e)
    req(prod == v, t)
    req(len({int(p) for p, e in fl}) == len(fl), ("duplicate prime in the factor list", t))   # rel2
    for p, e in fl:
        o = t
        for q in pdiv(t):
            while o % q == 0 and pow(2, o // q, p) == 1: o //= q
        req(pow(2, o, p) == 1)
        if o == t: prim.append((int(p), t))
        else: req(t % p == 0)
req(len({p for p, t in prim}) == len(prim))
ordm = {p: t for p, t in prim}
log(f"[1] factorizations verified to T0={T0}: {len(prim)} primes")
for p in ELL: req(p in ordm and p > 2)
PER = 1
for p in ELL: PER = PER * ordm[p] // math.gcd(PER, ordm[p])
req(PER == cert["PER"])
ell = 1; phil = 1
for p in ELL: ell *= p; phil *= p - 1

# 2. tails
def dp(plist):
    W = {1: arb(1)}; dropped = arb(0)
    for p, t in plist:
        f = arb(fmpq(1, p - 2)); new = dict(W)
        for L, w in W.items():
            L2 = L * t // math.gcd(L, t)
            if L2 > LMAX: dropped += w * f; continue
            new[L2] = new[L2] + w * f if L2 in new else w * f
        W = new
    return W, dropped
def fup(x): m, e = x.upper().man_exp(); return Fr(int(m)) * Fr(2) ** int(e)
def flo(x): m, e = x.lower().man_exp(); return Fr(int(m)) * Fr(2) ** int(e)
pt = sorted((p, t) for p, t in prim if p not in ELL)
W, dropped = dp(pt)
prodall = arb(1)
for p, t in pt: prodall *= 1 + arb(fmpq(1, p - 2))
prune = dropped * prodall * arb(fmpq(PER, LMAX))
Lg = {}
for L, w in W.items():
    g = math.gcd(L, PER); Lg[g] = Lg.get(g, arb(0)) + w * arb(fmpq(g, L))
T = [fup(sum((v for g, v in Lg.items() if c % g == 0), arb(0)) + prune) for c in range(PER)]
W2, _ = dp(sorted(prim))
R0s = sum((w * arb(fmpq(1, L)) for L, w in W2.items()), arb(0))
R0slo = flo(R0s)
Tb = [Fr(0)] * PER
if FACBIG:
    import numpy as np
    facb = json.load(open(FACBIG))
    Mt = {}                                         # order t -> list of proven primes q < 10^100 with ord_q(2) = t
    for t in range(T0 + 1, T1 + 1):
        fl = facb[str(t)]
        v = fmpz(fmpz_poly.cyclotomic(t)(2)); prod = fmpz(1)
        for q, e in fl: prod *= fmpz(q) ** int(e)
        req(prod == v, t)
        req(len({int(q) for q, e in fl}) == len(fl), ("duplicate prime in the factor list", t))   # rel2 (referee r1 (c))
        for q, e in fl:
            q = int(q)
            if math.gcd(q, t) != 1 or q >= 10 ** 100: continue
            req(fmpz(q).is_prime(), (t, q))
            req(pow(2, t, q) == 1 and all(pow(2, t // r, q) != 1 for r in pdiv(t)))     # exact order t
            Mt.setdefault(t, []).append(q)
    req(not (set(q for v in Mt.values() for q in v) & set(ELL)))
    def f_up(qs): return math.nextafter(float(sum((Fr(1, q - 2) for q in qs), Fr(0))), math.inf)
    def f_lo(qs): return math.nextafter(float(sum((Fr(1, q - 2) for q in qs), Fr(0))), 0.0)
    # class (b) for T: T-DP weights (primes of order <= T0 not dividing ell), upper endpoints
    LT = np.array(list(W.keys()), dtype=np.int64)
    wT = np.array([math.nextafter(float(w.upper()), math.inf) for w in W.values()])
    TbF = np.zeros(PER); Fsum = 0.0
    divs_ = [g for g in range(1, PER + 1) if PER % g == 0]
    for t, qs in Mt.items():
        Ft = f_up(qs); Fsum += Ft
        Lp = LT // np.gcd(LT, t) * t
        gp = np.gcd(Lp, PER)
        vals = wT * gp / Lp.astype(np.float64)
        A = {g: float(vals[gp == g].sum()) for g in divs_}
        for c in range(PER):
            TbF[c] += Ft * sum(A[g] for g in divs_ if c % g == 0)
    pruneb = float((dropped * prodall).upper()) * PER / LMAX * Fsum
    Tb = [Fr(math.nextafter(TbF[c] * (1 + 1e-9) + pruneb, math.inf)) for c in range(PER)]
    # class (b) for R0: all-small-primes DP weights, lower endpoints
    L2 = np.array(list(W2.keys()), dtype=np.int64)
    w2 = np.array([math.nextafter(float(w.lower()), 0.0) for w in W2.values()])
    req((w2 >= 0).all())
    R0b = 0.0
    for t, qs in Mt.items():
        R0b += f_lo(qs) * float(np.sum(w2 / (L2 // np.gcd(L2, t) * t).astype(np.float64)))
    R0b_lo = Fr(math.nextafter(R0b * (1 - 1e-9), 0.0))
    log(f"[2b] class (b): {sum(len(v) for v in Mt.values())} proven primes, orders {T0+1}..{T1}; T_b(0) <= {float(Tb[0]):.3e}; R0_b >= {float(R0b_lo):.9f}")
    R0slo += R0b_lo
T = [T[c] + Tb[c] for c in range(PER)]
R0tail = R0up - R0slo
req(R0tail > 0)
log(f"[2] T_up(0)={float(T[0]):.9f}  tail mass <= {float(R0tail):.4e}")
if "--tails-out" in sys.argv:
    json.dump(dict(ELL=ELL, PER=PER, T0=T0, T1=T1, LMAX=LMAX, T_up=[str(x) for x in T], R0s_low=str(R0slo), R0tail=str(R0tail)),
              open(sys.argv[sys.argv.index("--tails-out") + 1], "w"), indent=1)
    print("tails written"); sys.exit(0)

# 3. patterns and orbits (independent of the producer's code)
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
req(sum(pat.values()) == ell)
def canon(m):
    best = m; x = m
    for s in range(1, PER):
        x = ((x << 1) | (x >> (PER - 1))) & FULL
        if x < best: best = x
    return best
orb = {}
for ex, cnt in pat.items():
    m = FULL & ~ex
    if m: k = canon(m); orb[k] = orb.get(k, 0) + cnt
req(cert["n_orbits"] == len(orb))
od = {}
for rep, cnt in orb.items():
    U = [r for r in range(PER) if (rep >> r) & 1]; Us = set(U)
    od[rep] = (Fr(cnt, ell), len(U), [sum(1 for r in U if (r + c) % PER in Us) for c in range(PER)])
log(f"[3] patterns {len(pat)}, orbits {len(od)}")

# 4. Lagrangian bound with mu = budget multipliers (crude tail mode)
req(CRUDE, "v4 evaluates crude-tail certificates")
Pell = Fr(1)
for p in ELL: Pell *= Fr(p - 1, p - 2)
kap = C0up * Pell / (PER * log2lo)
norm = Fr(ell, phil) / (PER * log2hi)
Teff = [T[c] + math.gcd(c, PER) * R0tail for c in range(PER)]
Nc = [sum(d * n[c] for d, s, n in od.values()) for c in range(PER)]
mu = [Fr(0)] * PER
for key, val in cert["duals"]:
    if key[0] == "bud":
        x = Fr(val); req(x >= 0); mu[int(key[1])] += x
def phi(D):          # exact piecewise-linear interpolation of 1/x at integers, D >= 1
    j = D.numerator // D.denominator
    if Fr(j) == D: return Fr(1, j)
    return (2 * j + 1 - D) / (j * (j + 1))
order = sorted(range(PER), key=lambda c: mu[c])
B = -sum((mu[c] * C1 * kap * Nc[c] * Teff[c] for c in range(PER)), Fr(0))
for rep, (d, s, n) in od.items():
    caps = [(mu[c], CAP * kap * n[c] * Teff[c]) for c in order if n[c] > 0]
    cum = [Fr(0)]; cost = [Fr(0)]
    for m, cp in caps:
        cum.append(cum[-1] + cp); cost.append(cost[-1] + m * cp)
    Ymax = cum[-1]
    w = norm * d * s
    cand = set(cum)
    j = 1
    while s * (j - 1) <= Ymax:
        cand.add(Fr(s * (j - 1))); j += 1
    best = None
    for Y in cand:
        # K(Y): interpolate cost on the cumulative-capacity grid
        lo_i, hi_i = 0, len(cum) - 1
        while hi_i - lo_i > 1:
            mid = (lo_i + hi_i) // 2
            if cum[mid] <= Y: lo_i = mid
            else: hi_i = mid
        if cum[hi_i] == cum[lo_i]: K = cost[lo_i]
        else: K = cost[lo_i] + (Y - cum[lo_i]) * (cost[hi_i] - cost[lo_i]) / (cum[hi_i] - cum[lo_i])
        g = w * phi(1 + Y / s) + d * K
        if best is None or g < best: best = g
    B += best
log(f"[4] Lagrangian evaluation over {len(od)} orbits")
print(f"CERTIFIED: lower density of {{p + 2^a}} >= {float(B):.9f}")
print(f"rounded down: {math.floor(B * 10**6) / 10**6:.6f}")

if CLAIM is not None:
    _c = Fr(CLAIM)
    if B >= _c:
        print(f"PASS: certified bound >= claim {CLAIM}"); sys.exit(0)
    print(f"FAIL: certified bound {float(B):.9f} < claim {CLAIM}"); sys.exit(1)
