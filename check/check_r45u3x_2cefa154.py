"""Exact checker u3x for the Romanov (Tao page 45a) lower bound: rel2 (check_r45a5_rel2_3cf71761.py) plus formats r45a-u3
and r45a-u3x.  Usage: check_r45u3x.py FAC.json CERT.json [LMAX] [FACBIG.json T1] [--claim X] [--workers N]

r45a-u3x = r45a-u3 with ADDED primes evaluated as exact option sums.  ELL = BASE + ADD (all of ELL enters the tails, kappa,
the normalization and PER = lcm of all orders).  The residue patterns are enumerated for BASE only (period PER0 | PER), and
reduced to rotation orbits as in step [3].  For k = (k_BASE, k_ADD) by CRT, U_k = U(k_BASE) cap U(k_ADD) (masks lifted to
period PER), and U(k_ADD) excludes, for each added p, nothing (p - o_p residues k_p) or the class r = j mod o_p (k_p = 2^j,
one residue each).  If U(k_BASE) = U_rep + t, then sum over k_ADD of F(U(k_BASE) cap U(k_ADD)) = sum over k_ADD of
F(U_rep cap U(2^-t k_ADD)) = sum over k_ADD of F(U_rep cap U(k_ADD)), for every rotation-invariant F; so every class k mod ell
is counted exactly once with weight cnt(orbit) x (option weight).  T(c) is rounded UP to the grid 2^-40 (still an upper bound)
so that all orbit sums are exact int64 / Python-int arithmetic; the Pintz index j of each row is chosen in floating point at
alpha_j (any integer j >= 1 is valid, so this affects only the tightness).
Conditional variant (certificate field "mu" > 0; uses (I2) with the budget constant C1): Lagrangian relaxation of the budget
rows with ONE uniform multiplier mu >= 0, and weak duality on the caps of each row with multiplier lambda_r = (omega_r/ell) nu_j
>= 0 (omega_r = class count, j = the row's group): for every alpha in the simplex,
  row value >= (omega_r/ell) [s_r h_j - nu_j CAP kap (Q_r + tau_r(alpha))],  h_j = min_{i >= 1} (norm/i + (mu + nu_j)(i - 1)),
because inf_{y >= 0} [w phi(1 + Y/s) + (d mu + lambda) Y] is attained at an integer D = 1 + Y/s (phi is convex, piecewise linear
with kinks at the integers). The budget term is -mu C1 kap (1/ell) sum_r omega_r (Q_r + tau_r(alpha)). Everything is affine and
nonincreasing in alpha, so again the minimum over the simplex is at a vertex. nu_j = max(0, norm/(j(j+1)) - mu) (any nu_j >= 0
is valid). mu = 0 gives nu_j = norm/(j(j+1)), h_j = 2 norm/(j+1): exactly the unconditional minorant.

r45a-u3 (unconditional, adversarial class-(c) tail).  The budget rows are dropped (a relaxation of the adversary, so the
bound stays valid and uses no Lichtman input); with no budget the adversary fills every cap, so for a fixed tail vector alpha
  B(alpha) = sum_u w_u phi(1 + Y_u(alpha)/s_u),   Y_u(alpha) = CAP kap sum_c n_u(c) (T(c) + sum_{g | PER, g | c} g alpha_g),
and the bound is min B(alpha) over the simplex alpha_g >= 0 (g | PER), sum_g alpha_g <= R0tail (the v1 tail form; here with
the class-(b) tail mass).  Certificate: a point alpha_j of the simplex (given as fractions of R0tail).  For each orbit the
checker takes the Pintz index j_u = floor(1 + Y_u(alpha_j)/s_u) and uses phi(D) >= (2j + 1 - D)/(j (j+1)) (valid for every
integer j >= 1).  The resulting minorant is affine and nonincreasing in alpha, so its minimum over the simplex is attained at
a vertex alpha = R0tail e_g; the checker evaluates all vertices (and alpha = 0) exactly and certifies the smallest value.
The choice of alpha_j affects only the tightness, never the validity.  Steps [0]-[3] are rel2's code unchanged.

Exact checker v2 for the Romanov (Tao page 45a) combined lower-bound certificate (format r45a-v2).

Adversary LP (min sum_u w_u z_u), columns y[u,c] in [0, ymax], alpha[g] in [0, R0tail], Y[u] in [0, sum_c ymax[u,c]], z[u] in [0,1]:
  cap[u,c]: -y[u,c] + sum_{g|c} CAP*kap*n_u(c)*g*alpha_g >= -CAP*kap*n_u(c)*T(c)
  bud[c]:   -sum_u d_u y[u,c] + sum_{g|c} C1*kap*N(c)*g*alpha_g >= -C1*kap*N(c)*T(c),   N(c) = sum_u d_u n_u(c)
  tail:     -sum_g alpha_g >= -R0tail
  sum[u]:   sum_c y[u,c] - Y[u] >= 0
  epi[u,j]: z[u] + Y[u]/(s_u j (j+1)) >= 2/(j+1)          (any integer j >= 1)
w_u = norm * d_u * s_u, d_u = (#classes k mod ell in orbit u)/ell.  For any u >= 0: min >= u.b + sum_cols min(r*lo, r*hi).
Everything except the external constants in params is recomputed here (factorizations with primality proofs, tail
bounds in arb, residue patterns, orbits).  Usage: check_r45u3x.py FAC.json CERT.json [LMAX] [FACBIG.json T1] [--tails-out TAILS.json]
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
FMT = cert.get("format"); req(FMT in ("r45a-v2", "r45a-u3", "r45a-u3x"), "unknown certificate format")
U3 = FMT == "r45a-u3"
U3X = FMT == "r45a-u3x"
WORKERS = 1
if "--workers" in sys.argv:
    _i = sys.argv.index("--workers"); WORKERS = int(sys.argv[_i + 1]); del sys.argv[_i:_i + 2]
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

if U3X:
    import numpy as np
    from multiprocessing import get_context
    req(cert.get("tail_mode") == "alpha_simplex", "r45a-u3x certificates use tail_mode alpha_simplex")
    req(not cert.get("duals"), "r45a-u3x certificates carry no per-c budget multipliers")
    MU = Fr(cert.get("mu", "0"))
    req(MU >= 0, "mu must be >= 0")
    print(f"[0x] {'CONDITIONAL on (I2): uniform budget multiplier mu = ' + str(MU) + ', budget constant C1 = ' + str(C1) if MU > 0 else 'UNCONDITIONAL: budget rows dropped (mu = 0)'}", flush=True)
    ADD = [int(p) for p in cert["ADD"]]
    req(len(ADD) >= 1 and len(ADD) == len(set(ADD)) and all(p in ELL for p in ADD), "ADD must be distinct primes of ELL")
    BASE = [p for p in ELL if p not in ADD]
    req(len(BASE) >= 1, "BASE must be nonempty")
    PER0 = 1
    for p in BASE: PER0 = PER0 * ordm[p] // math.gcd(PER0, ordm[p])
    req(PER % PER0 == 0)
    ell0 = 1
    for p in BASE: ell0 *= p
    FULL0 = (1 << PER0) - 1
    pat = {0: 1}
    for p in BASE:
        o = ordm[p]; pw = {pow(2, r, p): r for r in range(o)}; opts = {}
        for k in range(p):
            m = 0
            if k in pw:
                for r in range(pw[k], PER0, o): m |= 1 << r
            opts[m] = opts.get(m, 0) + 1
        new = {}
        for ex, cnt in pat.items():
            for m, c in opts.items(): new[ex | m] = new.get(ex | m, 0) + cnt * c
        pat = new
    req(sum(pat.values()) == ell0)
    def canon0(m):
        best = m; x = m
        for _s in range(1, PER0):
            x = ((x << 1) | (x >> (PER0 - 1))) & FULL0
            if x < best: best = x
        return best
    orb = {}
    for ex, cnt in pat.items():
        m = FULL0 & ~ex
        if m: k = canon0(m); orb[k] = orb.get(k, 0) + cnt
    req(cert["n_base_orbits"] == len(orb))
    log(f"[3x] BASE {BASE}: PER0 {PER0}, patterns {len(pat)}, orbits {len(orb)}; ADD {ADD} (orders {[ordm[p] for p in ADD]}); PER {PER}")
    divs = [g for g in range(1, PER + 1) if PER % g == 0]
    aj = {}
    for gs, fs in cert["alpha_j"].items():
        g = int(gs); f = Fr(fs)
        req(g in divs, ("alpha_j: g must divide PER", g)); req(f >= 0, ("alpha_j: negative weight", g))
        aj[g] = aj.get(g, Fr(0)) + f * R0tail
    req(sum(aj.values(), Fr(0)) <= R0tail, "alpha_j lies outside the tail simplex (mass above R0tail)")
    Pell = Fr(1)
    for p in ELL: Pell *= Fr(p - 1, p - 2)
    kap = C0up * Pell / (PER * log2lo)
    norm = Fr(ell, phil) / (PER * log2hi)
    E = 40
    Tg = [-((-T[c].numerator * 2 ** E) // T[c].denominator) for c in range(PER)]          # ceil(T(c) 2^E)
    req(all(Fr(Tg[c], 2 ** E) >= T[c] for c in range(PER)) and 0 <= min(Tg) and max(Tg) < 2 ** 42)
    req(PER * PER * max(Tg) < 2 ** 63)                # int64 safety (v3): Q = sum_{r1,r2} Tg <= PER^2 max(Tg); X @ M <= PER max(Tg)
    GL = dict(PER=PER, PER0=PER0, ADD=[(p, ordm[p]) for p in ADD], divs=divs,
              M=np.array([[Tg[(r2 - r1) % PER] for r2 in range(PER)] for r1 in range(PER)], dtype=np.int64),
              capk=float(CAP * kap), ajf=[(g, float(a)) for g, a in aj.items()], E=E)
    def orbit_sums(item):
        rep_, cnt_ = item
        P_, P0 = GL["PER"], GL["PER0"]
        base = np.array([(rep_ >> r) & 1 for r in range(P0)], dtype=np.int64)
        rows = [np.tile(base, P_ // P0)]; wts = [1]
        for p, o in GL["ADD"]:
            nr, nw = [], []
            for X, w in zip(rows, wts):
                nr.append(X); nw.append(w * (p - o))
                for j in range(o):
                    Y = X.copy(); Y[j::o] = 0; nr.append(Y); nw.append(w)
            rows, wts = nr, nw
        X = np.array(rows, dtype=np.int64); W = np.array(wts, dtype=np.int64)
        tw = int(sum(wts))
        # int64 safety (v3) for the weighted row sums below: n_rows * max(W) * max(term) < 2^63 with
        # terms s <= PER, Q >> 32 < 2^31, Q & (2^32 - 1) < 2^32, S_g <= PER^2
        assert len(wts) * max(wts) * max(2 ** 32, P_ * P_) < 2 ** 63, "int64 bound for the row sums"
        s = X.sum(axis=1); keep = s > 0
        X, W, s = X[keep], W[keep], s[keep]
        Q = np.einsum("ij,ij->i", X @ GL["M"], X)
        n = len(s)
        SG = np.stack([(lambda Cn: (Cn * Cn).sum(axis=1))(X.reshape(n, P_ // g, g).sum(axis=1)) for g in GL["divs"]], axis=1)
        tail = np.zeros(n)
        for g, a in GL["ajf"]: tail += g * a * SG[:, GL["divs"].index(g)]
        D = 1 + GL["capk"] * (Q / 2.0 ** GL["E"] + tail) / s
        J = np.floor(D).astype(np.int64)
        out = {}
        for j in np.unique(J):
            sel = J == j; Wj = W[sel]
            qh = Q[sel] >> 32; ql = Q[sel] & ((1 << 32) - 1)
            out[int(j)] = (int((Wj * s[sel]).sum()), int((Wj * qh).sum()), int((Wj * ql).sum()),
                           [int((Wj * SG[sel, i]).sum()) for i in range(len(GL["divs"]))])
        return cnt_, tw, out
    items = list(orb.items())
    A1, QJ, SJ = {}, {}, {}
    totw = 0
    with get_context("fork").Pool(WORKERS) as pool:
        for cnt_, tw, out in pool.imap_unordered(orbit_sums, items, chunksize=4):
            totw += cnt_ * tw
            for j, (a1, qh, ql, sg) in out.items():
                req(j >= 1)
                A1[j] = A1.get(j, 0) + cnt_ * a1
                QJ[j] = QJ.get(j, 0) + cnt_ * ((qh << 32) + ql)
                v = SJ.setdefault(j, [0] * len(divs))
                for i in range(len(divs)): v[i] += cnt_ * sg[i]
    addprod = 1
    for p in ADD: addprod *= p
    req(totw == sum(orb.values()) * addprod and ell == ell0 * addprod)
    log(f"[3x] rows evaluated: Pintz indices j in [{min(A1)}, {max(A1)}], {len(A1)} groups")
    NH = {}
    for j in A1:
        nu = max(Fr(0), norm / (j * (j + 1)) - MU)
        req(MU + nu > 0)
        hbest = None; i = 1
        while True:                      # h_j = min over i >= 1 of a convex sequence: stop at the first increase
            v = norm / i + (MU + nu) * (i - 1)
            if hbest is not None and v > hbest: break
            if hbest is None or v < hbest: hbest = v
            i += 1
            req(i < 10 ** 7)
        NH[j] = (nu, hbest)
    def vertex(gi):          # minorant at alpha = R0tail e_g (gi = None: alpha = 0)
        tot = Fr(0)
        for j in A1:
            nu, h = NH[j]
            Qj = Fr(QJ[j], 2 ** E)
            if gi is not None: Qj += divs[gi] * R0tail * SJ[j][gi]
            tot += h * A1[j] - (nu * CAP + MU * C1) * kap * Qj
        return tot / ell
    vals = {None: vertex(None)}
    for gi in range(len(divs)): vals[gi] = vertex(gi)
    for gi, v in vals.items():
        print(f"  vertex {'alpha = 0' if gi is None else 'alpha = R0tail e_' + str(divs[gi])}: minorant {float(v):.12f}", flush=True)
    gmin = min(vals, key=lambda k: vals[k]); B = vals[gmin]
    log(f"[4x] minorant minimized over the {len(vals)} vertices of the tail simplex: minimum at "
        f"{'alpha = 0' if gmin is None else 'g = ' + str(divs[gmin])}")
    print(f"CERTIFIED: lower density of {{p + 2^a}} >= {float(B):.9f}")
    print(f"rounded down: {math.floor(B * 10**6) / 10**6:.6f}")
    if CLAIM is not None:
        _c = Fr(CLAIM)
        if B >= _c:
            print(f"PASS: certified bound >= claim {CLAIM}"); sys.exit(0)
        print(f"FAIL: certified bound {float(B):.9f} < claim {CLAIM}"); sys.exit(1)
    sys.exit(0)

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

if U3:
    # 4u. unconditional bound, adversarial tail on the simplex, budget rows dropped
    req(cert.get("tail_mode") == "alpha_simplex", "r45a-u3 certificates use tail_mode alpha_simplex")
    req(not cert.get("duals"), "r45a-u3 certificates carry no budget multipliers (the budget rows are dropped)")
    divs = [g for g in range(1, PER + 1) if PER % g == 0]
    aj = {}
    for gs, fs in cert["alpha_j"].items():
        g = int(gs); f = Fr(fs)
        req(g in divs, ("alpha_j: g must divide PER", g)); req(f >= 0, ("alpha_j: negative weight", g))
        aj[g] = aj.get(g, Fr(0)) + f * R0tail
    req(sum(aj.values(), Fr(0)) <= R0tail, "alpha_j lies outside the tail simplex (mass above R0tail)")
    Pell = Fr(1)
    for p in ELL: Pell *= Fr(p - 1, p - 2)
    kap = C0up * Pell / (PER * log2lo)
    norm = Fr(ell, phil) / (PER * log2hi)
    LCD = 1
    for c in range(PER): LCD = LCD * T[c].denominator // math.gcd(LCD, T[c].denominator)
    Tn = [T[c].numerator * (LCD // T[c].denominator) for c in range(PER)]
    req(all(Fr(Tn[c], LCD) == T[c] for c in range(PER)))
    A1 = {}; NJ = {}
    for rep, (d, s, n) in od.items():
        cnt = d * ell
        req(cnt.denominator == 1 and s == n[0] and s >= 1)
        cnt = int(cnt)
        Q = Fr(sum(n[c] * Tn[c] for c in range(PER)), LCD)
        Q += sum((g * a * sum(n[c] for c in range(0, PER, g)) for g, a in aj.items()), Fr(0))
        D = 1 + CAP * kap * Q / s
        j = D.numerator // D.denominator
        req(j >= 1)
        A1[j] = A1.get(j, 0) + cnt * s
        v = NJ.setdefault(j, [0] * PER)
        for c in range(PER): v[c] += cnt * n[c]
    req(sum(A1.values()) == sum(int(d * ell) * s for d, s, n in od.values()))
    log(f"[3u] Pintz indices at alpha_j = {{{', '.join(f'{g}: {float(a / R0tail)} R0tail' for g, a in sorted(aj.items()))}}}: "
        f"j in [{min(A1)}, {max(A1)}], {len(A1)} groups")
    def vertex(g):          # minorant at alpha = R0tail e_g (g = 0: alpha = 0)
        tot = Fr(0)
        for j in A1:
            v = NJ[j]
            Qj = Fr(sum(v[c] * Tn[c] for c in range(PER)), LCD)
            if g: Qj += g * R0tail * sum(v[c] for c in range(0, PER, g))
            tot += (2 * j * A1[j] - CAP * kap * Qj) / (j * (j + 1))
        return norm * tot / ell
    vals = {g: vertex(g) for g in [0] + divs}
    for g in [0] + divs:
        print(f"  vertex {'alpha = 0' if g == 0 else 'alpha = R0tail e_' + str(g)}: minorant {float(vals[g]):.12f}", flush=True)
    gmin = min(vals, key=lambda g: vals[g]); B = vals[gmin]
    log(f"[4u] minorant minimized over the {len(vals)} vertices of the tail simplex: minimum at "
        f"{'alpha = 0' if gmin == 0 else 'g = ' + str(gmin)}")
    print(f"CERTIFIED: lower density of {{p + 2^a}} >= {float(B):.9f}")
    print(f"rounded down: {math.floor(B * 10**6) / 10**6:.6f}")
    if CLAIM is not None:
        _c = Fr(CLAIM)
        if B >= _c:
            print(f"PASS: certified bound >= claim {CLAIM}"); sys.exit(0)
        print(f"FAIL: certified bound {float(B):.9f} < claim {CLAIM}"); sys.exit(1)
    sys.exit(0)

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
