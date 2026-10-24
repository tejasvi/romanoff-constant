"""Exact checker u3f for the Romanov (Tao page 45a) lower bound: u3e v5 (check_r45u3e.py 7e8e7170) plus format r45a-u3f.
Usage: check_r45u3f.py FAC.json CERT.json [LMAX] [FACBIG.json T1] [--claim X] [--workers N] [--time-sample K]

r45a-u3f = r45a-u3e with INDEPENDENT CRT COMPONENTS.  The certificate lists primes IND.  Each added prime p is either a core
prime (gcd(o_p, prod IND) = 1) or belongs to exactly one q in IND, with o_p = q m_p, gcd(m_p, q) = 1 and m_p | PERc, where
PERc = lcm of the orders of BASE and the core primes, q does not divide PERc, and PER = PERc * prod IND.  Write r <-> (x, y)
with x = r mod PERc and y = (r mod q)_q (CRT).  The BASE mask and the core exclusions depend on x only; the class j mod o_p of an
independent p is {r : x = a_p (mod m_p), y_q = b_p} with (a_p, b_p) = (j mod m_p, j mod q).  Hence
  1_U(x, y) = core(x) * prod_q F_q(x, y_q),   F_q(x, y) = prod_{p in P_q} (1 - [x = a_p (m_p)] [y = b_p]),
and for g = g_c * prod_q g_q (g_c | PERc, g_q in {1, q}), [g | r1 - r2] = [g_c | x1 - x2] prod_q [g_q | y1_q - y2_q], so
  S_g(U) = sum_{x1, x2} core(x1) core(x2) [g_c | x1 - x2] prod_q W_q^{g_q}(x1, x2),
  W_q^1(x1, x2) = f_q(x1) f_q(x2),  W_q^q(x1, x2) = q - |B_q(x1) u B_q(x2)|,  f_q(x) = q - |B_q(x)|,
where B_q(x) = {b_p : p in P_q, x = a_p (m_p)} is the set of excluded VALUES of y_q.  W depends on x only through x mod M,
M = lcm of all m_p, so S_g(U) = sum_{u, v mod M} W(u, v) T_{g_c}(u, v) with
  T_{g_c}(u, v) = #{(x1, x2) in core^2 : x1 = x2 (g_c), x1 = u (M), x2 = v (M)} = sum_{c mod g_c} N^L_{(c,u)} N^L_{(c,v)},
L = lcm(g_c, M) | PERc, N^L = class counts of the core mask mod L, (c, u) = the class mod L with x = c (g_c), x = u (M) (zero if
incompatible).  Also s = |U| = sum_u N^M_u prod_q f_q(u).  Symmetry: a permutation of Z/q acting on y_q maps the row of an
option tuple to the row of the permuted tuple and leaves s and every S_g unchanged ([q | y1 - y2] is permutation invariant).
So the options of P_q enter only through their PATTERN: for each p, "none" or the residue a_p mod m_p, and the partition of the
class options into blocks of equal b.  A pattern with k blocks stands for q (q-1) ... (q-k+1) option tuples, times the weights
(p - o_p for "none", 1 for a class).  The checker verifies that the pattern multiplicities add up to prod_{p in P_q} p.
Everything else (BASE orbits, rotation argument, core options, Pintz minorant, tail vertices, conditional mu) is r45a-u3e's,
except that the core options are enumerated explicitly (no last-prime trick).  --time-sample K evaluates K evenly spaced BASE
orbits, prints the time per orbit and exits WITHOUT certifying (pilots only).

Exact checker u3e for the Romanov (Tao page 45a) lower bound: rel2 (check_r45a5_rel2_3cf71761.py) plus formats r45a-u3,
r45a-u3x and r45a-u3e.  Usage: check_r45u3e.py FAC.json CERT.json [LMAX] [FACBIG.json T1] [--claim X] [--workers N]

r45a-u3e = r45a-u3x evaluated in DIVISOR FORM, for large periods.  The class-(a) and class-(b) parts of T are bounded per
divisor instead of per residue: T(c) <= sum_{g | PER, g | c} B_g, with B_g = fup(sum of the class-(a) DP terms with
gcd(L, PER) = g) + (class-(b) float sum for g, times (1 + 1e-9), rounded up), plus both prune terms at g = 1.  Each per-residue
bound of r45a-u3x is a sum of these terms, so B_g-form T is never smaller.  Then for every row
  Q = sum_{r1, r2 in U} T(r2 - r1) <= sum_g B_g S_g,   S_g = sum_{a mod g} |U cap (a + gZ)|^2,
and the tail vertices use the same S_g.  B_g is rounded UP to the grid 2^-48 and split into 24-bit halves; all row quantities
are exact int64, and all weighted sums are exact Python integers (int64 batches with asserted bounds).
The options of the LAST added prime p_L (order o_L) are evaluated together.  For a prefix row U' (the options of the other
added primes) and the class C_j = U' cap (j + o_L Z):
  S_g(U' minus C_j) = S_g(U') - 2 sum_{x mod lcm(g, o_L), x = j (o_L)} N^g_{x mod g}(U') N^lcm_x(U') + sum_{x = j (o_L)} N^lcm_x(U')^2,
where N^h_x(U') = |U' cap (x + hZ)|; this holds because r = a (g) and r = j (o_L) is the single class x mod lcm(g, o_L) by CRT.
Also |C_j| = N^{o_L}_j(U').  Everything else (the rotation argument, the weights, the vertices, the conditional option) is as in
r45a-u3x.

Exact checker u3x for the Romanov (Tao page 45a) lower bound: rel2 (check_r45a5_rel2_3cf71761.py) plus formats r45a-u3
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
bounds in arb, residue patterns, orbits).  Usage: check_r45u3f.py FAC.json CERT.json [LMAX] [FACBIG.json T1] [--tails-out TAILS.json]
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
FMT = cert.get("format"); req(FMT in ("r45a-v2", "r45a-u3", "r45a-u3x", "r45a-u3e", "r45a-u3f"), "unknown certificate format")
U3 = FMT == "r45a-u3"
U3X = FMT == "r45a-u3x"
U3E = FMT == "r45a-u3e"
U3F = FMT == "r45a-u3f"
DIVF = U3E or U3F                                   # per-divisor tail bounds
TSAMPLE = 0
if "--time-sample" in sys.argv:
    _i = sys.argv.index("--time-sample"); TSAMPLE = int(sys.argv[_i + 1]); del sys.argv[_i:_i + 2]
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
if DIVF:                                            # u3e: per-divisor upper bounds (no per-residue table)
    Ta_g = {g: fup(v) for g, v in Lg.items()}; prune_up = fup(prune); T = None
else:
    T = [fup(sum((v for g, v in Lg.items() if c % g == 0), arb(0)) + prune) for c in range(PER)]
W2, _ = dp(sorted(prim))
R0s = sum((w * arb(fmpq(1, L)) for L, w in W2.items()), arb(0))
R0slo = flo(R0s)
Tb = [Fr(0)] * PER
Tb_g = {}; pruneb_up = Fr(0)
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
    TbF = np.zeros(PER); Fsum = 0.0; TbG = {}
    divs_ = [g for g in range(1, PER + 1) if PER % g == 0]
    for t, qs in Mt.items():
        Ft = f_up(qs); Fsum += Ft
        Lp = LT // np.gcd(LT, t) * t
        gp = np.gcd(Lp, PER)
        vals = wT * gp / Lp.astype(np.float64)
        A = {g: float(vals[gp == g].sum()) for g in divs_}
        if DIVF:
            for g in divs_: TbG[g] = TbG.get(g, 0.0) + Ft * A[g]
        else:
            for c in range(PER):
                TbF[c] += Ft * sum(A[g] for g in divs_ if c % g == 0)
    pruneb = float((dropped * prodall).upper()) * PER / LMAX * Fsum
    if DIVF:
        Tb_g = {g: Fr(math.nextafter(TbG[g] * (1 + 1e-9), math.inf)) for g in divs_}
        pruneb_up = Fr(math.nextafter(pruneb * (1 + 1e-9), math.inf))
    else:
        Tb = [Fr(math.nextafter(TbF[c] * (1 + 1e-9) + pruneb, math.inf)) for c in range(PER)]
    # class (b) for R0: all-small-primes DP weights, lower endpoints
    L2 = np.array(list(W2.keys()), dtype=np.int64)
    w2 = np.array([math.nextafter(float(w.lower()), 0.0) for w in W2.values()])
    req((w2 >= 0).all())
    R0b = 0.0
    for t, qs in Mt.items():
        R0b += f_lo(qs) * float(np.sum(w2 / (L2 // np.gcd(L2, t) * t).astype(np.float64)))
    R0b_lo = Fr(math.nextafter(R0b * (1 - 1e-9), 0.0))
    log(f"[2b] class (b): {sum(len(v) for v in Mt.values())} proven primes, orders {T0+1}..{T1}; T_b(0) <= {float(sum(Tb_g.values()) + pruneb_up if DIVF else Tb[0]):.3e}; R0_b >= {float(R0b_lo):.9f}")
    R0slo += R0b_lo
if not DIVF:
    T = [T[c] + Tb[c] for c in range(PER)]
R0tail = R0up - R0slo
req(R0tail > 0)
if DIVF:
    log(f"[2] divisor form: T_up(0) <= {float(sum(Ta_g.values()) + prune_up + sum(Tb_g.values()) + pruneb_up):.9f}  tail mass <= {float(R0tail):.4e}")
else:
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

if U3F:
    import numpy as np, itertools
    from multiprocessing import get_context
    req(cert.get("tail_mode") == "alpha_simplex", "r45a-u3f certificates use tail_mode alpha_simplex")
    req(not cert.get("duals"), "r45a-u3f certificates carry no per-c budget multipliers")
    MU = Fr(cert.get("mu", "0"))
    req(MU >= 0, "mu must be >= 0")
    print(f"[0f] {'CONDITIONAL on (I2): uniform budget multiplier mu = ' + str(MU) + ', budget constant C1 = ' + str(C1) if MU > 0 else 'UNCONDITIONAL: budget rows dropped (mu = 0)'}", flush=True)
    ADD = [int(p) for p in cert["ADD"]]
    IND = [int(q) for q in cert["IND"]]
    req(len(ADD) >= 1 and len(ADD) == len(set(ADD)) and all(p in ELL for p in ADD), "ADD must be distinct primes of ELL")
    req(len(IND) >= 1 and len(IND) == len(set(IND)) and all(q > 1 and fmpz(q).is_prime() for q in IND), "IND must be distinct primes")
    BASE = [p for p in ELL if p not in ADD]
    req(len(BASE) >= 1, "BASE must be nonempty")
    qprod = 1
    for q in IND: qprod *= q
    ADDC = [p for p in ADD if math.gcd(ordm[p], qprod) == 1]
    ADDI = {q: [p for p in ADD if ordm[p] % q == 0] for q in IND}
    for p in ADD:
        req((p in ADDC) + sum(p in ADDI[q] for q in IND) == 1, ("added prime must be core or in exactly one IND component", p))
    def lcmlist(xs):
        L = 1
        for x_ in xs: L = L * x_ // math.gcd(L, x_)
        return L
    PER0 = lcmlist([ordm[p] for p in BASE])
    PERc = lcmlist([ordm[p] for p in BASE + ADDC])
    MP = {}
    for q in IND:
        req(PERc % q != 0, ("IND prime divides the core period", q))
        req(len(ADDI[q]) >= 1, ("IND prime without added primes", q))
        for p in ADDI[q]:
            m_ = ordm[p] // q
            req(m_ * q == ordm[p] and m_ % q != 0 and PERc % m_ == 0, ("o_p must be q m_p with m_p | PERc", p))
            MP[p] = m_
    req(PER == PERc * qprod, "PER must equal PERc * prod IND")
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
    divs = [g for g in range(1, PER + 1) if PER % g == 0]
    divsc = [g for g in range(1, PERc + 1) if PERc % g == 0]
    log(f"[3f] BASE {BASE}: PER0 {PER0}, orbits {len(orb)}; core ADD {ADDC} (PERc {PERc}); independent "
        + "; ".join(f"q={q}: {[(p, MP[p]) for p in ADDI[q]]}" for q in IND) + f"; PER {PER}")
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
    req(all(g in divs for g in Ta_g) and all(g in divs for g in Tb_g))
    Bg = {g: Ta_g.get(g, Fr(0)) + Tb_g.get(g, Fr(0)) for g in divs}
    Bg[1] += prune_up + pruneb_up
    req(all(v >= 0 for v in Bg.values()))
    E = 48
    Bn = [-((-Bg[g].numerator * 2 ** E) // Bg[g].denominator) for g in divs]
    req(all(Fr(b, 2 ** E) >= Bg[g] for b, g in zip(Bn, divs)))
    Bhi = [b >> 24 for b in Bn]; Blo = [b & ((1 << 24) - 1) for b in Bn]
    req(sum(Bhi) * PER * PER < 2 ** 63 and sum(Blo) * PER * PER < 2 ** 63, "int64 bound for Q")
    req(PER * PER < 2 ** 32, "S_g <= PER^2 < 2^32 (group-sum columns)")
    # patterns of each independent component
    Mq = {q: lcmlist([MP[p] for p in ADDI[q]]) for q in IND}
    M = lcmlist(list(Mq.values()))
    req(PERc % M == 0)
    def set_partitions(items):
        if not items:
            yield []
            return
        first, rest = items[0], items[1:]
        for part in set_partitions(rest):
            for i in range(len(part)):
                yield part[:i] + [[first] + part[i]] + part[i + 1:]
            yield [[first]] + part
    PATS = {}
    for q in IND:
        Pq = ADDI[q]; lst = []; tot = 0
        for choice in itertools.product(*[[None] + list(range(MP[p])) for p in Pq]):
            cls = [p for p, a in zip(Pq, choice) if a is not None]
            amap = {p: a for p, a in zip(Pq, choice) if a is not None}
            wnone = 1
            for p, a in zip(Pq, choice):
                if a is None: wnone *= p - ordm[p]
            for part in set_partitions(cls):
                k = len(part)
                ff = 1
                for i in range(k): ff *= q - i
                mult = wnone * ff
                if mult == 0: continue
                excl = [set(bi for bi, blk in enumerate(part) if any(u % MP[p] == amap[p] for p in blk)) for u in range(M)]
                f = [q - len(excl[u]) for u in range(M)]
                W1 = [[f[u] * f[v] for v in range(M)] for u in range(M)]
                Wq = [[q - len(excl[u] | excl[v]) for v in range(M)] for u in range(M)]
                lst.append((mult, f, W1, Wq))
                tot += mult
        prodp = 1
        for p in Pq: prodp *= p
        req(tot == prodp, ("pattern multiplicities must add up to prod p", q, tot, prodp))
        PATS[q] = lst
    # combined patterns, and the divisor map g = g_c * prod_q g_q
    combos = list(itertools.product(*[range(len(PATS[q])) for q in IND]))
    gsel = list(itertools.product(*[[False, True] for q in IND]))
    NP, NG = len(combos), len(gsel)
    Wt = np.zeros((NP, NG, M, M), dtype=np.int64); Fm = np.zeros((NP, M), dtype=np.int64); multv = []
    for pi, cmb in enumerate(combos):
        mult = 1; fv = np.ones(M, dtype=np.int64)
        for q, ci in zip(IND, cmb):
            mult *= PATS[q][ci][0]; fv = fv * np.array(PATS[q][ci][1], dtype=np.int64)
        multv.append(mult); Fm[pi] = fv
        for gi, sel in enumerate(gsel):
            Wm = np.ones((M, M), dtype=np.int64)
            for q, ci, on in zip(IND, cmb, sel):
                Wm = Wm * np.array(PATS[q][ci][3] if on else PATS[q][ci][2], dtype=np.int64)
            Wt[pi, gi] = Wm
    gidx = np.zeros((len(divsc), NG), dtype=np.int64)
    for ci_, gc in enumerate(divsc):
        for gi, sel in enumerate(gsel):
            g = gc
            for q, on in zip(IND, sel):
                if on: g *= q
            gidx[ci_, gi] = divs.index(g)
    req(sorted(gidx.reshape(-1).tolist()) == list(range(len(divs))), "divisor map must be a bijection")
    _indp = 1
    for q in IND:
        for p in ADDI[q]: _indp *= p
    req(sum(multv) == _indp, "combined pattern multiplicities must add up to the product of the independent primes")
    # index maps for T_{g_c}: (u, c) -> class mod L = lcm(g_c, M), or -1 if incompatible
    TIDX = []
    for gc in divsc:
        L = gc * M // math.gcd(gc, M)
        idx = -np.ones((M, gc), dtype=np.int64)
        for x_ in range(L): idx[x_ % M, x_ % gc] = x_
        # v3: A_u[c] = 0 unless c = u (mod d), d = gcd(g_c, M); so T(u, v) = 0 unless u = v (mod d), and the sum runs over c = u (mod d)
        d_ = math.gcd(gc, M)
        cp_ = [(u, v, np.array([c for c in range(gc) if c % d_ == u % d_], dtype=np.int64))
               for u in range(M) for v in range(u, M) if (v - u) % d_ == 0]
        TIDX.append((gc, L, idx, cp_))
    def _spf(n):
        d_ = 2
        while n % d_: d_ += 1
        return d_
    HPLAN = []
    for h in sorted(divsc, reverse=True):
        if h != PERc:
            q_ = _spf(PERc // h); HPLAN.append((h, h * q_, q_))
    # v2: S is kept in the natural column order k = ci * NG + gi (divisor divs[col_div[k]]); coefficients are permuted once
    col_div = gidx.reshape(-1); inv_col = np.argsort(col_div)
    req(sorted(col_div.tolist()) == list(range(len(divs))))
    # v2: S = W . T is evaluated in float64 BLAS; exact because every operand is a nonnegative integer and every partial sum is
    # at most M^2 max(W) max(T) with T <= PERc^2, asserted < 2^53
    req(M * M * int(Wt.max()) * PERc * PERc < 2 ** 53, "float64 exactness bound for S = W . T")
    # v3: exact float64 group sums: every summand W_core * S <= wmax PER^2 (S <= PER^2, s <= PER), at most CH rows per sum
    wmax = 1
    for p in ADDC: wmax *= max(p - ordm[p], 1)
    CH = max(1, min((1 << 24) // (NP * len(divs)), (2 ** 53 - 1) // (wmax * PER * PER)))
    req(CH * wmax * PER * PER < 2 ** 53, "float64 exactness bound for the group sums")
    Bn_nat = [Bn[int(i)] for i in col_div]
    Bf = np.array([float(Fr(b, 2 ** E)) for b in Bn_nat])                     # J selection only
    Wt4 = Wt.astype(np.float64)                                                 # (NP, NG, M, M)
    Zf = np.einsum('cg,pguv->pcuv', Bf.reshape(len(divsc), NG), Wt4).reshape(NP, len(divsc) * M * M).T.copy()
    GL = dict(PERc=PERc, PER0=PER0, ADDC=[(p, ordm[p]) for p in ADDC], divs=divs, divsc=divsc, M=M, NP=NP, NG=NG,
              Wt=Wt.reshape(NP * NG, M * M).T.astype(np.float64).copy(), Fm=Fm.T.copy(), mult=np.array(multv, dtype=np.int64),
              TIDX=TIDX, HPLAN=HPLAN, Zf=Zf, multp=[int(m_) for m_ in multv],
              Bhi=np.array(Bhi, dtype=np.int64)[col_div], Blo=np.array(Blo, dtype=np.int64)[col_div],
              capk=float(CAP * kap), ajf=[(int(inv_col[divs.index(g)]), g, float(a)) for g, a in aj.items()], E=E, CH=CH,
              PER2=PER * PER)
    log(f"[3f] v3 patterns: " + ", ".join(f"q={q}: {len(PATS[q])}" for q in IND) + f"; combined {NP}; M {M}; divisors {len(divs)} "
        f"(core {len(divsc)}); core-row chunk {CH}")
    def gsum(Wg, Mg):
        """exact sum of Wg[i] * Mg[i, :] as Python ints: int64 batches with bound n * max(W) * max(M) < 2^63"""
        mw = int(Wg.max()); mm = int(Mg.max())
        if mw == 0 or mm == 0: return [0] * Mg.shape[1]
        bs = max(1, (2 ** 63 - 1) // (mw * mm))
        tot = [0] * Mg.shape[1]
        for i in range(0, len(Wg), bs):
            part = Wg[i:i + bs] @ Mg[i:i + bs]
            for k_ in range(len(tot)): tot[k_] += int(part[k_])
        return tot
    def orbit_sums_f(item):
        rep_, cnt_ = item
        Pc, P0, Mm = GL["PERc"], GL["PER0"], GL["M"]
        base = np.array([(rep_ >> r) & 1 for r in range(P0)], dtype=np.int8)
        rows = [np.tile(base, Pc // P0)]; wts = [1]
        for p, o in GL["ADDC"]:
            nr, nw = [], []
            for X, w in zip(rows, wts):
                nr.append(X); nw.append(w * (p - o))
                for j in range(o):
                    Y = X.copy(); Y[j::o] = 0; nr.append(Y); nw.append(w)
            rows, wts = nr, nw
        tw = int(sum(wts))
        out = {}
        nd = len(GL["divs"]); ndc = len(GL["divsc"]); NPl, NGl = GL["NP"], GL["NG"]
        for c0 in range(0, len(wts), GL["CH"]):
            X = np.array(rows[c0:c0 + GL["CH"]], dtype=np.int32); W = np.array(wts[c0:c0 + GL["CH"]], dtype=np.int64)
            n1 = len(W)
            N = {Pc: X}
            for h, H, q_ in GL["HPLAN"]:
                N[h] = N[H].reshape(n1, q_, h).sum(axis=1, dtype=np.int32)
            T = np.zeros((n1, ndc, Mm * Mm), dtype=np.float64)
            for ci_, (gc, L, idx, cp_) in enumerate(GL["TIDX"]):
                NL = N[L].astype(np.int64)
                A = np.where(idx[None, :, :] >= 0, NL[:, np.maximum(idx, 0)], 0)          # (n1, M, g_c), int64
                for u, v, cols in cp_:
                    t_ = (A[:, u, cols] * A[:, v, cols]).sum(axis=1)                         # exact int64
                    T[:, ci_, u * Mm + v] = t_; T[:, ci_, v * Mm + u] = t_
            Sf = (T.reshape(n1 * ndc, Mm * Mm) @ GL["Wt"]).reshape(n1, ndc, NPl, NGl)       # float64, exact (bound asserted)
            Qf = T.reshape(n1, ndc * Mm * Mm) @ GL["Zf"]                                    # (n1, NP), float: Pintz index only
            s = N[Mm].astype(np.int64) @ GL["Fm"]                                            # (n1, NP), exact
            tail = np.zeros((n1, NPl))
            for k_, g, a in GL["ajf"]: tail += g * a * Sf[:, k_ // NGl, :, k_ % NGl]
            J = np.floor(1 + GL["capk"] * (Qf + tail) / np.maximum(s, 1)).astype(np.int64)
            assert (s >= 0).all() and float(Sf.min()) >= 0
            assert n1 * int(W.max()) * GL["PER2"] < 2 ** 53, "float64 exactness bound (chunk)"
            Wc = W.astype(np.float64); jmin = int(J.min()); G_ = int(J.max()) - jmin + 1
            XP = np.empty((n1, 1 + nd)); E1 = np.zeros((G_, n1)); ar = np.arange(n1)
            for P in range(NPl):
                XP[:, 0] = Wc * s[:, P]
                XP[:, 1:] = (Wc[:, None, None] * Sf[:, :, P, :]).reshape(n1, nd)
                E1[:] = 0.0; E1[J[:, P] - jmin, ar] = 1.0
                sums = E1 @ XP                                                              # exact: all partial sums < 2^53
                mP = GL["multp"][P]
                for gi_ in np.flatnonzero(E1.sum(axis=1) > 0):
                    j = jmin + int(gi_)
                    vec = sums[gi_].astype(np.int64).astype(object) * mP
                    if j in out: out[j] += vec
                    else: out[j] = vec
        return cnt_, tw, out
    items = list(orb.items())
    if TSAMPLE:
        step = max(1, len(items) // TSAMPLE)
        samp = items[::step][:TSAMPLE]
        t0_ = time.time()
        with get_context("fork").Pool(WORKERS) as pool:
            for _ in pool.imap_unordered(orbit_sums_f, samp, chunksize=1): pass
        dt = time.time() - t0_
        print(f"TIMING ONLY (NOT A CERTIFICATE): {len(samp)} of {len(items)} BASE orbits in {dt:.1f} s with {WORKERS} workers "
              f"-> {dt / len(samp) * WORKERS:.2f} worker-s per orbit; full run ~ {dt / len(samp) * len(items) / 3600:.2f} h at "
              f"{WORKERS} workers", flush=True)
        sys.exit(3)
    A1, QJ, SJ = {}, {}, {}
    totw = 0
    with get_context("fork").Pool(WORKERS) as pool:
        for cnt_, tw, out in pool.imap_unordered(orbit_sums_f, items, chunksize=2):
            totw += cnt_ * tw
            for j, vec in out.items():
                req(j >= 1)
                A1[j] = A1.get(j, 0) + cnt_ * int(vec[0])
                v = SJ.setdefault(j, [0] * len(divs))
                for i in range(len(divs)): v[i] += cnt_ * int(vec[1 + i])
    for j in SJ:                                       # v3: exact Q sums from the exact S sums (natural order), then reorder
        QJ[j] = sum(Bn_nat[k] * SJ[j][k] for k in range(len(divs)))
        v_ = SJ[j]; SJ[j] = [v_[int(inv_col[i])] for i in range(len(divs))]
    addcprod = 1
    for p in ADDC: addcprod *= p
    indprod = 1
    for q in IND:
        for p in ADDI[q]: indprod *= p
    req(totw == sum(orb.values()) * addcprod and ell == ell0 * addcprod * indprod)
    log(f"[3f] rows evaluated: Pintz indices j in [{min(A1)}, {max(A1)}], {len(A1)} groups")
    NH = {}
    for j in A1:
        nu = max(Fr(0), norm / (j * (j + 1)) - MU)
        req(MU + nu > 0)
        hbest = None; i = 1
        while True:
            v = norm / i + (MU + nu) * (i - 1)
            if hbest is not None and v > hbest: break
            if hbest is None or v < hbest: hbest = v
            i += 1
            req(i < 10 ** 7)
        NH[j] = (nu, hbest)
    def vertex(gi):
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
    log(f"[4f] minorant minimized over the {len(vals)} vertices of the tail simplex: minimum at "
        f"{'alpha = 0' if gmin is None else 'g = ' + str(divs[gmin])}")
    print(f"CERTIFIED: lower density of {{p + 2^a}} >= {float(B):.9f}")
    print(f"rounded down: {math.floor(B * 10**6) / 10**6:.6f}")
    if CLAIM is not None:
        _c = Fr(CLAIM)
        if B >= _c:
            print(f"PASS: certified bound >= claim {CLAIM}"); sys.exit(0)
        print(f"FAIL: certified bound {float(B):.9f} < claim {CLAIM}"); sys.exit(1)
    sys.exit(0)

if U3E:
    import numpy as np
    from multiprocessing import get_context
    req(cert.get("tail_mode") == "alpha_simplex", "r45a-u3e certificates use tail_mode alpha_simplex")
    req(not cert.get("duals"), "r45a-u3e certificates carry no per-c budget multipliers")
    MU = Fr(cert.get("mu", "0"))
    req(MU >= 0, "mu must be >= 0")
    print(f"[0e] {'CONDITIONAL on (I2): uniform budget multiplier mu = ' + str(MU) + ', budget constant C1 = ' + str(C1) if MU > 0 else 'UNCONDITIONAL: budget rows dropped (mu = 0)'}", flush=True)
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
    log(f"[3e] BASE {BASE}: PER0 {PER0}, patterns {len(pat)}, orbits {len(orb)}; ADD {ADD} (orders {[ordm[p] for p in ADD]}; last {ADD[-1]}); PER {PER}")
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
    req(all(g in divs for g in Ta_g) and all(g in divs for g in Tb_g))
    Bg = {g: Ta_g.get(g, Fr(0)) + Tb_g.get(g, Fr(0)) for g in divs}
    Bg[1] += prune_up + pruneb_up
    req(all(v >= 0 for v in Bg.values()))
    E = 48
    Bn = [-((-Bg[g].numerator * 2 ** E) // Bg[g].denominator) for g in divs]        # ceil(B_g 2^E)
    req(all(Fr(b, 2 ** E) >= Bg[g] for b, g in zip(Bn, divs)))
    Bhi = [b >> 24 for b in Bn]; Blo = [b & ((1 << 24) - 1) for b in Bn]
    req(sum(Bhi) * PER * PER < 2 ** 63 and sum(Blo) * PER * PER < 2 ** 63, "int64 bound for Q")
    req(PER * PER < 2 ** 31, "int32 bound for products of class counts (v5)")
    pL = ADD[-1]; oL = ordm[pL]
    def _spf(n):
        d_ = 2
        while n % d_: d_ += 1
        return d_
    HPLAN = []                                 # v3: N^h = N^(hq) folded, q = least prime with hq | PER, in decreasing h
    for h in sorted(divs, reverse=True):
        if h != PER:
            q_ = _spf(PER // h); HPLAN.append((h, h * q_, q_))
    GL = dict(PER=PER, PER0=PER0, PRE=[(p, ordm[p]) for p in ADD[:-1]], pL=pL, oL=oL, divs=divs, HPLAN=HPLAN,
              Bhi=np.array(Bhi, dtype=np.int64), Blo=np.array(Blo, dtype=np.int64),
              capk=float(CAP * kap), ajf=[(divs.index(g), g, float(a)) for g, a in aj.items()], E=E)
    def wsum(wv, xv):
        """exact sum of wv * xv (int64 arrays, nonnegative) as a Python int, in int64 batches with asserted bounds"""
        if len(wv) == 0: return 0
        mw = int(wv.max()); mx = int(xv.max())
        if mw == 0 or mx == 0: return 0
        bs = max(1, (2 ** 62) // (mw * mx))
        tot = 0
        for i in range(0, len(wv), bs):
            tot += int((wv[i:i + bs] * xv[i:i + bs]).sum())
        return tot
    def orbit_sums_e(item):
        rep_, cnt_ = item
        P_, P0, oL_, pL_, dv = GL["PER"], GL["PER0"], GL["oL"], GL["pL"], GL["divs"]
        base = np.array([(rep_ >> r) & 1 for r in range(P0)], dtype=np.int8)
        rows = [np.tile(base, P_ // P0)]; wts = [1]
        for p, o in GL["PRE"]:
            nr, nw = [], []
            for X, w in zip(rows, wts):
                nr.append(X); nw.append(w * (p - o))
                for j in range(o):
                    Y = X.copy(); Y[j::o] = 0; nr.append(Y); nw.append(w)
            rows, wts = nr, nw
        tw = int(sum(wts)) * pL_
        out = {}
        CH = max(1, (1 << 22) // P_)                        # prefix rows per chunk (memory bound)
        for c0 in range(0, len(wts), CH):
            X = np.array(rows[c0:c0 + CH], dtype=np.int32); W = np.array(wts[c0:c0 + CH], dtype=np.int64)
            n1 = len(W)
            N = {P_: X}                                       # v3: counts folded down the divisor lattice (int32: counts <= PER)
            for h, H, q_ in GL["HPLAN"]:
                N[h] = N[H].reshape(n1, q_, h).sum(axis=1, dtype=np.int32)
            s0 = N[1][:, 0].astype(np.int64)
            nopt = oL_ + 1
            St = np.empty((len(dv), n1, nopt), dtype=np.int64)       # v5: one contiguous (n1, nopt) block per divisor
            s = np.zeros((n1, nopt), dtype=np.int64)
            s[:, 0] = s0
            s[:, 1:] = s0[:, None] - N[oL_]
            sqc = {}
            for gi, g in enumerate(dv):
                Ng = N[g]                                             # v5: int32 products (each <= PER^2 < 2^31), int64 sums
                Sg0 = (Ng * Ng).sum(axis=1, dtype=np.int64)
                Lh = g * oL_ // math.gcd(g, oL_)
                NL = N[Lh]
                # v3: column x of NL is x = k oL + j, so grouping by j = x mod oL is a reshape; N^g_{x mod g} is a tile
                cross = (np.tile(Ng, (1, Lh // g)) * NL).reshape(n1, Lh // oL_, oL_).sum(axis=1, dtype=np.int64)
                if Lh not in sqc: sqc[Lh] = (NL * NL).reshape(n1, Lh // oL_, oL_).sum(axis=1, dtype=np.int64)
                St[gi, :, 0] = Sg0
                St[gi, :, 1:] = Sg0[:, None] - 2 * cross + sqc[Lh]
            S = St.transpose(1, 2, 0)
            Wf = np.concatenate([W[:, None] * (pL_ - oL_), np.repeat(W[:, None], oL_, axis=1)], axis=1)
            s = s.reshape(-1); S = S.reshape(-1, len(dv)); Wf = Wf.reshape(-1)
            assert (s >= 0).all() and (S >= 0).all()
            keep = s > 0
            s, S, Wf = s[keep], S[keep], Wf[keep]
            Qhi = S @ GL["Bhi"]; Qlo = S @ GL["Blo"]
            tail = np.zeros(len(s))
            for gi, g, a in GL["ajf"]: tail += g * a * S[:, gi]
            D = 1 + GL["capk"] * ((Qhi.astype(np.float64) * 2.0 ** 24 + Qlo) / 2.0 ** GL["E"] + tail) / s
            J = np.floor(D).astype(np.int64)
            # v4: one exact int64 matmul per Pintz group. Columns: s, Qhi split at 2^32, Qlo split at 2^32, S_g; all < 2^32.
            M32 = (1 << 32) - 1
            Mv = np.concatenate([s[:, None], (Qhi >> 32)[:, None], (Qhi & M32)[:, None], (Qlo >> 32)[:, None],
                                 (Qlo & M32)[:, None], S], axis=1)
            assert int(Mv.min()) >= 0 and int(Mv.max()) < 2 ** 32, "column bound"
            order = np.argsort(J, kind="stable"); Js = J[order]
            cuts = np.flatnonzero(np.diff(Js)) + 1
            for a, b in zip(np.concatenate([[0], cuts]), np.concatenate([cuts, [len(Js)]])):
                idx = order[a:b]; Wg = Wf[idx]; Mg = Mv[idx]
                assert int(b - a) * int(Wg.max()) * 2 ** 32 < 2 ** 63, "int64 bound for the group sums"
                sm = [int(v) for v in (Wg @ Mg)]
                j = int(Js[a])
                a1, qh, ql, sg = out.get(j, (0, 0, 0, [0] * len(dv)))
                out[j] = (a1 + sm[0], qh + (sm[1] << 32) + sm[2], ql + (sm[3] << 32) + sm[4],
                          [sg[i] + sm[5 + i] for i in range(len(dv))])
        return cnt_, tw, out
    items = list(orb.items())
    A1, QJ, SJ = {}, {}, {}
    totw = 0
    with get_context("fork").Pool(WORKERS) as pool:
        for cnt_, tw, out in pool.imap_unordered(orbit_sums_e, items, chunksize=2):
            totw += cnt_ * tw
            for j, (a1, qh, ql, sg) in out.items():
                req(j >= 1)
                A1[j] = A1.get(j, 0) + cnt_ * a1
                QJ[j] = QJ.get(j, 0) + cnt_ * ((qh << 24) + ql)
                v = SJ.setdefault(j, [0] * len(divs))
                for i in range(len(divs)): v[i] += cnt_ * sg[i]
    addprod = 1
    for p in ADD: addprod *= p
    req(totw == sum(orb.values()) * addprod and ell == ell0 * addprod)
    log(f"[3e] rows evaluated: Pintz indices j in [{min(A1)}, {max(A1)}], {len(A1)} groups")
    NH = {}
    for j in A1:
        nu = max(Fr(0), norm / (j * (j + 1)) - MU)
        req(MU + nu > 0)
        hbest = None; i = 1
        while True:
            v = norm / i + (MU + nu) * (i - 1)
            if hbest is not None and v > hbest: break
            if hbest is None or v < hbest: hbest = v
            i += 1
            req(i < 10 ** 7)
        NH[j] = (nu, hbest)
    def vertex(gi):
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
    log(f"[4e] minorant minimized over the {len(vals)} vertices of the tail simplex: minimum at "
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
