"""Generate RCert/G/EvData.lean: constants of the U3g/V4g stage-2 evaluator at period 27720 = 360 * 7 * 11
(core divisors and count plan at 360, B_g on the 2^-32 grid in the (tau, g_c) order, the independent-option patterns of
q = 7 (primes 43, 29) and q = 11 (prime 23) with their weights and signature tables, the Pintz-index constants, and the
optimal integer i*(J) of the V4g minorant).  Usage: python3 -I -B gen_evg.py ROOT"""
import re, sys, math
from fractions import Fraction as Fr

ROOT = sys.argv[1]
PER, PERC, M = 27720, 360, 4
TAU = [1, 7, 11, 77]
divG = [g for g in range(1, PER + 1) if PER % g == 0]
src = open(f"{ROOT}/RCert/M3G/Defs.lean").read()
m = re.search(r"def divG : List Nat := \[([^\]]*)\]", src)
assert [int(t) for t in m.group(1).replace("\n", " ").split(",")] == divG
dC = [g for g in range(1, PERC + 1) if PERC % g == 0]
assert len(divG) == 96 and len(dC) == 24
blit = open(f"{ROOT}/RCert/G/BLit.lean").read()
B = {int(g): Fr(int(a), int(b)) for g, a, b in re.findall(r"\((\d+), \((\d+) : Rat\) / (\d+)\)", blit)}
assert sorted(B) == divG
E = 32
def ceil2(x): return -((-x.numerator * 2 ** E) // x.denominator)
bnC = [ceil2(B[dC[c] * TAU[t]]) for t in range(4) for c in range(24)]
gIdx = [divG.index(dC[c] * TAU[t]) for t in range(4) for c in range(24)]
assert sorted(gIdx) == list(range(96))
assert all(Fr(b, 2 ** E) >= B[dC[i % 24] * TAU[i // 24]] for i, b in enumerate(bnC))
# Q <= sum_g bn_g PER^2 / g < 2^63 (scalar Nat arithmetic in the evaluator)
qmax = sum(Fr(bnC[i] * PER * PER, dC[i % 24] * TAU[i // 24]) for i in range(96))
assert qmax < 2 ** 63, float(qmax)
def spf(n):
    d = 2
    while n % d: d += 1
    return d
idx = {g: i for i, g in enumerate(dC)}
plan = []
for g in sorted(dC, reverse=True):
    if g == PERC: continue
    q = spf(PERC // g)
    plan.append((idx[g], idx[g * q], q))

# independent options: phi_p(r)(u, y) = [2^(j(u, y)) mod p != r], j = the class mod o_p with j = u (m_p), j = y (q)
def jidx(m_, q, u, y):
    o = m_ * q
    js = [j for j in range(o) if j % m_ == u % m_ and j % q == y]
    assert len(js) == 1
    return js[0]
IND = {43: (2, 7), 29: (4, 7), 23: (1, 11)}
for p, (m_, q) in IND.items():
    o = m_ * q
    assert min(k for k in range(1, p) if pow(2, k, p) == 1) == o
    for e in range(PER):
        assert e % o == jidx(m_, q, e % 4, e % q)
# closed forms used in Lean: j43 = ((u % 2) * 7 + 8 y) % 14, j29 = ((u % 4) * 21 + 8 y) % 28, j23 = y
for u in range(4):
    for y in range(7):
        assert jidx(2, 7, u, y) == ((u % 2) * 7 + 8 * y) % 14 and jidx(4, 7, u, y) == ((u % 4) * 21 + 8 * y) % 28
    for y in range(11):
        assert jidx(1, 11, u, y) == y
def phi(p, r, u, y):
    m_, q = IND[p]
    return 0 if pow(2, jidx(m_, q, u, y), p) == r else 1
def tables(ph, q):
    f = [sum(ph(u, y) for y in range(q)) for u in range(4)]
    W = [sum(ph(u, y) * ph(v, y) for y in range(q)) for u in range(4) for v in range(4)]
    return tuple(f), tuple(W)
def patterns(keys):
    pats, sig, wts = [], [], []
    for k in keys:
        if k not in pats:
            pats.append(k); wts.append(0)
        i = pats.index(k); sig.append(i); wts[i] += 1
    return pats, sig, wts
k7 = [tables(lambda u, y: phi(43, r43, u, y) * phi(29, r29, u, y), 7) for r43 in range(43) for r29 in range(29)]
pat7, sig7, w7 = patterns(k7)
k11 = [tables(lambda u, y: phi(23, r23, u, y), 11) for r23 in range(23)]
pat11, sig11, w11 = patterns(k11)
# grouping by the tables (f, W) is at least as coarse as the orbits of Section 6 of the paper: 19 <= 23 for q = 7
assert len(pat7) <= 23 and sum(w7) == 43 * 29 and len(pat11) == 2 and sum(w11) == 23, (len(pat7), len(pat11))
print("w7", w7, "w11", w11, file=sys.stderr)
f7 = [x for f, W in pat7 for x in f]; q7 = [x for f, W in pat7 for x in W]
f11 = [x for f, W in pat11 for x in f]; q11 = [x for f, W in pat11 for x in W]

# Pintz index (tightness only): J = 1 + floor(8 kap (Q / (2^32 s) + 27720 R0t)), as 1 + ((Q / (256 s)) KM + KC) / 2^48
C0up = Fr(33008090792343479, 50000000000000000)
log2lo = Fr(693147180559945309, 10 ** 18); log2hi = Fr(69314718055994531, 10 ** 17)
ELL = [3, 5, 7, 11, 13, 17, 31, 241, 41, 19, 73, 37, 23, 43, 29]
pell = Fr(1); ellN = 1; philN = 1
for p in ELL:
    pell *= Fr(p - 1, p - 2); ellN *= p; philN *= p - 1
assert pell == Fr(24159191040, 4458927161)
kap = C0up * pell / (PER * log2lo)
norm = Fr(ellN, philN) / (PER * log2hi)
tl = open(f"{ROOT}/RCert/M3G/TeffLit.lean").read()
mr = re.search(r"def R0tLit : Rat := \((\d+) : Rat\) / (\d+)\n", tl)
R0t = Fr(int(mr.group(1)), int(mr.group(2)))
assert R0t == Fr(705564034673165133, 3602879701896396800000)
KM = round(8 * kap * 2 ** 24)
KC = round(8 * kap * PER * R0t * 2 ** 48)
# V4g: mu, lambda_J = max(mu, norm / (J (J + 1))), i*(J) with norm / (i (i + 1)) <= lambda <= norm / ((i - 1) i)
MU = Fr(687217, 10 ** 12)
istar = [1]
for J in range(1, 64):
    lam = max(MU, norm / (J * (J + 1)))
    i = 1
    while not (norm / (i * (i + 1)) <= lam): i += 1
    assert i == 1 or lam <= norm / ((i - 1) * i)
    istar.append(i)
print(f"kap={float(kap):.6e} norm={float(norm):.6e} mu/norm={float(MU / norm):.4e} KM={KM} KC={KC} "
      f"plan cost={sum(dC[I] for i, I, q in plan)} qmax/2^63={float(qmax / 2 ** 63):.3f} istar={istar}", file=sys.stderr)

def arr(xs, per_line=24):
    xs = [str(x) for x in xs]
    if len(xs) <= per_line: return "#[" + ", ".join(xs) + "]"
    rows = [", ".join(xs[i:i + per_line]) for i in range(0, len(xs), per_line)]
    return "#[" + (",\n  ").join(rows) + "]"
L = []
L.append("/-! U3g/V4g stage 2: constants of the evaluator (generated by u3g/tools/gen_evg.py). -/")
L.append("")
L.append("namespace R45.EVG")
L.append("")
L.append("/-- The divisors of 360 (increasing). -/")
L.append("def dC : Array Nat := " + arr(dC))
L.append("")
L.append("/-- `⌈B_g 2^32⌉` for `g = dC[c] τ_t`, `τ = (1, 7, 11, 77)`, at index `24 t + c`. -/")
L.append("def bnC : Array Nat := " + arr(bnC, 8))
L.append("")
L.append("/-- The index of `dC[c] τ_t` in `divG`, at index `24 t + c`. -/")
L.append("def gIdx : Array Nat := " + arr(gIdx))
L.append("")
L.append("/-- The count plan `(i, I, q)` at period 360: `dC[I] = q dC[i]`, parents before children. -/")
L.append("def plan : List (Nat × Nat × Nat) := [" + ", ".join(f"({a}, {b}, {c})" for a, b, c in plan) + "]")
L.append("")
L.append(f"/-- The numbers of patterns of q = 7 and q = 11. -/")
L.append(f"def np7 : Nat := {len(pat7)}")
L.append(f"def np11 : Nat := {len(pat11)}")
L.append("")
L.append(f"/-- q = 7 (primes 43, 29): the {len(pat7)} patterns `(weight, f(u), W(u, v))`; `sig7[29 r43 + r29]` is the pattern of the")
L.append("residues `(r43, r29)`. -/")
L.append("def w7 : Array Nat := " + arr(w7))
L.append("def f7 : Array Nat := " + arr(f7, 32))
L.append("def q7 : Array Nat := " + arr(q7, 32))
L.append("def sig7 : Array Nat := " + arr(sig7, 29))
L.append("")
L.append("/-- q = 11 (prime 23): the 2 patterns; `sig11[r23]`. -/")
L.append("def w11 : Array Nat := " + arr(w11))
L.append("def f11 : Array Nat := " + arr(f11))
L.append("def q11 : Array Nat := " + arr(q11, 32))
L.append("def sig11 : Array Nat := " + arr(sig11, 32))
L.append("")
L.append("/-- Constants of the Pintz index (tightness only): `8 κ 2^24` and `8 κ 27720 R0t 2^48`, rounded. -/")
L.append(f"def KM : Nat := {KM}")
L.append(f"def KC : Nat := {KC}")
L.append("")
L.append("/-- The tail mass `R0t` of stage 1 (equal to `M3G.R0tLit`, copied so that the evaluator does not import the table). -/")
L.append(f"def R0tG : Rat := ({mr.group(1)} : Rat) / {mr.group(2)}")
L.append("")
L.append("/-- V4g: the integer `i*(J)` minimizing `norm/i + λ_J (i - 1)`, `λ_J = max(μ, norm/(J(J+1)))` (index `J < 64`). -/")
L.append("def istarV : Array Nat := " + arr(istar, 32))
L.append("")
L.append("end R45.EVG")
open(f"{ROOT}/RCert/G/EvData.lean", "w").write("\n".join(L) + "\n")
print("wrote RCert/G/EvData.lean", file=sys.stderr)
