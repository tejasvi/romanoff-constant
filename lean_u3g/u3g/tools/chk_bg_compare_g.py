"""U3g/V4g (period 27720): float re-computation of the r45a-u3f checker's divisor-form B_g (steps [1]-[2b] of check_r45u3f.py, arb -> float),
compared with the Lean table BLit; prints the predicted vertex shift sum_g (B^chk_g - BLit_g) U_g, with the sensitivities
U_g = (V_0 - V_g) / (R0tail g) taken from the checker's vertex prints (R0tail approximated by the Lean R0tLit,
equal to the printed 1.9583e-04).
Usage: chk_bg_compare_g.py CERTS_U3G_DIR BLIT_LEAN LOG [LOG2]  (e.g. certs_u3g RCert/G/BLit.lean logs/u3f_u3g27720_96663daa.log logs/u3f_v4g27720_6557658d.log)"""
import json, math, re, sys, time
from fractions import Fraction as Fr
t0 = time.time()
D = sys.argv[1].rstrip('/') + '/'
fac = json.load(open(D + 'fac300_41e4cdd6.json')); facb = json.load(open(D + 'fac1200_fdb_af082adc.json'))
ELL = [3, 5, 7, 11, 13, 17, 31, 241, 41, 19, 73, 23, 37, 43, 29]; PER = 27720; LMAX = 3_000_000; T0 = 300; T1 = 1200
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
pt = sorted((p, t) for p, t in prim if p not in ELL)
print("primes", len(prim), "pt", len(pt), file=sys.stderr)
W = {1: 1.0}; dropped = 0.0
for p, t in pt:
    f = 1.0 / (p - 2); new = dict(W)
    for L, w in W.items():
        L2 = L * t // math.gcd(L, t)
        if L2 > LMAX: dropped += w * f; continue
        new[L2] = new.get(L2, 0.0) + w * f
    W = new
prodall = 1.0
for p, t in pt: prodall *= 1 + 1.0 / (p - 2)
prune = dropped * prodall * PER / LMAX
print("DP states", len(W), "dropped", dropped, "prodall", prodall, "prune", prune, f"{time.time()-t0:.0f}s", file=sys.stderr)
divs = [g for g in range(1, PER + 1) if PER % g == 0]
Ta = {g: 0.0 for g in divs}
for L, w in W.items():
    g = math.gcd(L, PER); Ta[g] += w * g / L
Mt = {}
for t in range(T0 + 1, T1 + 1):
    for q, e in facb[str(t)]:
        q = int(q)
        if math.gcd(q, t) != 1 or q >= 10 ** 100: continue
        Mt.setdefault(t, []).append(q)
Tb = {g: 0.0 for g in divs}; Fsum = 0.0
items = list(W.items())
for t, qs in Mt.items():
    Ft = sum(1.0 / (q - 2) for q in qs); Fsum += Ft
    A = {}
    for L, w in items:
        Lp = L // math.gcd(L, t) * t; gp = math.gcd(Lp, PER)
        A[gp] = A.get(gp, 0.0) + w * gp / Lp
    for g, a in A.items(): Tb[g] += Ft * a
pruneb = dropped * prodall * PER / LMAX * Fsum
print("class b t's", len(Mt), "Fsum", Fsum, "pruneb", pruneb, f"{time.time()-t0:.0f}s", file=sys.stderr)
Bchk = {g: Ta[g] + Tb[g] for g in divs}; Bchk[1] += prune + pruneb
s = open(sys.argv[2]).read()
BL = {int(g): float(Fr(int(a), int(b))) for g, a, b in re.findall(r"\((\d+), \((\d+) : Rat\) / (\d+)\)", s)}
for LOG in sys.argv[3:]:
    txt = open(LOG).read()
    vals = {int(g): float(v) for g, v in re.findall(r'e_(\d+): minorant ([0-9.]+)', txt)}
    V0 = float(re.search(r'vertex alpha = 0: minorant ([0-9.]+)', txt).group(1))
    R0 = 705564034673165133 / 3602879701896396800000
    U = {g: (V0 - vals[g]) / (R0 * g) for g in divs}
    print(LOG); print("sum Bchk", sum(Bchk.values()), "sum BLit", sum(BL.values()))
    dV = 0.0
    for g in divs:
        d = Bchk[g] - BL[g]; dV += d * U[g]
        if abs(d) > 1e-9 or g in (1, 2, 3, 4, 27720): print(f"g={g:5d} Bchk={Bchk[g]:.12e} BLit={BL[g]:.12e} diff={d:+.3e} U={U[g]:.4e} contrib={d*U[g]:+.3e}")
    print("predicted V_lean - V_chk(e_27720) =", dV, " -> V_lean ~", vals[27720] + dV)
print(f"{time.time()-t0:.0f}s", file=sys.stderr)
