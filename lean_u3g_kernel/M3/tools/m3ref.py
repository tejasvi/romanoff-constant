"""Reference implementation (Python integers) of the M3 checker arithmetic, mirroring the Lean checker exactly.

usage: m3ref.py PRATT.json TAILS.json [FTHRESH_EXP]
Fixed point SC = 2^64.  T-DP over groups of A (non-ell, by order), entries (L, a, b) = (lcm, lower, upper numerators),
pruned at LMAX; R0-DP = T-DP table continued with the ell groups (lower only used).
"""
import json, sys, math, time
from fractions import Fraction as Fr
SC = 1 << 64; LMAX = 3_000_000; PER = 120
R0UP = Fr(193656, 100000)
ELL = [3, 5, 7, 11, 13, 17, 31, 41, 241]
DIV120 = [g for g in range(1, PER + 1) if PER % g == 0]
def fUp(p): return (SC + p - 3) // (p - 2)
def fLo(p): return SC // (p - 2)
def mulUp(x, y): return (x * y + SC - 1) // SC
def mulLo(x, y): return x * y // SC
def eUp(ps):
    acc = SC
    for p in ps: acc = mulUp(acc, SC + fUp(p))
    return acc - SC
def eLo(ps):
    acc = SC
    for p in ps: acc = mulLo(acc, SC + fLo(p))
    return acc - SC
def groups(lst):
    g = {}
    for p, t in lst: g.setdefault(t, []).append(p)
    return [(t, sorted(g[t])) for t in sorted(g)]
import os
KAPPA = int(os.environ.get("KAPPA", "0"))
DROP = [0]
def step(tab, t, ea, eb):
    new = dict(tab)
    for L, (a, b) in tab.items():
        L2 = L * t // math.gcd(L, t)
        if L2 <= LMAX:
            x = new.get(L2, (0, 0))
            new[L2] = (x[0] + mulLo(a, ea), x[1] + mulUp(b, eb))
    if KAPPA:
        keep = {}
        for L, (a, b) in new.items():
            if b < KAPPA * L: DROP[0] += (b + L - 1) // L
            else: keep[L] = (a, b)
        new = keep
    return new
if __name__ == "__main__":
    t00 = time.time()
    d = json.load(open(sys.argv[1])); tails = json.load(open(sys.argv[2]))
    FT = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-12
    A = [(p, t) for p, t in d["A"] if p not in ELL]; E = [(p, t) for p, t in d["A"] if p in ELL]; B = d["B"]
    gA, gE, gB = groups(A), groups(E), groups(B)
    print(f"groups A {len(gA)} ({len(A)} primes), E {len(gE)}, B {len(gB)} ({len(B)} primes)", flush=True)
    tab = {1: (SC, SC)}
    PiUp = SC
    for t, ps in gA:
        ea, eb = eLo(ps), eUp(ps)
        tab = step(tab, t, ea, eb)
        PiUp = mulUp(PiUp, SC + eb)
    DT = DROP[0]
    print(f"T table {len(tab)} entries, dropped D = {DT} ({DT/SC:.3e}) ({time.time()-t00:.0f}s)", flush=True)
    sumA = sum(a for L, (a, b) in tab.items())
    Pr = PiUp - sumA
    print(f"PiUp {PiUp/SC:.15f} sumA {sumA/SC:.15f} pruned mass <= {Pr/SC:.6e}")
    Lg = {g: 0 for g in DIV120}
    for L, (a, b) in tab.items():
        g = math.gcd(L, PER); Lg[g] += (b * g + L - 1) // L
    Ta = [sum(Lg[g] for g in DIV120 if c % g == 0) for c in range(PER)]
    prune = [(Pr * math.gcd(c, PER) + LMAX - 1) // LMAX + (math.gcd(c, PER) * PiUp * DT + SC - 1) // SC for c in range(PER)]
    # class B
    sumB = sum(b for L, (a, b) in tab.items())
    tabR = tab
    for t, ps in gE:
        tabR = step(tabR, t, eLo(ps), eUp(ps))
    print(f"R0 table {len(tabR)} entries ({time.time()-t00:.0f}s)", flush=True)
    R0a = sum(a // L for L, (a, b) in tabR.items())
    R0aR = sum(Fr(a, L) for L, (a, b) in tabR.items())
    Tb = [0] * PER; R0b = 0; nex = 0
    for t, ps in gB:
        FU = sum(fUp(q) for q in ps); FL = sum(fLo(q) for q in ps)
        if FU >= FT * SC:
            nex += 1
            Ag = {g: 0 for g in DIV120}
            for L, (a, b) in tab.items():
                L2 = L * t // math.gcd(L, t); g = math.gcd(L2, PER); Ag[g] += (b * g + L2 - 1) // L2
            At = [sum(Ag[g] for g in DIV120 if c % g == 0) for c in range(PER)]
            r = 0
            for L, (a, b) in tabR.items():
                r += a // (L * t // math.gcd(L, t))
        else:
            At = [(sumB * math.gcd(c, PER) + t - 1) // t for c in range(PER)]
            r = R0a // t
        for c in range(PER):
            Tb[c] += mulUp(FU, At[c] + prune[c])
        R0b += mulLo(FL, r)
    print(f"class B: {nex} exact passes of {len(gB)} ({time.time()-t00:.0f}s)", flush=True)
    R0tail = R0UP - Fr(R0a + R0b, SC)
    teff = [Fr(Ta[c] + prune[c] + Tb[c], SC) + math.gcd(c, PER) * R0tail for c in range(PER)]
    ref = [Fr(x) for x in tails["T_up"]]; rtail = Fr(tails["R0tail"])
    tref = [ref[c] + math.gcd(c, PER) * rtail for c in range(PER)]
    rel = [float((teff[c] - tref[c]) / tref[c]) for c in range(PER)]
    print(f"R0a {float(Fr(R0a, SC)):.15f} (exact-division {float(R0aR / SC):.15f}), R0b {float(Fr(R0b, SC)):.15f}")
    print(f"R0tail {float(R0tail):.15e} vs ref {float(rtail):.15e}: diff {float(R0tail - rtail):.3e}")
    print(f"T_a(0) {Ta[0]/SC:.12f} prune(0) {prune[0]/SC:.3e} T_b(0) {Tb[0]/SC:.6e}")
    print(f"teff(0) {float(teff[0]):.12f} ref {float(tref[0]):.12f}; rel diff min {min(rel):.3e} max {max(rel):.3e}")
    json.dump(dict(kappa=KAPPA, D=DT, teff=[str(x) for x in teff], R0tail=str(R0tail), Ta=Ta, prune=prune, Tb=Tb, R0a=R0a, R0b=R0b,
                   PiUp=PiUp, sumA=sumA, ntab=len(tab), ntabR=len(tabR), rel=rel), open(os.environ.get("REFOUT", "out/m3ref_out.json"), "w"))
    print(f"done ({time.time()-t00:.0f}s)")
