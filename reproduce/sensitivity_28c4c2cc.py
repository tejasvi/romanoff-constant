"""Sensitivity of the Lagrangian bound (uniform multiplier, crude class-(c) tail) to the two sieve constants.
Usage: sensitivity.py PARAMS.json TAILS.json"""
import json, sys, math
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, ".")
from patterns_fast import patterns, orbits, orbit_arrays
par = json.load(open(sys.argv[1])); tl = json.load(open(sys.argv[2]))
ELL = par["ELL"]
PER, pat = patterns(ELL); reps = orbits(PER, pat); keys, cnt, size, nU = orbit_arrays(PER, reps)
ell = 1; phil = 1
for p in ELL: ell *= p; phil *= p - 1
Pell = Fr(1)
for p in ELL: Pell *= Fr(p - 1, p - 2)
kappa = float(Fr(par["C0_up"]) * Pell / (PER * Fr(par["log2_low"]))); norm = float(Fr(ell, phil) / (PER * Fr(par["log2_up"])))
T = np.array([float(Fr(x)) for x in tl["T_up"]]); R0tail = float(Fr(par["R0_up"]) - Fr(tl["R0s_low"]))
Teff = T + np.array([math.gcd(c, PER) for c in range(PER)]) * R0tail
dens = np.array([float(Fr(int(c), ell)) for c in cnt]); s = size.astype(float); w = norm * dens * s
base = kappa * (nU * Teff[None, :]).sum(1)          # per-orbit total capacity per unit constant
Btot = kappa * (Teff * (dens[:, None] * nU).sum(0)).sum()
def phi(D):
    f = np.floor(D); c = np.ceil(D)
    return np.where(c == f, 1.0 / D, (c + f - D) / (c * f))
def lam(m, CAP, C1):
    Ymax = CAP * base
    best = np.minimum(w * phi(1.0 + 0 * s), w * phi(1 + Ymax / s) + dens * m * Ymax)
    jmax = int(np.ceil((1 + Ymax / s).max())) + 1
    for jj in range(1, jmax + 1):
        Y = s * (jj - 1); ok = Y <= Ymax
        g = w * phi(1 + np.minimum(Y, Ymax) / s) + dens * m * np.minimum(Y, Ymax)
        best = np.where(ok, np.minimum(best, g), best)
    return best.sum() - m * C1 * Btot
def opt(CAP, C1):
    a, b = 0.0, 1e-2; gr = (math.sqrt(5) - 1) / 2
    x1, x2 = b - gr * (b - a), a + gr * (b - a); f1, f2 = lam(x1, CAP, C1), lam(x2, CAP, C1)
    for _ in range(120):
        if f1 < f2: a, x1, f1 = x1, x2, f2; x2 = a + gr * (b - a); f2 = lam(x2, CAP, C1)
        else: b, x2, f2 = x2, x1, f1; x1 = b - gr * (b - a); f1 = lam(x1, CAP, C1)
    return lam((a + b) / 2, CAP, C1)
print(f"PER={PER} orbits={len(keys)}")
for CAP, C1 in [(8, 8), (8, 7.8209), (8, 6.7814), (8, 6.5), (8, 6.0), (8, 5.0), (8, 4.0), (7.8209, 6.7814), (7.8209, 7.8209), (6.7814, 6.7814), (4, 4)]:
    print(f"CAP={CAP:<7} C1={C1:<7} d >= {opt(CAP, C1):.6f}", flush=True)
