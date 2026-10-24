"""Dual-only producer: maximize the Lagrangian bound Lambda(mu) over budget multipliers mu(c) >= 0 (crude tail mode),
vectorized over orbits, by a cutting-plane (Kelley) method with a trust region; HiGHS solves the small master LP.
Lambda(mu) = sum_u min_{0<=y<=ymax} [w_u phi(1+Y/s_u) + d_u sum_c mu_c y_c] - sum_c mu_c budget_c   (concave in mu).
Usage: dual_opt.py PARAMS.json TAILS.json OUT_CERT.json [iters]"""
import json, sys, math, time
from fractions import Fraction as Fr
import numpy as np, highspy
sys.path.insert(0, ".")
from patterns_fast import patterns, orbits, orbit_arrays
par = json.load(open(sys.argv[1])); tl = json.load(open(sys.argv[2])); out = sys.argv[3]
iters = int(sys.argv[4]) if len(sys.argv) > 4 else 300
ELL = par["ELL"]; CAP = float(Fr(par["CAP"])); C1 = float(Fr(par["C1"]))
t0 = time.time()
PER, pat = patterns(ELL); reps = orbits(PER, pat); keys, cnt, size, nU = orbit_arrays(PER, reps)
ell = 1; phil = 1
for p in ELL: ell *= p; phil *= p - 1
Pell = Fr(1)
for p in ELL: Pell *= Fr(p - 1, p - 2)
kappa = float(Fr(par["C0_up"]) * Pell / (PER * Fr(par["log2_low"]))); norm = float(Fr(ell, phil) / (PER * Fr(par["log2_up"])))
T = np.array([float(Fr(x)) for x in tl["T_up"]]); R0tail = float(Fr(par["R0_up"]) - Fr(tl["R0s_low"]))
Teff = T + np.array([math.gcd(c, PER) for c in range(PER)]) * R0tail
dens = np.array([float(Fr(int(c), ell)) for c in cnt]); s = size.astype(float); w = norm * dens * s
caps = CAP * kappa * nU * Teff[None, :]                       # [P, PER]
budget = C1 * kappa * Teff * (dens[:, None] * nU).sum(0)
P = len(keys); print(f"PER={PER} orbits={P} ({time.time()-t0:.1f}s)", flush=True)
def phi(D):
    f = np.floor(D); c = np.ceil(D)
    return np.where(c == f, 1.0 / D, (c + f - D) / (c * f))
def lam(mu):
    order = np.argsort(mu, kind="stable")
    cp = caps[:, order]; cum = np.concatenate([np.zeros((P, 1)), np.cumsum(cp, 1)], 1)
    cost = np.concatenate([np.zeros((P, 1)), np.cumsum(cp * mu[order][None, :], 1)], 1)
    best = np.full(P, np.inf); bY = np.zeros(P)
    for j in range(PER + 1):
        g = w * phi(1 + cum[:, j] / s) + dens * cost[:, j]
        u = g < best; best[u] = g[u]; bY[u] = cum[u, j]
    Ymax = cum[:, -1]; rows = np.arange(P)
    for jj in range(1, int(np.ceil((1 + Ymax / s).max())) + 1):
        Y = s * (jj - 1); ok = Y <= Ymax
        if not ok.any(): break
        idx = np.minimum((cum <= Y[:, None]).sum(1) - 1, PER - 1)
        c0, c1 = cum[rows, idx], cum[rows, idx + 1]; k0, k1 = cost[rows, idx], cost[rows, idx + 1]
        K = k0 + np.where(c1 > c0, (Y - c0) / np.where(c1 > c0, c1 - c0, 1), 0) * (k1 - k0)
        g = w * phi(1 + Y / s) + dens * K
        u = ok & (g < best); best[u] = g[u]; bY[u] = Y[u]
    fill = np.clip(bY[:, None] - cum[:, :-1], 0, cp)
    load = np.zeros(PER); load[order] = (dens[:, None] * fill).sum(0)
    return best.sum() - mu @ budget, load - budget          # value, supergradient
# 1) uniform multiplier: Lambda(m * 1) is concave in the scalar m; golden-section search
def lam1(m): return lam(np.full(PER, m))[0]
a, b = 0.0, 1e-2
while lam1(b) > lam1(b / 2) and b < 1e3: b *= 2
gr = (math.sqrt(5) - 1) / 2
x1, x2 = b - gr * (b - a), a + gr * (b - a); f1, f2 = lam1(x1), lam1(x2)
for _ in range(200):
    if f1 < f2: a, x1, f1 = x1, x2, f2; x2 = a + gr * (b - a); f2 = lam1(x2)
    else: b, x2, f2 = x2, x1, f1; x1 = b - gr * (b - a); f1 = lam1(x1)
    if b - a < 1e-15: break
m0 = (a + b) / 2
print(f"uniform mu = {m0:.6e}: Lambda = {lam1(m0):.9f} ({time.time()-t0:.0f}s)", flush=True)
# 2) Kelley cutting planes with box trust region around the uniform solution
mu = np.full(PER, m0); cuts = []; bestv, bestmu = lam1(m0), mu.copy(); R = m0 * 0.1
for it in range(iters):
    v, g = lam(mu)
    if v > bestv: bestv, bestmu = v, mu.copy()
    cuts.append((v - g @ mu, g.copy()))
    h = highspy.Highs(); h.setOptionValue("output_flag", False); inf = highspy.kHighsInf
    lo = np.maximum(bestmu - R, 0); hi = bestmu + R
    h.addVars(PER + 1, np.concatenate([lo, [-inf]]), np.concatenate([hi, [inf]]))
    h.changeColsCost(PER + 1, np.arange(PER + 1, dtype=np.int32), np.concatenate([np.zeros(PER), [-1.0]]))
    for a, gg in cuts:          # theta <= a + gg.mu
        h.addRow(-a, inf, PER + 1, np.arange(PER + 1, dtype=np.int32), np.concatenate([gg, [-1.0]]))
    h.run(); sol = np.array(h.getSolution().col_value); ub = sol[-1]
    mu = np.maximum(sol[:PER], 0)
    if it % 20 == 0: print(f"it {it}: best {bestv:.9f} model-ub {ub:.9f} R {R:.3g} ({time.time()-t0:.0f}s)", flush=True)
    if ub - bestv < 1e-10: R *= 0.5
    if ub - bestv < 1e-11 and R < 1e-6: break
print(f"best Lambda = {bestv:.9f}", flush=True)
cert = dict(format="r45a-v2", tail_mode="crude", params=par, PER=PER, n_orbits=P, lp_obj=float(bestv),
            duals=[[["bud", c], repr(float(x))] for c, x in enumerate(bestmu) if x > 0],
            note="budget multipliers from dual_opt.py (Lagrangian, crude class-(c) tail). Evaluate ONLY with check_r45a5_rel.py and the class-(b) data: python -I check_r45a5_rel.py fac300.json CERT 3000000 fac1200_fdb.json 1200 --claim VALUE (omitting fac1200/1200 gives a smaller bound; check_r45a3/4 are withdrawn)")
json.dump(cert, open(out, "w"))
print("wrote", out)
