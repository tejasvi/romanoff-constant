"""Producer v2 (vectorized): combined adversary LP with aggregated Y_u, solve with HiGHS IPM, write the dual certificate.
Columns: y[u,c] (n_u(c) > 0), alpha[g] (g | PER), Y[u], z[u].
Rows (all >=):  cap[u,c]:  -y + sum_{g|c} CAP k n g alpha_g >= -CAP k n T(c)
                bud[c]:    -sum_u d_u y[u,c] + sum_{g|c} C1 k N(c) g alpha_g >= -C1 k N(c) T(c)
                tail:      -sum_g alpha_g >= -R0tail
                sum[u]:    sum_c y[u,c] - Y[u] >= 0
                epi[u,j]:  z[u] + Y[u]/(s j (j+1)) >= 2/(j+1),  j = 1..J_u
Usage: cert_build2.py PARAMS.json TAILS.json OUT_CERT.json"""
import json, sys, math, time
from fractions import Fraction as Fr
import os
import numpy as np, highspy
CRUDE = os.environ.get("CRUDE") == "1"
sys.path.insert(0, ".")
from patterns_fast import patterns, orbits, orbit_arrays

par = json.load(open(sys.argv[1])); tl = json.load(open(sys.argv[2])); out = sys.argv[3]
ELL = par["ELL"]; CAP = Fr(par["CAP"]); C1 = Fr(par["C1"]); C0up = Fr(par["C0_up"])
log2lo = Fr(par["log2_low"]); log2hi = Fr(par["log2_up"]); R0up = Fr(par["R0_up"])
t0 = time.time()
PER, pat = patterns(ELL)
assert PER == tl["PER"] and tl["ELL"] == ELL
reps = orbits(PER, pat)
keys, cnt, size, nU = orbit_arrays(PER, reps)
ell = 1; phil = 1
for p in ELL: ell *= p; phil *= p - 1
Pell = Fr(1)
for p in ELL: Pell *= Fr(p - 1, p - 2)
kappa = float(C0up * Pell / (PER * log2lo)); norm = float(Fr(ell, phil) / (PER * log2hi))
T = np.array([float(Fr(x)) for x in tl["T_up"]])
R0tail = float(R0up - Fr(tl["R0s_low"]))
dens = np.array([float(Fr(int(c), ell)) for c in cnt])
CAPf, C1f = float(CAP), float(C1)
P = len(keys); divs = [g for g in range(1, PER + 1) if PER % g == 0]; G = len(divs)
print(f"PER={PER} patterns={len(pat)} orbits={P} R0tail={R0tail:.4e} ({time.time()-t0:.1f}s)", flush=True)
uu, cc = np.nonzero(nU)                     # y columns
ny = len(uu)
yidx = -np.ones((P, PER), dtype=np.int64); yidx[uu, cc] = np.arange(ny)
gcdc = np.array([math.gcd(c, PER) for c in range(PER)], dtype=float)
Teff = T + gcdc * R0tail
ymax = CAPf * kappa * nU[uu, cc] * (Teff[cc] if CRUDE else (T[cc] + PER * R0tail))
ia = ny + np.arange(G); iY = ny + G + np.arange(P); iz = ny + G + P + np.arange(P)
ncol = ny + G + 2 * P
Ymax = np.bincount(uu, weights=ymax, minlength=P)
lo = np.zeros(ncol); hi = np.concatenate([ymax, np.full(G, R0tail), Ymax, np.ones(P)])
cost = np.zeros(ncol); cost[iz] = norm * dens * size
h = highspy.Highs(); h.setOptionValue("output_flag", True); h.setOptionValue("log_to_console", False)
inf = highspy.kHighsInf
h.addVars(ncol, lo, hi)
h.changeColsCost(ncol, np.arange(ncol, dtype=np.int32), cost)
V = np.array([[g if c % g == 0 else 0 for g in divs] for c in range(PER)], dtype=np.float64)   # [PER, G]
rowkeys = []
def add_rows(lbs, starts, idx, val, keys_):
    h.addRows(len(lbs), np.asarray(lbs, float), np.full(len(lbs), inf), len(idx), np.asarray(starts, np.int32),
              np.asarray(idx, np.int32), np.asarray(val, float))
    rowkeys.extend(keys_)
# cap rows (vectorized)
gl = [np.nonzero(V[c])[0] for c in range(PER)]
idx, val, starts, lbs = [], [], [], []
pos = 0
for k in range(ny):
    u, c = uu[k], cc[k]
    starts.append(pos)
    idx.append(k); val.append(-1.0)
    coef = CAPf * kappa * nU[u, c]
    for gi in gl[c]:
        idx.append(ia[gi]); val.append(coef * V[c, gi])
    pos += 1 + len(gl[c])
    lbs.append(-coef * T[c])
if not CRUDE: add_rows(lbs, starts, idx, val, [("cap", int(keys[u]), int(c)) for u, c in zip(uu, cc)])
print(f"  cap rows {ny} ({time.time()-t0:.1f}s)", flush=True)
Nc = (dens[:, None] * nU).sum(0)
idx, val, starts, lbs = [], [], [], []; pos = 0
for c in range(PER):
    starts.append(pos)
    us = np.nonzero(nU[:, c])[0]
    idx.extend(yidx[us, c].tolist()); val.extend((-dens[us]).tolist())
    if not CRUDE:
        for gi in gl[c]:
            idx.append(ia[gi]); val.append(C1f * kappa * Nc[c] * V[c, gi])
    pos += len(us) + (0 if CRUDE else len(gl[c])); lbs.append(-C1f * kappa * Nc[c] * (Teff[c] if CRUDE else T[c]))
add_rows(lbs, starts, idx, val, [("bud", c) for c in range(PER)])
if not CRUDE: add_rows([-R0tail], [0], ia.tolist(), [-1.0] * G, [("tail",)])
idx, val, starts, lbs = [], [], [], []; pos = 0
order = np.argsort(uu, kind="stable")
bounds = np.searchsorted(uu[order], np.arange(P + 1))
for u in range(P):
    ks = order[bounds[u]:bounds[u + 1]]
    starts.append(pos); idx.extend(ks.tolist()); val.extend([1.0] * len(ks)); idx.append(iY[u]); val.append(-1.0)
    pos += len(ks) + 1; lbs.append(0.0)
add_rows(lbs, starts, idx, val, [("sum", int(keys[u])) for u in range(P)])
idx, val, starts, lbs, ek = [], [], [], [], []; pos = 0
for u in range(P):
    s = int(size[u]); J = int(math.floor(1 + Ymax[u] / s))
    for j in range(1, J + 1):
        starts.append(pos); idx.extend([iz[u], iY[u]]); val.extend([1.0, 1.0 / (s * j * (j + 1))]); pos += 2
        lbs.append(2.0 / (j + 1)); ek.append(("epi", int(keys[u]), j))
add_rows(lbs, starts, idx, val, ek)
print(f"LP: {ncol} cols, {len(rowkeys)} rows ({time.time()-t0:.1f}s)", flush=True)
h.setOptionValue("solver", "ipm"); h.setOptionValue("run_crossover", "on"); h.setOptionValue("threads", 1)
h.run()
st = h.modelStatusToString(h.getModelStatus()); obj = h.getInfo().objective_function_value
u = np.maximum(np.array(h.getSolution().row_dual), 0.0)
print(f"status {st} obj {obj:.9f} ({time.time()-t0:.1f}s)", flush=True)
cert = dict(format="r45a-v2", tail_mode=("crude" if CRUDE else "alpha"), params=par, PER=PER, lp_obj=obj, n_orbits=P,
            duals=[[list(k), repr(float(x))] for k, x in zip(rowkeys, u) if x > 0])
json.dump(cert, open(out, "w"))
print(f"wrote {out}: {len(cert['duals'])} nonzero duals")
