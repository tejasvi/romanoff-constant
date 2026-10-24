"""Independent cross-check of the U3e stage-2 evaluator on one BASE key (numpy, as the r45a-u3e checker):
per Pintz slot J the sums (sum w s, sum w Q), Q = sum_g bn_g S_g, J = jIdx(s, Q).  Usage: xcheck_key.py INDEX"""
import sys, math, re
import numpy as np
idx = int(sys.argv[1]); ROOT = sys.argv[2]
PER = 3960; PER0 = 120
divs = [g for g in range(1, PER + 1) if PER % g == 0]
src = open(f"{ROOT}/RCert/E/EvData.lean").read()
bn = [int(t) for t in re.search(r"def bnA : Array Nat := #\[([^\]]*)\]", src).group(1).split(",")]
KM = int(re.search(r"def KM : Nat := (\d+)", src).group(1)); KC = int(re.search(r"def KC : Nat := (\d+)", src).group(1))
def mask(per, p, r):
    m = 0
    for e in range(per):
        if pow(2, e, p) == r: m |= 1 << e
    return m
def optsP(per, p):
    nz = [(mask(per, p, r), 1) for r in range(p) if mask(per, p, r) != 0]
    return nz + [(0, sum(1 for r in range(p) if mask(per, p, r) == 0))]
F0 = (1 << PER0) - 1
def canon(x):
    b = x; y = x
    for _ in range(PER0):
        y = ((y << 1) | (y >> (PER0 - 1))) & F0; b = min(b, y)
    return b
L = {0: 1}
for p in [3, 5, 7, 11, 13, 17, 31, 241]:
    o = optsP(PER0, p); new = {}
    for x, c in L.items():
        for m, d in o:
            k = canon(x | m); new[k] = new.get(k, 0) + c * d
    L = new
keys = sorted(L.items())
y, cnt = keys[idx]
R = sum(1 << (120 * i) for i in range(33))
x = y * R
print("key popcount", bin(x).count("1"), "cnt", cnt)
def row(m): return np.array([0 if (m >> e) & 1 else 1 for e in range(PER)], dtype=np.int64)
b = row(x)
opts = {p: [(row(m), w) for m, w in optsP(PER, p)] for p in [41, 19, 73, 23]}
pre = []
for r1, w1 in opts[41]:
    a1 = b * r1
    for r2, w2 in opts[19]:
        a2 = a1 * r2
        for r3, w3 in opts[73]:
            a3 = a2 * r3
            for r4, w4 in opts[23]:
                pre.append((a3 * r4, w1 * w2 * w3 * w4))
print("prefix rows", len(pre))
A = {}; Qs = {}
bnv = np.array(bn, dtype=np.int64)
for c0 in range(0, len(pre), 1000):
    X = np.array([r for r, w in pre[c0:c0 + 1000]], dtype=np.int64); W = [w for r, w in pre[c0:c0 + 1000]]
    n1 = len(W)
    # all 37 options of 37: none, then classes j mod 36
    rows = [X]
    for j in range(36):
        Y = X.copy(); Y[:, j::36] = 0; rows.append(Y)
    for Y in rows:
        s = Y.sum(axis=1)
        S = np.stack([(Y.reshape(n1, PER // g, g).sum(axis=1) ** 2).sum(axis=1) for g in divs], axis=1)
        Q = S @ bnv
        for k in range(n1):
            sk = int(s[k]); qk = int(Q[k])
            J = 1 if sk == 0 else min(63, 1 + (qk // (sk * 256) * KM + KC) // 2 ** 56)
            A[J] = A.get(J, 0) + W[k] * sk; Qs[J] = Qs.get(J, 0) + W[k] * qk
out = [0] * 128
for J in A: out[2 * J] = A[J]; out[2 * J + 1] = Qs[J]
print("PY", out)
