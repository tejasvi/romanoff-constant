"""Brute-force check of the U3g/V4g evaluator's row data at period 27720.
Input: the output of `gpilot row K R41 R19 R73 R37` (the core mask Y and (s_P, Q_P) for every pattern P).  For every
pattern, up to NS residue triples (r23, r43, r29) of that pattern (or all 23*43*29 triples with NS = 0) are expanded to
the full row U = {e < 27720 : e mod 360 not in Y, 2^e mod p != r_p (p = 23, 43, 29)}, and s = |U|,
Q = sum_{g | 27720} ceil(B_g 2^32) S_g(U), S_g = sum_a #{e in U : e = a (g)}^2 are compared with (s_P, Q_P).
Usage: python3 -I -B xcheck_row_g.py ROOT ROW_OUTPUT NS"""
import re, sys
from fractions import Fraction as Fr
import numpy as np

ROOT, ROWF, NS = sys.argv[1], sys.argv[2], int(sys.argv[3])
PER = 27720
txt = open(ROWF).read()
Y = int(re.search(r"^Y (\d+)$", txt, re.M).group(1))
rows = [tuple(map(int, l.split())) for l in txt.splitlines() if re.fullmatch(r"\d+ \d+", l)]
ev = open(f"{ROOT}/RCert/G/EvData.lean").read()
def arr(name):
    m = re.search(r"def " + name + r" : Array Nat := #\[([^\]]*)\]", ev)
    return [int(t) for t in m.group(1).replace("\n", " ").split(",")]
sig7, sig11 = arr("sig7"), arr("sig11")
np7 = int(re.search(r"def np7 : Nat := (\d+)", ev).group(1)); np11 = int(re.search(r"def np11 : Nat := (\d+)", ev).group(1))
assert len(rows) == np7 * np11, (len(rows), np7, np11)
blit = open(f"{ROOT}/RCert/G/BLit.lean").read()
B = {int(g): Fr(int(a), int(b)) for g, a, b in re.findall(r"\((\d+), \((\d+) : Rat\) / (\d+)\)", blit)}
divs = sorted(B)
assert divs == [g for g in range(1, PER + 1) if PER % g == 0]
bn = {g: -((-B[g].numerator * 2 ** 32) // B[g].denominator) for g in divs}
e = np.arange(PER)
core = np.array([0 if (Y >> (x % 360)) & 1 else 1 for x in range(PER)], dtype=np.int64)
pw = {p: np.array([pow(2, int(k), p) for k in e]) for p in (23, 43, 29)}
def rowdata(r23, r43, r29):
    U = core * (pw[23] != r23) * (pw[43] != r43) * (pw[29] != r29)
    idx = e[U == 1]
    Q = 0
    for g in divs:
        N = np.bincount(idx % g, minlength=g).astype(np.int64)
        Q += bn[g] * int((N * N).sum())                      # S_g <= |U|^2 < 2^30: exact in int64
    return int(U.sum()), Q
bad = 0; n = 0
for P in range(np7 * np11):
    a, b = P // np11, P % np11
    trip = [(r23, r43, r29) for r23 in range(23) if sig11[r23] == b for r43 in range(43) for r29 in range(29)
            if sig7[29 * r43 + r29] == a]
    if NS: trip = trip[:: max(1, len(trip) // NS)][:NS]
    for t in trip:
        sq = rowdata(*t); n += 1
        if sq != rows[P]:
            bad += 1
            print("MISMATCH P", P, "triple", t, "brute", sq, "lean", rows[P])
print(f"Y popcount {bin(Y).count('1')}; checked {n} rows over {np7 * np11} patterns; mismatches {bad}")
print("PASS" if bad == 0 else "FAIL")
