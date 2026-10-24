#!/usr/bin/env python3
"""Write RCert/G/BLit.lean: the divisor form B_g (g | 27720) of the M3 table at period 27720, by Moebius inversion of
tab(c) = teff(c) - gcd(c, 27720) R0t over the divisors; checks tabB(B)(c) = tab(c) for every c < 27720 and B_g >= 0.
Usage: gen_blit_g.py TEFFLIT.lean OUT.lean"""
import re, sys
from fractions import Fraction as Fr
from math import gcd
PER = 27720
src = open(sys.argv[1]).read()
m = re.search(r"def R0tLit : Rat := \((\d+) : Rat\) / (\d+)", src)
R0t = Fr(int(m.group(1)), int(m.group(2)))
vals = [Fr(int(a), int(b)) for a, b in re.findall(r"^\s*\((-?\d+) : Rat\) / (\d+)[,\]]", src, re.M)]
assert len(vals) == PER, len(vals)
divs = [g for g in range(1, PER + 1) if PER % g == 0]
tab = {d: vals[d % PER] - gcd(d, PER) * R0t for d in divs}
def mu(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0: return 0
            r = -r
        p += 1
    return -r if n > 1 else r
B = {g: sum((mu(g // d) * tab[d] for d in divs if g % d == 0), Fr(0)) for g in divs}
assert all(b >= 0 for b in B.values()), [g for g, b in B.items() if b < 0]
for c in range(PER):
    assert sum((B[g] for g in divs if c % g == 0), Fr(0)) == vals[c] - gcd(c, PER) * R0t, c
L = ["import RCert.G.U3G", "",
     "/-! U3g/V4g: the divisor-form table `tab = tabB BLit` of the M3 values at period 27720",
     "(`tab(c) = teff(c) - gcd(c, 27720) R0t`; `BLit` by Moebius inversion over the divisors of 27720, written by",
     "u3g/tools/gen_blit_g.py; checked in RCert/G/BCheck.lean). -/",
     "", "namespace R45.U3G", "", "/-- `(g, B_g)` for the 96 divisors `g` of 27720. -/", "def bList : List (Nat × Rat) := ["]
L += [f"  ({g}, ({B[g].numerator} : Rat) / {B[g].denominator})" + ("," if i + 1 < len(divs) else "]") for i, g in enumerate(divs)]
L += ["", "/-- `B_g` (0 off the divisors). -/", "def BLit (g : Nat) : Rat := ((bList.find? fun x => x.1 == g).map (·.2)).getD 0",
      "", "end R45.U3G", ""]
open(sys.argv[2], "w").write("\n".join(L))
print("B_1 =", float(B[1]), " sum B =", float(sum(B.values())), " R0t =", float(R0t), " wrote", sys.argv[2])
