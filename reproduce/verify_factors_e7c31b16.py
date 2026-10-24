"""Verify factorizations of Phi_t(2): product check, primality proofs (flint fmpz.is_prime), exact orders.
Output: JSON list of [p, t] for every prime p with ord_p(2) = t (t <= T0), excluding p = 2."""
import json, sys
from flint import fmpz, fmpz_poly
data = json.load(open(sys.argv[1])); out = sys.argv[2]
def prime_divisors(n):
    ps, d = [], 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: ps.append(n)
    return ps
plist = []
T0 = max(int(t) for t in data)
assert sorted(int(t) for t in data) == list(range(1, T0 + 1))
for ts, fl in data.items():
    t = int(ts)
    v = fmpz(fmpz_poly.cyclotomic(t)(2))
    prod = fmpz(1)
    for p, e in fl:
        prod *= fmpz(p) ** e
        assert fmpz(p).is_prime(), (t, p)
    assert prod == v, t
    for p, e in fl:
        # order of 2 mod p
        assert pow(2, t, p) == 1
        o = t
        for q in prime_divisors(t):
            while o % q == 0 and pow(2, o // q, p) == 1: o //= q
        if o == t:
            plist.append([p, t])
        else:
            assert t % p == 0, (t, p, o)   # intrinsic factor: p | t, order smaller (counted at its own t)
# every prime with order t <= T0 divides Phi_t(2), so the list is complete for orders <= T0
ps = [p for p, t in plist]
assert len(ps) == len(set(ps))
json.dump(sorted(plist), open(out, "w"))
print(f"verified T0={T0}: {len(plist)} primes with order <= T0")
