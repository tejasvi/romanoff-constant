"""Convert factordb factorizations of 2^t - 1 (files m{t}.json in DIR, untrusted) into Phi_t(2) factorizations
(JSON {t: [[p, e], ...]}) for t = 1..T0.  Checks: status FF/P/Unit, product == 2^t - 1, primality (BPSW here; the checker
proves primality), and that Phi_t(2) / (primitive part) is 1 or a prime dividing t.  Run with python -I.
Usage: fdb_to_phi.py DIR T0 OUT"""
import json, os, sys
from flint import fmpz, fmpz_poly
d, T0, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
def pdiv(n):
    o, q = [], 2
    while q * q <= n:
        if n % q == 0:
            o.append(q)
            while n % q == 0: n //= q
        q += 1
    if n > 1: o.append(n)
    return o
res, bad = {}, []
for t in range(1, T0 + 1):
    js = json.load(open(os.path.join(d, f"m{t}.json")))
    if js.get("status") not in ("FF", "P", "Unit"):
        bad.append((t, js.get("status"))); continue
    fl = [(int(p), int(e)) for p, e in js["factors"]]
    prod = 1
    for p, e in fl: prod *= p ** e
    if prod != 2 ** t - 1: bad.append((t, "product")); continue
    if not all(fmpz(p).is_probable_prime() for p, e in fl): bad.append((t, "notprime")); continue
    phi = int(fmpz(fmpz_poly.cyclotomic(t)(2)))
    prim = []
    for p, e in fl:
        o = t
        for q in pdiv(t):
            while o % q == 0 and pow(2, o // q, p) == 1: o //= q
        if o == t: prim.append([p, e])
    rem = phi
    for p, e in prim:
        assert rem % p ** e == 0; rem //= p ** e
    if rem != 1:
        assert t % rem == 0 and fmpz(rem).is_prime(), (t, rem)
        prim.append([rem, 1])
    res[str(t)] = sorted(prim)
json.dump(res, open(out, "w"))
print(f"converted {len(res)} of {T0}; problems: {bad[:20]}{' ...' if len(bad) > 20 else ''} ({len(bad)} total)")
