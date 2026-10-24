"""M3 data: certified prime lists (exact orders) + flat Pratt certificates.

usage: gen_pratt.py FAC300.json FAC1200.json OUT.json [NPROC]
Classes: A = primitive primes of Phi_t(2), t <= 300 (exact order t); B = primes q < 10^100 of exact order t, 300 < t <= 1200,
gcd(q, t) = 1, from the factor lists of Phi_t(2).  Every prime p >= SMALL gets a Pratt certificate: p - 1 = prod q^e
(all q found by flint's factor_smooth; each q >= SMALL certified recursively), a witness a with a^(p-1) = 1 and
a^((p-1)/q) != 1 mod p.  Primes whose p - 1 cannot be factored within the effort bound are DROPPED (they fall into the
rest class); the drop list and its mass are reported.  Primes < SMALL are certified by trial division in the checker.
"""
import json, sys, math, time
from multiprocessing import Pool
from flint import fmpz
SMALL = 1 << 16
BITS = [int(b) for b in __import__("os").environ.get("PBITS", "40,60").split(",")]          # factor_smooth effort levels

def pdiv(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return out

def factor_pm1(n):
    """Full factorization of n - 1 into probable primes, or None."""
    m = fmpz(n - 1)
    for b in BITS:
        fl = m.factor_smooth(bits=b)
        if all(fmpz(q).is_probable_prime() for q, e in fl):
            out = {}
            for q, e in fl: out[int(q)] = out.get(int(q), 0) + int(e)
            prod = 1
            for q, e in out.items(): prod *= q ** e
            assert prod == n - 1
            return sorted(out.items())
    return None

def cert_tree(n, memo):
    """Returns dict {p: (a, [(q, e)])} for n and all big primes below it, or None."""
    if n < SMALL: return {}
    if n in memo: return memo[n]
    fl = factor_pm1(n)
    if fl is None:
        memo[n] = None; return None
    out = {}
    for q, e in fl:
        if q >= SMALL:
            sub = cert_tree(q, memo)
            if sub is None:
                memo[n] = None; return None
            out.update(sub)
    for a in range(2, 10000):
        if pow(a, n - 1, n) == 1 and all(pow(a, (n - 1) // q, n) != 1 for q, e in fl):
            break
    else:
        raise RuntimeError(f"no witness for {n} (composite?)")
    out[n] = (a, fl)
    memo[n] = out
    return out

def work(p):
    t0 = time.time()
    try:
        r = cert_tree(p, {})
    except Exception as ex:
        return p, None, repr(ex), time.time() - t0
    return p, r, None, time.time() - t0

if __name__ == "__main__":
    fac = json.load(open(sys.argv[1])); facb = json.load(open(sys.argv[2])); outp = sys.argv[3]
    nproc = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    A = []   # (p, t)
    for ts, fl in fac.items():
        t = int(ts)
        for p, e in fl:
            p = int(p); o = t
            for q in pdiv(t):
                while o % q == 0 and pow(2, o // q, p) == 1: o //= q
            if o == t: A.append((p, t))
    B = []
    for t in range(301, 1201):
        for q, e in facb[str(t)]:
            q = int(q)
            if math.gcd(q, t) != 1 or q >= 10 ** 100: continue
            if pow(2, t, q) == 1 and all(pow(2, t // r, q) != 1 for r in pdiv(t)):
                B.append((q, t))
    print(f"A: {len(A)} primes, B: {len(B)} primes", flush=True)
    allp = sorted({p for p, t in A + B if p >= SMALL})
    t0 = time.time(); recs = {}; failed = []; slow = []
    with Pool(nproc) as pool:
        for p, r, err, dt in pool.imap_unordered(work, allp, chunksize=1):
            if dt > 30: slow.append((p, round(dt, 1)))
            if r is None: failed.append((p, err))
            else: recs.update(r)
    print(f"certified {len(allp) - len(failed)}/{len(allp)} big primes, {len(recs)} records ({time.time()-t0:.0f}s)", flush=True)
    bad = {p for p, e in failed}
    for nm, L in (("A", A), ("B", B)):
        dropped = [(p, t) for p, t in L if p in bad]
        print(f"{nm}: dropped {len(dropped)}, min dropped p = {min((p for p, t in dropped), default=None)}, "
              f"mass sum 1/(p-2) = {sum(1/(p-2) for p, t in dropped):.3e}", flush=True)
    json.dump(dict(SMALL=SMALL,
                   A=[[p, t] for p, t in sorted(A, key=lambda x: (x[1], x[0])) if p not in bad],
                   B=[[p, t] for p, t in sorted(B, key=lambda x: (x[1], x[0])) if p not in bad],
                   recs=[[n, a, [[q, e] for q, e in fl]] for n, (a, fl) in sorted(recs.items())],
                   dropped=[[p, err] for p, err in sorted(failed)], slow=sorted(slow)),
              open(outp, "w"))
    print("written", outp)
