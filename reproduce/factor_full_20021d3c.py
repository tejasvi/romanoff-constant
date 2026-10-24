"""Full factorizations of Phi_t(2), t = 1..T0, with python-flint. Output JSON {t: [[p, e], ...]} (all prime factors).
Usage: factor_full.py T0 OUT [workers]"""
import json, sys, time
from multiprocessing import Pool
from flint import fmpz, fmpz_poly

def fac(t):
    s = time.time()
    v = fmpz(fmpz_poly.cyclotomic(t)(2))
    f = [[int(p), int(e)] for p, e in v.factor()]
    return t, f, time.time() - s

if __name__ == "__main__":
    T0, out = int(sys.argv[1]), sys.argv[2]
    w = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    res = {}
    with Pool(w) as pool:
        for t, f, el in pool.imap_unordered(fac, range(1, T0 + 1)):
            res[t] = f
            if el > 10: print(f"t={t}: {el:.0f}s", flush=True)
    json.dump({str(t): res[t] for t in sorted(res)}, open(out, "w"))
    print("done", len(res))
