"""Exact residue patterns and rotation orbits for squarefree ell = prod(ELL), vectorized.
Returns PER, list of orbit reps (python ints, canonical = least rotation), integer class counts, sizes, n_U(c) matrix."""
import math
import numpy as np

def order2(p):
    o, x = 1, 2 % p
    while x != 1:
        x = x * 2 % p; o += 1
    return o

def patterns(ELL):
    PER = 1
    for p in ELL: PER = PER * order2(p) // math.gcd(PER, order2(p))
    FULL = (1 << PER) - 1
    pat = {0: 1}
    for p in ELL:
        o = order2(p); pw = {pow(2, r, p): r for r in range(o)}; opts = {}
        for k in range(p):
            m = 0
            if k in pw:
                for r in range(pw[k], PER, o): m |= 1 << r
            opts[m] = opts.get(m, 0) + 1
        new = {}
        for ex, cnt in pat.items():
            for m, c in opts.items():
                key = ex | m
                new[key] = new.get(key, 0) + cnt * c
        pat = new
    out = {}
    for ex, cnt in pat.items():
        m = FULL & ~ex
        if m: out[m] = out.get(m, 0) + cnt
    return PER, out

def orbits(PER, pat, chunk=200000):
    """least-rotation canonical form (as integer) via two/more uint64 words; returns dict rep(int) -> count(int)"""
    masks = list(pat.keys()); cnts = list(pat.values())
    W = (PER + 63) // 64
    reps = {}
    for i in range(0, len(masks), chunk):
        mm = masks[i:i + chunk]
        B = np.array([[(m >> r) & 1 for r in range(PER)] for m in mm], dtype=np.uint8)
        best = None
        for s in range(PER):
            R = np.roll(B, s, axis=1)
            Rp = np.zeros((R.shape[0], 64 * W), dtype=np.uint8); Rp[:, :PER] = R
            words = np.packbits(Rp, axis=1, bitorder="little").view("<u8")    # [n, W], word w = bits 64w..64w+63
            if best is None:
                best = words.copy(); bestR = R.copy(); continue
            less = np.zeros(len(mm), dtype=bool); eq = np.ones(len(mm), dtype=bool)
            for w in range(W - 1, -1, -1):          # most significant word first
                less |= eq & (words[:, w] < best[:, w]); eq &= words[:, w] == best[:, w]
            best[less] = words[less]; bestR[less] = R[less]
        for row, c in zip(bestR, cnts[i:i + chunk]):
            m = int("".join("1" if b else "0" for b in row[::-1]), 2)
            reps[m] = reps.get(m, 0) + c
    return reps

def orbit_arrays(PER, reps):
    keys = sorted(reps)
    cnt = np.array([reps[k] for k in keys], dtype=object)
    bits = np.array([[(k >> r) & 1 for r in range(PER)] for k in keys], dtype=np.float64)
    size = bits.sum(1).astype(np.int64)
    F = np.fft.rfft(bits, axis=1)
    nU = np.rint(np.fft.irfft(np.abs(F) ** 2, n=PER, axis=1)).astype(np.int64)
    assert (nU.sum(1) == size ** 2).all()
    return keys, cnt, size, nU
