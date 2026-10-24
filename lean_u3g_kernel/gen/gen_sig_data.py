# k45g: the W-table signatures of the fibered component F = (19, 73, 37) in the conventions of the evaluator
# RCert/G/Ev.lean: options are optsP 360 p = [(maskP 360 p r, 1) for r in range(p) with a nonzero mask]
# ++ [(0, #residues with the zero mask)], enumerated o19 (outer), o73, o37 (inner) as in evalKey.
# For a = x mod 12 and w = (x mod 9) div 3, the exclusion of x < 360 depends on (a, w) only (asserted here).
# Output: JSON with the per-triple signature index, the signature weights, f_w(a) and W_w^1(a, b) (z(a) = z(b)).
import json, sys, hashlib

def maskP(per, p, r):
    return frozenset(e for e in range(per) if pow(2, e, p) == r)

def optsP(per, p):
    out, zero = [], 0
    for r in range(p):
        m = maskP(per, p, r)
        if m: out.append((m, 1))
        else: zero += 1
    out.append((frozenset(), zero))
    return out

F = [19, 73, 37]
O = {p: optsP(360, p) for p in F}
assert [len(O[p]) for p in F] == [19, 10, 37]
assert [sum(c for _, c in O[p]) for p in F] == F

# x < 360 grouped by (a, w)
cells = {}
for x in range(360):
    cells.setdefault((x % 12, (x % 9) // 3), []).append(x)
assert len(cells) == 36 and all(len(v) == 10 for v in cells.values())

ZPAIRS = [(a, b) for a in range(12) for b in range(12) if (a - b) % 3 == 0]      # 48 pairs, a-major
assert len(ZPAIRS) == 48

sig_index, sigs, wts, triples = {}, [], [], []
for i19, (m19, c19) in enumerate(O[19]):
    for i73, (m73, c73) in enumerate(O[73]):
        for i37, (m37, c37) in enumerate(O[37]):
            E = m19 | m73 | m37
            ex = {}
            for (a, w), xs in cells.items():
                st = {x in E for x in xs}
                assert len(st) == 1, ("exclusion must depend on (a, w) only", i19, i73, i37, a, w)
                ex[(a, w)] = st.pop()
            fw = tuple(sum(1 for w in range(3) if not ex[(a, w)]) for a in range(12))
            w1 = tuple(sum(1 for w in range(3) if not ex[(a, w)] and not ex[(b, w)]) for (a, b) in ZPAIRS)
            key = (fw, w1)
            if key not in sig_index:
                sig_index[key] = len(sigs); sigs.append(key); wts.append(0)
            s = sig_index[key]
            wts[s] += c19 * c73 * c37
            triples.append(s)
assert len(triples) == 19 * 10 * 37 and sum(wts) == 19 * 73 * 37
out = {"note": "k45g signatures of (19, 73, 37); order of first appearance in the o19 x o73 x o37 enumeration",
       "nsig": len(sigs), "sigF": triples, "wtF": wts, "fw": [list(s[0]) for s in sigs], "w1": [list(s[1]) for s in sigs],
       "zpairs": ZPAIRS}
txt = json.dumps(out, separators=(",", ":"))
open(sys.argv[1], "w").write(txt)
print("signatures", len(sigs), "triples", len(triples), "weight", sum(wts), "sha256", hashlib.sha256(txt.encode()).hexdigest()[:16])
