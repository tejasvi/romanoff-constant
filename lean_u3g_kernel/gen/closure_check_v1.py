# k45g: import closure of a module over layered source roots (later roots override earlier ones only if identical files are
# expected; a module found in two roots with different bytes is reported). Lists the closure, flags modules whose source
# contains native_decide (outside comments is not distinguished: every hit is listed for reading), and counts Mathlib/Lean
# imports separately. Usage: python3 -I closure_check_v1.py ROOT_MODULE SRC_DIR [SRC_DIR ...]
import hashlib, os, re, sys
root, dirs = sys.argv[1], sys.argv[2:]
def path_of(m):
    hits = []
    for d in dirs:
        p = os.path.join(d, *m.split('.')) + '.lean'
        if os.path.exists(p):
            hits.append(p)
    return hits
seen, ext, order, conflicts = set(), set(), [], []
st = [root]
while st:
    m = st.pop()
    if m in seen:
        continue
    seen.add(m)
    hits = path_of(m)
    if not hits:
        ext.add(m.split('.')[0])
        continue
    shas = {hashlib.sha256(open(p, 'rb').read()).hexdigest() for p in hits}
    if len(shas) > 1:
        conflicts.append((m, hits))
    order.append((m, hits[0]))
    src = open(hits[0]).read()
    st.extend(re.findall(r'^import\s+(\S+)', src, re.M))
nat = []
for m, p in order:
    for i, l in enumerate(open(p), 1):
        if 'native_decide' in l or 'ofReduceBool' in l or 'implemented_by' in l or 'extern' in l.split('--')[0] and '@[extern' in l:
            nat.append((m, i, l.strip()[:120]))
print(f'closure of {root}: {len(order)} project modules; external roots: {sorted(ext)}')
print(f'conflicting copies: {len(conflicts)}')
for c in conflicts:
    print('  CONFLICT', c)
print(f'lines mentioning native_decide / ofReduceBool / implemented_by / @[extern: {len(nat)}')
for n in nat:
    print('  ', n)
