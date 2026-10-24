"""K plan for M3 v2: DP checkpoint schedule (by cumulative table size), class-B chunks, values.
usage: gen_kplan.py PRATT.json OUT.json [WORK_PER_SHARD]"""
import json, sys, os, math
sys.set_int_max_str_digits(0)
os.environ.setdefault("KAPPA", "16384")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import m3ref
from m3ref import groups, step, eLo, eUp, ELL, SC
d = json.load(open(sys.argv[1])); WPS = float(sys.argv[3]) if len(sys.argv) > 3 else 250000
A = [(p, t) for p, t in d["A"] if p not in ELL]
gA = groups(A)
tab = {1: (SC, SC)}; sizes = []
for t, ps in gA:
    sizes.append(len(tab))      # work of this step ~ size of the input table
    tab = step(tab, t, eLo(ps), eUp(ps))
sched = [0]; acc = 0
for k, w in enumerate(sizes):
    acc += w
    if acc >= WPS:
        sched.append(k + 1); acc = 0
if sched[-1] != len(gA): sched.append(len(gA))
print("steps", len(gA), "final", len(tab), "total work", sum(sizes), "shards", len(sched) - 1)
print("schedule", sched)
json.dump(dict(sched=sched, sizes=sizes), open(sys.argv[2], "w"))
