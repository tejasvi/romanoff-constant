#!/bin/bash
# Kernel-only build of the 45a proof, from scratch (Mathlib prebuilt). Usage: bash tools/build_k.sh [K45_JOBS] [MEMCAP_GB]
# (works in the repository root, the parent of tools/; logs in logs/k_*.log). Steps:
#  1. lake build of the modules that are not kernel shards (the analytic layers up to Romanoff.Reduction, Romanoff.CertK,
#     the M3 checker functions) and of the M3 literal modules;
#  2. the K45 fold and value shards by lake, at most K45_JOBS in parallel (LEAN_NUM_THREADS; default 80% of RAM at
#     10 GB per job: the shards need about 6 GB each, a few more);
#  3. the 244 M3 kernel shards by M3/tools/kbuild45.py (memory-aware: 2 GB + 0.2 GB per estimated kernel second per job,
#     total <= MEMCAP_GB, default 80% of RAM); all must have rc 0 in M3/logs/kbuild45.tsv;
#  4. lake env lean -o for Romanoff/M3/KMain.lean and Romanoff/CertKFinal.lean (their imports are compiled outside lake);
#  5. lake env lean Axioms45K.lean > results/axioms_shipped.txt.
set -u
cd "$(dirname "$0")/.." || exit 1
mkdir -p logs results
MEM_GB=$(awk '/MemTotal/ {printf "%d", $2 / 1e6}' /proc/meminfo)
CPUS=$(getconf _NPROCESSORS_ONLN)
JOBS=${1:-$(( MEM_GB * 8 / 10 / 10 ))}
[ "$JOBS" -lt 1 ] && JOBS=1
[ "$JOBS" -gt "$CPUS" ] && JOBS=$CPUS
MEMCAP=${2:-$(( MEM_GB * 8 / 10 ))}
echo "build_k: $CPUS CPUs, $MEM_GB GB; K45 jobs $JOBS, M3 shard memory cap $MEMCAP GB; $(date -u)"
LITS=$(ls Romanoff/M3/K | grep -E '^(Tab|Sub|Vals|BDs)' | sed 's/\.lean$//; s/^/Romanoff.M3.K./')
LEAN_NUM_THREADS=$JOBS lake build Romanoff.Reduction Romanoff.CertK RCert.M3.Data RCert.M3.KFun Romanoff.M3.KGlue \
  RCert.M3.TeffLit $LITS > logs/k_deps.log 2>&1
rc=$?; echo "1. dependencies and literal modules: rc=$rc $(date -u)"; [ $rc = 0 ] || exit 1
LEAN_NUM_THREADS=$JOBS lake build K45.Fold K45.Lag.All > logs/k_k45.log 2>&1
rc=$?; echo "2. K45 fold and value shards: rc=$rc $(date -u)"; [ $rc = 0 ] || exit 1
python3 M3/tools/kbuild45.py Romanoff/M3/K/jobs.txt "$MEMCAP" "$CPUS" > logs/k_m3.log 2>&1
rc=$?
bad=0
while read -r n est; do
  [ -n "$n" ] || continue
  r=$(awk -v n="$n" '$1 == n { x = $2 } END { print x }' M3/logs/kbuild45.tsv 2>/dev/null)
  [ -s ".lake/build/lib/lean/Romanoff/M3/K/$n.olean" ] && [ "$r" = 0 ] || { echo "   M3 shard $n: rc=$r"; bad=1; }
done < Romanoff/M3/K/jobs.txt
echo "3. M3 kernel shards: kbuild45 rc=$rc, failed shards: $bad $(date -u)"; [ $rc = 0 ] && [ $bad = 0 ] || exit 1
ulimit -s unlimited
O=.lake/build/lib/lean/Romanoff
mkdir -p $O/M3
for m in M3/KMain CertKFinal; do
  lake env lean -o $O/$m.olean -i $O/$m.ilean Romanoff/$m.lean > logs/k_final_${m##*/}.log 2>&1
  rc=$?; echo "4. Romanoff/$m.lean: rc=$rc $(date -u)"; [ $rc = 0 ] || exit 1
done
lake env lean Axioms45K.lean > results/axioms_shipped.txt 2> logs/k_axioms.err
rc=$?; echo "5. Axioms45K.lean: rc=$rc ($(wc -l < results/axioms_shipped.txt) lines) $(date -u)"
grep -A3 'depends on axioms' results/axioms_shipped.txt
[ $rc = 0 ] || exit 1
