#!/usr/bin/env python3
"""kbuild45.py JOBS_FILE MEMCAP_GB MAXJOBS [MEM_PER_S]: run from the project root (or KB_ROOT).
Memory-aware scheduler for the kernel shards Romanoff/M3/K/<name>.lean. JOBS_FILE lines: `name est_kernel_s`.
Each job: lake env lean -o .lake/build/lib/lean/Romanoff/M3/K/<name>.olean (decide +kernel inside).
Memory estimate per job 2 GB + MEM_PER_S (default 0.2) GB per estimated kernel second; the sum stays <= MEMCAP; a watchdog
kills the youngest job when MemAvailable < 12 GB and requeues it with twice the estimate.
Results appended to M3/logs/kbuild45.tsv: name rc elapsed_s maxrss_kb est_s. Jobs with rc 0 in that file are skipped."""
import os, sys, time, subprocess, signal, re

jobs_file, memcap, maxjobs = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
MEMK = float(sys.argv[4]) if len(sys.argv) > 4 else 0.2
os.chdir(os.environ.get('KB_ROOT', os.getcwd()))
os.makedirs('M3/logs/kb', exist_ok=True)
os.makedirs('M3/tmp', exist_ok=True)
outd = '.lake/build/lib/lean/Romanoff/M3/K'
os.makedirs(outd, exist_ok=True)
tsv = 'M3/logs/kbuild45.tsv'
done = set()
if os.path.exists(tsv):
    for l in open(tsv):
        p = l.split()
        if len(p) >= 2 and p[1] == '0':
            done.add(p[0])
queue = []
for l in open(jobs_file):
    p = l.split()
    if p and p[0] not in done:
        queue.append([p[0], float(p[1]), 2.0 + MEMK * float(p[1])])
queue.sort(key=lambda q: -q[1])
env = dict(os.environ, TMPDIR=os.path.abspath('M3/tmp'))
running = {}

def memavail_gb():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable:'):
            return int(l.split()[1]) / 1e6
    return 0.0

def start(job):
    n = job[0]
    log = f'M3/logs/kb/{n}.log'
    cmd = (f'ulimit -s unlimited; exec /usr/bin/time -v lake env lean --tstack=1000000 -DElab.async=false '
           f'-o {outd}/{n}.olean -i {outd}/{n}.ilean Romanoff/M3/K/{n}.lean > {log} 2>&1')
    p = subprocess.Popen(['bash', '-c', cmd], env=env, start_new_session=True)
    running[p.pid] = (job, p, time.time())

def finish(job, p, t0):
    n = job[0]
    log = open(f'M3/logs/kb/{n}.log').read()
    m = re.search(r'Maximum resident set size \(kbytes\): (\d+)', log)
    rss = int(m.group(1)) if m else -1
    rc = p.returncode
    if rc == 0 and ('error' in log.lower().split('command being timed')[0]):
        rc = 99
    with open(tsv, 'a') as f:
        f.write(f'{n} {rc} {time.time() - t0:.1f} {rss} {job[1]:.0f}\n')

t_start = time.time()
while queue or running:
    for pid, (job, p, t0) in list(running.items()):
        if p.poll() is not None:
            finish(job, p, t0)
            del running[pid]
    if memavail_gb() < 12 and running:
        pid = max(running, key=lambda q: running[q][2])
        job, p, t0 = running.pop(pid)
        os.killpg(pid, signal.SIGKILL)
        p.wait()
        job[2] *= 2
        queue.append(job)
        with open(tsv + '.kills', 'a') as f:
            f.write(f'{job[0]} killed at {time.time() - t_start:.0f}s new_est_gb {job[2]:.1f}\n')
    used = sum(r[0][2] for r in running.values())
    while queue and len(running) < maxjobs:
        k = next((idx for idx, q in enumerate(queue) if used + q[2] <= memcap), None)
        if k is None:
            if not running:
                k = 0
            else:
                break
        job = queue.pop(k)
        start(job)
        used += job[2]
    time.sleep(2)
print(f'all done in {time.time() - t_start:.0f}s', flush=True)
