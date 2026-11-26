# One family (i,k): cover all l >= l0 (raising l0 past failures), check it, and run the
# per-tuple pipeline on the residual tuples below the final l0.
import sys, json, math, subprocess, os
from fractions import Fraction as F
from math import gcd

i, k = int(sys.argv[1]), int(sys.argv[2])
l0 = max(7, 2 * k - i + 1, 2 * i - k)
here = os.path.dirname(os.path.abspath(__file__)); fin = os.path.join(here, '../../final/checks')
log = open(os.path.join(here, 'driver_%d_%d.log' % (i, k)), 'w')
def say(*a):
    print(*a, file=log, flush=True)

def run(cmd, cwd):
    return subprocess.run(cmd, shell=True, cwd=cwd, capture_output=True, text=True, timeout=3000)

import residual  # prints a table on import; harmless
from residual import proved
fn = 'covIK_%d_%d.json' % (i, k)
start = l0
for attempt in range(4):
    run('python3 coverik.py %d %d %d %s > logIK_%d_%d.txt 2>&1' % (i, k, l0, fn, i, k), here)
    D = json.load(open(os.path.join(here, fn)))
    say('cover l0=%d certs=%d failures=%d' % (l0, len(D['certs']), len(D['failures'])))
    if not D['failures']: break
    r = run('python3 fixup.py %s' % fn, here).stdout
    line = [s for s in r.splitlines() if 'raise l0' in s or 'TOUCHES' in s]
    say(line)
    if not line or 'TOUCHES' in line[0]:
        say('FAILURE TOUCHES d=0: family not closed'); sys.exit()
    l0 = int(line[0].split('to ')[1].split(' ')[0])
r = run('python3 check3f.py %s' % fn, here).stdout.strip().splitlines()
say('check:', r[-1] if r else 'NO OUTPUT')
fam_ok = bool(r) and r[-1].endswith('OK') and not D['failures']
# per-tuple residual tuples in [start, l0)
low_all = [l for l in range(7, l0) if not proved(i, k, l)]
low = [l for l in low_all if l <= 10]
say('family ok' if fam_ok else 'FAMILY NOT OK', 'final l0', l0, 'per-tuple', low, 'pending (not run, l>10):', [l for l in low_all if l > 10])
for l in low:
    S = i + k + l; m = i + l - 2 * k; c = i + l - 2; kap = 3 if S % 3 else 1
    g0 = gcd(S, 3 * (i + l) - S); h = F(i + l) - F(S, 3); gam = F(g0, 3)
    if not (m != 0 and abs(m) <= c and m % g0 == 0 and h >= 1 + F(1, c) + gam):
        say('tuple', (i, k, l), 'per-tuple pipeline not applicable'); continue
    Y0 = F(S, 3) + h - gam - i - min(F(S, 3), k, h)
    t = '%d_%d_%d' % (i, k, l)
    run('python3 cover.py %d %d %d %s cov_%s.json > log_%s.txt 2>&1' % (i, k, l, Y0 * kap, t, t), fin)
    run('python3 points.py cov_%s.json > pts_%s.txt 2>&1' % (t, t), fin)
    out = run('python3 check_certs.py cov_%s.json' % t, fin).stdout.strip().splitlines()
    pts = open(os.path.join(fin, 'pts_%s.txt' % t)).read().strip().splitlines()
    say('tuple', (i, k, l), pts[-1] if pts else '', '|', out[-1] if out else 'NO OUTPUT')
say('DONE')
