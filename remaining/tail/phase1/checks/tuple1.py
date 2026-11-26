# Per-tuple 2D pipeline for one (i,k,l), same steps as driver.py's residual loop.
import sys, os, subprocess
from fractions import Fraction as F
from math import gcd
i, k, l = map(int, sys.argv[1:4]); fin = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'final', 'checks')
S = i + k + l; m = i + l - 2 * k; c = i + l - 2; kap = 3 if S % 3 else 1
g0 = gcd(S, 3 * (i + l) - S); h = F(i + l) - F(S, 3); gam = F(g0, 3)
if not (m != 0 and abs(m) <= c and m % g0 == 0 and h >= 1 + F(1, c) + gam):
    print((i, k, l), 'per-tuple pipeline not applicable'); sys.exit()
Y0 = F(S, 3) + h - gam - i - min(F(S, 3), k, h); t = '%d_%d_%d' % (i, k, l)
sh = lambda c: subprocess.run(c, shell=True, cwd=fin, capture_output=True, text=True).stdout.strip().splitlines()
sh('python3 cover.py %d %d %d %s cov_%s.json > log_%s.txt 2>&1' % (i, k, l, Y0 * kap, t, t))
sh('python3 points.py cov_%s.json > pts_%s.txt 2>&1' % (t, t))
out = sh('python3 check_certs.py cov_%s.json' % t)
pts = open(os.path.join(fin, 'pts_%s.txt' % t)).read().strip().splitlines()
print((i, k, l), pts[-1] if pts else '', '|', out[-1] if out else 'NO OUTPUT', flush=True)
