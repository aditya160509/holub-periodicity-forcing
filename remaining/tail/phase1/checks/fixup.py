# For families whose covering left failures: raise l0 past every failure piece (which must stay away
# from d = 0), and list the tuples l0_old <= l < l0_new for the per-tuple pipeline.
import json, sys, math
from fractions import Fraction as F
import check3f as C
out = []
for fn in sys.argv[1:]:
    D = json.load(open(fn)); i, k = D['family'] if isinstance(D['family'], list) else (0, 1); l0 = D['l0']
    if not D['failures']: continue
    dmax = F(3, i + k + l0)
    box = [((1,0,0,0),False),((-1,0,0,dmax),False),((0,1,0,0),False),((0,-1,0,dmax/(i+l0-2)),False),((0,0,1,0),False),((0,0,-1,1),False)]
    dmin = min(min(v[0] for v in C.Cell([(tuple(F(a) for a in f), s) for f, s in q], box).V) for p, q, dd in D['failures'])
    if dmin == 0: print(fn, 'FAILURE TOUCHES d=0'); continue
    lmax = math.floor(F(3) / dmin) - i - k          # largest l whose slice can meet a failure piece
    out.append((i, k, l0, lmax + 1))
    print(fn, 'raise l0 from', l0, 'to', lmax + 1, '; per-tuple l =', list(range(l0, lmax + 1)))
json.dump(out, open('fixup.json', 'w'))
