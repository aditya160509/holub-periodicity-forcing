"""Recompute the original and new open counts from exponent inequalities."""
from itertools import product
from pathlib import Path

def old_covered(i,k,l):
    s=i+k+l
    return (not k or not(i+l) or i==k==l or (not l and k==2*i)
            or (s%3==0 and (i==s//3 or i<=2*s//3<=i+k))
            or (not i and k==l) or (not l and i==k) or i==2*k==2*l)

def new_covered(i,k,l):
    return (i>0 and k>0 and l==0 and k!=2*i) or (i==0 and l>0 and k>2*l) or (i*k*l>0 and k>=2 and i+k>2*l and i<2*k+2*l)

for cap in (4,6):
    old=[t for t in product(range(cap+1),repeat=3) if not old_covered(*t)]
    proved=[t for t in old if new_covered(*t)]
    remaining=[t for t in old if not new_covered(*t)]
    print(cap, 'original', len(old), 'new',len(proved),'remaining',len(remaining))
    for prefix,items in [('proved',proved),('remaining',remaining)]:
        assert (Path(__file__).resolve().parent.parent/f'{prefix}_exp{cap}.txt').read_text()==''.join(','.join(map(str,t))+'\n' for t in items)
    assert len(old)=={4:63,6:210}[cap]
    assert len(remaining)=={4:36,6:120}[cap]
