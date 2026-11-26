import random, sys
from math import gcd
sys.path.insert(0,'../../final/checks')
from points import classes
from sys01 import Sys01
import engine_n as E
def per(cl,x,g): return all(cl[t]==cl[(t+g)%x] for t in range(x))
def holds(cons,pt):
    for f,s in cons:
        v=sum(a*b for a,b in zip(f,pt))
        if v<0 or (s and v==0): return False
    return True
random.seed(11); S=Sys01(7); bad=0; n=0; cone=0
pts=[]
for l in range(7,23):
    for d in range(1,40):
        if ((l+1)*d)%3: continue
        D=(l+1)*d//3
        for u in range(1,d):
            if (l-2)*u>=d: break
            for y in range(1,D): pts.append((l,d,u,y,D))
random.shuffle(pts)
for (l,d,u,y,D) in pts[:150]:
    r,Bg,dep=E.Prover(S,(d,u,y,D),uniform=True).run(); n+=1
    g=0
    for f in Bg: g=gcd(g,sum(a*b for a,b in zip(f,(d,u,y,D))))
    cl,x=classes(0,1,l,d,u,y)
    if not per(cl,x,g): bad+=1; print('UNSOUND',(l,d,u,y,D))
    if r:
        for q in random.sample(pts,800):
            if holds(dep,q[1:]):
                l2,d2,u2,y2,D2=q; cl2,x2=classes(0,1,l2,d2,u2,y2)
                g2=0
                for f in Bg: g2=gcd(g2,sum(a*b for a,b in zip(f,q[1:])))
                cone+=1
                if not per(cl2,x2,g2): bad+=1; print('UNSOUND cone',q)
print('points',n,'cone tests',cone,'unsound',bad)
