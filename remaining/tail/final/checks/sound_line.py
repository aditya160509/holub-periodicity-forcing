# soundness of the zeros (line) mode: integer points on a line, claimed period vs union-find
import random, sys
from math import gcd
from engine import *
from points import classes
def has_period(cl,x,g): return all(cl[t]==cl[(t+g)%x] for t in range(x))
def holds(cons,pt):
    for f,s in cons:
        v=sum(a*b for a,b in zip(f,pt))
        if v<0 or (s and v==0): return False
    return True
random.seed(5); bad=0; n=0; cl_=0
lines={(0,2,5):[(1,3,-1),(2,1,-1),(1,-2,0)],(0,1,3):[(1,-1,-2),(1,1,-1)],(0,1,4):[(4,1,-6),(1,0,-1)],(1,1,4):[(1,0,-1),(2,1,-2)]}
for tup,zs in lines.items():
    S=System(*tup); c=tup[0]+tup[2]-2
    for z in zs:
        for _ in range(60):
            # integer point on z=0: z0*w+z1*u+z2*y=0
            w=random.randint(1,12); u=random.randint(1,max(1,S.kap*w//c))
            if c*u>=S.kap*w: continue
            if z[2]==0: continue
            num=-(z[0]*w+z[1]*u)
            if num % z[2]: continue
            y=num//z[2]
            if y<=0: continue
            pr=Prover(S,(w,u,y),zeros=[z]); r,Bg,dep=pr.run(); n+=1
            g=0
            for f in Bg: g=gcd(g,sum(a*b for a,b in zip(f,(w,u,y))))
            cl,x=classes(*tup,S.kap*w,u,y)
            if not has_period(cl,x,g): bad+=1; print('UNSOUND',tup,(w,u,y),Bg)
            if r:
                cl_+=1
                for t in range(2,5):
                    for w2 in range(1,15):
                        for u2 in range(1,S.kap*w2):
                            if c*u2>=S.kap*w2: continue
                            num=-(z[0]*w2+z[1]*u2)
                            if num%z[2]: continue
                            y2=num//z[2]
                            if y2<=0 or not holds(dep,(w2,u2,y2)): continue
                            cl2,x2=classes(*tup,S.kap*w2,u2,y2)
                            g2=0
                            for f in Bg: g2=gcd(g2,sum(a*b for a,b in zip(f,(w2,u2,y2))))
                            ok = has_period(cl2,x2,g2)
                            if not ok: bad+=1; print('UNSOUND cone',tup,(w,u,y),'->',(w2,u2,y2))
                    break
print('line points',n,'closed',cl_,'unsound',bad)
