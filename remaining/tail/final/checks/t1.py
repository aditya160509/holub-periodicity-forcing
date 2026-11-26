import sys, random, time
from fractions import Fraction as Fr
from engine import *
i,k,l=map(int,sys.argv[1:4]); n=int(sys.argv[4])
S=System(i,k,l); c=i+l-2
random.seed(1); ok=0; t0=time.time()
for _ in range(n):
    umax=Fr(S.kap*1,c) if c>0 else Fr(S.kap)
    u=Fr(random.randint(1,999),1000)*umax
    y=Fr(random.randint(1,9999),1000)
    pr=Prover(S,(1,u,y))
    r,Bg,dep=pr.run()
    ok+= r is not None
    print(float(u),float(y),r,len(dep) if r else '-',flush=True)
print('ok',ok,'/',n,time.time()-t0)
