import random, sys
from fractions import Fraction as F
from sysik import SysIK
import engine_n as E
random.seed(4)
for (i,k,l0) in [(0,1,7),(1,1,7),(0,2,7),(2,1,7),(1,2,7),(3,1,7),(0,3,7),(2,2,7),(4,1,9),(1,3,8)]:
    S=SysIK(i,k,l0); ok=0; N=60
    for _ in range(N):
        L=random.choice([l0,l0+1,l0+4,30,300,10**4])
        D=F(i+k+L,3)*F(random.randint(950,1050),1000); D=max(D,F(i+k+l0,3))
        u=F(random.randint(1,999),1000)/(i+l0-2); y=F(random.randint(1,999),1000)*(D-i)
        r=E.Prover(S,(1,u,y,D),uniform=True).run(budget=10)[0]; ok+= r is not None
    print((i,k,'l>=%d'%l0),'closed',ok,'/',N,flush=True)
