import random, sys
from fractions import Fraction as F
from sys01 import Sys01
import engine_n as E
l0=int(sys.argv[1]); N=int(sys.argv[2]); random.seed(4)
S=Sys01(l0); ok=0; bad=[]
for _ in range(N):
    L=random.choice([l0,l0+1,l0+3,10,20,100,1000,10**5])
    D=F(L+1,3)*F(random.randint(900,1100),1000)   # near admissible, also off it
    if 3*D<(l0+1): D=F(l0+1,3)
    u=F(random.randint(1,999),1000)/(l0-2); y=F(random.randint(1,999),1000)*D
    r=E.Prover(S,(1,u,y,D),uniform=True).run(budget=10)[0]
    if r: ok+=1
    else: bad.append((float(u),float(y/D),float(D)))
print('l0',l0,'closed',ok,'/',N); print(bad[:10])
