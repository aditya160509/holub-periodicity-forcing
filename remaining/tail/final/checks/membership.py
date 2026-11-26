import json, sys, random
from fractions import Fraction as Fr
D=json.load(open(sys.argv[1])); i,k,l=D['tuple']; Ymax=Fr(D['Ymax'])
from engine import System
S=System(i,k,l); c=i+l-2; umax=Fr(S.kap,c)
certs=[[(tuple(f),s) for f,s in C['cons']] for C in D['certs']]
def inK(cons,u,y):
    for f,s in cons:
        v=f[0]+f[1]*u+f[2]*y
        if v<0 or (s and v==0): return False
    return True
random.seed(3); miss=0; N=int(sys.argv[2])
pts=[]
for _ in range(N):
    q=random.choice([1,2,3,5,7,9,11,12,13,30,97,1000])
    u=Fr(random.randint(1,10**6),10**6)*umax; y=Fr(random.randint(1,10**6),10**6)*Ymax
    if random.random()<0.5: u=Fr(round(u*q),q); y=Fr(round(y*q),q)
    if not (0<u<umax and 0<y<Ymax): continue
    pts.append((u,y))
for extra in sys.argv[3:]:
    a,b,cc=map(int,extra.split(',')); pts.append((Fr(b,a),Fr(cc,a)))
for u,y in pts:
    if not any(inK(K,u,y) for K in certs): miss+=1; print('MISS',u,y)
print('tested',len(pts),'missed',miss)
