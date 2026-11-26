# Soundness test: claimed global period gcd(Bg) must hold in the exact generic solution
# (union-find over positions, code independent of engine.py, adapted from ../../me/genall.py).
import sys, random
from math import gcd
from fractions import Fraction as Fr
from engine import *
def uf_classes(i,k,l,d,u,y,drop=()):
    S=i+k+l; D=S*d//3; x=u+d; h=(i+l)*d-D; a=D-i*d; gl=l*d-D
    par=list(range(x))
    def f(p):
        while par[p]!=p: par[p]=par[par[p]]; p=par[p]
        return p
    def un(p,q): par[f(p)]=f(q)
    W=lambda lo,n:[(lo+t)%x for t in range(n)]
    U=W(0,u) if i>0 else W(x-u,u)
    C=W(i*u,i*d); H=W(0,h); A=W(h,a)
    E=[(W(0,i*x),U*i+C)]
    E.append((W(0,l*x),H+A+U*l))
    T=A+C; Y=[T[t%len(T)] for t in range(y)]; G=(Y+H)[:gl]
    E.append((Y+H,G+C+Y)); E.append((Y+W(0,k*x)+G,A+C+Y+A+U*k))
    for n,(P_,Q_) in enumerate(E):
        if n in drop: continue
        for p,q in zip(P_,Q_): un(p,q)
    return [f(p) for p in range(x)], x
def has_period(cl,x,g): return all(cl[t]==cl[(t+g)%x] for t in range(x))
def holds(cons,pt):
    for f,s in cons:
        v=sum(a*b for a,b in zip(f,pt))
        if v<0 or (s and v==0): return False
    return True
i,k,l=map(int,sys.argv[1:4]); N=int(sys.argv[4]); DROP=tuple(map(int,sys.argv[5:]))
Sy=System(i,k,l); Sy.drop=DROP; kap=Sy.kap; c=i+l-2
random.seed(7); STAT=[0,0]; bad=0; tested=0; cone_tests=0
for _ in range(N):
    w=random.randint(2,9); d=kap*w
    umax=d//c if c>0 else d
    u=random.randint(1,max(1,umax-1)); 
    if c>0 and c*u>=d: continue
    y=random.randint(1,(i+l+k)*d)
    pr=Prover(Sy,(w,u,y)); r,Bg,dep=pr.run()
    cl,x=uf_classes(i,k,l,d,u,y,DROP)
    g=0
    for f in Bg: g=gcd(g,sum(a*b for a,b in zip(f,(w,u,y))))
    tested+=1
    STAT[0]+= r is not None; STAT[1]+= not has_period(cl,x,gcd(x,u))
    if not has_period(cl,x,g): bad+=1; print('UNSOUND at point',(w,u,y),Bg,g)
    if r:
        # cone propagation: test other integer points satisfying the certificate
        for _ in range(40):
            w2=random.randint(1,12); d2=kap*w2; u2=random.randint(1,d2); y2=random.randint(1,(i+l+k)*d2)
            q=(w2,u2,y2)
            if c>0 and c*u2>=d2: continue
            if not holds(dep,q): continue
            cl2,x2=uf_classes(i,k,l,d2,u2,y2,DROP)
            g2=0
            for f in Bg: g2=gcd(g2,sum(a*b for a,b in zip(f,q)))
            cone_tests+=1
            if not has_period(cl2,x2,g2): bad+=1; print('UNSOUND cone',(w,u,y),'->',q,Bg)
nf=sum(1 for _ in [0]);print('engine-closed',STAT[0],'uf-nonforcing',STAT[1]);print((i,k,l),'drop',DROP,'points',tested,'cone tests',cone_tests,'unsound',bad)
