"""Generic-solution test for Holub's periodicity-forcing problem.
For fixed lengths, union-find on symbolic letter positions gives the most general
solution; every solution is a letter-image of it, so a counterexample exists at
these lengths iff the generic solution is one (X!=U or Y!=V, and not all commuting)."""
import sys
from math import gcd

def pattern(i,j,k,l): return 'a'*i+'b'+'a'*j+'b'+'a'*k+'b'+'a'*l

def generic(pat,x,y,u,v):
    # variables: X0..x-1, Y.., U.., V..
    off={'X':0,'Y':x,'U':x+y,'V':x+y+u}; n=x+y+u+v
    par=list(range(n))
    def f(a):
        while par[a]!=a: par[a]=par[par[a]]; a=par[a]
        return a
    L=[];R=[]
    for c in pat:
        L+= [off['X']+t for t in range(x)] if c=='a' else [off['Y']+t for t in range(y)]
        R+= [off['U']+t for t in range(u)] if c=='a' else [off['V']+t for t in range(v)]
    if len(L)!=len(R): return None
    for p,q in zip(L,R): par[f(p)]=f(q)
    w=lambda name,ln:tuple(f(off[name]+t) for t in range(ln))
    return w('X',x),w('Y',y),w('U',u),w('V',v)

def is_counter(X,Y,U,V):
    if X==U and Y==V: return False
    W=[X,Y,U,V]
    return any(a+b!=b+a for a in W for b in W)

def search(t,vmax,cond=True):
    i,j,k,l=t; p=pattern(i,j,k,l); na=i+j+k+l
    for v in range(vmax+1):
        for x in range(v+1):
            for u in range(v+1):
                # na*x+3y = na*u+3v
                num=na*(u-x)+3*v
                if num%3: continue
                y=num//3
                if y<0 or (cond and y>v): continue
                g=generic(p,x,y,u,v)
                if g and is_counter(*g): return (x,y,u,v),g
    return None

if __name__=='__main__':
    t=tuple(map(int,sys.argv[1])); r=search(t,int(sys.argv[2]))
    print(t, r[0] if r else None)
