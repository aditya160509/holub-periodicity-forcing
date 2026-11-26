"""Independent literal position-graph and concrete phase checks; Python 3 stdlib only.
No finite test is asserted to prove an unbounded theorem.
"""
from itertools import product
from collections import defaultdict
from math import gcd


def covered(i,k,l):
    return ((i>0 and k>0 and l==0 and k!=2*i) or
            (i==0 and l>0 and k>2*l) or
            (i*k*l>0 and ((2*k>i+l and i+k>2*l) or
                           (k>=2 and i+k>2*l and 2*k+2*l>i))))


def expand(i,k,l,X,Y):
    return X*i+Y*2+X*k+Y+X*l


def root(w):
    for n in range(1,len(w)+1):
        if len(w)%n==0 and w[:n]*(len(w)//n)==w:
            return w[:n]
    return w


def commute(words):
    return all(a+b==b+a for a in words for b in words)


def generic(i,k,l,x,y,u,v):
    # Literal expanded index arrays followed by DFS, not the C++ streaming DSU.
    words=[]; off=0
    for n in (x,y,u,v):
        words.append(tuple(range(off,off+n))); off+=n
    left=expand(i,k,l,*words[:2]); right=expand(i,k,l,*words[2:])
    assert len(left)==len(right)
    adj=[[] for _ in range(off)]
    for a,b in zip(left,right):
        adj[a].append(b); adj[b].append(a)
    labels=[-1]*off
    for a in range(off):
        if labels[a]>=0: continue
        labels[a]=a; stack=[a]
        while stack:
            b=stack.pop()
            for c in adj[b]:
                if labels[c]<0:
                    labels[c]=a; stack.append(c)
    return tuple(tuple(labels[a] for a in w) for w in words)


def factor(R,start,n):
    return tuple(R[(start+j)%len(R)] for j in range(n))


def check(i,k,l,words,counts):
    X,Y,U,V=words; x,y,u,v=map(len,words)
    assert expand(i,k,l,X,Y)==expand(i,k,l,U,V)
    periodic=commute(words)
    counts['solutions']+=1
    if covered(i,k,l):
        counts['new_region_solutions']+=1
        assert periodic, (i,k,l,words)
    if not periodic: counts['nonperiodic']+=1
    if not min(x,y,u,v) or x<=u: return
    d=x-u; D=v-y; R=root(X); r=len(R)
    assert 3*D==(i+k+l)*d
    if len(set(R))>1: counts['nonunary_roots']+=1
    L=2*D-i*d; Q=D-l*d
    if L<0 or Q<0: return
    C=(X*i)[i*u:]; B=(X*l)[:l*d]; P=(X*k)[:L]; A=(X*k)[L+k*u:]
    assert X*i==U*i+C and X*l==B+U*l and X*k==P+U*k+A
    assert len(A)==Q and V==A+Y+B and C+Y*2+P==V*2
    counts['nested_identities']+=1
    H=Q-i*d; F=L-l*d
    if i and min(i*u,k*u)+min(i*d,Q)>=r:
        assert H%r==0; counts['prefix_phase']+=1
    if l and min(l*u,k*u)+min(l*d,L)>=r:
        assert F%r==0; counts['suffix_phase']+=1
    if D%r==0 or X+U==U+X:
        assert periodic; counts['propagation']+=1
    if not periodic: counts['nested_nonperiodic_controls']+=1
    if not l and i>0 and i+k>=3 and k!=2*i and k<=i<=2*k:
        E=C[len(A):]; assert E and E==factor(R,0,len(E)) and len(E)%r==0
        assert E+Y*2+P==Y+A+Y
        assert y%r==(-D)%r; counts['nested_zero_tail_transport']+=1
    if not i and k>2*l>0:
        E=P[:len(P)-len(B)]; assert E and P==E+B and len(E)%r==0
        assert Y*2+E==A+Y+B+A+Y; counts['zero_head_transport']+=1
    if i*k*l>0 and k>=2 and L>0 and Q>0 and F<0 and Q>=d:
        E=C[len(A):]; G=B[:len(B)-len(P)]
        assert C==A+E and B==G+P and E+Y*2==Y+B+A+Y+G
        counts['negative_F_transport']+=1


def main():
    counts=defaultdict(int)
    for i,k,l in product(range(7),range(1,7),range(7)):
        if not i+l: continue
        for d,u,y in product(range(1,7),range(4),range(4)):
            if (i+k+l)*d%3: continue
            D=(i+k+l)*d//3
            check(i,k,l,generic(i,k,l,u+d,y,u,y+D),counts)
    print('literal graph:',dict(counts))
    counts=defaultdict(int)
    for i,k,l in product(range(7),range(1,7),range(7)):
        if not i+l: continue
        for R,u,y,d in product(('ab','aba','aabb','abac'),range(1,3),range(1,3),(3,6)):
            D=(i+k+l)*d//3
            check(i,k,l,tuple(tuple(w) for w in (R*(u+d),R*y,R*u,R*(y+D))),counts)
    print('nonunary periodic instantiations:',dict(counts))
    cnt=0
    for n in range(1,7):
        X='a'*n+'b'+'a'*n; Y=('b'+'a'*(2*n))*(n-1)+'b'; U='a'; V=Y+'a'*n+Y
        for i,k,l in ((n,n,n),(n,2*n,0)):
            assert not covered(i,k,l) and not commute((X,Y,U,V))
            assert len(V)>=max(map(len,(X,Y,U)))
            check(i,k,l,tuple(tuple(w) for w in (X,Y,U,V)),defaultdict(int)); cnt+=1
        if n>=3:
            T='0'*(3*n); X=(T+'1')*3; Y='0'*n; U='000'; V=('1'+T)*n
            for i,l,words in ((n,0,(X,Y,U,V)),(0,n,tuple(w[::-1] for w in (X,Y,U,V)))):
                assert not covered(i,0,l) and not commute(words)
                assert expand(i,0,l,*words[:2])==expand(i,0,l,*words[2:])
                assert len(words[3])>=max(map(len,words[:3])); cnt+=1
    words=('aaba','aaa','b','aaaa')
    assert expand(0,1,0,*words[:2])==expand(0,1,0,*words[2:]) and not commute(words)
    assert not covered(0,1,0); cnt+=1
    print('explicit B/C/D/sporadic nonforcing controls:',cnt)
    # Validate the local rotation-count obstruction independently of the full equation.
    ntests=0
    for u in range(1,6):
        for U,J in product(product('01',repeat=u),repeat=2):
            if U==J: continue
            for m in range(5,9):
                R=J+U*(m-1)
                for s in range(m*u):
                    rot=R[s:]+R[:s]; blocks=[rot[a:a+u] for a in range(0,m*u,u)]
                    assert not (blocks.count(J)==2 and blocks.count(U)==m-2)
                    ntests+=1
    print('rotation obstruction tests:',ntests)
    print('PASS')

if __name__=='__main__': main()
