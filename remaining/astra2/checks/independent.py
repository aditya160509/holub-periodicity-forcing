"""Local and solution-level regression checks. No dependencies outside Python."""
import csv
from itertools import accumulate, combinations, product
from math import gcd
from pathlib import Path
from functools import reduce

here = Path(__file__).resolve().parent

def expand(pattern, a, b):
    return sum((a if c == 'a' else b for c in pattern), ())

def generic(w, lengths):
    off = list(accumulate((0, *lengths)))
    blocks = [tuple(range(a,b)) for a,b in zip(off,off[1:])]
    par = list(range(off[-1]))
    def root(x):
        while x != par[x]:
            par[x] = par[par[x]]
            x = par[x]
        return x
    left, right = expand(w,*blocks[:2]), expand(w,*blocks[2:])
    assert len(left)==len(right)
    for a,b in zip(left,right):
        par[root(a)] = root(b)
    words = [tuple(map(root,block)) for block in blocks]
    assert expand(w,*words[:2])==expand(w,*words[2:])
    return words

def bad(words):
    return any(a+b!=b+a for a,b in combinations(words,2))

def bounds(w,d,D):
    es = {'a': [],'b': []}
    e=0
    for c in w:
        es[c].append(e)
        e+=d if c=='a' else -D
    res=[]
    for c,delta in [('a',-d),('b',D)]:
        m,M=min(es[c]),max(es[c])
        P=M-m
        z=max(0,m)
        res.append(min(2*max(abs(m),abs(M))+7*P,
            max(z-m+2*P,z-m+P+d,z+2*P+d-delta)+min(0,delta)))
    return res

def cell(w,x,y,u,v):
    # Relative order of all occurrence boundaries, including ties.
    L=list(accumulate(x if c=='a' else y for c in w))
    R=list(accumulate(u if c=='a' else v for c in w))
    return tuple((a>b)-(a<b) for a in L for b in R)

cells={}
examples=None
checked=positive=scaled=0
for row in csv.DictReader((here/'controls.csv').open()):
    i,k,l,d=map(int,[row[s] for s in ('i','k','l','d')])
    if d>6:continue
    w='a'*i+'bb'+'a'*k+'b'+'a'*l
    D=(i+k+l)*d//3
    A,B=bounds(w,d,D)
    counts=[0,0]
    for u,y in product(range(A),range(B)):
        lengths=(u+d,y,u,y+D)
        words=generic(w,lengths)
        witness=bad(words)
        positive+=witness
        checked+=1
        h=reduce(gcd,lengths)
        if h>1:
            small=generic(w,[x//h for x in lengths])
            assert bad(small)==witness
            scaled+=witness
        if witness:
            counts[0]+=1
            counts[1]+=int(y+D>=u+d)
        if min(lengths)>0 and h==1:
            key=w,cell(w,*lengths),lengths[3]>=lengths[0]
            if key in cells and cells[key][1]!=witness and examples is None:
                examples=(w,cells[key],(lengths,witness))
            cells[key]=(lengths,witness)
    assert counts==[int(row['bad_free']),int(row['bad_holub'])]
print('literal component-label control checks',checked,'positive',positive,'positive scaled',scaled)
assert examples
print('same endpoint order, different answer (X,Y,U,V lengths)',examples)

# Test extreme-offset cuts on abstract words, including nonunary components.
cnt=rich=0
for m,M in combinations(range(-4,5),2):
    P=M-m; z=max(m,0); t=z-m
    for d in range(1,9):
        a=max(t+2*P,t+P+d)
        b=z+2*P+d
        # Concrete periodic interval; use distinct symbols outside it.
        B=list(range(b))
        B[z:]=[100+j%P for j in range(b-z)]
        A=[B[m+j] if 0<=m+j<b else -j-1 for j in range(a)]
        assert A[t:t+P]==A[t+P:t+2*P]
        ref=B[:z]+B[z+P:]
        for j in range(z,z+P+1):
            assert ref==B[:j]+B[j+P:]
        cnt+=1;rich+=len(set(B[z:]))>1
print('local periodic cuts',cnt,'nonunary periodic cores',rich)

# Binary literal local factors; the word equation is not imposed here.
words=[''.join(v) for n in range(1,7) for v in product('01',repeat=n)]
middle=nonunary=0
for X,U in [*product(words,repeat=2), ('ab'*5,'ab'*2)]:
    x,u=len(X),len(U);d=x-u
    if d<=0:continue
    for i,k,l in ((0,3,1),(1,3,0),(1,4,0),(1,5,1),(0,6,2)):
        if (i+k+l)*d%3 or k*u<x+u-gcd(x,u):continue
        D=(i+k+l)*d//3; L=2*D-i*d
        if i and not X.startswith(U) or l and not X.endswith(U):continue
        if (X*k)[L:L+k*u]!=U*k:continue
        assert X+U==U+X
        r=next(h for h in range(1,x+1) if x%h==0 and X[:h]*(x//h)==X)
        assert D%r==0
        middle+=1;nonunary+=r>1
print('middle-block local instances',middle,'nonunary primitive roots',nonunary)
assert nonunary

# Check the k=3 edge implication directly from its local suffix/nesting identities.
edge=0
for s in (2,3,4):
    for C in map(''.join,product('01',repeat=s)):
        for u in range(2*s+1,3*s):
            for U in map(''.join,product('01',repeat=u)):
                X=U+C*3
                if not (X*3).endswith(U*3+C*4):continue
                assert U+C==C+U
                edge+=1
assert edge
print('edge local instances',edge)
# Arbitrary word pairs check the two-constant conjunction encoding.
short=['',*words[:6]]
for L,R,A,B in product(short,repeat=4):
    assert (L+'0'+A+L+'1'+A==R+'0'+B+R+'1'+B)==(L==R and A==B)
print('two-constant equation encodings',len(short)**4)

# The prescribed mismatch constants prevent a spurious Boolean branch.
short=['','0','1','00','01','10','11']
for a,b,c,d in product(short,repeat=4):
    assert ((a+'0'+b+a+'1'+b)==(c+'0'+d+c+'1'+d))==((a,b)==(c,d))
enc=0
for V,X in product(words,repeat=2):
    branch=any((V[j:]+V[:j]).startswith(X) for j in range(len(V)))
    assert branch==(len(X)<=len(V) and X in V+V)
    enc+=branch
print('equation-pair encodings',len(short)**4,'positive rotation certificates',enc)
