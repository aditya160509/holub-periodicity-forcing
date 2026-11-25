"""Execute in any directory. Reuse the repository's exhaustive length-30 table."""
from itertools import product
from math import gcd
from pathlib import Path

root = Path(__file__).resolve().parents[2]
table = dict(line.split(maxsplit=1) for line in (root/'free6.txt').read_text().splitlines())
for bound in (4,6):
    before, removed = [], []
    for i,k,l in product(range(bound+1), repeat=3):
        s = i+k+l
        if (not k or i==l==0 or i==k==l or (l==0 and k==2*i)
            or (s%3==0 and (i==s//3 or i<=2*s//3<=i+k)) or (i,k,l)==(2,1,1)):
            continue
        before.append((i,k,l))
        if (i==0 and k==l or l==0 and i==k or i==2*k and k==l):
            removed.append((i,k,l))
            assert table[f'{i}0{k}{l}']=='none'
    print(bound,len(before),len(before)-len(removed),removed)

# Generic positions satisfying the lemma's local overlap hypotheses only.
# Every concrete input is a letterwise image of the resulting components.
count = rich = 0
for offsets in product(range(-4,5),repeat=3):
    m,M=min(offsets),max(offsets)
    P=M-m
    if not P: continue
    H=max(-m,M)
    n=2*H+7*P
    for a,b in ((n,n),(n+3,n),(n,n+4)):
        parent=list(range(a+b))
        def find(x):
            while x!=parent[x]:
                parent[x]=parent[parent[x]]
                x=parent[x]
            return x
        for e in offsets:
            for t in range(max(0,-e),min(a,b-e)):
                parent[find(t)]=find(a+t+e)
        A=[find(x) for x in range(a)]
        B=[find(a+x) for x in range(b)]
        def cut(word,t):
            assert word[t:t+3*P]==word[t+3*P:t+6*P]
            return word[:t]+word[t+3*P:]
        cut(A,H)
        assert all(cut(B,H+e)==cut(B,H+m) for e in offsets)
        rich+=len(set(A+B))>1
        count+=1
print('local generic overlap tests',count,'with multiple components',rich)
# Directly enumerate possible border pairs, independently of word equations.
words=[''.join(w) for n in range(1,7) for w in product('01',repeat=n)]
hits=0
for X,U in product(words,repeat=2):
    x,u=len(X),len(U)
    if x<=u:continue
    for i,l in product(range(4),repeat=2):
        if (i+l)*u<x+u-gcd(x,u):continue
        if (X*i).startswith(U*i) and (X*l).endswith(U*l):
            hits+=1
            assert X+U==U+X
print('two-ended Fine-Wilf instances',hits)
