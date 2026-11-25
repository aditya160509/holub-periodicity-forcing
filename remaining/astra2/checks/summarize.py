"""Verify full-box coverage and merge the two Holub ranges, per tuple and d."""
import csv
from pathlib import Path
from itertools import product

base=Path(__file__).resolve().parent
def rows(name):
    with (base/name).open() as f:
        return [dict((k,int(v)) for k,v in r.items()) for r in csv.DictReader(f)]
def key(r):
    return tuple(r[c] for c in ('i','k','l','d'))
def open_tuple(i,k,l):
    s=i+k+l
    return not (k==0 or i==l==0 or i==k==l or l==0 and k==2*i
                or s%3==0 and (3*i==s or 3*i<=2*s<=3*(i+k))
                or i==0 and k==l or l==0 and i==k or i==2*k and k==l)
for n in (4,6):
    full,extra,tight=(rows(f'{mode}{n}.csv') for mode in ('full','extra','through'))
    expected={(i,k,l,d) for i,k,l in product(range(n+1),repeat=3)
              if open_tuple(i,k,l) for d in range(1,13)}
    for data in (full,extra,tight):
        assert len(expected)==len(data) and set(map(key,data))==expected
    totals=[0]*4
    with (base/f'results{n}.csv').open('w') as f:
        out=csv.writer(f)
        out.writerow(['i','k','l','d','free_checked','holub_checked','free_witnesses','holub_witnesses'])
        for a,b,c in zip(full,extra,tight):
            assert key(a)==key(b)==key(c)
            i,k,l,d=key(a)
            common=restricted=0
            if (i+k+l)*d%3==0:
                D=(i+k+l)*d//3
                e=0; off={'a':[],'b':[]}
                for ch in 'a'*i+'bb'+'a'*k+'b'+'a'*l:
                    off[ch].append(e)
                    e+=d if ch=='a' else -D
                def T(z):
                    return 2*max(map(abs,z))+7*(max(z)-min(z))
                A,B=map(T,off.values())
                common=A*B
                ymax=max(B,A+d+3*(max(off['b'])-min(off['b']))-D)
                restricted=sum(max(0,ymax-max(0,u+d-D)) for u in range(A))
            counts=[a['visited'],a['holub_visited']+b['holub_visited'],a['bad_free'],a['bad_holub']+b['bad_holub']]
            assert counts[:2]==[common,restricted]
            assert c['bad_free']==0 and counts[2:]==[0,0]
            out.writerow([*key(a),*counts])
            totals=[x+y for x,y in zip(totals,counts)]
    print(n,len(expected)//12,'tuples',len(expected),'rows',*totals)
