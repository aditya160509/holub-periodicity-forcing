import json, re, sys
from fractions import Fraction as F
T=[(0,1,3),(0,1,4),(1,1,3),(1,1,4),(0,1,5),(0,1,6),(0,2,5),(0,2,6),(0,3,5),(0,4,6),(1,1,5),(1,1,6),(1,2,5),(1,2,6),(2,1,5),(2,1,6),(2,2,6),(3,1,6)]
rows=[]; tot=[0,0,0,0]
for t in T:
    n=''.join(map(str,t))
    D=json.load(open('cov%s.json'%n)); chk=open('chk%s.txt'%n).read().strip().splitlines()[-1]
    m=re.search(r'covering pieces: (\d+)',chk); ok=chk.endswith('OK')
    S=sum(t); kap=3 if S%3 else 1; c=t[0]+t[2]-2
    nz=sum(1 for C in D['certs'] if C.get('zeros'))
    nu=sum(1 for C in D['certs'] if C['kind']=='u'); npp=len(D['certs'])-nu
    rows.append((t,kap,F(kap,c),F(D['Ymax']),len(D['certs']),nu,npp,nz,len(D.get('points',[])),int(m.group(1)) if m else -1,ok))
    tot[0]+=len(D['certs']); tot[1]+=len(D.get('points',[])); tot[2]+=nz
print('tuple kap u/w< y/w< certs (u-closed,p-closed) line-certs points pieces checked')
for r in rows: print(*r)
print('total certs',tot[0],'points',tot[1],'line certs',tot[2],'all checked',all(r[-1] for r in rows))
# LaTeX table
L=['\\begin{table}[ht]\\centering\\small','\\begin{tabular}{lcccrrrr}','\\toprule',
   '\\((i,k,\\ell)\\) & \\(\\kappa\\) & \\(u/w<\\) & \\(Y_*\\) & cones & \\(u\\)/\\(p\\) closures & on lines & points\\\\','\\midrule']
for (t,kap,ub,Y,nc,nu,npp,nz,npt,pieces,ok) in rows:
    L.append('\\((%d,%d,%d)\\) & %d & \\(%s\\) & \\(%s\\) & %d & %d/%d & %d & %d\\\\'%(t+(kap,str(ub),str(Y),nc,nu,npp,nz,npt)))
L+=['\\midrule','total & & & & %d & & %d & %d\\\\'%(tot[0],tot[2],tot[1]),'\\bottomrule','\\end{tabular}',
    '\\caption{Certified coverings for Theorem~\\ref{tail:certified}. Here \\(d=\\kappa w\\); the region is \\(0<u/w<\\kappa/c\\), \\(0<y/w<Y_*\\). Points are closed by Lemma~\\ref{tail:dilation}.}\\label{tab:cert}','\\end{table}']
open('table.tex','w').write('\n'.join(L)+'\n')
