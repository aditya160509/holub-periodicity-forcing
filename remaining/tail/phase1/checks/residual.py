from math import gcd
def general(i,k,l):
    # Theorem tail:general
    if not (i+k<2*l and 2*i<=k+l): return False
    m=i+l-2*k; c=i+l-2
    if m==0 or c<abs(m) or c<1: return False
    a=k+l-2*i; gs=2*l-i-k; s=i+k+l; eta=2*i+2*l-k; g0=gcd(s,eta)
    if (eta-3-g0)*c<3: return False
    if m>0: return (3*k>=gs or 3*(k-1)>=a) and min(s,3*k,eta)>=gs-g0
    return 3*(k-1)>=a and min(s,3*k,eta)>=a-g0
def windows(i,k,l):
    if not (i+k<2*l and k>=1): return False
    c=i+l-2; m=i+l-2*k
    if m==0: return False
    a=min(3*i,i+k+l); b=3*k+min(0,2*m); s=3*k+max(m,2*m)
    return c>0 and abs(m)<=c+1 and c*(a+b-s)>=3*(c+1)
def proved(i,k,l):
    if k==0 or l==0: return True                 # slices
    if not (i+k<2*l): return True                # outside tail: other sections
    if i+l==2*k: return True                     # ray
    if k>=l: return True                         # diagonal & k>=l corollary
    if 2*i>k+l: return True                      # band
    if 2*k-i-l>=3: return True                   # seam/div
    if general(i,k,l) or windows(i,k,l): return True
    if max(i,k,l)<=6: return True                # settled computations (Sec. 13)
    return False
for N in (10,20,40):
    R=[(i,k,l) for i in range(N+1) for k in range(N+1) for l in range(N+1) if not proved(i,k,l)]
    ks=sorted({k for i,k,l in R}); print('N',N,'residual',len(R),'k values',ks[:12],'max k/l %.3f'%max(k/l for i,k,l in R) if R else '')
    from collections import Counter
    print('  count by k',sorted(Counter(k for i,k,l in R).items())[:10])
    print('  i max by k',{kk:max(i for i,k,l in R if k==kk) for kk in ks[:6]})
