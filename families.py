"""Explicit counterexample families for Holub's problem; each check is a full proof for that instance."""
def P(t,A,B):
    i,j,k,l=t; return A*i+B+A*j+B+A*k+B+A*l
def ok(t,X,Y,U,V):
    W=[X,Y,U,V]
    return (P(t,X,Y)==P(t,U,V) and not(X==U and Y==V)
            and any(a+b!=b+a for a in W for b in W) and max(len(X),len(Y),len(U))<=len(V))
bad=[]
for n in range(1,41):
    X='a'*n+'b'+'a'*n; Y=('b'+'a'*(2*n))*(n-1)+'b'; U='a'; V=Y+'a'*n+Y
    for t in [(n,0,n,n),(n,n,0,n),(0,n,2*n,0),(0,2*n,n,0),(0,2*n,0,n),(n,0,2*n,0)]:
        if not ok(t,X,Y,U,V): bad.append(t)
for m in range(0,41):          # family A: (i,m,m,m-i)
    for i in range(m+1):
        if not ok((i,m,m,m-i),'a','b','',  'a'*i+'b'+'a'*(m-i)): bad.append((i,m,m,m-i))
for m in range(3,41):          # family B (manuscript): a^m b^3 and reversal
    T='0'*(3*m); X=(T+'1')*3; Y='0'*m; U='000'; V=('1'+T)*m
    if not ok((m,0,0,0),X,Y,U,V): bad.append((m,0,0,0))
    if not ok((0,0,0,m),X[::-1],Y[::-1],U[::-1],V[::-1]): bad.append((0,0,0,m))
sp={(1,0,0,0):('abbb','bbb','a','bbbb'),(2,0,0,0):('aabaaaabaaaab','aabaa','a','baaaabaaaabaa'),
    (0,0,1,0):('aaba','aaa','b','aaaa'),(0,1,1,0):('abababa','bab','a','bababab'),(1,1,1,1):('abababa','b','a','babababab')}
for t,w in list(sp.items()):
    sp[t[::-1]]=tuple(s[::-1] for s in w)
for t,w in sp.items():
    if not ok(t,*w): bad.append(t)
print('failures:',bad)
