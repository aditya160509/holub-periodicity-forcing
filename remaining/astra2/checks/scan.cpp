// c++ -std=c++17 -O3 scan.cpp -o scan && ./scan > search.csv
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
struct Box { int old, tight; };
Box bounds(const vector<int>& e,int delta,int d){
    // a=|A|, b=|B|=a+delta. z=max(0,m), t=z-m.
    int m=*min_element(e.begin(),e.end()), M=*max_element(e.begin(),e.end());
    int p=M-m,z=max(0,m),t=z-m;
    if(p<=0) abort();
    int amin=max(t+2*p,t+p+d);
    amin=max(amin,z+2*p+d-delta);
    return {2*max(abs(m),abs(M))+7*p,amin+min(0,delta)};
}
bool covered(int i,int k,int l){
    int s=i+k+l;
    return !k || (!i&&!l) || i==k&&k==l || !l&&k==2*i ||
      s%3==0&&(i==s/3||i<=2*s/3&&2*s/3<=i+k) ||
      !i&&k==l || !l&&i==k || i==2*k&&k==l;
}
struct Solver{
    vector<int> parent;
    int root(int a){
        while(parent[a]!=a){parent[a]=parent[parent[a]];a=parent[a];}
        return a;
    }
    bool bad(const string& w,int x,int y,int u,int v){
        int g=gcd(gcd(x,u),gcd(y,v));
        x/=g;y/=g;u/=g;v/=g;
        int n=x+y+u+v, components=n;
        parent.resize(n);iota(parent.begin(),parent.end(),0);
        auto join=[&](int a,int b){a=root(a);b=root(b);if(a!=b){parent[a]=b;--components;}};
        int i=0,j=0,t=0,s=0;
        while(i<(int)w.size()&&j<(int)w.size()){
            bool a=w[i]=='a',b=w[j]=='a';
            int ll=a?x:y,rr=b?u:v,L=a?0:x,R=b?x+y:x+y+u;
            int len=min(ll-t,rr-s);
            for(int h=0;h<len;++h)join(L+t+h,R+s+h);
            if(components==1)return false;
            t+=len;s+=len;
            if(t==ll){++i;t=0;}
            if(s==rr){++j;s=0;}
        }
        return components>1;
    }
};
int main(int argc,char**argv){
    int cap=argc>1?atoi(argv[1]):6;
    bool controls=argc>2 && string(argv[2])=="controls";
    bool full=argc>2 && string(argv[2])=="full";
    bool extra=argc>2 && string(argv[2])=="extra";
    cout<<"i,k,l,d,old_box,visited,holub_visited,bad_free,bad_holub\n";
    Solver solver;
    for(int i=0;i<=cap;++i)for(int k=0;k<=cap;++k)for(int l=0;l<=cap;++l){
        if(controls ? !(i==k&&k==l&&i>0 || i>0&&k==2*i&&!l) : covered(i,k,l))continue;
        string w=string(i,'a')+"bb"+string(k,'a')+"b"+string(l,'a');
        for(int d=1;d<=12;++d){
            long long old=0,total=0,cond=0,bad=0,restricted=0;
            if((i+k+l)*d%3==0){
                int D=(i+k+l)*d/3,e=0; vector<int>a,b;
                for(char c:w){(c=='a'?a:b).push_back(e);e+=c=='a'?d:-D;}
                Box A=bounds(a,-d,d),B=bounds(b,D,d);
                old=1LL*A.old*B.old;
                int span=*max_element(b.begin(),b.end())-*min_element(b.begin(),b.end());
                int max_y=extra?max(B.old,A.old+d+3*span-D):(full?B.old:min(B.old,B.tight));
                for(int u=0;u<(full||extra?A.old:min(A.old,A.tight));++u)
                  for(int y=extra?max(B.old,u+d-D):0;y<max_y;++y){
                    ++total;bool ok=y+D>=u+d;cond+=ok;
                    if(solver.bad(w,u+d,y,u,y+D)){++bad;restricted+=ok;}
                  }
            }
            cout<<i<<','<<k<<','<<l<<','<<d<<','<<old<<','<<total<<','<<cond<<','<<bad<<','<<restricted<<'\n';
        }
    }
}
