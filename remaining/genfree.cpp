// Fast generic-solution search for Holub periodicity forcing.
// usage: gen MAXEXP VMAX  -> per tuple: first counterexample lengths (x y u v) or "none"
#include <vector>
#include <string>
#include <numeric>
#include <cstdio>
#include <cstdlib>
using namespace std;
vector<int> par;
int f(int a){while(par[a]!=a){par[a]=par[par[a]];a=par[a];}return a;}
bool comm(const vector<int>&a,const vector<int>&b){
  size_t n=a.size()+b.size();
  for(size_t t=0;t<n;t++){int p=t<a.size()?a[t]:b[t-a.size()];int q=t<b.size()?b[t]:a[t-b.size()];if(p!=q)return false;}
  return true;}
int main(int c,char**v){
  int M=atoi(v[1]),VM=atoi(v[2]);
  int I0=c>3?atoi(v[3]):-1;
  for(int i=0;i<=M;i++){ if(I0>=0&&i!=I0)continue;for(int j=0;j<=0;j++)for(int k=0;k<=M;k++)for(int l=0;l<=M;l++){
    string pat=string(i,'a')+"b"+string(j,'a')+"b"+string(k,'a')+"b"+string(l,'a');
    int na=i+j+k+l; bool found=false;
    for(int V=0;V<=VM&&!found;V++)for(int x=0;x<=VM&&!found;x++)for(int u=0;u<=VM&&!found;u++){
      int num=na*(u-x)+3*V; if(num%3)continue; int y=num/3; if(y<0||y>VM)continue;
      int ox=0,oy=x,ou=x+y,ov=x+y+u,n=ov+V; par.resize(n); iota(par.begin(),par.end(),0);
      vector<int>L,R;
      for(char ch:pat){ if(ch=='a'){for(int t=0;t<x;t++)L.push_back(ox+t);for(int t=0;t<u;t++)R.push_back(ou+t);}
        else{for(int t=0;t<y;t++)L.push_back(oy+t);for(int t=0;t<V;t++)R.push_back(ov+t);} }
      for(size_t t=0;t<L.size();t++){int a=f(L[t]),b=f(R[t]);if(a!=b)par[a]=b;}
      auto w=[&](int o,int ln){vector<int>r(ln);for(int t=0;t<ln;t++)r[t]=f(o+t);return r;};
      auto X=w(ox,x),Y=w(oy,y),U=w(ou,u),W=w(ov,V);
      if(X==U&&Y==W)continue;
      vector<vector<int>>A={X,Y,U,W}; bool all=true;
      for(auto&p:A)for(auto&q:A)if(!comm(p,q))all=false;
      if(!all){printf("%d%d%d%d %d %d %d %d\n",i,j,k,l,x,y,u,V);found=true;}
    }
    if(!found)printf("%d%d%d%d none\n",i,j,k,l);
    fflush(stdout);
  }}
}
