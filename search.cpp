#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
struct DSU {
    vector<int> p;
    explicit DSU(int n):p(n,-1){}
    int root(int x){return p[x]<0?x:p[x]=root(p[x]);}
    void join(int a,int b){a=root(a);b=root(b);if(a==b)return;
        if(p[a]>p[b])swap(a,b);p[a]+=p[b];p[b]=a;}
};
int main(int argc,char**argv){
    int limit=argc>1?stoi(argv[1]):100;
    long long all=0,primitive=0;
    for(int v=1;v<=limit;v++)for(int t=1;4*t<=v;t++)for(int u=0;u+3*t<=v;u++){
        int y=v-4*t,x=u+3*t,g=gcd(gcd(u,y),t);++all;
        if(g>1)continue;
        ++primitive;
        array<int,4> len{x,y,u,v},off{0,x,x+y,x+y+u};
        DSU d(x+y+u+v);
        vector<int> left,right;
        for(int i:{0,0,1,1,0,1,0}){
            for(int j=0;j<len[i];j++)left.push_back(off[i]+j);
            for(int j=0;j<len[i+2];j++)right.push_back(off[i+2]+j);}
        for(int i=0;i<(int)left.size();i++)d.join(left[i],right[i]);
        int classes=count_if(d.p.begin(),d.p.end(),[](int z){return z<0;});
        if(classes!=1){cout<<"candidate "<<u<<" "<<y<<" "<<t<<" classes "<<classes<<endl;return 1;}
    }
    cout<<"max V "<<limit<<" admissible "<<all<<" primitive "<<primitive<<" failures 0\n";
}
