#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <random>
using U=__uint128_t;
struct G{int op,a,b;};
using C=std::array<G,12>;
const std::array<G,13> baseline={G{1,0,2},G{0,0,2},G{0,4,7},G{1,8,9},G{1,7,4},G{1,5,6},G{0,11,12},G{1,10,13},G{1,1,3},G{0,1,3},G{0,6,15},G{1,16,17},G{1,14,18}};
std::array<U,7> raw;
U target;
unsigned pop(U a){return std::popcount((uint64_t)a)+std::popcount((uint64_t)(a>>64));}
int score(const C& c){
 std::array<U,19>w{};for(int i=0;i<7;i++)w[i]=raw[i];
 for(int j=0;j<12;j++){auto g=c[j];w[7+j]=g.op?(w[g.a]|w[g.b]):(w[g.a]&w[g.b]);}
 U x=w[18];return 8*pop(x&~target)+pop(target&~x);
}
C erase(int k,int side){
 C c; int alt=side?baseline[k].b:baseline[k].a;
 auto ren=[&](int w){if(w==7+k)w=alt;return w>7+k?w-1:w;};
 for(int i=0,j=0;i<13;i++)if(i!=k){auto g=baseline[i];c[j++]={g.op,ren(g.a),ren(g.b)};}
 return c;
}
int main(){
 int edges[][2]={{0,2},{1,3},{0,4},{2,4},{0,5},{2,5},{4,5},{0,6},{1,6},{2,6},{3,6},{4,6}};
 for(int x=0;x<128;x++){
  for(int i=0;i<7;i++)if(x>>i&1)raw[i]|=U(1)<<x;
  for(auto&e:edges)if((x>>e[0]&1)&&(x>>e[1]&1)){target|=U(1)<<x;break;}
 }
 std::mt19937_64 rng(10696);C best{};int bs=100000;uint64_t evals=0,restarts=0;
 auto start=std::chrono::steady_clock::now();bool done=false;
 while(!done){
  C c=erase(rng()%12,rng()%2);int cs=score(c);evals++;
  if(restarts%7==0)for(int j=0;j<12;j++)c[j]={int(rng()%2),int(rng()%(7+j)),int(rng()%(7+j))};
  cs=score(c);evals++;
  for(int step=0;step<8000;step++){
   if(cs<bs){bs=cs;best=c;std::cerr<<"best "<<bs<<" at "<<evals<<" evaluations\n";}
   if(bs==0){done=true;break;}
   int j=rng()%12;G old=c[j];int kind=rng()%5;
   if(kind==0)c[j].op^=1;
   else if(kind<3)c[j].a=rng()%(7+j);
   else c[j].b=rng()%(7+j);
   int ns=score(c);evals++;
   bool take=ns<=cs || ((rng()%10000)<(step%1000<50?90:3));
   if(take)cs=ns;else c[j]=old;
   if((evals&16383)==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=20){done=true;break;}
  }
  restarts++;
 }
 double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::cout<<"{\"seed\":10696,\"seconds_cap\":20,\"elapsed_seconds\":"<<elapsed<<",\"evaluations\":"<<evals<<",\"restarts\":"<<restarts<<",\"best_weighted_score\":"<<bs<<",\"output\":18,\"gates\":[";
 for(int i=0;i<12;i++){if(i)std::cout<<",";auto g=best[i];std::cout<<"[\""<<(g.op?"or":"and")<<"\","<<g.a<<","<<g.b<<"]";}
 std::cout<<"]}\n";
}
