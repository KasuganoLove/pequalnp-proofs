#include <array>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

// Search only a structured subfamily: 38 point-only gates with 13 outputs,
// followed by 13 line-ANDs and 12 final ORs. First point gate stays a raw OR.
// No unsuccessful search is interpreted as a lower-bound proof.
using Bits=std::array<uint64_t,4>;
struct Gate {int op,a,b;};
using State=std::array<Gate,38>;
struct Eval {int score;std::array<int,13> outputs,errors;};
std::array<Bits,13> raw{},positive{},negative{};
std::vector<State> seeds;
uint64_t calls=0;
std::mt19937_64 rng(38234320261125ULL);
int line[13][4];

Eval eval(const State &s,int weight=4) {
 ++calls;std::array<Bits,51>w;
 for(int i=0;i<13;i++)w[i]=raw[i];
 for(int i=0;i<38;i++)for(int k=0;k<4;k++)w[13+i][k]=s[i].op?(w[s[i].a][k]|w[s[i].b][k]):(w[s[i].a][k]&w[s[i].b][k]);
 Eval e;e.score=0;
 for(int l=0;l<13;l++){
  int best=100000,out=0;
  for(int v=0;v<51;v++){
   int err=0;for(int k=0;k<4;k++)err+=weight*__builtin_popcountll(~w[v][k]&positive[l][k])+__builtin_popcountll(w[v][k]&negative[l][k]);
   if(err<best){best=err;out=v;if(best==0)break;}
  }
  e.score+=best;e.outputs[l]=out;e.errors[l]=best;
 }
 return e;
}
void save(const State &s,const Eval&e,const char*fn){
 std::ofstream f(fn);f<<"{\"gates\":[";
 for(int i=0;i<38;i++)f<<(i?",":"")<<"["<<s[i].op<<","<<s[i].a<<","<<s[i].b<<"]";
 f<<"],\"outputs\":[";for(int i=0;i<13;i++)f<<(i?",":"")<<e.outputs[i];
 f<<"],\"errors\":[";for(int i=0;i<13;i++)f<<(i?",":"")<<e.errors[i];
 f<<"],\"weighted_score\":"<<e.score<<"}\n";
}
int main(int argc,char**argv){
 int sec=argc>1?std::atoi(argv[1]):120;
 const int D[4]={0,1,3,9};for(int l=0;l<13;l++)for(int j=0;j<4;j++)line[l][j]=(l+D[j])%13;
 for(int p=0;p<13;p++)raw[p][0]|=1ULL<<p;
 int row=13;
 for(int a=0;a<13;a++)for(int b=a+1;b<13;b++)for(int c=b+1;c<13;c++)for(int d=c+1;d<13;d++){
  int mask=(1<<a)|(1<<b)|(1<<c)|(1<<d);bool good=true;
  for(int l=0;l<13;l++){int n=0;for(int j=0;j<4;j++)n+=(mask>>line[l][j])&1;if(n>2)good=false;}
  if(!good)continue;
  for(int p=0;p<13;p++)if((mask>>p)&1)raw[p][row/64]|=1ULL<<(row%64);
  for(int l=0;l<13;l++){int n=0;for(int j=0;j<4;j++)n+=(mask>>line[l][j])&1;if(n==0)negative[l][row/64]|=1ULL<<(row%64);}
  row++;
 }
 if(row!=247)return 2;
 for(int l=0;l<13;l++){
  for(int j=0;j<4;j++)positive[l][0]|=1ULL<<line[l][j];
  negative[l][0]|=((1ULL<<13)-1)&~positive[l][0];
 }
 std::array<Gate,39> base;
 for(int l=0;l<13;l++){int k=3*l;base[k]={1,line[l][0],line[l][1]};base[k+1]={1,line[l][2],line[l][3]};base[k+2]={1,13+k,14+k};}
 for(int dead=0;dead<39;dead++)if(dead%3!=2)for(int side=0;side<2;side++){
  int old=13+dead,alias=side?base[dead].b:base[dead].a;
  auto remap=[&](int x){if(x==old)x=alias;return x-(x>old);};State s;int k=0;
  for(int j=0;j<39;j++)if(j!=dead)s[k++]={base[j].op,remap(base[j].a),remap(base[j].b)};
  if(eval(s).score!=4)return 3;seeds.push_back(s);
 }
 auto start=std::chrono::steady_clock::now(),last=start;
 int best=4;uint64_t restarts=0,accepted=0;State bs=seeds[0];Eval be=eval(bs);
 while(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<sec){
  State cur=seeds[rng()%seeds.size()];int weight=1+restarts%5;auto ce=eval(cur,weight);
  for(int iter=0;iter<7000;iter++){
   State cand=cur;int changes=rng()%12==0?2:1;
   for(int k=0;k<changes;k++){
    int j=rng()%38,f=rng()%12;
    if(f==0 && j!=0)cand[j].op^=1;
    else if(f<=5)cand[j].a=rng()%(13+j);
    else if(f<=10)cand[j].b=rng()%(13+j);
    else{cand[j].a=rng()%(13+j);cand[j].b=rng()%(13+j);}
    if(cand[j].a>cand[j].b)std::swap(cand[j].a,cand[j].b);
   }
   auto ne=eval(cand,weight);
   if(ne.score==0){save(cand,ne,"multioutput-witness.json");std::cout<<"WITNESS evals="<<calls<<"\n";return 0;}
   if(ne.score<4){auto norm=eval(cand);if(norm.score<best){best=norm.score;bs=cand;be=norm;save(bs,be,"multioutput-best.json");std::cout<<"best="<<best<<" calls="<<calls<<"\n"<<std::flush;}}
   double temp=(iter<5000?0.5:0.1)+0.2*(restarts%4);
   if(ne.score<=ce.score||std::generate_canonical<double,53>(rng)<std::exp((ce.score-ne.score)/temp)){cur=cand;ce=ne;++accepted;}
   if((iter&255)==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=sec)break;
  }
  ++restarts;auto now=std::chrono::steady_clock::now();
  if(std::chrono::duration<double>(now-last).count()>=15){std::cout<<"elapsed="<<int(std::chrono::duration<double>(now-start).count())<<" evals="<<calls<<" restarts="<<restarts<<" best="<<best<<"\n"<<std::flush;last=now;}
 }
 save(bs,be,"multioutput-best.json");
 std::cout<<"DONE no witness; evaluations="<<calls<<" accepted="<<accepted<<" restarts="<<restarts<<" best="<<best<<"\n";
}
