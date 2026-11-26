// Bounded heuristic search, not an impossibility certificate.
// Exact rows: all 15 edges and all 15 maximal independent sets of Petersen.
// A zero-error candidate must still be independently checked on all 1024 inputs.
#include <array>
#include <algorithm>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
struct Gate { int a,b; bool isOr; };
using Circuit = array<Gate,19>;
const array<pair<int,int>,15> E={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
vector<int> rows;
array<uint32_t,10> raw;
uint32_t target;
mt19937_64 rng;
uint64_t trials=0;
int ri(int n) {return int(rng()%n);}
bool positive(int m) { for(auto [a,b]:E)if((m>>a&1)&&(m>>b&1))return true;return false; }
int score(const Circuit &c) {
  array<uint32_t,29> v{}; copy(raw.begin(),raw.end(),v.begin());
  for(int i=0;i<19;i++){auto g=c[i];v[10+i]=g.isOr?(v[g.a]|v[g.b]):(v[g.a]&v[g.b]);}
  return popcount(v[28]^target);
}
void save(const Circuit &c,int sc,const string &path,uint64_t seed,double seconds) {
  ofstream o(path);o<<"{\"seed\":"<<seed<<",\"seconds\":"<<seconds<<",\"trials\":"<<trials<<",\"row_count\":"<<rows.size()<<",\"sample_errors\":"<<sc<<",\"output\":28,\"gates\":[";
  for(int i=0;i<19;i++){if(i)o<<',';auto g=c[i];o<<"{\"op\":\""<<(g.isOr?"or":"and")<<"\",\"inputs\":["<<g.a<<','<<g.b<<"]}";}
  o<<"]}\n";
}
Circuit seedCircuit() {
  vector<int> independent;
  for(int m=0;m<1024;m++)if(popcount((unsigned)m)==4&&!positive(m))independent.push_back(m);
  int cover=1023^independent[ri(independent.size())];
  vector<vector<int>> lists(10);
  for(auto [a,b]:E){int owner=(cover>>a&1)?a:b;if((cover>>a&1)&&(cover>>b&1))owner=ri(2)?a:b;lists[owner].push_back(owner==a?b:a);}
  vector<Gate> gs;
  auto join=[&](vector<int> a){while(a.size()>1){int k=ri(a.size());int x=a[k];a.erase(a.begin()+k);k=ri(a.size());int y=a[k];a.erase(a.begin()+k);gs.push_back({x,y,true});a.push_back(9+gs.size());}return a[0];};
  vector<int> centers, products;for(int v=0;v<10;v++)if(cover>>v&1)centers.push_back(v);shuffle(centers.begin(),centers.end(),rng);
  for(int v:centers){int w=join(lists[v]);gs.push_back({v,w,false});products.push_back(9+gs.size());}
  join(products);
  if(gs.size()!=20)abort();
  // Randomly interleave independent gates while preserving dependency order.
  vector<int> order, left(20);for(int i=0;i<20;i++)left[i]=i;array<int,30> rename{};for(int i=0;i<10;i++)rename[i]=i;
  vector<Gate> sorted;
  while(!left.empty()){vector<int> ready;for(int k=0;k<(int)left.size();k++){auto g=gs[left[k]];if((g.a<10||rename[g.a])&&(g.b<10||rename[g.b]))ready.push_back(k);}int k=ready[ri(ready.size())],old=left[k];left.erase(left.begin()+k);auto g=gs[old];sorted.push_back({rename[g.a],rename[g.b],g.isOr});rename[10+old]=9+sorted.size();}
  Circuit best{};int bs=99;
  for(int r=0;r<20;r++)for(int side=0;side<2;side++){
    Circuit c{};int replacement=side?sorted[r].a:sorted[r].b;
    auto remap=[&](int w){return w==10+r?replacement:w>10+r?w-1:w;};
    int j=0;for(int k=0;k<20;k++)if(k!=r){auto g=sorted[k];c[j++]={remap(g.a),remap(g.b),g.isOr};}
    // If the removed gate was the output, this seed is simply a candidate on
    // the remaining last wire; the scored circuit still has valid semantics.
    int s=score(c);if(s<bs||(s==bs&&ri(4)==0)){best=c;bs=s;}
  }
  return best;
}
int main(int argc,char**argv) {
  if(argc<4){cerr<<"usage: search seconds seed output.json\n";return 2;}
  double limit=atof(argv[1]);uint64_t seed=strtoull(argv[2],nullptr,10);rng.seed(seed);
  for(auto[a,b]:E)rows.push_back((1<<a)|(1<<b));
  for(int m=0;m<1024;m++)if(!positive(m)){bool maximal=true;for(int v=0;v<10;v++)if(!(m>>v&1)&&!positive(m|(1<<v)))maximal=false;if(maximal)rows.push_back(m);}
  if(rows.size()!=30)abort();target=(1u<<15)-1;
  for(int i=0;i<10;i++){raw[i]=0;for(int r=0;r<30;r++)if(rows[r]>>i&1)raw[i]|=1u<<r;}
  auto start=chrono::steady_clock::now();int global=99;Circuit winner{};uint64_t restarts=0;
  while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<limit){
    Circuit c=seedCircuit();int current=score(c);restarts++;
    for(int iter=0;iter<30000;iter++){
      if(current<global){global=current;winner=c;double t=chrono::duration<double>(chrono::steady_clock::now()-start).count();save(winner,global,argv[3],seed,t);cout<<"best="<<global<<" trials="<<trials<<" seconds="<<t<<endl;if(global==0)return 0;}
      Circuit next=c;int mutations=ri(15)==0?2:1;
      for(int u=0;u<mutations;u++){int k=ri(19),what=ri(3);if(what==0)next[k].isOr=!next[k].isOr;else if(what==1)next[k].a=ri(10+k);else next[k].b=ri(10+k);}
      int ns=score(next);trials++;double phase=(iter%5000)/5000.0,temperature=1.2*(1-phase)+0.08;
      if(ns<=current||double(rng()>>11)/double(1ull<<53)<exp(double(current-ns)/temperature)){c=next;current=ns;}
    }
  }
  double elapsed=chrono::duration<double>(chrono::steady_clock::now()-start).count();save(winner,global,argv[3],seed,elapsed);
  cout<<"finished best="<<global<<" trials="<<trials<<" restarts="<<restarts<<" seconds="<<elapsed<<endl;return 1;
}
