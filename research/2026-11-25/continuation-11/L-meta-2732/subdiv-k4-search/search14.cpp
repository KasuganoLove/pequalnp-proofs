#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
#include <unistd.h>

// Bounded heuristic adapted from the archived local_search.cpp interface.
// Raw inputs0..9, coupled input10=raw4 OR raw5. op0=AND, op1=OR.
// STOP in this working directory requests prompt graceful termination.
// No nonexistence conclusion is supported.
constexpr int N=11, G=14;
struct Gate { uint8_t op,a,b; };
struct State { std::array<Gate,G> gates; uint8_t out; };
struct Eval { int fp,fn; int loss() const { return fp+fn; } };
std::array<uint64_t,N> raw{};
uint64_t positives=0, negatives=0, calls=0;
std::mt19937_64 rng(273220261125ULL);
volatile std::sig_atomic_t stopped=0;
void request_stop(int) { stopped=1; }

Eval evaluate(const State& s) {
  ++calls;
  std::array<uint64_t,N+G> w;
  std::copy(raw.begin(),raw.end(),w.begin());
  for(int k=0;k<G;++k) {
    const auto g=s.gates[k];
    w[N+k]=g.op?(w[g.a]|w[g.b]):(w[g.a]&w[g.b]);
  }
  return {__builtin_popcountll(w[s.out]&negatives),
          __builtin_popcountll(~w[s.out]&positives)};
}

void save(const State& s,const char* name,Eval e) {
  std::ofstream f(name);
  f<<"{\n\"size\":14,\"output\":"<<int(s.out)
   <<",\"training_false_positive\":"<<e.fp<<",\"training_false_negative\":"<<e.fn
   <<",\n\"gates\":[\n";
  for(int i=0;i<G;++i) {
    auto g=s.gates[i];
    f<<"["<<int(g.op)<<","<<int(g.a)<<","<<int(g.b)<<"]"<<(i+1==G?"\n":",\n");
  }
  f<<"]}\n";
}

std::vector<int> live_gates(const State& s) {
  std::array<bool,N+G> live{};live[s.out]=true;
  std::vector<int> result;
  for(int i=G-1;i>=0;--i) if(live[N+i]) {
    result.push_back(i);live[s.gates[i].a]=true;live[s.gates[i].b]=true;
  }
  return result;
}

int main(int argc,char** argv) {
  std::signal(SIGTERM,request_stop);std::signal(SIGINT,request_stop);
  const int budget=argc>1?std::atoi(argv[1]):300;
  std::ofstream("search.pid")<<getpid()<<"\n";
  std::ofstream log("search.log");
  auto say=[&](const std::string& s){std::cout<<s<<std::endl;log<<s<<std::endl;};
  std::ifstream rows("rows.txt");int nr,np;rows>>nr>>np;
  if(!rows||nr>64||nr<=0||np<=0||np>=nr)return 2;
  for(int k=0;k<nr;++k) {
    unsigned m;rows>>m;if(!rows||m>=(1u<<N))return 3;
    uint64_t bit=uint64_t(1)<<k;
    for(int j=0;j<N;++j)if(m&(1u<<j))raw[j]|=bit;
    (k<np?positives:negatives)|=bit;
  }
  std::ifstream in("seeds.txt");int count;in>>count;
  if(!in||count<=0)return 4;
  std::vector<State> seeds;seeds.reserve(count);
  State beststate{};Eval beste{nr,0};
  for(int q=0;q<count;++q) {
    State s;int out;in>>out;if(out<0||out>=N+G)return 5;s.out=out;
    for(int j=0;j<G;++j) {
      int op,a,b;in>>op>>a>>b;
      if(!in||op<0||op>1||a<0||b<0||a>=N+j||b>=N+j)return 6;
      s.gates[j]={uint8_t(op),uint8_t(a),uint8_t(b)};
    }
    Eval e=evaluate(s);
    if(e.loss()<beste.loss()){beststate=s;beste=e;}
    seeds.push_back(s);
  }
  save(beststate,"best-14.json",beste);
  const auto start=std::chrono::steady_clock::now();auto last=start;
  auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  bool found=false;uint64_t edits=0,restarts=0,accepted=0;
  std::vector<State> elite;
  auto consider=[&](const State& s,Eval e) {
    if(e.loss()<beste.loss()) {
      beststate=s;beste=e;save(s,"best-14.json",e);
      say("best fp="+std::to_string(e.fp)+" fn="+std::to_string(e.fn)+" calls="+std::to_string(calls));
    }
    if(e.loss()==0){save(s,"candidate-14.json",e);found=true;return true;}
    if(e.loss()==beste.loss()&&(calls&4095)==0) {
      if(elite.size()<1024)elite.push_back(s);else elite[rng()%elite.size()]=s;
    }
    return false;
  };
  say("START pid="+std::to_string(getpid())+" rows="+std::to_string(nr)+" seeds="+std::to_string(count)+" best="+std::to_string(beste.loss()));
  // Exact one-field neighborhoods of representative near-correct seeds.
  for(int q=0;q<count&&!found&&!stopped;q+=30) {
    if(evaluate(seeds[q]).loss()>4)continue;
    for(int j=0;j<G&&!found&&!stopped;++j)for(int field=0;field<3&&!found;++field) {
      for(int v=0;v<(field==0?2:N+j);++v) {
        State s=seeds[q];
        if(field==0)s.gates[j].op=v;else if(field==1)s.gates[j].a=v;else s.gates[j].b=v;
        ++edits;if(consider(s,evaluate(s)))break;
      }
    }
  }
  say("neighborhood_edits="+std::to_string(edits)+" best="+std::to_string(beste.loss()));
  while(!found&&!stopped&&elapsed()<budget) {
    if(std::ifstream("STOP").good()){stopped=1;break;}
    State cur=(!elite.empty()&&restarts%3==0)?elite[rng()%elite.size()]:
              (restarts%5==0?beststate:seeds[rng()%seeds.size()]);
    Eval ce=evaluate(cur);auto live=live_gates(cur);
    const int fpweight=1+restarts%4,fnweight=1+(restarts/4)%2;
    for(int iter=0;iter<120000&&!found&&!stopped;++iter) {
      State cand=cur;
      unsigned roll=rng()%100;int changes=roll<2?3:roll<14?2:1;
      for(int change=0;change<changes;++change) {
        if(rng()%96==0){cand.out=rng()%(N+G);continue;}
        int j=(!live.empty()&&rng()%5<3)?live[rng()%live.size()]:rng()%G;
        int field=rng()%20;
        if(field==0)cand.gates[j].op^=1;
        else if(field<10)cand.gates[j].a=rng()%(N+j);
        else if(field<19)cand.gates[j].b=rng()%(N+j);
        else cand.gates[j]={uint8_t(rng()%2),uint8_t(rng()%(N+j)),uint8_t(rng()%(N+j))};
        if(cand.gates[j].a>cand.gates[j].b)std::swap(cand.gates[j].a,cand.gates[j].b);
      }
      Eval ne=evaluate(cand);if(consider(cand,ne))break;
      int delta=fpweight*(ce.fp-ne.fp)+fnweight*(ce.fn-ne.fn);
      double phase=double(iter)/120000.0;
      double temp=restarts%4==0?0.05:restarts%4==1?0.65:restarts%4==2?3.0*(1.0-phase)+0.1:1.4*(1.0-phase)+0.1;
      if(delta>=0||std::generate_canonical<double,53>(rng)<std::exp(delta/temp)) {
        cur=cand;ce=ne;++accepted;
        if((accepted&63)==0)live=live_gates(cur);
      }
      if((iter&4095)==0&&elapsed()>=budget)break;
    }
    ++restarts;
    auto now=std::chrono::steady_clock::now();
    if(std::chrono::duration<double>(now-last).count()>=20) {
      say("elapsed="+std::to_string(int(elapsed()))+" evaluations="+std::to_string(calls)+" restarts="+std::to_string(restarts)+" best_fp="+std::to_string(beste.fp)+" best_fn="+std::to_string(beste.fn));last=now;
    }
  }
  save(beststate,"best-14.json",beste);
  std::ofstream summary("run-summary.json");
  summary<<"{\"seed\":273220261125,\"budget_seconds\":"<<budget
    <<",\"elapsed_seconds\":"<<elapsed()<<",\"training_rows\":"<<nr<<",\"seeds\":"<<count
    <<",\"one_field_edits\":"<<edits<<",\"evaluations\":"<<calls<<",\"restarts\":"<<restarts
    <<",\"accepted\":"<<accepted<<",\"candidate_found\":"<<(found?"true":"false")
    <<",\"stopped_by_signal\":"<<(stopped?"true":"false")
    <<",\"best_training_false_positive\":"<<beste.fp<<",\"best_training_false_negative\":"<<beste.fn
    <<",\"nonexistence_proved\":false}\n";
  say("DONE candidate="+std::to_string(found)+" evaluations="+std::to_string(calls)+" best_fp="+std::to_string(beste.fp)+" best_fn="+std::to_string(beste.fn));
}
