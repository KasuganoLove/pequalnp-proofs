// Literal L9539 signed live-wire recursion on selected samples for L11315.
// No canonicalization, memoization, or constant/duplicate skipping.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <string>
#include <sys/resource.h>
#include <vector>
using U=uint64_t;
U FULL, P;
U complement(U x){return FULL^x;}
std::array<U,7> raw;
std::vector<int> negatives;
struct Step{U a,b,z;int op;};
std::vector<Step> path,found;
U found_output=0;
uint64_t nodes=0,seps=0,branches=0,subsets=0;
std::array<uint64_t,10> depth{};
bool timed=false;
std::chrono::steady_clock::time_point start;
double elapsed(){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
bool separates(const std::vector<U>&w){
 seps++;
 for(int q:negatives){U t=P;for(U f:w){t&=((f>>q)&1)?f:complement(f);if(!t)break;}if(t)return false;}
 return true;
}
bool optimized(int n,int extra,const std::vector<U>&w){
 nodes++;depth[9-n]++;
 if((nodes&1023)==0&&elapsed()>=60){timed=true;return false;}
 if((nodes&1048575)==0)std::cerr<<"nodes "<<nodes<<" elapsed "<<elapsed()<<"\n";
 if(w.size()==1&&(w[0]==P||w[0]==complement(P))){found=path;found_output=w[0];return true;}
 if(n==0)return false;
 for(size_t i=0;i<w.size();i++)for(size_t j=i+1;j<w.size();j++){
  U a=w[i],b=w[j];std::vector<U>r;for(size_t q=0;q<w.size();q++)if(q!=i&&q!=j)r.push_back(w[q]);
  std::array<U,4>ops={a&b,a|b,a&complement(b),b&complement(a)};
  for(int op=0;op<4;op++){
   U z=ops[op];
   for(int keep:std::array<int,4>{0,1,2,3}){
    int cost=(keep&1?1:0)+(keep&2?1:0);if(cost>extra)continue;
    std::vector<U>v{z};if(keep&1)v.push_back(a);if(keep&2)v.push_back(b);v.insert(v.end(),r.begin(),r.end());
    if(!separates(v))continue;
    branches++;path.push_back({a,b,z,op});if(optimized(n-1,extra-cost,v))return true;
    path.pop_back();if(timed)return false;
   }
  }
 }
 return false;
}
int main(int argc,char**argv){
 std::string mode=argc>1?argv[1]:"edges_all";
 if(mode!="edges_all"&&mode!="edges_maximal")return 2;
 std::vector<std::pair<int,int>>E={{0,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{1,6},{3,6},{5,6}};
 auto target=[&](int x){for(auto[a,b]:E)if((x>>a&1)&&(x>>b&1))return true;return false;};
 std::vector<int>ps,ns,samples;
 for(auto[a,b]:E)ps.push_back((1<<a)|(1<<b));std::sort(ps.begin(),ps.end());
 for(int x=0;x<128;x++)if(!target(x)){
  bool maximal=true;for(int i=0;i<7;i++)if(!(x>>i&1)&&!target(x|(1<<i)))maximal=false;
  if(mode=="edges_all"||maximal)ns.push_back(x);
 }
 samples=ps;samples.insert(samples.end(),ns.begin(),ns.end());
 if(samples.size()>=64)return 3;
 FULL=(U(1)<<samples.size())-1;P=(U(1)<<ps.size())-1;
 for(size_t c=0;c<samples.size();c++){
  for(int i=0;i<7;i++)if(samples[c]>>i&1)raw[i]|=U(1)<<c;
  if(c>=ps.size())negatives.push_back(c);
 }
 // Check all initial sublists before starting the bounded recursive search.
 std::vector<unsigned>initial;
 for(unsigned mask=0;mask<128;mask++){
  std::vector<U>w;for(int i=0;i<7;i++)if(mask>>i&1)w.push_back(raw[i]);
  if(separates(w))initial.push_back(mask);
 }
 seps=0;start=std::chrono::steady_clock::now();bool success=false;
 for(unsigned mask:initial){
  std::vector<U>w;for(int i=0;i<7;i++)if(mask>>i&1)w.push_back(raw[i]);
  if(w.size()<=10){subsets++;success=optimized(9,10-w.size(),w);if(success||timed)break;}
 }
 struct rusage ru{};getrusage(RUSAGE_SELF,&ru);
 std::cout<<"{\"task\":11315,\"mode\":\""<<mode<<"\",\"binary_budget\":9,\"seconds_cap\":60,\"elapsed_seconds\":"<<elapsed()
 <<",\"outcome\":\""<<(success?"FOUND":timed?"UNKNOWN":"EXHAUSTED_NO_MODEL")<<"\",\"nodes\":"<<nodes<<",\"separation_checks\":"<<seps
 <<",\"branches\":"<<branches<<",\"initial_sublists_visited\":"<<subsets<<",\"maximum_resident_set_size_kib\":"<<ru.ru_maxrss<<",\"depth_nodes\":[";
 for(int i=0;i<=9;i++){if(i)std::cout<<",";std::cout<<depth[i];}
 std::cout<<"],\"sample_count\":"<<samples.size()<<",\"positive_count\":"<<ps.size()<<",\"negative_count\":"<<ns.size()<<",\"all_separating_initial_sublists\":[";
 for(size_t i=0;i<initial.size();i++){if(i)std::cout<<",";std::cout<<initial[i];}
 std::cout<<"],\"found_output\":"<<found_output<<",\"steps\":[";
 for(size_t i=0;i<found.size();i++){if(i)std::cout<<",";auto s=found[i];std::cout<<"{\"a\":"<<s.a<<",\"b\":"<<s.b<<",\"z\":"<<s.z<<",\"op\":"<<s.op<<"}";}
 std::cout<<"],\"memoization\":false,\"complement_canonicalization\":false,\"skip_constants_or_duplicates\":false,\"formal_certificate\":false,\"sample_domain_only\":true}\n";
}
