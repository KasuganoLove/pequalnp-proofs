// Exploratory signed live-wire search, derived from the semantics of L9539.
// Free complementation is allowed; this is NOT an at-most-one-NOT search.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using U=__uint128_t;
const U FULL=(U(1)<<29)-1;
U complement(U x){return FULL^x;}
U canonical(U x){return std::min(x,complement(x));}
std::string hex(U x){std::ostringstream s;s<<std::hex<<std::setw(16)<<std::setfill('0')<<(uint64_t)(x>>64)<<std::setw(16)<<(uint64_t)x;return s.str();}
struct Key{int n;std::vector<U>w;bool operator==(const Key&b)const{return n==b.n&&w==b.w;}};
struct Hash{size_t operator()(const Key&k)const{size_t h=k.n;for(U w:k.w){h^=(uint64_t)w+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);h^=(uint64_t)(w>>64)+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);}return h;}};
struct Step{U a,b,z;int op;bool inv;};
std::unordered_set<Key,Hash> failed;
std::vector<int> negatives;
std::vector<Step> path,found;
std::array<U,7> raw;
U positive,goal;
uint64_t nodes=0,checks=0,hits=0,branches=0;
std::array<uint64_t,16> depthnodes{};
bool timeout=false;int initial_budget;double seconds;
std::chrono::steady_clock::time_point start;
bool separates(const std::vector<U>&w){
 checks++;
 for(int n:negatives){
  U matching=positive;
  for(U x:w){matching&=((x>>n)&1)?x:complement(x);if(!matching)break;}
  if(matching)return false;
 }
 return true;
}
bool dfs(int left,const std::vector<U>&w){
 nodes++;depthnodes[initial_budget-left]++;
 if((nodes&1023)==0 && std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=seconds){timeout=true;return false;}
 if(std::binary_search(w.begin(),w.end(),goal)){found=path;return true;}
 if(!left || w.size()<2)return false;
 if(w.size()>(size_t)left+1)return false;
 Key key{left,w};if(failed.contains(key)){hits++;return false;}
 int extra=left+1-(int)w.size();
 for(size_t i=0;i<w.size();i++)for(size_t j=i+1;j<w.size();j++){
  U a=w[i],b=w[j];std::array<U,4>op={a&b,a|b,a&complement(b),b&complement(a)};
  for(int o=0;o<4;o++){
   U z=canonical(op[o]);
   if(z==0 || std::binary_search(w.begin(),w.end(),z))continue;
   for(int keep=0;keep<4;keep++){
    if(std::popcount((unsigned)keep)>extra)continue;
    std::vector<U>v;v.reserve(w.size()+1);v.push_back(z);
    for(size_t t=0;t<w.size();t++)if((t!=i&&t!=j)||(t==i&&(keep&1))||(t==j&&(keep&2)))v.push_back(w[t]);
    if(!separates(v))continue;
    std::sort(v.begin(),v.end());branches++;
    path.push_back({a,b,z,o,z!=op[o]});
    if(dfs(left-1,v))return true;
    path.pop_back();if(timeout)return false;
   }
  }
 }
 // Bounded cache; dropping new failed entries only repeats work, never prunes extra states.
 if(failed.size()<600000)failed.insert(std::move(key));
 return false;
}
int main(int argc,char**argv){
 int id=argc>1?std::stoi(argv[1]):10487;
 initial_budget=argc>2?std::stoi(argv[2]):10;seconds=argc>3?std::stod(argv[3]):60;
 std::vector<std::pair<int,int>>edges;
 if(id==10487)edges={{0,2},{1,3},{0,4},{1,4},{2,4},{3,4},{0,5},{1,5},{2,5},{3,5},{0,6},{1,6},{2,6},{3,6},{4,6}};
  else return 2;
 std::vector<int> positive_samples,negative_samples,samples;
 for(auto[a,b]:edges)positive_samples.push_back((1<<a)|(1<<b));
 std::sort(positive_samples.begin(),positive_samples.end());
 if(std::adjacent_find(positive_samples.begin(),positive_samples.end())!=positive_samples.end())return 4;
 for(int x=0;x<128;x++){
  bool yes=false;for(auto[a,b]:edges)if((x>>a&1)&&(x>>b&1)){yes=true;break;}
  if(!yes)negative_samples.push_back(x);
 }
 if(positive_samples.size()!=15||negative_samples.size()!=14)return 5;
 samples=positive_samples;samples.insert(samples.end(),negative_samples.begin(),negative_samples.end());
 for(size_t column=0;column<samples.size();column++){
  int x=samples[column];
  for(int i=0;i<7;i++)if(x>>i&1)raw[i]|=U(1)<<column;
  if(column<positive_samples.size())positive|=U(1)<<column;else negatives.push_back(column);
 }
 goal=canonical(positive);std::vector<U>w;for(U x:raw)w.push_back(canonical(x));std::sort(w.begin(),w.end());
 // Sample-domain essentiality: a positive and negative differ only at this raw bit.
 for(int i=0;i<7;i++){
  bool essential=false;
  for(int a:positive_samples)for(int b:negative_samples)if((a^b)==(1<<i))essential=true;
  if(!essential)return 3;
 }
 // Independently check every raw-input sublist: only the complete one separates.
 for(unsigned m=0;m<128;m++){
  std::vector<U>v;for(int i=0;i<7;i++)if(m>>i&1)v.push_back(raw[i]);
  if(separates(v)!=(m==127))return 6;
 }
 checks=0;
 failed.reserve(600000);start=std::chrono::steady_clock::now();bool success=dfs(initial_budget,w);
 double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 std::cout<<"{\"task\":"<<id<<",\"binary_budget\":"<<initial_budget<<",\"seconds_cap\":"<<seconds<<",\"elapsed_seconds\":"<<elapsed
 <<",\"outcome\":\""<<(success?"FOUND":timeout?"UNKNOWN":"EXHAUSTED_NO_MODEL")<<"\",\"nodes\":"<<nodes<<",\"separation_checks\":"<<checks
 <<",\"surviving_branches\":"<<branches<<",\"memo_hits\":"<<hits<<",\"cached_failed_states\":"<<failed.size()<<",\"positive_assignments\":"<<(29-negatives.size())
 <<",\"negative_assignments\":"<<negatives.size()<<",\"positive_mask\":\""<<hex(positive)<<"\",\"goal_canonical\":\""<<hex(goal)<<"\",\"depth_nodes\":[";
 for(int i=0;i<=initial_budget;i++){if(i)std::cout<<",";std::cout<<depthnodes[i];}
 std::cout<<"],\"steps\":[";for(size_t i=0;i<found.size();i++){if(i)std::cout<<",";auto s=found[i];std::cout<<"{\"a\":\""<<hex(s.a)<<"\",\"b\":\""<<hex(s.b)<<"\",\"z\":\""<<hex(s.z)<<"\",\"op\":"<<s.op<<",\"invert_output\":"<<(s.inv?"true":"false")<<"}";}
 std::cout<<"],\"scope\":\"Exploratory 29-column partial-function signed binary search, arbitrary free NOT; no formal UNSAT certificate\"}\n";
}
