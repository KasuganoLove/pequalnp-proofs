// Literal ordered algorithm from L9539, represented on all128 assignments.
// NO memoization, normalization, constant/duplicate skipping, or extra pruning.
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <sys/resource.h>
#include <vector>
using U=__uint128_t;
U P;
std::array<U,7> raw;
std::vector<int> negative;
uint64_t nodes=0,seps=0,branches=0,subsets=0;
std::array<uint64_t,12> depth{};
bool timed=false;
std::chrono::steady_clock::time_point start;
double elapsed(){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
bool separates(const std::vector<U>&w){
 seps++;
 for(int q:negative){U t=P;for(U f:w){t&=((f>>q)&1)?f:~f;if(!t)break;}if(t)return false;}
 return true;
}
bool optimized(int n,int extra,const std::vector<U>&w){
 nodes++;depth[9-n]++;
 if((nodes&1023)==0&&elapsed()>=60){timed=true;return false;}
 if((nodes&1048575)==0)std::cerr<<"nodes "<<nodes<<" elapsed "<<elapsed()<<"\n";
 if(w.size()==1&&(w[0]==P||w[0]==~P))return true;
 if(n==0)return false;
 for(size_t i=0;i<w.size();i++)for(size_t j=i+1;j<w.size();j++){
  U a=w[i],b=w[j];std::vector<U>r;for(size_t q=0;q<w.size();q++)if(q!=i&&q!=j)r.push_back(w[q]);
  for(U z:std::array<U,4>{a&b,a|b,a&~b,b&~a}){
   for(int keep:std::array<int,4>{0,1,2,3}){
    int cost=(keep&1?1:0)+(keep&2?1:0);if(cost>extra)continue;
    std::vector<U>v{z};if(keep&1)v.push_back(a);if(keep&2)v.push_back(b);v.insert(v.end(),r.begin(),r.end());
    if(!separates(v))continue;
    branches++;if(optimized(n-1,extra-cost,v))return true;
    if(timed)return false;
   }
  }
 }
 return false;
}
int main(){
 std::vector<std::pair<int,int>>E={{0,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{1,6},{3,6},{5,6}};
 for(int x=0;x<128;x++){
  for(int i=0;i<7;i++)if(x>>i&1)raw[i]|=U(1)<<x;
  bool yes=false;for(auto[a,b]:E)if((x>>a&1)&&(x>>b&1)){yes=true;break;}
  if(yes)P|=U(1)<<x;else negative.push_back(x);
 }
 struct Child{int extra,i,j,op,keep;std::vector<U>w;};
 std::vector<Child>children;
 for(int i=0;i<7;i++)for(int j=i+1;j<7;j++){
  U a=raw[i],b=raw[j];std::vector<U>r;for(int k=0;k<7;k++)if(k!=i&&k!=j)r.push_back(raw[k]);
  std::array<U,4>ops={a&b,a|b,a&~b,b&~a};
  for(int op=0;op<4;op++)for(int keep=0;keep<4;keep++){
   int cost=(keep&1?1:0)+(keep&2?1:0);
   std::vector<U>w{ops[op]};if(keep&1)w.push_back(a);if(keep&2)w.push_back(b);w.insert(w.end(),r.begin(),r.end());
   if(separates(w))children.push_back({3-cost,i,j,op,keep,w});
  }
 }
 if(children.size()!=92)return 3;
 std::cout<<"[";
 for(size_t k=0;k<children.size();k++){
  auto &c=children[k];nodes=seps=branches=0;depth.fill(0);timed=false;start=std::chrono::steady_clock::now();
  bool found=optimized(8,c.extra,c.w);double seconds=elapsed();
  if(k)std::cout<<",";
  std::cout<<"{\"index\":"<<k<<",\"extra\":"<<c.extra<<",\"frontier_size\":"<<c.w.size()
   <<",\"pair\":["<<c.i<<","<<c.j<<"],\"op\":"<<c.op<<",\"keep_mask\":"<<c.keep
   <<",\"outcome\":\""<<(found?"FOUND":timed?"UNKNOWN":"EXHAUSTED_NO_MODEL")<<"\",\"nodes\":"<<nodes
   <<",\"separation_checks\":"<<seps<<",\"descendant_branches\":"<<branches<<",\"elapsed_seconds\":"<<seconds<<",\"depth_nodes\":[";
  for(int d=0;d<=9;d++){if(d)std::cout<<",";std::cout<<depth[d];}std::cout<<"]}";
  if(found||timed){std::cout<<"]\n";return 4;}
 }
 std::cout<<"]\n";
}
