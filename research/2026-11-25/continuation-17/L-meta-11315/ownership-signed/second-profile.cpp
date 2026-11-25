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
U parseHex(std::string s){U v=0;for(size_t i=(s.rfind("0x",0)==0?2:0);i<s.size();i++){char c=s[i];unsigned d=c>='0'&&c<='9'?c-'0':c>='a'&&c<='f'?c-'a'+10:99;if(d>15)throw 1;v=(v<<4)|d;}return v;}
int main(){
 std::vector<std::pair<int,int>>E={{0,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{1,6},{3,6},{5,6}};
 for(int x=0;x<128;x++){bool yes=false;for(auto[a,b]:E)if((x>>a&1)&&(x>>b&1)){yes=true;break;}if(yes)P|=U(1)<<x;else negative.push_back(x);}
 int parent,index,n,extra,count;
 while(std::cin>>parent>>index>>n>>extra>>count){
  std::vector<U>w;for(int j=0;j<count;j++){std::string z;std::cin>>z;w.push_back(parseHex(z));}
  nodes=seps=branches=0;depth.fill(0);timed=false;start=std::chrono::steady_clock::now();
  bool found=optimized(n,extra,w);
  std::cout<<"{\"parent\":"<<parent<<",\"index\":"<<index<<",\"nodes\":"<<nodes
   <<",\"separation_checks\":"<<seps<<",\"elapsed_seconds\":"<<elapsed()
   <<",\"outcome\":\""<<(found?"FOUND":timed?"UNKNOWN":"EXHAUSTED_NO_MODEL")<<"\"}\n";
  if(found||timed)return 4;
 }
}
