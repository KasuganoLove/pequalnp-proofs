#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
// Enumerate all assignments, 64 at a time. This is ordinary computation,
// not a Lean certificate or a circuit nonexistence argument.
struct Gate {int op,a,b;};
int main(int argc,char**argv){
 if(argc!=2)return 2;
 std::ifstream f(argv[1]);int n,s,out,m;f>>n>>s>>out>>m;
 if(!f||n<6||n>26||s<0||s>200||out<0||out>n+s)return 3;
 std::vector<std::pair<int,int>> edges(m);
 for(auto &[a,b]:edges){f>>a>>b;if(a<0||b<0||a>=n||b>=n)return 4;}
 std::vector<Gate> gates(s);
 for(int j=0;j<s;++j){auto&g=gates[j];f>>g.op>>g.a>>g.b;if(!f||g.op<0||g.op>2||g.a<0||g.b<0||g.a>n+j||g.b>n+j)return 5;}
 const uint64_t low[6]={0xaaaaaaaaaaaaaaaaULL,0xccccccccccccccccULL,0xf0f0f0f0f0f0f0f0ULL,0xff00ff00ff00ff00ULL,0xffff0000ffff0000ULL,0xffffffff00000000ULL};
 std::vector<uint64_t>w(n+s);uint64_t fp=0,fn=0,first=uint64_t(-1);const uint64_t rows=1ULL<<n;
 for(uint64_t base=0;base<rows;base+=64){
  for(int i=0;i<n;++i)w[i]=i<6?low[i]:((base>>i&1)?~0ULL:0ULL);
  for(int j=0;j<s;++j){auto g=gates[j];uint64_t a=g.a<n+j?w[g.a]:0,b=g.b<n+j?w[g.b]:0;w[n+j]=g.op==2?~0ULL:g.op?(a|b):(a&b);}
  uint64_t expected=0;for(auto [a,b]:edges)expected|=w[a]&w[b];
  uint64_t value=out<n+s?w[out]:0;
  uint64_t badp=value&~expected,badn=expected&~value;
  fp+=__builtin_popcountll(badp);fn+=__builtin_popcountll(badn);
  if((badp|badn)&&first==uint64_t(-1))first=base+__builtin_ctzll(badp|badn);
 }
 std::cout<<"{\"inputs\":"<<n<<",\"gates\":"<<s<<",\"assignments_checked\":"<<rows<<",\"false_positives\":"<<fp<<",\"false_negatives\":"<<fn<<",\"all_correct\":"<<((fp==0&&fn==0)?"true":"false")<<",\"first_error\":";
 if(first==uint64_t(-1))std::cout<<"null";else std::cout<<first;
 std::cout<<",\"lean_verified\":false}\n";
 return fp||fn?1:0;
}
