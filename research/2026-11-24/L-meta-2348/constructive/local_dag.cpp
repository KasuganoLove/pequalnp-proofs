#include <array>
#include <cstdint>
#include <iostream>
using U = uint32_t;
std::array<U, 10> wires{};
struct G { int op,a,b; };
std::array<G,6> gates{};
U target;
uint64_t candidates=0;
U gateAnd(U a,U b){
 U ma=a&65535u,mb=b&65535u;
 U d1=(((ma>>1)&1u)&((b>>16)&1u))|(((a>>16)&1u)&((mb>>1)&1u));
 U d2=(((ma>>2)&1u)&((b>>17)&1u))|(((a>>17)&1u)&((mb>>2)&1u));
 return (ma&mb)|(d1<<16)|(d2<<17);
}
bool search(int depth,int limit){
 int count=4+depth;
 for(int a=0;a<count;++a)for(int b=a+1;b<count;++b)for(int op=0;op<2;++op){
  U z=op? (wires[a]|wires[b]) : gateAnd(wires[a],wires[b]);
  ++candidates;
  gates[depth]={op,a,b};wires[count]=z;
  if(z==target){
   std::cout<<"found gates="<<(depth+1)<<" checked="<<candidates<<"\n";
   for(int i=0;i<=depth;++i)std::cout<<(4+i)<<" "<<(gates[i].op?"OR":"AND")<<" "<<gates[i].a<<" "<<gates[i].b<<"\n";
   return true;
  }
  if(depth+1<limit && search(depth+1,limit))return true;
 }
 return false;
}
int main(){
 for(int i=0;i<4;++i){for(int a=0;a<16;++a)wires[i]|=U((a>>i)&1u)<<a;}
 wires[0]|=1u<<17;wires[1]|=1u<<16;
 U p=wires[0]&65535u,q=wires[1]&65535u,P=wires[2]&65535u,Q=wires[3]&65535u;
 target=(p&q)|(p&Q)|(q&P);
 bool found=search(0,5);
 if(!found)std::cout<<"No circuit with at most 5 gates; checked "<<candidates<<" ordered partial circuits (4 metavariables, binary distinct inputs, AND/OR).\n";
}
