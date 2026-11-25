// Exact bounded counterexample search. No global nonexistence claim.
// Coordinates: (00,01,02,03,11,12,13,22,23,33).
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Z {
  long long r=0,i=0;
  Z()=default; Z(long long a):r(a){} Z(long long a,long long b):r(a),i(b){}
  bool operator==(const Z& b)const{return r==b.r&&i==b.i;}
  bool operator!=(const Z& b)const{return !(*this==b);}
  Z operator+(const Z& b)const{return {r+b.r,i+b.i};}
  Z operator-(const Z& b)const{return {r-b.r,i-b.i};}
  Z operator*(const Z& b)const{return {r*b.r-i*b.i,r*b.i+i*b.r};}
  Z& operator+=(const Z& b){r+=b.r;i+=b.i;return *this;}
};
using Vec=array<Z,10>;
const array<pair<int,int>,10> coords={{{0,0},{0,1},{0,2},{0,3},{1,1},{1,2},{1,3},{2,2},{2,3},{3,3}}};
vector<array<int,4>> permutations;
array<array<int,4>,4> indexOf;
auto begun=chrono::steady_clock::now();
double limitSeconds=45;
bool expired(){return chrono::duration<double>(chrono::steady_clock::now()-begun).count()>limitSeconds;}
double elapsed(){return chrono::duration<double>(chrono::steady_clock::now()-begun).count();}
Z sumEntries(const Vec&a){Z s;for(int k=0;k<10;k++)s+=a[k]*Z(coords[k].first==coords[k].second?1:2);return s;}
array<Z,4> rows(const Vec&a){array<Z,4> r{};for(int k=0;k<10;k++){auto[i,j]=coords[k];r[i]+=a[k];if(i!=j)r[j]+=a[k];}return r;}
Z bilinear(const Vec&a,const Vec&b){Z q;auto ar=rows(a),br=rows(b);for(int k=0;k<10;k++)q+=a[k]*b[k]*Z(coords[k].first==coords[k].second?1:2);for(int i=0;i<4;i++)q=q-ar[i]*br[i]*Z(2);return q;}
array<Z,2> cubicQuartic(const Vec&a){Z c,d;for(auto p:permutations){array<Z,4> e;for(int i=0;i<4;i++)e[i]=a[indexOf[i][p[i]]];d+=e[0]*e[1]*e[2]*e[3];for(int omit=0;omit<4;omit++){Z z(1);for(int j=0;j<4;j++)if(j!=omit)z=z*e[j];c+=z;}}return{c,d};}
bool line(const Vec&a){if(sumEntries(a)!=Z(0)||bilinear(a,a)!=Z(0))return false;auto z=cubicQuartic(a);return z[0]==Z(0)&&z[1]==Z(0);}
Vec combine(const Vec&a,const Vec&b,int m=1){Vec c;for(int i=0;i<10;i++)c[i]=a[i]+b[i]*Z(m);return c;}
bool pairOK(const Vec&a,const Vec&b){if(bilinear(a,b)!=Z(0))return false;return line(combine(a,b))&&line(combine(a,b,-1))&&line(combine(a,b,2));}
Z det3(Z a,Z b,Z c,Z d,Z e,Z f,Z g,Z h,Z i){return a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g);}
bool rank3(const Vec&a,const Vec&b,const Vec&c){for(int i=0;i<10;i++)for(int j=i+1;j<10;j++)for(int k=j+1;k<10;k++)if(det3(a[i],a[j],a[k],b[i],b[j],b[k],c[i],c[j],c[k])!=Z(0))return true;return false;}
bool tripleOK(const Vec&a,const Vec&b,const Vec&c){
  Vec abc=combine(combine(a,b),c);
  return line(abc)&&line(combine(abc,a))&&line(combine(abc,b))&&line(combine(abc,c));
}
void emitVec(ostream&o,const Vec&a){o<<'[';for(int i=0;i<10;i++){if(i)o<<',';o<<'['<<a[i].r<<','<<a[i].i<<']';}o<<']';}
int main(int argc,char**argv){
  if(argc<5){cerr<<"usage: search real|gaussian support seconds output.json\n";return 2;}
  bool gaussian=string(argv[1])=="gaussian";int maxSupport=atoi(argv[2]);limitSeconds=atof(argv[3]);string outfile=argv[4];
  for(int k=0;k<10;k++){auto[i,j]=coords[k];indexOf[i][j]=indexOf[j][i]=k;}
  array<int,4> p={0,1,2,3};do{permutations.push_back(p);}while(next_permutation(p.begin(),p.end()));
  vector<Z> alphabet={Z(0),Z(1),Z(-1)};if(gaussian){alphabet.push_back({0,1});alphabet.push_back({0,-1});}
  vector<Vec> vs;uint64_t enumerated=0,pairs=0,compatible=0,triangles=0,independent=0;bool enumerationComplete=true,pairComplete=true,tripleComplete=true,found=false;array<Vec,3>witness{};
  Vec work{};
  auto rec=[&](auto&&self,int at,int support,bool hasFirst)->void{
    if(support>maxSupport)return;
    if((enumerated&65535)==0&&expired()){enumerationComplete=false;return;}
    if(at==10){enumerated++;if(hasFirst&&line(work))vs.push_back(work);return;}
    for(auto z:alphabet){if(!hasFirst&&z!=Z(0)&&z!=Z(1))continue;work[at]=z;self(self,at+1,support+(z!=Z(0)),hasFirst||z!=Z(0));if(!enumerationComplete)return;}
  };rec(rec,0,0,false);
  cout<<"directions="<<vs.size()<<" vectors="<<enumerated<<" enumeration_complete="<<enumerationComplete<<" seconds="<<elapsed()<<endl;
  vector<vector<unsigned char>> adj(vs.size(),vector<unsigned char>(vs.size(),0));
  for(size_t i=0;i<vs.size()&&pairComplete;i++)for(size_t j=i+1;j<vs.size();j++){
    if((pairs&4095)==0&&expired()){pairComplete=false;break;}pairs++;
    if(pairOK(vs[i],vs[j])){adj[i][j]=adj[j][i]=1;compatible++;}
  }
  cout<<"pairs="<<pairs<<" compatible="<<compatible<<" pairs_complete="<<pairComplete<<" seconds="<<elapsed()<<endl;
  if(pairComplete)for(size_t i=0;i<vs.size()&&!found&&tripleComplete;i++)for(size_t j=i+1;j<vs.size()&&!found&&tripleComplete;j++)if(adj[i][j])for(size_t k=j+1;k<vs.size();k++)if(adj[i][k]&&adj[j][k]){
    if((triangles&1023)==0&&expired()){tripleComplete=false;break;}triangles++;if(!rank3(vs[i],vs[j],vs[k]))continue;independent++;
    if(tripleOK(vs[i],vs[j],vs[k])){found=true;witness={vs[i],vs[j],vs[k]};break;}
  }
  ofstream out(outfile);out<<"{\"mode\":\""<<(gaussian?"gaussian":"real")<<"\",\"support_cap\":"<<maxSupport<<",\"seconds\":"<<elapsed()<<",\"enumerated_canonical_vectors\":"<<enumerated<<",\"line_directions\":"<<vs.size()<<",\"enumeration_complete\":"<<(enumerationComplete?"true":"false")<<",\"pairs_checked\":"<<pairs<<",\"compatible_pairs\":"<<compatible<<",\"pair_enumeration_complete\":"<<(pairComplete?"true":"false")<<",\"compatible_triples\":"<<triangles<<",\"independent_triples\":"<<independent<<",\"triple_enumeration_complete\":"<<(tripleComplete&&pairComplete?"true":"false")<<",\"witness_found\":"<<(found?"true":"false")<<",\"witness\":";
  if(found){out<<'[';for(int i=0;i<3;i++){if(i)out<<',';emitVec(out,witness[i]);}out<<']';}else out<<"null";
  out<<",\"scope\":\"Only the specified finite coefficient family; no global nonexistence conclusion.\"}\n";
  cout<<"triangles="<<triangles<<" independent="<<independent<<" found="<<found<<" seconds="<<elapsed()<<endl;
  return found?0:1;
}
