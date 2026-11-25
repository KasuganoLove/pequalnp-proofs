#include <array>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

// A bounded heuristic search, never a proof of a lower bound. All 286 rows are
// checked together, and every proposed input index is strictly earlier.
using Bits = std::array<uint64_t,5>;
struct Gate { int op,a,b; };
struct State { std::array<Gate,62> gs; int pa,pb; };
struct Eval { int fp,fn,score; };
std::array<Bits,26> raw{};
Bits target{}, mask{};
std::vector<State> seeds;
uint64_t calls=0;
std::mt19937_64 rng(234320261125ULL);

Eval eval(const State &s, int positive_weight=4) {
    ++calls;
    std::array<Bits,89> w;
    for(int i=0;i<26;i++) w[i]=raw[i];
    for(int k=0;k<5;k++) w[26][k]=raw[s.pa][k]|raw[s.pb][k];
    for(int i=0;i<62;i++) {
        const auto &g=s.gs[i];
        for(int k=0;k<5;k++) w[27+i][k]=g.op ? (w[g.a][k]|w[g.b][k]) : (w[g.a][k]&w[g.b][k]);
    }
    int fp=0,fn=0;
    for(int k=0;k<5;k++) {
        fp+=__builtin_popcountll(w[88][k]&~target[k]&mask[k]);
        fn+=__builtin_popcountll(~w[88][k]&target[k]);
    }
    return {fp,fn,fp+positive_weight*fn};
}

void save(const State &s, const char *file, Eval e) {
    std::ofstream f(file);
    f << "{\n  \"free_or\": ["<<s.pa<<","<<s.pb<<"],\n  \"output\": 88,\n  \"size\": 62,\n  \"false_positive\": "<<e.fp<<",\n  \"false_negative\": "<<e.fn<<",\n  \"gates\": [\n";
    for(int i=0;i<62;i++){auto g=s.gs[i];f<<"    ["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(i==61?"\n":",\n");}
    f << "  ]\n}\n";
}

bool check(const State &s, Eval e) {
    if(e.fp==0 && e.fn==0){save(s,"witness-62.json",e);std::cout<<"WITNESS after "<<calls<<" evaluations\n"<<std::flush;return true;}
    return false;
}

int main(int argc,char **argv) {
    int seconds=argc>1?std::atoi(argv[1]):120;
    std::ifstream in("search-input.txt");int rows,ns;in>>rows>>ns;
    if(rows!=286 || ns<=0) return 2;
    for(int r=0;r<rows;r++){uint32_t x;in>>x;mask[r/64]|=uint64_t(1)<<(r%64);if(r<52)target[r/64]|=uint64_t(1)<<(r%64);for(int k=0;k<26;k++)if((x>>k)&1)raw[k][r/64]|=uint64_t(1)<<(r%64);}
    for(int t=0;t<ns;t++){State s;in>>s.pa>>s.pb;for(auto &g:s.gs)in>>g.op>>g.a>>g.b;auto e=eval(s);if(e.fp!=0||e.fn!=1)return 3;seeds.push_back(s);}
    auto start=std::chrono::steady_clock::now();
    uint64_t one_edit=0;
    // Exhaust every one-field edit of every structured seed first.
    for(auto base:seeds)for(int j=0;j<62;j++)for(int field=0;field<3;field++){
        int top=field==0?2:27+j;
        for(int v=0;v<top;v++){
            State s=base;
            if(field==0)s.gs[j].op=v;else if(field==1)s.gs[j].a=v;else s.gs[j].b=v;
            if(check(s,eval(s)))return 0;
            ++one_edit;
        }
    }
    std::cout<<"one-field neighborhood exhausted: "<<one_edit<<" candidates, no witness\n"<<std::flush;
    int best=4,bfp=0,bfn=1;uint64_t accepted=0,restarts=0;
    State beststate=seeds[0];
    auto last=start;
    while(true){
        auto now=std::chrono::steady_clock::now();
        if(std::chrono::duration<double>(now-start).count()>=seconds)break;
        State cur=seeds[rng()%seeds.size()];
        int weight=1+(restarts%5);
        Eval ce=eval(cur,weight);
        for(int iter=0;iter<12000;iter++){
            State cand=cur;
            int changes=(rng()%10==0)?2:1;
            for(int m=0;m<changes;m++){
                int j=rng()%62;
                int f=rng()%12;
                if(f==0)cand.gs[j].op^=1;
                else if(f<=5)cand.gs[j].a=rng()%(27+j);
                else if(f<=10)cand.gs[j].b=rng()%(27+j);
                else {cand.gs[j].a=rng()%(27+j);cand.gs[j].b=rng()%(27+j);}
                if(cand.gs[j].a>cand.gs[j].b)std::swap(cand.gs[j].a,cand.gs[j].b);
            }
            Eval ne=eval(cand,weight);
            if(check(cand,ne))return 0;
            int normal=ne.fp+4*ne.fn;
            if(normal<best){best=normal;bfp=ne.fp;bfn=ne.fn;beststate=cand;save(cand,"best-62.json",ne);std::cout<<"best: fp="<<bfp<<" fn="<<bfn<<" evals="<<calls<<"\n"<<std::flush;}
            double temp=(iter<9000?0.65:0.12)+0.25*(restarts%4);
            if(ne.score<=ce.score || std::generate_canonical<double,53>(rng)<std::exp((ce.score-ne.score)/temp)){
                cur=cand;ce=ne;++accepted;
            }
            if((iter&1023)==0){
                now=std::chrono::steady_clock::now();
                if(std::chrono::duration<double>(now-start).count()>=seconds)break;
            }
        }
        ++restarts;
        now=std::chrono::steady_clock::now();
        if(std::chrono::duration<double>(now-last).count()>=15){
            std::cout<<"elapsed="<<int(std::chrono::duration<double>(now-start).count())<<" evals="<<calls<<" restarts="<<restarts<<" best_fp="<<bfp<<" best_fn="<<bfn<<"\n"<<std::flush;last=now;
        }
    }
    save(beststate,"best-62.json",eval(beststate));
    std::cout<<"DONE no witness; evaluations="<<calls<<" accepted="<<accepted<<" restarts="<<restarts<<" best_fp="<<bfp<<" best_fn="<<bfn<<"\n";
}
