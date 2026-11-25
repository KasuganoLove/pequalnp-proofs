#include <array>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

// Heuristic only. Each evaluation covers every one of the 1024 assignments.
using Bits=std::array<uint64_t,16>;
struct Gate{int op,a,b;};
struct State{std::array<Gate,18> gs;int out;};
struct Eval{int fp,fn;};
std::array<Bits,11> raw{};Bits target{};
uint64_t calls=0;
std::mt19937_64 rng(188420261125ULL);

Eval evaluate(const State&s){
    ++calls;std::array<Bits,29>w;
    for(int i=0;i<11;i++)w[i]=raw[i];
    for(int i=0;i<18;i++){
        const auto&g=s.gs[i];
        for(int k=0;k<16;k++)w[11+i][k]=g.op==0?(w[g.a][k]&w[g.b][k]):g.op==1?(w[g.a][k]|w[g.b][k]):~w[g.a][k];
    }
    int fp=0,fn=0;
    for(int k=0;k<16;k++){fp+=__builtin_popcountll(w[s.out][k]&~target[k]);fn+=__builtin_popcountll(~w[s.out][k]&target[k]);}
    return {fp,fn};
}

void save(const State&s,const char*path,Eval e){
    std::ofstream f(path);
    f<<"{\n\"size\":18,\"output\":"<<s.out<<",\"false_positive\":"<<e.fp<<",\"false_negative\":"<<e.fn<<",\n\"gates\":[\n";
    for(int i=0;i<18;i++){auto g=s.gs[i];f<<"["<<g.op<<","<<g.a<<","<<g.b<<"]"<<(i==17?"\n":",\n");}
    f<<"]}\n";
}

int main(int argc,char**argv){
    const int seconds=argc>1?std::atoi(argv[1]):180;
    const std::array<std::pair<int,int>,15> edges={{{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{4,9},{5,7},{7,9},{9,6},{6,8},{8,5}}};
    for(int x=0;x<1024;x++){
        auto bit=uint64_t(1)<<(x%64);
        for(int i=0;i<10;i++)if((x>>i)&1)raw[i][x/64]|=bit;
        if(!(x&1))raw[10][x/64]|=bit;
        for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1)){target[x/64]|=bit;break;}
    }
    std::ifstream in("seeds.txt");int ns;in>>ns;if(ns<=0)return 2;
    std::vector<State>seeds;
    int best=1025;State beststate;Eval beste{};
    for(int q=0;q<ns;q++){State s;in>>s.out;for(int j=0;j<18;j++){auto&g=s.gs[j];in>>g.op>>g.a>>g.b;if(g.a>=11+j||g.b>=11+j||g.op<0||g.op>2)return 3;}auto e=evaluate(s);if(e.fp+e.fn<best){best=e.fp+e.fn;beststate=s;beste=e;}seeds.push_back(s);}
    save(beststate,"best-18.json",beste);
    auto start=std::chrono::steady_clock::now(),last=start;
    auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
    uint64_t edited=0,restarts=0,accepted=0;
    bool found=false;
    auto consider=[&](const State&s,Eval e){
        if(e.fp+e.fn<best){best=e.fp+e.fn;beststate=s;beste=e;save(s,"best-18.json",e);std::cout<<"best fp="<<e.fp<<" fn="<<e.fn<<" calls="<<calls<<"\n"<<std::flush;}
        if(e.fp+e.fn==0){save(s,"witness-18.json",e);found=true;return true;}return false;
    };
    // Exhaust one-field neighborhoods of one representative per cover/orientation.
    for(int q=0;q<ns && !found;q+=16)for(int j=0;j<18 && !found;j++)for(int field=0;field<3 && !found;field++){
        for(int v=0;v<(field==0?3:11+j);v++){
            State s=seeds[q];if(field==0)s.gs[j].op=v;else if(field==1)s.gs[j].a=v;else s.gs[j].b=v;
            ++edited;if(consider(s,evaluate(s)))break;
        }
    }
    std::cout<<"initial one-field edits="<<edited<<" best="<<best<<"\n"<<std::flush;
    while(!found&&elapsed()<seconds){
        State cur=(restarts%5==0)?beststate:seeds[rng()%seeds.size()];
        int fpweight=1+(restarts%5);Eval ce=evaluate(cur);
        for(int iter=0;iter<24000;iter++){
            State cand=cur;int changes=rng()%12==0?2:1;
            for(int m=0;m<changes;m++){
                if(rng()%48==0){cand.out=rng()%29;continue;}
                int j=rng()%18,f=rng()%16;
                if(f==0)cand.gs[j].op=rng()%3;
                else if(f<=7)cand.gs[j].a=rng()%(11+j);
                else if(f<=14)cand.gs[j].b=rng()%(11+j);
                else {cand.gs[j].op=rng()%3;cand.gs[j].a=rng()%(11+j);cand.gs[j].b=rng()%(11+j);}
                if(cand.gs[j].op<2&&cand.gs[j].a>cand.gs[j].b)std::swap(cand.gs[j].a,cand.gs[j].b);
            }
            Eval ne=evaluate(cand);if(consider(cand,ne))break;
            int delta=fpweight*(ce.fp-ne.fp)+ce.fn-ne.fn;
            double temp=(iter<16000?2.2:0.35)+0.8*(restarts%4);
            if(delta>=0||std::generate_canonical<double,53>(rng)<std::exp(delta/temp)){cur=cand;ce=ne;++accepted;}
            if((iter&2047)==0&&elapsed()>=seconds)break;
        }
        ++restarts;
        auto now=std::chrono::steady_clock::now();
        if(std::chrono::duration<double>(now-last).count()>=15){std::cout<<"elapsed="<<int(elapsed())<<" calls="<<calls<<" restarts="<<restarts<<" best_fp="<<beste.fp<<" best_fn="<<beste.fn<<"\n"<<std::flush;last=now;}
    }
    save(beststate,"best-18.json",beste);
    std::ofstream f("run-summary.json");
    f<<"{\"seed\":188420261125,\"budget_seconds\":"<<seconds<<",\"elapsed_seconds\":"<<elapsed()<<",\"seeds\":"<<ns<<",\"one_field_edits\":"<<edited<<",\"evaluations\":"<<calls<<",\"restarts\":"<<restarts<<",\"accepted\":"<<accepted<<",\"witness\":"<<(found?"true":"false")<<",\"best_false_positive\":"<<beste.fp<<",\"best_false_negative\":"<<beste.fn<<"}\n";
    std::cout<<"DONE witness="<<found<<" calls="<<calls<<" best_fp="<<beste.fp<<" best_fn="<<beste.fn<<"\n";
}
