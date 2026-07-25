#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <mutex>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>
#include <omp.h>
using namespace std;

namespace {
constexpr int N=16, H=8, TARGET=33;
constexpr uint16_t ALL=0xffffu;
constexpr int UNITS[8]={1,3,5,7,9,11,13,15};
using Profile=array<int,6>; // r,c,d0,d1,a0,a1

vector<uint16_t> masks_by_size[17];
vector<uint16_t> masks_by_parity[9][9];
vector<uint16_t> necklaces[17];
uint16_t translation_canon_table[1<<N];
uint16_t scale_canon_table[8][1<<N];

inline uint16_t transform_mask(uint16_t m,int u,int shift=0){
    uint16_t out=0;
    while(m){int x=__builtin_ctz((unsigned)m);m &= uint16_t(m-1);out|=uint16_t(1u<<((u*x+shift)&15));}
    return out;
}
inline uint16_t rotate16(uint16_t m,int s){
    if(!s)return m;
    return uint16_t((uint32_t(m)<<s)|(uint32_t(m)>>(16-s)));
}
inline int parity_pop(uint16_t m,int p){
    return __builtin_popcount((unsigned)(m & (p?0xaaaau:0x5555u)));
}
void initialize_masks(){
    for(int m=0;m<(1<<N);++m){
        uint16_t best=0xffff;
        for(int s=0;s<N;s++)best=min(best,rotate16((uint16_t)m,s));
        translation_canon_table[m]=best;
        int k=__builtin_popcount((unsigned)m);
        masks_by_size[k].push_back((uint16_t)m);
        masks_by_parity[parity_pop((uint16_t)m,0)][parity_pop((uint16_t)m,1)].push_back((uint16_t)m);
    }
    for(int ui=0;ui<8;ui++)for(int m=0;m<(1<<N);m++){
        scale_canon_table[ui][m]=translation_canon_table[transform_mask((uint16_t)m,UNITS[ui])];
    }
    for(int k=0;k<=N;k++){
        unordered_set<uint16_t> seen;
        seen.reserve(masks_by_size[k].size()*2+1);
        for(uint16_t m:masks_by_size[k])seen.insert(translation_canon_table[m]);
        necklaces[k].assign(seen.begin(),seen.end());
        sort(necklaces[k].begin(),necklaces[k].end());
    }
}
int unit_index(int u){for(int i=0;i<8;i++)if(UNITS[i]==u)return i;abort();}

struct PairKey{int r,c;bool relative_sign;bool operator<(const PairKey&o)const{return tie(r,c,relative_sign)<tie(o.r,o.c,o.relative_sign);}};
vector<pair<uint16_t,uint16_t>> generate_pair_representatives(int r,int c,bool relative_sign){
    assert(r<=c); const bool transpose=(r==c);
    unordered_set<uint32_t> visited;
    visited.reserve(necklaces[r].size()*necklaces[c].size()*2+1);
    vector<pair<uint16_t,uint16_t>> reps;
    for(uint16_t R:necklaces[r])for(uint16_t C:necklaces[c]){
        uint32_t key=uint32_t(R)|(uint32_t(C)<<16);
        if(visited.count(key))continue;
        reps.push_back({R,C});
        for(int ui=0;ui<8;ui++){
            int u=UNITS[ui]; uint16_t Rt=scale_canon_table[ui][R];
            int signs=relative_sign?2:1;
            for(int sg=0;sg<signs;sg++){
                int v=sg?(N-u)&15:u;
                uint16_t Ct=scale_canon_table[unit_index(v)][C];
                visited.insert(uint32_t(Rt)|(uint32_t(Ct)<<16));
                if(transpose)visited.insert(uint32_t(Ct)|(uint32_t(Rt)<<16));
            }
        }
    }
    return reps;
}
map<PairKey,vector<pair<uint16_t,uint16_t>>> pair_cache;
const vector<pair<uint16_t,uint16_t>>& pair_reps(int r,int c,bool relative_sign){
    if(r>c)swap(r,c);PairKey k{r,c,relative_sign};auto it=pair_cache.find(k);
    if(it==pair_cache.end())it=pair_cache.emplace(k,generate_pair_representatives(r,c,relative_sign)).first;
    return it->second;
}

inline long long da_intersection(int d0,int d1,int a0,int a1){return 2LL*(d0*a0+d1*a1);}
bool profile_passes(const Profile&p){
    int r=p[0],c=p[1],d0=p[2],d1=p[3],a0=p[4],a1=p[5],d=d0+d1,a=a0+a1;
    if(accumulate(p.begin(),p.end(),0)>2*N)return false;
    for(auto xy:{pair<int,int>{r,c},{r,d},{r,a},{c,d},{c,a}})if(xy.first*xy.second<TARGET)return false;
    if(da_intersection(d0,d1,a0,a1)<TARGET)return false;
    int rr=N-r,cc=N-c,dd=N-d,aa=N-a;
    for(auto xy:{pair<int,int>{rr,cc},{rr,dd},{rr,aa},{cc,dd},{cc,aa}})if(xy.first*xy.second<TARGET)return false;
    if(2LL*((H-d0)*(H-a0)+(H-d1)*(H-a1))<TARGET)return false;
    auto triple_simple=[](int x,int y,int z){return 1LL*N*N-1LL*N*(x+y+z)+1LL*x*y+1LL*x*z+1LL*y*z;};
    if(triple_simple(r,c,d)<2*TARGET || triple_simple(r,c,a)<2*TARGET)return false;
    long long I=da_intersection(d0,d1,a0,a1);
    for(int x:{r,c}){
        long long v=1LL*N*N-1LL*N*(x+d+a)+1LL*x*d+1LL*x*a+I;
        if(v<2*TARGET)return false;
    }
    return true;
}
Profile swapRC(Profile p){swap(p[0],p[1]);return p;}
Profile swapDA(Profile p){swap(p[2],p[4]);swap(p[3],p[5]);return p;}
Profile flipParity(Profile p){swap(p[2],p[3]);swap(p[4],p[5]);return p;}
Profile canonical_profile(const Profile&p){
    set<Profile>s{p};bool changed=true;
    while(changed){changed=false;vector<Profile>v(s.begin(),s.end());for(Profile q:v){for(Profile z:{swapRC(q),swapDA(q),flipParity(q)})if(s.insert(z).second)changed=true;}}
    return *s.begin();
}
vector<Profile> generate_profiles(){
    set<Profile>u;int ordered=0;
    for(int r=0;r<=N;r++)for(int c=0;c<=N;c++)for(int d0=0;d0<=H;d0++)for(int d1=0;d1<=H;d1++)for(int a0=0;a0<=H;a0++)for(int a1=0;a1<=H;a1++){
        Profile p{r,c,d0,d1,a0,a1};if(profile_passes(p)){ordered++;u.insert(canonical_profile(p));}
    }
    if(ordered!=1898){cerr<<"profile ordered mismatch "<<ordered<<"\n";exit(5);} 
    vector<Profile>out(u.begin(),u.end());
    sort(out.begin(),out.end(),[](const Profile&x,const Profile&y){int sx=accumulate(x.begin(),x.end(),0),sy=accumulate(y.begin(),y.end(),0);return sx!=sy?sx<sy:x<y;});
    return out;
}
string pstr(const Profile&p){ostringstream os;os<<p[0]<<','<<p[1]<<','<<p[2]<<','<<p[3]<<','<<p[4]<<','<<p[5];return os.str();}

struct Item{uint8_t p,q,par;};
constexpr int NEG=-10000, INF=10000;
bool dfs_choose(const Item*it,int pos,int ce,int co,int k0,int k1,int ps,int qs,int qlim,
                int maxP[17][9][9],int minQ[17][9][9],uint64_t&nodes){
    ++nodes; int ne=k0-ce,no=k1-co;
    if(ne<0||no<0||ne>H||no>H||maxP[pos][ne][no]==NEG||qs>qlim)return false;
    if(ps+maxP[pos][ne][no]<TARGET)return false;
    if(minQ[pos][ne][no]>=INF||qs+minQ[pos][ne][no]>qlim)return false;
    if(ne==0&&no==0)return ps>=TARGET;
    if(ps>=TARGET)return true;
    if(pos>=N)return false;
    int nce=ce+(it[pos].par==0),nco=co+(it[pos].par==1);
    if(dfs_choose(it,pos+1,nce,nco,k0,k1,ps+it[pos].p,qs+it[pos].q,qlim,maxP,minQ,nodes))return true;
    return dfs_choose(it,pos+1,ce,co,k0,k1,ps,qs,qlim,maxP,minQ,nodes);
}
bool exists_D(const uint8_t p[N],const uint8_t q[N],int k0,int k1,int totalq,uint64_t&nodes,bool&entered){
    int qlim=totalq-TARGET;if(qlim<0)return false;
    int maxp=0,minq=0;
    for(int par=0;par<2;par++){
        vector<int>pv,qv;for(int i=par;i<N;i+=2){pv.push_back(p[i]);qv.push_back(q[i]);}
        sort(pv.rbegin(),pv.rend());sort(qv.begin(),qv.end());int k=par?k1:k0;
        for(int i=0;i<k;i++){maxp+=pv[i];minq+=qv[i];}
    }
    if(maxp<TARGET||minq>qlim)return false;
    Item it[N];for(int i=0;i<N;i++)it[i]=Item{p[i],q[i],uint8_t(i&1)};
    sort(it,it+N,[](const Item&a,const Item&b){int lhs=a.p*(b.q+1),rhs=b.p*(a.q+1);if(lhs!=rhs)return lhs>rhs;if(a.p!=b.p)return a.p>b.p;if(a.q!=b.q)return a.q<b.q;return a.par<b.par;});
    static thread_local int maxP[17][9][9],minQ[17][9][9];
    for(int i=0;i<=N;i++)for(int e=0;e<=H;e++)for(int o=0;o<=H;o++){maxP[i][e][o]=NEG;minQ[i][e][o]=INF;}
    maxP[N][0][0]=0;minQ[N][0][0]=0;
    for(int pos=N-1;pos>=0;--pos){
        for(int e=0;e<=H;e++)for(int o=0;o<=H;o++){
            int bp=maxP[pos+1][e][o],bq=minQ[pos+1][e][o];
            int pe=e-(it[pos].par==0),po=o-(it[pos].par==1);
            if(pe>=0&&po>=0&&maxP[pos+1][pe][po]!=NEG)bp=max(bp,maxP[pos+1][pe][po]+it[pos].p);
            if(pe>=0&&po>=0&&minQ[pos+1][pe][po]<INF)bq=min(bq,minQ[pos+1][pe][po]+it[pos].q);
            maxP[pos][e][o]=bp;minQ[pos][e][o]=bq;
        }
    }
    entered=true;return dfs_choose(it,0,0,0,k0,k1,0,0,qlim,maxP,minQ,nodes);
}
bool brute_exists_D(const uint8_t p[N],const uint8_t q[N],int k0,int k1,int totalq){
    for(uint16_t D:masks_by_parity[k0][k1]){int b=0,w=0;for(int d=0;d<N;d++)if((D>>d)&1)b+=p[d];else w+=q[d];if(b>=TARGET&&w>=TARGET)return true;}return false;
}
void completion_self_test(){
    mt19937_64 rng(0x16e0ddc0ffeeULL);
    for(int tc=0;tc<20000;tc++){
        uint8_t p[N],q[N];int tq=0;for(int i=0;i<N;i++){p[i]=uint8_t(rng()%17);q[i]=uint8_t(rng()%17);tq+=q[i];}
        int k0=rng()%9,k1=rng()%9;uint64_t nodes=0;bool entered=false;
        bool x=exists_D(p,q,k0,k1,tq,nodes,entered),y=brute_exists_D(p,q,k0,k1,tq);
        if(x!=y){cerr<<"completion mismatch "<<tc<<" k="<<k0<<","<<k1<<"\n";exit(3);}
    }
}

struct Job{Profile canonical,oriented;int r,c,d0,d1,a0,a1;bool sign;uint64_t reps,Acount;__uint128_t cost;};
long long choose8(int k){return masks_by_parity[k][0].size();} // not used
Job make_job(Profile canon,Profile q){
    // R/C canonical orientation.
    if(q[0]>q[1])q=swapRC(q);
    // Choose which of D/A to enumerate as A; D/A swap is a global symmetry.
    uint64_t ca=masks_by_parity[q[4]][q[5]].size(),cd=masks_by_parity[q[2]][q[3]].size();
    if(cd<ca){q=swapDA(q);swap(ca,cd);} // now A count <= D count
    Job j;j.canonical=canon;j.oriented=q;j.r=q[0];j.c=q[1];j.d0=q[2];j.d1=q[3];j.a0=q[4];j.a1=q[5];
    j.sign=(j.d0==j.a0&&j.d1==j.a1);j.reps=pair_reps(j.r,j.c,j.sign).size();j.Acount=ca;j.cost=(__uint128_t)j.reps*j.Acount;return j;
}
string u128str(__uint128_t x){if(!x)return"0";string s;while(x){s.push_back(char('0'+x%10));x/=10;}reverse(s.begin(),s.end());return s;}

struct Stats{uint64_t A=0,triple=0,calls=0,nodes=0;};
struct Witness{atomic<bool>found{false};uint16_t R=0,C=0,D=0,A=0;mutex mu;};
bool verify(uint16_t R,uint16_t C,uint16_t D,uint16_t A,int&B,int&W){B=W=0;for(int r=0;r<N;r++)for(int c=0;c<N;c++){int d=(r-c)&15,a=(r+c)&15;bool br=(R>>r)&1,bc=(C>>c)&1,bd=(D>>d)&1,ba=(A>>a)&1;if(br&&bc&&bd&&ba)B++;if(!br&&!bc&&!bd&&!ba)W++;}return B>=TARGET&&W>=TARGET;}
Stats search_job(const Job&j,Witness&w){
    const auto&reps=pair_reps(j.r,j.c,j.sign);const auto&As=masks_by_parity[j.a0][j.a1];Stats total;
    #pragma omp parallel
    {
        Stats local;
        #pragma omp for schedule(dynamic,8)
        for(size_t ii=0;ii<reps.size();ii++){
            if(w.found.load(memory_order_relaxed))continue;uint16_t R=reps[ii].first,C=reps[ii].second;
            uint16_t P1[N]={},P2[N]={},Q1[N]={},Q2[N]={};
            for(int d=0;d<N;d++)for(int a=0;a<N;a++){
                if((d^a)&1)continue;
                int sum=(a+d)&15, diff=(a-d)&15;
                int r0=(sum>>1)&7, c0=(diff>>1)&7;
                int rr[2],cc[2];
                if((((r0-c0)&15)==d) && (((r0+c0)&15)==a)) {
                    rr[0]=r0; cc[0]=c0; rr[1]=r0+8; cc[1]=c0+8;
                } else {
                    rr[0]=r0+8; cc[0]=c0; rr[1]=r0; cc[1]=c0+8;
                }
                int pc=0,qc=0;
                for(int t=0;t<2;t++){
                    int r=rr[t],c=cc[t];bool br=(R>>r)&1,bc=(C>>c)&1;
                    pc+=br&&bc;qc+=(!br)&&(!bc);
                }
                if(pc>=1)P1[d]|=uint16_t(1u<<a);if(pc==2)P2[d]|=uint16_t(1u<<a);
                if(qc>=1)Q1[d]|=uint16_t(1u<<a);if(qc==2)Q2[d]|=uint16_t(1u<<a);
            }
            for(uint16_t A:As){
                if(w.found.load(memory_order_relaxed))break;++local.A;uint16_t Ac=ALL^A;uint8_t p[N],q[N];int tp=0,tq=0;
                for(int d=0;d<N;d++){
                    p[d]=uint8_t(__builtin_popcount((unsigned)(P1[d]&A))+__builtin_popcount((unsigned)(P2[d]&A)));
                    q[d]=uint8_t(__builtin_popcount((unsigned)(Q1[d]&Ac))+__builtin_popcount((unsigned)(Q2[d]&Ac)));
                    tp+=p[d];tq+=q[d];
                }
                if(tp<TARGET||tq<TARGET)continue;++local.triple;bool entered=false;
                if(brute_exists_D(p,q,j.d0,j.d1,tq)){
                    uint16_t foundD=0;bool got=false;
                    for(uint16_t D:masks_by_parity[j.d0][j.d1]){int b=0,ww=0;for(int d=0;d<N;d++)if((D>>d)&1)b+=p[d];else ww+=q[d];if(b>=TARGET&&ww>=TARGET){foundD=D;got=true;break;}}
                    if(!got){cerr<<"witness recovery failure\n";abort();}
                    bool expected=false;if(w.found.compare_exchange_strong(expected,true)){lock_guard<mutex>lk(w.mu);w.R=R;w.C=C;w.D=foundD;w.A=A;}break;
                }
                (void)entered;
            }
        }
        #pragma omp critical
        {total.A+=local.A;total.triple+=local.triple;total.calls+=local.calls;total.nodes+=local.nodes;}
    }
    return total;
}
}

int main(int argc,char**argv){
    bool estimate=false;string out="/tmp/peace16_certificate.tsv";for(int i=1;i<argc;i++){string s=argv[i];if(s=="--estimate-only")estimate=true;else if(s=="--output"&&i+1<argc)out=argv[++i];else{cerr<<"bad arg\n";return 2;}}
    double start=omp_get_wtime();initialize_masks();completion_self_test();
    if(necklaces[8].size()!=810){cerr<<"necklace mismatch\n";return 4;}
    if(pair_reps(7,8,false).size()!=73663||pair_reps(8,8,false).size()!=42062){cerr<<"pair orbit mismatch "<<pair_reps(7,8,false).size()<<" "<<pair_reps(8,8,false).size()<<"\n";return 4;}
    vector<Profile>profiles=generate_profiles();if(profiles.size()!=342){cerr<<"profiles mismatch "<<profiles.size()<<"\n";return 5;}
    vector<Job>jobs;__uint128_t est=0;
    for(Profile p:profiles){set<Profile>ors{p,flipParity(p)};for(Profile q:ors){Job j=make_job(p,q);jobs.push_back(j);est+=j.cost;}}
    sort(jobs.begin(),jobs.end(),[](const Job&x,const Job&y){int sx=accumulate(x.canonical.begin(),x.canonical.end(),0),sy=accumulate(y.canonical.begin(),y.canonical.end(),0);if(sx!=sy)return sx<sy;if(x.canonical!=y.canonical)return x.canonical<y.canonical;return x.oriented<y.oriented;});
    cerr<<"SELFTEST_OK profiles="<<profiles.size()<<" jobs="<<jobs.size()<<" estimated_A="<<u128str(est)<<" threads="<<omp_get_max_threads()<<"\n";
    if(estimate)return 0;
    ofstream cert(out);cert<<"canonical\toriented\tS\tr\tc\td0\td1\ta0\ta1\tsign\tpair_orbits\tA_per_orbit\tA_checked\ttriple_pass\tdfs_calls\tdfs_nodes\tresult\tseconds\n";
    uint64_t allA=0,allt=0,allc=0,alln=0;
    for(size_t z=0;z<jobs.size();z++){
        auto&j=jobs[z];double t0=omp_get_wtime();Witness w;Stats st=search_job(j,w);double sec=omp_get_wtime()-t0;allA+=st.A;allt+=st.triple;allc+=st.calls;alln+=st.nodes;string result=w.found?"SAT":"UNSAT";int S=accumulate(j.canonical.begin(),j.canonical.end(),0);
        cert<<pstr(j.canonical)<<'\t'<<pstr(j.oriented)<<'\t'<<S<<'\t'<<j.r<<'\t'<<j.c<<'\t'<<j.d0<<'\t'<<j.d1<<'\t'<<j.a0<<'\t'<<j.a1<<'\t'<<j.sign<<'\t'<<j.reps<<'\t'<<j.Acount<<'\t'<<st.A<<'\t'<<st.triple<<'\t'<<st.calls<<'\t'<<st.nodes<<'\t'<<result<<'\t'<<fixed<<setprecision(6)<<sec<<'\n';cert.flush();
        cerr<<"["<<setw(3)<<z+1<<"/"<<jobs.size()<<"] "<<pstr(j.canonical)<<" -> "<<pstr(j.oriented)<<" orb="<<j.reps<<" A="<<st.A<<" "<<result<<" sec="<<fixed<<setprecision(3)<<sec<<"\n";
        if(w.found){int B,W;bool ok=verify(w.R,w.C,w.D,w.A,B,W);cerr<<"WITNESS R="<<w.R<<" C="<<w.C<<" D="<<w.D<<" A="<<w.A<<" B="<<B<<" W="<<W<<" verify="<<ok<<"\n";cert<<"# WITNESS "<<w.R<<' '<<w.C<<' '<<w.D<<' '<<w.A<<" B="<<B<<" W="<<W<<"\n";return 10;}
    }
    double elapsed=omp_get_wtime()-start;cert<<"# TOTAL A="<<allA<<" triple="<<allt<<" calls="<<allc<<" nodes="<<alln<<" result=UNSAT elapsed="<<elapsed<<"\n";cerr<<"ALL_UNSAT A="<<allA<<" triple="<<allt<<" calls="<<allc<<" nodes="<<alln<<" elapsed="<<elapsed<<"\n";return 0;
}
