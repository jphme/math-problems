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
constexpr int N = 15;
constexpr int TARGET = 21;
constexpr uint16_t ALL = (1u << N) - 1;
constexpr int INV2 = 8; // 2*8 = 1 mod 15
constexpr int UNITS[8] = {1,2,4,7,8,11,13,14};

using Profile = array<int,4>;

vector<uint16_t> masks_by_size[16];
vector<uint16_t> necklaces[16];
uint16_t translation_canon_table[1 << N];
uint16_t scale_canon_table[8][1 << N];

inline uint16_t transform_mask(uint16_t m, int u, int shift = 0) {
    uint16_t out = 0;
    while (m) {
        int x = __builtin_ctz((unsigned)m);
        m &= uint16_t(m - 1);
        out |= uint16_t(1u << ((u * x + shift) % N));
    }
    return out;
}

inline uint16_t rotate15(uint16_t m, int s) {
    if (!s) return m;
    return uint16_t((((uint32_t)m << s) | ((uint32_t)m >> (N-s))) & ALL);
}

void initialize_masks() {
    for (int m = 0; m < (1 << N); ++m) {
        uint16_t best = numeric_limits<uint16_t>::max();
        for (int s=0;s<N;s++) best=min(best,rotate15((uint16_t)m,s));
        translation_canon_table[m]=best;
        masks_by_size[__builtin_popcount((unsigned)m)].push_back((uint16_t)m);
    }
    for (int ui=0;ui<8;ui++) for (int m=0;m<(1<<N);m++) {
        uint16_t raw=transform_mask((uint16_t)m,UNITS[ui]);
        scale_canon_table[ui][m]=translation_canon_table[raw];
    }
    for (int k = 0; k <= N; ++k) {
        unordered_set<uint16_t> seen;
        seen.reserve(masks_by_size[k].size() * 2 + 1);
        for (uint16_t m : masks_by_size[k]) seen.insert(translation_canon_table[m]);
        necklaces[k].assign(seen.begin(), seen.end());
        sort(necklaces[k].begin(), necklaces[k].end());
    }
}

inline int unit_index(int u) {
    for (int i=0;i<8;i++) if (UNITS[i]==u) return i;
    abort();
}

struct PairKey {
    int r, c;
    bool relative_sign;
    bool operator<(const PairKey& o) const {
        return tie(r,c,relative_sign) < tie(o.r,o.c,o.relative_sign);
    }
};

vector<pair<uint16_t,uint16_t>> generate_pair_representatives(int r, int c, bool relative_sign) {
    assert(r <= c);
    const bool transpose = (r == c);
    unordered_set<uint32_t> visited;
    visited.reserve(necklaces[r].size() * necklaces[c].size() * 2 + 1);
    vector<pair<uint16_t,uint16_t>> reps;

    for (uint16_t R : necklaces[r]) {
        for (uint16_t C : necklaces[c]) {
            const uint32_t key = uint32_t(R) | (uint32_t(C) << N);
            if (visited.find(key) != visited.end()) continue;
            reps.push_back({R,C});

            for (int ui=0;ui<8;ui++) {
                const int u=UNITS[ui];
                const uint16_t Rt=scale_canon_table[ui][R];
                const int sign_count=relative_sign?2:1;
                for (int sg=0;sg<sign_count;++sg) {
                    const int v=sg?(N-u)%N:u;
                    const uint16_t Ct=scale_canon_table[unit_index(v)][C];
                    visited.insert(uint32_t(Rt) | (uint32_t(Ct) << N));
                    if (transpose)
                        visited.insert(uint32_t(Ct) | (uint32_t(Rt) << N));
                }
            }
        }
    }
    return reps;
}

map<PairKey, vector<pair<uint16_t,uint16_t>>> pair_cache;
const vector<pair<uint16_t,uint16_t>>& pair_reps(int r, int c, bool relative_sign) {
    if (r > c) swap(r,c);
    PairKey key{r,c,relative_sign};
    auto it = pair_cache.find(key);
    if (it == pair_cache.end()) {
        auto reps = generate_pair_representatives(r,c,relative_sign);
        it = pair_cache.emplace(key, move(reps)).first;
    }
    return it->second;
}

long long triple_complement_total(int x, int y, int z) {
    return 225 - 15LL*(x+y+z) + 1LL*x*y + 1LL*x*z + 1LL*y*z;
}

bool profile_passes_filters(const Profile& s) {
    const int S = accumulate(s.begin(), s.end(), 0);
    if (S > 30) return false;
    for (int i=0;i<4;i++) for (int j=i+1;j<4;j++) {
        if (s[i]*s[j] < TARGET) return false;
        if ((15-s[i])*(15-s[j]) < TARGET) return false;
    }
    for (int omit=0;omit<4;omit++) {
        int v[3], q=0;
        for (int i=0;i<4;i++) if (i!=omit) v[q++]=s[i];
        if (triple_complement_total(v[0],v[1],v[2]) < 2*TARGET) return false;
    }
    return true;
}

const int D4[8][4] = {
    {0,1,2,3},{0,1,3,2},{1,0,2,3},{1,0,3,2},
    {2,3,0,1},{2,3,1,0},{3,2,0,1},{3,2,1,0}
};

Profile profile_canonical(const Profile& s) {
    Profile best{99,99,99,99};
    for (int z=0;z<8;z++) {
        Profile t;
        for (int i=0;i<4;i++) t[i]=s[D4[z][i]];
        best=min(best,t);
    }
    if (accumulate(s.begin(),s.end(),0)==30) {
        Profile comp;
        for (int i=0;i<4;i++) comp[i]=15-s[i];
        for (int z=0;z<8;z++) {
            Profile t;
            for (int i=0;i<4;i++) t[i]=comp[D4[z][i]];
            best=min(best,t);
        }
    }
    return best;
}

vector<Profile> generate_profiles() {
    set<Profile> uniq;
    for (int r=0;r<=15;r++) for (int c=0;c<=15;c++)
    for (int d=0;d<=15;d++) for (int a=0;a<=15;a++) {
        Profile s{r,c,d,a};
        if (profile_passes_filters(s)) uniq.insert(profile_canonical(s));
    }
    vector<Profile> out(uniq.begin(),uniq.end());
    sort(out.begin(),out.end(),[](const Profile& x,const Profile& y){
        int sx=accumulate(x.begin(),x.end(),0), sy=accumulate(y.begin(),y.end(),0);
        return sx!=sy ? sx<sy : x<y;
    });
    return out;
}

string profile_string(const Profile& s) {
    ostringstream os;
    os << s[0] << ',' << s[1] << ',' << s[2] << ',' << s[3];
    return os.str();
}

set<Profile> read_worklist_profiles(const string& path) {
    ifstream in(path);
    if (!in) throw runtime_error("cannot open worklist: " + path);
    set<Profile> out;
    string line;
    while (getline(in,line)) {
        if (line.empty() || line[0]=='#') continue;
        string first = line.substr(0,line.find('\t'));
        replace(first.begin(),first.end(),',',' ');
        istringstream is(first);
        Profile p;
        if (!(is>>p[0]>>p[1]>>p[2]>>p[3])) throw runtime_error("bad worklist line: "+line);
        out.insert(p);
    }
    return out;
}

struct Item { uint8_t p, q; };

bool dfs_choose(const Item* items, int pos, int chosen, int k,
                int psum, int qsum, int qlimit,
                int maxP[16][16], int minQ[16][16], uint64_t& nodes) {
    ++nodes;
    const int need = k - chosen;
    if (need < 0 || 15-pos < need || qsum > qlimit) return false;
    if (maxP[pos][need] < 0 || psum + maxP[pos][need] < TARGET) return false;
    if (minQ[pos][need] >= 999 || qsum + minQ[pos][need] > qlimit) return false;
    if (need == 0) return psum >= TARGET;
    if (psum >= TARGET) return true; // the minQ test guarantees a q-feasible completion

    if (dfs_choose(items,pos+1,chosen+1,k,
                   psum+items[pos].p,qsum+items[pos].q,qlimit,maxP,minQ,nodes)) return true;
    return dfs_choose(items,pos+1,chosen,k,psum,qsum,qlimit,maxP,minQ,nodes);
}

bool exists_D(const uint8_t p[15], const uint8_t q[15], int k, int total_q,
              uint64_t& nodes, bool& entered_dfs) {
    const int qlimit = total_q - TARGET;
    if (qlimit < 0) return false;

    int pc[16] = {}, qc[16] = {};
    for (int i=0;i<15;i++) { ++pc[p[i]]; ++qc[q[i]]; }

    int maxp=0, remaining=k;
    for (int v=15;v>=0 && remaining;--v) {
        int take=min(remaining,pc[v]); maxp += take*v; remaining -= take;
    }
    if (maxp < TARGET) return false;

    int minq=0; remaining=k;
    for (int v=0;v<=15 && remaining;++v) {
        int take=min(remaining,qc[v]); minq += take*v; remaining -= take;
    }
    if (minq > qlimit) return false;

    Item items[15];
    for (int i=0;i<15;i++) items[i] = Item{p[i],q[i]};
    sort(items,items+15,[](const Item& a,const Item& b){
        const int lhs=a.p*(b.q+1), rhs=b.p*(a.q+1);
        if (lhs!=rhs) return lhs>rhs;
        if (a.p!=b.p) return a.p>b.p;
        return a.q<b.q;
    });

    constexpr int NEG=-1000, INF=999;
    int maxP[16][16], minQ[16][16];
    for (int i=0;i<=15;i++) for (int j=0;j<=15;j++) { maxP[i][j]=NEG; minQ[i][j]=INF; }
    maxP[15][0]=0; minQ[15][0]=0;
    for (int pos=14;pos>=0;--pos) {
        maxP[pos][0]=0; minQ[pos][0]=0;
        for (int j=1;j<=15-pos;j++) {
            maxP[pos][j] = max(maxP[pos+1][j],
                maxP[pos+1][j-1]==NEG ? NEG : maxP[pos+1][j-1]+items[pos].p);
            minQ[pos][j] = min(minQ[pos+1][j],
                minQ[pos+1][j-1]>=INF ? INF : minQ[pos+1][j-1]+items[pos].q);
        }
    }
    entered_dfs=true;
    return dfs_choose(items,0,0,k,0,0,qlimit,maxP,minQ,nodes);
}

bool brute_exists_D(const uint8_t p[15], const uint8_t q[15], int k, int total_q) {
    for (uint16_t D : masks_by_size[k]) {
        int b=0,w=0;
        for (int d=0;d<15;d++) {
            if ((D>>d)&1) b+=p[d]; else w+=q[d];
        }
        if (b>=TARGET && w>=TARGET) return true;
    }
    return false;
}

void completion_self_test() {
    mt19937_64 rng(0x4d595df4d0f33173ULL);
    for (int tc=0;tc<20000;tc++) {
        uint8_t p[15],q[15]; int tq=0;
        for (int i=0;i<15;i++) {
            p[i]=uint8_t(rng()%9); q[i]=uint8_t(rng()%9); tq+=q[i];
        }
        int k=3 + int(rng()%10);
        uint64_t nodes=0; bool entered=false;
        bool x=exists_D(p,q,k,tq,nodes,entered);
        bool y=brute_exists_D(p,q,k,tq);
        if (x!=y) {
            cerr << "completion self-test mismatch at case " << tc << "\n";
            exit(3);
        }
    }
}

struct Orientation {
    string fixed_name;
    int r,c,d,a;
    bool relative_sign;
    uint64_t reps;
    uint64_t A_count;
    __uint128_t cost;
};

Orientation make_orientation(const Profile& p, bool fix_first_pair) {
    int x0,x1,y0,y1;
    if (fix_first_pair) { x0=p[0];x1=p[1];y0=p[2];y1=p[3]; }
    else { x0=p[2];x1=p[3];y0=p[0];y1=p[1]; }
    int r=min(x0,x1), c=max(x0,x1);

    // We may globally swap the two unfinished families. Enumerate whichever
    // size has fewer subsets; the other size is selected by the exact D search.
    int a,d;
    if (masks_by_size[y0].size() <= masks_by_size[y1].size()) { a=y0;d=y1; }
    else { a=y1;d=y0; }

    const bool sign = (y0==y1); // relative sign swaps the unfinished families
    const auto& repsv=pair_reps(r,c,sign);
    Orientation o;
    o.fixed_name=fix_first_pair?"RC":"DA";
    o.r=r;o.c=c;o.d=d;o.a=a;o.relative_sign=sign;
    o.reps=repsv.size();o.A_count=masks_by_size[a].size();
    o.cost=(__uint128_t)o.reps*o.A_count;
    return o;
}

string u128str(__uint128_t x) {
    if (!x) return "0";
    string s;
    while (x) { s.push_back(char('0'+x%10)); x/=10; }
    reverse(s.begin(),s.end()); return s;
}

struct SearchStats {
    uint64_t A_checked=0;
    uint64_t triple_pass=0;
    uint64_t dfs_calls=0;
    uint64_t dfs_nodes=0;
};

struct Witness {
    atomic<bool> found{false};
    uint16_t R=0,C=0,D=0,A=0;
    mutex mu;
};

bool verify_quadruple(uint16_t R,uint16_t C,uint16_t D,uint16_t A,int& B,int& W) {
    B=W=0;
    for (int r=0;r<15;r++) for (int c=0;c<15;c++) {
        int d=(r-c+15)%15, a=(r+c)%15;
        bool br=(R>>r)&1, bc=(C>>c)&1, bd=(D>>d)&1, ba=(A>>a)&1;
        if (br&&bc&&bd&&ba) ++B;
        if (!br&&!bc&&!bd&&!ba) ++W;
    }
    return B>=TARGET&&W>=TARGET;
}

SearchStats search_profile(const Orientation& o, Witness& witness) {
    const auto& reps=pair_reps(o.r,o.c,o.relative_sign);
    const auto& As=masks_by_size[o.a];
    SearchStats total;

    #pragma omp parallel
    {
        SearchStats local;
        #pragma omp for schedule(dynamic,8)
        for (size_t ii=0;ii<reps.size();++ii) {
            if (witness.found.load(memory_order_relaxed)) continue;
            const uint16_t R=reps[ii].first, C=reps[ii].second;
            uint16_t Pmask[15]={}, Qmask[15]={};
            for (int d=0;d<15;d++) for (int a=0;a<15;a++) {
                const int r=(INV2*(a+d))%15;
                const int c=(INV2*((a-d+15)%15))%15;
                if (((R>>r)&1) && ((C>>c)&1)) Pmask[d] |= uint16_t(1u<<a);
                if (!((R>>r)&1) && !((C>>c)&1)) Qmask[d] |= uint16_t(1u<<a);
            }

            for (uint16_t A:As) {
                if (witness.found.load(memory_order_relaxed)) break;
                ++local.A_checked;
                uint8_t p[15],q[15]; int total_p=0,total_q=0;
                const uint16_t Ac=ALL^A;
                for (int d=0;d<15;d++) {
                    p[d]=uint8_t(__builtin_popcount((unsigned)(Pmask[d]&A)));
                    q[d]=uint8_t(__builtin_popcount((unsigned)(Qmask[d]&Ac)));
                    total_p+=p[d]; total_q+=q[d];
                }
                if (total_p<TARGET || total_q<TARGET) continue;
                ++local.triple_pass;

                bool entered=false;
                if (exists_D(p,q,o.d,total_q,local.dfs_nodes,entered)) {
                    if (entered) ++local.dfs_calls;
                    uint16_t foundD=0;
                    for (uint16_t D:masks_by_size[o.d]) {
                        int b=0,w=0;
                        for (int d=0;d<15;d++) {
                            if ((D>>d)&1) b+=p[d]; else w+=q[d];
                        }
                        if (b>=TARGET&&w>=TARGET) { foundD=D; break; }
                    }
                    if (!foundD && o.d!=0) {
                        cerr << "internal error: witness not recovered\n"; abort();
                    }
                    bool expected=false;
                    if (witness.found.compare_exchange_strong(expected,true)) {
                        lock_guard<mutex> lock(witness.mu);
                        witness.R=R;witness.C=C;witness.D=foundD;witness.A=A;
                    }
                    break;
                }
                if (entered) ++local.dfs_calls;
            }
        }
        #pragma omp critical
        {
            total.A_checked+=local.A_checked;
            total.triple_pass+=local.triple_pass;
            total.dfs_calls+=local.dfs_calls;
            total.dfs_nodes+=local.dfs_nodes;
        }
    }
    return total;
}

uint64_t fnv_pair_hash(const vector<pair<uint16_t,uint16_t>>& reps) {
    uint64_t h=1469598103934665603ULL;
    for (auto [r,c]:reps) {
        uint32_t x=uint32_t(r)|(uint32_t(c)<<15);
        for (int i=0;i<4;i++) { h^=(x>>(8*i))&255; h*=1099511628211ULL; }
    }
    return h;
}

} // namespace

int main(int argc,char**argv) {
    string out_path="/mnt/data/peace15_certificate.tsv";
    string worklist="/mnt/data/WORKLIST-2026-07-25.tsv";
    bool estimate_only=false;
    for (int i=1;i<argc;i++) {
        string a=argv[i];
        if (a=="--estimate-only") estimate_only=true;
        else if (a=="--output" && i+1<argc) out_path=argv[++i];
        else if (a=="--worklist" && i+1<argc) worklist=argv[++i];
        else { cerr<<"unknown argument: "<<a<<"\n"; return 2; }
    }

    const double start=omp_get_wtime();
    initialize_masks();
    completion_self_test();

    // Independent, known orbit-count checks.
    if (pair_reps(7,7,false).size()!=11793) { cerr<<"bad H orbit count\n"; return 4; }
    if (pair_reps(7,7,true).size()!=6892) { cerr<<"bad G orbit count\n"; return 4; }
    if (pair_reps(7,8,true).size()!=13654) { cerr<<"bad unequal orbit count\n"; return 4; }

    vector<Profile> profiles=generate_profiles();
    if (profiles.size()!=247) { cerr<<"expected 247 profiles, got "<<profiles.size()<<"\n"; return 5; }
    set<Profile> generated(profiles.begin(),profiles.end());
    set<Profile> supplied=read_worklist_profiles(worklist);
    if (generated!=supplied) { cerr<<"generated profile set differs from supplied worklist\n"; return 6; }

    struct Job { Profile p; Orientation o; };
    vector<Job> jobs;
    __uint128_t total_cost=0;
    for (const Profile& p:profiles) {
        Orientation x=make_orientation(p,true), y=make_orientation(p,false);
        Orientation o=(y.cost<x.cost)?y:x;
        jobs.push_back({p,o}); total_cost+=o.cost;
    }
    sort(jobs.begin(),jobs.end(),[](const Job& x,const Job& y){
        int sx=accumulate(x.p.begin(),x.p.end(),0), sy=accumulate(y.p.begin(),y.p.end(),0);
        if (sx!=sy) return sx<sy;
        return x.p<y.p;
    });

    cerr << "SELFTEST_OK profiles=247 estimated_A=" << u128str(total_cost)
         << " threads=" << omp_get_max_threads() << "\n";
    if (estimate_only) return 0;

    ofstream cert(out_path);
    if (!cert) { cerr<<"cannot create certificate file\n"; return 7; }
    cert << "# peaceable queens on Z_15^2 exact exhaustive certificate\n";
    cert << "# target=21 profiles=247 estimated_A="<<u128str(total_cost)<<"\n";
    cert << "profile\tS\tfixed\tr\tc\td\ta\trelative_sign\tpair_orbits\tpair_hash_fnv64\tA_per_orbit\tA_checked\ttriple_pass\tdfs_calls\tdfs_nodes\tresult\tseconds\n";

    uint64_t all_A=0,all_triple=0,all_calls=0,all_nodes=0;
    for (size_t j=0;j<jobs.size();j++) {
        const Job& job=jobs[j];
        const auto& reps=pair_reps(job.o.r,job.o.c,job.o.relative_sign);
        const uint64_t ph=fnv_pair_hash(reps);
        const double t0=omp_get_wtime();
        Witness witness;
        SearchStats st=search_profile(job.o,witness);
        const double sec=omp_get_wtime()-t0;
        all_A+=st.A_checked;all_triple+=st.triple_pass;all_calls+=st.dfs_calls;all_nodes+=st.dfs_nodes;
        const int S=accumulate(job.p.begin(),job.p.end(),0);
        const string result=witness.found.load()?"SAT":"UNSAT";
        cert << profile_string(job.p)<<'\t'<<S<<'\t'<<job.o.fixed_name<<'\t'
             <<job.o.r<<'\t'<<job.o.c<<'\t'<<job.o.d<<'\t'<<job.o.a<<'\t'
             <<(job.o.relative_sign?1:0)<<'\t'<<job.o.reps<<'\t'
             <<hex<<setw(16)<<setfill('0')<<ph<<dec<<setfill(' ')<<'\t'
             <<job.o.A_count<<'\t'<<st.A_checked<<'\t'<<st.triple_pass<<'\t'
             <<st.dfs_calls<<'\t'<<st.dfs_nodes<<'\t'<<result<<'\t'
             <<fixed<<setprecision(6)<<sec<<'\n';
        cert.flush();

        cerr << "["<<setw(3)<<(j+1)<<"/247] "<<profile_string(job.p)
             <<" S="<<S<<" "<<job.o.fixed_name<<"("<<job.o.r<<','<<job.o.c<<")"
             <<" rem("<<job.o.d<<','<<job.o.a<<")"
             <<" orbits="<<job.o.reps<<" A="<<st.A_checked
             <<" result="<<result<<" sec="<<fixed<<setprecision(3)<<sec<<"\n";

        if (witness.found.load()) {
            int B,W; verify_quadruple(witness.R,witness.C,witness.D,witness.A,B,W);
            cerr << "WITNESS masks R="<<witness.R<<" C="<<witness.C<<" D="<<witness.D<<" A="<<witness.A
                 <<" B="<<B<<" W="<<W<<"\n";
            cert << "# WITNESS "<<witness.R<<' '<<witness.C<<' '<<witness.D<<' '<<witness.A<<" B="<<B<<" W="<<W<<"\n";
            cert.close();
            return 10;
        }
    }
    const double elapsed=omp_get_wtime()-start;
    cert << "# TOTAL A_checked="<<all_A<<" triple_pass="<<all_triple
         <<" dfs_calls="<<all_calls<<" dfs_nodes="<<all_nodes
         <<" result=UNSAT elapsed_seconds="<<fixed<<setprecision(6)<<elapsed<<"\n";
    cert.close();
    cerr << "ALL_UNSAT A_checked="<<all_A<<" triple_pass="<<all_triple
         <<" dfs_calls="<<all_calls<<" dfs_nodes="<<all_nodes
         <<" elapsed="<<fixed<<setprecision(3)<<elapsed<<"\n";
    return 0;
}
