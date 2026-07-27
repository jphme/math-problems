
#include <algorithm>
#include <array>
#include <atomic>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#else
static double omp_get_wtime() { return 0.0; }
static int omp_get_max_threads() { return 1; }
#endif

namespace union_enum {

constexpr int N=16;
constexpr int H=8;
constexpr int TARGET=33;
constexpr std::uint16_t ALL=0xffffu;
constexpr std::array<int,8> UNITS{1,3,5,7,9,11,13,15};

using Mask=std::uint16_t;
using Profile=std::array<int,6>; // r,c,d0,d1,a0,a1

struct DCounts {
    std::uint8_t even=0;
    std::uint8_t odd=0;
    auto operator<=>(const DCounts&) const=default;
};

struct TypeDomain {
    int r=0,c=0;
    std::array<std::vector<DCounts>,81> d_for_a;
    std::vector<std::pair<int,int>> a_counts;
    std::uint64_t A_masks_per_pair=0;
};

Mask rotate_mask(Mask m,int s) {
    s&=15;
    if (!s) return m;
    std::uint32_t x=m;
    return Mask(((x<<s)|(x>>(16-s)))&0xffffu);
}

Mask multiply_mask(Mask m,int u) {
    Mask out=0;
    for (int x=0;x<N;++x) if ((m>>x)&1u) out|=Mask(1u<<((u*x)&15));
    return out;
}

Mask translation_canonical(Mask m) {
    Mask best=ALL;
    for (int s=0;s<N;++s) best=std::min(best,rotate_mask(m,s));
    return best;
}

std::vector<Mask> necklaces(int size) {
    std::vector<Mask> out;
    for (unsigned x=0;x<(1u<<N);++x) {
        Mask m=static_cast<Mask>(x);
        if (std::popcount(x)==size && translation_canonical(m)==m) out.push_back(m);
    }
    return out;
}

std::pair<Mask,Mask> pair_canonical(Mask R,Mask C,bool equal_sizes) {
    std::pair<Mask,Mask> best{ALL,ALL};
    auto consider=[&](Mask X,Mask Y) {
        best=std::min(best,std::pair{
            translation_canonical(X),translation_canonical(Y)
        });
    };
    for (int u:UNITS) {
        Mask Ru=multiply_mask(R,u);
        Mask Cu=multiply_mask(C,u);
        Mask Cminus=multiply_mask(C,(N-u)&15);
        consider(Ru,Cu);
        consider(Ru,Cminus);
        if (equal_sizes) {
            consider(Cu,Ru);
            consider(Cminus,Ru);
        }
    }
    return best;
}

std::vector<std::pair<Mask,Mask>> pair_transversal(
    int r,int c,const std::vector<Mask>& Rneck,const std::vector<Mask>& Cneck
) {
    std::vector<std::pair<Mask,Mask>> out;
    for (Mask R:Rneck) for (Mask C:Cneck) {
        if (pair_canonical(R,C,r==c)==std::pair{R,C}) out.push_back({R,C});
    }
    return out;
}

long long da_pairs(int d0,int d1,int a0,int a1) {
    return 2LL*(d0*a0+d1*a1);
}

bool necessary_profile(const Profile& p) {
    int r=p[0],c=p[1],d0=p[2],d1=p[3],a0=p[4],a1=p[5];
    int d=d0+d1,a=a0+a1;
    if (std::accumulate(p.begin(),p.end(),0)>32) return false;

    for (auto [x,y]:std::array<std::pair<int,int>,5>{
        std::pair{r,c},std::pair{r,d},std::pair{r,a},
        std::pair{c,d},std::pair{c,a}
    }) if (x*y<TARGET) return false;
    if (da_pairs(d0,d1,a0,a1)<TARGET) return false;

    int rr=N-r,cc=N-c,dd=N-d,aa=N-a;
    for (auto [x,y]:std::array<std::pair<int,int>,5>{
        std::pair{rr,cc},std::pair{rr,dd},std::pair{rr,aa},
        std::pair{cc,dd},std::pair{cc,aa}
    }) if (x*y<TARGET) return false;
    if (2LL*((H-d0)*(H-a0)+(H-d1)*(H-a1))<TARGET) return false;

    auto ordinary=[](int x,int y,int z) {
        return 1LL*N*N-1LL*N*(x+y+z)+1LL*x*y+1LL*x*z+1LL*y*z;
    };
    if (ordinary(r,c,d)<2*TARGET || ordinary(r,c,a)<2*TARGET) return false;

    long long exceptional=da_pairs(d0,d1,a0,a1);
    for (int x:{r,c}) {
        long long triple=1LL*N*N-1LL*N*(x+d+a)+1LL*x*d+1LL*x*a+exceptional;
        if (triple<2*TARGET) return false;
    }
    return true;
}

std::map<std::pair<int,int>,TypeDomain> build_domain(int& ordered_profiles) {
    std::map<std::pair<int,int>,TypeDomain> types;
    ordered_profiles=0;
    for (int r=0;r<=N;++r) for (int c=0;c<=N;++c)
    for (int d0=0;d0<=H;++d0) for (int d1=0;d1<=H;++d1)
    for (int a0=0;a0<=H;++a0) for (int a1=0;a1<=H;++a1) {
        Profile p{r,c,d0,d1,a0,a1};
        if (!necessary_profile(p)) continue;
        ++ordered_profiles;
        int x=r,y=c;
        if (x>y) std::swap(x,y); // transpose; negating D preserves parity counts
        auto& td=types[{x,y}];
        td.r=x;td.c=y;
        td.d_for_a[9*a0+a1].push_back(
            DCounts{static_cast<std::uint8_t>(d0),static_cast<std::uint8_t>(d1)}
        );
    }

    auto choose8=[](int k)->std::uint64_t {
        if (k<0 || k>8) return 0;
        std::uint64_t z=1;
        for (int i=1;i<=k;++i) z=z*(8-k+i)/i;
        return z;
    };
    for (auto& [key,td]:types) {
        for (int a0=0;a0<=H;++a0) for (int a1=0;a1<=H;++a1) {
            auto& v=td.d_for_a[9*a0+a1];
            std::sort(v.begin(),v.end());
            v.erase(std::unique(v.begin(),v.end()),v.end());
            if (!v.empty()) {
                td.a_counts.push_back({a0,a1});
                td.A_masks_per_pair+=choose8(a0)*choose8(a1);
            }
        }
    }
    return types;
}

struct MaskTables {
    std::array<std::vector<Mask>,81> by_parity_count;
    std::array<Mask,256> even_mask{};
    std::array<Mask,256> odd_mask{};
    std::array<std::uint8_t,256> cardinality{};

    MaskTables() {
        for (int s=0;s<256;++s) {
            cardinality[s]=static_cast<std::uint8_t>(
                std::popcount(static_cast<unsigned>(s))
            );
            Mask e=0,o=0;
            for (int i=0;i<8;++i) if ((s>>i)&1) {
                e|=Mask(1u<<(2*i));
                o|=Mask(1u<<(2*i+1));
            }
            even_mask[s]=e;odd_mask[s]=o;
        }
        for (unsigned m=0;m<(1u<<N);++m) {
            Mask x=static_cast<Mask>(m);
            int e=std::popcount(static_cast<unsigned>(x&0x5555u));
            int o=std::popcount(static_cast<unsigned>(x&0xaaaau));
            by_parity_count[9*e+o].push_back(x);
        }
    }
};

struct WeightedSubset {
    Mask mask=0;
    std::uint8_t black=0;
    std::uint8_t selected_white=0;
};

struct Stats {
    std::uint64_t pair_reps=0;
    std::uint64_t logical_A=0;
    std::uint64_t A_tested=0;
    std::uint64_t scalar_survivors=0;
    std::uint64_t d_count_cases=0;
    std::uint64_t logical_D=0;
    std::uint64_t D_tested=0;
    std::uint64_t candidate_xor=0;
    std::uint64_t candidate_sum=0;
    std::uint64_t pair_hash=14695981039346656037ULL;
    bool sat=false;
    Mask R=0,C=0,D=0,A=0;
};

std::uint64_t splitmix64(std::uint64_t x) {
    x+=0x9e3779b97f4a7c15ULL;
    x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;
    x=(x^(x>>27))*0x94d049bb133111ebULL;
    return x^(x>>31);
}

void fnv_word(std::uint64_t& h,Mask x) {
    h^=x&0xffu;h*=1099511628211ULL;
    h^=(x>>8)&0xffu;h*=1099511628211ULL;
}

bool verify_witness(Mask R,Mask C,Mask D,Mask A,int& B,int& W) {
    B=W=0;
    for (int r=0;r<N;++r) for (int c=0;c<N;++c) {
        int d=(r-c)&15,a=(r+c)&15;
        bool br=(R>>r)&1u,bc=(C>>c)&1u,bd=(D>>d)&1u,ba=(A>>a)&1u;
        B+=br&&bc&&bd&&ba;
        W+=!br&&!bc&&!bd&&!ba;
    }
    return B>=TARGET && W>=TARGET;
}

void incidence(
    Mask R,Mask C,
    std::array<int,16>& antiB,std::array<int,16>& antiW,
    std::array<std::array<std::uint8_t,16>,16>& cellB,
    std::array<std::array<std::uint8_t,16>,16>& cellW
) {
    antiB.fill(0);antiW.fill(0);
    for (auto& x:cellB) x.fill(0);
    for (auto& x:cellW) x.fill(0);
    for (int r=0;r<N;++r) for (int c=0;c<N;++c) {
        int d=(r-c)&15,a=(r+c)&15;
        bool rb=(R>>r)&1u,cb=(C>>c)&1u;
        if (rb&&cb) {++antiB[a];++cellB[d][a];}
        if (!rb&&!cb) {++antiW[a];++cellW[d][a];}
    }
}

Stats search_type(
    const TypeDomain& td,
    const std::vector<std::pair<Mask,Mask>>& reps,
    const MaskTables& masks
) {
    Stats total;
    total.pair_reps=reps.size();
    total.logical_A=static_cast<std::uint64_t>(reps.size())*td.A_masks_per_pair;

    std::atomic<bool> found{false};
    Mask foundR=0,foundC=0,foundD=0,foundA=0;

    #pragma omp parallel
    {
        Stats local;
        #pragma omp for schedule(dynamic,16)
        for (std::size_t i=0;i<reps.size();++i) {
            if (found.load(std::memory_order_relaxed)) continue;
            auto [R,C]=reps[i];

            std::array<int,16> antiB{},antiW{};
            std::array<std::array<std::uint8_t,16>,16> cellB{},cellW{};
            incidence(R,C,antiB,antiW,cellB,cellW);
            int all_white=std::accumulate(antiW.begin(),antiW.end(),0);
            int white_selected_cap=all_white-TARGET;

            std::array<std::uint8_t,256> eB{},eW{},oB{},oW{};
            for (int s=1;s<256;++s) {
                int bit=std::countr_zero(static_cast<unsigned>(s));
                int prev=s&(s-1);
                eB[s]=static_cast<std::uint8_t>(eB[prev]+antiB[2*bit]);
                eW[s]=static_cast<std::uint8_t>(eW[prev]+antiW[2*bit]);
                oB[s]=static_cast<std::uint8_t>(oB[prev]+antiB[2*bit+1]);
                oW[s]=static_cast<std::uint8_t>(oW[prev]+antiW[2*bit+1]);
            }

            std::array<std::vector<WeightedSubset>,9> even,odd;
            for (int s=0;s<256;++s) {
                int k=masks.cardinality[s];
                even[k].push_back({masks.even_mask[s],eB[s],eW[s]});
                odd[k].push_back({masks.odd_mask[s],oB[s],oW[s]});
            }

            for (auto [a0,a1]:td.a_counts) {
                for (const auto& e:even[a0]) for (const auto& o:odd[a1]) {
                    ++local.A_tested;
                    int tripleB=e.black+o.black;
                    int selectedW=e.selected_white+o.selected_white;
                    if (tripleB<TARGET || selectedW>white_selected_cap) continue;

                    ++local.scalar_survivors;
                    Mask A=Mask(e.mask|o.mask);
                    std::uint64_t cid=splitmix64(
                        std::uint64_t(R)|(std::uint64_t(C)<<16)|(std::uint64_t(A)<<32)
                    );
                    local.candidate_xor^=cid;
                    local.candidate_sum+=cid;

                    std::array<int,16> p{},q{};
                    for (int d=0;d<N;++d) {
                        for (int a=0;a<N;++a) {
                            if ((A>>a)&1u) p[d]+=cellB[d][a];
                            else q[d]+=cellW[d][a];
                        }
                    }
                    if (std::accumulate(p.begin(),p.end(),0)!=tripleB ||
                        std::accumulate(q.begin(),q.end(),0)!=all_white-selectedW) {
                        std::cerr<<"scalar/detail mismatch\n";
                        std::abort();
                    }
                    int q_limit=std::accumulate(q.begin(),q.end(),0)-TARGET;

                    for (DCounts dc:td.d_for_a[9*a0+a1]) {
                        ++local.d_count_cases;
                        const auto& Ddomain=masks.by_parity_count[9*dc.even+dc.odd];
                        local.logical_D+=Ddomain.size();
                        for (Mask D:Ddomain) {
                            ++local.D_tested;
                            int black=0,selected_q=0;
                            for (int d=0;d<N;++d) if ((D>>d)&1u) {
                                black+=p[d];
                                selected_q+=q[d];
                            }
                            if (black<TARGET || selected_q>q_limit) continue;

                            int B=0,W=0;
                            if (!verify_witness(R,C,D,A,B,W)) {
                                std::cerr<<"recovered witness failed verification\n";
                                std::abort();
                            }
                            bool expected=false;
                            if (found.compare_exchange_strong(expected,true)) {
                                foundR=R;foundC=C;foundD=D;foundA=A;
                            }
                            break;
                        }
                        if (found.load(std::memory_order_relaxed)) break;
                    }
                    if (found.load(std::memory_order_relaxed)) break;
                }
                if (found.load(std::memory_order_relaxed)) break;
            }
        }

        #pragma omp critical
        {
            total.A_tested+=local.A_tested;
            total.scalar_survivors+=local.scalar_survivors;
            total.d_count_cases+=local.d_count_cases;
            total.logical_D+=local.logical_D;
            total.D_tested+=local.D_tested;
            total.candidate_xor^=local.candidate_xor;
            total.candidate_sum+=local.candidate_sum;
        }
    }

    for (auto [R,C]:reps) {fnv_word(total.pair_hash,R);fnv_word(total.pair_hash,C);}
    total.sat=found.load();
    total.R=foundR;total.C=foundC;total.D=foundD;total.A=foundA;
    return total;
}

std::string hex64(std::uint64_t x) {
    std::ostringstream s;
    s<<std::hex<<std::setfill('0')<<std::setw(16)<<x;
    return s.str();
}

} // namespace union_enum

int main(int argc,char** argv) {
    using namespace union_enum;
    std::string output="peace16_union_certificate.tsv";
    for (int i=1;i<argc;++i) {
        std::string a=argv[i];
        if (a=="--output" && i+1<argc) output=argv[++i];
        else {
            std::cerr<<"usage: "<<argv[0]<<" [--output certificate.tsv]\n";
            return 2;
        }
    }

    double start=omp_get_wtime();
    MaskTables masks;
    int ordered=0;
    auto types=build_domain(ordered);
    const std::set<std::pair<int,int>> expected{
        {5,7},{5,8},{6,6},{6,7},{6,8},{7,7},{7,8}
    };
    std::set<std::pair<int,int>> actual;
    for (const auto& [k,v]:types) actual.insert(k);
    if (ordered!=1898 || actual!=expected) {
        std::cerr<<"profile-domain gate failed\n";
        return 3;
    }

    std::map<int,std::vector<Mask>> neck;
    for (int k=5;k<=8;++k) neck[k]=necklaces(k);

    std::ofstream cert(output);
    cert<<"r\tc\tA_count_pairs\tpair_reps\tpair_hash\tlogical_A\tA_tested"
           "\tscalar_survivors\tcandidate_xor\tcandidate_sum\td_count_cases"
           "\tlogical_D\tD_tested\tresult\tseconds\n";

    std::uint64_t reps_total=0,logical_A_total=0,A_total=0,scalar_total=0;
    std::uint64_t dc_total=0,logical_D_total=0,D_total=0,xor_total=0,sum_total=0;

    for (const auto& [key,td]:types) {
        auto [r,c]=key;
        auto reps=pair_transversal(r,c,neck[r],neck[c]);
        double t0=omp_get_wtime();
        Stats st=search_type(td,reps,masks);
        double sec=omp_get_wtime()-t0;
        std::string result=st.sat?"SAT":"UNSAT";

        cert<<r<<'\t'<<c<<'\t'<<td.a_counts.size()<<'\t'
            <<st.pair_reps<<'\t'<<hex64(st.pair_hash)<<'\t'
            <<st.logical_A<<'\t'<<st.A_tested<<'\t'
            <<st.scalar_survivors<<'\t'<<hex64(st.candidate_xor)<<'\t'
            <<hex64(st.candidate_sum)<<'\t'<<st.d_count_cases<<'\t'
            <<st.logical_D<<'\t'<<st.D_tested<<'\t'<<result<<'\t'
            <<std::fixed<<std::setprecision(6)<<sec<<'\n';
        cert.flush();

        std::cerr<<"TYPE "<<r<<','<<c
                 <<" reps="<<st.pair_reps
                 <<" A="<<st.A_tested
                 <<" scalar="<<st.scalar_survivors
                 <<" d_cases="<<st.d_count_cases
                 <<" D="<<st.D_tested
                 <<" result="<<result
                 <<" sec="<<std::fixed<<std::setprecision(3)<<sec<<"\n";

        reps_total+=st.pair_reps;logical_A_total+=st.logical_A;A_total+=st.A_tested;
        scalar_total+=st.scalar_survivors;dc_total+=st.d_count_cases;
        logical_D_total+=st.logical_D;D_total+=st.D_tested;
        xor_total^=st.candidate_xor;sum_total+=st.candidate_sum;

        if (st.sat) {
            int B=0,W=0;
            verify_witness(st.R,st.C,st.D,st.A,B,W);
            cert<<"# WITNESS "<<st.R<<' '<<st.C<<' '<<st.D<<' '<<st.A
                <<" B="<<B<<" W="<<W<<"\n";
            return 10;
        }
    }

    if (logical_A_total!=A_total || logical_D_total!=D_total) {
        std::cerr<<"exhaustiveness counter mismatch\n";
        return 4;
    }

    double elapsed=omp_get_wtime()-start;
    cert<<"# TOTAL profiles=1898 pair_reps="<<reps_total
        <<" logical_A="<<logical_A_total<<" A_tested="<<A_total
        <<" scalar="<<scalar_total<<" candidate_xor="<<hex64(xor_total)
        <<" candidate_sum="<<hex64(sum_total)<<" d_cases="<<dc_total
        <<" logical_D="<<logical_D_total<<" D_tested="<<D_total
        <<" result=UNSAT elapsed="<<elapsed<<"\n";

    std::cerr<<"ALL_UNSAT profiles=1898 pair_reps="<<reps_total
             <<" logical_A="<<logical_A_total<<" A_tested="<<A_total
             <<" scalar="<<scalar_total<<" candidate_xor="<<hex64(xor_total)
             <<" candidate_sum="<<hex64(sum_total)<<" d_cases="<<dc_total
             <<" logical_D="<<logical_D_total<<" D_tested="<<D_total
             <<" elapsed="<<std::fixed<<std::setprecision(3)<<elapsed
             <<" threads="<<omp_get_max_threads()<<"\n";
    return 0;
}
