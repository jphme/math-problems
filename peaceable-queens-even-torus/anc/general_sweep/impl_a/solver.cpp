#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <optional>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "sha256.hpp"

// Independent implementation of the even-order line-colouring enumeration
// described in BRIEF-2026-07-25-general-n.md.  It deliberately uses no code
// from either earlier n=16 solver.

namespace pq {

using Mask = std::uint32_t;
using Count = std::uint64_t;
constexpr int INF = 1'000'000'000;

struct Config {
    int n = 16;
    int tau = 33;
};

struct Profile {
    int r{}, c{}, d0{}, d1{}, a0{}, a1{};
    auto tie() const { return std::tie(r, c, d0, d1, a0, a1); }
    bool operator<(const Profile& o) const { return tie() < o.tie(); }
    bool operator==(const Profile& o) const { return tie() == o.tie(); }
    int sum() const { return r + c + d0 + d1 + a0 + a1; }
};

std::string profile_string(const Profile& p) {
    std::ostringstream out;
    out << p.r << ',' << p.c << ',' << p.d0 << ',' << p.d1 << ','
        << p.a0 << ',' << p.a1;
    return out.str();
}

Profile swap_rc(Profile p) {
    std::swap(p.r, p.c);
    return p;
}
Profile swap_da(Profile p) {
    std::swap(p.d0, p.a0);
    std::swap(p.d1, p.a1);
    return p;
}
Profile flip_parity(Profile p) {
    std::swap(p.d0, p.d1);
    std::swap(p.a0, p.a1);
    return p;
}

Count choose(int n, int k) {
    if (k < 0 || k > n) return 0;
    k = std::min(k, n - k);
    Count ans = 1;
    for (int i = 1; i <= k; ++i) ans = ans * Count(n - k + i) / Count(i);
    return ans;
}

bool valid_profile(const Config& cfg, const Profile& p) {
    const int n = cfg.n, h = n / 2, t = cfg.tau;
    const int d = p.d0 + p.d1, a = p.a0 + p.a1;
    if (p.r < 0 || p.r > n || p.c < 0 || p.c > n ||
        p.d0 < 0 || p.d0 > h || p.d1 < 0 || p.d1 > h ||
        p.a0 < 0 || p.a0 > h || p.a1 < 0 || p.a1 > h ||
        p.sum() > 2 * n) return false;
    for (auto [x, y] : std::array<std::pair<int,int>,5>{{
             {p.r,p.c},{p.r,d},{p.r,a},{p.c,d},{p.c,a}}}) {
        if (x * y < t || (n - x) * (n - y) < t) return false;
    }
    const int da = p.d0 * p.a0 + p.d1 * p.a1;
    if (2 * da < t) return false;
    if (2 * ((h-p.d0)*(h-p.a0) + (h-p.d1)*(h-p.a1)) < t) return false;
    for (int z : {d, a}) {
        if (n*n - n*(p.r+p.c+z) + p.r*p.c + p.r*z + p.c*z < 2*t)
            return false;
    }
    for (int x : {p.r, p.c}) {
        if (n*n - n*(x+d+a) + x*d + x*a + 2*da < 2*t)
            return false;
    }
    return true;
}

Profile complement_profile(Profile p,int n) {
    const int h=n/2;
    return {n-p.r,n-p.c,h-p.d0,h-p.d1,h-p.a0,h-p.a1};
}

Profile canonical_profile(Profile p,int n) {
    Profile best = p;
    std::vector<Profile> bases{p};
    if(p.sum()==2*n)bases.push_back(complement_profile(p,n));
    for(const Profile&base:bases)
      for (int rc = 0; rc < 2; ++rc)
       for (int da = 0; da < 2; ++da)
        for (int fl = 0; fl < 2; ++fl) {
            Profile q = base;
            if (rc) q = swap_rc(q);
            if (da) q = swap_da(q);
            if (fl) q = flip_parity(q);
            best = std::min(best, q);
        }
    return best;
}

struct Job {
    Profile canonical;
    Profile oriented;
    bool sign{};
};

std::vector<Job> make_jobs(const Config& cfg, Count* ordered_count = nullptr) {
    if (cfg.n % 2) throw std::runtime_error("C1 engine currently requires even n");
    const int h = cfg.n / 2;
    std::set<Profile> canon;
    Count ordered = 0;
    for (int r = 0; r <= cfg.n; ++r)
      for (int c = 0; c <= cfg.n; ++c)
       for (int d0 = 0; d0 <= h; ++d0)
        for (int d1 = 0; d1 <= h; ++d1)
         for (int a0 = 0; a0 <= h; ++a0)
          for (int a1 = 0; a1 <= h; ++a1) {
              Profile p{r,c,d0,d1,a0,a1};
              if (!valid_profile(cfg,p)) continue;
              ++ordered;
              canon.insert(canonical_profile(p,cfg.n));
          }
    if (ordered_count) *ordered_count = ordered;
    std::vector<Job> jobs;
    for (const Profile& cp : canon) {
        Profile q = cp, q2 = swap_da(cp);
        auto cost_key = [h](const Profile& x) {
            return std::pair<Count,Profile>{choose(h,x.a0)*choose(h,x.a1),x};
        };
        if (cost_key(q2) < cost_key(q)) q = q2;
        std::vector<Profile> oriented{q};
        Profile f = flip_parity(q);
        if (!(f == q)) oriented.push_back(f);
        std::sort(oriented.begin(), oriented.end());
        for (const Profile& o : oriented)
            jobs.push_back(Job{cp,o,o.d0 == o.a0 && o.d1 == o.a1});
    }
    std::sort(jobs.begin(), jobs.end(), [](const Job& x, const Job& y) {
        return std::tuple{x.canonical.sum(),x.canonical,x.oriented} <
               std::tuple{y.canonical.sum(),y.canonical,y.oriented};
    });
    return jobs;
}

struct OddProfile {
    int r{},c{},d{},a{};
    auto tie() const{return std::tie(r,c,d,a);}
    bool operator<(const OddProfile&o)const{return tie()<o.tie();}
    bool operator==(const OddProfile&o)const{return tie()==o.tie();}
    int sum()const{return r+c+d+a;}
};

std::string profile_string(const OddProfile&p) {
    std::ostringstream out;out<<p.r<<','<<p.c<<','<<p.d<<','<<p.a;return out.str();
}

std::set<OddProfile> odd_profile_orbit(OddProfile p,int n) {
    std::set<OddProfile> out;
    std::vector<OddProfile>bases{p};
    if(p.sum()==2*n)bases.push_back({n-p.r,n-p.c,n-p.d,n-p.a});
    for(const auto&base:bases)
      for(int block=0;block<2;++block)
       for(int rc=0;rc<2;++rc)
        for(int da=0;da<2;++da) {
            OddProfile q=base;
            if(rc)std::swap(q.r,q.c);
            if(da)std::swap(q.d,q.a);
            if(block){std::swap(q.r,q.d);std::swap(q.c,q.a);}
            out.insert(q);
        }
    return out;
}

bool valid_odd_profile(const Config&cfg,const OddProfile&p) {
    const int n=cfg.n,t=cfg.tau;
    std::array<int,4>s{{p.r,p.c,p.d,p.a}};
    if(p.sum()>2*n)return false;
    for(int i=0;i<4;++i)for(int j=0;j<i;++j)
        if(s[i]*s[j]<t||(n-s[i])*(n-s[j])<t)return false;
    for(int omit=0;omit<4;++omit) {
        std::array<int,3>x{};int k=0;
        for(int i=0;i<4;++i)if(i!=omit)x[k++]=s[i];
        if(n*n-n*(x[0]+x[1]+x[2])+x[0]*x[1]+x[0]*x[2]+x[1]*x[2]<2*t)
            return false;
    }
    return true;
}

struct OddJob {OddProfile canonical,oriented;bool sign{};};

std::vector<OddJob> make_odd_jobs(const Config&cfg,Count*ordered_count=nullptr) {
    std::set<OddProfile>canon;Count ordered=0;
    for(int r=0;r<=cfg.n;++r)for(int c=0;c<=cfg.n;++c)
     for(int d=0;d<=cfg.n;++d)for(int a=0;a<=cfg.n;++a) {
        OddProfile p{r,c,d,a};
        if(!valid_odd_profile(cfg,p))continue;
        ++ordered;canon.insert(*odd_profile_orbit(p,cfg.n).begin());
     }
    if(ordered_count)*ordered_count=ordered;
    std::vector<OddJob>jobs;
    for(const auto&cp:canon) {
        const auto orbit=odd_profile_orbit(cp,cfg.n);
        auto cost=[&](const OddProfile&q) {
            Count raw=choose(cfg.n,q.r)*choose(cfg.n,q.c)*choose(cfg.n,q.a);
            if(q.r==q.c)raw/=2;
            if(q.d==q.a)raw/=2;
            return std::pair<Count,OddProfile>{raw,q};
        };
        OddProfile best=*std::min_element(orbit.begin(),orbit.end(),
            [&](const OddProfile&x,const OddProfile&y){return cost(x)<cost(y);});
        jobs.push_back({cp,best,best.d==best.a});
    }
    std::sort(jobs.begin(),jobs.end(),[](const OddJob&x,const OddJob&y){
        return std::tuple{x.canonical.sum(),x.canonical,x.oriented}<
               std::tuple{y.canonical.sum(),y.canonical,y.oriented};
    });
    return jobs;
}

Mask affine_mask(Mask m, int mult, int add, int n) {
    Mask out = 0;
    for (int x = 0; x < n; ++x)
        if ((m >> x) & 1U)
            out |= Mask(1) << ((mult * x + add) % n);
    return out;
}

Mask necklace(Mask m, int n) {
    Mask best = m;
    for (int b = 1; b < n; ++b) best = std::min(best, affine_mask(m,1,b,n));
    return best;
}

std::vector<Mask> necklaces_of_size(int n, int k) {
    if (n > 24) throw std::runtime_error("subset necklace generation is limited to n<=24");
    std::vector<Mask> out;
    const std::uint64_t lim = std::uint64_t(1) << n;
    for (std::uint64_t x = 0; x < lim; ++x) {
        Mask m = Mask(x);
        if (std::popcount(m) == k && necklace(m,n) == m) out.push_back(m);
    }
    return out;
}

struct PairType {
    int r{}, c{};
    bool sign{};
    auto tie() const { return std::tie(r,c,sign); }
    bool operator<(const PairType& o) const { return tie() < o.tie(); }
};
struct PairRep { Mask r{}, c{}; };

std::vector<int> units_mod(int n) {
    std::vector<int> out;
    for (int u = 1; u < n; ++u) if (std::gcd(u,n) == 1) out.push_back(u);
    return out;
}

std::vector<PairRep> pair_representatives(
        int n, const PairType& type,
        const std::vector<Mask>& nr, const std::vector<Mask>& nc) {
    const auto units = units_mod(n);
    std::vector<std::vector<Mask>> ar(units.size(), std::vector<Mask>(nr.size()));
    std::vector<std::vector<Mask>> ac(units.size(), std::vector<Mask>(nc.size()));
    for (std::size_t ui=0; ui<units.size(); ++ui) {
        for (std::size_t i=0; i<nr.size(); ++i)
            ar[ui][i] = necklace(affine_mask(nr[i],units[ui],0,n),n);
        for (std::size_t i=0; i<nc.size(); ++i)
            ac[ui][i] = necklace(affine_mask(nc[i],units[ui],0,n),n);
    }
    std::vector<int> neg(units.size());
    for (std::size_t ui=0; ui<units.size(); ++ui) {
        const int want = (n - units[ui]) % n;
        neg[ui] = int(std::find(units.begin(),units.end(),want)-units.begin());
    }
    const bool transpose = type.r == type.c;
    std::vector<PairRep> reps;
    for (std::size_t i=0; i<nr.size(); ++i) {
        for (std::size_t j=0; j<nc.size(); ++j) {
            std::pair<Mask,Mask> original{nr[i],nc[j]}, best=original;
            for (std::size_t ui=0; ui<units.size(); ++ui) {
                auto consider = [&](Mask x, Mask y) {
                    best = std::min(best,std::pair<Mask,Mask>{x,y});
                    if (transpose) best=std::min(best,std::pair<Mask,Mask>{y,x});
                };
                consider(ar[ui][i],ac[ui][j]);
                if (type.sign) consider(ar[ui][i],ac[neg[ui]][j]);
            }
            if (original == best) reps.push_back(PairRep{nr[i],nc[j]});
        }
    }
    return reps;
}

// SHA-256 over one stable textual line per representative.
std::string orbit_fingerprint(const std::vector<PairRep>& reps) {
    Sha256 hash;
    for (const auto& p : reps) {
        std::ostringstream s;
        s << std::hex << std::setw(8) << std::setfill('0') << p.r << ','
          << std::setw(8) << p.c << '\n';
        hash.update(s.str());
    }
    return hash.hex_digest();
}

struct SuffixBounds {
    int h{};
    std::vector<std::vector<int>> maxp, minq;
};

SuffixBounds make_bounds(const std::vector<int>& pv, const std::vector<int>& qv) {
    const int h = int(pv.size());
    SuffixBounds b;
    b.h=h;
    b.maxp.assign(h+1,std::vector<int>(h+1,-INF));
    b.minq.assign(h+1,std::vector<int>(h+1,INF));
    b.maxp[h][0]=0; b.minq[h][0]=0;
    for (int pos=h-1; pos>=0; --pos) {
        for (int k=0; k<=h-pos; ++k) {
            b.maxp[pos][k]=b.maxp[pos+1][k];
            b.minq[pos][k]=b.minq[pos+1][k];
            if (k && b.maxp[pos+1][k-1]>-INF)
                b.maxp[pos][k]=std::max(b.maxp[pos][k],
                                        pv[pos]+b.maxp[pos+1][k-1]);
            if (k && b.minq[pos+1][k-1]<INF)
                b.minq[pos][k]=std::min(b.minq[pos][k],
                                        qv[pos]+b.minq[pos+1][k-1]);
        }
    }
    return b;
}

struct PairData {
    int n{}, h{};
    std::vector<std::vector<std::uint8_t>> P,Q;
    std::vector<int> colp,colq,rowq;
    std::array<std::vector<int>,2> labels,pv,qv;
    std::array<SuffixBounds,2> bounds;
};

PairData make_pair_data(int n, Mask rm, Mask cm) {
    PairData x;
    x.n=n; x.h=n/2;
    x.P.assign(n,std::vector<std::uint8_t>(n));
    x.Q.assign(n,std::vector<std::uint8_t>(n));
    x.colp.assign(n,0); x.colq.assign(n,0); x.rowq.assign(n,0);
    for (int r=0;r<n;++r) for (int c=0;c<n;++c) {
        int d=(r-c+n)%n, a=(r+c)%n;
        if (((rm>>r)&1U) && ((cm>>c)&1U)) ++x.P[d][a];
        if (!((rm>>r)&1U) && !((cm>>c)&1U)) ++x.Q[d][a];
    }
    for (int d=0;d<n;++d) for (int a=0;a<n;++a) {
        x.colp[a]+=x.P[d][a]; x.colq[a]+=x.Q[d][a]; x.rowq[d]+=x.Q[d][a];
    }
    for (int parity=0;parity<2;++parity) {
        for (int a=parity;a<n;a+=2) {
            x.labels[parity].push_back(a);
            x.pv[parity].push_back(x.colp[a]);
            x.qv[parity].push_back(x.colq[a]);
        }
        x.bounds[parity]=make_bounds(x.pv[parity],x.qv[parity]);
    }
    return x;
}

struct EmitStats { Count nodes{}, emitted{}; };

template<class Callback>
class AEmitter {
public:
    AEmitter(const PairData& x, int k0, int k1, int tau, Callback& cb)
      : x_(x), k_{k0,k1}, tau_(tau), cb_(cb) {
        totalq_=std::accumulate(x.colq.begin(),x.colq.end(),0);
        capq_=totalq_-tau_;
    }
    EmitStats run() {
        if (capq_ < 0) return stats_;
        const auto& e=x_.bounds[0]; const auto& o=x_.bounds[1];
        if (e.maxp[0][k_[0]] + o.maxp[0][k_[1]] < tau_) return stats_;
        if (e.minq[0][k_[0]] + o.minq[0][k_[1]] > capq_) return stats_;
        dfs_even(0,k_[0],0,0,0);
        return stats_;
    }
private:
    const PairData& x_;
    std::array<int,2> k_;
    int tau_,totalq_,capq_;
    Callback& cb_;
    EmitStats stats_;

    void dfs_even(int pos,int rem,int ps,int qs,Mask mask) {
        ++stats_.nodes;
        const auto& b=x_.bounds[0]; const auto& o=x_.bounds[1];
        if (rem<0 || rem>x_.h-pos) return;
        if (ps+b.maxp[pos][rem]+o.maxp[0][k_[1]]<tau_) return;
        if (qs+b.minq[pos][rem]+o.minq[0][k_[1]]>capq_) return;
        if (pos==x_.h) {
            if (rem==0) dfs_odd(0,k_[1],ps,qs,mask);
            return;
        }
        dfs_even(pos+1,rem,ps,qs,mask);
        const int a=x_.labels[0][pos];
        dfs_even(pos+1,rem-1,ps+x_.colp[a],qs+x_.colq[a],
                 mask|(Mask(1)<<a));
    }
    void dfs_odd(int pos,int rem,int ps,int qs,Mask mask) {
        ++stats_.nodes;
        const auto& b=x_.bounds[1];
        if (rem<0 || rem>x_.h-pos) return;
        if (ps+b.maxp[pos][rem]<tau_ || qs+b.minq[pos][rem]>capq_) return;
        if (pos==x_.h) {
            if (rem==0 && ps>=tau_ && qs<=capq_) {
                ++stats_.emitted; cb_(mask);
            }
            return;
        }
        dfs_odd(pos+1,rem,ps,qs,mask);
        const int a=x_.labels[1][pos];
        dfs_odd(pos+1,rem-1,ps+x_.colp[a],qs+x_.colq[a],
                mask|(Mask(1)<<a));
    }
};

template<class Callback>
EmitStats emit_antidiagonals(const PairData& x,int a0,int a1,int tau,Callback&& cb) {
    using Cb=std::remove_reference_t<Callback>;
    Cb& ref=cb;
    AEmitter<Cb> emitter(x,a0,a1,tau,ref);
    return emitter.run();
}

struct CompletionResult { bool sat{}; Mask mask{}; Count nodes{}; };

class CompletionSearch {
public:
    CompletionSearch(const std::vector<int>& p,const std::vector<int>& q,
                     int k0,int k1,int tau,int q0)
      : p_(p),q_(q),n_(int(p.size())),h_(n_/2),k_{k0,k1},
        tau_(tau),capq_(q0-tau) {
        for(int parity=0;parity<2;++parity) {
            for(int d=parity;d<n_;d+=2) {
                label_[parity].push_back(d);
                pv_[parity].push_back(p[d]);
                qv_[parity].push_back(q[d]);
            }
            b_[parity]=make_bounds(pv_[parity],qv_[parity]);
        }
    }
    CompletionResult run() {
        if(capq_<0) return result_;
        if(b_[0].maxp[0][k_[0]]+b_[1].maxp[0][k_[1]]<tau_) return result_;
        if(b_[0].minq[0][k_[0]]+b_[1].minq[0][k_[1]]>capq_) return result_;
        dfs(0,0,k_[0],k_[1],0,0,0);
        return result_;
    }
private:
    const std::vector<int>& p_; const std::vector<int>& q_;
    int n_,h_; std::array<int,2> k_; int tau_,capq_;
    std::array<std::vector<int>,2> label_,pv_,qv_;
    std::array<SuffixBounds,2> b_;
    CompletionResult result_;
    bool dfs(int phase,int pos,int r0,int r1,int ps,int qs,Mask mask) {
        ++result_.nodes;
        int rem=phase?r1:r0;
        if(rem<0 || rem>h_-pos) return false;
        int maxp=ps+b_[phase].maxp[pos][rem];
        int minq=qs+b_[phase].minq[pos][rem];
        if(!phase) {
            maxp+=b_[1].maxp[0][r1];
            minq+=b_[1].minq[0][r1];
        }
        if(maxp<tau_ || minq>capq_) return false;
        if(pos==h_) {
            if(rem) return false;
            if(!phase) return dfs(1,0,0,r1,ps,qs,mask);
            if(ps>=tau_ && qs<=capq_) {
                result_.sat=true; result_.mask=mask; return true;
            }
            return false;
        }
        if(dfs(phase,pos+1,r0,r1,ps,qs,mask)) return true;
        const int d=label_[phase][pos];
        if(phase) --r1; else --r0;
        return dfs(phase,pos+1,r0,r1,ps+p_[d],qs+q_[d],mask|(Mask(1)<<d));
    }
};

CompletionResult exact_completion(const std::vector<int>& p,const std::vector<int>& q,
                                  int d0,int d1,int tau,int q0) {
    return CompletionSearch(p,q,d0,d1,tau,q0).run();
}

template<class Callback>
class FixedCardinalityEmitter {
public:
    FixedCardinalityEmitter(const std::vector<int>&p,const std::vector<int>&q,
                            int k,int tau,Callback&cb)
      :p_(p),q_(q),n_(int(p.size())),k_(k),tau_(tau),cb_(cb),
       bounds_(make_bounds(p,q)) {
        totalq_=std::accumulate(q.begin(),q.end(),0);capq_=totalq_-tau;
    }
    EmitStats run() {
        if(capq_<0||bounds_.maxp[0][k_]<tau_||bounds_.minq[0][k_]>capq_)
            return stats_;
        dfs(0,k_,0,0,0);return stats_;
    }
private:
    const std::vector<int>&p_;const std::vector<int>&q_;
    int n_,k_,tau_,totalq_,capq_;Callback&cb_;SuffixBounds bounds_;
    EmitStats stats_;
    void dfs(int pos,int rem,int ps,int qs,Mask mask) {
        ++stats_.nodes;
        if(rem<0||rem>n_-pos)return;
        if(ps+bounds_.maxp[pos][rem]<tau_||qs+bounds_.minq[pos][rem]>capq_)return;
        if(pos==n_) {
            if(!rem&&ps>=tau_&&qs<=capq_){++stats_.emitted;cb_(mask);}
            return;
        }
        dfs(pos+1,rem,ps,qs,mask);
        dfs(pos+1,rem-1,ps+p_[pos],qs+q_[pos],mask|(Mask(1)<<pos));
    }
};

template<class Callback>
EmitStats emit_fixed_cardinality(const std::vector<int>&p,const std::vector<int>&q,
                                 int k,int tau,Callback&&cb) {
    using Cb=std::remove_reference_t<Callback>;Cb&ref=cb;
    FixedCardinalityEmitter<Cb> emitter(p,q,k,tau,ref);return emitter.run();
}

class FixedCompletionSearch {
public:
    FixedCompletionSearch(const std::vector<int>&p,const std::vector<int>&q,
                          int k,int tau,int q0)
      :p_(p),q_(q),n_(int(p.size())),k_(k),tau_(tau),capq_(q0-tau),
       bounds_(make_bounds(p,q)) {}
    CompletionResult run() {
        if(capq_<0||bounds_.maxp[0][k_]<tau_||bounds_.minq[0][k_]>capq_)
            return result_;
        dfs(0,k_,0,0,0);return result_;
    }
private:
    const std::vector<int>&p_;const std::vector<int>&q_;
    int n_,k_,tau_,capq_;SuffixBounds bounds_;CompletionResult result_;
    bool dfs(int pos,int rem,int ps,int qs,Mask mask) {
        ++result_.nodes;
        if(rem<0||rem>n_-pos)return false;
        if(ps+bounds_.maxp[pos][rem]<tau_||qs+bounds_.minq[pos][rem]>capq_)return false;
        if(pos==n_) {
            if(!rem&&ps>=tau_&&qs<=capq_){
                result_.sat=true;result_.mask=mask;return true;
            }
            return false;
        }
        if(dfs(pos+1,rem,ps,qs,mask))return true;
        return dfs(pos+1,rem-1,ps+p_[pos],qs+q_[pos],
                   mask|(Mask(1)<<pos));
    }
};

CompletionResult exact_fixed_completion(const std::vector<int>&p,const std::vector<int>&q,
                                        int k,int tau,int q0) {
    return FixedCompletionSearch(p,q,k,tau,q0).run();
}

std::pair<int,int> direct_counts(int n,Mask R,Mask C,Mask D,Mask A) {
    int B=0,W=0;
    for(int r=0;r<n;++r) for(int c=0;c<n;++c) {
        int d=(r-c+n)%n,a=(r+c)%n;
        bool rb=(R>>r)&1U,cb=(C>>c)&1U,db=(D>>d)&1U,ab=(A>>a)&1U;
        B += rb&&cb&&db&&ab;
        W += !rb&&!cb&&!db&&!ab;
    }
    return {B,W};
}

Mask setmask(std::initializer_list<int> xs) {
    Mask m=0; for(int x:xs)m|=Mask(1)<<x; return m;
}

bool brute_completion(const std::vector<int>& p,const std::vector<int>& q,
                      int k0,int k1,int tau,int q0) {
    int n=int(p.size());
    for(std::uint64_t m=0;m<(std::uint64_t(1)<<n);++m) {
        int c0=0,c1=0,ps=0,qs=0;
        for(int d=0;d<n;++d) if((m>>d)&1U) {
            (d&1?c1:c0)++; ps+=p[d]; qs+=q[d];
        }
        if(c0==k0&&c1==k1&&ps>=tau&&qs<=q0-tau)return true;
    }
    return false;
}

bool brute_fixed_completion(const std::vector<int>&p,const std::vector<int>&q,
                            int k,int tau,int q0) {
    const int n=int(p.size());
    for(std::uint64_t m=0;m<(std::uint64_t(1)<<n);++m) {
        if(std::popcount(m)!=k)continue;
        int ps=0,qs=0;
        for(int i=0;i<n;++i)if((m>>i)&1U){ps+=p[i];qs+=q[i];}
        if(ps>=tau&&qs<=q0-tau)return true;
    }
    return false;
}

void self_tests() {
    {
        Sha256 empty;
        if (empty.hex_digest() !=
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
            throw std::runtime_error("SHA-256 empty-vector self-test failed");
        Sha256 abc; abc.update(std::string("abc"));
        if (abc.hex_digest() !=
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
            throw std::runtime_error("SHA-256 abc-vector self-test failed");
    }
    auto check_witness=[](int n,Mask r,Mask c,Mask d,Mask a,int eb,int ew) {
        auto[b,w]=direct_counts(n,r,c,d,a);
        if(b!=eb||w!=ew)throw std::runtime_error(
            "witness self-test failed at n="+std::to_string(n));
    };
    check_witness(5,setmask({0}),setmask({0,4}),setmask({0,1}),
                    setmask({0,4}),2,2);
    check_witness(6,setmask({1,3,4}),setmask({1,2,3}),setmask({1,3,5}),
                    setmask({1,3,5}),4,5);
    check_witness(7,setmask({1,5,6}),setmask({3,5,6}),setmask({0,1,3,4}),
                    setmask({2,3,4,5}),4,4);
    check_witness(8,setmask({2,5,6,7}),setmask({1,2,5,6}),setmask({1,3,5,7}),
                    setmask({1,3,5,7}),8,8);
    check_witness(9,setmask({1,2,4,5}),setmask({1,2,4,5}),setmask({0,1,3,8}),
                    setmask({0,3,4,5,8}),7,7);
    check_witness(10,setmask({2,6,7,8}),setmask({3,5,7,8,9}),
                    setmask({1,3,5,7,9}),setmask({1,3,5,7,9}),13,12);
    check_witness(11,setmask({3,5,6,8,10}),setmask({2,3,4,5,6,7}),
                    setmask({0,1,3,8,9}),setmask({1,5,6,7,9}),10,10);
    check_witness(12,setmask({2,3,4,6,7,8}),setmask({1,2,4,5,6,7}),
                    setmask({1,3,5,7,9,11}),setmask({1,3,5,7,9,11}),18,18);
    check_witness(13,setmask({0,2,3,5,9}),setmask({1,4,6,7,8,10,11,12}),
                    setmask({3,4,5,8,9,10}),setmask({0,1,2,8,9,10}),16,16);
    check_witness(14,setmask({2,6,8,10,12}),setmask({1,3,4,7,11,13}),
                    setmask({1,3,5,7,9,11,13}),setmask({1,3,5,7,9,11,13}),25,26);
    {
        auto [b,w]=direct_counts(15,setmask({5,7,8,11,12,14}),
             setmask({0,3,4,7,9,10,12,13}),setmask({0,1,4,8,12,13,14}),
             setmask({1,2,3,9,10,12,14}));
        if(b!=20||w!=22) throw std::runtime_error("n=15 witness self-test failed");
    }
    {
        Mask rc=setmask({5,7,9,11,13,15}), da=setmask({0,2,4,6,8,10,12,14});
        auto [b,w]=direct_counts(16,rc,rc,da,da);
        if(b!=36||w!=32) throw std::runtime_error("n=16 witness self-test failed");
    }
    {
        auto [b,w]=direct_counts(17,setmask({0,1,5,6,7,11,12,14,15}),
          setmask({1,5,6,8,9,11,12,16}),setmask({1,5,6,7,11,13,14,15,16}),
          setmask({1,5,7,11,13,14,15,16}));
        if(b!=28||w!=28) throw std::runtime_error("n=17 witness self-test failed");
    }
    {
        Mask da=setmask({0,2,4,6,8,10,12,14,16});
        auto [b,w]=direct_counts(18,setmask({1,3,7,9,11,15}),
          setmask({1,2,7,9,11,13,15,17}),da,da);
        if(b!=42||w!=42) throw std::runtime_error("n=18 witness self-test failed");
    }
    // Exhaustively verify the even two-lift incidence statement at n=16.
    for(int d=0;d<16;++d)for(int a=0;a<16;++a) {
        int count=0;
        for(int r=0;r<16;++r)for(int c=0;c<16;++c)
            count += ((r-c+16)%16==d && (r+c)%16==a);
        int want=((d^a)&1)?0:2;
        if(count!=want) throw std::runtime_error("two-lift self-test failed");
    }
    // Required >=100,000 deterministic random exact-kernel comparisons.
    std::mt19937 rng(0xC1A16U);
    for(int it=0;it<100000;++it) {
        int n=2+2*int(rng()%3); // 2,4,6: brute force remains cheap.
        std::vector<int> p(n),q(n);
        for(int i=0;i<n;++i){p[i]=int(rng()%(n+1));q[i]=int(rng()%(n+1));}
        int k0=int(rng()%(n/2+1)),k1=int(rng()%(n/2+1));
        int q0=std::accumulate(q.begin(),q.end(),0);
        int tau=int(rng()%(n*n+1));
        bool fast=exact_completion(p,q,k0,k1,tau,q0).sat;
        bool slow=brute_completion(p,q,k0,k1,tau,q0);
        if(fast!=slow) throw std::runtime_error("completion random self-test failed");
    }
    for(int it=0;it<100000;++it) {
        int n=2+int(rng()%6);
        std::vector<int>p(n),q(n);
        for(int i=0;i<n;++i){p[i]=int(rng()%(n+1));q[i]=int(rng()%(n+1));}
        int k=int(rng()%(n+1)),q0=std::accumulate(q.begin(),q.end(),0);
        int tau=int(rng()%(n*n+1));
        bool fast=exact_fixed_completion(p,q,k,tau,q0).sat;
        bool slow=brute_fixed_completion(p,q,k,tau,q0);
        if(fast!=slow)throw std::runtime_error("odd completion random self-test failed");
    }
    // Independent random A-emitter comparisons against mask brute force.
    for(int it=0;it<3000;++it) {
        PairData x; x.n=8;x.h=4;x.colp.resize(8);x.colq.resize(8);
        for(int a=0;a<8;++a){x.colp[a]=int(rng()%9);x.colq[a]=int(rng()%9);}
        for(int parity=0;parity<2;++parity) {
            for(int a=parity;a<8;a+=2) {
                x.labels[parity].push_back(a);x.pv[parity].push_back(x.colp[a]);
                x.qv[parity].push_back(x.colq[a]);
            }
            x.bounds[parity]=make_bounds(x.pv[parity],x.qv[parity]);
        }
        int k0=int(rng()%5),k1=int(rng()%5),tau=int(rng()%33);
        std::set<Mask> got,want;
        auto cb=[&](Mask m){got.insert(m);};
        emit_antidiagonals(x,k0,k1,tau,cb);
        int tq=std::accumulate(x.colq.begin(),x.colq.end(),0);
        for(Mask m=0;m<256;++m) {
            int c0=0,c1=0,ps=0,sq=0;
            for(int a=0;a<8;++a)if((m>>a)&1U){
                (a&1?c1:c0)++;ps+=x.colp[a];sq+=x.colq[a];
            }
            if(c0==k0&&c1==k1&&ps>=tau&&tq-sq>=tau)want.insert(m);
        }
        if(got!=want)throw std::runtime_error("A emitter random self-test failed");
    }
    for(int it=0;it<3000;++it) {
        const int n=7;std::vector<int>p(n),q(n);
        for(int i=0;i<n;++i){p[i]=int(rng()%8);q[i]=int(rng()%8);}
        int k=int(rng()%8),tau=int(rng()%30),tq=std::accumulate(q.begin(),q.end(),0);
        std::set<Mask>got,want;auto cb=[&](Mask m){got.insert(m);};
        emit_fixed_cardinality(p,q,k,tau,cb);
        for(Mask m=0;m<(Mask(1)<<n);++m) {
            if(std::popcount(m)!=k)continue;int ps=0,sq=0;
            for(int i=0;i<n;++i)if((m>>i)&1U){ps+=p[i];sq+=q[i];}
            if(ps>=tau&&tq-sq>=tau)want.insert(m);
        }
        if(got!=want)throw std::runtime_error("odd A emitter random self-test failed");
    }
}

struct JobStats {
    Count a_checked{}, survivors{}, exact_calls{}, a_nodes{}, completion_nodes{};
    bool sat{};
    Mask wr{},wc{},wd{},wa{};
    double seconds{};
};

std::string job_key(const Job& j) {
    return profile_string(j.canonical)+"|"+profile_string(j.oriented);
}
std::string job_key(const OddJob& j) {
    return profile_string(j.canonical)+"|"+profile_string(j.oriented);
}

std::filesystem::path job_log_path(const std::string&certificate,const std::string&key) {
    std::filesystem::path cert(certificate);
    std::filesystem::path dir=cert.parent_path()/(cert.filename().string()+".job-logs");
    Sha256 hash;hash.update(key);
    return dir/(hash.hex_digest()+".json");
}

std::unordered_set<std::string> read_completed(const std::string& path,
                                               const Config&cfg,bool*has_sat=nullptr) {
    std::unordered_set<std::string> done;
    std::ifstream in(path);
    std::string line;
    bool header_ok=false;
    if(has_sat)*has_sat=false;
    while(std::getline(in,line)) {
        if(line.empty())continue;
        if(line[0]=='#') {
            if(line.find("# impl_a independent")==0) {
                header_ok=line.find(" n="+std::to_string(cfg.n)+" ")!=std::string::npos&&
                          line.find("tau="+std::to_string(cfg.tau))!=std::string::npos;
            }
            continue;
        }
        std::vector<std::string>f;std::istringstream ss(line);std::string x;
        while(std::getline(ss,x,'\t'))f.push_back(x);
        if(f.size()<24)throw std::runtime_error("resume: malformed TSV row");
        const std::string key=f[0]+"|"+f[1];
        if(!done.insert(key).second)throw std::runtime_error("resume: duplicate job key "+key);
        if(f[11].size()!=64)throw std::runtime_error("resume: invalid orbit SHA-256");
        if(f[18]=="UNSAT") {
            if(std::stoull(f[13])!=std::stoull(f[10])*std::stoull(f[12]))
                throw std::runtime_error("resume: incomplete UNSAT job "+key);
        } else if(f[18]=="SAT") {
            if(has_sat)*has_sat=true;
            Mask R=Mask(std::stoul(f[19],nullptr,16)),C=Mask(std::stoul(f[20],nullptr,16));
            Mask D=Mask(std::stoul(f[21],nullptr,16)),A=Mask(std::stoul(f[22],nullptr,16));
            auto[b,w]=direct_counts(cfg.n,R,C,D,A);
            if(b<cfg.tau||w<cfg.tau)throw std::runtime_error("resume: invalid SAT witness");
        } else throw std::runtime_error("resume: invalid verdict");
        const auto log=job_log_path(path,key);
        if(!std::filesystem::is_regular_file(log))
            throw std::runtime_error("resume: missing atomic job log "+log.string());
        std::ifstream log_in(log);
        std::string body((std::istreambuf_iterator<char>(log_in)),
                         std::istreambuf_iterator<char>());
        auto require=[&](const std::string&needle) {
            if(body.find(needle)==std::string::npos)
                throw std::runtime_error("resume: job log disagrees with TSV: "+log.string());
        };
        require("\"schema\": \"pq-impl-a-job-v1\"");
        require("\"n\": "+std::to_string(cfg.n));
        require("\"tau\": "+std::to_string(cfg.tau));
        require("\"canonical\": \""+f[0]+"\"");
        require("\"oriented\": \""+f[1]+"\"");
        require("\"verdict\": \""+f[18]+"\"");
    }
    if(!done.empty()&&!header_ok)throw std::runtime_error("resume: n/tau header mismatch");
    return done;
}

struct ExistingTotals {
    Count rows{}, a_checked{}, survivors{}, exact_calls{}, completion_nodes{};
};

ExistingTotals read_totals(const std::string& path) {
    ExistingTotals t;
    std::ifstream in(path);
    std::string line;
    while(std::getline(in,line)) {
        if(line.empty()||line[0]=='#')continue;
        std::vector<std::string> fields;
        std::istringstream ss(line); std::string field;
        while(std::getline(ss,field,'\t'))fields.push_back(field);
        if(fields.size()<18)throw std::runtime_error("malformed certificate row");
        ++t.rows;
        t.a_checked+=std::stoull(fields[13]);
        t.survivors+=std::stoull(fields[15]);
        t.exact_calls+=std::stoull(fields[16]);
        t.completion_nodes+=std::stoull(fields[17]);
    }
    return t;
}

void write_header(std::ostream& out,const Config& cfg) {
    out<<"# impl_a independent even-order exact enumerator n="<<cfg.n
       <<" tau="<<cfg.tau<<"\n";
    out<<"# columns\tcanonical\toriented\tS\tr\tc\td0\td1\ta0\ta1\tsign"
          "\tpair_orbits\torbit_sha256\tA_per_orbit\tA_checked\tA_tree_nodes"
          "\tprefilter_survivors\texact_calls\tcompletion_nodes\tverdict"
          "\twitness_R\twitness_C\twitness_D\twitness_A\tseconds\n";
}

void write_row(std::ostream& out,const Job& j,const JobStats& s,
               Count orbits,const std::string& hash,int h) {
    const auto&p=j.oriented;
    out<<profile_string(j.canonical)<<'\t'<<profile_string(p)<<'\t'<<p.sum()
       <<'\t'<<p.r<<'\t'<<p.c<<'\t'<<p.d0<<'\t'<<p.d1<<'\t'<<p.a0<<'\t'<<p.a1
       <<'\t'<<int(j.sign)<<'\t'<<orbits<<'\t'<<hash<<'\t'
       <<choose(h,p.a0)*choose(h,p.a1)<<'\t'<<s.a_checked<<'\t'<<s.a_nodes
       <<'\t'<<s.survivors<<'\t'<<s.exact_calls<<'\t'<<s.completion_nodes
       <<'\t'<<(s.sat?"SAT":"UNSAT")<<'\t';
    auto pm=[&](Mask m){std::ostringstream q;q<<std::hex<<m;return q.str();};
    if(s.sat) out<<pm(s.wr)<<'\t'<<pm(s.wc)<<'\t'<<pm(s.wd)<<'\t'<<pm(s.wa);
    else out<<"\t\t\t";
    out<<'\t'<<std::fixed<<std::setprecision(6)<<s.seconds<<'\n';
    out.flush();
}

void write_odd_header(std::ostream&out,const Config&cfg) {
    out<<"# impl_a independent odd-order exact enumerator n="<<cfg.n
       <<" tau="<<cfg.tau<<"\n";
    out<<"# columns\tcanonical\toriented\tS\tr\tc\td\td_unused\ta\ta_unused\tsign"
          "\tpair_orbits\torbit_sha256\tA_per_orbit\tA_checked\tA_tree_nodes"
          "\tprefilter_survivors\texact_calls\tcompletion_nodes\tverdict"
          "\twitness_R\twitness_C\twitness_D\twitness_A\tseconds\n";
}

void write_row(std::ostream&out,const OddJob&j,const JobStats&s,
               Count orbits,const std::string&hash,int n) {
    const auto&p=j.oriented;
    out<<profile_string(j.canonical)<<'\t'<<profile_string(p)<<'\t'<<p.sum()
       <<'\t'<<p.r<<'\t'<<p.c<<'\t'<<p.d<<"\t0\t"<<p.a<<"\t0\t"
       <<int(j.sign)<<'\t'<<orbits<<'\t'<<hash<<'\t'<<choose(n,p.a)
       <<'\t'<<s.a_checked<<'\t'<<s.a_nodes<<'\t'<<s.survivors<<'\t'
       <<s.exact_calls<<'\t'<<s.completion_nodes<<'\t'
       <<(s.sat?"SAT":"UNSAT")<<'\t';
    auto pm=[](Mask m){std::ostringstream q;q<<std::hex<<m;return q.str();};
    if(s.sat)out<<pm(s.wr)<<'\t'<<pm(s.wc)<<'\t'<<pm(s.wd)<<'\t'<<pm(s.wa);
    else out<<"\t\t\t";
    out<<'\t'<<std::fixed<<std::setprecision(6)<<s.seconds<<'\n';out.flush();
}

template<class J>
void write_job_log(const std::string&certificate,const Config&cfg,const J&j,
                   const JobStats&s,Count orbits,const std::string&hash,
                   bool partial_campaign) {
    namespace fs=std::filesystem;
    fs::path cert(certificate);
    fs::path dir=cert.parent_path()/(cert.filename().string()+".job-logs");
    fs::create_directories(dir);
    fs::path target=job_log_path(certificate,job_key(j));
    fs::path temporary=target;temporary+=".tmp";
    std::ofstream out(temporary,std::ios::trunc);
    if(!out)throw std::runtime_error("cannot write job log "+temporary.string());
    auto hex=[](Mask m){std::ostringstream q;q<<std::hex<<m;return q.str();};
    out<<"{\n"
       <<"  \"schema\": \"pq-impl-a-job-v1\",\n"
       <<"  \"n\": "<<cfg.n<<",\n"
       <<"  \"tau\": "<<cfg.tau<<",\n"
       <<"  \"canonical\": \""<<profile_string(j.canonical)<<"\",\n"
       <<"  \"oriented\": \""<<profile_string(j.oriented)<<"\",\n"
       <<"  \"pair_orbits\": "<<orbits<<",\n"
       <<"  \"orbit_sha256\": \""<<hash<<"\",\n"
       <<"  \"A_checked\": "<<s.a_checked<<",\n"
       <<"  \"A_tree_nodes\": "<<s.a_nodes<<",\n"
       <<"  \"prefilter_survivors\": "<<s.survivors<<",\n"
       <<"  \"exact_calls\": "<<s.exact_calls<<",\n"
       <<"  \"completion_nodes\": "<<s.completion_nodes<<",\n"
       <<"  \"verdict\": \""<<(s.sat?"SAT":"UNSAT")<<"\",\n"
       <<"  \"partial_campaign\": "<<(partial_campaign?"true":"false")<<",\n"
       <<"  \"witness\": ";
    if(s.sat)
        out<<"{\"R\":\""<<hex(s.wr)<<"\",\"C\":\""<<hex(s.wc)
           <<"\",\"D\":\""<<hex(s.wd)<<"\",\"A\":\""<<hex(s.wa)<<"\"}";
    else out<<"null";
    out<<",\n  \"seconds\": "<<std::fixed<<std::setprecision(6)<<s.seconds<<"\n}\n";
    out.flush();out.close();
    if(!out)throw std::runtime_error("failed writing job log "+temporary.string());
    std::error_code ec;fs::rename(temporary,target,ec);
    if(ec)throw std::runtime_error("atomic job-log rename failed: "+ec.message());
}

struct EarlySat {int job_index;};

struct Options {
    Config cfg;
    std::string output="impl_a_certificate.tsv";
    std::string only_canonical;
    bool resume{},self_test_only{},worklist_only{},stop_on_sat{};
    int max_types=-1;
};

Options parse_options(int argc,char**argv) {
    Options o;
    for(int i=1;i<argc;++i) {
        std::string a=argv[i];
        auto val=[&](){if(++i>=argc)throw std::runtime_error("missing value after "+a);
                       return std::string(argv[i]);};
        if(a=="--n")o.cfg.n=std::stoi(val());
        else if(a=="--tau")o.cfg.tau=std::stoi(val());
        else if(a=="--output")o.output=val();
        else if(a=="--only-canonical")o.only_canonical=val();
        else if(a=="--resume")o.resume=true;
        else if(a=="--self-test-only")o.self_test_only=true;
        else if(a=="--worklist-only")o.worklist_only=true;
        else if(a=="--stop-on-sat")o.stop_on_sat=true;
        else if(a=="--max-types")o.max_types=std::stoi(val());
        else if(a=="--help") {
            std::cout<<"usage: impl_a_solver [--n N --tau T] [--output FILE] "
                        "[--resume] [--self-test-only] [--worklist-only] "
                        "[--stop-on-sat] [--only-canonical PROFILE] [--max-types K]\n";
            std::exit(0);
        } else throw std::runtime_error("unknown option: "+a);
    }
    return o;
}

int run_odd(const Options&opt,const std::chrono::steady_clock::time_point&startup) {
    Count ordered=0;auto jobs=make_odd_jobs(opt.cfg,&ordered);
    std::map<int,int>strata;
    for(const auto&j:jobs)strata[j.canonical.sum()]++;
    std::cerr<<"odd worklist: ordered="<<ordered<<" canonical="<<jobs.size()
             <<" oriented="<<jobs.size()<<" strata=";
    for(auto[s,c]:strata)std::cerr<<s<<':'<<c<<' ';std::cerr<<'\n';
    if(opt.cfg.n==17&&opt.cfg.tau==29) {
        const std::map<int,int>want{{23,1},{24,3},{25,5},{26,9},{27,13},{28,21},
          {29,28},{30,38},{31,45},{32,53},{33,58},{34,42}};
        if(ordered!=2145||jobs.size()!=316||strata!=want)
            throw std::runtime_error("n=17 worklist cross-check failed");
    }
    if(!opt.only_canonical.empty()) {
        std::erase_if(jobs,[&](const OddJob&j){
            return profile_string(j.canonical)!=opt.only_canonical;
        });
        if(jobs.empty())throw std::runtime_error("--only-canonical did not match a valid profile");
        std::cerr<<"profile selector: "<<opt.only_canonical<<" -> "<<jobs.size()<<" job\n";
    }
    if(opt.self_test_only||opt.worklist_only)return 0;
    bool prior_sat=false;
    auto done=opt.resume?read_completed(opt.output,opt.cfg,&prior_sat):
                         std::unordered_set<std::string>{};
    std::unordered_set<std::string>expected;
    for(const auto&j:jobs)expected.insert(job_key(j));
    for(const auto&key:done)if(!expected.count(key))
        throw std::runtime_error("resume: job is not in regenerated worklist: "+key);
    if(prior_sat){std::cerr<<"resume: directly verified SAT row already decides target\n";return 0;}
    if(opt.resume&&done.size()==jobs.size()) {
        std::cerr<<"resume: all "<<jobs.size()<<" jobs are already complete\n";return 0;
    }
    const ExistingTotals prior=opt.resume?read_totals(opt.output):ExistingTotals{};
    std::ofstream out;
    out.open(opt.output,opt.resume?std::ios::app:std::ios::trunc);
    if(!out)throw std::runtime_error("cannot open output "+opt.output);
    if(!opt.resume||std::ifstream(opt.output,std::ios::ate).tellg()==0)
        write_odd_header(out,opt.cfg);
    std::map<PairType,std::vector<int>>by_type;
    for(int i=0;i<int(jobs.size());++i)if(!done.count(job_key(jobs[i])))
        by_type[{jobs[i].oriented.r,jobs[i].oriented.c,jobs[i].sign}].push_back(i);
    std::map<int,std::vector<Mask>>neck_cache;std::vector<JobStats>stats(jobs.size());
    Count total_a=prior.a_checked,total_surv=prior.survivors;
    Count total_exact=prior.exact_calls,total_nodes=prior.completion_nodes,completed_now=0;
    int types_done=0;
    for(auto&[type,indices]:by_type) {
        if(opt.max_types>=0&&types_done>=opt.max_types)break;++types_done;
        auto get_neck=[&](int k)->const std::vector<Mask>&{
            auto it=neck_cache.find(k);
            if(it==neck_cache.end())
                it=neck_cache.emplace(k,necklaces_of_size(opt.cfg.n,k)).first;
            return it->second;
        };
        auto reps=pair_representatives(opt.cfg.n,type,get_neck(type.r),get_neck(type.c));
        const std::string hash=orbit_fingerprint(reps);
        std::cerr<<"odd pair type ("<<type.r<<','<<type.c<<",sign="<<type.sign
                 <<"): "<<reps.size()<<" orbits, "<<indices.size()<<" jobs\n";
        std::map<int,std::vector<int>>groups;
        for(int ji:indices) {
            const auto&p=jobs[ji].oriented;groups[p.a].push_back(ji);
        }
        auto type_start=std::chrono::steady_clock::now();
        std::optional<int> early_job;
        try { for(const auto&rep:reps) {
            PairData pd=make_pair_data(opt.cfg.n,rep.r,rep.c);
            for(auto&[asize,jis]:groups) {
                auto cb=[&](Mask amask) {
                    if(early_job&&opt.stop_on_sat)return;
                    std::vector<int>p(opt.cfg.n),q=pd.rowq;
                    for(int d=0;d<opt.cfg.n;++d)for(int a=0;a<opt.cfg.n;++a)
                        if((amask>>a)&1U){p[d]+=pd.P[d][a];q[d]-=pd.Q[d][a];}
                    int q0=std::accumulate(q.begin(),q.end(),0);
                    for(int ji:jis) {
                        auto&s=stats[ji];const auto&jp=jobs[ji].oriented;
                        ++s.survivors;++s.exact_calls;
                        auto cr=exact_fixed_completion(p,q,jp.d,opt.cfg.tau,q0);
                        s.completion_nodes+=cr.nodes;
                        if(cr.sat&&!s.sat) {
                            auto[b,w]=direct_counts(opt.cfg.n,rep.r,rep.c,cr.mask,amask);
                            if(b<opt.cfg.tau||w<opt.cfg.tau)
                                throw std::runtime_error("odd direct witness verification failed");
                            s.sat=true;s.wr=rep.r;s.wc=rep.c;s.wd=cr.mask;s.wa=amask;
                            if(opt.stop_on_sat){early_job=ji;break;}
                        }
                    }
                };
                auto es=emit_fixed_cardinality(pd.colp,pd.colq,asize,opt.cfg.tau,cb);
                for(int ji:jis){
                    stats[ji].a_nodes+=es.nodes;
                    stats[ji].a_checked+=choose(opt.cfg.n,asize);
                }
                if(early_job)throw EarlySat{*early_job};
            }
        }} catch(const EarlySat&e) {
            const double sec=std::chrono::duration<double>(
                std::chrono::steady_clock::now()-type_start).count();
            stats[e.job_index].seconds=sec;
            write_job_log(opt.output,opt.cfg,jobs[e.job_index],stats[e.job_index],
                          reps.size(),hash,true);
            write_row(out,jobs[e.job_index],stats[e.job_index],reps.size(),hash,opt.cfg.n);
            out<<"# EARLY_SAT\tjob="<<job_key(jobs[e.job_index])
               <<"\tA_checked="<<stats[e.job_index].a_checked<<'\n';
            out.flush();return 0;
        }
        const double sec=std::chrono::duration<double>(
            std::chrono::steady_clock::now()-type_start).count();
        for(int ji:indices) {
            stats[ji].seconds=sec;
            write_job_log(opt.output,opt.cfg,jobs[ji],stats[ji],reps.size(),hash,false);
            write_row(out,jobs[ji],stats[ji],reps.size(),hash,opt.cfg.n);
            total_a+=stats[ji].a_checked;total_surv+=stats[ji].survivors;
            total_exact+=stats[ji].exact_calls;total_nodes+=stats[ji].completion_nodes;
            ++completed_now;
        }
    }
    if(done.size()+completed_now==jobs.size()) {
        const double elapsed=std::chrono::duration<double>(
            std::chrono::steady_clock::now()-startup).count();
        out<<"# TOTAL\tA_checked="<<total_a<<"\tprefilter_survivors="<<total_surv
           <<"\texact_calls="<<total_exact<<"\tcompletion_nodes="<<total_nodes
           <<"\telapsed="<<std::fixed<<std::setprecision(6)<<elapsed<<'\n';
    }
    return 0;
}

int run(const Options& opt) {
    const auto startup=std::chrono::steady_clock::now();
    self_tests();
    std::cerr<<"self-tests: PASS (200000 completion comparisons; 6000 emitter comparisons)\n";
    if(opt.cfg.n%2)return run_odd(opt,startup);
    Count ordered=0;
    auto jobs=make_jobs(opt.cfg,&ordered);
    std::map<int,int> strata;
    for(const auto&j:jobs)strata[j.canonical.sum()]++;
    // jobs double-count canonicals; recompute the stratum on unique keys.
    strata.clear(); std::set<Profile> cps;
    for(const auto&j:jobs)cps.insert(j.canonical);
    for(const auto&p:cps)strata[p.sum()]++;
    std::cerr<<"worklist: ordered="<<ordered<<" canonical="<<cps.size()
             <<" oriented="<<jobs.size()<<" strata=";
    for(auto [s,c]:strata)std::cerr<<s<<':'<<c<<' ';
    std::cerr<<'\n';
    if(opt.cfg.n==16&&opt.cfg.tau==33) {
        if(ordered!=1898||cps.size()!=342||jobs.size()!=677)
            throw std::runtime_error("C1 worklist count mismatch");
    }
    if(!opt.only_canonical.empty()) {
        std::erase_if(jobs,[&](const Job&j){
            return profile_string(j.canonical)!=opt.only_canonical;
        });
        if(jobs.empty())throw std::runtime_error("--only-canonical did not match a valid profile");
        std::cerr<<"profile selector: "<<opt.only_canonical<<" -> "<<jobs.size()<<" oriented jobs\n";
    }
    if(opt.self_test_only||opt.worklist_only)return 0;

    std::unordered_set<std::string> done;
    bool prior_sat=false;
    if(opt.resume)done=read_completed(opt.output,opt.cfg,&prior_sat);
    std::unordered_set<std::string>expected;
    for(const auto&j:jobs)expected.insert(job_key(j));
    for(const auto&key:done)if(!expected.count(key))
        throw std::runtime_error("resume: job is not in regenerated worklist: "+key);
    if(prior_sat){std::cerr<<"resume: directly verified SAT row already decides target\n";return 0;}
    if(opt.resume&&done.size()==jobs.size()) {
        std::cerr<<"resume: all "<<jobs.size()<<" jobs are already complete\n";
        return 0;
    }
    const ExistingTotals prior=opt.resume?read_totals(opt.output):ExistingTotals{};
    std::ofstream out;
    if(opt.resume)out.open(opt.output,std::ios::app);
    else out.open(opt.output,std::ios::trunc);
    if(!out)throw std::runtime_error("cannot open output "+opt.output);
    if(!opt.resume||std::ifstream(opt.output,std::ios::ate).tellg()==0)write_header(out,opt.cfg);

    std::map<PairType,std::vector<int>> by_type;
    for(int i=0;i<int(jobs.size());++i)
        if(!done.count(job_key(jobs[i])))
            by_type[{jobs[i].oriented.r,jobs[i].oriented.c,jobs[i].sign}].push_back(i);
    std::map<int,std::vector<Mask>> neck_cache;
    std::vector<JobStats> stats(jobs.size());
    Count total_a=prior.a_checked,total_surv=prior.survivors;
    Count total_exact=prior.exact_calls,total_nodes=prior.completion_nodes;
    Count completed_now=0;
    int types_done=0;
    for(auto&[type,indices]:by_type) {
        if(opt.max_types>=0&&types_done>=opt.max_types)break;
        ++types_done;
        auto get_neck=[&](int k)->const std::vector<Mask>&{
            auto it=neck_cache.find(k);
            if(it==neck_cache.end())
                it=neck_cache.emplace(k,necklaces_of_size(opt.cfg.n,k)).first;
            return it->second;
        };
        const auto&nr=get_neck(type.r);const auto&nc=get_neck(type.c);
        auto reps=pair_representatives(opt.cfg.n,type,nr,nc);
        std::string hash=orbit_fingerprint(reps);
        std::cerr<<"pair type ("<<type.r<<','<<type.c<<",sign="<<type.sign
                 <<"): "<<reps.size()<<" orbits, "<<indices.size()<<" jobs\n";

        std::map<std::pair<int,int>,std::vector<int>> groups;
        for(int ji:indices) {
            const auto&p=jobs[ji].oriented;
            groups[{p.a0,p.a1}].push_back(ji);
        }
        auto type_start=std::chrono::steady_clock::now();
        std::optional<int> early_job;
        try { for(const PairRep& rep:reps) {
            PairData pd=make_pair_data(opt.cfg.n,rep.r,rep.c);
            for(auto&[ashape,jis]:groups) {
                auto cb=[&](Mask amask) {
                    if(early_job&&opt.stop_on_sat)return;
                    std::vector<int> p(opt.cfg.n),q=pd.rowq;
                    for(int d=0;d<opt.cfg.n;++d)for(int a=0;a<opt.cfg.n;++a)
                        if((amask>>a)&1U){p[d]+=pd.P[d][a];q[d]-=pd.Q[d][a];}
                    int q0=std::accumulate(q.begin(),q.end(),0);
                    for(int ji:jis) {
                        auto&s=stats[ji];const auto&jp=jobs[ji].oriented;
                        ++s.survivors;++s.exact_calls;
                        auto cr=exact_completion(p,q,jp.d0,jp.d1,opt.cfg.tau,q0);
                        s.completion_nodes+=cr.nodes;
                        if(cr.sat&&!s.sat) {
                            auto [b,w]=direct_counts(opt.cfg.n,rep.r,rep.c,cr.mask,amask);
                            if(b<opt.cfg.tau||w<opt.cfg.tau)
                                throw std::runtime_error("direct witness verification failed");
                            s.sat=true;s.wr=rep.r;s.wc=rep.c;s.wd=cr.mask;s.wa=amask;
                            if(opt.stop_on_sat){early_job=ji;break;}
                        }
                    }
                };
                auto es=emit_antidiagonals(pd,ashape.first,ashape.second,opt.cfg.tau,cb);
                const Count per=choose(opt.cfg.n/2,ashape.first)*
                                choose(opt.cfg.n/2,ashape.second);
                for(int ji:jis){stats[ji].a_nodes+=es.nodes;stats[ji].a_checked+=per;}
                if(early_job)throw EarlySat{*early_job};
            }
        }} catch(const EarlySat&e) {
            const double sec=std::chrono::duration<double>(
                std::chrono::steady_clock::now()-type_start).count();
            stats[e.job_index].seconds=sec;
            write_job_log(opt.output,opt.cfg,jobs[e.job_index],stats[e.job_index],
                          reps.size(),hash,true);
            write_row(out,jobs[e.job_index],stats[e.job_index],reps.size(),hash,opt.cfg.n/2);
            out<<"# EARLY_SAT\tjob="<<job_key(jobs[e.job_index])
               <<"\tA_checked="<<stats[e.job_index].a_checked<<'\n';
            out.flush();return 0;
        }
        double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-type_start).count();
        for(int ji:indices) {
            stats[ji].seconds=sec;
            write_job_log(opt.output,opt.cfg,jobs[ji],stats[ji],reps.size(),hash,false);
            write_row(out,jobs[ji],stats[ji],reps.size(),hash,opt.cfg.n/2);
            total_a+=stats[ji].a_checked;total_surv+=stats[ji].survivors;
            total_exact+=stats[ji].exact_calls;total_nodes+=stats[ji].completion_nodes;
            ++completed_now;
        }
    }
    if(done.size()+completed_now==jobs.size()) {
        double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-startup).count();
        out<<"# TOTAL\tA_checked="<<total_a<<"\tprefilter_survivors="<<total_surv
           <<"\texact_calls="<<total_exact<<"\tcompletion_nodes="<<total_nodes
           <<"\telapsed="<<std::fixed<<std::setprecision(6)<<elapsed<<'\n';
    }
    return 0;
}

} // namespace pq

int main(int argc,char**argv) {
    try { return pq::run(pq::parse_options(argc,argv)); }
    catch(const std::exception&e){std::cerr<<"ERROR: "<<e.what()<<'\n';return 2;}
}
