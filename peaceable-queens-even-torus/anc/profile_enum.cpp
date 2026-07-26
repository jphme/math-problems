// Independent exact profile enumerator for 15x15 toroidal peaceable queens.
//
// Build:
//   clang++ -O3 -std=c++20 -DNDEBUG scripts/profile_enum.cpp -o work/profile_enum/profile_enum
//
// Validation:
//   work/profile_enum/profile_enum --self-test --random 100000
//
// One profile:
//   work/profile_enum/profile_enum --profile 7,7,8,8 --fix RC \
//     --expected-orbits 6892 --results work/profile_enum/results.jsonl \
//     --log work/profile_enum/logs/profile_7_7_8_8.log

#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

namespace {

constexpr int N = 15;
constexpr uint16_t ALL = (uint16_t{1} << N) - 1;
constexpr std::array<int, 8> UNITS{1, 2, 4, 7, 8, 11, 13, 14};
constexpr int INF = 30000;

int mod15(int x) {
    x %= N;
    return x < 0 ? x + N : x;
}

uint16_t mask_of(std::initializer_list<int> xs) {
    uint16_t ans = 0;
    for (int x : xs) ans |= uint16_t{1} << mod15(x);
    return ans;
}

std::string mask_values(uint16_t mask) {
    std::ostringstream out;
    out << '[';
    bool first = true;
    for (int i = 0; i < N; ++i) {
        if ((mask >> i) & 1U) {
            if (!first) out << ',';
            out << i;
            first = false;
        }
    }
    out << ']';
    return out.str();
}

struct Tables {
    std::array<std::vector<uint16_t>, N + 1> combinations;
    std::array<std::array<int16_t, 1 << N>, N + 1> rank{};
    // affine[unit index][translation][mask] = {u*x+t : x in mask}.
    std::array<std::array<std::vector<uint16_t>, N>, UNITS.size()> affine;
    std::array<int, UNITS.size()> negative_unit_index{};

    Tables() {
        for (auto &by_size : rank) by_size.fill(-1);
        for (uint32_t mask = 0; mask <= ALL; ++mask) {
            combinations[std::popcount(mask)].push_back(static_cast<uint16_t>(mask));
        }
        for (int k = 0; k <= N; ++k) {
            for (int i = 0; i < static_cast<int>(combinations[k].size()); ++i) {
                rank[k][combinations[k][i]] = static_cast<int16_t>(i);
            }
        }
        for (int ui = 0; ui < static_cast<int>(UNITS.size()); ++ui) {
            int wanted = mod15(-UNITS[ui]);
            auto it = std::find(UNITS.begin(), UNITS.end(), wanted);
            if (it == UNITS.end()) throw std::logic_error("negative unit missing");
            negative_unit_index[ui] = static_cast<int>(it - UNITS.begin());
            for (int t = 0; t < N; ++t) {
                affine[ui][t].resize(1 << N);
                affine[ui][t][0] = 0;
                for (uint32_t mask = 1; mask <= ALL; ++mask) {
                    uint32_t lb = mask & (~mask + 1);
                    int x = std::countr_zero(lb);
                    uint32_t rest = mask ^ lb;
                    int y = mod15(UNITS[ui] * x + t);
                    affine[ui][t][mask] =
                        affine[ui][t][rest] | (uint16_t{1} << y);
                }
            }
        }
    }

    uint16_t transform(uint16_t mask, int unit_index, int translation) const {
        return affine[unit_index][mod15(translation)][mask];
    }
};

const Tables &tables() {
    static const Tables value;
    return value;
}

struct PairRepresentative {
    uint16_t first;
    uint16_t second;
};

struct PairGroup {
    bool epsilon = false;   // (r,c) -> (r,-c), swaps the two completion families
    bool transpose = false; // (r,c) -> (c,r), requires equal fixed sizes

    int order() const {
        return 8 * N * N * (epsilon ? 2 : 1) * (transpose ? 2 : 1);
    }
};

class PackedBits {
  public:
    explicit PackedBits(uint64_t count) : words_((count + 63) / 64, 0) {}
    bool get(uint64_t i) const { return (words_[i >> 6] >> (i & 63)) & 1U; }
    void set(uint64_t i) { words_[i >> 6] |= uint64_t{1} << (i & 63); }

  private:
    std::vector<uint64_t> words_;
};

std::vector<PairRepresentative> pair_representatives(
    int k1, int k2, PairGroup group, bool quiet = false) {
    if (group.transpose && k1 != k2) {
        throw std::invalid_argument("transpose quotient requires equal fixed sizes");
    }
    const auto &tab = tables();
    const auto &xs = tab.combinations[k1];
    const auto &ys = tab.combinations[k2];
    const uint64_t ny = ys.size();
    PackedBits visited(uint64_t(xs.size()) * ny);
    std::vector<PairRepresentative> reps;

    for (int ix = 0; ix < static_cast<int>(xs.size()); ++ix) {
        for (int iy = 0; iy < static_cast<int>(ys.size()); ++iy) {
            uint64_t key = uint64_t(ix) * ny + iy;
            if (visited.get(key)) continue;
            uint16_t x = xs[ix], y = ys[iy];
            reps.push_back({x, y});

            for (int ui = 0; ui < static_cast<int>(UNITS.size()); ++ui) {
                for (int alpha = 0; alpha < N; ++alpha) {
                    uint16_t xt = tab.transform(x, ui, alpha);
                    int ixt = tab.rank[k1][xt];
                    for (int ecase = 0; ecase < (group.epsilon ? 2 : 1); ++ecase) {
                        int cui = ecase == 0 ? ui : tab.negative_unit_index[ui];
                        for (int beta = 0; beta < N; ++beta) {
                            uint16_t yt = tab.transform(y, cui, beta);
                            int iyt = tab.rank[k2][yt];
                            visited.set(uint64_t(ixt) * ny + iyt);
                            if (group.transpose) {
                                visited.set(uint64_t(iyt) * ny + ixt);
                            }
                        }
                    }
                }
            }
        }
        if (!quiet && ix != 0 && ix % 1000 == 0) {
            std::cerr << "orbit scan: " << ix << '/' << xs.size()
                      << " first-family sets, " << reps.size() << " reps\n";
        }
    }
    return reps;
}

struct PQData {
    std::array<uint8_t, N> p{};
    std::array<uint8_t, N> q{};
    int total_q = 0;
};

std::array<uint16_t, N> positive_rows(uint16_t rset, uint16_t cset) {
    std::array<uint16_t, N> rows{};
    constexpr int INV2 = 8;
    for (int d = 0; d < N; ++d) {
        for (int a = 0; a < N; ++a) {
            int r = mod15(INV2 * (d + a));
            int c = mod15(INV2 * (a - d));
            if (((rset >> r) & 1U) && ((cset >> c) & 1U)) {
                rows[d] |= uint16_t{1} << a;
            }
        }
    }
    return rows;
}

std::array<uint16_t, N> negative_rows(uint16_t rset, uint16_t cset) {
    std::array<uint16_t, N> rows{};
    constexpr int INV2 = 8;
    for (int d = 0; d < N; ++d) {
        for (int a = 0; a < N; ++a) {
            int r = mod15(INV2 * (d + a));
            int c = mod15(INV2 * (a - d));
            if (!((rset >> r) & 1U) && !((cset >> c) & 1U)) {
                rows[d] |= uint16_t{1} << a;
            }
        }
    }
    return rows;
}

PQData make_pq(const std::array<uint16_t, N> &prows,
               const std::array<uint16_t, N> &nrows, uint16_t aset) {
    PQData data;
    uint16_t not_a = ALL ^ aset;
    for (int d = 0; d < N; ++d) {
        data.p[d] = std::popcount(uint16_t(prows[d] & aset));
        data.q[d] = std::popcount(uint16_t(nrows[d] & not_a));
        data.total_q += data.q[d];
    }
    return data;
}

int extreme_sum(const std::array<uint8_t, N> &values, int choose, bool largest) {
    std::array<int, N + 1> histogram{};
    for (uint8_t x : values) ++histogram[x];
    int answer = 0, left = choose;
    if (largest) {
        for (int x = N; x >= 0 && left; --x) {
            int take = std::min(left, histogram[x]);
            answer += take * x;
            left -= take;
        }
    } else {
        for (int x = 0; x <= N && left; ++x) {
            int take = std::min(left, histogram[x]);
            answer += take * x;
            left -= take;
        }
    }
    return answer;
}

// Exact 7+8 meet-in-the-middle decision. Among right-half subsets with a
// fixed cardinality and p sum at least x, retain the minimum q sum.
bool exact_subset_decision(const PQData &data, int choose, int black_threshold,
                           int white_threshold, uint16_t *witness) {
    if (choose < 0 || choose > N) return false;
    int q_limit = data.total_q - white_threshold;
    if (q_limit < 0) return false;
    if (extreme_sum(data.p, choose, true) < black_threshold) return false;
    if (extreme_sum(data.q, choose, false) > q_limit) return false;

    constexpr int SPLIT = 7;
    constexpr int RIGHT = N - SPLIT;
    constexpr int MAXP = N * N;
    std::array<std::array<int16_t, MAXP + 2>, RIGHT + 1> best_q;
    std::array<std::array<uint16_t, MAXP + 2>, RIGHT + 1> best_mask;
    for (auto &row : best_q) row.fill(INF);
    for (auto &row : best_mask) row.fill(0);

    std::array<uint8_t, 1 << RIGHT> rcard{}, rpsum{}, rqsum{};
    for (int subset = 1; subset < (1 << RIGHT); ++subset) {
        int lb = subset & -subset;
        int bit = std::countr_zero(static_cast<unsigned>(lb));
        int rest = subset ^ lb;
        rcard[subset] = rcard[rest] + 1;
        rpsum[subset] = rpsum[rest] + data.p[SPLIT + bit];
        rqsum[subset] = rqsum[rest] + data.q[SPLIT + bit];
    }
    for (int subset = 0; subset < (1 << RIGHT); ++subset) {
        int k = rcard[subset], ps = rpsum[subset], qs = rqsum[subset];
        if (qs < best_q[k][ps]) {
            best_q[k][ps] = qs;
            best_mask[k][ps] = static_cast<uint16_t>(subset);
        }
    }
    for (int k = 0; k <= RIGHT; ++k) {
        for (int ps = MAXP; ps >= 0; --ps) {
            if (best_q[k][ps + 1] < best_q[k][ps]) {
                best_q[k][ps] = best_q[k][ps + 1];
                best_mask[k][ps] = best_mask[k][ps + 1];
            }
        }
    }

    std::array<uint8_t, 1 << SPLIT> lcard{}, lpsum{}, lqsum{};
    for (int subset = 1; subset < (1 << SPLIT); ++subset) {
        int lb = subset & -subset;
        int bit = std::countr_zero(static_cast<unsigned>(lb));
        int rest = subset ^ lb;
        lcard[subset] = lcard[rest] + 1;
        lpsum[subset] = lpsum[rest] + data.p[bit];
        lqsum[subset] = lqsum[rest] + data.q[bit];
    }
    for (int subset = 0; subset < (1 << SPLIT); ++subset) {
        int rk = choose - lcard[subset];
        if (rk < 0 || rk > RIGHT) continue;
        int need_p = std::max(0, black_threshold - int(lpsum[subset]));
        if (need_p > MAXP) continue;
        int allowed_q = q_limit - int(lqsum[subset]);
        if (allowed_q < 0) continue;
        if (best_q[rk][need_p] <= allowed_q) {
            if (witness) {
                *witness = static_cast<uint16_t>(
                    subset | (uint32_t(best_mask[rk][need_p]) << SPLIT));
            }
            return true;
        }
    }
    return false;
}

bool naive_subset_decision(const PQData &data, int choose, int black_threshold,
                           int white_threshold, uint16_t *witness) {
    int q_limit = data.total_q - white_threshold;
    for (uint16_t dset : tables().combinations[choose]) {
        int ps = 0, qs = 0;
        for (int d = 0; d < N; ++d) {
            if ((dset >> d) & 1U) {
                ps += data.p[d];
                qs += data.q[d];
            }
        }
        if (ps >= black_threshold && qs <= q_limit) {
            if (witness) *witness = dset;
            return true;
        }
    }
    return false;
}

std::pair<int, int> direct_counts(
    uint16_t rset, uint16_t cset, uint16_t dset, uint16_t aset) {
    int black = 0, white = 0;
    for (int r = 0; r < N; ++r) {
        for (int c = 0; c < N; ++c) {
            bool br = (rset >> r) & 1U;
            bool bc = (cset >> c) & 1U;
            bool bd = (dset >> mod15(r - c)) & 1U;
            bool ba = (aset >> mod15(r + c)) & 1U;
            black += br && bc && bd && ba;
            white += !br && !bc && !bd && !ba;
        }
    }
    return {black, white};
}

struct Witness {
    uint16_t r = 0, c = 0, d = 0, a = 0;
};

struct GenericWitness {
    uint16_t x = 0, y = 0, z = 0, w = 0;
};

struct SearchResult {
    bool sat = false;
    uint64_t reps_enumerated = 0;
    uint64_t completions = 0;
    GenericWitness witness;
};

SearchResult search_with_reps(
    const std::vector<PairRepresentative> &reps, int completion_z_size,
    int completion_w_size, int black_threshold, int white_threshold,
    std::ofstream *log = nullptr, bool progress = false) {
    SearchResult answer;
    const auto &wsets = tables().combinations[completion_w_size];
    for (const PairRepresentative &pair : reps) {
        ++answer.reps_enumerated;
        auto prows = positive_rows(pair.first, pair.second);
        auto nrows = negative_rows(pair.first, pair.second);
        for (uint16_t wset : wsets) {
            ++answer.completions;
            PQData pq = make_pq(prows, nrows, wset);
            uint16_t zset = 0;
            if (exact_subset_decision(
                    pq, completion_z_size, black_threshold, white_threshold, &zset)) {
                answer.sat = true;
                answer.witness = {pair.first, pair.second, zset, wset};
                return answer;
            }
        }
        if (progress && answer.reps_enumerated % 500 == 0) {
            std::ostringstream msg;
            msg << "search: " << answer.reps_enumerated << '/' << reps.size()
                << " reps, " << answer.completions << " completions";
            std::cerr << msg.str() << '\n';
            if (log) {
                *log << msg.str() << '\n';
                log->flush();
            }
        }
    }
    return answer;
}

Witness generic_to_original(const GenericWitness &g, std::string_view fixed) {
    if (fixed == "RC") return {g.x, g.y, g.z, g.w};
    if (fixed == "DA") {
        // New coordinates are (d,a). Their difference is -2c and their
        // sum is 2r, hence C=(-1/2)Z=7Z and R=(1/2)W=8W modulo 15.
        const auto &tab = tables();
        int u7 = static_cast<int>(std::find(UNITS.begin(), UNITS.end(), 7) - UNITS.begin());
        int u8 = static_cast<int>(std::find(UNITS.begin(), UNITS.end(), 8) - UNITS.begin());
        return {tab.transform(g.w, u8, 0), tab.transform(g.z, u7, 0), g.x, g.y};
    }
    throw std::invalid_argument("fixed pair must be RC or DA");
}

std::array<int, 4> parse_profile(const std::string &text) {
    std::array<int, 4> p{};
    char comma1 = 0, comma2 = 0, comma3 = 0;
    std::istringstream in(text);
    if (!(in >> p[0] >> comma1 >> p[1] >> comma2 >> p[2] >> comma3 >> p[3]) ||
        comma1 != ',' || comma2 != ',' || comma3 != ',' ||
        std::any_of(p.begin(), p.end(), [](int x) { return x < 0 || x > N; })) {
        throw std::invalid_argument("profile must be four comma-separated integers in 0..15");
    }
    return p;
}

std::string profile_string(const std::array<int, 4> &p) {
    std::ostringstream out;
    out << p[0] << ',' << p[1] << ',' << p[2] << ',' << p[3];
    return out.str();
}

std::string json_witness(const Witness &w) {
    std::ostringstream out;
    out << "{\"R\":" << mask_values(w.r)
        << ",\"C\":" << mask_values(w.c)
        << ",\"D\":" << mask_values(w.d)
        << ",\"A\":" << mask_values(w.a) << '}';
    return out.str();
}

struct CanonicalizedWitness {
    GenericWitness witness;
    uint64_t pair_key = 0;
};

CanonicalizedWitness canonicalize_witness(
    GenericWitness input, int k1, int k2, PairGroup group) {
    const auto &tab = tables();
    uint64_t ny = tab.combinations[k2].size();
    CanonicalizedWitness best;
    best.pair_key = std::numeric_limits<uint64_t>::max();

    for (int ui = 0; ui < static_cast<int>(UNITS.size()); ++ui) {
        for (int alpha = 0; alpha < N; ++alpha) {
            uint16_t xt = tab.transform(input.x, ui, alpha);
            for (int ecase = 0; ecase < (group.epsilon ? 2 : 1); ++ecase) {
                int cui = ecase == 0 ? ui : tab.negative_unit_index[ui];
                for (int beta = 0; beta < N; ++beta) {
                    uint16_t yt = tab.transform(input.y, cui, beta);
                    uint16_t zt, wt;
                    if (ecase == 0) {
                        zt = tab.transform(input.z, ui, alpha - beta);
                        wt = tab.transform(input.w, ui, alpha + beta);
                    } else {
                        zt = tab.transform(input.w, ui, alpha - beta);
                        wt = tab.transform(input.z, ui, alpha + beta);
                    }
                    int ixt = tab.rank[k1][xt], iyt = tab.rank[k2][yt];
                    uint64_t key = uint64_t(ixt) * ny + iyt;
                    if (key < best.pair_key) {
                        best = {{xt, yt, zt, wt}, key};
                    }
                    if (group.transpose) {
                        int ineg = tab.negative_unit_index[0]; // -1
                        uint16_t zneg = tab.transform(zt, ineg, 0);
                        uint64_t swapped_key = uint64_t(iyt) * ny + ixt;
                        if (swapped_key < best.pair_key) {
                            best = {{yt, xt, zneg, wt}, swapped_key};
                        }
                    }
                }
            }
        }
    }
    return best;
}

void require(bool condition, const std::string &message) {
    if (!condition) throw std::runtime_error("validation failed: " + message);
}

void randomized_reference_test(uint64_t instances) {
    std::mt19937_64 rng(0x20260725d15aULL);
    auto started = std::chrono::steady_clock::now();
    for (uint64_t test = 0; test < instances; ++test) {
        int kr = rng() % 16, kc = rng() % 16;
        int ka = rng() % 16, kd = rng() % 16;
        const auto &tab = tables();
        uint16_t r = tab.combinations[kr][rng() % tab.combinations[kr].size()];
        uint16_t c = tab.combinations[kc][rng() % tab.combinations[kc].size()];
        uint16_t a = tab.combinations[ka][rng() % tab.combinations[ka].size()];
        int bthr = rng() % 51, wthr = rng() % 51;
        if (bthr == 21 && wthr == 21) bthr = 20;

        PQData pq = make_pq(positive_rows(r, c), negative_rows(r, c), a);
        uint16_t fast_witness = 0, slow_witness = 0;
        bool fast = exact_subset_decision(pq, kd, bthr, wthr, &fast_witness);
        bool slow = naive_subset_decision(pq, kd, bthr, wthr, &slow_witness);
        if (fast != slow) {
            std::ostringstream msg;
            msg << "random instance " << test << " disagreed: sizes "
                << kr << ',' << kc << ',' << kd << ',' << ka
                << " thresholds " << bthr << ',' << wthr
                << " fast=" << fast << " naive=" << slow;
            throw std::runtime_error(msg.str());
        }
        if (fast) {
            int ps = 0, qs = 0;
            for (int d = 0; d < N; ++d) {
                if ((fast_witness >> d) & 1U) {
                    ps += pq.p[d];
                    qs += pq.q[d];
                }
            }
            require(std::popcount(fast_witness) == kd &&
                        ps >= bthr && qs <= pq.total_q - wthr,
                    "fast random witness does not meet its constraints");
        }
        if ((test + 1) % 25000 == 0) {
            std::cerr << "reference agreement: " << (test + 1) << '/'
                      << instances << '\n';
        }
    }
    double seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - started).count();
    std::cout << "reference_agreement instances=" << instances
              << " result=PASS seconds=" << std::fixed << std::setprecision(3)
              << seconds << '\n';
}

void positive_controls() {
    Witness known{
        mask_of({5, 7, 8, 11, 12, 14}),
        mask_of({0, 3, 4, 7, 9, 10, 12, 13}),
        mask_of({0, 1, 4, 8, 12, 13, 14}),
        mask_of({1, 2, 3, 9, 10, 12, 14})};
    require(direct_counts(known.r, known.c, known.d, known.a) ==
                std::pair<int, int>{20, 22},
            "20+20 witness is not B=20, W=22");
    PQData known_pq =
        make_pq(positive_rows(known.r, known.c), negative_rows(known.r, known.c), known.a);
    uint16_t found_d = 0;
    require(exact_subset_decision(known_pq, 7, 20, 22, &found_d),
            "20+20 witness completion was not detected");

    Witness triangle{
        mask_of({0, 1, 2}),
        mask_of({0, 1, 2, 3, 4, 5, 6, 7, 8}),
        mask_of({-8, -7, -6, -5, -4, -3, -2, -1, 0}),
        mask_of({0, 1, 2, 3, 4, 5, 6, 7, 8})};
    require(direct_counts(triangle.r, triangle.c, triangle.d, triangle.a) ==
                std::pair<int, int>{21, 6},
            "triangle control is not B=21, W=6");

    // This orientation fixes (R,C), for which epsilon is sound because
    // |D|=|A|=7. It deliberately over-covers the worklist's cheaper DA
    // choice and therefore supplies an independent orbit-sanity gate.
    PairGroup group68{true, false};
    auto reps68 = pair_representatives(6, 8, group68, true);
    require(reps68.size() == 10908,
            "(6,8) full epsilon-group orbit count is not 10,908");

    GenericWitness generic{known.r, known.c, known.d, known.a};
    auto canonical = canonicalize_witness(generic, 6, 8, group68);
    bool rep_present = false;
    for (const auto &rep : reps68) {
        uint64_t key =
            uint64_t(tables().rank[6][rep.first]) * tables().combinations[8].size() +
            tables().rank[8][rep.second];
        if (key == canonical.pair_key) {
            rep_present = true;
            break;
        }
    }
    require(rep_present, "known witness's (R,C) orbit has no representative");
    auto transformed_counts = direct_counts(
        canonical.witness.x, canonical.witness.y,
        canonical.witness.z, canonical.witness.w);
    require(transformed_counts == std::pair<int, int>{20, 22},
            "canonicalized known witness changed B,W");
    PQData canonical_pq = make_pq(
        positive_rows(canonical.witness.x, canonical.witness.y),
        negative_rows(canonical.witness.x, canonical.witness.y),
        canonical.witness.w);
    require(exact_subset_decision(canonical_pq, 7, 20, 22, nullptr),
            "known witness orbit is not among enumerator hits");

    SearchResult profile_control = search_with_reps(reps68, 7, 7, 20, 22);
    require(profile_control.sat,
            "profile (6,8,7,7) at thresholds (20,22) did not return SAT");
    Witness profile_witness = generic_to_original(profile_control.witness, "RC");
    auto profile_counts =
        direct_counts(profile_witness.r, profile_witness.c,
                      profile_witness.d, profile_witness.a);
    require(profile_counts.first >= 20 && profile_counts.second >= 22,
            "profile-control witness failed direct count");

    // Exercise the (r,c) <-> (d,a) coordinate change used when fixing DA.
    // This also checks the signs and factors in generic_to_original().
    const auto &tab = tables();
    int u2 = static_cast<int>(std::find(UNITS.begin(), UNITS.end(), 2) - UNITS.begin());
    int u13 = static_cast<int>(std::find(UNITS.begin(), UNITS.end(), 13) - UNITS.begin());
    GenericWitness known_da{
        known.d, known.a, tab.transform(known.c, u13, 0),
        tab.transform(known.r, u2, 0)};
    Witness known_roundtrip = generic_to_original(known_da, "DA");
    require(known_roundtrip.r == known.r && known_roundtrip.c == known.c &&
                known_roundtrip.d == known.d && known_roundtrip.a == known.a,
            "DA coordinate conversion did not round-trip the known witness");
    PQData da_pq = make_pq(
        positive_rows(known_da.x, known_da.y),
        negative_rows(known_da.x, known_da.y), known_da.w);
    require(exact_subset_decision(da_pq, 8, 20, 22, nullptr),
            "DA-oriented known witness completion was not detected");

    std::mt19937_64 map_rng(0xda20260725ULL);
    for (int test = 0; test < 1000; ++test) {
        GenericWitness g;
        g.x = static_cast<uint16_t>(map_rng()) & ALL;
        g.y = static_cast<uint16_t>(map_rng()) & ALL;
        g.z = static_cast<uint16_t>(map_rng()) & ALL;
        g.w = static_cast<uint16_t>(map_rng()) & ALL;
        Witness original = generic_to_original(g, "DA");
        require(direct_counts(g.x, g.y, g.z, g.w) ==
                    direct_counts(original.r, original.c, original.d, original.a),
                "DA coordinate conversion changed B,W on a random quadruple");
    }

    std::cout << "positive_controls result=PASS known_BW=20,22 triangle_BW=21,6"
              << " profile_6,8,7,7=SAT profile_completions="
              << profile_control.completions << " DA_mapping=PASS\n";
}

void orbit_controls() {
    auto no_epsilon =
        pair_representatives(7, 7, PairGroup{false, true}, true);
    require(no_epsilon.size() == 11793,
            "(7,7) order-3600 orbit count is not 11,793");
    auto full =
        pair_representatives(7, 7, PairGroup{true, true}, true);
    require(full.size() == 6892,
            "(7,7) order-7200 orbit count is not 6,892");
    std::cout << "orbit_controls result=PASS g3600=11793 g7200=6892\n";
}

struct Options {
    bool self_test = false;
    uint64_t random_instances = 100000;
    bool has_profile = false;
    bool batch = false;
    int batch_limit = -1;
    std::array<int, 4> profile{};
    std::string fixed = "auto";
    int black_threshold = 21;
    int white_threshold = 21;
    int64_t expected_orbits = -1;
    std::filesystem::path results;
    std::filesystem::path log;
    std::filesystem::path worklist;
};

Options parse_options(int argc, char **argv) {
    Options opt;
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        auto value = [&](const char *name) -> std::string {
            if (++i >= argc) throw std::invalid_argument(std::string(name) + " needs a value");
            return argv[i];
        };
        if (arg == "--self-test") opt.self_test = true;
        else if (arg == "--batch") opt.batch = true;
        else if (arg == "--limit") opt.batch_limit = std::stoi(value("--limit"));
        else if (arg == "--random") opt.random_instances = std::stoull(value("--random"));
        else if (arg == "--profile") {
            opt.profile = parse_profile(value("--profile"));
            opt.has_profile = true;
        } else if (arg == "--fix") opt.fixed = value("--fix");
        else if (arg == "--black") opt.black_threshold = std::stoi(value("--black"));
        else if (arg == "--white") opt.white_threshold = std::stoi(value("--white"));
        else if (arg == "--expected-orbits")
            opt.expected_orbits = std::stoll(value("--expected-orbits"));
        else if (arg == "--results") opt.results = value("--results");
        else if (arg == "--log") opt.log = value("--log");
        else if (arg == "--worklist") opt.worklist = value("--worklist");
        else if (arg == "--help") {
            std::cout
                << "profile_enum --self-test [--random 100000]\n"
                << "profile_enum --profile R,C,D,A [--fix RC|DA|auto]"
                << " [--black 21 --white 21] [--expected-orbits N]"
                << " [--results FILE --log FILE]\n"
                << "profile_enum --batch --worklist FILE --results FILE"
                << " --log LOG_DIRECTORY [--limit N]\n";
            std::exit(0);
        } else {
            throw std::invalid_argument("unknown option: " + arg);
        }
    }
    return opt;
}

int run_profile(const Options &opt) {
    std::string fixed = opt.fixed;
    if (fixed == "auto") {
        // A conservative automatic choice: compare raw pair counts. This does
        // not use the potentially invalid epsilon reduction when the two
        // completion-family sizes differ.
        uint64_t rc_raw =
            uint64_t(tables().combinations[opt.profile[0]].size()) *
            tables().combinations[opt.profile[1]].size();
        uint64_t da_raw =
            uint64_t(tables().combinations[opt.profile[2]].size()) *
            tables().combinations[opt.profile[3]].size();
        fixed = rc_raw <= da_raw ? "RC" : "DA";
    }
    if (fixed != "RC" && fixed != "DA") {
        throw std::invalid_argument("--fix must be RC, DA, or auto");
    }

    int xsize, ysize, zsize, wsize;
    if (fixed == "RC") {
        std::tie(xsize, ysize, zsize, wsize) =
            std::tuple{opt.profile[0], opt.profile[1], opt.profile[2], opt.profile[3]};
    } else {
        std::tie(xsize, ysize, zsize, wsize) =
            std::tuple{opt.profile[2], opt.profile[3], opt.profile[1], opt.profile[0]};
    }
    PairGroup group{zsize == wsize, xsize == ysize};

    std::ofstream log;
    if (!opt.log.empty()) {
        std::filesystem::create_directories(opt.log.parent_path());
        log.open(opt.log, std::ios::out | std::ios::trunc);
        if (!log) throw std::runtime_error("cannot open log " + opt.log.string());
    }
    auto record = [&](const std::string &line) {
        std::cout << line << '\n';
        if (log) {
            log << line << '\n';
            log.flush();
        }
    };

    auto started = std::chrono::steady_clock::now();
    {
        std::ostringstream msg;
        msg << "profile=" << profile_string(opt.profile)
            << " fixed=" << fixed
            << " generic_sizes=" << xsize << ',' << ysize << ',' << zsize << ',' << wsize
            << " black=" << opt.black_threshold
            << " white=" << opt.white_threshold
            << " epsilon=" << group.epsilon
            << " transpose=" << group.transpose
            << " group_order=" << group.order();
        record(msg.str());
    }

    auto reps = pair_representatives(xsize, ysize, group);
    {
        std::ostringstream msg;
        msg << "orbit_representatives=" << reps.size();
        if (opt.expected_orbits >= 0) msg << " expected=" << opt.expected_orbits;
        record(msg.str());
    }
    if (opt.expected_orbits >= 0 &&
        reps.size() < static_cast<uint64_t>(opt.expected_orbits)) {
        throw std::runtime_error(
            "representative count is below worklist count; refusing unsound run");
    }

    SearchResult search =
        search_with_reps(reps, zsize, wsize, opt.black_threshold,
                         opt.white_threshold, log ? &log : nullptr, true);
    double seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - started).count();
    Witness witness;
    if (search.sat) {
        witness = generic_to_original(search.witness, fixed);
        auto [black, white] =
            direct_counts(witness.r, witness.c, witness.d, witness.a);
        if (black < opt.black_threshold || white < opt.white_threshold) {
            throw std::runtime_error("reported SAT witness failed direct checker");
        }
        if (std::array<int, 4>{std::popcount(witness.r), std::popcount(witness.c),
                               std::popcount(witness.d), std::popcount(witness.a)} !=
            opt.profile) {
            throw std::runtime_error("reported SAT witness has the wrong profile");
        }
    }

    {
        std::ostringstream msg;
        msg << "result=" << (search.sat ? "SAT" : "UNSAT")
            << " reps_enumerated=" << search.reps_enumerated
            << " completions=" << search.completions
            << " seconds=" << std::fixed << std::setprecision(6) << seconds;
        if (search.sat) msg << " witness=" << json_witness(witness);
        record(msg.str());
    }

    if (!opt.results.empty()) {
        std::filesystem::create_directories(opt.results.parent_path());
        std::ofstream out(opt.results, std::ios::out | std::ios::app);
        if (!out) throw std::runtime_error("cannot open results " + opt.results.string());
        out << "{\"profile\":[" << opt.profile[0] << ',' << opt.profile[1] << ','
            << opt.profile[2] << ',' << opt.profile[3] << ']'
            << ",\"S\":" << (opt.profile[0] + opt.profile[1] +
                              opt.profile[2] + opt.profile[3])
            << ",\"fixed\":\"" << fixed << '"'
            << ",\"symmetry\":{\"epsilon\":" << (group.epsilon ? "true" : "false")
            << ",\"transpose\":" << (group.transpose ? "true" : "false")
            << ",\"order\":" << group.order() << '}'
            << ",\"reps_enumerated\":" << search.reps_enumerated
            << ",\"orbit_reps_total\":" << reps.size()
            << ",\"completions\":" << search.completions
            << ",\"result\":\"" << (search.sat ? "SAT" : "UNSAT") << '"'
            << ",\"witness\":" << (search.sat ? json_witness(witness) : "null")
            << ",\"thresholds\":[" << opt.black_threshold << ',' << opt.white_threshold << ']'
            << ",\"seconds\":" << std::fixed << std::setprecision(6) << seconds
            << "}\n";
    }
    return search.sat ? 10 : 20;
}

struct WorkRow {
    std::array<int, 4> profile{};
    int sum = 0;
    int64_t brief_orbits = 0;
    int64_t brief_completions = 0;
};

std::vector<WorkRow> read_worklist(const std::filesystem::path &path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open worklist " + path.string());
    std::vector<WorkRow> rows;
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        std::vector<std::string> fields;
        std::istringstream split(line);
        std::string field;
        while (std::getline(split, field, '\t')) fields.push_back(field);
        if (fields.size() < 7) {
            throw std::runtime_error("malformed worklist row: " + line);
        }
        rows.push_back({
            parse_profile(fields[0]), std::stoi(fields[1]),
            std::stoll(fields[4]), std::stoll(fields[6])});
    }
    return rows;
}

std::set<std::string> completed_profiles(const std::filesystem::path &results) {
    std::set<std::string> done;
    if (results.empty() || !std::filesystem::exists(results)) return done;
    std::ifstream in(results);
    std::string line;
    while (std::getline(in, line)) {
        std::string marker = "\"profile\":[";
        auto begin = line.find(marker);
        if (begin == std::string::npos) continue;
        begin += marker.size();
        auto end = line.find(']', begin);
        if (end == std::string::npos) continue;
        // Batch results are only reusable for the mission thresholds.
        if (line.find("\"thresholds\":[21,21]") == std::string::npos) continue;
        done.insert(line.substr(begin, end - begin));
    }
    return done;
}

struct BatchJob {
    WorkRow row;
    std::string fixed;
    int xsize = 0, ysize = 0, zsize = 0, wsize = 0;
    PairGroup group;
    uint64_t sound_completions = 0;
    std::tuple<int, int, bool, bool> group_key;
};

int run_batch(const Options &opt) {
    if (opt.worklist.empty() || opt.results.empty() || opt.log.empty()) {
        throw std::invalid_argument(
            "--batch requires --worklist, --results, and --log (a directory)");
    }
    std::filesystem::create_directories(opt.results.parent_path());
    std::filesystem::create_directories(opt.log);

    using GroupKey = std::tuple<int, int, bool, bool>;
    std::map<GroupKey, std::vector<PairRepresentative>> cache;
    auto get_reps = [&](const GroupKey &key) -> std::vector<PairRepresentative> & {
        auto it = cache.find(key);
        if (it != cache.end()) return it->second;
        auto [k1, k2, epsilon, transpose] = key;
        std::cerr << "building orbit representatives for " << k1 << ',' << k2
                  << " epsilon=" << epsilon << " transpose=" << transpose << '\n';
        auto [inserted, ok] = cache.emplace(
            key, pair_representatives(k1, k2, PairGroup{epsilon, transpose}, true));
        (void)ok;
        std::cerr << "  -> " << inserted->second.size() << " representatives\n";
        return inserted->second;
    };

    std::vector<BatchJob> jobs;
    uint64_t corrected_total = 0, brief_total = 0;
    for (const WorkRow &row : read_worklist(opt.worklist)) {
        int r = row.profile[0], c = row.profile[1];
        int d = row.profile[2], a = row.profile[3];
        GroupKey rc_key{r, c, d == a, r == c};
        GroupKey da_key{d, a, c == r, d == a};
        auto &rc_reps = get_reps(rc_key);
        auto &da_reps = get_reps(da_key);
        uint64_t rc_work = uint64_t(rc_reps.size()) * tables().combinations[a].size();
        uint64_t da_work = uint64_t(da_reps.size()) * tables().combinations[r].size();
        BatchJob job;
        job.row = row;
        if (rc_work <= da_work) {
            job.fixed = "RC";
            job.xsize = r; job.ysize = c; job.zsize = d; job.wsize = a;
            job.group = {d == a, r == c};
            job.sound_completions = rc_work;
            job.group_key = rc_key;
        } else {
            job.fixed = "DA";
            job.xsize = d; job.ysize = a; job.zsize = c; job.wsize = r;
            job.group = {c == r, d == a};
            job.sound_completions = da_work;
            job.group_key = da_key;
        }
        auto &chosen_reps = get_reps(job.group_key);
        if (chosen_reps.size() < static_cast<uint64_t>(row.brief_orbits)) {
            throw std::runtime_error(
                "sound representative count fell below brief count for " +
                profile_string(row.profile));
        }
        corrected_total += job.sound_completions;
        brief_total += row.brief_completions;
        jobs.push_back(job);
    }
    std::sort(jobs.begin(), jobs.end(), [](const BatchJob &a, const BatchJob &b) {
        if (a.sound_completions != b.sound_completions)
            return a.sound_completions < b.sound_completions;
        return a.row.profile < b.row.profile;
    });

    auto done = completed_profiles(opt.results);
    std::cout << "batch profiles=" << jobs.size()
              << " already_completed=" << done.size()
              << " brief_completions=" << brief_total
              << " sound_completions=" << corrected_total << '\n';
    auto batch_started = std::chrono::steady_clock::now();
    int newly_finished = 0;
    for (const BatchJob &job : jobs) {
        std::string ptext = profile_string(job.row.profile);
        if (done.contains(ptext)) continue;
        if (opt.batch_limit >= 0 && newly_finished >= opt.batch_limit) break;

        std::string log_name = "profile_";
        for (char ch : ptext) log_name += (ch == ',' ? '_' : ch);
        log_name += ".log";
        std::filesystem::path log_path = opt.log / log_name;
        std::ofstream log(log_path, std::ios::out | std::ios::trunc);
        if (!log) throw std::runtime_error("cannot open log " + log_path.string());
        auto &reps = get_reps(job.group_key);
        log << "profile=" << ptext << " fixed=" << job.fixed
            << " generic_sizes=" << job.xsize << ',' << job.ysize << ','
            << job.zsize << ',' << job.wsize
            << " epsilon=" << job.group.epsilon
            << " transpose=" << job.group.transpose
            << " group_order=" << job.group.order()
            << " orbit_representatives=" << reps.size()
            << " brief_orbit_lower_bound=" << job.row.brief_orbits
            << " planned_completions=" << job.sound_completions << '\n';
        log << "soundness: epsilon is enabled iff the two completion-family"
               " cardinalities are equal\n";
        log.flush();

        std::cout << "batch_start profile=" << ptext
                  << " fixed=" << job.fixed << " reps=" << reps.size()
                  << " completions=" << job.sound_completions << '\n';
        auto started = std::chrono::steady_clock::now();
        SearchResult search = search_with_reps(
            reps, job.zsize, job.wsize, 21, 21, &log, false);
        double seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - started).count();
        Witness witness;
        if (search.sat) {
            witness = generic_to_original(search.witness, job.fixed);
            auto [black, white] =
                direct_counts(witness.r, witness.c, witness.d, witness.a);
            if (black < 21 || white < 21) {
                throw std::runtime_error("batch SAT witness failed direct checker");
            }
        }
        log << "result=" << (search.sat ? "SAT" : "UNSAT")
            << " reps_enumerated=" << search.reps_enumerated
            << " completions=" << search.completions
            << " seconds=" << std::fixed << std::setprecision(6) << seconds;
        if (search.sat) log << " witness=" << json_witness(witness);
        log << '\n';
        log.close();

        std::ofstream out(opt.results, std::ios::out | std::ios::app);
        if (!out) throw std::runtime_error("cannot append " + opt.results.string());
        out << "{\"profile\":[" << job.row.profile[0] << ',' << job.row.profile[1]
            << ',' << job.row.profile[2] << ',' << job.row.profile[3] << ']'
            << ",\"S\":" << job.row.sum
            << ",\"fixed\":\"" << job.fixed << '"'
            << ",\"symmetry\":{\"epsilon\":"
            << (job.group.epsilon ? "true" : "false")
            << ",\"transpose\":" << (job.group.transpose ? "true" : "false")
            << ",\"order\":" << job.group.order() << '}'
            << ",\"reps_enumerated\":" << search.reps_enumerated
            << ",\"orbit_reps_total\":" << reps.size()
            << ",\"brief_orbit_lower_bound\":" << job.row.brief_orbits
            << ",\"completions\":" << search.completions
            << ",\"result\":\"" << (search.sat ? "SAT" : "UNSAT") << '"'
            << ",\"witness\":" << (search.sat ? json_witness(witness) : "null")
            << ",\"thresholds\":[21,21]"
            << ",\"seconds\":" << std::fixed << std::setprecision(6) << seconds
            << "}\n";
        out.close();
        ++newly_finished;
        done.insert(ptext);
        std::cout << "batch_done profile=" << ptext
                  << " result=" << (search.sat ? "SAT" : "UNSAT")
                  << " completions=" << search.completions
                  << " seconds=" << std::fixed << std::setprecision(3)
                  << seconds << '\n';
        if (search.sat) {
            std::cout << "batch_stop reason=SAT witness=" << json_witness(witness) << '\n';
            return 10;
        }
    }
    double batch_seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - batch_started).count();
    std::cout << "batch_complete newly_finished=" << newly_finished
              << " total_completed=" << done.size()
              << " seconds=" << std::fixed << std::setprecision(3)
              << batch_seconds << '\n';
    return 0;
}

} // namespace

int main(int argc, char **argv) {
    try {
        Options opt = parse_options(argc, argv);
        if (opt.self_test) {
            randomized_reference_test(opt.random_instances);
            positive_controls();
            orbit_controls();
            std::cout << "self_test result=PASS\n";
        }
        if (opt.batch) return run_batch(opt);
        if (opt.has_profile) return run_profile(opt);
        if (!opt.self_test) {
            std::cerr << "nothing to do; use --self-test or --profile (see --help)\n";
            return 2;
        }
        return 0;
    } catch (const std::exception &error) {
        std::cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
}
