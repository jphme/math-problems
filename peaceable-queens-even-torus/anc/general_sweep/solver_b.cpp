// Independent general-n exact solver for toroidal peaceable queens.
//
// Design constraint: this implementation was written from the general-n
// compute brief and mathematical proof prose only.  Its completion kernel is
// meet-in-the-middle with Pareto queries, not a suffix DFS.

#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <optional>
#include <random>
#include <regex>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace pqb {

using Mask = std::uint32_t;
using U128 = unsigned __int128;

[[noreturn]] void fail(const std::string& message) {
    throw std::runtime_error(message);
}

std::string decimal(U128 x) {
    if (x == 0) return "0";
    std::string s;
    while (x != 0) {
        s.push_back(static_cast<char>('0' + x % 10));
        x /= 10;
    }
    std::reverse(s.begin(), s.end());
    return s;
}

std::string hex_mask(Mask x, int n) {
    const int digits = (n + 3) / 4;
    std::ostringstream out;
    out << "0x" << std::hex << std::setfill('0') << std::setw(digits)
        << static_cast<std::uint64_t>(x);
    return out.str();
}

std::string json_escape(const std::string& s) {
    std::ostringstream out;
    for (unsigned char ch : s) {
        switch (ch) {
            case '"': out << "\\\""; break;
            case '\\': out << "\\\\"; break;
            case '\b': out << "\\b"; break;
            case '\f': out << "\\f"; break;
            case '\n': out << "\\n"; break;
            case '\r': out << "\\r"; break;
            case '\t': out << "\\t"; break;
            default:
                if (ch < 0x20) {
                    out << "\\u" << std::hex << std::setw(4)
                        << std::setfill('0') << static_cast<int>(ch)
                        << std::dec;
                } else {
                    out << static_cast<char>(ch);
                }
        }
    }
    return out.str();
}

std::string vec_json(const std::vector<int>& v) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < v.size(); ++i) {
        if (i) out << ',';
        out << v[i];
    }
    out << ']';
    return out.str();
}

std::string vec_key(const std::vector<int>& v) {
    std::ostringstream out;
    for (std::size_t i = 0; i < v.size(); ++i) {
        if (i) out << ',';
        out << v[i];
    }
    return out.str();
}

int mod(int x, int n) {
    x %= n;
    if (x < 0) x += n;
    return x;
}

Mask full_mask(int n) {
    if (n == 32) return std::numeric_limits<Mask>::max();
    return (Mask{1} << n) - 1;
}

Mask rotate_mask(Mask x, int shift, int n) {
    shift = mod(shift, n);
    x &= full_mask(n);
    if (shift == 0) return x;
    if (n == 32) {
        return std::rotl(x, shift);
    }
    return static_cast<Mask>(((static_cast<std::uint64_t>(x) << shift) |
                              (x >> (n - shift))) &
                             full_mask(n));
}

Mask normalize_translation(Mask x, int n) {
    Mask best = x & full_mask(n);
    for (int shift = 1; shift < n; ++shift) {
        best = std::min(best, rotate_mask(x, shift, n));
    }
    return best;
}

Mask scale_mask(Mask x, int multiplier, int n) {
    Mask y = 0;
    for (int i = 0; i < n; ++i) {
        if ((x >> i) & 1U) {
            y |= Mask{1} << mod(multiplier * i, n);
        }
    }
    return y;
}

std::vector<int> units_mod_n(int n) {
    std::vector<int> units;
    for (int u = 1; u < n; ++u) {
        if (std::gcd(u, n) == 1) units.push_back(u);
    }
    return units;
}

U128 choose(int n, int k) {
    if (k < 0 || k > n) return 0;
    k = std::min(k, n - k);
    U128 answer = 1;
    for (int i = 1; i <= k; ++i) {
        answer = answer * static_cast<unsigned>(n - k + i) /
                 static_cast<unsigned>(i);
    }
    return answer;
}

std::vector<Mask> fixed_size_necklaces(int n, int k) {
    if (n < 1 || n > 32) fail("n must be in 1..32");
    if (k < 0 || k > n) return {};
    if (k == 0) return {0};
    if (k == n) return {full_mask(n)};

    std::vector<Mask> necklaces;
    std::uint64_t x = (std::uint64_t{1} << k) - 1;
    const std::uint64_t limit = std::uint64_t{1} << n;
    while (x < limit) {
        const Mask m = static_cast<Mask>(x);
        if (normalize_translation(m, n) == m) necklaces.push_back(m);
        const std::uint64_t low = x & (~x + 1);
        const std::uint64_t ripple = x + low;
        if (ripple >= limit) break;
        x = ripple | (((ripple ^ x) >> 2) / low);
    }
    return necklaces;
}

// Minimal SHA-256 implementation used solely to fingerprint deterministic
// orbit lists and source/certificate manifests.
class Sha256 {
  public:
    void update(const void* data, std::size_t size) {
        const auto* bytes = static_cast<const std::uint8_t*>(data);
        bit_length_ += static_cast<std::uint64_t>(size) * 8;
        while (size != 0) {
            const std::size_t take = std::min(size, block_.size() - used_);
            std::copy(bytes, bytes + take, block_.begin() + used_);
            bytes += take;
            size -= take;
            used_ += take;
            if (used_ == block_.size()) {
                compress(block_.data());
                used_ = 0;
            }
        }
    }

    void update(const std::string& s) { update(s.data(), s.size()); }

    std::string finish() {
        const std::uint64_t original_bits = bit_length_;
        const std::uint8_t one = 0x80;
        update_without_length(&one, 1);
        const std::uint8_t zero = 0;
        while (used_ != 56) update_without_length(&zero, 1);
        std::array<std::uint8_t, 8> length_bytes{};
        for (int i = 0; i < 8; ++i) {
            length_bytes[7 - i] =
                static_cast<std::uint8_t>(original_bits >> (8 * i));
        }
        update_without_length(length_bytes.data(), length_bytes.size());

        std::ostringstream out;
        out << std::hex << std::setfill('0');
        for (std::uint32_t h : state_) out << std::setw(8) << h;
        return out.str();
    }

  private:
    static constexpr std::array<std::uint32_t, 64> K_ = {
        0x428a2f98U, 0x71374491U, 0xb5c0fbcfU, 0xe9b5dba5U,
        0x3956c25bU, 0x59f111f1U, 0x923f82a4U, 0xab1c5ed5U,
        0xd807aa98U, 0x12835b01U, 0x243185beU, 0x550c7dc3U,
        0x72be5d74U, 0x80deb1feU, 0x9bdc06a7U, 0xc19bf174U,
        0xe49b69c1U, 0xefbe4786U, 0x0fc19dc6U, 0x240ca1ccU,
        0x2de92c6fU, 0x4a7484aaU, 0x5cb0a9dcU, 0x76f988daU,
        0x983e5152U, 0xa831c66dU, 0xb00327c8U, 0xbf597fc7U,
        0xc6e00bf3U, 0xd5a79147U, 0x06ca6351U, 0x14292967U,
        0x27b70a85U, 0x2e1b2138U, 0x4d2c6dfcU, 0x53380d13U,
        0x650a7354U, 0x766a0abbU, 0x81c2c92eU, 0x92722c85U,
        0xa2bfe8a1U, 0xa81a664bU, 0xc24b8b70U, 0xc76c51a3U,
        0xd192e819U, 0xd6990624U, 0xf40e3585U, 0x106aa070U,
        0x19a4c116U, 0x1e376c08U, 0x2748774cU, 0x34b0bcb5U,
        0x391c0cb3U, 0x4ed8aa4aU, 0x5b9cca4fU, 0x682e6ff3U,
        0x748f82eeU, 0x78a5636fU, 0x84c87814U, 0x8cc70208U,
        0x90befffaU, 0xa4506cebU, 0xbef9a3f7U, 0xc67178f2U};

    static std::uint32_t rotr(std::uint32_t x, int n) {
        return std::rotr(x, n);
    }

    void update_without_length(const void* data, std::size_t size) {
        const auto* bytes = static_cast<const std::uint8_t*>(data);
        while (size != 0) {
            const std::size_t take = std::min(size, block_.size() - used_);
            std::copy(bytes, bytes + take, block_.begin() + used_);
            bytes += take;
            size -= take;
            used_ += take;
            if (used_ == block_.size()) {
                compress(block_.data());
                used_ = 0;
            }
        }
    }

    void compress(const std::uint8_t* block) {
        std::array<std::uint32_t, 64> w{};
        for (int i = 0; i < 16; ++i) {
            w[i] = (static_cast<std::uint32_t>(block[4 * i]) << 24) |
                   (static_cast<std::uint32_t>(block[4 * i + 1]) << 16) |
                   (static_cast<std::uint32_t>(block[4 * i + 2]) << 8) |
                   static_cast<std::uint32_t>(block[4 * i + 3]);
        }
        for (int i = 16; i < 64; ++i) {
            const std::uint32_t s0 =
                rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^
                (w[i - 15] >> 3);
            const std::uint32_t s1 =
                rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^
                (w[i - 2] >> 10);
            w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        }
        auto [a, b, c, d, e, f, g, h] = std::tuple{
            state_[0], state_[1], state_[2], state_[3],
            state_[4], state_[5], state_[6], state_[7]};
        for (int i = 0; i < 64; ++i) {
            const std::uint32_t s1 =
                rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
            const std::uint32_t ch = (e & f) ^ ((~e) & g);
            const std::uint32_t temp1 = h + s1 + ch + K_[i] + w[i];
            const std::uint32_t s0 =
                rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
            const std::uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
            const std::uint32_t temp2 = s0 + maj;
            h = g;
            g = f;
            f = e;
            e = d + temp1;
            d = c;
            c = b;
            b = a;
            a = temp1 + temp2;
        }
        state_[0] += a;
        state_[1] += b;
        state_[2] += c;
        state_[3] += d;
        state_[4] += e;
        state_[5] += f;
        state_[6] += g;
        state_[7] += h;
    }

    std::array<std::uint32_t, 8> state_ = {
        0x6a09e667U, 0xbb67ae85U, 0x3c6ef372U, 0xa54ff53aU,
        0x510e527fU, 0x9b05688cU, 0x1f83d9abU, 0x5be0cd19U};
    std::array<std::uint8_t, 64> block_{};
    std::size_t used_ = 0;
    std::uint64_t bit_length_ = 0;
};

struct ProfileSet {
    std::vector<std::vector<int>> canonical;
    std::uint64_t ordered_survivors = 0;
};

bool profile_passes(int n, int tau, const std::vector<int>& p) {
    if (n % 2 == 1) {
        if (p.size() != 4) return false;
        if (std::accumulate(p.begin(), p.end(), 0) > 2 * n) return false;
        for (int i = 0; i < 4; ++i) {
            for (int j = i + 1; j < 4; ++j) {
                if (p[i] * p[j] < tau) return false;
                if ((n - p[i]) * (n - p[j]) < tau) return false;
            }
        }
        for (int omitted = 0; omitted < 4; ++omitted) {
            std::array<int, 3> s{};
            int at = 0;
            for (int i = 0; i < 4; ++i) {
                if (i != omitted) s[at++] = p[i];
            }
            const int lhs =
                n * n - n * (s[0] + s[1] + s[2]) +
                s[0] * s[1] + s[0] * s[2] + s[1] * s[2];
            if (lhs < 2 * tau) return false;
        }
        return true;
    }

    if (p.size() != 6) return false;
    const int h = n / 2;
    const int r = p[0], c = p[1];
    const int d0 = p[2], d1 = p[3], a0 = p[4], a1 = p[5];
    const int d = d0 + d1, a = a0 + a1;
    if (r + c + d + a > 2 * n) return false;
    const std::array<std::pair<int, int>, 5> pairs = {
        std::pair{r, c}, std::pair{r, d}, std::pair{r, a},
        std::pair{c, d}, std::pair{c, a}};
    for (auto [x, y] : pairs) {
        if (x * y < tau) return false;
        if ((n - x) * (n - y) < tau) return false;
    }
    if (2 * (d0 * a0 + d1 * a1) < tau) return false;
    if (2 * ((h - d0) * (h - a0) + (h - d1) * (h - a1)) <
        tau) {
        return false;
    }
    const int rcd = n * n - n * (r + c + d) + r * c + r * d + c * d;
    const int rca = n * n - n * (r + c + a) + r * c + r * a + c * a;
    if (rcd < 2 * tau || rca < 2 * tau) return false;
    for (int x : {r, c}) {
        const int lhs = n * n - n * (x + d + a) + x * d + x * a +
                        2 * (d0 * a0 + d1 * a1);
        if (lhs < 2 * tau) return false;
    }
    return true;
}

std::vector<int> odd_g_rc(const std::vector<int>& p) {
    return {p[1], p[0], p[2], p[3]};
}
std::vector<int> odd_g_da(const std::vector<int>& p) {
    return {p[0], p[1], p[3], p[2]};
}
std::vector<int> odd_g_pair(const std::vector<int>& p) {
    // Induced by (r,c) -> ((r+c)/2,(r-c)/2).
    return {p[3], p[2], p[1], p[0]};
}

std::vector<int> even_g_rc(const std::vector<int>& p) {
    return {p[1], p[0], p[2], p[3], p[4], p[5]};
}
std::vector<int> even_g_da(const std::vector<int>& p) {
    return {p[0], p[1], p[4], p[5], p[2], p[3]};
}
std::vector<int> even_g_flip(const std::vector<int>& p) {
    return {p[0], p[1], p[3], p[2], p[5], p[4]};
}

std::vector<int> complement_profile(int n, const std::vector<int>& p) {
    if (n % 2 == 1) {
        return {n - p[0], n - p[1], n - p[2], n - p[3]};
    }
    const int h = n / 2;
    return {n - p[0], n - p[1], h - p[2], h - p[3],
            h - p[4], h - p[5]};
}

std::vector<int> canonical_profile(int n, const std::vector<int>& input) {
    std::set<std::vector<int>> seen;
    std::vector<std::vector<int>> queue{input};
    seen.insert(input);
    const bool complement_allowed =
        std::accumulate(input.begin(), input.end(), 0) == 2 * n;
    for (std::size_t at = 0; at < queue.size(); ++at) {
        const auto p = queue[at];
        std::vector<std::vector<int>> next;
        if (n % 2 == 1) {
            next = {odd_g_rc(p), odd_g_da(p), odd_g_pair(p)};
        } else {
            next = {even_g_rc(p), even_g_da(p), even_g_flip(p)};
        }
        if (complement_allowed) next.push_back(complement_profile(n, p));
        for (auto& q : next) {
            if (seen.insert(q).second) queue.push_back(std::move(q));
        }
    }
    return *seen.begin();
}

ProfileSet generate_profiles(int n, int tau) {
    std::set<std::vector<int>> canonical;
    ProfileSet result;
    if (n % 2 == 1) {
        for (int r = 0; r <= n; ++r)
            for (int c = 0; c <= n; ++c)
                for (int d = 0; d <= n; ++d)
                    for (int a = 0; a <= n; ++a) {
                        std::vector<int> p{r, c, d, a};
                        if (!profile_passes(n, tau, p)) continue;
                        ++result.ordered_survivors;
                        canonical.insert(canonical_profile(n, p));
                    }
    } else {
        const int h = n / 2;
        for (int r = 0; r <= n; ++r) {
            for (int c = 0; c <= n; ++c) {
                for (int d0 = 0; d0 <= h; ++d0) {
                    for (int d1 = 0; d1 <= h; ++d1) {
                        const int partial = r + c + d0 + d1;
                        if (partial > 2 * n) continue;
                        for (int a0 = 0; a0 <= h; ++a0) {
                            for (int a1 = 0; a1 <= h; ++a1) {
                                if (partial + a0 + a1 > 2 * n) continue;
                                std::vector<int> p{r, c, d0, d1, a0, a1};
                                if (!profile_passes(n, tau, p)) continue;
                                ++result.ordered_survivors;
                                canonical.insert(canonical_profile(n, p));
                            }
                        }
                    }
                }
            }
        }
    }
    result.canonical.assign(canonical.begin(), canonical.end());
    return result;
}

struct Job {
    int id = -1;
    std::vector<int> canonical;
    std::vector<int> oriented;
};

U128 oriented_job_cost(int n, const std::vector<int>& p);

std::vector<std::vector<int>> odd_family_orientations(
    const std::vector<int>& input) {
    std::set<std::vector<int>> seen{input};
    std::vector<std::vector<int>> queue{input};
    for (std::size_t at = 0; at < queue.size(); ++at) {
        for (auto next : {odd_g_rc(queue[at]), odd_g_da(queue[at]),
                          odd_g_pair(queue[at])}) {
            if (seen.insert(next).second) queue.push_back(std::move(next));
        }
    }
    return {seen.begin(), seen.end()};
}

std::vector<Job> make_jobs(int n, const ProfileSet& profiles) {
    std::vector<Job> jobs;
    for (const auto& p : profiles.canonical) {
        std::vector<int> base = p;
        if (n % 2 == 1) {
            // Odd boards may exchange any opposite family pair with the
            // fixed (R,C) pair.  Pick the exact cheapest D4 orientation,
            // including the resulting affine-orbit count.
            for (const auto& candidate : odd_family_orientations(p)) {
                const auto candidate_key =
                    std::pair{oriented_job_cost(n, candidate), candidate};
                const auto base_key =
                    std::pair{oriented_job_cost(n, base), base};
                if (candidate_key < base_key) base = candidate;
            }
        } else {
            // Even boards must keep (R,C) fixed, but D and A may be
            // exchanged.  Put the cheaper subset cardinality in the
            // enumerated A family.  R/C exchange is a deterministic tie
            // orientation and does not change the cost.
            const std::array<std::vector<int>, 4> candidates = {
                p, even_g_rc(p), even_g_da(p), even_g_rc(even_g_da(p))};
            for (const auto& candidate : candidates) {
                const auto candidate_key =
                    std::pair{oriented_job_cost(n, candidate), candidate};
                const auto base_key =
                    std::pair{oriented_job_cost(n, base), base};
                if (candidate_key < base_key) base = candidate;
            }
        }
        jobs.push_back(Job{-1, p, base});
        if (n % 2 == 0) {
            auto flipped = even_g_flip(base);
            if (flipped != base) {
                jobs.push_back(Job{-1, p, std::move(flipped)});
            }
        }
    }
    std::sort(jobs.begin(), jobs.end(), [](const Job& x, const Job& y) {
        return std::tie(x.canonical, x.oriented) <
               std::tie(y.canonical, y.oriented);
    });
    for (int i = 0; i < static_cast<int>(jobs.size()); ++i) jobs[i].id = i;
    return jobs;
}

struct PairGroup {
    int n = 0;
    int r = 0;
    int c = 0;
    bool transpose = false;
    bool relative_sign = false;

    auto operator<=>(const PairGroup&) const = default;
};

struct PairRep {
    Mask rows = 0;
    Mask columns = 0;
};

std::uint64_t pair_key(Mask r, Mask c, int n) {
    return (static_cast<std::uint64_t>(r) << n) | c;
}

PairRep canonical_pair(Mask rows, Mask columns, const PairGroup& group) {
    PairRep best{normalize_translation(rows, group.n),
                 normalize_translation(columns, group.n)};
    std::uint64_t best_key = pair_key(best.rows, best.columns, group.n);
    const auto units = units_mod_n(group.n);
    const int signs = group.relative_sign ? 2 : 1;
    for (int sign = 0; sign < signs; ++sign) {
        for (int u : units) {
            const int cu = sign ? mod(-u, group.n) : u;
            const Mask rr =
                normalize_translation(scale_mask(rows, u, group.n), group.n);
            const Mask cc = normalize_translation(
                scale_mask(columns, cu, group.n), group.n);
            const std::uint64_t direct = pair_key(rr, cc, group.n);
            if (direct < best_key) {
                best = {rr, cc};
                best_key = direct;
            }
            if (group.transpose) {
                const std::uint64_t swapped = pair_key(cc, rr, group.n);
                if (swapped < best_key) {
                    best = {cc, rr};
                    best_key = swapped;
                }
            }
        }
    }
    return best;
}

std::uint64_t invariant_subsets_affine(int n, int k, int multiplier,
                                       int shift) {
    std::vector<bool> seen(n, false);
    std::vector<int> cycles;
    for (int x = 0; x < n; ++x) {
        if (seen[x]) continue;
        int length = 0;
        int y = x;
        do {
            if (seen[y]) fail("affine cycle decomposition is not bijective");
            seen[y] = true;
            ++length;
            y = mod(multiplier * y + shift, n);
        } while (y != x);
        cycles.push_back(length);
    }
    std::vector<std::uint64_t> dp(k + 1, 0);
    dp[0] = 1;
    for (int length : cycles) {
        for (int s = k; s >= length; --s) dp[s] += dp[s - length];
    }
    return dp[k];
}

U128 burnside_pair_orbits(const PairGroup& group) {
    if (group.transpose && group.r != group.c) {
        fail("transpose quotient requested for unequal pair sizes");
    }
    const auto units = units_mod_n(group.n);
    const int signs = group.relative_sign ? 2 : 1;
    const int swaps = group.transpose ? 2 : 1;
    U128 fixed_sum = 0;
    for (int swapped = 0; swapped < swaps; ++swapped) {
        for (int sign = 0; sign < signs; ++sign) {
            for (int u : units) {
                const int v = sign ? mod(-u, group.n) : u;
                for (int alpha = 0; alpha < group.n; ++alpha) {
                    for (int beta = 0; beta < group.n; ++beta) {
                        if (!swapped) {
                            const auto fr = invariant_subsets_affine(
                                group.n, group.r, u, alpha);
                            const auto fc = invariant_subsets_affine(
                                group.n, group.c, v, beta);
                            fixed_sum += static_cast<U128>(fr) * fc;
                        } else {
                            // new R = u*C+alpha, new C = v*R+beta.
                            // A fixed pair is determined by an R-set invariant
                            // under x -> u(v*x+beta)+alpha.
                            const int composition_multiplier =
                                mod(u * v, group.n);
                            const int composition_shift =
                                mod(u * beta + alpha, group.n);
                            fixed_sum += invariant_subsets_affine(
                                group.n, group.r, composition_multiplier,
                                composition_shift);
                        }
                    }
                }
            }
        }
    }
    const U128 group_order = static_cast<U128>(units.size()) * group.n *
                             group.n * signs * swaps;
    if (fixed_sum % group_order != 0) fail("nonintegral Burnside average");
    return fixed_sum / group_order;
}

U128 oriented_job_cost(int n, const std::vector<int>& p) {
    if (n % 2 == 0) {
        return choose(n / 2, p[4]) * choose(n / 2, p[5]);
    }
    const PairGroup group{n, p[0], p[1], p[0] == p[1], p[2] == p[3]};
    static std::map<PairGroup, U128> orbit_count_cache;
    auto it = orbit_count_cache.find(group);
    if (it == orbit_count_cache.end()) {
        it = orbit_count_cache.emplace(group, burnside_pair_orbits(group)).first;
    }
    return it->second * choose(n, p[3]);
}

struct PairRepList {
    std::vector<PairRep> reps;
    std::string sha256;
    U128 burnside_count = 0;
};

PairRepList enumerate_pair_reps(const PairGroup& group) {
    if (group.n > 31) {
        // pair_key can represent n=32, but the current exhaustive necklace
        // generator is deliberately limited to campaigns in the brief.
        fail("pair representative enumeration currently supports n <= 31");
    }
    const auto row_necklaces = fixed_size_necklaces(group.n, group.r);
    const auto column_necklaces = fixed_size_necklaces(group.n, group.c);
    PairRepList answer;
    for (Mask rows : row_necklaces) {
        for (Mask columns : column_necklaces) {
            const auto representative = canonical_pair(rows, columns, group);
            if (representative.rows == rows &&
                representative.columns == columns) {
                answer.reps.push_back({rows, columns});
            }
        }
    }
    std::sort(answer.reps.begin(), answer.reps.end(),
              [n = group.n](const PairRep& x, const PairRep& y) {
                  return pair_key(x.rows, x.columns, n) <
                         pair_key(y.rows, y.columns, n);
              });
    answer.burnside_count = burnside_pair_orbits(group);
    if (answer.burnside_count != answer.reps.size()) {
        fail("pair representative count " +
             std::to_string(answer.reps.size()) +
             " disagrees with Burnside count " +
             decimal(answer.burnside_count) + " for (" +
             std::to_string(group.n) + "," + std::to_string(group.r) + "," +
             std::to_string(group.c) + ",transpose=" +
             std::to_string(group.transpose) + ",sign=" +
             std::to_string(group.relative_sign) + ")");
    }
    Sha256 hash;
    for (const auto& rep : answer.reps) {
        const std::string line = hex_mask(rep.rows, group.n) + "," +
                                 hex_mask(rep.columns, group.n) + "\n";
        hash.update(line);
    }
    answer.sha256 = hash.finish();
    return answer;
}

struct Incidence {
    int n = 0;
    std::vector<std::uint8_t> black;
    std::vector<std::uint8_t> white;
    std::vector<int> col_black;
    std::vector<int> col_white;
};

Incidence make_incidence(int n, Mask rows, Mask columns) {
    Incidence incidence;
    incidence.n = n;
    incidence.black.assign(n * n, 0);
    incidence.white.assign(n * n, 0);
    incidence.col_black.assign(n, 0);
    incidence.col_white.assign(n, 0);
    for (int r = 0; r < n; ++r) {
        for (int c = 0; c < n; ++c) {
            const int d = mod(r - c, n);
            const int a = (r + c) % n;
            const bool rb = (rows >> r) & 1U;
            const bool cb = (columns >> c) & 1U;
            if (rb && cb) {
                ++incidence.black[d * n + a];
                ++incidence.col_black[a];
            }
            if (!rb && !cb) {
                ++incidence.white[d * n + a];
                ++incidence.col_white[a];
            }
        }
    }
    return incidence;
}

struct VerifyResult {
    int black = 0;
    int white = 0;
};

VerifyResult verify_direct(int n, Mask rows, Mask columns, Mask diagonals,
                           Mask antidiagonals) {
    VerifyResult result;
    for (int r = 0; r < n; ++r) {
        for (int c = 0; c < n; ++c) {
            const int d = mod(r - c, n);
            const int a = (r + c) % n;
            const bool rb = (rows >> r) & 1U;
            const bool cb = (columns >> c) & 1U;
            const bool db = (diagonals >> d) & 1U;
            const bool ab = (antidiagonals >> a) & 1U;
            if (rb && cb && db && ab) ++result.black;
            if (!rb && !cb && !db && !ab) ++result.white;
        }
    }
    return result;
}

struct AEnumerationStats {
    U128 nodes = 0;
    U128 covered_candidates = 0;
    U128 emitted = 0;
    U128 pruned_black = 0;
    U128 pruned_white = 0;
};

// Enumerates exactly the fixed-cardinality A masks satisfying both column
// thresholds.  A suffix table stores the best black sum and the least
// selected-white sum for every exact remaining quota.  Thus every pruned
// subtree violates a necessary condition.
class AEnumerator {
  public:
    using Callback = std::function<bool(Mask)>;

    AEnumerator(int n, bool parity, int quota0, int quota1, int tau,
                const std::vector<int>& col_black,
                const std::vector<int>& col_white,
                const std::vector<std::uint8_t>* matrix_black = nullptr,
                const std::vector<std::uint8_t>* matrix_white = nullptr)
        : n_(n),
          parity_(parity),
          q0_(quota0),
          q1_(parity ? quota1 : 0),
          tau_(tau),
          black_(col_black),
          white_(col_white),
          total_white_(std::accumulate(white_.begin(), white_.end(), 0)),
          white_budget_(total_white_ - tau),
          dim0_(q0_ + 1),
          dim1_(q1_ + 1),
          matrix_black_(matrix_black),
          matrix_white_(matrix_white) {
        if (static_cast<int>(black_.size()) != n_ ||
            static_cast<int>(white_.size()) != n_) {
            fail("bad column vector size");
        }
        if ((matrix_black_ == nullptr) != (matrix_white_ == nullptr)) {
            fail("both detailed incidence matrices are required");
        }
        if (matrix_black_) {
            if (matrix_black_->size() != static_cast<std::size_t>(n_ * n_) ||
                matrix_white_->size() != static_cast<std::size_t>(n_ * n_)) {
                fail("bad detailed incidence matrix size");
            }
            current_black_.assign(n_, 0);
            current_white_.assign(n_, 0);
            for (int d = 0; d < n_; ++d) {
                for (int a = 0; a < n_; ++a) {
                    current_white_[d] += (*matrix_white_)[d * n_ + a];
                }
                current_white_total_ += current_white_[d];
            }
        }
        const std::size_t cells =
            static_cast<std::size_t>(n_ + 1) * dim0_ * dim1_;
        max_black_.assign(cells, kNegInf);
        min_white_.assign(cells, kPosInf);
        max_black_[index(n_, 0, 0)] = 0;
        min_white_[index(n_, 0, 0)] = 0;
        for (int pos = n_ - 1; pos >= 0; --pos) {
            const int cls = parity_ ? (pos & 1) : 0;
            for (int r0 = 0; r0 <= q0_; ++r0) {
                for (int r1 = 0; r1 <= q1_; ++r1) {
                    int best_black = max_black_[index(pos + 1, r0, r1)];
                    int best_white = min_white_[index(pos + 1, r0, r1)];
                    int t0 = r0, t1 = r1;
                    if (cls == 0) --t0;
                    else --t1;
                    if (t0 >= 0 && t1 >= 0) {
                        const int next_black =
                            max_black_[index(pos + 1, t0, t1)];
                        const int next_white =
                            min_white_[index(pos + 1, t0, t1)];
                        if (next_black != kNegInf) {
                            best_black =
                                std::max(best_black, next_black + black_[pos]);
                        }
                        if (next_white != kPosInf) {
                            best_white =
                                std::min(best_white, next_white + white_[pos]);
                        }
                    }
                    max_black_[index(pos, r0, r1)] = best_black;
                    min_white_[index(pos, r0, r1)] = best_white;
                }
            }
        }
    }

    bool enumerate(const Callback& callback) {
        callback_ = &callback;
        stopped_ = false;
        recurse(0, q0_, q1_, 0, 0, 0);
        callback_ = nullptr;
        return stopped_;
    }

    const AEnumerationStats& stats() const { return stats_; }

    U128 candidate_count() const {
        if (!parity_) return choose(n_, q0_);
        return choose((n_ + 1) / 2, q0_) * choose(n_ / 2, q1_);
    }

    bool root_possible() const {
        const int mb = max_black_[index(0, q0_, q1_)];
        const int mw = min_white_[index(0, q0_, q1_)];
        return mb != kNegInf && mb >= tau_ && mw != kPosInf &&
               mw <= white_budget_;
    }

    const std::vector<int>& current_black_by_diagonal() const {
        if (!matrix_black_) fail("detailed A state was not requested");
        return current_black_;
    }

    const std::vector<int>& current_white_by_diagonal() const {
        if (!matrix_white_) fail("detailed A state was not requested");
        return current_white_;
    }

    int current_white_total() const {
        if (!matrix_white_) fail("detailed A state was not requested");
        return current_white_total_;
    }

  private:
    static constexpr int kNegInf = -1'000'000'000;
    static constexpr int kPosInf = 1'000'000'000;

    std::size_t index(int pos, int r0, int r1) const {
        return (static_cast<std::size_t>(pos) * dim0_ + r0) * dim1_ + r1;
    }

    std::pair<int, int> remaining_class_counts(int pos) const {
        if (!parity_) return {n_ - pos, 0};
        int even = 0, odd = 0;
        for (int i = pos; i < n_; ++i) {
            if (i & 1) ++odd;
            else ++even;
        }
        return {even, odd};
    }

    U128 ways(int pos, int r0, int r1) const {
        const auto [c0, c1] = remaining_class_counts(pos);
        return choose(c0, r0) * choose(c1, r1);
    }

    void recurse(int pos, int r0, int r1, int selected_black,
                 int selected_white, Mask mask) {
        if (stopped_) return;
        ++stats_.nodes;
        if (r0 < 0 || r1 < 0) return;
        const int max_b = max_black_[index(pos, r0, r1)];
        const int min_w = min_white_[index(pos, r0, r1)];
        if (max_b == kNegInf || min_w == kPosInf) return;
        if (selected_black + max_b < tau_) {
            ++stats_.pruned_black;
            stats_.covered_candidates += ways(pos, r0, r1);
            return;
        }
        if (selected_white + min_w > white_budget_) {
            ++stats_.pruned_white;
            stats_.covered_candidates += ways(pos, r0, r1);
            return;
        }
        if (pos == n_) {
            if (r0 != 0 || r1 != 0) return;
            ++stats_.covered_candidates;
            ++stats_.emitted;
            if (!(*callback_)(mask)) stopped_ = true;
            return;
        }

        // Exclusion first gives deterministic increasing-mask order.
        recurse(pos + 1, r0, r1, selected_black, selected_white, mask);
        if (stopped_) return;
        const int cls = parity_ ? (pos & 1) : 0;
        if ((cls == 0 && r0 > 0) || (cls == 1 && r1 > 0)) {
            if (matrix_black_) {
                for (int d = 0; d < n_; ++d) {
                    current_black_[d] += (*matrix_black_)[d * n_ + pos];
                    current_white_[d] -= (*matrix_white_)[d * n_ + pos];
                }
                current_white_total_ -= white_[pos];
            }
            recurse(pos + 1, r0 - (cls == 0), r1 - (cls == 1),
                    selected_black + black_[pos],
                    selected_white + white_[pos], mask | (Mask{1} << pos));
            if (matrix_black_) {
                for (int d = 0; d < n_; ++d) {
                    current_black_[d] -= (*matrix_black_)[d * n_ + pos];
                    current_white_[d] += (*matrix_white_)[d * n_ + pos];
                }
                current_white_total_ += white_[pos];
            }
        }
    }

    int n_;
    bool parity_;
    int q0_;
    int q1_;
    int tau_;
    std::vector<int> black_;
    std::vector<int> white_;
    int total_white_;
    int white_budget_;
    int dim0_;
    int dim1_;
    std::vector<int> max_black_;
    std::vector<int> min_white_;
    const Callback* callback_ = nullptr;
    bool stopped_ = false;
    AEnumerationStats stats_;
    const std::vector<std::uint8_t>* matrix_black_;
    const std::vector<std::uint8_t>* matrix_white_;
    std::vector<int> current_black_;
    std::vector<int> current_white_;
    int current_white_total_ = 0;
};

struct CompletionStats {
    U128 left_records = 0;
    U128 right_records = 0;
    U128 pareto_queries = 0;
    bool root_pruned = false;
};

struct CompletionResult {
    bool sat = false;
    Mask diagonals = 0;
    CompletionStats stats;
};

struct HalfRecord {
    int black = 0;
    int white = 0;
    Mask mask = 0;
    std::uint8_t k0 = 0;
    std::uint8_t k1 = 0;
};

std::pair<int, int> independent_extrema(const std::vector<int>& black,
                                        const std::vector<int>& white,
                                        bool parity, int q0, int q1) {
    std::array<std::array<int, 33>, 2> black_hist{};
    std::array<std::array<int, 33>, 2> white_hist{};
    std::array<int, 2> available{};
    for (int i = 0; i < static_cast<int>(black.size()); ++i) {
        const int cls = parity ? (i & 1) : 0;
        if (black[i] < 0 || black[i] > 32 || white[i] < 0 ||
            white[i] > 32) {
            fail("completion values outside supported 0..32 range");
        }
        ++black_hist[cls][black[i]];
        ++white_hist[cls][white[i]];
        ++available[cls];
    }
    int max_black = 0;
    int min_white = 0;
    for (int cls = 0; cls < (parity ? 2 : 1); ++cls) {
        const int quota = cls == 0 ? q0 : q1;
        if (quota > available[cls]) return {-1, -1};
        int remaining = quota;
        for (int value = 32; value >= 0 && remaining > 0; --value) {
            const int take = std::min(remaining, black_hist[cls][value]);
            max_black += take * value;
            remaining -= take;
        }
        remaining = quota;
        for (int value = 0; value <= 32 && remaining > 0; ++value) {
            const int take = std::min(remaining, white_hist[cls][value]);
            min_white += take * value;
            remaining -= take;
        }
    }
    return {max_black, min_white};
}

std::vector<HalfRecord> enumerate_half(const std::vector<int>& black,
                                       const std::vector<int>& white,
                                       int offset, int length, bool parity,
                                       int max0, int max1) {
    const std::uint32_t count = std::uint32_t{1} << length;
    std::vector<int> sum_black(count, 0), sum_white(count, 0);
    std::vector<std::uint8_t> cnt0(count, 0), cnt1(count, 0);
    std::vector<HalfRecord> records;
    records.reserve(count);
    records.push_back(HalfRecord{});
    for (std::uint32_t bits = 1; bits < count; ++bits) {
        const std::uint32_t previous = bits & (bits - 1);
        const int local = std::countr_zero(bits);
        const int item = offset + local;
        sum_black[bits] = sum_black[previous] + black[item];
        sum_white[bits] = sum_white[previous] + white[item];
        cnt0[bits] = cnt0[previous];
        cnt1[bits] = cnt1[previous];
        const int cls = parity ? (item & 1) : 0;
        if (cls == 0) ++cnt0[bits];
        else ++cnt1[bits];
        if (cnt0[bits] <= max0 && cnt1[bits] <= max1) {
            const Mask global_mask = static_cast<Mask>(bits) << offset;
            records.push_back(HalfRecord{
                sum_black[bits], sum_white[bits], global_mask,
                cnt0[bits], cnt1[bits]});
        }
    }
    return records;
}

CompletionResult complete_mitm(const std::vector<int>& black,
                               const std::vector<int>& white, bool parity,
                               int quota0, int quota1, int black_target,
                               int white_budget) {
    if (black.size() != white.size() || black.empty() ||
        black.size() > 32) {
        fail("bad completion instance");
    }
    if (!parity) quota1 = 0;
    CompletionResult answer;
    const auto [max_black, min_white] =
        independent_extrema(black, white, parity, quota0, quota1);
    if (max_black < black_target || min_white > white_budget) {
        answer.stats.root_pruned = true;
        return answer;
    }

    const int n = static_cast<int>(black.size());
    const int left_length = n / 2;
    const int right_length = n - left_length;
    auto left = enumerate_half(black, white, 0, left_length, parity,
                               quota0, quota1);
    auto right = enumerate_half(black, white, left_length, right_length,
                                parity, quota0, quota1);
    answer.stats.left_records = left.size();
    answer.stats.right_records = right.size();

    const int width = quota1 + 1;
    std::vector<std::vector<HalfRecord>> groups(
        static_cast<std::size_t>(quota0 + 1) * width);
    auto group_index = [width](int k0, int k1) {
        return static_cast<std::size_t>(k0) * width + k1;
    };
    for (const auto& rec : right) {
        groups[group_index(rec.k0, rec.k1)].push_back(rec);
    }

    struct Frontier {
        std::vector<HalfRecord> sorted;
        std::vector<int> prefix_min_white;
        std::vector<Mask> prefix_mask;
    };
    std::vector<Frontier> frontiers(groups.size());
    for (std::size_t g = 0; g < groups.size(); ++g) {
        auto& f = frontiers[g];
        f.sorted = std::move(groups[g]);
        std::sort(f.sorted.begin(), f.sorted.end(),
                  [](const HalfRecord& x, const HalfRecord& y) {
                      if (x.black != y.black) return x.black > y.black;
                      if (x.white != y.white) return x.white < y.white;
                      return x.mask < y.mask;
                  });
        f.prefix_min_white.resize(f.sorted.size());
        f.prefix_mask.resize(f.sorted.size());
        int best_white = std::numeric_limits<int>::max();
        Mask best_mask = 0;
        for (std::size_t i = 0; i < f.sorted.size(); ++i) {
            if (f.sorted[i].white < best_white ||
                (f.sorted[i].white == best_white &&
                 f.sorted[i].mask < best_mask)) {
                best_white = f.sorted[i].white;
                best_mask = f.sorted[i].mask;
            }
            f.prefix_min_white[i] = best_white;
            f.prefix_mask[i] = best_mask;
        }
    }

    for (const auto& l : left) {
        const int need0 = quota0 - l.k0;
        const int need1 = quota1 - l.k1;
        if (need0 < 0 || need1 < 0) continue;
        const auto& f = frontiers[group_index(need0, need1)];
        if (f.sorted.empty()) continue;
        const int need_black = black_target - l.black;
        const int allow_white = white_budget - l.white;
        ++answer.stats.pareto_queries;
        std::size_t lo = 0, hi = f.sorted.size();
        while (lo < hi) {
            const std::size_t mid = lo + (hi - lo) / 2;
            if (f.sorted[mid].black >= need_black) lo = mid + 1;
            else hi = mid;
        }
        if (lo == 0) continue;
        const std::size_t last = lo - 1;
        if (f.prefix_min_white[last] <= allow_white) {
            answer.sat = true;
            answer.diagonals = l.mask | f.prefix_mask[last];
            int check_black = 0, check_white = 0, c0 = 0, c1 = 0;
            for (int i = 0; i < n; ++i) {
                if (!((answer.diagonals >> i) & 1U)) continue;
                check_black += black[i];
                check_white += white[i];
                if (parity && (i & 1)) ++c1;
                else ++c0;
            }
            if (check_black < black_target || check_white > white_budget ||
                c0 != quota0 || c1 != quota1) {
                fail("meet-in-the-middle reconstruction failed");
            }
            return answer;
        }
    }
    return answer;
}

CompletionResult complete_bruteforce(const std::vector<int>& black,
                                     const std::vector<int>& white,
                                     bool parity, int quota0, int quota1,
                                     int black_target, int white_budget) {
    const int n = static_cast<int>(black.size());
    if (n > 20) fail("brute force restricted to at most 20 items");
    if (!parity) quota1 = 0;
    const std::uint64_t limit = std::uint64_t{1} << n;
    for (std::uint64_t bits = 0; bits < limit; ++bits) {
        int b = 0, w = 0, k0 = 0, k1 = 0;
        for (int i = 0; i < n; ++i) {
            if (!((bits >> i) & 1U)) continue;
            b += black[i];
            w += white[i];
            if (parity && (i & 1)) ++k1;
            else ++k0;
        }
        if (k0 == quota0 && k1 == quota1 && b >= black_target &&
            w <= white_budget) {
            return CompletionResult{true, static_cast<Mask>(bits), {}};
        }
    }
    return {};
}

void vectors_for_antidiagonal(const Incidence& incidence, Mask a_mask,
                              std::vector<int>& p, std::vector<int>& q,
                              int& q_total) {
    const int n = incidence.n;
    p.assign(n, 0);
    q.assign(n, 0);
    q_total = 0;
    for (int d = 0; d < n; ++d) {
        for (int a = 0; a < n; ++a) {
            if ((a_mask >> a) & 1U) {
                p[d] += incidence.black[d * n + a];
            } else {
                q[d] += incidence.white[d * n + a];
            }
        }
        q_total += q[d];
    }
}

Mask mask_of(std::initializer_list<int> values) {
    Mask answer = 0;
    for (int x : values) answer |= Mask{1} << x;
    return answer;
}

struct PositiveControl {
    int n;
    Mask rows;
    Mask columns;
    Mask diagonals;
    Mask antidiagonals;
    int expected_black;
    int expected_white;
};

std::vector<PositiveControl> positive_controls() {
    return {
        {15,
         mask_of({5, 7, 8, 11, 12, 14}),
         mask_of({0, 3, 4, 7, 9, 10, 12, 13}),
         mask_of({0, 1, 4, 8, 12, 13, 14}),
         mask_of({1, 2, 3, 9, 10, 12, 14}),
         20,
         22},
        {16,
         mask_of({5, 7, 9, 11, 13, 15}),
         mask_of({5, 7, 9, 11, 13, 15}),
         mask_of({0, 2, 4, 6, 8, 10, 12, 14}),
         mask_of({0, 2, 4, 6, 8, 10, 12, 14}),
         36,
         32},
        {17,
         mask_of({0, 1, 5, 6, 7, 11, 12, 14, 15}),
         mask_of({1, 5, 6, 8, 9, 11, 12, 16}),
         mask_of({1, 5, 6, 7, 11, 13, 14, 15, 16}),
         mask_of({1, 5, 7, 11, 13, 14, 15, 16}),
         28,
         28},
        {18,
         mask_of({1, 3, 7, 9, 11, 15}),
         mask_of({1, 2, 7, 9, 11, 13, 15, 17}),
         mask_of({0, 2, 4, 6, 8, 10, 12, 14, 16}),
         mask_of({0, 2, 4, 6, 8, 10, 12, 14, 16}),
         42,
         42},
    };
}

void test_sha256() {
    Sha256 hash;
    hash.update("abc");
    const std::string got = hash.finish();
    const std::string expected =
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
    if (got != expected) fail("SHA-256 self-test failed: " + got);
}

void test_two_lifts(int n) {
    if (n % 2 != 0) fail("two-lift test requires even n");
    for (int d = 0; d < n; ++d) {
        for (int a = 0; a < n; ++a) {
            int count = 0;
            for (int r = 0; r < n; ++r) {
                for (int c = 0; c < n; ++c) {
                    if (mod(r - c, n) == d && (r + c) % n == a) ++count;
                }
            }
            const int expected = ((d ^ a) & 1) ? 0 : 2;
            if (count != expected) {
                fail("two-lift incidence failure at n=" + std::to_string(n));
            }
        }
    }
}

void test_positive_controls() {
    for (const auto& control : positive_controls()) {
        const auto direct =
            verify_direct(control.n, control.rows, control.columns,
                          control.diagonals, control.antidiagonals);
        if (direct.black != control.expected_black ||
            direct.white != control.expected_white) {
            fail("positive control direct count failed for n=" +
                 std::to_string(control.n) + ": got " +
                 std::to_string(direct.black) + "/" +
                 std::to_string(direct.white));
        }
        const auto incidence =
            make_incidence(control.n, control.rows, control.columns);
        std::vector<int> p, q;
        int q_total = 0;
        vectors_for_antidiagonal(incidence, control.antidiagonals, p, q,
                                 q_total);
        const bool parity = control.n % 2 == 0;
        int d0 = 0, d1 = 0;
        for (int d = 0; d < control.n; ++d) {
            if (!((control.diagonals >> d) & 1U)) continue;
            if (parity && (d & 1)) ++d1;
            else ++d0;
        }
        const int target = std::min(control.expected_black,
                                    control.expected_white);
        const auto completion = complete_mitm(
            p, q, parity, d0, d1, target, q_total - target);
        if (!completion.sat) {
            fail("positive control completion failed for n=" +
                 std::to_string(control.n));
        }
        const auto reconstructed =
            verify_direct(control.n, control.rows, control.columns,
                          completion.diagonals, control.antidiagonals);
        if (reconstructed.black < target || reconstructed.white < target) {
            fail("positive control reconstructed witness failed");
        }
        std::vector<int> profile;
        if (!parity) {
            profile = {std::popcount(control.rows),
                       std::popcount(control.columns),
                       std::popcount(control.diagonals),
                       std::popcount(control.antidiagonals)};
        } else {
            int a0 = 0, a1 = 0;
            for (int a = 0; a < control.n; ++a) {
                if (!((control.antidiagonals >> a) & 1U)) continue;
                if (a & 1) ++a1;
                else ++a0;
            }
            profile = {std::popcount(control.rows),
                       std::popcount(control.columns), d0, d1, a0, a1};
        }
        if (!profile_passes(control.n, target, profile)) {
            fail("positive control profile rejected at its SAT target");
        }
    }
}

void test_profiles() {
    {
        const auto p15 = generate_profiles(15, 21);
        if (p15.canonical.size() != 247) {
            fail("n=15 profile count mismatch: " +
                 std::to_string(p15.canonical.size()));
        }
    }
    {
        const auto p16 = generate_profiles(16, 33);
        const auto jobs16 = make_jobs(16, p16);
        if (p16.ordered_survivors != 1898 ||
            p16.canonical.size() != 342 || jobs16.size() != 677) {
            fail("n=16 profile gate mismatch: ordered=" +
                 std::to_string(p16.ordered_survivors) +
                 " canonical=" + std::to_string(p16.canonical.size()) +
                 " jobs=" + std::to_string(jobs16.size()));
        }
    }
    {
        const auto p17 = generate_profiles(17, 29);
        if (p17.ordered_survivors != 2145 || p17.canonical.size() != 316) {
            fail("n=17 profile gate mismatch");
        }
    }
    {
        const auto p18 = generate_profiles(18, 43);
        if (p18.ordered_survivors != 641 || p18.canonical.size() != 130) {
            fail("n=18 profile gate mismatch");
        }
    }
}

void test_burnside_references() {
    const std::array<std::pair<PairGroup, U128>, 3> cases = {
        std::pair{PairGroup{15, 7, 7, true, false}, U128{11793}},
        std::pair{PairGroup{15, 7, 7, true, true}, U128{6892}},
        std::pair{PairGroup{15, 7, 8, false, true}, U128{13654}},
    };
    for (const auto& [group, expected] : cases) {
        const U128 got = burnside_pair_orbits(group);
        if (got != expected) {
            fail("Burnside reference mismatch: got " + decimal(got) +
                 " expected " + decimal(expected));
        }
    }
}

void test_completion_random(std::uint64_t cases) {
    std::mt19937_64 rng(0x5045515545454e42ULL);
    for (std::uint64_t trial = 0; trial < cases; ++trial) {
        const int n = 1 + static_cast<int>(rng() % 9);
        const bool parity = (n % 2 == 0) && ((rng() & 1U) != 0);
        std::vector<int> p(n), q(n);
        int total_p = 0, total_q = 0;
        for (int i = 0; i < n; ++i) {
            p[i] = static_cast<int>(rng() % 7);
            q[i] = static_cast<int>(rng() % 7);
            total_p += p[i];
            total_q += q[i];
        }
        int quota0 = 0, quota1 = 0;
        if (parity) {
            quota0 = static_cast<int>(rng() % ((n + 1) / 2 + 1));
            quota1 = static_cast<int>(rng() % (n / 2 + 1));
        } else {
            quota0 = static_cast<int>(rng() % (n + 1));
        }
        const int black_target =
            static_cast<int>(rng() % static_cast<std::uint64_t>(total_p + 5));
        const int white_budget =
            static_cast<int>(rng() %
                             static_cast<std::uint64_t>(total_q + 7)) -
            3;
        const auto fast = complete_mitm(p, q, parity, quota0, quota1,
                                        black_target, white_budget);
        const auto brute = complete_bruteforce(
            p, q, parity, quota0, quota1, black_target, white_budget);
        if (fast.sat != brute.sat) {
            fail("completion randomized mismatch at trial " +
                 std::to_string(trial));
        }
    }
}

void test_a_enumerator_random(std::uint64_t cases) {
    std::mt19937_64 rng(0x41454e554d455241ULL);
    for (std::uint64_t trial = 0; trial < cases; ++trial) {
        const int n = 1 + static_cast<int>(rng() % 10);
        const bool parity = (n % 2 == 0) && ((rng() & 1U) != 0);
        int quota0 = 0, quota1 = 0;
        if (parity) {
            quota0 = static_cast<int>(rng() % ((n + 1) / 2 + 1));
            quota1 = static_cast<int>(rng() % (n / 2 + 1));
        } else {
            quota0 = static_cast<int>(rng() % (n + 1));
        }
        std::vector<int> bp(n, 0), wq(n, 0);
        std::vector<std::uint8_t> matrix_black(n * n);
        std::vector<std::uint8_t> matrix_white(n * n);
        int total_white = 0;
        for (int d = 0; d < n; ++d) {
            for (int a = 0; a < n; ++a) {
                matrix_black[d * n + a] =
                    static_cast<std::uint8_t>(rng() % 3);
                matrix_white[d * n + a] =
                    static_cast<std::uint8_t>(rng() % 3);
                bp[a] += matrix_black[d * n + a];
                wq[a] += matrix_white[d * n + a];
            }
        }
        total_white = std::accumulate(wq.begin(), wq.end(), 0);
        const int tau =
            static_cast<int>(rng() %
                             static_cast<std::uint64_t>(
                                 std::max(1, total_white + 5)));
        AEnumerator enumerator(n, parity, quota0, quota1, tau, bp, wq,
                               &matrix_black, &matrix_white);
        std::vector<Mask> got;
        enumerator.enumerate([&](Mask mask) {
            std::vector<int> direct_black(n, 0), direct_white(n, 0);
            int direct_white_total = 0;
            for (int d = 0; d < n; ++d) {
                for (int a = 0; a < n; ++a) {
                    if ((mask >> a) & 1U) {
                        direct_black[d] += matrix_black[d * n + a];
                    } else {
                        direct_white[d] += matrix_white[d * n + a];
                    }
                }
                direct_white_total += direct_white[d];
            }
            if (direct_black != enumerator.current_black_by_diagonal() ||
                direct_white != enumerator.current_white_by_diagonal() ||
                direct_white_total != enumerator.current_white_total()) {
                fail("detailed A traversal state mismatch");
            }
            got.push_back(mask);
            return true;
        });
        std::vector<Mask> expected;
        const std::uint64_t limit = std::uint64_t{1} << n;
        for (std::uint64_t bits = 0; bits < limit; ++bits) {
            int k0 = 0, k1 = 0, black = 0, selected_white = 0;
            for (int i = 0; i < n; ++i) {
                if (!((bits >> i) & 1U)) continue;
                if (parity && (i & 1)) ++k1;
                else ++k0;
                black += bp[i];
                selected_white += wq[i];
            }
            if (k0 == quota0 && k1 == quota1 && black >= tau &&
                total_white - selected_white >= tau) {
                expected.push_back(static_cast<Mask>(bits));
            }
        }
        std::sort(got.begin(), got.end());
        if (got != expected) {
            fail("A enumerator randomized mismatch at trial " +
                 std::to_string(trial));
        }
        if (enumerator.stats().covered_candidates !=
            enumerator.candidate_count()) {
            fail("A enumerator coverage accounting mismatch");
        }
    }
}

void run_self_tests(std::uint64_t completion_cases = 100000,
                    std::uint64_t a_cases = 5000) {
    if (completion_cases < 100000) {
        fail("soundness gate requires at least 100000 completion cases");
    }
    const auto started = std::chrono::steady_clock::now();
    test_sha256();
    test_two_lifts(16);
    test_two_lifts(18);
    test_positive_controls();
    test_profiles();
    test_burnside_references();
    test_completion_random(completion_cases);
    test_a_enumerator_random(a_cases);
    const double seconds =
        std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                      started)
            .count();
    std::cerr << "SELF_TEST_OK completion_cases=" << completion_cases
              << " a_enumerator_cases=" << a_cases
              << " positive_controls=4 profile_gates=4 burnside_refs=3"
              << " seconds=" << std::fixed << std::setprecision(3)
              << seconds << "\n";
}

struct JobStats {
    U128 a_space = 0;
    U128 a_checked = 0;
    U128 a_nodes = 0;
    U128 a_survivors = 0;
    U128 a_pruned_black = 0;
    U128 a_pruned_white = 0;
    U128 pair_early_kills = 0;
    U128 completion_calls = 0;
    U128 completion_root_prunes = 0;
    U128 mitm_left_records = 0;
    U128 mitm_right_records = 0;
    U128 mitm_queries = 0;
};

struct JobResult {
    bool complete = true;
    bool sat = false;
    Mask witness_rows = 0;
    Mask witness_columns = 0;
    Mask witness_diagonals = 0;
    Mask witness_antidiagonals = 0;
    int witness_black = 0;
    int witness_white = 0;
    std::size_t pair_orbits = 0;
    std::string orbit_sha256;
    JobStats stats;
    double seconds = 0.0;
};

struct JobParameters {
    int r = 0;
    int c = 0;
    int d0 = 0;
    int d1 = 0;
    int a0 = 0;
    int a1 = 0;
    bool parity = false;
    bool transpose = false;
    bool relative_sign = false;
};

JobParameters parameters_for(int n, const std::vector<int>& p) {
    JobParameters x;
    x.r = p[0];
    x.c = p[1];
    x.parity = n % 2 == 0;
    if (!x.parity) {
        x.d0 = p[2];
        x.a0 = p[3];
    } else {
        x.d0 = p[2];
        x.d1 = p[3];
        x.a0 = p[4];
        x.a1 = p[5];
    }
    x.transpose = x.r == x.c;
    x.relative_sign = x.d0 == x.a0 && x.d1 == x.a1;
    return x;
}

U128 a_count_per_pair(int n, const JobParameters& p) {
    if (!p.parity) return choose(n, p.a0);
    return choose(n / 2, p.a0) * choose(n / 2, p.a1);
}

JobResult solve_job(int n, int target, const Job& job,
                    const PairRepList& pair_list,
                    std::optional<std::size_t> max_reps = std::nullopt) {
    const auto started = std::chrono::steady_clock::now();
    JobResult result;
    result.pair_orbits = pair_list.reps.size();
    result.orbit_sha256 = pair_list.sha256;
    const auto params = parameters_for(n, job.oriented);
    const U128 per_pair = a_count_per_pair(n, params);
    result.stats.a_space =
        static_cast<U128>(pair_list.reps.size()) * per_pair;

    const std::size_t reps_to_run =
        max_reps ? std::min(*max_reps, pair_list.reps.size())
                 : pair_list.reps.size();
    if (max_reps && reps_to_run != pair_list.reps.size()) {
        result.complete = false;
    }

    for (std::size_t rep_index = 0; rep_index < reps_to_run; ++rep_index) {
        const auto& rep = pair_list.reps[rep_index];
        const auto incidence = make_incidence(n, rep.rows, rep.columns);
        AEnumerator enumerator(n, params.parity, params.a0, params.a1,
                               target, incidence.col_black,
                               incidence.col_white, &incidence.black,
                               &incidence.white);
        if (!enumerator.root_possible()) ++result.stats.pair_early_kills;
        const bool stopped = enumerator.enumerate([&](Mask antidiagonals) {
            ++result.stats.completion_calls;
            const auto& p = enumerator.current_black_by_diagonal();
            const auto& q = enumerator.current_white_by_diagonal();
            const int q_total = enumerator.current_white_total();
            auto completion = complete_mitm(
                p, q, params.parity, params.d0, params.d1, target,
                q_total - target);
            if (completion.stats.root_pruned) {
                ++result.stats.completion_root_prunes;
            }
            result.stats.mitm_left_records +=
                completion.stats.left_records;
            result.stats.mitm_right_records +=
                completion.stats.right_records;
            result.stats.mitm_queries += completion.stats.pareto_queries;
            if (!completion.sat) return true;

            const auto direct =
                verify_direct(n, rep.rows, rep.columns,
                              completion.diagonals, antidiagonals);
            if (direct.black < target || direct.white < target) {
                fail("direct witness verification rejected SAT completion");
            }
            result.sat = true;
            result.witness_rows = rep.rows;
            result.witness_columns = rep.columns;
            result.witness_diagonals = completion.diagonals;
            result.witness_antidiagonals = antidiagonals;
            result.witness_black = direct.black;
            result.witness_white = direct.white;
            return false;
        });
        const auto& es = enumerator.stats();
        result.stats.a_checked += es.covered_candidates;
        result.stats.a_nodes += es.nodes;
        result.stats.a_survivors += es.emitted;
        result.stats.a_pruned_black += es.pruned_black;
        result.stats.a_pruned_white += es.pruned_white;
        if (stopped != result.sat) fail("enumerator stop/SAT mismatch");
        if (result.sat) break;
    }

    if (result.complete && !result.sat &&
        result.stats.a_checked != result.stats.a_space) {
        fail("UNSAT job did not cover its full A candidate space");
    }
    if (result.sat) result.complete = true;
    result.seconds =
        std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                      started)
            .count();
    return result;
}

std::string job_key(int n, int target, const Job& job) {
    return "n" + std::to_string(n) + "-t" + std::to_string(target) + "-j" +
           std::to_string(job.id) + "-" + vec_key(job.oriented);
}

std::string job_record_json(int n, int target, const Job& job,
                            const JobParameters& params,
                            const JobResult& result) {
    std::ostringstream out;
    out << '{'
        << "\"schema\":\"peaceable-queens-impl-b-job-v1\","
        << "\"algorithm\":\"mitm-pareto-output-sensitive-a\","
        << "\"n\":" << n << ','
        << "\"target\":" << target << ','
        << "\"job_id\":" << job.id << ','
        << "\"job_key\":\"" << job_key(n, target, job) << "\","
        << "\"canonical_profile\":" << vec_json(job.canonical) << ','
        << "\"oriented_profile\":" << vec_json(job.oriented) << ','
        << "\"S\":"
        << std::accumulate(job.oriented.begin(), job.oriented.end(), 0)
        << ','
        << "\"r\":" << params.r << ','
        << "\"c\":" << params.c << ','
        << "\"d0\":" << params.d0 << ','
        << "\"d1\":" << params.d1 << ','
        << "\"a0\":" << params.a0 << ','
        << "\"a1\":" << params.a1 << ','
        << "\"parity_refined\":" << (params.parity ? "true" : "false")
        << ','
        << "\"transpose_quotient\":"
        << (params.transpose ? "true" : "false") << ','
        << "\"relative_sign_quotient\":"
        << (params.relative_sign ? "true" : "false") << ','
        << "\"orbit_count\":" << result.pair_orbits << ','
        << "\"orbit_list_sha256\":\"" << result.orbit_sha256 << "\","
        << "\"a_count_per_orbit\":\""
        << decimal(a_count_per_pair(n, params)) << "\","
        << "\"a_space\":\"" << decimal(result.stats.a_space) << "\","
        << "\"a_checked\":\"" << decimal(result.stats.a_checked) << "\","
        << "\"a_enumeration_nodes\":\"" << decimal(result.stats.a_nodes)
        << "\","
        << "\"prefilter_survivors\":\""
        << decimal(result.stats.a_survivors) << "\","
        << "\"a_pruned_black\":\""
        << decimal(result.stats.a_pruned_black) << "\","
        << "\"a_pruned_white\":\""
        << decimal(result.stats.a_pruned_white) << "\","
        << "\"pair_early_kills\":\""
        << decimal(result.stats.pair_early_kills) << "\","
        << "\"exact_calls\":\""
        << decimal(result.stats.completion_calls) << "\","
        << "\"completion_root_prunes\":\""
        << decimal(result.stats.completion_root_prunes) << "\","
        << "\"mitm_left_records\":\""
        << decimal(result.stats.mitm_left_records) << "\","
        << "\"mitm_right_records\":\""
        << decimal(result.stats.mitm_right_records) << "\","
        << "\"mitm_queries\":\"" << decimal(result.stats.mitm_queries)
        << "\","
        << "\"verdict\":\"" << (result.sat ? "SAT" : "UNSAT") << "\","
        << "\"complete\":" << (result.complete ? "true" : "false") << ',';
    if (result.sat) {
        out << "\"witness\":{"
            << "\"R\":\"" << hex_mask(result.witness_rows, n) << "\","
            << "\"C\":\"" << hex_mask(result.witness_columns, n) << "\","
            << "\"D\":\"" << hex_mask(result.witness_diagonals, n) << "\","
            << "\"A\":\"" << hex_mask(result.witness_antidiagonals, n)
            << "\","
            << "\"B\":" << result.witness_black << ','
            << "\"W\":" << result.witness_white << "},";
    } else {
        out << "\"witness\":null,";
    }
    out << "\"seconds\":" << std::fixed << std::setprecision(6)
        << result.seconds << '}';
    return out.str();
}

std::map<int, std::string> completed_jobs(
    const std::filesystem::path& records, int n, int target) {
    std::map<int, std::string> completed;
    std::ifstream in(records);
    if (!in) return completed;
    std::string line;
    const std::regex prefix(
        R"JOB(^\{"schema":"peaceable-queens-impl-b-job-v1","algorithm":"mitm-pareto-output-sensitive-a","n":([0-9]+),"target":([0-9]+),"job_id":([0-9]+),"job_key":"([^"]+)")JOB");
    const std::regex completion(R"(,"complete":(true|false),)");
    int line_number = 0;
    while (std::getline(in, line)) {
        ++line_number;
        if (line.empty() || line[0] == '#') continue;
        std::smatch header_match, complete_match;
        if (line.back() != '}' ||
            !std::regex_search(line, header_match, prefix) ||
            !std::regex_search(line, complete_match, completion)) {
            fail("malformed JSONL job record at " + records.string() + ":" +
                 std::to_string(line_number));
        }
        const int record_n = std::stoi(header_match[1].str());
        const int record_target = std::stoi(header_match[2].str());
        const int id = std::stoi(header_match[3].str());
        const std::string key = header_match[4].str();
        const bool is_complete = complete_match[1].str() == "true";
        if (record_n != n || record_target != target || !is_complete) continue;
        const auto [it, inserted] = completed.emplace(id, key);
        if (!inserted && it->second != key) {
            fail("conflicting completed job records for id " +
                 std::to_string(id));
        }
    }
    return completed;
}

void atomic_job_log(const std::filesystem::path& directory, int job_id,
                    const std::string& record) {
    std::filesystem::create_directories(directory);
    std::ostringstream name;
    name << "job-" << std::setfill('0') << std::setw(6) << job_id << ".json";
    const auto final_path = directory / name.str();
    const auto temp_path = final_path.string() + ".tmp";
    {
        std::ofstream out(temp_path, std::ios::trunc);
        if (!out) fail("cannot write temporary job log " + temp_path);
        out << record << '\n';
        out.flush();
        if (!out) fail("failed writing temporary job log");
    }
    std::error_code ec;
    std::filesystem::rename(temp_path, final_path, ec);
    if (ec) {
        std::filesystem::remove(final_path, ec);
        ec.clear();
        std::filesystem::rename(temp_path, final_path, ec);
        if (ec) fail("cannot install job log " + final_path.string());
    }
}

struct SolveOptions {
    int n = 0;
    int target = 0;
    std::filesystem::path records;
    std::filesystem::path log_dir;
    std::optional<int> only_job;
    std::optional<int> max_jobs;
    std::optional<std::size_t> max_reps;
    std::optional<int> job_modulus;
    std::optional<int> job_remainder;
};

void run_campaign(const SolveOptions& options) {
    const auto profiles = generate_profiles(options.n, options.target);
    const auto jobs = make_jobs(options.n, profiles);
    std::cerr << "WORKLIST n=" << options.n << " target=" << options.target
              << " ordered=" << profiles.ordered_survivors
              << " canonical=" << profiles.canonical.size()
              << " oriented_jobs=" << jobs.size() << "\n";

    if (!options.records.parent_path().empty()) {
        std::filesystem::create_directories(options.records.parent_path());
    }
    auto done = completed_jobs(options.records, options.n, options.target);
    std::ofstream records(options.records, std::ios::app);
    if (!records) fail("cannot append records file " + options.records.string());

    std::map<PairGroup, PairRepList> orbit_cache;
    int jobs_run = 0;
    bool campaign_sat = false;
    for (const auto& job : jobs) {
        if (options.only_job && job.id != *options.only_job) continue;
        if (options.job_modulus &&
            job.id % *options.job_modulus != *options.job_remainder) {
            continue;
        }
        if (const auto done_it = done.find(job.id); done_it != done.end()) {
            const std::string expected_key =
                job_key(options.n, options.target, job);
            if (done_it->second != expected_key) {
                fail("completed job id " + std::to_string(job.id) +
                     " has stale key " + done_it->second +
                     "; expected " + expected_key +
                     " (use a fresh versioned campaign directory)");
            }
            std::cerr << "SKIP completed job=" << job.id << "\n";
            continue;
        }
        if (options.max_jobs && jobs_run >= *options.max_jobs) break;
        const auto params = parameters_for(options.n, job.oriented);
        const PairGroup group{options.n, params.r, params.c,
                              params.transpose, params.relative_sign};
        auto cache_it = orbit_cache.find(group);
        if (cache_it == orbit_cache.end()) {
            std::cerr << "ORBITS generate r=" << params.r
                      << " c=" << params.c
                      << " transpose=" << params.transpose
                      << " sign=" << params.relative_sign << "\n";
            cache_it =
                orbit_cache.emplace(group, enumerate_pair_reps(group)).first;
            std::cerr << "ORBITS_OK count=" << cache_it->second.reps.size()
                      << " sha256=" << cache_it->second.sha256 << "\n";
        }
        std::cerr << "JOB_START id=" << job.id
                  << " profile=" << vec_key(job.oriented) << "\n";
        const auto result =
            solve_job(options.n, options.target, job, cache_it->second,
                      options.max_reps);
        const auto record =
            job_record_json(options.n, options.target, job, params, result);
        if (result.complete) {
            atomic_job_log(options.log_dir, job.id, record);
            records << record << '\n';
            records.flush();
            if (!records) fail("failed appending completed job record");
        }
        std::cerr << "JOB_" << (result.complete ? "DONE" : "PARTIAL")
                  << " id=" << job.id
                  << " verdict=" << (result.sat ? "SAT" : "UNSAT")
                  << " orbits=" << result.pair_orbits
                  << " a_space=" << decimal(result.stats.a_space)
                  << " a_checked=" << decimal(result.stats.a_checked)
                  << " survivors=" << decimal(result.stats.a_survivors)
                  << " seconds=" << std::fixed << std::setprecision(3)
                  << result.seconds << "\n";
        ++jobs_run;
        if (result.sat && result.complete) {
            campaign_sat = true;
            break;
        }
    }
    std::cerr << "CAMPAIGN_STOP jobs_run=" << jobs_run
              << " sat=" << campaign_sat
              << " completed_before=" << done.size() << "\n";
}

class Arguments {
  public:
    Arguments(int argc, char** argv) {
        if (argc >= 2) command_ = argv[1];
        for (int i = 2; i < argc; ++i) {
            std::string key = argv[i];
            if (!key.starts_with("--")) fail("unexpected argument " + key);
            if (i + 1 < argc && !std::string(argv[i + 1]).starts_with("--")) {
                values_[key] = argv[++i];
            } else {
                flags_.insert(key);
            }
        }
    }

    const std::string& command() const { return command_; }
    bool flag(const std::string& name) const { return flags_.contains(name); }
    bool has(const std::string& name) const { return values_.contains(name); }

    std::string value(const std::string& name,
                      const std::string& fallback = "") const {
        const auto it = values_.find(name);
        return it == values_.end() ? fallback : it->second;
    }

    int integer(const std::string& name, int fallback = 0) const {
        const auto it = values_.find(name);
        if (it == values_.end()) return fallback;
        return std::stoi(it->second);
    }

  private:
    std::string command_;
    std::map<std::string, std::string> values_;
    std::set<std::string> flags_;
};

void print_usage(std::ostream& out) {
    out << R"(Independent exact toroidal peaceable-queens solver (impl_b)

Usage:
  solver_b self-test
  solver_b profiles --n N --target TAU
  solver_b orbits --n N --r R --c C [--transpose] [--sign]
  solver_b solve --n N --target TAU --records FILE --log-dir DIR
                 [--job ID] [--max-jobs K] [--max-reps K]
                 [--job-modulus M --job-remainder R]
                 [--unsafe-skip-self-test]

The solve command is single-threaded and resumes by skipping complete job IDs
already present in FILE.  --max-reps is a smoke-test facility; an incomplete
UNSAT job is deliberately not recorded.
)";
}

int run_main(int argc, char** argv) {
    const Arguments args(argc, argv);
    if (args.command().empty() || args.command() == "help" ||
        args.flag("--help")) {
        print_usage(std::cout);
        return 0;
    }
    if (args.command() == "self-test") {
        run_self_tests();
        return 0;
    }
    if (args.command() == "profiles") {
        const int n = args.integer("--n");
        const int target = args.integer("--target");
        if (n < 5 || n > 31 || target <= 0) fail("bad profiles parameters");
        const auto profiles = generate_profiles(n, target);
        const auto jobs = make_jobs(n, profiles);
        std::map<int, int> strata;
        for (const auto& p : profiles.canonical) {
            ++strata[std::accumulate(p.begin(), p.end(), 0)];
        }
        std::cout << "{\"n\":" << n << ",\"target\":" << target
                  << ",\"ordered_survivors\":"
                  << profiles.ordered_survivors
                  << ",\"canonical_profiles\":" << profiles.canonical.size()
                  << ",\"oriented_jobs\":" << jobs.size()
                  << ",\"strata\":{";
        bool first = true;
        for (auto [s, count] : strata) {
            if (!first) std::cout << ',';
            first = false;
            std::cout << '"' << s << "\":" << count;
        }
        std::cout << "}}\n";
        return 0;
    }
    if (args.command() == "orbits") {
        const PairGroup group{args.integer("--n"), args.integer("--r"),
                              args.integer("--c"), args.flag("--transpose"),
                              args.flag("--sign")};
        if (group.n < 5 || group.n > 31 || group.r < 0 ||
            group.r > group.n || group.c < 0 || group.c > group.n) {
            fail("bad orbit parameters");
        }
        const auto list = enumerate_pair_reps(group);
        std::cout << "{\"n\":" << group.n << ",\"r\":" << group.r
                  << ",\"c\":" << group.c
                  << ",\"transpose\":"
                  << (group.transpose ? "true" : "false")
                  << ",\"sign\":" << (group.relative_sign ? "true" : "false")
                  << ",\"enumerated\":" << list.reps.size()
                  << ",\"burnside\":\"" << decimal(list.burnside_count)
                  << "\",\"sha256\":\"" << list.sha256 << "\"}\n";
        return 0;
    }
    if (args.command() == "solve") {
        SolveOptions options;
        options.n = args.integer("--n");
        options.target = args.integer("--target");
        if (options.n < 5 || options.n > 31 || options.target <= 0) {
            fail("bad solve parameters");
        }
        options.records = args.value(
            "--records", "records-n" + std::to_string(options.n) + "-t" +
                             std::to_string(options.target) + ".jsonl");
        options.log_dir =
            args.value("--log-dir", "job-logs-n" + std::to_string(options.n) +
                                        "-t" +
                                        std::to_string(options.target));
        if (args.has("--job")) options.only_job = args.integer("--job");
        if (args.has("--max-jobs"))
            options.max_jobs = args.integer("--max-jobs");
        if (args.has("--max-reps"))
            options.max_reps =
                static_cast<std::size_t>(args.integer("--max-reps"));
        if (args.has("--job-modulus") || args.has("--job-remainder")) {
            if (!args.has("--job-modulus") || !args.has("--job-remainder")) {
                fail("--job-modulus and --job-remainder must be used together");
            }
            options.job_modulus = args.integer("--job-modulus");
            options.job_remainder = args.integer("--job-remainder");
            if (*options.job_modulus < 1 || *options.job_modulus > 5 ||
                *options.job_remainder < 0 ||
                *options.job_remainder >= *options.job_modulus) {
                fail("bad disjoint-worker modulus/remainder");
            }
        }
        if (!args.flag("--unsafe-skip-self-test")) run_self_tests();
        run_campaign(options);
        return 0;
    }
    fail("unknown command " + args.command());
}

}  // namespace pqb

int main(int argc, char** argv) {
    try {
        return pqb::run_main(argc, argv);
    } catch (const std::exception& error) {
        std::cerr << "ERROR: " << error.what() << '\n';
        return 2;
    }
}
