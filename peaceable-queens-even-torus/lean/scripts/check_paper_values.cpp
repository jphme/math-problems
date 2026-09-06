// Reproduce paper Table tab:Hvals and Remark rem:plaid16 using integers only.
// This optional computation check is independent of the Lean formal proof.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>

using Int = std::int64_t;

Int black(Int r0, Int r1, Int c0, Int c1) {
    return r0 * c1 + r1 * c0;
}

Int white(Int q, Int r0, Int r1, Int c0, Int c1) {
    return (q - r0) * (q - c0) + (q - r1) * (q - c1);
}

Int profile(Int q, Int r0, Int r1, Int c0, Int c1) {
    return std::min(black(r0, r1, c0, c1), white(q, r0, r1, c0, c1));
}

Int h_brute(Int q) {
    Int best = 0;
    for (Int r0 = 0; r0 <= q; ++r0)
        for (Int r1 = 0; r1 <= q; ++r1)
            for (Int c0 = 0; c0 <= q; ++c0)
                for (Int c1 = 0; c1 <= q; ++c1)
                    best = std::max(best, profile(q, r0, r1, c0, c1));
    return best;
}

Int h_affine(Int q) {
    Int best = 0;
    for (Int r0 = 0; r0 <= q; ++r0) {
        for (Int r1 = 0; r1 <= q; ++r1) {
            for (Int c0 = 0; c0 <= q; ++c0) {
                // With r0, r1, c0 fixed, black increases and white decreases
                // as c1 increases. Their minimum is maximized at an endpoint
                // or at one of the two integers bracketing their intersection.
                const Int denominator = q + r0 - r1;
                const Int numerator = 2 * q * q - q * (r0 + r1)
                                      - (q - r0 + r1) * c0;
                Int lo = 0;
                if (denominator != 0) {
                    if (numerator >= denominator * q) lo = q;
                    else if (numerator > 0) lo = numerator / denominator;
                }
                // If denominator is zero then r0=0 and r1=q: both
                // capacities are independent of c1, so c1=0 suffices.
                best = std::max(best, profile(q, r0, r1, c0, lo));
                best = std::max(best, profile(q, r0, r1, c0, std::min(q, lo + 1)));
            }
        }
    }
    return best;
}

Int plaid(Int q) {
    Int best = 0;
    for (Int u = 0; u <= q; ++u)
        for (Int v = 0; v <= q; ++v)
            best = std::max(best, std::min(q * (u + v), (q - u) * (q - v)));
    return best;
}

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}

int main() {
    // All inputs are in 0..200; intermediate arithmetic is far below 2^63.
    const std::array<Int, 20> table = {
        0, 2, 4, 8, 12, 18, 25, 32, 42, 51,
        64, 74, 90, 101, 120, 133, 153, 170, 190, 210
    };
    for (Int q = 0; q <= 12; ++q)
        require(h_affine(q) == h_brute(q), "affine optimizer disagrees with four-loop enumeration");
    std::array<Int, 3> histogram{};
    std::array<Int, 3> first_order{};
    for (Int q = 1; q <= 200; ++q) {
        const Int h = h_affine(q);
        const Int p = plaid(q);
        if (q <= 20) require(h == table[static_cast<std::size_t>(q - 1)], "H table mismatch");
        const Int difference = h - p;
        require(0 <= difference && difference <= 2, "plaid difference outside {0,1,2}");
        const auto index = static_cast<std::size_t>(difference);
        ++histogram[index];
        if (first_order[index] == 0) first_order[index] = 2 * q;
    }
    require(histogram == std::array<Int, 3>{146, 33, 21}, "plaid histogram mismatch");
    require(first_order[1] == 20 && first_order[2] == 24, "first exceptional orders mismatch");
    require(plaid(10) == 50 && plaid(12) == 72, "displayed plaid values mismatch");
    require(profile(10, 7, 2, 1, 7) == 51, "H(20) witness mismatch");
    require(profile(12, 8, 2, 1, 9) == 74, "H(24) witness mismatch");
    require(black(0, 6, 6, 0) == 36 && white(8, 0, 6, 6, 0) == 32,
            "16-torus homogeneous-cell witness mismatch");
    std::cout << "PAPER_VALUE_CHECKS_OK table=20 histogram=146,33,21 orders=200 "
                 "first_exceptions=20,24 brute_crosscheck=0..12\n";
}
