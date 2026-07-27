// Independent exact C++ accelerator for envelope_checker.py's box proof.
//
// Input is a deliberately tiny integer-only interchange format produced by
// run_cpp_ladder.py.  No JSON or reference-verifier code is imported.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <queue>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace {

using I64 = std::int64_t;
using U64 = std::uint64_t;
using Point = std::array<int, 8>;

struct Term {
  int left;
  int right;
  I64 coefficient;
};

struct Cut {
  I64 constant = 0;
  std::array<I64, 8> linear{};
  std::vector<Term> quadratic;
  std::vector<int> variables;
};

struct Box {
  Point lo{};
  Point hi{};
  int depth = 0;
  int hint = 0;
};

struct Stats {
  U64 nodes = 0;
  U64 propagation_infeasible = 0;
  U64 certified_boxes = 0;
  U64 interval_certified_boxes = 0;
  U64 corner_certified_boxes = 0;
  U64 point_boxes = 0;
  U64 fallback_full_library_points = 0;
  U64 fallback_cut_point_evaluations = 0;
  U64 survivor_count = 0;
  U64 cut_center_evaluations = 0;
  U64 cut_interval_evaluations = 0;
  U64 cut_corner_calls = 0;
  U64 corners_inspected = 0;
  U64 max_depth = 0;
  U64 max_stack = 1;
};

struct QueryResult {
  std::string verdict;
  I64 threshold = 0;
  double runtime_seconds = 0.0;
  Stats stats;
  std::vector<Point> survivors;
  std::map<int, U64> cut_wins;
  U64 unfinished_stack_boxes = 0;
};

constexpr std::array<std::array<int, 8>, 5> kDomainRows{{
    {{1, -1, 0, 0, 0, 0, 0, 0}},
    {{0, 0, 1, -1, 0, 0, 0, 0}},
    {{1, 1, -1, -1, 0, 0, 0, 0}},
    {{0, 0, 0, 0, 1, 1, -1, -1}},
    {{1, 1, 1, 1, 1, 1, 1, 1}},
}};

I64 evaluate(const Cut& cut, int q, const Point& point) {
  I64 value = cut.constant * q * q;
  for (int index = 0; index < 8; ++index) {
    value += cut.linear[index] * q * point[index];
  }
  for (const Term& term : cut.quadratic) {
    value += term.coefficient * point[term.left] * point[term.right];
  }
  return value;
}

I64 interval_upper(const Cut& cut, int q, const Point& lo,
                   const Point& hi) {
  I64 value = cut.constant * q * q;
  for (int index = 0; index < 8; ++index) {
    const I64 coefficient = cut.linear[index];
    const int endpoint = coefficient > 0 ? hi[index] : lo[index];
    value += coefficient * q * endpoint;
  }
  for (const Term& term : cut.quadratic) {
    const I64 product =
        term.coefficient > 0
            ? static_cast<I64>(hi[term.left]) * hi[term.right]
            : static_cast<I64>(lo[term.left]) * lo[term.right];
    value += term.coefficient * product;
  }
  return value;
}

std::pair<bool, U64> exact_corner_leq(const Cut& cut, int q,
                                      const Point& lo, const Point& hi,
                                      I64 threshold) {
  std::vector<int> active;
  for (int variable : cut.variables) {
    if (lo[variable] != hi[variable]) {
      active.push_back(variable);
    }
  }
  I64 value = evaluate(cut, q, lo);
  if (value > threshold) {
    return {false, 1};
  }
  if (active.empty()) {
    return {true, 1};
  }
  const int count = static_cast<int>(active.size());
  std::array<int, 8> position{};
  position.fill(-1);
  for (int local = 0; local < count; ++local) {
    position[active[local]] = local;
  }
  std::array<I64, 8> first_order{};
  std::array<std::array<I64, 8>, 8> interactions{};
  for (int local = 0; local < count; ++local) {
    const int variable = active[local];
    I64 derivative = cut.linear[variable] * q;
    for (const Term& term : cut.quadratic) {
      if (term.left == variable) {
        derivative += term.coefficient * lo[term.right];
      } else if (term.right == variable) {
        derivative += term.coefficient * lo[term.left];
      }
    }
    first_order[local] =
        static_cast<I64>(hi[variable] - lo[variable]) * derivative;
  }
  for (const Term& term : cut.quadratic) {
    const int first = position[term.left];
    const int second = position[term.right];
    if (first < 0 || second < 0) {
      continue;
    }
    const I64 interaction =
        term.coefficient * static_cast<I64>(hi[term.left] - lo[term.left]) *
        (hi[term.right] - lo[term.right]);
    interactions[first][second] = interaction;
    interactions[second][first] = interaction;
  }
  std::array<bool, 8> selected{};
  unsigned previous_gray = 0;
  U64 inspected = 1;
  const unsigned corner_count = 1U << count;
  for (unsigned ordinal = 1; ordinal < corner_count; ++ordinal) {
    const unsigned gray = ordinal ^ (ordinal >> 1U);
    const unsigned changed = gray ^ previous_gray;
    const int local = __builtin_ctz(changed);
    I64 adjustment = first_order[local];
    for (int other = 0; other < count; ++other) {
      if (other != local && selected[other]) {
        adjustment += interactions[local][other];
      }
    }
    if (selected[local]) {
      value -= adjustment;
      selected[local] = false;
    } else {
      value += adjustment;
      selected[local] = true;
    }
    ++inspected;
    if (value > threshold) {
      return {false, inspected};
    }
    previous_gray = gray;
  }
  return {true, inspected};
}

bool propagate_box(int q, Point& lo, Point& hi) {
  bool changed = true;
  while (changed) {
    changed = false;
    for (int row = 0; row < 5; ++row) {
      const int rhs = row == 4 ? 4 * q : 0;
      I64 minimum = 0;
      for (int index = 0; index < 8; ++index) {
        const int coefficient = kDomainRows[row][index];
        if (coefficient > 0) {
          minimum += static_cast<I64>(coefficient) * lo[index];
        } else if (coefficient < 0) {
          minimum += static_cast<I64>(coefficient) * hi[index];
        }
      }
      if (minimum > rhs) {
        return false;
      }
      for (int index = 0; index < 8; ++index) {
        const int coefficient = kDomainRows[row][index];
        if (coefficient == 0) {
          continue;
        }
        const int used = coefficient > 0 ? lo[index] : hi[index];
        const I64 other_minimum =
            minimum - static_cast<I64>(coefficient) * used;
        if (coefficient == 1) {
          const I64 candidate = rhs - other_minimum;
          if (candidate < hi[index]) {
            hi[index] = static_cast<int>(candidate);
            changed = true;
          }
        } else if (coefficient == -1) {
          const I64 candidate = other_minimum - rhs;
          if (candidate > lo[index]) {
            lo[index] = static_cast<int>(candidate);
            changed = true;
          }
        } else {
          throw std::logic_error("unexpected domain coefficient");
        }
        if (lo[index] > hi[index]) {
          return false;
        }
      }
    }
  }
  return true;
}

bool in_domain(int q, const Point& point) {
  I64 total = 0;
  for (int value : point) {
    if (value < 0 || value > q) {
      return false;
    }
    total += value;
  }
  return point[0] <= point[1] && point[2] <= point[3] &&
         point[0] + point[1] <= point[2] + point[3] &&
         point[4] + point[5] <= point[6] + point[7] && total <= 4 * q;
}

I64 split_score(const Cut& cut, int q, const Point& lo, const Point& hi,
                int index) {
  if (lo[index] == hi[index]) {
    return -1;
  }
  I64 derivative_low = cut.linear[index] * q;
  I64 derivative_high = derivative_low;
  for (const Term& term : cut.quadratic) {
    int other = -1;
    if (term.left == index) {
      other = term.right;
    } else if (term.right == index) {
      other = term.left;
    }
    if (other < 0) {
      continue;
    }
    const I64 first = term.coefficient * lo[other];
    const I64 second = term.coefficient * hi[other];
    derivative_low += std::min(first, second);
    derivative_high += std::max(first, second);
  }
  const I64 sensitivity =
      std::max<I64>({std::llabs(derivative_low),
                     std::llabs(derivative_high), 1});
  return static_cast<I64>(hi[index] - lo[index]) * sensitivity;
}

int choose_split(const Cut& cut, int q, const Point& lo, const Point& hi) {
  int best = -1;
  std::tuple<I64, int, int> best_key{-1, -1, -8};
  for (int index = 0; index < 8; ++index) {
    if (lo[index] == hi[index]) {
      continue;
    }
    const auto key =
        std::make_tuple(split_score(cut, q, lo, hi, index),
                        hi[index] - lo[index], -index);
    if (best < 0 || key > best_key) {
      best = index;
      best_key = key;
    }
  }
  return best;
}

std::string cut_label(int index) {
  if (index < 76) {
    return "benders76:" + std::to_string(index);
  }
  return "new684:" + std::to_string(index - 76);
}

QueryResult certify(int q, I64 h_value, I64 scale,
                    const std::vector<Cut>& cuts, int active_cut_count,
                    int corner_candidates, double timeout_seconds) {
  if (scale % 2 != 0) {
    throw std::runtime_error("arithmetic scale must be even");
  }
  QueryResult result;
  result.threshold = scale * h_value + scale / 2;
  Point initial_lo{};
  Point initial_hi{};
  initial_hi.fill(q);
  if (!propagate_box(q, initial_lo, initial_hi)) {
    throw std::logic_error("empty initial domain");
  }
  std::vector<Box> stack;
  stack.push_back({initial_lo, initial_hi, 0, 0});
  const auto started = std::chrono::steady_clock::now();
  bool timed_out = false;

  using Candidate = std::tuple<I64, I64, int>;
  while (!stack.empty()) {
    result.stats.max_stack =
        std::max<U64>(result.stats.max_stack, stack.size());
    Box box = stack.back();
    stack.pop_back();
    ++result.stats.nodes;
    result.stats.max_depth =
        std::max<U64>(result.stats.max_depth, box.depth);
    if (result.stats.nodes % 1024 == 0) {
      const double elapsed =
          std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                        started)
              .count();
      if (elapsed > timeout_seconds) {
        timed_out = true;
        break;
      }
    }

    Point lo = box.lo;
    Point hi = box.hi;
    if (!propagate_box(q, lo, hi)) {
      ++result.stats.propagation_infeasible;
      continue;
    }
    if (lo == hi) {
      ++result.stats.point_boxes;
      if (!in_domain(q, lo)) {
        throw std::logic_error("propagated point outside domain");
      }
      int covering = -1;
      for (int index = 0; index < active_cut_count; ++index) {
        ++result.stats.cut_center_evaluations;
        if (evaluate(cuts[index], q, lo) <= result.threshold) {
          covering = index;
          break;
        }
      }
      if (covering < 0) {
        for (int index = active_cut_count;
             index < static_cast<int>(cuts.size()); ++index) {
          ++result.stats.fallback_cut_point_evaluations;
          if (evaluate(cuts[index], q, lo) <= result.threshold) {
            covering = index;
            ++result.stats.fallback_full_library_points;
            break;
          }
        }
      }
      if (covering < 0) {
        ++result.stats.survivor_count;
        result.survivors.push_back(lo);
        break;
      }
      ++result.cut_wins[covering];
      ++result.stats.certified_boxes;
      continue;
    }

    Point center{};
    for (int index = 0; index < 8; ++index) {
      center[index] = (lo[index] + hi[index]) / 2;
    }
    std::priority_queue<Candidate, std::vector<Candidate>,
                        std::greater<Candidate>>
        ranked;
    int certified_by = -1;
    bool interval_certified = false;
    for (int ordinal = 0; ordinal < active_cut_count; ++ordinal) {
      const int cut_index =
          ordinal == 0 ? box.hint
                       : (ordinal <= box.hint ? ordinal - 1 : ordinal);
      const Cut& cut = cuts[cut_index];
      const I64 center_value = evaluate(cut, q, center);
      ++result.stats.cut_center_evaluations;
      if (center_value > result.threshold) {
        continue;
      }
      const I64 upper = interval_upper(cut, q, lo, hi);
      ++result.stats.cut_interval_evaluations;
      if (upper <= result.threshold) {
        certified_by = cut_index;
        interval_certified = true;
        break;
      }
      ranked.emplace(upper, center_value, cut_index);
    }

    if (certified_by < 0) {
      const int attempts =
          std::min<int>(corner_candidates, ranked.size());
      for (int attempt = 0; attempt < attempts; ++attempt) {
        const int cut_index = std::get<2>(ranked.top());
        ranked.pop();
        ++result.stats.cut_corner_calls;
        const auto [covered, inspected] = exact_corner_leq(
            cuts[cut_index], q, lo, hi, result.threshold);
        result.stats.corners_inspected += inspected;
        if (covered) {
          certified_by = cut_index;
          break;
        }
      }
    }
    if (certified_by >= 0) {
      ++result.stats.certified_boxes;
      if (interval_certified) {
        ++result.stats.interval_certified_boxes;
      } else {
        ++result.stats.corner_certified_boxes;
      }
      ++result.cut_wins[certified_by];
      continue;
    }

    int hint = -1;
    if (!ranked.empty()) {
      hint = std::get<2>(ranked.top());
    } else {
      I64 best_value = std::numeric_limits<I64>::max();
      for (int index = 0; index < active_cut_count; ++index) {
        const I64 value = evaluate(cuts[index], q, center);
        if (value < best_value) {
          best_value = value;
          hint = index;
        }
      }
      result.stats.cut_center_evaluations += active_cut_count;
    }
    const int split_index = choose_split(cuts[hint], q, lo, hi);
    if (split_index < 0) {
      throw std::logic_error("non-point box has no split dimension");
    }
    const int midpoint = (lo[split_index] + hi[split_index]) / 2;
    Point low_hi = hi;
    low_hi[split_index] = midpoint;
    Point high_lo = lo;
    high_lo[split_index] = midpoint + 1;
    stack.push_back({lo, low_hi, box.depth + 1, hint});
    stack.push_back({high_lo, hi, box.depth + 1, hint});
  }

  result.runtime_seconds =
      std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                    started)
          .count();
  result.unfinished_stack_boxes = stack.size();
  if (timed_out) {
    result.verdict = "timeout";
  } else if (!result.survivors.empty()) {
    result.verdict = "envelope_exceeds_threshold";
  } else {
    result.verdict = "envelope_le_h_plus_half";
  }
  return result;
}

void print_point(const Point& point) {
  std::cout << '[';
  for (int index = 0; index < 8; ++index) {
    if (index) {
      std::cout << ',';
    }
    std::cout << point[index];
  }
  std::cout << ']';
}

void print_result(const QueryResult& result, I64 scale, int active_cut_count,
                  int corner_candidates) {
  const Stats& stats = result.stats;
  std::cout << "{\"verdict\":\"" << result.verdict
            << "\",\"threshold\":{\"expression\":\"H(2q) + 1/2\","
               "\"integer_comparison_scale\":"
            << scale << ",\"integer_threshold\":" << result.threshold
            << "},\"active_cut_count\":" << active_cut_count
            << ",\"corner_candidate_limit\":" << corner_candidates
            << ",\"runtime_seconds\":" << result.runtime_seconds
            << ",\"stats\":{"
            << "\"nodes\":" << stats.nodes
            << ",\"propagation_infeasible\":"
            << stats.propagation_infeasible
            << ",\"certified_boxes\":" << stats.certified_boxes
            << ",\"interval_certified_boxes\":"
            << stats.interval_certified_boxes
            << ",\"corner_certified_boxes\":"
            << stats.corner_certified_boxes
            << ",\"point_boxes\":" << stats.point_boxes
            << ",\"fallback_full_library_points\":"
            << stats.fallback_full_library_points
            << ",\"fallback_cut_point_evaluations\":"
            << stats.fallback_cut_point_evaluations
            << ",\"survivor_count\":" << stats.survivor_count
            << ",\"cut_center_evaluations\":"
            << stats.cut_center_evaluations
            << ",\"cut_interval_evaluations\":"
            << stats.cut_interval_evaluations
            << ",\"cut_corner_calls\":" << stats.cut_corner_calls
            << ",\"corners_inspected\":" << stats.corners_inspected
            << ",\"max_depth\":" << stats.max_depth
            << ",\"max_stack\":" << stats.max_stack << "},\"survivors\":[";
  for (std::size_t index = 0; index < result.survivors.size(); ++index) {
    if (index) {
      std::cout << ',';
    }
    print_point(result.survivors[index]);
  }
  std::cout << "],\"cut_box_wins\":{";
  bool first = true;
  for (const auto& [index, wins] : result.cut_wins) {
    if (!first) {
      std::cout << ',';
    }
    first = false;
    std::cout << '"' << cut_label(index) << "\":" << wins;
  }
  std::cout << "},\"unfinished_stack_boxes\":"
            << result.unfinished_stack_boxes << "}\n";
}

}  // namespace

int main() {
  try {
    I64 scale = 0;
    int cut_count = 0;
    int active_cut_count = 0;
    int corner_candidates = 0;
    int q = 0;
    I64 h_value = 0;
    double timeout_seconds = 0.0;
    if (!(std::cin >> scale >> cut_count >> active_cut_count >>
          corner_candidates >> q >> h_value >> timeout_seconds)) {
      throw std::runtime_error("missing input header");
    }
    if (q < 1 || q > 1000 || cut_count != 760 ||
        active_cut_count < 1 || active_cut_count > cut_count ||
        corner_candidates < 0) {
      throw std::runtime_error("invalid input header");
    }
    std::vector<Cut> cuts(cut_count);
    for (int index = 0; index < cut_count; ++index) {
      Cut& cut = cuts[index];
      int term_count = 0;
      std::cin >> cut.constant;
      for (I64& coefficient : cut.linear) {
        std::cin >> coefficient;
      }
      std::cin >> term_count;
      if (!std::cin || term_count < 0 || term_count > 64) {
        throw std::runtime_error("malformed cut header");
      }
      std::array<bool, 8> used{};
      for (int variable = 0; variable < 8; ++variable) {
        used[variable] = cut.linear[variable] != 0;
      }
      for (int term_index = 0; term_index < term_count; ++term_index) {
        Term term{};
        std::cin >> term.left >> term.right >> term.coefficient;
        if (!std::cin || term.left < 0 || term.left >= 8 ||
            term.right < 0 || term.right >= 8 ||
            term.left == term.right) {
          throw std::runtime_error("malformed quadratic term");
        }
        cut.quadratic.push_back(term);
        used[term.left] = true;
        used[term.right] = true;
      }
      for (int variable = 0; variable < 8; ++variable) {
        if (used[variable]) {
          cut.variables.push_back(variable);
        }
      }
    }
    const QueryResult result =
        certify(q, h_value, scale, cuts, active_cut_count,
                corner_candidates, timeout_seconds);
    print_result(result, scale, active_cut_count, corner_candidates);
    return result.verdict == "envelope_le_h_plus_half" ? 0 : 2;
  } catch (const std::exception& error) {
    std::cerr << "box_engine error: " << error.what() << '\n';
    return 1;
  }
}
