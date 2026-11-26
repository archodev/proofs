#ifndef COVERING_ARRAY_CUBE_HPP
#define COVERING_ARRAY_CUBE_HPP

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <stdexcept>
#include <utility>
#include <vector>

namespace cube {
using Rows = std::vector<int>;
using Map = std::array<int, 9>;
inline int pop(unsigned x) { return __builtin_popcount(x); }

// A mode 2*j+f maps source coordinate j, complemented by f, to the target.
inline int image(int row, const Map &modes, int width) {
    int result = 0;
    for (int i = 0; i < width; ++i) {
        const int mode = modes[i];
        result |= (((row >> (mode / 2)) ^ mode) & 1) << i;
    }
    return result;
}

// Enumerate signed coordinate permutations carrying one row multiset to another.
// A callback returning true requests the first match only. Every rejected prefix
// already has a different multiset on the assigned target coordinates.
template<class Visit>
bool isometries(const Rows &source, const Rows &target, int width, Visit visit) {
    if (source.size() != target.size()) return false;
    std::array<std::array<int, 512>, 10> target_counts{};
    for (int d = 1; d <= width; ++d) {
        for (int x : target) ++target_counts[d][x & ((1 << d) - 1)];
    }
    std::array<Rows, 10> partial;
    for (int d = 0; d <= width; ++d) partial[d].resize(source.size());
    Map modes{};
    auto search = [&](auto &&self, int depth, int used) -> bool {
        if (depth == width) return visit(modes);
        const int span = 2 << depth;
        for (int j = 0; j < width; ++j) {
            if ((used >> j) & 1) continue;
            for (int flip = 0; flip < 2; ++flip) {
                std::array<int, 512> counts;
                std::fill_n(counts.begin(), span, 0);
                for (std::size_t r = 0; r < source.size(); ++r) {
                    const int bit = ((source[r] >> j) ^ flip) & 1;
                    const int prefix = partial[depth][r] | (bit << depth);
                    partial[depth + 1][r] = prefix;
                    ++counts[prefix];
                }
                if (!std::equal(counts.begin(), counts.begin() + span,
                                target_counts[depth + 1].begin())) continue;
                modes[depth] = 2 * j + flip;
                if (self(self, depth + 1, used | (1 << j))) return true;
            }
        }
        return false;
    };
    return search(search, 0, 0);
}

// Distance profiles are a lookup accelerator. A candidate is discarded only
// after isometries() actually finds a signed coordinate permutation.
class Classes {
    int width;
    std::map<Rows, std::vector<int>> buckets;
public:
    std::vector<Rows> representatives;
    explicit Classes(int width) : width(width) {}

    int index(Rows rows) {
        std::sort(rows.begin(), rows.end());
        Rows signature;
        std::vector<std::array<int, 10>> profiles;
        for (int x : rows) {
            std::array<int, 10> histogram{};
            for (int y : rows) ++histogram[pop(x ^ y)];
            profiles.push_back(histogram);
        }
        std::sort(profiles.begin(), profiles.end());
        for (const auto &p : profiles) {
            signature.insert(signature.end(), p.begin(), p.begin() + width + 1);
        }
        auto &candidates = buckets[signature];
        for (int id : candidates) {
            if (rows == representatives[id] ||
                isometries(rows, representatives[id], width, [](const Map &) { return true; }))
                return id;
        }
        const int id = static_cast<int>(representatives.size());
        candidates.push_back(id);
        representatives.push_back(std::move(rows));
        return id;
    }
};

inline void require(bool condition, const char *message) {
    if (!condition) throw std::runtime_error(message);
}
} // namespace cube
#endif
