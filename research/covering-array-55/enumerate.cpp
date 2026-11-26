#include "cube.hpp"

// Regenerates every row-deletion-minimal binary CA(m;4,9,2), m <= 27,
// up to row order, column order, and independent column complementation.
using namespace cube;
using Bits = std::uint32_t;
using Word = std::uint64_t;

struct Quota {
    Bits support;
    int lower, upper; // inclusive bounds on the number assigned the new bit 1
};

std::vector<Rows> seeds(int n) {
    constexpr int minimum[] = {0, 6, 2, 1}; // necessary for CA(n;3,8,2)
    std::vector<Rows> old{Rows(n, 0)};
    for (int depth = 0; depth < 8; ++depth) {
        Classes next(depth + 1);
        for (const auto &rows : old) {
            std::vector<Quota> quotas;
            for (int mask = 0; mask < (1 << depth); ++mask) {
                const int order = pop(mask) + 1;
                if (order > 3) continue;
                for (int p = mask; ; p = (p - 1) & mask) {
                    Bits support = 0;
                    for (int i = 0; i < n; ++i)
                        if ((rows[i] & mask) == p) support |= 1u << i;
                    quotas.push_back({support, minimum[order],
                                      pop(support) - minimum[order]});
                    if (p == 0) break;
                }
            }
            Bits equal = 0;
            for (int i = 1; i < n; ++i)
                if (rows[i] == rows[i - 1]) equal |= 1u << i;
            for (Bits column = 0; column < (1u << n); ++column) {
                // Permute identical prefix rows and choose the lighter new bit.
                if ((equal & (column << 1) & ~column) || pop(column) > n / 2) continue;
                bool valid = true;
                for (const auto &q : quotas) {
                    const int count = pop(column & q.support);
                    if (count < q.lower || count > q.upper) { valid = false; break; }
                }
                if (valid) {
                    Rows extended = rows;
                    for (int i = 0; i < n; ++i) extended[i] |= ((column >> i) & 1) << depth;
                    next.index(std::move(extended));
                }
            }
        }
        old = std::move(next.representatives);
    }
    // A seed lives inside a deletion-minimal array. Duplicate full rows cannot occur.
    old.erase(std::remove_if(old.begin(), old.end(), [](const Rows &r) {
        return std::adjacent_find(r.begin(), r.end()) != r.end();
    }), old.end());
    return old;
}

// For each difference of two rows, record the four-coordinate sets on which
// the two rows differ. A private four-coordinate restriction singles out a row.
struct PrivatePatterns {
    std::array<std::array<Word, 2>, 512> distinguish{};
    PrivatePatterns() {
        int index = 0;
        for (int mask = 0; mask < 512; ++mask) if (pop(mask) == 4) {
            for (int delta = 0; delta < 512; ++delta)
                if (mask & delta) distinguish[delta][index / 64] |= Word(1) << (index % 64);
            ++index;
        }
        require(index == 126, "wrong number of four-coordinate sets");
    }
    bool minimal(const Rows &rows) const {
        for (std::size_t i = 0; i < rows.size(); ++i) {
            Word low = ~Word(0), high = ~Word(0);
            for (std::size_t j = 0; j < rows.size(); ++j) if (j != i) {
                const auto &mask = distinguish[rows[i] ^ rows[j]];
                low &= mask[0];
                high &= mask[1];
                if ((low | high) == 0) return false;
            }
        }
        return true;
    }
};

// Six row bits have 64 possible assignments. A machine word stores an exact
// set of these assignments. The remaining row bits are enumerated explicitly.
struct SixRows {
    Word allowed[64][8][8]{};
    Word ordered[64][2]{};
    SixRows() {
        for (int mask = 0; mask < 64; ++mask) for (int w = 0; w < 64; ++w) {
            int count = pop(mask & w);
            for (int lo = 0; lo <= count; ++lo)
                for (int end = count + 1; end <= 7; ++end)
                    allowed[mask][lo][end] |= Word(1) << w;
            for (int previous = 0; previous < 2; ++previous)
                if (!(mask & ((w << 1) | previous) & ~w))
                    ordered[mask][previous] |= Word(1) << w;
        }
    }
};

struct Requirement { int pattern, ones, zeros; };
struct Rule {
    int low_rows, tightness;
    std::array<Word, 10> allowed{};
};

class Completions {
    const Rows &seed;
    const SixRows &six;
    const PrivatePatterns &private_patterns;
    Classes &classes;
    const int n, low_count;
    std::array<std::vector<Requirement>, 8> requirements;
    std::array<int, 9> power{};
    std::array<Bits, 2187> supports{}; // every ternary pattern on the first 7 columns
    std::array<Bits, 8> columns{};

    void finish() {
        Rows rows;
        for (int i = 0; i < n; ++i) {
            int value = 0;
            for (int j = 0; j < 8; ++j) value |= ((columns[j] >> i) & 1) << j;
            rows.push_back(value);
        }
        for (int r : seed) rows.push_back(256 | r);
        if (private_patterns.minimal(rows)) classes.index(std::move(rows));
    }

    void extend(int d) {
        std::vector<Rule> rules;
        for (const auto &q : requirements[d]) {
            Bits support = supports[q.pattern];
            int length = pop(support), lower = q.ones, upper = length - q.zeros;
            if (lower > upper) return;
            Rule rule{};
            rule.low_rows = support & ((1 << low_count) - 1);
            // Prioritize the smallest and most constrained supports. This order
            // affects elapsed time only.
            rule.tightness = 16 * (upper - lower) + length;
            for (int c = 0; c <= low_count; ++c) {
                int lo = std::clamp(lower - c, 0, 7);
                int end = std::clamp(upper - c + 1, 0, 7);
                rule.allowed[c] = six.allowed[support >> low_count][lo][end];
            }
            rules.push_back(rule);
        }
        std::sort(rules.begin(), rules.end(), [](const Rule &a, const Rule &b) {
            return a.tightness < b.tightness;
        });
        // Any permutation of rows still identical in all earlier columns is free.
        Bits equal = ((1u << n) - 1) ^ 1u;
        for (int j = 0; j < d; ++j) equal &= ~(columns[j] ^ (columns[j] << 1));
        const int limit = 1 << low_count;
        for (int low = 0; low < limit; ++low) {
            if (low & ((~low & equal & (limit - 1)) >> 1)) continue;
            Word high = six.ordered[equal >> low_count][low >> (low_count - 1)];
            for (const Rule &rule : rules) {
                high &= rule.allowed[pop(low & rule.low_rows)];
                if (!high) break;
            }
            while (high) {
                Bits w = low | (static_cast<Bits>(__builtin_ctzll(high)) << low_count);
                high &= high - 1;
                columns[d] = w;
                if (d == 7) { finish(); continue; }
                for (int p = 0; p < power[d]; ++p) {
                    supports[p + power[d]] = supports[p] & ~w;
                    supports[p + 2 * power[d]] = supports[p] & w;
                }
                extend(d + 1);
            }
        }
    }
public:
    Completions(const Rows &seed, int n, const SixRows &six, const PrivatePatterns &patterns,
                Classes &classes)
        : seed(seed), six(six), private_patterns(patterns), classes(classes), n(n), low_count(n - 6) {
        power[0] = 1;
        for (int d = 0; d < 8; ++d) power[d + 1] = 3 * power[d];
        const int minimum_full[] = {0, static_cast<int>(seed.size()), 6, 2, 1};
        constexpr int minimum_half[] = {0, 6, 2, 1, 0};
        for (int d = 0; d < 8; ++d) for (int p = 0; p < power[d]; ++p) {
            int mask = 0, value = 0;
            for (int j = 0, digits = p; j < d; ++j, digits /= 3) {
                if (digits % 3) mask |= 1 << j;
                if (digits % 3 == 2) value |= 1 << j;
            }
            const int order = pop(mask) + 1;
            if (order > 4) continue;
            int supplied[2]{};
            for (int row : seed) if ((row & mask) == value) ++supplied[(row >> d) & 1];
            const int ones = std::max(minimum_half[order], minimum_full[order] - supplied[1]);
            const int zeros = std::max(minimum_half[order], minimum_full[order] - supplied[0]);
            if (ones || zeros) requirements[d].push_back({p, ones, zeros});
        }
    }
    void run() { supports[0] = (1u << n) - 1; extend(0); }
};

int main() {
    SixRows six;
    PrivatePatterns patterns;
    Classes small(9);
    for (int q : {12, 13}) {
        auto list = seeds(q);
        std::cerr << q << "-row simple strength-three seeds: " << list.size() << '\n';
        for (int m = 2 * q; m <= 27; ++m) {
            std::size_t before = small.representatives.size();
            for (const Rows &seed : list) Completions(seed, m - q, six, patterns, small).run();
            std::cerr << "m=" << m << ", q=" << q << ", new types="
                      << small.representatives.size() - before << '\n';
        }
    }
    auto &types = small.representatives;
    std::sort(types.begin(), types.end(), [](const Rows &a, const Rows &b) {
        return a.size() != b.size() ? a.size() < b.size() : a < b;
    });
    for (const Rows &type : types) {
        for (std::size_t i = 0; i < type.size(); ++i) std::cout << (i ? " " : "") << type[i];
        std::cout << '\n';
    }
}
