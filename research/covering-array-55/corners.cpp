#include "cube.hpp"
#include <set>
#include <sstream>
#include <string>

using namespace cube;
using PointSet = std::array<std::uint64_t, 2>;

bool minimal_cover(const Rows &rows) {
    std::set<int> essential;
    for (int mask = 0; mask < 512; ++mask) if (pop(mask) == 4) {
        std::map<int, Rows> groups;
        for (int r : rows) groups[r & mask].push_back(r);
        if (groups.size() != 16) return false;
        for (const auto &entry : groups)
            if (entry.second.size() == 1) essential.insert(entry.second.front());
    }
    return essential.size() == rows.size();
}

struct Graph {
    std::map<PointSet, int> labels;
    std::vector<std::set<int>> neighbors;

    int vertex(const PointSet &points) {
        auto result = labels.emplace(points, static_cast<int>(labels.size()));
        if (result.second) neighbors.emplace_back();
        return result.first->second;
    }
    void edge(const PointSet &a, const PointSet &b) {
        int x = vertex(a), y = vertex(b);
        neighbors[x].insert(y);
        neighbors[y].insert(x);
    }
};

struct Alignment {
    int graph_id;
    std::vector<Map> maps;
};

class Corners {
    Classes common{7};
    std::map<Rows, Alignment> cache;
    std::vector<Graph> graphs;

    const Alignment &align(const Rows &corner) {
        auto it = cache.find(corner);
        if (it != cache.end()) return it->second;
        int id = common.index(corner);
        if (static_cast<int>(graphs.size()) <= id) graphs.resize(id + 1);
        Alignment a{id, {}};
        isometries(corner, common.representatives[id], 7, [&](const Map &map) {
            a.maps.push_back(map);
            return false; // enumerate every alignment, including stabilizers
        });
        require(!a.maps.empty(), "no isometry to representative");
        return cache.emplace(corner, std::move(a)).first->second;
    }

    static PointSet transform(const Rows &rows, const Map &map) {
        PointSet result{};
        for (int r : rows) {
            int x = image(r, map, 7);
            result[x / 64] |= std::uint64_t(1) << (x % 64);
        }
        return result;
    }
public:
    void append(const Rows &slice) {
        for (int first = 0; first < 9; ++first) for (int second = first + 1; second < 9; ++second) {
            std::array<Rows, 4> cells;
            for (int row : slice) {
                int position = 0, free_bits = 0;
                for (int j = 0; j < 9; ++j) if (j != first && j != second)
                    free_bits |= ((row >> j) & 1) << position++;
                int cell = ((row >> first) & 1) | (((row >> second) & 1) << 1);
                cells[cell].push_back(free_bits);
            }
            for (Rows &cell : cells) std::sort(cell.begin(), cell.end());
            for (int center = 0; center < 4; ++center) {
                const auto &a = align(cells[center]);
                for (const auto &map : a.maps)
                    graphs[a.graph_id].edge(transform(cells[center ^ 1], map),
                                            transform(cells[center ^ 2], map));
            }
        }
    }

    bool report() const {
        // Each row records the number of graphs, vertices, edges, loops and
        // triangles, plus the number of nonbipartite graphs for this corner size.
        std::map<int, std::array<std::uint64_t, 6>> summary;
        bool obstruction = true;
        for (std::size_t i = 0; i < graphs.size(); ++i) {
            auto &s = summary[common.representatives[i].size()];
            const auto &neighbors = graphs[i].neighbors;
            std::vector<int> color(neighbors.size(), -1);
            bool bipartite = true;
            for (int start = 0; start < static_cast<int>(neighbors.size()); ++start) {
                if (color[start] != -1) continue;
                std::vector<int> queue{start};
                color[start] = 0;
                for (std::size_t pos = 0; pos < queue.size(); ++pos) {
                    int x = queue[pos];
                    for (int y : neighbors[x]) {
                        if (color[y] == -1) {
                            color[y] = 1 - color[x];
                            queue.push_back(y);
                        } else if (color[y] == color[x]) {
                            bipartite = false;
                        }
                    }
                }
            }
            if (!bipartite) ++s[5];
            ++s[0];
            s[1] += neighbors.size();
            for (int x = 0; x < static_cast<int>(neighbors.size()); ++x) {
                for (int y : neighbors[x]) if (y >= x) {
                    ++s[2];
                    if (y == x) { ++s[3]; obstruction = false; }
                    for (int z : neighbors[x]) {
                        if (x < y && y < z && neighbors[y].count(z)) {
                            ++s[4];
                            obstruction = false;
                        }
                    }
                }
            }
        }
        std::cout << "|O| graphs vertices edges loops triangles nonbipartite\n";
        for (const auto &entry : summary) {
            std::cout << entry.first;
            for (auto count : entry.second) std::cout << ' ' << count;
            std::cout << '\n';
        }
        return obstruction;
    }
};

int main(int argc, char **argv) {
    bool positive = argc == 2 && std::string(argv[1]) == "--positive";
    require(argc == 1 || positive, "usage: corners [--positive] < types");
    std::map<int, int> sizes;
    Corners corners;
    std::string line;
    while (std::getline(std::cin, line)) {
        std::istringstream input(line);
        Rows rows;
        int value;
        while (input >> value) {
            require(0 <= value && value < 512, "invalid 9-bit row");
            rows.push_back(value);
        }
        require(input.eof(), "unexpected input");
        require(!rows.empty() && minimal_cover(rows), "invalid or deletable slice");
        ++sizes[rows.size()];
        corners.append(rows);
    }
    std::cout << "Slice sizes and counts\n";
    for (auto entry : sizes) std::cout << entry.first << ' ' << entry.second << '\n';
    if (!positive)
        require(sizes == std::map<int,int>{{24,1},{26,1},{27,91}}, "unexpected type counts");
    bool excluded = corners.report();
    require(positive ? !excluded : excluded, "unexpected corner graph result");
    std::cout << (positive ? "Positive control admits a closed three-step walk.\n"
                           : "All corner graphs are loopless and triangle-free.\n");
}
