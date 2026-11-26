"""Exhaust the finite cases in README.md. Run with Python 3."""

from collections import Counter
from itertools import combinations, permutations


def has_path(graph, u, v, length, seen=frozenset()):
    """Does a simple u-v path have exactly this many edges?"""
    if length == 1:
        return v in graph[u]
    return any(
        has_path(graph, w, v, length - 1, seen | {u})
        for w in graph[u] if w != v and w not in seen
    )


def extend(graph, a, b):
    """Append a vertex with precisely the two indicated older neighbours."""
    z = len(graph)
    return [ns | {z} if i in (a, b) else ns for i, ns in enumerate(graph)] + [{a, b}]


def small_cones():
    # A cone is stored as (ordered list of parent pairs, terminal).
    result = [((), 0), ((), 1)]

    def visit(graph, parents, used):
        n = len(graph)
        if n >= 3 and all(i in used for i in range(2, n - 1)):
            result.append((parents, n - 1))
        if n == 8:
            return
        for a, b in combinations(range(n), 2):
            if n < 7 or not has_path(graph, a, b, 6):
                visit(extend(graph, a, b), parents + ((a, b),), used | {a, b})

    visit([{1}, {0}], (), set())
    return result


def is_exception(graph):
    """Match the exact neighbourhoods in the eight-vertex graph in Figure 1."""
    if len(graph) != 8:
        return False
    for a, b, c, p, q, r, x, y in permutations(range(8)):
        if (graph[a] == graph[b] == {p, q, r, x, y}
                and graph[c] == {p, q, r}
                and graph[p] == graph[q] == graph[r] == {a, b, c}
                and graph[x] == {a, b, y} and graph[y] == {a, b, x}):
            return True
    return False


def unions(left, right):
    """Identify all compatible common vertices, keeping the two roots fixed."""
    left_parents, left_tip = left
    right_parents, right_tip = right
    graph = [{1}, {0}]
    matches = {}
    for v, (a, b) in enumerate(left_parents, 2):
        graph = extend(graph, a, b)
        matches.setdefault((a, b), []).append(v)

    def embed(k, image, current):
        if k == len(right_parents):
            yield current, left_tip, image[right_tip]
            return
        a, b = sorted(image[i] for i in right_parents[k])
        for v in matches.get((a, b), ()):
            if v not in image:
                yield from embed(k + 1, image + (v,), current)
        if not has_path(current, a, b, 6):
            yield from embed(k + 1, image + (len(current),), extend(current, a, b))

    yield from embed(0, (0, 1), graph)


def main():
    cones = small_cones()
    sizes = Counter(len(parents) + 2 for parents, tip in cones)
    orders = Counter()
    one_edge = Counter()
    exceptional = Counter()
    for left in cones:
        for right in cones:
            for graph, u, v in unions(left, right):
                if u == v:
                    continue
                n = len(graph)
                if not has_path(graph, u, v, 6):
                    orders[n + 1] += 1
                    if n + 1 > 8:
                        raise AssertionError(("Large cone", graph, u, v))
                if n >= 8 and v not in graph[u] and not has_path(graph, u, v, 7):
                    augmented = list(graph)
                    augmented[u] = graph[u] | {v}
                    augmented[v] = graph[v] | {u}
                    if min(map(len, augmented)) >= 3:
                        one_edge[n] += 1
                        if not is_exception(augmented):
                            raise AssertionError(("Unexpected graph", augmented))
                        exceptional[n] += 1

    print("Input cones by order:", sorted(sizes.items()))
    print("New-terminal cases by order:", sorted(orders.items()))
    print("Extra-edge cases of minimum degree >= 3, order >= 8:", sorted(one_edge.items()))
    print("Cases isomorphic to Figure 1:", sorted(exceptional.items()))


if __name__ == "__main__":
    main()
