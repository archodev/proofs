"""Exact low-degree checks for Adrianov–Kreines, Theorem 1.3 and Example 1.2."""

from itertools import permutations


def cycle_type(p):
    seen = set()
    lengths = []
    for point in range(len(p)):
        if point in seen:
            continue
        start_size = len(seen)
        while point not in seen:
            seen.add(point)
            point = p[point]
        lengths.append(len(seen) - start_size)
    return tuple(sorted(lengths))


def representative(lengths):
    p = []
    for size in lengths:
        start = len(p)
        p.extend(range(start + 1, start + size))
        p.append(start)
    return tuple(p)


def canonical_pair(x, y):
    """Try every root. Traverse the two named generators in fixed order."""
    forms = []
    for root in range(len(x)):
        order = [root]
        number = {root: 0}
        for point in order:
            for neighbor in (x[point], y[point]):
                if neighbor not in number:
                    number[neighbor] = len(order)
                    order.append(neighbor)
        if len(order) < len(x):
            return None
        forms.append(tuple((number[x[i]], number[y[i]]) for i in order))
    return min(forms)


def count_classes(passport):
    a, b, c = (tuple(sorted(row)) for row in passport)
    n = sum(a)
    assert n == sum(b) == sum(c) and len(a) + len(b) + len(c) == n + 2
    x = representative(a)
    classes = set()
    for y in permutations(range(n)):
        if cycle_type(y) != b:
            continue
        # The inverse of x*y has the same cycle type as x*y.
        if cycle_type(tuple(x[j] for j in y)) == c:
            key = canonical_pair(x, y)
            if key is not None:
                classes.add(key)
    return len(classes)


if __name__ == "__main__":
    examples = [
        ((2, 1), (3,), (1, 2)),
        ((2, 2, 1), (3, 2), (3, 2)),
        ((2, 2, 3), (3, 3, 1), (3, 3, 1)),
        ((2, 2, 2, 1), (3, 4), (3, 3, 1)),
        ((2, 2, 2, 1), (3, 3, 1), (3, 4)),
        ((2, 2, 2, 3), (3, 3, 3), (3, 3, 1, 2)),
        ((2, 2, 2, 2, 1), (3, 3, 3), (3, 4, 2)),
        ((2, 2, 2, 2, 1), (3, 3, 3), (3, 1, 5)),
    ]
    mirror_control = ((2, 2, 2, 1), (3, 3, 1), (6, 1))
    for passport in examples + [mirror_control]:
        count = count_classes(passport)
        print(passport, count)
        assert count == (2 if passport == mirror_control else 1)
