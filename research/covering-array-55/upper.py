"""Verify the 56-row Witt-design construction; --slices prints its zero slices."""

from itertools import combinations, product
import sys


def hexads():
    # A ternary generator matrix [I | C]. Coordinates of C are infinity,0,1,2,3,4.
    # Off its diagonal the finite part of C is the quadratic character modulo 5.
    points = (None, 0, 1, 2, 3, 4)
    def entry(a, b):
        if a == b:
            return 0
        if a is None or b is None:
            return 1
        return 1 if (a - b) % 5 in (1, 4) else -1

    blocks = set()
    for u in product(range(3), repeat=6):
        v = tuple(sum(x * entry(a, b) for x, a in zip(u, points)) % 3 for b in points)
        support = sum(1 << i for i, x in enumerate(u + v) if x)
        if support.bit_count() == 6:
            blocks.add(support)
    return blocks


def masks(k, t):
    return [sum(1 << j for j in cols) for cols in combinations(range(k), t)]


def main():
    blocks = hexads()
    if len(blocks) != 132 or any(sum((b & m) == m for b in blocks) != 1 for m in masks(12, 5)):
        raise ValueError("Invalid Steiner system")
    # Keep blocks through point 11 and avoiding point 10, then puncture both.
    middle = [b & 1023 for b in blocks if b & 2048 and not b & 1024]
    units = [1 << j for j in range(10)]
    rows = sorted(middle + units + [1023 ^ r for r in units])
    if len(set(middle)) != 36 or len(rows) != 56 or len(set(rows)) != 56:
        raise ValueError("Invalid row count")
    if any(len({r & m for r in rows}) != 32 for m in masks(10, 5)):
        raise ValueError("Incomplete five-column projection")

    if sys.argv[1:] == ["--slices"]:
        for j in range(10):
            print(*(r & ((1 << j) - 1) | (r >> (j + 1)) << j for r in rows if not r & (1 << j)))
    elif sys.argv[1:] == ["--rows"]:
        print(*(format(r, "010b") for r in rows), sep="\n")
    elif not sys.argv[1:]:
        print("56 distinct rows; 252 five-column sets; all 8,064 requirements covered.")
    else:
        raise SystemExit("usage: python3 upper.py [--rows | --slices]")


if __name__ == "__main__":
    main()
