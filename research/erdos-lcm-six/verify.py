"""Certificate for the four six-term product equations. Run with python-flint 0.9."""

from fractions import Fraction
import re
import subprocess
from math import gcd, isqrt, lcm, prod
from flint import acb, arb, arb_mat, ctx, fmpq, fmpz_mat, fmpz_poly

# a, b, shift from the minimal x to the quartic-model X, minimal a2,a4,a6, basis
CASES = [
    (2, 1, 5, -1, -65, 261, [(5, -6), (-7, 18), (-4, 21)]),
    (5, 2, 27, 1, -1633, 32963, [(23, -90), (-37, 210), (-31, 234)]),
    (5, 1, 13, -1, -408, 6912, [(-24, 48), (12, -60), (-18, 90)]),
    (10, 1, 27, 1, -1633, 97763, [(-58, 27), (23, -270), (-37, 330)]),
]


def verify_basis(A, B, C, points):
    model = f"[0,{A},0,{B},{C}]"
    result = subprocess.run(
        ["mwrank", "-q", "-p", "100", "-S", "-1"],
        input=model + "\n",
        text=True,
        capture_output=True,
        check=True,
    )
    log = result.stdout + "\n" + result.stderr
    assert (
        "The rank and full Mordell-Weil basis have been determined unconditionally."
        in log
    )
    generators = re.findall(r"Generator \d+ is \[(-?\d+):(-?\d+):1\]", log)
    assert [(int(x), int(y)) for x, y in generators] == points


def verify_david_parameters(A, B, C):
    # Weierstrass invariants in David's convention.
    g2 = 4 * (Fraction(A * A, 3) - B)
    g3 = -4 * (C - Fraction(A * B, 3) + Fraction(2 * A**3, 27))
    j = 1728 * g2**3 / (g2**3 - 27 * g3**2)
    den = lcm(g2.denominator, g3.denominator)
    assert arb(max(den, abs(int(den * g2)), abs(int(den * g3)))).log() < 100
    assert arb(max(abs(j.numerator), j.denominator)).log() < 100
    # Round the fractional exponent 107.3 up to 108 in David's constant.
    assert 3 * 10**36 * 4**50 * 6**108 * 3**12 * 5000**5 < 10**200


def height_bound(A, B, C, x):
    """Ball for the doubled Neron-Tate height, using seven exact doublings."""
    x = fmpq(x)
    for _ in range(7):
        x = (x**4 - 2 * B * x**2 - 8 * C * x + B**2 - 4 * A * C) / (
            4 * (x**3 + A * x * x + B * x + C)
        )
    H = max(abs(x.numerator), x.denominator)
    return (arb(H).log() + arb(0, 74)) / 4**7


def verify_heights(A, B, C, points):
    duplication_coeffs = (1, -2 * B, -8 * C, B * B - 4 * A * C, 4, 4 * A, 4 * B, 4 * C)
    assert max(map(abs, duplication_coeffs)) <= 10**12
    heights = [height_bound(A, B, C, x) for x, y in points]
    matrix = [[arb(0) for _ in points] for _ in points]
    for i, (x, y) in enumerate(points):
        assert y * y == x**3 + A * x * x + B * x + C
        matrix[i][i] = heights[i] - arb(1) / 20
        for j, (s, t) in enumerate(points[:i]):
            slope = fmpq(t - y, s - x)
            hsum = height_bound(A, B, C, slope**2 - A - x - s)
            matrix[i][j] = matrix[j][i] = (hsum - heights[i] - heights[j]) / 2
    for k in (1, 2, 3):
        assert arb_mat([row[:k] for row in matrix[:k]]).det() > 0
    # For any possible rational torsion prime l, l divides p*#E(F_p) for
    # every good p. This test needs only prime-to-p torsion specialization.
    common = 0
    for p in (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43):
        if (A * A * B * B - 4 * B**3 - 4 * A**3 * C - 27 * C * C + 18 * A * B * C) % p:
            counts = [sum(y * y % p == x for y in range(p)) for x in range(p)]
            size = 1 + sum(counts[(x**3 + A * x * x + B * x + C) % p] for x in range(p))
            common = gcd(common, p * size)
    assert common == 1


def logarithms(a, b, s, A, B, C, points):
    """Signed real integrals from x to infinity divided by the real period."""
    roots = fmpz_poly([C, B, A, 1]).complex_roots()
    assert len(roots) == 3 and all(mult == 1 for _, mult in roots)
    (e,) = [z.real for z, _ in roots if z.imag.is_zero()]
    (c,) = [z for z, _ in roots if z.imag > 0]
    period = 2 * acb.elliptic_rf(0, e - c, e - c.conjugate()).real
    assert arb(1) / 1000 < period < 3
    w = (arb(a) / b).root(3)
    z = -2 * (a - b * w * w)
    X = (2 * a * (z + a) + 3 * a * b * w) / (w * w)
    Y = ((X * X - 4 * a * a * b * b) * w - 3 * a * b * X - 6 * a**3 * b) / (2 * a)
    values = []
    for x, y in list(points) + [(X - s, Y)]:
        assert x > e and (y > 0 or y < 0)
        ell = acb.elliptic_rf(x - e, x - c, x - c.conjugate()).real
        values.append((ell if y > 0 else -ell) / period)
    return values


def lattice_check(values, B, T, tag):
    """Prove every nonzero vector in the rounded lattice has length > 5B."""
    rows = [
        [int(i == j) for j in range(4)]
        + [int((T * values[i] + arb(1) / 2).floor().unique_fmpz())]
        for i in range(4)
    ]
    L = fmpz_mat(rows + [[0, 0, 0, 0, T]])
    R, U = L.lll(transform=True)
    assert abs(U.det()) == 1 and U * L == R
    gram = R * R.transpose()
    d = 1
    margins = []
    for k in range(1, 6):
        block = fmpz_mat([[gram[i, j] for j in range(k)] for i in range(k)])
        nxt = block.det()
        assert nxt > (5 * B) ** 2 * d, tag
        margins.append(int(nxt // ((5 * B) ** 2 * d)))
        d = nxt
    return min(margins)


def product6(n):
    return prod(range(n + 1, n + 7))


def final_search(a, b, qmax):
    """Enumerate the exact-convergent neighborhoods that can contain a block."""
    ctx.prec = 400
    alpha = (arb(a) / b).root(6)
    p0, q0, p1, q1 = 0, 1, 1, 0
    hits = []
    tested = 0
    while True:
        aj = int(alpha.floor().unique_fmpz())
        p2, q2 = aj * p1 + p0, aj * q1 + q0
        if q1 > 0:
            lo, hi = max(9, q1), min(qmax, q2 - 1)
            if lo <= hi:
                for v in range(-101, 102):
                    lower = -((v * q0 - lo) // q1)
                    upper = (hi - v * q0) // q1
                    for u in range(lower, upper + 1):
                        q = u * q1 + v * q0
                        p = u * p1 + v * p0
                        if q % 2 == 0 or p % 2 == 0 or p <= q:
                            continue
                        n, m = (q - 7) // 2, (p - 7) // 2
                        tested += 1
                        if b * product6(m) == a * product6(n):
                            hits.append((n, m))
        if q2 > qmax:
            break
        p0, q0, p1, q1 = p1, q1, p2, q2
        alpha = 1 / (alpha - aj)
    return sorted(hits), tested


def run():
    for a, b, s, A, B, C, points in CASES:
        ctx.prec = 120
        verify_basis(A, B, C, points)
        verify_heights(A, B, C, points)
        verify_david_parameters(A, B, C)
        assert A == 3 * s - 8 * a * b
        assert B == 3 * s * s - 16 * a * b * s + 5 * a * a * b * b
        assert C == s**3 - 8 * a * b * s * s + 5 * a * a * b * b * s + a * a * b * b * (
            9 * a * a + 32 * a * b + 9 * b * b
        )
        ctx.prec = 17300
        values = logarithms(a, b, s, A, B, C, points)
        print(f"{a}/{b} height and log balls verified", flush=True)
        first = lattice_check(values, 10**1000, 10**5050, "first stage")
        second = lattice_check(values, 1000, 10**25, "second stage")
        print(f"  minimum squared Gram-Schmidt margins: {first}, {second}")
        # u=(n+3)(n+4)/2 and (2n+7)^2=8u+1.
        qmax = isqrt(8 * 1000 * 10**25 + 1)
        hits, tested = final_search(a, b, qmax)
        print(
            f"{a}/{b}  q <= {qmax}, tested {tested}, product pairs {hits}", flush=True
        )
        expected = {
            (2, 1): [(5, 6), (13, 15)],
            (5, 2): [(3, 4)],
            (5, 1): [],
            (10, 1): [],
        }
        assert hits == expected[(a, b)]
        for n, m in hits:
            value = lcm(*range(n + 1, n + 7))
            assert value == lcm(*range(m + 1, m + 7))
            print(f"  M({n},6) = M({m},6) = {value}")
        assert all(m < n + 6 for n, m in hits)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run the certificate with Python assertions enabled.")
    run()
