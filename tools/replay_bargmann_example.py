"""Replay the core §5.3 four-state example with exact rational projectors."""
from fractions import Fraction
from itertools import permutations


def projector(direction):
    norm_squared = sum(x * x for x in direction)
    return [[Fraction(x * y, norm_squared) for y in direction] for x in direction]


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, column)) for column in zip(*b)] for row in a]


def jordan(a, b):
    return [
        [(x + y) / 2 for x, y in zip(left, right)]
        for left, right in zip(multiply(a, b), multiply(b, a))
    ]


def trace(matrix):
    return sum(row[i] for i, row in enumerate(matrix))


if __name__ == "__main__":
    projections = [projector(v) for v in [(1, 0, 0), (1, 1, 0), (1, 2, 0), (1, 3, 0)]]
    traces = set()
    for a, b, c, d in permutations(projections):
        traces.add(trace(multiply(multiply(multiply(a, b), c), d)))
    a, b, c, d = projections
    t = [trace(multiply(jordan(a, x), jordan(y, z))) for x, y, z in [(b,c,d),(c,b,d),(d,b,c)]]
    omega = [sum(t) - 2 * value for value in t]
    assert t[0] == Fraction(49, 200)
    assert traces == {Fraction(x, 100) for x in (12, 21, 28)}
    assert set(omega) == traces and omega[0] == Fraction(12, 100)
    print("Double-pair traces:", *t)
    print("Signed combinations:", *omega)
