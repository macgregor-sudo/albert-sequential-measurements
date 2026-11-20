#!/usr/bin/env python3
"""Audit literal companion A.2 final-q choices against the checked entry data."""
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import prod
import sys

sys.dont_write_bytecode = True

from replay_residual_occurrences import add_pair, load, longest, reduce_prefix


def r3_words(x, y, z):
    # Core TeX 2670–2675: the five short and twelve three-letter words.
    return frozenset(
        [(y,), (z, y), (z + 4, y), (x, y), (x + 4, y)]
        + [
            (first + a, second + b, last)
            for first, second, last in ((x, y, z), (z, x, y), (y, x, z))
            for a in (0, 4)
            for b in (0, 4)
        ]
    )


R3_WORD_SETS = {r3_words(x, y, z) for x, y, z in permutations(range(1, 4))}


def is_r3(records):
    if len(records) != 17:
        return False
    weight, alpha, history, q, _, _ = records[0]
    return (
        history == ()
        and q == 0
        and all(r[1:4] == (alpha, history, q) and abs(r[0]) == abs(weight) for r in records)
        and frozenset(r[4] for r in records) in R3_WORD_SETS
    )


def is_r2(records):
    if len(records) != 3:
        return False
    first, second, third = records
    return (
        first[1:4] == second[1:4] == third[1:4]
        and len(first[4]) == 1
        and len(second[4]) == len(third[4]) == 2
        and second[4][0] == third[4][0] + 4
        and first[4][0] == second[4][1] == third[4][1]
        and first[0] == -second[0] == third[0]
    )


def split_steps(records):
    i = 0
    while i < len(records):
        if is_r3(records[i : i + 17]):
            name, size = "R3", 17
        elif is_r2(records[i : i + 3]):
            name, size = "R2", 3
        else:
            name, size = "R1", 1
            assert len(records[i][4]) == 1
        yield name, records[i : i + size]
        i += size


def path_kind(path):
    if len(path) == 3:
        return "H"
    return "C" if path[-1] == 0 else "R"


def printed_exception(step, left, right, records):
    # Companion TeX 2415–2419. The RR example is W3 with a terminal q, not W1.
    _, alpha, history, q, _, _ = records[0]
    if step != "R2" or history:
        return False
    if q != 0 and alpha == (q,):
        return True
    if q != 0 or len(alpha) != 4:
        return False
    if (path_kind(left), path_kind(right)) == ("C", "R"):
        left, right = right, left
    if (path_kind(left), path_kind(right)) != ("R", "C"):
        return False
    x, y, z = left[:3]
    # RC(zxy) quotes RC(yxz) in the core TeX.
    return alpha == (x, y, z, 0) and right[:3] in ((y, x, z), (z, x, y))


def replay_choices(configuration, strict):
    pairs = load(configuration)
    theta = Fraction(3, 2 ** (19 if configuration == "M" else 20))
    output = Counter()
    buckets = Counter()
    removed = Counter()
    raw_l1 = Fraction(0)
    penalty = Fraction(0)
    table_l1 = Fraction(0)

    def emit(amount, word):
        nonlocal raw_l1
        output[reduce_prefix(word)] += amount
        raw_l1 += abs(amount)

    def probability(alpha):
        return prod(
            Fraction(1, 2 if configuration == "S" and {a, b} == {0, 1} else 3)
            for a, b in zip((0,) + alpha, alpha)
        )

    for k, left, right, tabs, defects in pairs:
        identity = Counter()
        add_pair(identity, 1, left, right)
        for coefficient, word in tabs:
            add_pair(identity, -coefficient, word, word)
            emit(k * coefficient, word)
            table_l1 += abs(k * coefficient)
        for step, records in split_steps(defects):
            exceptional = printed_exception(step, left, right, records)
            for y, alpha, history, q, suffix, c in records:
                if strict and alpha[-1:] == (q,) and not exceptional:
                    removed[(step, path_kind(left) + path_kind(right))] += 1
                    alpha = alpha[:-1]
                start = history + (q,)
                long_word = longest(history, q, suffix)
                add_pair(identity, -y, alpha, long_word)
                add_pair(identity, y * c, alpha, start)
                mass = abs(k * y)
                pi = probability(alpha)
                buckets[pi] += mass
                r = 1
                while 4 * r * r * pi <= 1:
                    r *= 2
                eps = theta * r
                p = mass * eps / 2
                penalty += p * pi
                emit(p, alpha)
                emit(mass / (2 * eps), long_word)
                emit(-mass * c / eps, start + suffix)
                emit(mass * c * c / (2 * eps), start)
        assert not any(identity.values())
    output = {w: c for w, c in output.items() if c}
    assert all(w[0] == 0 and len(w) <= 7 for w in output)
    margin = ((Fraction(4, 27) if configuration == "M" else Fraction(205, 1458)) - penalty) / 3
    return removed, buckets, margin, table_l1, raw_l1, sum(map(abs, output.values())), output


def printed_envelope(configuration, table_l1, buckets):
    theta = Fraction(3, 2 ** (19 if configuration == "M" else 20))
    c_max = Fraction(1, 3 if configuration == "M" else 2)
    total = table_l1
    for pi, mass in buckets.items():
        r = 1
        while 4 * r * r * pi <= 1:
            r *= 2
        eps = theta * r
        total += mass * (eps / 2 + (1 + c_max) ** 2 / (2 * eps))
    return total


def main():
    published_margins = {
        "M": Fraction(4588961, 169869312),
        "S": Fraction(412734271, 18345885696),
    }
    bounds = {"M": 5268 * 10**6, "S": 2892 * 10**7}
    for configuration in ("M", "S"):
        old = replay_choices(configuration, strict=False)
        strict = replay_choices(configuration, strict=True)
        removed, buckets, margin, table_l1, raw_l1, merged_l1, support = strict
        assert old[2] == published_margins[configuration]
        assert old[3] == table_l1
        assert removed == Counter({("R3", "CC"): 306, ("R3", "CH"): 306,
                                   ("R3", "HC"): 306, ("R2", "RR"): 18})
        assert old[-1] != support and old[1] != buckets and old[2] != margin
        expected_margin, expected_delta = {
            "M": (Fraction(4466849, 169869312), Fraction(-12320768, 9)),
            "S": (Fraction(394539295, 18345885696), Fraction(-8519680, 9)),
        }[configuration]
        assert expected_margin == margin
        delta = support[(0, 1, 2)] - old[-1][(0, 1, 2)]
        assert delta == expected_delta
        envelope = printed_envelope(configuration, table_l1, buckets)
        assert raw_l1 < bounds[configuration] < envelope
        print(f"{configuration}: removed {sum(removed.values())} terminal q records {dict(removed)}")
        print(f"  literal buckets: {tuple((str(p), str(buckets[p])) for p in sorted(buckets, reverse=True))}")
        print(f"  table coefficient norm {table_l1}; original margin {old[2]}; literal margin {margin}")
        print(f"  literal raw ℓ¹ {raw_l1} (printed bound {bounds[configuration]}); merged ℓ¹ {merged_l1}")
        print(f"  exact norm meets published bound; published coarse calculation becomes {envelope}")
        print(f"  coefficient change at (A,B,C): {delta}; support {len(support)}")


if __name__ == "__main__":
    main()
