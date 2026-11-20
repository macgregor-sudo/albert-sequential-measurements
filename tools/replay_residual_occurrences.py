#!/usr/bin/env python3
"""Independent exact replay from the pinned literal robust Gram entry records."""
from collections import Counter
from fractions import Fraction
from itertools import groupby
from math import prod
from pathlib import Path
import re


def word(text):
    return tuple(map(int, text.split(","))) if text else ()


def load(configuration):
    entries, pairs = {}, []
    for path in sorted(Path("src/RobustCert").glob(f"Data{configuration}*.lean")):
        text = path.read_text()
        headers = rf"^def e{configuration}_(\d+) : Entry :=\s+mkE \[([^]]*)\] \[([^]]*)\](.*?)^theorem"
        for index, left, right, body in re.findall(headers, text, re.M | re.S):
            tabs = [
                (Fraction(int(n), int(d)), word(path))
                for n, d, path in re.findall(r"mkY \((-?\d+)\) (\d+) \[([^]]*)\]", body)
            ]
            tabs += [
                (Fraction(int(n), int(d)), word(start) + (int(no) + 4, int(yes)) + word(end))
                for n, d, start, no, yes, end in re.findall(
                    r"mkO \((-?\d+)\) (\d+) \[([^]]*)\] (\d+) (\d+) \[([^]]*)\]", body)
            ]
            defects = [
                (Fraction(int(yn), int(yd)), word(alpha), word(history), int(q), word(v),
                 Fraction(int(cn), int(cd)))
                for yn, yd, alpha, history, q, v, cn, cd in re.findall(
                    r"mkD \((-?\d+)\) (\d+) \[([^]]*)\] \[([^]]*)\] (\d+) \[([^]]*)\] \((-?\d+)\) (\d+)", body)
            ]
            assert len(tabs) == len(re.findall(r"\bmk[YO]\b", body))
            assert len(defects) == body.count("mkD")
            entries[int(index)] = word(left), word(right), tabs, defects
        declaration = re.search(rf"^def pairs{configuration}\d+ : [^\n]+$", text, re.M)[0]
        pairs.extend((Fraction(int(n), int(d)), int(i)) for n, d, i in re.findall(
            rf"\(\((-?\d+) / (\d+) : ℚ\), e{configuration}_(\d+)\)", declaration))
    assert len(entries) == len(pairs) == 324
    assert {i for _, i in pairs} == set(entries)
    return [(k, *entries[i]) for k, i in pairs]


def expand(signed):
    result = [(1, ())]
    for a in signed:
        if a < 4:
            result = [(k, w + (a,)) for k, w in result]
        else:
            result += [(-k, w + (a - 4,)) for k, w in result]
    return result


def canonical(walk):
    reduced = tuple(k for k, _ in groupby(walk))
    if reduced[:1] == (0,):
        reduced = reduced[1:]
    if reduced[-1:] == (0,):
        reduced = reduced[:-1]
    return min(reduced, reduced[::-1])


def add_pair(target, weight, left, right):
    for i, a in expand(left):
        for j, b in expand(right):
            target[canonical(a + b[::-1])] += weight * i * j


def longest(history, q, suffix):
    return history + (q,) + suffix + suffix[:-1][::-1] + (q,)


def reduce_prefix(path):
    return (0,) + (path[1:] if path[:1] == (0,) else path)


def replay(configuration):
    pairs = load(configuration)
    count = 0
    table_l1 = Fraction(0)
    buckets = Counter()
    bucket_rows = Counter()
    terms = Counter()
    raw_l1 = Fraction(0)
    tab_value = Fraction(0)
    native_left_penalty = Fraction(0)
    theta = Fraction(3, 2 ** (19 if configuration == "M" else 20))

    def add_term(weight, source_path):
        nonlocal raw_l1
        terms[reduce_prefix(source_path)] += weight
        raw_l1 += abs(weight)

    def overlap(a, b):
        assert a != b
        return Fraction(1, 2 if configuration == "S" and {a, b} == {0, 1} else 3)

    def chain(path):
        return prod(overlap(a, b) for a, b in zip(path, path[1:]))

    def native_tab(path):
        negatives = [i for i, a in enumerate(path) if a >= 4]
        if not negatives:
            return chain((0,) + path)
        (i,) = negatives
        start, end = (0,) + path[:i], path[i+1:]
        previous, no, following = start[-1], path[i] - 4, end[0]
        assert len({previous, no, following}) == 3
        includes_ab = {0, 1} <= {previous, no, following}
        triangle = Fraction(1, 6 if configuration == "S" and includes_ab else 9)
        complement_bridge = (overlap(previous, following) - 2 * triangle +
                             overlap(previous, no) * overlap(no, following))
        return chain(start) * complement_bridge * chain(end)

    def kind(path):
        return "H" if len(path) == 3 else "C" if path[-1] == 0 else "R"

    for k, left, right, tabs, defects in pairs:
        pair_type = "".join(sorted((kind(left), kind(right))))
        row = "CC" if pair_type == "CH" else pair_type
        check = Counter()
        add_pair(check, 1, left, right)
        for coeff, path in tabs:
            add_pair(check, -coeff, path, path)
            table_l1 += abs(k * coeff)
            tab_value += k * coeff * native_tab(path)
            add_term(k * coeff, path)
        for y, alpha, history, q, v, c in defects:
            count += 1
            start = history + (q,)
            long = longest(history, q, v)
            add_pair(check, -y, alpha, long)
            add_pair(check, y * c, alpha, start)
            pi = prod(overlap(a, b) for a, b in zip((0,) + alpha, alpha))
            buckets[pi] += abs(k * y)
            bucket_rows[pi, row] += abs(k * y)
            r = 1
            while 4 * r * r * pi <= 1:
                r *= 2
            eps = theta * r
            weight = abs(k * y)
            add_term(weight * eps / 2, alpha)
            native_left_penalty += weight * eps * pi / 2
            add_term(weight / (2 * eps), long)
            add_term(-weight * c / eps, start + v)
            add_term(weight * c * c / (2 * eps), start)
        assert all(value == 0 for value in check.values())
    ordered = tuple(buckets[q] for q in sorted(buckets, reverse=True))
    expected = {
        "M": (Fraction(1738400, 243), (Fraction(231377, 18), Fraction(17863, 3),
              Fraction(45542, 3), 14008, 32064)),
        "S": (Fraction(21466321, 1458), (Fraction(3099331, 108), 4065, Fraction(73880, 9),
              Fraction(28534, 3), Fraction(191914, 9), 9674, Fraction(56086, 3), 25290, 29772)),
    }[configuration]
    assert (table_l1, ordered) == expected
    assert count == 7962
    if configuration == "M":
        rows = [bucket_rows[Fraction(1, 27), row] for row in ("HH", "CC", "RR", "HR", "CR")]
        assert rows == [0, 1408, 2400, 5400, 4800]
        print("M 1/27 row contributions (HH, CC including CH, RR, RH, RC):", tuple(map(str, rows)))
    expected_tab_value, expected_margin = {
        "M": (Fraction(-4, 27), Fraction(4588961, 169869312)),
        "S": (Fraction(-205, 1458), Fraction(412734271, 18345885696)),
    }[configuration]
    assert tab_value == expected_tab_value
    native_margin = -(tab_value + native_left_penalty) / 3
    assert native_margin == expected_margin
    merged = {path: weight for path, weight in terms.items() if weight}
    assert all(len(path) <= 7 and path[0] == 0 for path in merged)
    print(f"{configuration}: replayed 324 exact pair identities, {count} residual occurrences")
    print(f"  T = {table_l1}; W = {tuple(map(str, ordered))}")
    print(f"  native table value from p_A = {tab_value}; margin from e/3 = {native_margin}")
    print(f"  raw coefficient norm = {raw_l1}; merged norm = {sum(map(abs, merged.values()))}; "
          f"merged support = {len(merged)}")


if __name__ == "__main__":
    for name in ("M", "S"):
        replay(name)
