#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Reconstruct the reflected five-test margin from the deposited vector and the Lean recipes."""
import argparse
from collections import defaultdict, deque
from fractions import Fraction as Q
from hashlib import sha256
from math import prod
from pathlib import Path
import re
from zipfile import ZipFile

if not __debug__:
    raise SystemExit("Run without -O to enable exact certificate assertions")

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("archive", type=Path, help="Hexagon v1 source ZIP")
parser.add_argument("--negative-control", action="store_true", help="alter one ordered Gram coefficient")
args = parser.parse_args()
with ZipFile(args.archive) as archive:
    member = archive.read("companion/macgregor-finite-certificates.tex")
if sha256(member).hexdigest() != "775aac59da0f202323ffdb49c629c930b19dbee9ce6a8ba18a1658c4cc7f9134":
    raise SystemExit("Unexpected companion source digest")
source = member.decode()
block = source.split(r"\Phi={}&", maxsplit=1)[1].split(r"\end{aligned}", maxsplit=1)[0]
fraction = r"\\tfrac(?:\{(\d+)\}|(\d))(?:\{(\d+)\}|(\d))"
pattern = rf"([+-]?)\s*(?:(\d+)|{fraction})?\\eta\^([CRHJ])_\{{([BCD]+)\}}"
paper = []
for sign, integer, nb, ns, db, ds, kind, word in re.findall(pattern, block):
    value = Q(int(nb or ns), int(db or ds)) if nb or ns else Q(int(integer or "1"))
    p = tuple("ABCD".index(letter) for letter in word)
    suffix = (0,) if kind == "C" else (p[0],) if kind == "R" else ()
    paper.append(((-value if sign == "-" else value), p + suffix))

lean_text = Path("src/ReflectedRobustVector.lean").read_text()
raw = re.findall(r"\(\((-?\d+(?:/\d+)?) : ℚ\), \[([\d, ]+)\]\.map lt\)", lean_text)
lean = [(Q(value), tuple(map(int, word.split(",")))) for value, word in raw]
assert len(paper) == len(lean) == 22, (len(paper), len(lean))
assert paper == lean, [(i, a, b) for i, (a, b) in enumerate(zip(paper, lean, strict=True)) if a != b]
assert sum(abs(c) for c, _ in paper) == Q(713, 9)
print("22 exact coefficients and chronological C/R/H/J words match the deposited vector; raw ℓ¹ norm 713/9")

token = re.compile(r"reflectedRecipe\d+|appendRecipe|scaleRecipe|ReflectedRecipe|reflectedGramEntry|mk[YOD]|-?\d+(?:/\d+)?|[()⟨⟩\[\],:ℚ]")
recipes = {}


class RecipeReader:
    def __init__(self, source):
        self.tokens = deque(token.findall(source))
        assert "".join(self.tokens) == re.sub(r"\s+", "", source)

    def take(self, expect=None):
        got = self.tokens.popleft()
        assert expect is None or got == expect, (got, expect)
        return got

    def seq(self, reader):
        self.take("[")
        elements = []
        if self.tokens[0] != "]":
            elements.append(reader())
            while self.tokens[0] == ",":
                self.take(",")
                elements.append(reader())
        self.take("]")
        return elements

    def naturals(self):
        return self.seq(lambda: int(self.take()))

    def rational(self, typed):
        self.take("(")
        value = Q(self.take())
        if typed:
            self.take(":")
            self.take("ℚ")
        self.take(")")
        if not typed:
            value /= Q(self.take())
        return value

    def tab(self):
        op = self.take()
        coeff = self.rational(False)
        u = recipe_yes_word(self.naturals())
        if op == "mkO":
            a, n = int(self.take()), int(self.take())
            u += [(a, False), (n, True)] + recipe_yes_word(self.naturals())
        else:
            assert op == "mkY"
        return coeff, u

    def defect(self):
        self.take("mkD")
        y, alpha = self.rational(False), self.naturals()
        t, q, v = signed_word(self.naturals()), int(self.take()), signed_word(self.naturals())
        c = self.rational(False)
        return {"y": y, "alpha": alpha, "t": t, "q": q, "v": v, "c": c}

    def recipe(self):
        head = self.take()
        if head.startswith("reflectedRecipe"):
            return recipes[head]
        assert head == "("
        operation = self.take()
        if operation == "appendRecipe":
            a, b = self.recipe(), self.recipe()
            tabs, defs = a[0] + b[0], a[1] + b[1]
        elif operation == "scaleRecipe":
            scalar = self.rational(True)
            raw_tabs, raw_defs = self.recipe()
            tabs = [(scalar * c, w) for c, w in raw_tabs]
            defs = [d | {"y": scalar * d["y"]} for d in raw_defs]
        else:
            assert operation == "⟨"
            tabs = self.seq(self.tab)
            self.take(",")
            defs = self.seq(self.defect)
            self.take("⟩")
            self.take(":")
            self.take("ReflectedRecipe")
        self.take(")")
        return tabs, defs


def recipe_yes_word(xs):
    return [(x, True) for x in xs]


def signed_word(xs):
    return [(x % 4, x < 4) for x in xs]


source = Path("src/ReflectedRobustRecipes.lean").read_text()
for name, rhs in re.findall(r"^def (reflectedRecipe\d+) : ReflectedRecipe :=\n  ([^\n]+)", source, re.M):
    reader = RecipeReader(rhs)
    assert name not in recipes
    recipes[name] = reader.recipe()
    assert not reader.tokens

rows = []
for block in range(1, 7):
    source = Path(f"src/ReflectedRobustData{block}.lean").read_text()
    for index, rhs in re.findall(r"^def reflectedGram(\d+) : ℚ × Entry :=\n(.*?)\n\ntheorem", source, re.M | re.S):
        assert int(index) == len(rows)
        reader = RecipeReader(rhs)
        reader.take("reflectedGramEntry")
        coeff, left, right = reader.rational(True), reader.naturals(), reader.naturals()
        tabs, defs = reader.recipe()
        assert not reader.tokens
        rows.append((coeff, left, right, tabs, defs))


if args.negative_control:
    coeff, *rest = rows[0]
    rows[0] = (coeff + 1, *rest)
pairs = [dict(k=k, u1=u, u2=v, tabs=tabs, defs=defs) for k, u, v, tabs, defs in rows]
phi = [(k, list(w)) for k, w in paper]
anchor = (0, True)
overlaps = {
    (0, 1): Q(1, 2), (0, 2): Q(5, 18), (0, 3): Q(5, 18),
    (1, 2): Q(5, 18), (1, 3): Q(5, 18), (2, 3): Q(1, 2),
}


def overlap(x, y):
    return overlaps[tuple(sorted((x, y)))]


def chain(letters):
    return prod(overlap(x, y) for x, y in zip(letters, letters[1:]))


def tab_value(word):
    letters = tuple(letter for letter, _ in word)
    no = [i for i, (_, yes) in enumerate(word) if not yes]
    if not no:
        return chain((0, *letters))
    (i,) = no
    previous = letters[i - 1] if i else 0
    middle, following = letters[i:i + 2]
    gap = overlap(previous, following) - 2 * Q(5, 36) + overlap(previous, middle) * overlap(middle, following)
    return chain((0, *letters[:i])) * gap * chain(letters[i + 1:])


def yes_word(letters):
    return tuple((a, True) for a in letters)


def tail(word):
    return word[1:] if word and word[0] == anchor else word


def switches(word):
    reflected = (False, *(letter >= 2 for letter, _ in word))
    return sum(a != b for a, b in zip(reflected, reflected[1:]))


def cost(word):
    return len(word) + switches(word)


def expand(word):
    options = [(1, (anchor,))]
    prev = False
    for letter, yes in word:
        reflected = letter >= 2
        if prev != reflected:
            options = [(k * scale, w + insert) for k, w in options
                       for scale, insert in ((2, ((2, True),)), (2, ((2, False),)), (-1, ()))]
        outcome = ((0, 1, 3, 4)[letter], yes)
        options = [(k, (*w, outcome)) for k, w in options]
        prev = reflected
    return options


actual_pairs = [(Q(row["k"]), row["u1"], row["u2"]) for row in pairs]
if actual_pairs != [(a * b, u, v) for a, u in phi for b, v in phi]:
    raise SystemExit("Gram coefficient or history does not match the deposited vector")

epsilon = Q(11, 1944) / (Q(713, 9) ** 2 * Q(97, 2))
subtotals = [Q(0), Q(0), Q(0)]
counter_t = counter_y = native_left_penalty = Q(0)
tail_coeffs = defaultdict(Q)
largest_table = largest_defect = Q(0)
max_cost = 0
table_count = defect_count = 0


def add_term(coeff, word):
    word = tail(word)
    assert cost(word) <= 10
    tail_coeffs[word] += coeff
    return cost(word)


for row in pairs:
    k = Q(row["k"])
    per_t = per_y = Q(0)
    raw_group = int(len(row["u1"]) == 2) + int(len(row["u2"]) == 2)
    for c, raw_word in row["tabs"]:
        coeff, word = Q(c), tuple(map(tuple, raw_word))
        subtotals[raw_group] += k * coeff * tab_value(word)
        per_t += abs(coeff)
        max_cost = max(max_cost, add_term(k * coeff, word))
        table_count += 1
    for d in row["defs"]:
        y, c = Q(d["y"]), Q(d["c"])
        assert 0 <= c <= 1
        per_y += abs(y)
        a = abs(k * y)
        prefix = (*map(tuple, d["t"]), (d["q"], True))
        v = tuple(map(tuple, d["v"]))
        mid = prefix + v
        long = (*mid, *reversed(v[:-1]), prefix[-1])
        alpha = yes_word(d["alpha"])
        native_left_penalty += a * epsilon / 2 * chain((0, *d["alpha"]))
        for coeff, word in ((a * epsilon / 2, alpha), (a / (2 * epsilon), long),
                            (-a * c / epsilon, mid), (a * c * c / (2 * epsilon), prefix)):
            max_cost = max(max_cost, add_term(coeff, word))
        defect_count += 1
    largest_table = max(largest_table, per_t)
    largest_defect = max(largest_defect, per_y)
    counter_t += abs(k) * per_t
    counter_y += abs(k) * per_y

assert len(pairs) == 484 and (table_count, defect_count) == (4210, 15468)
assert subtotals == [Q(1873, 11664), Q(-335, 972), Q(2081, 11664)]
assert counter_t == Q(40796195, 13122) and counter_y == Q(1006273, 27)
assert (largest_table, largest_defect) == (Q(1969, 1296), Q(111, 4))
native_tail = sum(subtotals) + native_left_penalty
assert native_tail == Q(-76976323523, 13804146085248)
assert native_tail / 3 <= -Q(11, 11664)
assert counter_t + counter_y * (epsilon / 2 + 2 / epsilon) < 32750000000000

physical = defaultdict(Q)
for word, a in tail_coeffs.items():
    if a:
        terms = expand(word)
        assert len(terms) == 3 ** switches(word)
        assert sum(abs(k) for k, _ in terms) == 5 ** switches(word) <= 5 ** 5
        for k, w in terms:
            assert len(w) <= 11 and w[0] == anchor
            physical[w] += a * k
nonzero = [w for w, c in physical.items() if c]
assert len(nonzero) == 5547 and max(map(len, nonzero)) == 11
assert max_cost == 10
assert sum(map(abs, physical.values())) < 5 ** 5 * 32750000000000
w11 = next(w for w in nonzero if len(w) == 11)
threshold = Q(11, 11664) / (5 ** 5 * 32750000000000)
assert threshold > Q(9, 10 ** 21)

print(f"{len(pairs)} ordered Gram pairs, {table_count} table terms, {defect_count} defects")
print(f"subtotals {', '.join(map(str, subtotals))}; counterT {counter_t}; counterY {counter_y}")
print(f"max per-row table {largest_table}; max per-row defect {largest_defect}; max tail cost {max_cost}")
print(f"native tail {native_tail}; native anchored {native_tail / 3}; paper threshold {threshold}")
print(f"{len(nonzero)} collected physical words; max length 11 with nonzero coefficient {physical[w11]} at {w11}")
