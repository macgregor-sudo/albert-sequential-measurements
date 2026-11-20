#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Replay selected exact certificates of Hexagon 2611.00620v1 from its TeX.

Usage: python3 tools/replay_paper_certificates.py /path/to/public.zip
The transcript binds both TeX members by hash. The code below transcribes the
published formulas and uses Python's standard library only.
"""

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, permutations, product
from math import prod
from pathlib import Path
from zipfile import BadZipFile, ZipFile


SOURCE_DIGESTS = {
    "main.tex": "b1d6e0990bef176501af5be6a9f8c645713fd9769ff4185e859521b75b6c7670",
    "companion/macgregor-finite-certificates.tex": (
        "775aac59da0f202323ffdb49c629c930b19dbee9ce6a8ba18a1658c4cc7f9134"
    ),
}
TRIPLES = tuple("".join(p) for p in permutations("BCD"))
SIGNED_ORDERS = (1, -1, -1, 1, 1, -1)
PARTITIONS = (("AB", "CD"), ("AC", "BD"), ("AD", "BC"))


def check(description, actual, expected):
    if actual != expected:
        raise ValueError(f"{description}: got {actual!r}, expected {expected!r}")


def bind_source(archive):
    with ZipFile(archive) as source:
        for member, expected in SOURCE_DIGESTS.items():
            digest = sha256(source.read(member)).hexdigest()
            check(member + " SHA-256", digest, expected)
            print(f"{digest}  {member}")


@dataclass(frozen=True)
class QRootTwo:
    """The rational quadratic extension used in M's second vector."""

    real: F = F(0)
    root: F = F(0)

    def __add__(self, other):
        return QRootTwo(self.real + other.real, self.root + other.root)

    def __neg__(self):
        return QRootTwo(-self.real, -self.root)

    def __mul__(self, other):
        return QRootTwo(
            self.real * other.real + 2 * self.root * other.root,
            self.real * other.root + self.root * other.real,
        )

    def scale(self, factor):
        return QRootTwo(self.real * factor, self.root * factor)

    def rational(self):
        check("quadratic irrational part", self.root, 0)
        return self.real


ZERO = QRootTwo()


def basis(index, coefficient=QRootTwo(F(1))):
    return tuple(coefficient if i == index else ZERO for i in range(8))


def quat_basis_mul(a, b):
    if not a or not b:
        return 1
    if a == b:
        return -1
    return 1 if (a, b) in ((1, 2), (2, 3), (3, 1)) else -1


def oct_basis_mul(i, j):
    # Core Appendix A.2: (a+bℓ)(c+dℓ)=(ac−d̄b)+(da+bc̄)ℓ.
    a, b = i % 4, j % 4
    if i < 4 and j < 4:
        return quat_basis_mul(a, b), a ^ b
    if i < 4:
        return quat_basis_mul(b, a), 4 + (a ^ b)
    if j < 4:
        return (1 if b == 0 else -1) * quat_basis_mul(a, b), 4 + (a ^ b)
    return (-1 if b == 0 else 1) * quat_basis_mul(b, a), a ^ b


def oct_add(x, y):
    return tuple(a + b for a, b in zip(x, y, strict=True))


def oct_scale(x, factor):
    return tuple(a.scale(factor) for a in x)


def oct_conj(x):
    return (x[0], *(-a for a in x[1:]))


def oct_mul(x, y):
    result = [ZERO] * 8
    for i, a in enumerate(x):
        if a == ZERO:
            continue
        for j, b in enumerate(y):
            if b == ZERO:
                continue
            sign, index = oct_basis_mul(i, j)
            result[index] = result[index] + (a * b).scale(sign)
    return tuple(result)


def oct_sum(terms):
    result = (ZERO,) * 8
    for x in terms:
        result = oct_add(result, x)
    return result


def matrix_add(x, y):
    return tuple(tuple(oct_add(a, b) for a, b in zip(r, s, strict=True))
                 for r, s in zip(x, y, strict=True))


def matrix_scale(x, factor):
    return tuple(tuple(oct_scale(a, factor) for a in row) for row in x)


def matrix_mul(x, y):
    return tuple(tuple(oct_sum(oct_mul(x[i][k], y[k][j]) for k in range(3))
                       for j in range(3)) for i in range(3))


def trace(x):
    value = oct_sum(x[i][i] for i in range(3))
    check("real trace", value[1:], (ZERO,) * 7)
    return value[0].rational()


def jordan(x, y):
    return matrix_scale(matrix_add(matrix_mul(x, y), matrix_mul(y, x)), F(1, 2))


def quadratic(x, y):
    return matrix_add(matrix_scale(jordan(x, jordan(x, y)), 2),
                      matrix_scale(jordan(jordan(x, x), y), -1))


def atom(column):
    result = tuple(tuple(oct_mul(a, oct_conj(b)) for b in column) for a in column)
    return matrix_scale(result, 1 / trace(result))


def paper_atoms():
    # Core sec:cer paragraph Two configurations, companion sec:five and sec:fiv:list.
    zero = (ZERO,) * 8
    one, i, j, ell = (basis(k) for k in (0, 1, 2, 4))
    a, b, c, d = map(atom, ((one, zero, zero), (one, one, zero),
                            (one, i, one), (one, j, ell)))
    bmax = atom((one, basis(0, QRootTwo(F(0), F(1))), zero))
    unit = tuple(tuple(one if r == s else zero for s in range(3)) for r in range(3))
    reflector = matrix_add(matrix_scale(c, 2), matrix_scale(unit, -1))
    cj = quadratic(reflector, atom((one, j, zero)))
    dl = quadratic(reflector, atom((one, ell, zero)))
    for label, p in zip("ABCDUVZ", (a, b, c, d, bmax, cj, dl), strict=True):
        check(f"{label} trace one", trace(p), 1)
        check(f"{label} idempotent", jordan(p, p) == p, True)
    return {"M": (a, bmax, c, d), "S": (a, b, c, d), "reflected": (a, b, cj, dl)}


@dataclass(frozen=True)
class Traces:
    pairs: dict
    triangles: dict
    double_pairs: tuple

    def o(self, a, b):
        return self.pairs["".join(sorted(a + b))]

    def r(self, a, b, c):
        return self.triangles["".join(sorted(a + b + c))]

    def w(self, letter):
        return sum(self.double_pairs) - 2 * self.double_pairs["BCD".index(letter)]

    def invariant_groups(self):
        # Core eq:A:Acal52, grouped in the order of companion app:cert:refl.
        a, b, c, d, e, f = self.pairs.values()
        x, y, z, t = self.triangles.values()
        u, v, w = (self.w(k) for k in "BCD")
        return (
            a * b * c * d * e * f,
            -(x * x * c * e * f + y * y * b * d * f + z * z * a * d * e + t * t * a * b * c),
            -4 * x * y * z * t,
            -(a * f * u * u + b * e * v * v + c * d * w * w),
            2 * u * (x * y * f + z * t * a),
            2 * v * (x * z * e + y * t * b),
            2 * w * (x * t * c + y * z * d),
            -2 * u * v * w,
        )


def atom_traces(atoms):
    p = dict(zip("ABCD", atoms, strict=True))
    jp = {a + b: jordan(p[a], p[b]) for a, b in combinations(p, 2)}
    return Traces(
        {ab: trace(x) for ab, x in jp.items()},
        {a + b + c: trace(jordan(jp[a + b], p[c])) for a, b, c in combinations(p, 3)},
        tuple(trace(jordan(jp[ab], jp[cd])) for ab, cd in PARTITIONS),
    )


def gram_hcr(traces, row, column):
    """Core Lemma C.1(b), with row (x,y,z) and columns in relative lexicographic order."""
    x, y, z = row
    ax, ay, az = (traces.o("A", k) for k in row)
    xy, xz, yz = traces.o(x, y), traces.o(x, z), traces.o(y, z)
    axy, axz, ayz, xyz = traces.r("A", x, y), traces.r("A", x, z), traces.r("A", y, z), traces.r(x, y, z)
    wx, wy, wz = (traces.w(k) for k in row)
    hh = (ax * xy * yz, ax * yz * xyz, 2 * xyz * axy - xy * wz,
          xz * yz * axy, xy * yz * axz, 2 * xyz * wy - xy * yz * axz)
    cc0, cc1, cc2 = ax * xy * yz * az, 2 * ax * ayz * xyz - ax * yz * wx, az * hh[2]
    cc = (cc0, cc1, cc2, 2 * wy * wz - cc1, 2 * wx * wy - cc2, 2 * wy * wy - cc0)
    rr0, rr3, rr4 = ax * xy * yz * xz, xy * hh[3], xz * hh[4]
    rr = (rr0, 2 * ax * xyz * xyz - rr0, 2 * xyz * hh[2] - rr3, rr3, rr4,
          2 * xz * xyz * wy - rr4)
    rh = (rr[0], rr[1], xz * hh[2], hh[3], xy * xz * wy, hh[5])
    rc0, rc2, rc3 = (ax * xy * yz * axz,
                     2 * axz * hh[2] - xz * (2 * axy * wy - ax * xy * ayz), ax * hh[3])
    rc = (rc0, 2 * ax * xyz * wz - rc3, rc2, rc3, 2 * ax * xyz * wx - rc2,
          2 * ax * xyz * wy - rc0)
    order = tuple("".join(p) for p in permutations(row))
    c = order.index(column)
    return {"HH": hh[c], "CC": cc[c], "RR": rr[c], "RH": rh[c], "RC": rc[c]}


def gram_j(traces, row, column_kind, column):
    """Core Lemma C.1(c), for row eta^J_(u,v)."""
    u, v = row
    w = next(k for k in "BCD" if k not in row)
    au, av = traces.o("A", u), traces.o("A", v)
    uv, vw = traces.o(u, v), traces.o(v, w)
    auv, auw, avw = traces.r("A", u, v), traces.r("A", u, w), traces.r("A", v, w)
    uvw = traces.r(u, v, w)
    wu, wv, ww = (traces.w(k) for k in (u, v, w))
    if column_kind == "J":
        return {u + v: au * uv, v + u: uv * auv, u + w: au * uvw,
                w + v: wv, v + w: vw * auv, w + u: uv * auw}[column]
    h2 = gram_hcr(traces, u + v + w, v + u + w)["HH"]
    c0, c1, c4 = au * uv * avw, au * av * uvw, av * uv * auw
    r0, r4 = au * uv * uvw, vw * uv * auw
    values = {
        "H": (au * uv * vw, au * uvw, h2, uv * ww, uv * auw, uv * wv),
        "C": (c0, c1, 2 * wu * auv - c4, 2 * ww * auv - c1, c4, 2 * wv * auv - c0),
        "R": (r0, r0, h2, 2 * uvw * auv - h2, r4, 2 * uvw * wv - r4),
    }
    order = tuple("".join(p) for p in permutations((u, v, w)))
    return values[column_kind][order.index(column)]


def gram_matrix(traces):
    vectors = [(kind, order) for kind in "CRH" for order in TRIPLES]
    vectors += [("J", "".join(p)) for p in permutations("BCD", 2)]
    entries = {}
    for a, b in product(vectors, repeat=2):
        kind_a, order_a = a
        kind_b, order_b = b
        if kind_a == "J":
            value = gram_j(traces, order_a, kind_b, order_b)
        elif kind_b == "J":
            value = gram_j(traces, order_b, kind_a, order_a)
        else:
            block = kind_a + kind_b
            if block in ("HR", "CR"):
                order_a, order_b = order_b, order_a
                block = block[::-1]
            if block in ("HC", "CH"):
                block = "CC"
            value = gram_hcr(traces, order_a, order_b)[block]
        entries[a, b] = value
    check("Gram symmetry", all(value == entries[b, a] for (a, b), value in entries.items()), True)
    check("Gram order", len(vectors), 24)
    return entries


def coefficients_for_triples(weights):
    return {(kind, order): signed * value
            for signed, order, coeffs in zip(SIGNED_ORDERS, TRIPLES, weights, strict=True)
            for kind, value in zip("CRH", coeffs, strict=True)}


def quadratic_form(gram, left, right):
    return sum(a * b * gram[u, v] for u, a in left.items() for v, b in right.items())


def canonical_walk(word):
    word = "".join(letter for i, letter in enumerate(word) if not i or word[i - 1] != letter).strip("A")
    return min(word, word[::-1])


def canonical_walks_by_length(horizon):
    yield {""}
    words = list("BCD")
    for _ in range(horizon):
        yield {min(word, word[::-1]) for word in words if not word.endswith("A")}
        words = [w + letter for w in words for letter in "ABCD" if w[-1] != letter]


def walk_relations(word, traces):
    """Core eq:cer:steps and eq:cer:R3step, with their right-history limits."""
    views = {word, word[::-1], word + "A", word[::-1] + "A"}
    for w in sorted(views):
        if w[1:2] == "A":
            yield traces.o("A", w[0]), canonical_walk(w[2:]), None
        for i in range(max(0, len(w) - 5), len(w) - 2):
            q, v, r = w[i:i + 3]
            if q == r:
                yield traces.o(q, v), canonical_walk(w[:i] + q + w[i + 3:]), None
        for i in range(max(0, len(w) - 5), len(w) - 3):
            q, v, s, r = w[i:i + 4]
            if q == r and len({q, v, s}) == 3:
                yield (2 * traces.r(q, v, s), canonical_walk(w[:i] + q + w[i + 4:]),
                       canonical_walk(w[:i] + q + s + v + q + w[i + 4:]))
        if len(w) >= 3 and set(w[-3:]) == set("BCD") and (len(w) == 3 or w[-4] == "A"):
            yield 2 * traces.w(w[-2]), canonical_walk(w[:-3]), canonical_walk(w[:-3] + w[-3:][::-1])


def walk_values(traces):
    """Recover values by propagating the printed relations, independently of Gram formulas."""
    values = {"": F(1), **{x: traces.o("A", x) for x in "BCD"}}

    def seed(word, value):
        key = canonical_walk(word)
        check(f"seed coherence at {key}", values.setdefault(key, value), value)

    for x, y, z in TRIPLES:
        seed(x + y, traces.r("A", x, y))
        seed(x + y + z, traces.w(y))
        seed(x + y + z + x, traces.o("A", x) * traces.r(x, y, z))
        seed(x + y + "A" + z + y + x, traces.o("A", x) * traces.o(x, y) * traces.r("A", y, z))

    for words in canonical_walks_by_length(8):
        equations = {w: tuple(walk_relations(w, traces)) for w in sorted(words)}
        unresolved = {w for w in words if w not in values}
        while unresolved:
            solved = set()
            for w in sorted(unresolved):
                for factor, short, peer in equations[w]:
                    if short not in values:
                        continue
                    if peer is None:
                        values[w] = factor * values[short]
                    elif peer == w:
                        values[w] = factor * values[short] / 2
                    elif peer in values:
                        values[w] = factor * values[short] - values[peer]
                    else:
                        continue
                    solved.add(w)
                    break
            if not solved:
                raise ValueError(f"walk relations left {len(unresolved)} unknowns: {sorted(unresolved)[:6]}")
            unresolved.difference_update(solved)
        for w, alternatives in equations.items():
            for factor, short, peer in alternatives:
                check(f"consistent walk relation at {w}", values[w],
                      factor * values[short] - (F(0) if peer is None else values[peer]))
    return values


def replay_gram_paths(name, traces, gram):
    # Core eq:cer:W28, in print order including the empty word.
    paths = ("", "CBA", "DCA", "BDA", "DCBA", "CDBA", "DBCA",
             "B", "CB", "DB", "CDAB", "DCB", "CDB", "BDCB",
             "C", "DC", "BC", "DBAC", "BDC", "DBC", "CBDC",
             "D", "BD", "CD", "BCAD", "CBD", "BCD", "DCBD")
    check("W28 distinct paths", len(set(paths)), 28)
    values = walk_values(traces)
    whole = {(a, b): values[canonical_walk(a + b[::-1])] for a, b in product(paths, repeat=2)}

    def in_w28(vector):
        kind, order = vector
        if kind in "HJ":
            return {order: 1}
        if kind == "C":
            if order + "A" in paths:
                return {order + "A": 1}
            return {"": 2 * traces.w(order[1]), order[::-1] + "A": -1}
        x, y, z = order
        if order + x in paths:
            return {order + x: 1}
        return {x: 2 * traces.r(x, y, z), x + z + y + x: -1}

    for (a, b), value in gram.items():
        check(f"{name} W28 reproduces printed Gram formula {a}/{b}",
              quadratic_form(whole, in_w28(a), in_w28(b)), value)
    digest = sha256("\n".join(str(whole[a, b]) for a in paths for b in paths).encode()).hexdigest()
    print(f"{name} W28: 784 entries, agrees with all 576 printed-form entries; SHA-256 {digest}")


def row_norms(traces, coefficients):
    # Core app:cert:seven, Ψ: C/H cross terms counted in the C row, R cross terms in R.
    def row_value(s):
        total = F(0)
        for t in TRIPLES:
            g = gram_hcr(traces, s, t)
            for block, value in g.items():
                left, right = block
                entry = coefficients[left, s] * coefficients[right, t] * value
                total += entry if left == right else 2 * entry
            total += 2 * coefficients["C", s] * coefficients["H", t] * g["CC"]
        return total

    return tuple(row_value(s) for s in TRIPLES)


def replay_gram(data, control):
    matrix = {key: gram_matrix(traces) for key, traces in data.items()}
    for name, traces in data.items():
        replay_gram_paths(name, traces, matrix[name])
    m = coefficients_for_triples([(4, 10, -9)] * 6)
    s = coefficients_for_triples([(1, 4 if s.endswith("B") else 3, -3) for s in TRIPLES])
    s_robust = coefficients_for_triples([((3, 14, -13), (4, 15, -13), (6, 17, -15))[s.index("B")]
                                         for s in TRIPLES])
    m_norm = quadratic_form(matrix["M"], m, m)
    s_norm = quadratic_form(matrix["S"], s, s)
    robust_s_norm = quadratic_form(matrix["S"], s_robust, s_robust)
    for name, norm, expected in (("M", m_norm, F(-4, 27)), ("S", s_norm, F(-2, 729)),
                                 ("S robust", robust_s_norm, F(-205, 1458))):
        check(name + " Gram contraction", norm, expected)
        print(f"{name} Gram contraction: {norm}")
    check("S row sums", tuple(row_norms(data["S"], s)[i] for i in (0, 2, 3)),
          (F(4, 81), F(1, 162), F(-83, 1458)))
    check("S robust row sums", tuple(row_norms(data["S"], s_robust)[i] for i in (0, 2, 3)),
          (F(869, 972), F(-22, 27), F(-109, 729)))
    core = dict(zip(product("CRH", TRIPLES),
                    (2, -2, -3, 2, 3, -2, 4, -4, -6, 6, 6, -6, -4, 4, 7, -4, -7, 4), strict=True))
    if control == "vector":
        core["C", "BCD"] += 1
    two_step = {("J", "CD"): F(-10, 9), ("J", "CB"): F(1, 2),
                ("J", "DC"): F(10, 9), ("J", "DB"): F(-1, 2)}
    reflected = matrix["reflected"]
    pieces = (quadratic_form(reflected, core, core), 2 * quadratic_form(reflected, core, two_step),
              quadratic_form(reflected, two_step, two_step))
    check("reflected certificate components", pieces, (F(1873, 11664), F(-335, 972), F(2081, 11664)))
    check("reflected actual contraction", quadratic_form(reflected, core | two_step, core | two_step), F(-11, 1944))
    check("reflected coefficient norm", sum(map(abs, (core | two_step).values())), F(713, 9))
    print(f"reflected Gram contraction: {sum(pieces)} from {', '.join(map(str, pieces))}")
    return m_norm, robust_s_norm


def replay_traces(atoms):
    data = {name: atom_traces(menu) for name, menu in atoms.items()}
    expected = {
        "M": ((F(1, 3),) * 6, (F(1, 9),) * 4, (F(1, 27),) * 3, F(4, 19683)),
        "S": ((F(1, 2),) + (F(1, 3),) * 5, (F(1, 6), F(1, 6), F(1, 9), F(1, 9)),
              (F(1, 18),) * 3, F(1, 5832)),
        "reflected": ((F(1, 2),) + (F(5, 18),) * 4 + (F(1, 2),), (F(5, 36),) * 4,
                      (F(5, 72), F(43, 648), F(43, 648)), F(1, 11664)),
    }
    for name, traces in data.items():
        invariant = sum(traces.invariant_groups())
        check(name + " thirteen traces and invariant",
              (tuple(traces.pairs.values()), tuple(traces.triangles.values()), traces.double_pairs, invariant),
              expected[name])
        print(f"{name} native thirteen traces: match, four-point invariant {invariant}")
    check("reflected eight groups", tuple(x * 1679616 for x in data["reflected"].invariant_groups()),
          (2500, -5000, -2500, -2931, 4100, 2500, 2500, -1025))
    sum_s = atoms["S"][0]
    for atom_s in atoms["S"][1:]:
        sum_s = matrix_add(sum_s, atom_s)
    tr1, tr2, tr3 = trace(sum_s), trace(jordan(sum_s, sum_s)), trace(jordan(sum_s, jordan(sum_s, sum_s)))
    e2 = (tr1 * tr1 - tr2) / 2
    determinant = (tr1 * tr1 * tr1 - 3 * tr1 * tr2 + 2 * tr3) / 6
    dtet = sum(data["S"].invariant_groups()) / prod(data["S"].pairs.values())
    check("S all-state separator scalar inputs", (tr1, tr2, tr3, e2, determinant, dtet),
          (4, F(25, 3), F(61, 3), F(23, 6), F(7, 9), F(1, 12)))
    check("S companion Prop 2.6 margin", dtet * (determinant / e2) / 2, F(7, 828))
    check("S generic margin", dtet * determinant / 8, F(7, 864))
    print(f"S Δtet: {dtet}, atom-sum determinant: {determinant}, improved scalar margin: 7/828")
    return data


def replay_robust_constants(norms, control):
    # Companion app:cert:sevenrobust prints the aggregate counters. The
    # per-entry defect-derivation data are not inputs to this calculation.
    configs = {
        "M": (F(1738400, 243), (F(1), F(1, 3), F(1, 9), F(1, 27), F(1, 81)),
              (F(231377, 18), F(17863, 3), F(45542, 3), F(14008), F(32064)),
              (1, 1, 2, 4, 8), F(3, 2**19), F(1, 3), F(422183, 18),
              F(4588961, 169869312), 5_268_000_000),
        "S": (F(21466321, 1458), (F(1), F(1, 2), F(1, 3), F(1, 6), F(1, 9), F(1, 18),
                                 F(1, 27), F(1, 54), F(1, 81)),
              (F(3099331, 108), F(4065), F(73880, 9), F(28534, 3), F(191914, 9), F(9674),
               F(56086, 3), F(25290), F(29772)),
              (1, 1, 1, 2, 2, 4, 4, 4, 8), F(3, 2**20), F(1, 2), F(16559187, 324),
              F(412734271, 18345885696), 28_920_000_000),
    }
    for norm, (name, config) in zip(norms, configs.items(), strict=True):
        table, probabilities, weights, dyadics, theta, max_c, bucket_sum, gap, printed_bound = config
        if control == "counter" and name == "S":
            weights = (weights[0] + 1, *weights[1:])
        buckets = tuple(zip(probabilities, weights, dyadics, strict=True))
        check(name + " dyadic calibration", all(r * r * p <= 1 < 4 * r * r * p for p, _, r in buckets), True)
        calibration = sum(p * v * r for p, v, r in buckets)
        check(name + " calibrated bucket sum", calibration, bucket_sum)
        actual_gap = (-norm - theta * calibration / 2) / 3
        check(name + " robust negative margin", actual_gap, gap)
        norm_bound = table + sum(v * (theta * r / 2 + (1 + max_c)**2 / (2 * theta * r)) for _, v, r in buckets)
        check(name + " printed norm inequality", norm_bound <= printed_bound, True)
        print(f"{name} robust margin {actual_gap}, coefficient bound {norm_bound} ≤ {printed_bound}")

    # The companion's five-test explicit margin uses upper bounds on two
    # quantities for every Gram entry. Check their propagation, not those
    # entry budgets or the generating residual identities themselves.
    total = F(713, 9)
    norm = F(11, 1944)
    table = total**2 * F(17, 2)
    weights = total**2 * F(97, 2)
    upper_bound = table + norm / 2 + 2 * weights**2 / norm
    printed_bound = 32_750_000_000_000
    check("five-test conservative coefficient bound", upper_bound < printed_bound, True)
    check("five-test margin arithmetic", F(11, 11664) / (5**5 * printed_bound) > F(9, 10**21), True)
    print("five-test margin propagation: >9e-21 given the printed per-entry budgets")


def companion_words(prefixes, orientations, reverse_orientations, control):
    # Companion eq:cer:elevenlist and tab:cer:tails. Uppercase is yes.
    tails_b = {"", *"BCD"}
    tails_b.update(x + "A" for x in "BCD")
    for x, y in permutations("BCD", 2):
        tails_b.update((x + y, x + y + x, x + y + "A", x + y + "A" + y))
    for x, y in orientations:
        b = x.lower()
        tails_b.update((b + y, x + y + x + "A", b + y + b + "A"))

    tails_d = {x.lower() + y for x, y in reverse_orientations}
    for x, y in reverse_orientations:
        for a in (x, x.lower()):
            tails_d.add(a + y + a + "A")
    for x, y, z in TRIPLES:
        for a, b in product((x, x.lower()), (y, y.lower())):
            tails_d.update((a + b + z, a + b + z + b + a + "A"))

    check("B-tail count", len(tails_b), 40)
    check("D-tail count", len(tails_d), 57)
    far = {"ABDCA", "ABCDA", "ABCDCB", "ABcDcB", "ABDCAC", "ABCDAD"}
    if control == "word":
        far.remove("ABcDcB")
    short = prefixes[0] | prefixes[1]
    b_family = {p + b for p in short | prefixes[2] for b in tails_b}
    d_family = {p + d for p in short for d in tails_d}
    check("B-prefix family count", len(b_family), 1636)
    check("D-prefix family count", len(d_family), 399)
    check("tail-family adjacency overlaps", (b_family & d_family) | ((b_family | d_family) & far), set())
    return b_family | d_family | far


def reduced(word):
    result = []
    for letter in word:
        if result and result[-1].upper() == letter.upper():
            check("adjacent complementary projections in ledger", letter, result[-1])
        else:
            result.append(letter)
    return "".join(result)


def replay_word_ledger(control):
    # Companion rows (i)–(iv) of tab:cer:ledger, the chronological purity
    # spellings, and app:cert:quantitative's R2/R3 primitive identities.
    pairings = tuple(permutations("BCD", 2))
    cyclic = ("BCD", "CDB", "DBC")
    orientations = tuple(s[:2] for s in cyclic)
    prefixes = tuple({"A" + "".join(x + y + "A" for x, y in path)
                      for path in product(pairings, repeat=d)} for d in range(3))
    tail_words = companion_words(prefixes, orientations, tuple(s[::-1] for s in orientations), control)

    def r2(history, base, x, y):
        return [(history, base, v) for v in (y, x + y, x.lower() + y)]

    def access(x, y, z):
        return tuple(a + b + z for a, b in product(("", x, x.lower()), ("", y, y.lower())))

    scalar_and_unitary = []
    for t in sorted(set.union(*prefixes)):
        for x, y in orientations:
            scalar_and_unitary.extend(r2(t, "A", x, y))
        for x, y in pairings:
            scalar_and_unitary.extend(((t + y, x, "A"), (t, y, x), (t, "A", y)))

    clifford, clifford_uncompressed = [], []
    for t in sorted(prefixes[0] | prefixes[1]):
        for x, y, z in cyclic:
            terms = access(x, y, z) + access(z, x, y) + access(y, x, z)
            contractions = [(t + x, y, "A"), (t + z, y, "A")]
            clifford.extend(contractions + [(t, "A", v) for v in sorted(set(terms))])
            clifford_uncompressed.extend(contractions + [(t, "A", v) for v in terms])

    fourth_face = [("AB", "D", "A"), ("ABD", "C", "A"), ("AB", "C", "A"), ("ABC", "D", "A")]
    fourth_face += r2("AB", "B", "C", "D") + [("A", "A", "B")]
    apps = scalar_and_unitary + clifford + fourth_face
    check("per-row purity applications", tuple(map(len, (scalar_and_unitary, clifford, fourth_face))), (1161, 504, 8))
    check("purity application occurrences", len(apps), 1673)
    check("uncompressed occurrences", len(scalar_and_unitary + clifford_uncompressed + fourth_face), 1778)

    def emit(applications):
        words = set()
        for t, q, v in applications:
            words.update(map(reduced, (t + q, t + q + v, t + q + v + v[:-1][::-1] + q)))
        return words

    emitted = emit(apps)
    check("ledger words outside printed list", sorted(emitted - tail_words), [])
    check("printed words outside relation ledger", sorted(tail_words - emitted), [])
    check("uncompressed word set", emit(scalar_and_unitary + clifford_uncompressed + fourth_face), emitted)
    histogram = tuple(Counter(map(len, emitted))[i] for i in range(1, 12))
    check("eleven-word list cardinality", len(emitted), 2041)
    check("eleven-word list histogram", histogram, (1, 3, 15, 36, 32, 94, 240, 180, 432, 576, 432))
    check("yes-first reduced words", all(w.startswith("A") and reduced(w) == w for w in emitted), True)
    union = set()
    for base in "ABCD":
        swap = str.maketrans({"A": base, base: "A", "a": base.lower(), base.lower(): "a"})
        union.update(w.translate(swap) for w in emitted)
    check("union under four base swaps", len(union), 8164)
    normalized_keys = {(reduced(t + q), v) for t, q, v in apps}
    print(f"relation ledger: {len(apps)} occurrences, {len(set(apps))} distinct raw keys, "
          f"{len(normalized_keys)} distinct keys after merging the base prefix")
    print(f"eleven-word base list: {len(emitted)}, histogram {histogram}, four-base union {len(union)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_archive", type=Path, help="Hexagon v1 public.zip containing both deposited TeX files")
    parser.add_argument("--negative-control", choices=("vector", "counter", "word"),
                        help="alter the reflected vector, one bucket weight or one far-face word")
    args = parser.parse_args()
    try:
        bind_source(args.source_archive)
        data = replay_traces(paper_atoms())
        norms = replay_gram(data, args.negative_control)
        replay_robust_constants(norms, args.negative_control)
        replay_word_ledger(args.negative_control)
    except (BadZipFile, KeyError, OSError, ValueError) as failure:
        parser.exit(1, f"Replay failed: {failure}\n")
    print("Selected paper certificate calculations passed.")


if __name__ == "__main__":
    main()
