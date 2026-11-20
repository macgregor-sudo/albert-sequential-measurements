#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Parse the deposited eleven-word tail table and compare its codes to Lean."""
import argparse
from itertools import permutations, product
from pathlib import Path
import re
from zipfile import ZipFile

from replay_paper_certificates import bind_source

SOURCE = "companion/macgregor-finite-certificates.tex"
MODULE = Path(__file__).resolve().parents[1] / "src/Ends/PrintedElevenList.lean"
START = "-- BEGIN deposited word codes"
END = "-- END deposited word codes"


def word_code(word):
    value = 0
    for letter in reversed(word):
        value = 9 * value + 1 + 2 * "ABCD".index(letter.upper()) + int(letter.isupper())
    return value


def expand(pattern, orientation):
    if pattern == r"\varnothing":
        return {""}
    pattern = re.sub(r"\s+", "", pattern.replace(r"\,", ""))
    tokens = re.findall(r"(?:\\bar|\\sigma|\\tau)?[jxyz]", pattern)
    if "".join(tokens) != pattern:
        raise ValueError(f"unread tail {pattern!r}")
    result = set()
    for x, y, z in permutations("BCD"):
        if orientation and (x + y in {"BC", "CD", "DB"}) != (orientation == "E"):
            continue
        for sigma, tau in product([True, False], repeat=2):
            word = ""
            for token in tokens:
                letter = dict(j="A", x=x, y=y, z=z)[token[-1]]
                negative = (token.startswith(r"\bar") or
                            (token.startswith(r"\sigma") and not sigma) or
                            (token.startswith(r"\tau") and not tau))
                word += letter.lower() if negative else letter
            result.add(word)
    return result


def source_codes(tex):
    section = tex.split(r"\subsection{The eleven-step list}", 1)[1]
    assert r"H_d=\{jx_1y_1j\cdots x_dy_dj:x_i,y_i\in X,\ x_i\ne y_i\}" in section
    pairs = list(permutations("BCD", 2))
    prefixes = {"A"}
    prefixes1 = {"A" + x + y + "A" for x, y in pairs}
    prefixes2 = {u + x + y + "A" for u in prefixes1 for x, y in pairs}
    families = {"B": set(), "D": set()}
    table = section.split(r"\label{tab:cer:tails}", 1)[1].split(r"\end{tabular}", 1)[0]
    family = None
    for line in table.splitlines():
        row = re.fullmatch(r"(.*?)&\$(\d)\$&(.*?)&\$(\d+)\$\\\\(?:\\midrule|\\bottomrule)?", line)
        if not row:
            continue
        label, length, body, size = row.groups()
        if label:
            family = re.fullmatch(r"\$\\mathcal ([BD])\$", label).group(1)
        words = set()
        for clause in body.replace(r"\ ", " ").split(";"):
            terms, _, condition = clause.partition(" with ")
            orientation = None
            if condition:
                orientation = {r"$(x,y)\in E$": "E", r"$(x,y)\in E^{\rm op}$": "op"}[condition.strip()]
            for formula in terms.split(" and "):
                words.update(expand(formula.strip().strip("$"), orientation))
        assert len(words) == int(size) and all(len(w) == int(length) for w in words)
        families[family].update(words)
    far_body = section.split(r"\mathcal F_{\rm far}=\{", 1)[1].split(r"\}", 1)[0]
    far = {w.replace(r"\bar l", "c").translate(str.maketrans("jklm", "ABCD")) for w in
           (entry.replace(r"\ ", "").strip() for entry in far_body.split(","))}
    assert (len(families["B"]), len(families["D"]), len(far)) == (40, 57, 6)
    groups = dict(prefix01=prefixes | prefixes1, prefix012=prefixes | prefixes1 | prefixes2,
                  tailB=families["B"], tailD=families["D"], farFace=far)
    return "\n".join("def " + name + "Codes : List ℕ :=\n  [" +
                     ", ".join(str(n) for n in sorted(map(word_code, words))) + "]"
                     for name, words in groups.items())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_archive", type=Path)
    args = parser.parse_args()
    bind_source(args.source_archive)
    with ZipFile(args.source_archive) as archive:
        block = source_codes(archive.read(SOURCE).decode())
    saved = MODULE.read_text().split(START + "\n", 1)[1].split("\n" + END, 1)[0]
    if block != saved:
        raise SystemExit("published prefixes, tails or far faces differ from Lean")
    print("Both prefix families, all 97 tabulated tails and the six far-face words agree.")


if __name__ == "__main__":
    main()
