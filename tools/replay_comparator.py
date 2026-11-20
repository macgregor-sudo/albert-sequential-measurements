#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Replay the tagged Comparator target on exports produced by the local pinned build."""
import os
import argparse
import json
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("output", type=Path, help="Directory for fresh exports and checker logs.")
args = parser.parse_args()
repo = Path(__file__).resolve().parents[1]
output = args.output.resolve()
output.mkdir(parents=True, exist_ok=True)
os.chdir(repo)
config = json.loads((repo / "comparator.json").read_text())
names = config["theorem_names"]
roots = ("Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub "
         "Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor "
         "Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String "
         "String.mk Char optParam autoParam semiOutParam outParam").split()
toolchain = Path(subprocess.check_output(["lean","--print-prefix"], text=True).strip())
os.environ["PATH"] = str(toolchain / "bin") + os.pathsep + os.environ["PATH"]
for module in ("Challenge", "Solution"):
    with (output / (module + ".export")).open("wb") as receipt:
        subprocess.run(["lake", "env", "leanexport", module, "--", *roots, *names],
                       stdout=receipt, check=True)
axioms = "import Solution\n" + "\n".join("#print axioms " + name for name in names)
result = subprocess.run(["lake", "env", "lean", "--stdin"], text=True, input=axioms,
                        capture_output=True, check=True)
(output / "twelve-axioms.log").write_text(result.stdout)
assert all(name in result.stdout for name in names)
for label, solution, expected in [("positive","Solution",True),("negative","Challenge",False)]:
    proc = subprocess.run(["lake", "comparator", "--config", "comparator.json",
                           "--challenge-from-export", str(output / "Challenge.export"),
                           "--solution-from-export", str(output / (solution + ".export"))],
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / (label + ".log")).write_text(proc.stdout)
    if (proc.returncode == 0) != expected:
        raise RuntimeError(f"{label} control unexpected status {proc.returncode}")
    if not expected and "sorryAx" not in proc.stdout:
        raise RuntimeError("negative control failed for an unexpected reason")
    print(label, proc.returncode, flush=True)
