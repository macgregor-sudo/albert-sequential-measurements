#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Audit the transitive axioms of exported declarations in built project modules.

Run from the repository root after lake build. With --negative-control, audit the
published challenge template instead. It must be rejected for its sorryAx.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys


def batch_source(modules, permitted):
    def names(items):
        return "#[" + ", ".join("`" + item for item in items) + "]"

    imports = "\n".join("import " + item for item in modules)
    return f"""import Lean.Util.CollectAxioms
{imports}
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := {names(permitted)}
  let auditModules : Array Name := {names(modules)}
  for modName in auditModules do
    let some idx := env.getModuleIdx? modName | throwError "missing module {{modName}}"
    let decls := env.header.moduleData[idx.toNat]!.constNames
    for decl in decls do
      for ax in ← collectAxioms decl do
        unless allowed.contains ax do
          throwError "forbidden axiom {{ax}} in {{decl}} from {{modName}}"
    logInfo m!"checked {{modName}}: {{decls.size}} exported declarations"
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--negative-control", action="store_true")
    args = parser.parse_args()
    config = json.loads(Path("comparator.json").read_text())
    if args.negative_control:
        modules = [config["challenge_module"]]
    else:
        paths = subprocess.check_output(
            ["git", "ls-tree", "-r", "--name-only", "HEAD", "--", "src"], text=True
        ).splitlines()
        modules = [
            ".".join(Path(path).relative_to("src").with_suffix("").parts)
            for path in paths if path.endswith(".lean")
        ]
        modules.remove(config["challenge_module"])
    for i in range(0, len(modules), 16):
        batch = modules[i:i + 16]
        result = subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            input=batch_source(batch, config["permitted_axioms"]), text=True
        )
        if result.returncode:
            return result.returncode
    if args.negative_control:
        print("The challenge template unexpectedly passed.", file=sys.stderr)
        return 2
    print(f"All {len(modules)} tracked proof and definition modules passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
