/- SPDX-License-Identifier: Apache-2.0
Descends from the Glennie layer of the Palomar entry PALOMAR-2026-10-16-000013
(https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515; same contributor) through a later version of the
same code; see THIRD_PARTY_NOTICES. -/
module

public import Glennie.Native.AlgebraLaws

/-! Elementary bilinear/trace maps, separated from the cubic-identity code.
Only the definitions and reflexive application lemmas are given. No cubic
residual or Jordan identity theorem is imported or asserted. The separation
removes an incidental computational-cubic dependency from the cone proof. -/

@[expose] public section
noncomputable section
namespace Glennie

def jordanLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert where
  toFun x :=
    { toFun := jordan x
      map_add' := fun y z => jordan_add_right x y z
      map_smul' := fun r y => jordan_smul_right r x y }
  map_add' x y := LinearMap.ext fun z => jordan_add_left x y z
  map_smul' r x := LinearMap.ext fun y => jordan_smul_left r x y

def traceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

@[simp] theorem jordanLinear_apply (x y : Albert) : jordanLinear x y = jordan x y := rfl
@[simp] theorem traceLinear_apply (x : Albert) : traceLinear x = trace x := rfl

end Glennie
