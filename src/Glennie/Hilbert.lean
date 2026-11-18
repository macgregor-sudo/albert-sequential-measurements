/- SPDX-License-Identifier: Apache-2.0
Descends from the Glennie layer of the Palomar entry PALOMAR-2026-10-16-000013
(https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515; same contributor) through a later version of the
same code; see THIRD_PARTY_NOTICES. -/
/- The positive native trace form as a real Hilbert space.
Diagonalizing a multiplication operator is not stated here as a Jordan-frame theorem. -/
module
public import Glennie.Native.LinearMaps
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section
namespace Glennie
noncomputable section

def Albert.coordinateLinearEquiv : Albert ≃ₗ[ℝ] Albert.Coordinates where
  __ := Albert.coordinateAddEquiv
  map_smul' _ _ := rfl

instance : FiniteDimensional ℝ Albert :=
  Albert.coordinateLinearEquiv.symm.finiteDimensional

theorem albert_finrank : Module.finrank ℝ Albert = 27 := by
  rw [Albert.coordinateLinearEquiv.finrank_eq]
  simp [Albert.Coordinates, Octonion, Quaternion.finrank_eq_four]

instance : Inner ℝ Albert := ⟨Glennie.inner⟩

@[instance_reducible] def nativeInnerCore : InnerProductSpace.Core ℝ Albert where
  toInner := inferInstance
  conj_inner_symm x y := by
    change inner y x = inner x y
    exact inner_comm y x
  re_inner_nonneg := inner_self_nonneg
  definite x := (inner_self_eq_zero x).mp
  add_left := inner_add_left
  smul_left x y r := by
    change inner (r • x) y = r * inner x y
    exact inner_smul_left r x y

instance : NormedAddCommGroup Albert := nativeInnerCore.toNormedAddCommGroup

instance : InnerProductSpace ℝ Albert :=
  InnerProductSpace.ofCore nativeInnerCore.toCore

theorem hilbert_inner_eq_native (x y : Albert) :
    Inner.inner ℝ x y = Glennie.inner x y := rfl

theorem native_norm_sq (x : Albert) : ‖x‖ ^ 2 = inner x x := by
  exact real_inner_self_eq_norm_sq x |>.symm

end
end Glennie
