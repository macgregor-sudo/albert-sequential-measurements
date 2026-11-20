/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanCubicCritical
public import EuclideanJordanSquareCone
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! The unit is an interior point of the actual square cone, core §3. -/
@[expose] public section
noncomputable section
open scoped Topology
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

theorem unit_mem_interior_squareCone : P.unit ∈ interior P.squareCone := by
  let sq (x : E) := P.product x x
  let L : E →L[ℝ] E := (2 : ℝ) • ContinuousLinearMap.id ℝ E
  have hd : HasStrictFDerivAt sq L P.unit := by
    have h := P.continuousProduct.hasStrictFDerivAt_of_bilinear
      (hasStrictFDerivAt_id P.unit) (hasStrictFDerivAt_id P.unit)
    convert h using 1
    · rfl
    · ext x
      change (2 : ℝ) • x = P.product P.unit x + P.product x P.unit
      rw [P.commutative x P.unit,P.unit_left,two_smul]
  have hsur : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    refine ⟨(1/2 : ℝ) • y,?_⟩
    change (2 : ℝ) • (1/2 : ℝ) • y = y
    rw [smul_smul]
    norm_num
  have hm := hd.map_nhds_eq_of_surj hsur
  have he : sq P.unit = P.unit := P.unit_left _
  rw [he] at hm
  rw [mem_interior_iff_mem_nhds,← hm]
  change sq ⁻¹' P.squareCone ∈ 𝓝 P.unit
  exact Filter.mem_of_superset Filter.univ_mem (fun x _ => ⟨x,rfl⟩)

end AlbertSequential.UnitalJordanProduct
