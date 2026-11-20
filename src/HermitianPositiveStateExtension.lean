/- SPDX-License-Identifier: Apache-2.0 -/
module
public import PositiveStateExtension
public import JordanOperatorTables
public import ExplicitJordanState
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-! A norm-one positive Hahn–Banach extension is represented on *all* Hermitian matrices by a density. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable (d : ℕ)
local notation "M" => Matrix (Fin d) (Fin d) ℂ
local notation "Eucl" => EuclideanSpace ℂ (Fin d)
local notation "A" => HilbertOperatorAlgebra ℂ Eucl
local notation "P" => selfAdjointOperatorJordanProduct (H := Eucl)

private abbrev matrixOpEquiv := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)

private def fullMatrixEmbedding : FaithfulHermitianJordanEmbedding P d where
  map := ((matrixOpEquiv d).symm.toAlgEquiv.toLinearMap.restrictScalars ℝ).comp
    (selfAdjointOperatorInclusion (H := Eucl))
  injective := (matrixOpEquiv d).symm.injective.comp Subtype.val_injective
  hermitian x := by
    change star ((matrixOpEquiv d).symm x.val) = _
    have hx : star (x.val : Eucl →L[ℂ] Eucl) = x.val := x.property
    exact ((matrixOpEquiv d).symm.map_star' (x.val : Eucl →L[ℂ] Eucl)).symm.trans (congrArg (matrixOpEquiv d).symm hx)
  unit := (matrixOpEquiv d).symm.map_one
  jordan x y := by
    let L := (matrixOpEquiv d).symm.toAlgEquiv.toLinearMap.restrictScalars ℝ
    let X : Eucl →L[ℂ] Eucl := x.val
    let Y : Eucl →L[ℂ] Eucl := y.val
    change L ((1/2 : ℝ) • (X*Y+Y*X)) = (1/2 : ℝ) • (L X * L Y + L Y * L X)
    rw [L.map_smul, L.map_add]
    change (1/2 : ℝ) • ((matrixOpEquiv d).symm (X*Y) + (matrixOpEquiv d).symm (Y*X)) = _
    rw [map_mul,map_mul]
    rfl

theorem positive_state_extension_density (S : Submodule ℝ M) (he : (1 : M) ∈ S)
    (hsa : ∀ x : S, IsSelfAdjoint (x : M)) (f : S →ₗ[ℝ] ℝ)
    (hp : ∀ x : S, 0 ≤ (x : M) → 0 ≤ f x) (hf : f ⟨1,he⟩ = 1) :
    ∃ (G : M →L[ℝ] ℝ) (σ : M), (∀ x : S, G x = f x) ∧ G 1 = 1 ∧
      (∀ x : M, 0 ≤ x → 0 ≤ G x) ∧ ‖G‖ = 1 ∧ σ.PosSemidef ∧ σ.trace = 1 ∧
      ∀ x : M, x.IsHermitian → (σ * x).trace = (G x : ℂ) := by
  obtain ⟨G,hGS,heG,hG,hGN⟩ := positive_state_extension S he hsa f hp hf
  let ι := fullMatrixEmbedding d
  let g := G.toLinearMap.comp ι.map
  have hpos (x : selfAdjoint A) : 0 ≤ g ((P).product x x) := by
    apply hG
    rw [ι.jordan]
    have hs : (1/2 : ℝ) • (ι.map x * ι.map x + ι.map x * ι.map x) = star (ι.map x) * ι.map x := by
      rw [show star (ι.map x) = ι.map x from (ι.hermitian x).eq]
      module
    rw [hs]
    exact star_mul_self_nonneg _
  have hunit : g (P).unit = 1 := by change G (ι.map (P).unit) = 1; rw [ι.unit,heG]
  obtain ⟨z,⟨hz,ht,hall⟩,_⟩ := ι.exists_unique_positive_trace_representative g hpos hunit
  refine ⟨G,ι.map z,hGS,heG,hG,hGN,hz,ht,?_⟩
  intro X hX
  let x : selfAdjoint A := ⟨matrixOpEquiv d X, by
    change star (matrixOpEquiv d X) = _
    exact (map_star (matrixOpEquiv d) X).symm.trans (congrArg (matrixOpEquiv d) hX.eq)⟩
  have hx : ι.map x = X := (matrixOpEquiv d).symm_apply_apply X
  rw [← hx,ι.complex_traceForm]
  exact congrArg Complex.ofReal (hall x)

end AlbertSequential
