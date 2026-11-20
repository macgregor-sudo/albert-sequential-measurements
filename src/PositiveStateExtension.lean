/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Tactic.Linarith

/-! The order-unit Hahn–Banach argument of core Appendix B. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A positive state on a unital self-adjoint real subspace extends to a positive,
normalized functional of norm one on the ambient algebra. -/
theorem positive_state_extension (S : Submodule ℝ A) (he : (1 : A) ∈ S)
    (hsa : ∀ x : S, IsSelfAdjoint (x : A)) (f : S →ₗ[ℝ] ℝ)
    (hp : ∀ x : S, 0 ≤ (x : A) → 0 ≤ f x) (hf : f ⟨1,he⟩ = 1) :
    ∃ g : A →L[ℝ] ℝ, (∀ x : S, g x = f x) ∧ g 1 = 1 ∧
      (∀ x : A, 0 ≤ x → 0 ≤ g x) ∧ ‖g‖ = 1 := by
  let e : S := ⟨1,he⟩
  have hfe : f e = 1 := hf
  have hnorm (x : S) : f x ≤ ‖(x : A)‖ := by
    have h := (hsa x).le_algebraMap_norm_self
    have hx := hp (‖(x : A)‖ • e - x) (by
      change 0 ≤ ‖(x : A)‖ • (1 : A) - (x : A)
      rwa [sub_nonneg, Algebra.smul_def, mul_one])
    simpa [map_sub,map_smul,hfe,sub_nonneg] using hx
  obtain ⟨g,hext,hbound⟩ := Module.Dual.exists_extension_of_le_seminorm_real S f
    (p := normSeminorm ℝ A) hnorm
  have hg (x : A) : ‖g x‖ ≤ 1 * ‖x‖ := by simpa [Real.norm_eq_abs] using hbound x
  let G := g.mkContinuous 1 hg
  have hGe : G 1 = 1 := (hext e).trans hf
  have hGpos (x : A) (hx : 0 ≤ x) : 0 ≤ G x := by
    let y := algebraMap ℝ A ‖x‖ - x
    have hy : 0 ≤ y := sub_nonneg.mpr (IsSelfAdjoint.of_nonneg hx).le_algebraMap_norm_self
    have hle : y ≤ algebraMap ℝ A ‖x‖ := sub_le_self _ hx
    have hny := (CStarAlgebra.norm_le_iff_le_algebraMap y (norm_nonneg x) hy).mpr hle
    have hgy : G y ≤ ‖y‖ := (le_abs_self _).trans (hbound y)
    have hy' : y = ‖x‖ • (1 : A) - x := by simp [y,Algebra.smul_def]
    rw [hy',map_sub,map_smul,hGe,smul_eq_mul,mul_one] at hgy
    rw [hy'] at hny
    linarith
  refine ⟨G,hext,hGe,hGpos,le_antisymm (g.mkContinuous_norm_le zero_le_one hg) ?_⟩
  have h := G.le_opNorm (1 : A)
  rw [hGe, norm_one] at h
  by_cases hA : Nontrivial A
  · simpa using h
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    have hz : (1 : A) = 0 := Subsingleton.elim _ _
    rw [hz, map_zero] at hGe
    norm_num at hGe

end AlbertSequential
