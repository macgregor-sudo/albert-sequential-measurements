/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Ring.Parity

@[expose] public section

namespace AlbertSequential

open Submodule

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private def hyperplaneReflection (v : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ v)ᗮ.reflection

omit [FiniteDimensional ℝ E] in
private theorem normalizeNormals (L : List E) :
    ∃ N : List E, (∀ v ∈ N, ‖v‖ = 1) ∧ N.length ≤ L.length ∧
      (N.map hyperplaneReflection).prod = (L.map hyperplaneReflection).prod := by
  induction L with
  | nil => exact ⟨[], by simp, le_rfl, rfl⟩
  | cons v tail ih =>
    obtain ⟨N,hN,hl,he⟩ := ih
    by_cases hv : v = 0
    · subst v
      have hz : hyperplaneReflection (0 : E) = 1 := by
        ext x
        apply Submodule.reflection_mem_subspace_eq_self
        simp
      exact ⟨N,hN,hl.trans (Nat.le_succ _),by simp [hz,he]⟩
    · let w := ‖v‖⁻¹ • v
      have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
      have heq : hyperplaneReflection w = hyperplaneReflection v := by
        simp only [hyperplaneReflection,w,span_singleton_smul_eq (inv_ne_zero (norm_ne_zero_iff.mpr hv)).isUnit]
      exact ⟨w :: N,by simpa only [List.forall_mem_cons] using And.intro hw hN,
        Nat.succ_le_succ hl,by simp [he,heq]⟩

private theorem normalsDet (N : List E) (hN : ∀ v ∈ N, ‖v‖ = 1) :
    LinearMap.det (N.map hyperplaneReflection).prod.toLinearMap = (-1 : ℝ)^N.length := by
  induction N with
  | nil => change LinearMap.det (LinearMap.id : E →ₗ[ℝ] E) = (-1 : ℝ)^0; simp
  | cons v tail ih =>
    have hv : v ≠ 0 := by
      have := hN v (by simp)
      rintro rfl; simp at this
    have hd : LinearMap.det (hyperplaneReflection v).toLinearMap = -1 := by
      have hperp : ((ℝ ∙ v)ᗮ : Submodule ℝ E)ᗮ = ℝ ∙ v := Submodule.orthogonal_orthogonal _
      rw [hyperplaneReflection, Submodule.det_reflection, hperp, finrank_span_singleton hv, pow_one]
    change LinearMap.det ((hyperplaneReflection v).toLinearMap.comp
      (tail.map hyperplaneReflection).prod.toLinearMap) = _
    rw [LinearMap.det_comp,hd,ih (fun x hx => hN x (List.mem_cons_of_mem _ hx)),
      List.length_cons,pow_succ,mul_comm]

/-- Every oriented Euclidean isometry, in particular every element of SO(9),
is a product of an even number of unit-normal hyperplane reflections. -/
theorem exists_even_unit_reflections (g : E ≃ₗᵢ[ℝ] E) (hg : LinearMap.det g.toLinearMap = 1) :
    ∃ N : List E, (∀ v ∈ N, ‖v‖ = 1) ∧ Even N.length ∧ N.length ≤ Module.finrank ℝ E ∧
      g = (N.map (fun v => (ℝ ∙ v)ᗮ.reflection)).prod := by
  obtain ⟨L,hL,he⟩ := g.reflections_generate_dim
  obtain ⟨N,hN,hl,hn⟩ := normalizeNormals L
  have hgN : g = (N.map hyperplaneReflection).prod := he.trans hn.symm
  have hdet := normalsDet N hN
  rw [← hgN,hg] at hdet
  exact ⟨N,hN,(neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hdet.symm,
    hl.trans hL,hgN⟩

end

end AlbertSequential
