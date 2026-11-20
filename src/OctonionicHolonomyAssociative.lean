/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OctonionicHolonomies
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

public section
noncomputable section

namespace AlbertSequential

private theorem assoc_I_J_snd_zero (z : Octonion) (h : octAssociator octI octJ z = 0) :
    z.2 = 0 := by
  let I : Quaternion ℝ := ⟨0,1,0,0⟩
  let J : Quaternion ℝ := ⟨0,0,1,0⟩
  let K : Quaternion ℝ := ⟨0,0,0,1⟩
  have hz : z.2 * K - (z.2 * J) * I = 0 := by
    have hh := congrArg (fun x : Octonion => x.2) h
    change (octonionMul (octonionMul octI octJ) z).2 -
      (octonionMul octI (octonionMul octJ z)).2 = 0 at hh
    simpa [octonionMul, octI, octJ, I, J, K] using hh
  have hji : J * I = -K := by
    apply Quaternion.ext <;>
      norm_num [J, I, K, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  rw [mul_assoc, hji, mul_neg, sub_neg_eq_add, ← two_smul ℝ] at hz
  have hk : K ≠ 0 := by
    intro he
    have hi := congrArg (fun q : Quaternion ℝ => q.imK) he
    change (1 : ℝ) = 0 at hi
    exact one_ne_zero hi
  exact (mul_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left two_ne_zero)).resolve_right hk

private def backQuaternion (α : OctonionAutomorphism) : Quaternion ℝ →ₗ[ℝ] Octonion :=
  α.symm.equiv.toLinearMap.comp quatEmbed1

private theorem mem_backQuaternion_of_snd_zero (α : OctonionAutomorphism) (z : Octonion)
    (hz : (α.equiv z).2 = 0) : z ∈ Set.range (backQuaternion α) := by
  refine ⟨(α.equiv z).1, ?_⟩
  apply α.equiv.injective
  change α.equiv (α.symm.equiv (quatEmbed1 (α.equiv z).1)) = _
  rw [OctonionAutomorphism.symm_apply, LinearEquiv.apply_symm_apply, quatEmbed1_apply]
  exact Prod.ext rfl hz.symm

theorem octAssociator_imaginary_eq_zero_iff_quaternionic
    (x y z : Octonion) (hx : octonionReal x = 0) (hy : octonionReal y = 0) :
    octAssociator x y z = 0 ↔
      ∃ φ : Quaternion ℝ →ₗ[ℝ] Octonion,
        IsQuatEmbedding φ ∧ x ∈ Set.range φ ∧ y ∈ Set.range φ ∧ z ∈ Set.range φ := by
  refine ⟨?_, ?_⟩
  · intro hass
    by_cases hx0 : x = 0
    · obtain ⟨φ, hφ, hyφ, hzφ⟩ := exists_quatEmbedding_containing_pair y z
      exact ⟨φ, hφ, ⟨0, by rw [map_zero, hx0]⟩, hyφ, hzφ⟩
    obtain ⟨α1,r,_,h1⟩ := exists_octAuto_imag_to_I x hx
    obtain ⟨α2,h2I,s0,s1,s2,_,h2⟩ := exists_octAuto_fix_I_to_IJ (α1.equiv y)
    let α := α2.comp α1
    have hxα : α.equiv x = r • octI := by
      simp only [α, OctonionAutomorphism.comp_apply, h1, map_smul, h2I]
    have hyα : α.equiv y = s0 • octOne + s1 • octI + s2 • octJ := h2
    have hs0 : s0 = 0 := by
      have h := congrArg octonionReal hyα
      rw [α.map_real, hy, octonionReal_add, octonionReal_add, octonionReal_smul,
        octonionReal_smul, octonionReal_smul, octonionReal_one] at h
      change 0 = s0 * 1 + s1 * 0 + s2 * 0 at h
      linarith
    rw [hs0, zero_smul, zero_add] at hyα
    have hr : r ≠ 0 := by
      intro hr'
      apply hx0
      apply α.equiv.injective
      rw [hxα, hr', zero_smul, map_zero]
    by_cases hs2 : s2 = 0
    · obtain ⟨φ, hφ, ⟨a, ha⟩, hzφ⟩ := exists_quatEmbedding_containing_pair x z
      have hyx : y = (s1/r) • x := by
        apply α.equiv.injective
        rw [map_smul, hxα, hyα, hs2, zero_smul, add_zero, smul_smul, div_mul_cancel₀ _ hr]
      exact ⟨φ, hφ, ⟨a, ha⟩, ⟨(s1/r) • a, by rw [map_smul, ha, ← hyx]⟩, hzφ⟩
    have hasα : octAssociator (α.equiv x) (α.equiv y) (α.equiv z) = 0 := by
      rw [← α.map_associator, hass, map_zero]
    rw [hxα, hyα, octAssociator_smul_left, octAssociator_add_mid, octAssociator_smul_mid,
      octAssociator_smul_mid, octAssociator_self_left, smul_zero, zero_add, smul_smul] at hasα
    have hz0 := assoc_I_J_snd_zero _ ((smul_eq_zero.mp hasα).resolve_left (mul_ne_zero hr hs2))
    refine ⟨backQuaternion α, octonionAutomorphism_comp_isQuatEmbedding α.symm quatEmbed1_isQuatEmbedding,
      mem_backQuaternion_of_snd_zero α x ?_, mem_backQuaternion_of_snd_zero α y ?_,
      mem_backQuaternion_of_snd_zero α z hz0⟩
    · rw [hxα]
      change r • (0 : Quaternion ℝ) = 0
      simp
    · rw [hyα]
      change s1 • (0 : Quaternion ℝ) + s2 • (0 : Quaternion ℝ) = 0
      simp
  · rintro ⟨φ, hφ, h₁, h₂, h₃⟩
    exact octAssociator_eq_zero_of_quatEmbedding φ hφ h₁ h₂ h₃

theorem OctonionicHolonomyData.determinant_zero_iff_quaternionic
    {q : Fin 4 → Albert} {h : Fin 3 → Octonion} (H : OctonionicHolonomyData q h) :
    MatchingModels.Dtet (fpOverlap q) (fpTriangle q) (MatchingModels.tVec q) = 0 ↔
      ∃ φ : Quaternion ℝ →ₗ[ℝ] Octonion,
        IsQuatEmbedding φ ∧ ∀ i, octIm (h i) ∈ Set.range φ := by
  rw [H.determinant_imaginary, mul_eq_zero, or_iff_right (by norm_num : (1/4 : ℝ) ≠ 0),
    octNormSq_eq_zero, octAssociator_imaginary_eq_zero_iff_quaternionic _ _ _
      (octonionReal_octIm _) (octonionReal_octIm _)]
  constructor
  · rintro ⟨φ,hφ,h₁,h₂,h₃⟩
    refine ⟨φ,hφ,?_⟩
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
    · exact h₃
  · rintro ⟨φ,hφ,hφs⟩
    exact ⟨φ,hφ,hφs 0,hφs 1,hφs 2⟩

end AlbertSequential
