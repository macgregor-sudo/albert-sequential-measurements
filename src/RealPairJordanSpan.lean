/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealPairJordanBlock
import Mathlib.Tactic.FieldSimp
import ThreeAtomAndFourPoint

public section
noncomputable section

namespace AlbertSequential

theorem generatedPair_eq_span_of_distinct_nonorthogonal (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (hne : p ≠ q) (hoverlap : 0 < tracePairing p q) :
    (generatedSubalgebra ({p, q} : Set Albert)).carrier =
      Submodule.span ℝ ({albertUnit, p, q, jordanMul p q} : Set Albert) := by
  obtain ⟨g,a,b,c,_,hb,hc,_,_,hp',hq',hB⟩ := realPairBlock_normal_generated p q hp hq hne hoverlap
  let B := generatedSubalgebra ({p,q} : Set Albert)
  let S : Set Albert := {albertUnit, p, q, jordanMul p q}
  have hpB : p ∈ B.carrier := subset_generatedSubalgebra _ (by simp)
  have hqB : q ∈ B.carrier := subset_generatedSubalgebra _ (by simp)
  have hd : diagAtom 0 = realPairBlockElement ![1,0,0,0] := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp [diagAtom, realPairBlockElement, octonionScalar_zero]
  have hgpq : g.linearEquiv (jordanMul p q) = realPairBlockElement ![a,0,0,c/2] := by
    rw [g.preserves_product, hp', hq', hd, realPairBlock_product]
    congr 1
    funext i
    fin_cases i <;> simp [realPairBlockProduct, div_eq_mul_inv, mul_comm]
  have hunit : albertUnit = realPairBlockElement ![1,1,1,0] := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  change B.carrier = Submodule.span ℝ S
  apply le_antisymm
  · intro x hx
    have hmem := map_mem_generated_pair g p q x hx
    rw [hB] at hmem
    obtain ⟨v,hv⟩ := (mem_realPairBlock_iff _).mp hmem
    let A : ℝ := v 2
    let C : ℝ := (v 1 - A) / b
    let D : ℝ := 2 * (v 3 - c*C) / c
    let B' : ℝ := v 0 - A - a*C - a*D
    have hvec : v =
        A • (![1,1,1,0] : RealPairCoordinates) + B' • ![1,0,0,0] +
          C • ![a,b,0,c] + D • ![a,0,0,c/2] := by
      funext i
      fin_cases i <;> simp [A, B', C, D] <;> field_simp <;> ring
    have heq : x = A • albertUnit + B' • p + C • q + D • jordanMul p q := by
      apply g.linearEquiv.injective
      simp only [map_add, map_smul, g.preserves_unit, hp', hq', hgpq, hd]
      rw [hunit]
      rw [← hv]
      conv_lhs => rw [hvec]
      simp only [map_add, map_smul, realPairBlockLinear_apply]
    rw [heq]
    apply Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
    all_goals apply Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact B.unit_mem
    · exact hpB
    · exact hqB
    · exact B.product_mem _ hpB _ hqB

private theorem span_closed_under_jordanMul (S : Set Albert)
    (h : ∀ x ∈ S, ∀ y ∈ S, jordanMul x y ∈ Submodule.span ℝ S)
    {x y : Albert} (hx : x ∈ Submodule.span ℝ S) (hy : y ∈ Submodule.span ℝ S) :
    jordanMul x y ∈ Submodule.span ℝ S := by
  let V := Submodule.span ℝ S
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => rw [jordanMul_zero_right]; exact V.zero_mem
    | add y z _ _ iy iz => rw [jordanMul_add_right]; exact V.add_mem iy iz
    | smul a y _ iy => rw [jordanMul_smul_right]; exact V.smul_mem a iy
  | zero => rw [jordanMul_zero_left]; exact V.zero_mem
  | add x z _ _ ix iz => rw [jordanMul_add_left]; exact V.add_mem ix iz
  | smul a x _ ix => rw [jordanMul_smul_left]; exact V.smul_mem a ix

private theorem generatedPair_eq_span_of_product_mem (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (hm : jordanMul p q ∈ Submodule.span ℝ ({albertUnit, p, q} : Set Albert)) :
    (generatedSubalgebra ({p, q} : Set Albert)).carrier =
      Submodule.span ℝ ({albertUnit, p, q, jordanMul p q} : Set Albert) := by
  let S : Set Albert := {albertUnit, p, q}
  let V := Submodule.span ℝ S
  have heV : albertUnit ∈ V := Submodule.subset_span (by simp [S])
  have hpV : p ∈ V := Submodule.subset_span (by simp [S])
  have hqV : q ∈ V := Submodule.subset_span (by simp [S])
  let B : NativeJordanSubalgebra :=
    { carrier := V
      unit_mem := heV
      product_mem := by
        intro x hx y hy
        apply span_closed_under_jordanMul S _ hx hy
        intro a ha b hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        all_goals first
          | rwa [jordanMul_albertUnit_left]
          | rwa [jordanMul_albertUnit_right]
          | rw [hp.1]; exact hpV
          | rw [hq.1]; exact hqV
          | exact hm
          | rw [jordanMul_comm]; exact hm }
  apply le_antisymm
  · have hgen : generatedSubalgebra ({p,q} : Set Albert) ≤ B := by
      apply generatedSubalgebra_le
      intro x hx
      rcases hx with rfl | rfl <;> assumption
    intro x hx
    exact Submodule.span_mono (by simp [S, Set.insert_subset_iff]) (hgen hx)
  · apply Submodule.span_le.mpr
    intro x hx
    let G := generatedSubalgebra ({p, q} : Set Albert)
    have hpG : p ∈ G.carrier := subset_generatedSubalgebra _ (by simp)
    have hqG : q ∈ G.carrier := subset_generatedSubalgebra _ (by simp)
    rcases hx with rfl | rfl | rfl | rfl
    · exact G.unit_mem
    · exact hpG
    · exact hqG
    · exact G.product_mem _ hpG _ hqG

/-- The actual generated pair carrier, including coincident and orthogonal pairs. -/
theorem generatedPair_eq_span (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    (generatedSubalgebra ({p, q} : Set Albert)).carrier =
      Submodule.span ℝ ({albertUnit, p, q, jordanMul p q} : Set Albert) := by
  by_cases he : p = q
  · subst q
    apply generatedPair_eq_span_of_product_mem _ _ hp hp
    rw [hp.1]
    exact Submodule.subset_span (by simp)
  by_cases ho : 0 < tracePairing p q
  · exact generatedPair_eq_span_of_distinct_nonorthogonal p q hp hq he ho
  · apply generatedPair_eq_span_of_product_mem p q hp hq
    have hz : tracePairing p q = 0 := le_antisymm (le_of_not_gt ho) (atom_tracePairing_bounds p q hp hq).1
    rw [(atom_tracePairing_eq_zero_iff p q hp hq).mp hz]
    exact Submodule.zero_mem _

theorem generatedSingleAtom_eq_span (p : Albert) (hp : IsAtom p) :
    (generatedSubalgebra ({p} : Set Albert)).carrier =
      Submodule.span ℝ ({p, albertUnit - p} : Set Albert) := by
  have h := generatedPair_eq_span p p hp hp
  have hd : ({p,p} : Set Albert) = {p} := by ext x; simp
  have hs : ({albertUnit,p,p} : Set Albert) = {albertUnit,p} := by ext x; simp
  rw [hp.1, hd, hs] at h
  rw [h]
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · intro x hx
    rcases hx with rfl | rfl
    · let V := Submodule.span ℝ ({p, albertUnit - p} : Set Albert)
      have h₁ : p ∈ V := Submodule.subset_span (by simp)
      have h₂ : albertUnit - p ∈ V := Submodule.subset_span (by simp)
      have hv := V.add_mem h₁ h₂
      rw [show p + (albertUnit - p) = albertUnit by abel] at hv
      exact hv
    · exact Submodule.subset_span (by simp)
  · intro x hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · apply Submodule.sub_mem _ <;> apply Submodule.subset_span <;> simp

end AlbertSequential
