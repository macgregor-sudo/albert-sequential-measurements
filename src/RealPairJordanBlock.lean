/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SubalgebraCoordsAndLine
public import AppF.ExactModel
import ThreeAtomAndFourPoint

public section
noncomputable section

namespace AlbertSequential

private theorem pair_add_diagonal (x y : Albert) (i : Fin 3) : (x+y).1 i = x.1 i + y.1 i := rfl
private theorem pair_add_upper (x y : Albert) (i : Fin 3) : (x+y).2 i = x.2 i + y.2 i := rfl
private theorem pair_smul_diagonal (r : ℝ) (x : Albert) (i : Fin 3) : (r • x).1 i = r * x.1 i := rfl
private theorem pair_smul_upper (r : ℝ) (x : Albert) (i : Fin 3) : (r • x).2 i = r • x.2 i := rfl
private theorem pair_slot_diagonal (v : Octonion) (i : Fin 3) : (slotElem01 v).1 i = 0 := rfl
private theorem pair_slot_upper0 (v : Octonion) : (slotElem01 v).2 0 = v := rfl
private theorem pair_slot_upper1 (v : Octonion) : (slotElem01 v).2 1 = 0 := rfl
private theorem pair_slot_upper2 (v : Octonion) : (slotElem01 v).2 2 = 0 := rfl

attribute [local simp] pair_add_diagonal pair_add_upper pair_smul_diagonal pair_smul_upper
  pair_slot_diagonal pair_slot_upper0 pair_slot_upper1 pair_slot_upper2 octonionScalar_zero

/-- Coordinates `(a,b,c,d)` for `ℝ ⊕ H₂(ℝ)`, where `c` is the scalar
summand and the symmetric block is `[[a,d],[d,b]]`. -/
abbrev RealPairCoordinates := Fin 4 → ℝ

@[expose] def realPairBlockElement (x : RealPairCoordinates) : Albert :=
  (![x 0,x 1,x 2], ![octonionScalar (x 3),0,0])

@[expose] def realPairBlockProduct (x y : RealPairCoordinates) : RealPairCoordinates :=
  ![x 0 * y 0 + x 3 * y 3, x 1 * y 1 + x 3 * y 3, x 2 * y 2,
    (1 / 2) * ((x 0 + x 1) * y 3 + (y 0 + y 1) * x 3)]

def realPairBlockLinear : RealPairCoordinates →ₗ[ℝ] Albert where
  toFun := realPairBlockElement
  map_add' x y := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i
      · exact octonionScalar_add _ _
      · exact (add_zero (0 : Octonion)).symm
      · exact (add_zero (0 : Octonion)).symm
  map_smul' r x := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i
      · exact octonionScalar_smul _ _
      · exact (smul_zero r).symm
      · exact (smul_zero r).symm

@[simp] theorem realPairBlockLinear_apply (x : RealPairCoordinates) :
    realPairBlockLinear x = realPairBlockElement x := by
  unfold realPairBlockLinear
  rfl

theorem realPairBlockLinear_injective : Function.Injective realPairBlockLinear := by
  intro x y h
  funext i
  fin_cases i
  · exact congrArg (fun z : Albert => z.1 0) h
  · exact congrArg (fun z : Albert => z.1 1) h
  · exact congrArg (fun z : Albert => z.1 2) h
  · exact congrArg (fun z : Albert => octonionReal (z.2 0)) h

set_option linter.unusedSimpArgs false in
theorem realPairBlock_product (x y : RealPairCoordinates) :
    jordanMul (realPairBlockElement x) (realPairBlockElement y) =
      realPairBlockElement (realPairBlockProduct x y) := by
  have hmul (a b : ℝ) : octonionMul (octonionScalar a) (octonionScalar b) =
      octonionScalar (a*b) := by
    rw [octonionMul_scalar_left, ← octonionScalar_smul]
  apply Prod.ext
  · funext i
    rw [AppF.jordanMul_fst']
    fin_cases i <;>
      simp [realPairBlockElement, realPairBlockProduct, octonionMatrixMul,
        Fin.sum_univ_three, albertMatrix, octonionConj_scalar, octonionConj_zero,
        octonionMul_zero_left, octonionMul_zero_right, octonionReal_add, octonionReal_scalar, hmul] <;> ring
  · funext i
    fin_cases i
    all_goals first
      | change (jordanMul (realPairBlockElement x) (realPairBlockElement y)).2 0 = _
        rw [AppF.jordanMul_snd0']
      | change (jordanMul (realPairBlockElement x) (realPairBlockElement y)).2 1 = _
        rw [AppF.jordanMul_snd1']
      | change (jordanMul (realPairBlockElement x) (realPairBlockElement y)).2 2 = _
        rw [AppF.jordanMul_snd2']
    all_goals simp [realPairBlockElement,
        realPairBlockProduct, octonionMatrixMul, Fin.sum_univ_three, albertMatrix, octonionConj_scalar,
        octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right, hmul,
        ← octonionScalar_add, ← octonionScalar_smul]
    congr 1
    ring

def realPairBlock : NativeJordanSubalgebra where
  carrier := LinearMap.range realPairBlockLinear
  unit_mem := ⟨![1,1,1,0], by apply Prod.ext <;> funext i <;> fin_cases i <;> rfl⟩
  product_mem x hx y hy := by
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨realPairBlockProduct a b, (realPairBlock_product a b).symm⟩

def realPairBlockEquiv : RealPairCoordinates ≃ₗ[ℝ] realPairBlock.carrier :=
  LinearEquiv.ofInjective realPairBlockLinear realPairBlockLinear_injective

theorem mem_realPairBlock_iff (x : Albert) :
    x ∈ realPairBlock.carrier ↔ ∃ v : RealPairCoordinates, realPairBlockLinear v = x := Iff.rfl

theorem realPairBlockProduct_matrix (x y : RealPairCoordinates) :
    let B (v : RealPairCoordinates) : Matrix (Fin 2) (Fin 2) ℝ := !![v 0,v 3;v 3,v 1]
    B (realPairBlockProduct x y) = (1 / 2 : ℝ) • (B x * B y + B y * B x) ∧
      realPairBlockProduct x y 2 = x 2 * y 2 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realPairBlockProduct] <;> ring
  · rfl

/-- The real symmetric two-by-two matrices appearing in the pair algebra. -/
def realPairSymmetric2 : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) where
  carrier := {A | A.transpose = A}
  zero_mem' := Matrix.transpose_zero
  add_mem' {A B} hA hB := by
    change A.transpose = A at hA
    change B.transpose = B at hB
    change (A+B).transpose = A+B
    rw [Matrix.transpose_add, hA, hB]
  smul_mem' a A hA := by
    change A.transpose = A at hA
    change (a • A).transpose = a • A
    rw [Matrix.transpose_smul, hA]

def realPairProductEquiv : RealPairCoordinates ≃ₗ[ℝ] ℝ × realPairSymmetric2 where
  toFun x := (x 2, ⟨!![x 0,x 3;x 3,x 1], by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩)
  invFun z := ![z.2.1 0 0,z.2.1 1 1,z.1,z.2.1 0 1]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> try rfl
      exact congrFun (congrFun z.2.2 1) 0
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> rfl

theorem realPairProductEquiv_product (x y : RealPairCoordinates) :
    (realPairProductEquiv (realPairBlockProduct x y)).1 =
      (realPairProductEquiv x).1 * (realPairProductEquiv y).1 ∧
    (realPairProductEquiv (realPairBlockProduct x y)).2.1 =
      (1 / 2 : ℝ) • ((realPairProductEquiv x).2.1 * (realPairProductEquiv y).2.1 +
        (realPairProductEquiv y).2.1 * (realPairProductEquiv x).2.1) := by
  exact And.symm (realPairBlockProduct_matrix x y)

set_option linter.unusedSimpArgs false in
theorem realPairBlock_standard_generated (a b c : ℝ) (hc : c ≠ 0) :
    generatedSubalgebra ({diagAtom 0, realPairBlockElement ![a,b,0,c]} : Set Albert) =
      realPairBlock := by
  let p := diagAtom 0
  let q := realPairBlockElement ![a,b,0,c]
  let e1 := diagAtom 1
  let e2 := diagAtom 2
  let s := realPairBlockElement ![0,0,0,1]
  let B := generatedSubalgebra ({p,q} : Set Albert)
  have hpE : p = realPairBlockLinear ![1,0,0,0] := by
    change diagAtom 0 = realPairBlockElement ![1,0,0,0]
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp [diagAtom, realPairBlockElement]
  have hqE : q = realPairBlockLinear ![a,b,0,c] := rfl
  have hp : p ∈ B.carrier := subset_generatedSubalgebra _ (by simp)
  have hq : q ∈ B.carrier := subset_generatedSubalgebra _ (by simp)
  have hJ : jordanMul p q = a • p + (c / 2) • s := by
    conv_lhs => rw [hpE, hqE]
    change jordanMul (realPairBlockElement ![1,0,0,0]) (realPairBlockElement ![a,b,0,c]) = _
    rw [realPairBlock_product]
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp only [pair_add_diagonal, pair_add_upper, pair_smul_diagonal, pair_smul_upper] <;>
      simp [p, s, realPairBlockElement, realPairBlockProduct, diagAtom,
        ← octonionScalar_smul, div_eq_mul_inv, mul_comm]
  have hs : s ∈ B.carrier := by
    have he := B.carrier.sub_mem (B.product_mem p hp q hq) (B.carrier.smul_mem a hp)
    rw [hJ, add_sub_cancel_left] at he
    have he' := B.carrier.smul_mem (c / 2)⁻¹ he
    rwa [smul_smul, inv_mul_cancel₀ (div_ne_zero hc (by norm_num)), one_smul] at he'
  have hs2 : jordanMul s s = p + e1 := by
    change jordanMul (realPairBlockElement ![0,0,0,1]) (realPairBlockElement ![0,0,0,1]) = _
    rw [realPairBlock_product]
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp only [pair_add_diagonal, pair_add_upper] <;>
      simp [p, e1, realPairBlockElement, realPairBlockProduct, diagAtom]
  have he1 : e1 ∈ B.carrier := by
    have he := B.carrier.sub_mem (B.product_mem s hs s hs) hp
    rwa [hs2, add_sub_cancel_left] at he
  have he2 : e2 ∈ B.carrier := by
    have he := B.carrier.sub_mem (B.carrier.sub_mem B.unit_mem hp) he1
    have hu : albertUnit = p + e1 + e2 := by
      simpa [Fin.sum_univ_three, p, e1, e2] using diagAtom_sum_eq_unit.symm
    rwa [hu, add_assoc, add_sub_cancel_left, add_sub_cancel_left] at he
  change B = realPairBlock
  apply le_antisymm
  · apply generatedSubalgebra_le
    rintro x (rfl | rfl)
    · exact ⟨![1,0,0,0], hpE.symm⟩
    · exact ⟨![a,b,0,c], hqE.symm⟩
  · intro x hx
    obtain ⟨v, rfl⟩ := hx
    have he : realPairBlockLinear v = v 0 • p + v 1 • e1 + v 2 • e2 + v 3 • s := by
      apply Prod.ext <;> funext i <;> fin_cases i <;>
        simp only [pair_add_diagonal, pair_add_upper, pair_smul_diagonal, pair_smul_upper,
          realPairBlockLinear_apply] <;>
        simp [p, e1, e2, s, realPairBlockElement, diagAtom, ← octonionScalar_smul]
    rw [he]
    exact B.carrier.add_mem (B.carrier.add_mem (B.carrier.add_mem
      (B.carrier.smul_mem _ hp) (B.carrier.smul_mem _ he1))
      (B.carrier.smul_mem _ he2)) (B.carrier.smul_mem _ hs)

theorem realPair_normal_form (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    ∃ (g : NativeAlbertAutomorphism) (a b c : ℝ),
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b = 1 ∧ a * b = c ^ 2 ∧
      g.linearEquiv p = diagAtom 0 ∧ g.linearEquiv q = realPairBlockElement ![a,b,0,c] := by
  let f : Fin 3 → Albert := ![p,q,p]
  have hf : ∀ i, IsAtom (f i) := by
    intro i
    fin_cases i
    · exact hp
    · exact hq
    · exact hp
  obtain ⟨g,hp',⟨a,b,c,ha,hb,hc,hab,hcb,hq'⟩,_⟩ := lemma_A_three f hf
  change g.linearEquiv p = diagAtom 0 at hp'
  change g.linearEquiv q = a • diagAtom 0 + b • diagAtom 1 + slotElem01 (octonionScalar c) at hq'
  have hq'': g.linearEquiv q = realPairBlockElement ![a,b,0,c] := by
    rw [hq']
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp only [pair_add_diagonal, pair_add_upper, pair_smul_diagonal, pair_smul_upper,
        pair_slot_diagonal] <;>
      simp [diagAtom, realPairBlockElement]
  exact ⟨g,a,b,c,ha,hb,hc,hab,hcb,hp',hq''⟩

theorem realPairBlock_normal_generated (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (hne : p ≠ q) (hoverlap : 0 < tracePairing p q) :
    ∃ (g : NativeAlbertAutomorphism) (a b c : ℝ),
      0 < a ∧ 0 < b ∧ 0 < c ∧ a + b = 1 ∧ a * b = c ^ 2 ∧
      g.linearEquiv p = diagAtom 0 ∧ g.linearEquiv q = realPairBlockElement ![a,b,0,c] ∧
      generatedSubalgebra ({g.linearEquiv p,g.linearEquiv q} : Set Albert) = realPairBlock := by
  obtain ⟨g,a,b,c,_,hb,hc,hab,hcb,hp',hq''⟩ := realPair_normal_form p q hp hq
  have hap : 0 < a := by
    have h := g.map_tracePairing p q
    rw [hp', hq'', tracePairing_diagAtom 0] at h
    change a = tracePairing p q at h
    exact h ▸ hoverlap
  have hbp : 0 < b := by
    refine lt_of_le_of_ne hb ?_
    intro hzero
    have h0 : b = 0 := hzero.symm
    have hc0 : c = 0 := by rw [h0, mul_zero] at hcb; nlinarith
    have ha1 : a = 1 := by simpa [h0] using hab
    apply hne
    apply g.linearEquiv.injective
    rw [hp', hq'', h0, hc0, ha1]
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp [diagAtom, realPairBlockElement]
  have hcp : 0 < c := by
    refine lt_of_le_of_ne hc ?_
    intro hzero
    have hh := mul_pos hap hbp
    rw [hcb, ← hzero] at hh
    norm_num at hh
  exact ⟨g,a,b,c,hap,hbp,hcp,hab,hcb,hp',hq'',by
    rw [hp', hq'']
    exact realPairBlock_standard_generated _ _ _ hcp.ne'⟩

theorem map_mem_generated_pair (g : NativeAlbertAutomorphism) (p q x : Albert)
    (hx : x ∈ (generatedSubalgebra ({p,q} : Set Albert)).carrier) :
    g.linearEquiv x ∈ (generatedSubalgebra ({g.linearEquiv p,g.linearEquiv q} : Set Albert)).carrier := by
  let Y : NativeJordanSubalgebra := generatedSubalgebra ({g.linearEquiv p,g.linearEquiv q} : Set Albert)
  let B : NativeJordanSubalgebra :=
    { carrier := Y.carrier.comap g.linearEquiv.toLinearMap
      unit_mem := by
        change g.linearEquiv albertUnit ∈ Y.carrier
        rw [g.preserves_unit]
        exact Y.unit_mem
      product_mem := fun u hu v hv => by
        change g.linearEquiv (jordanMul u v) ∈ Y.carrier
        rw [g.preserves_product]
        exact Y.product_mem _ hu _ hv }
  apply (mem_generatedSubalgebra_iff _ _).mp hx B
  rintro _ (rfl | rfl)
  · exact subset_generatedSubalgebra _ (by simp)
  · exact subset_generatedSubalgebra _ (by simp)

theorem realPairBlock_original_generated (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (hne : p ≠ q) (hoverlap : 0 < tracePairing p q) :
    ∃ g : NativeAlbertAutomorphism,
      ∀ x : Albert, x ∈ (generatedSubalgebra ({p,q} : Set Albert)).carrier ↔
        g.linearEquiv x ∈ realPairBlock.carrier := by
  obtain ⟨g, _, _, _, _, _, _, _, _, _, _, hB⟩ := realPairBlock_normal_generated p q hp hq hne hoverlap
  refine ⟨g, fun x => ?_⟩
  rw [← hB]
  constructor
  · exact map_mem_generated_pair g p q x
  · intro hx
    have hh := map_mem_generated_pair g.symm (g.linearEquiv p) (g.linearEquiv q) (g.linearEquiv x) hx
    simpa only [NativeAlbertAutomorphism.symm, LinearEquiv.symm_apply_apply] using hh

end AlbertSequential
