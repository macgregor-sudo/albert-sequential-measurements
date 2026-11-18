/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Contraction
public import ThreeAtomAndFourPoint

/-! # Complex windows: Jordan expressions in three letters transfer (prop:three step)

The paper uses Proposition `prop:three` (three atoms lie in a complex subalgebra `W ≅ H₃(ℂ)`) in
lem:cer:h5:refl(a) and in Step 2 of lem:cer:h5:seven: there, a Jordan polynomial in the letters of
a three-element set is evaluated with `3 × 3` complex matrices of square one, so its Albert value
is the image of its special value.  This file proves that step in Lean from
`complexTripleContract_holds`:

* `window_eval`: in a complex window `W`, any Jordan expression in window elements is the image
  of the symmetrized-product (special) evaluation of the same expression in `M₃(ℂ)`;
* `transfer_free_letter`: for any four atoms, if `F` does not involve the letter `x_j` and
  `σ̂(F) = 0`, then `ν̂(F) = 0`.

(No degree bound is needed; this is the part of Step 2 that does not use Cohn's theorem.) -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-- Evaluation only depends on the letters that occur. -/
theorem JTarget.eval_congr_free {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E)
    {X : Type} (v v' : X → E) (j : X) (h : ∀ x, x ≠ j → v x = v' x) (F : JPoly X)
    (hF : F.FreeOf j) : T.eval v F = T.eval v' F := by
  induction hF with
  | one => rfl
  | var x hx => exact h x hx
  | add a b _ _ ha hb =>
    show T.eval v a + T.eval v b = T.eval v' a + T.eval v' b
    rw [ha, hb]
  | smul r a _ ha =>
    show r • T.eval v a = r • T.eval v' a
    rw [ha]
  | mul a b _ _ ha hb =>
    show T.mul (T.eval v a) (T.eval v b) = T.mul (T.eval v' a) (T.eval v' b)
    rw [ha, hb]

/-- Algebra homomorphisms commute with the special evaluation. -/
theorem specialTarget_eval_hom {A B : Type*} [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]
    (φ : A →ₐ[ℝ] B) {X : Type} (v : X → A) (F : JPoly X) :
    φ ((specialTarget A).eval v F) = (specialTarget B).eval (fun x => φ (v x)) F := by
  induction F with
  | one => exact map_one φ
  | var x => rfl
  | add a b ha hb =>
    show φ ((specialTarget A).eval v a + (specialTarget A).eval v b) = _ + _
    rw [map_add, ha, hb]
  | smul r a ha =>
    show φ (r • (specialTarget A).eval v a) = r • _
    rw [map_smul, ha]
  | mul a b ha hb =>
    show φ ((specialTarget A).mul _ _) = (specialTarget B).mul _ _
    rw [specialTarget_mul, specialTarget_mul, map_smul, map_add, map_mul, map_mul, ha, hb]

/-- Jordan expressions in window elements are images of their special evaluation in `M₃(ℂ)`. -/
theorem window_eval (W : ComplexWindow) {X : Type} (Y : X → Hermitian3) (F : JPoly X) :
    ∃ Z : Hermitian3,
      (Z : ComplexMatrix3) = (specialTarget ComplexMatrix3).eval (fun x => (Y x : ComplexMatrix3)) F ∧
      W.embedding Z = albertTarget.eval (fun x => W.embedding (Y x)) F := by
  induction F with
  | one => exact ⟨1, rfl, W.unit⟩
  | var x => exact ⟨Y x, rfl, rfl⟩
  | add a b ha hb =>
    obtain ⟨Za, h1, h2⟩ := ha
    obtain ⟨Zb, h3, h4⟩ := hb
    refine ⟨Za + Zb, ?_, ?_⟩
    · show (Za : ComplexMatrix3) + Zb = _ + _
      rw [h1, h3]
    · show W.embedding (Za + Zb) = albertTarget.eval _ a + albertTarget.eval _ b
      rw [map_add, h2, h4]
  | smul r a ha =>
    obtain ⟨Za, h1, h2⟩ := ha
    refine ⟨r • Za, ?_, ?_⟩
    · show r • (Za : ComplexMatrix3) = r • _
      rw [h1]
    · show W.embedding (r • Za) = r • albertTarget.eval _ a
      rw [map_smul, h2]
  | mul a b ha hb =>
    obtain ⟨Za, h1, h2⟩ := ha
    obtain ⟨Zb, h3, h4⟩ := hb
    obtain ⟨Z, hZ⟩ := W.product_closed Za Zb
    refine ⟨Z, ?_, ?_⟩
    · show (Z : ComplexMatrix3) = (specialTarget ComplexMatrix3).mul _ _
      rw [hZ, specialTarget_mul, h1, h3]
    · show W.embedding Z = jordanMul (albertTarget.eval _ a) (albertTarget.eval _ b)
      rw [W.preserves_product Za Zb Z hZ, h2, h4]

theorem succAbove_surj (j x : Test) (h : x ≠ j) : ∃ k : Fin 3, j.succAbove k = x := by
  revert j x
  decide

/-- **prop:three step of companion `app:cert:h5` (proved).** For any four atoms, a Jordan expression that does
not involve `x_j` and has special value zero has Albert value zero. -/
theorem transfer_free_letter (p : Test → Albert) (hp : ∀ i, IsAtom (p i)) (j : Test)
    (F : JPoly Test) (hF : F.FreeOf j) (h0 : specialEval F = 0) : albertEval p F = 0 := by
  classical
  obtain ⟨W, hW⟩ := complexTripleContract_holds.common_window (fun k => p (j.succAbove k))
    (fun k => hp _)
  have hW' : ∀ k, ∃ x : Hermitian3, W.embedding x = p (j.succAbove k) := hW
  choose X hX using hW'
  -- the window matrices of the atoms are idempotent
  have hidem : ∀ k, (X k : ComplexMatrix3) * X k = X k := by
    intro k
    obtain ⟨Z, hZ⟩ := W.product_closed (X k) (X k)
    have h1 := W.preserves_product (X k) (X k) Z hZ
    rw [hX, (hp _).1, ← hX k] at h1
    have h2 := W.injective h1
    rw [h2] at hZ
    have h3 : (1 / 2 : ℝ) • ((X k : ComplexMatrix3) * X k + X k * X k) = X k * X k := by
      rw [← two_smul ℝ ((X k : ComplexMatrix3) * X k), smul_smul]
      norm_num
    rw [← h3]
    exact hZ.symm
  -- letter values
  let kOf : Test → Fin 3 := fun i => if h : i = j then 0 else Classical.choose (succAbove_surj j i h)
  have hkOf : ∀ i, i ≠ j → j.succAbove (kOf i) = i := by
    intro i hi
    simp only [kOf, dite_eq_right hi]
    exact Classical.choose_spec (succAbove_surj j i hi)
  let gen : Test → ComplexMatrix3 := fun i => if i = j then 0 else (X (kOf i) : ComplexMatrix3)
  have hgen : ∀ i, gen i * gen i = gen i := by
    intro i
    by_cases hi : i = j
    · simp [gen, hi]
    · simp only [gen, ite_eq_right hi]
      exact hidem _
  let φ : UniversalProjectionAlgebra 4 →ₐ[ℝ] ComplexMatrix3 :=
    RingQuot.liftAlgHom ℝ ⟨FreeAlgebra.lift ℝ gen, by
      intro x y h
      cases h with
      | generator i =>
        simp only [map_mul, FreeAlgebra.lift_ι_apply]
        exact hgen i⟩
  have hφP : ∀ i, φ (universalTests i) = gen i := by
    intro i
    simp only [φ, universalTests, universalProjection, projectionQuotient]
    rw [RingQuot.liftAlgHom_mkAlgHom_apply]
    simp only [FreeAlgebra.lift_ι_apply]
  let Y : Test → Hermitian3 := fun i => (2 : ℝ) • X (kOf i) - 1
  have hYmat : ∀ i, i ≠ j → (Y i : ComplexMatrix3) = φ (specialSymmetry i) := by
    intro i hi
    simp only [specialSymmetry, map_sub, map_smul, map_one, hφP, gen, ite_eq_right hi]
    rfl
  have hYalb : ∀ i, i ≠ j → W.embedding (Y i) = nativeSymmetry p i := by
    intro i hi
    simp only [Y, map_sub, map_smul, W.unit, hX, hkOf i hi, nativeSymmetry]
  obtain ⟨Z, hZ1, hZ2⟩ := window_eval W Y F
  have hZ0 : (Z : ComplexMatrix3) = 0 := by
    rw [hZ1, (specialTarget ComplexMatrix3).eval_congr_free _ (fun x => φ (specialSymmetry x)) j
      hYmat F hF, ← specialTarget_eval_hom]
    change φ (specialEval F) = 0
    rw [h0, map_zero]
  have hZz : Z = 0 := Subtype.ext hZ0
  rw [hZz, map_zero, albertTarget.eval_congr_free _ (nativeSymmetry p) j hYalb F hF] at hZ2
  exact hZ2.symm

end AlbertSequential.HorizonFive
