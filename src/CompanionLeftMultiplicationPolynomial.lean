/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationNormalForm
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The circle parameter in the proof sketch of companion Proposition 2.7. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

private def circleFactor (odd : Bool) (b : ℝ) : ℝ := if odd then b else 1

private def CirclePolynomial (odd : Bool) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ p : Polynomial ℝ, ∀ a b, a ^ 2 + b ^ 2 = 1 → f a b = circleFactor odd b * p.eval a

private theorem circle_const (r : ℝ) : CirclePolynomial false (fun _ _ => r) := by
  exact ⟨Polynomial.C r, fun _ _ _ => by simp [circleFactor]⟩

private theorem circle_zero (o : Bool) : CirclePolynomial o (fun _ _ => 0) :=
  ⟨0, fun _ _ _ => by simp⟩

private theorem circle_a : CirclePolynomial false (fun a _ => a) :=
  ⟨Polynomial.X, fun _ _ _ => by simp [circleFactor]⟩

private theorem circle_b : CirclePolynomial true (fun _ b => b) :=
  ⟨1, fun _ _ _ => by simp [circleFactor]⟩

private theorem circle_add {o : Bool} {f g : ℝ → ℝ → ℝ}
    (hf : CirclePolynomial o f) (hg : CirclePolynomial o g) :
    CirclePolynomial o (fun a b => f a b + g a b) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  refine ⟨p + q, fun a b h => ?_⟩
  change f a b + g a b = _
  rw [hp a b h, hq a b h, Polynomial.eval_add, mul_add]

private theorem circle_sub {o : Bool} {f g : ℝ → ℝ → ℝ}
    (hf : CirclePolynomial o f) (hg : CirclePolynomial o g) :
    CirclePolynomial o (fun a b => f a b - g a b) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  refine ⟨p - q, fun a b h => ?_⟩
  change f a b - g a b = _
  rw [hp a b h, hq a b h, Polynomial.eval_sub, mul_sub]

private theorem circle_neg {o : Bool} {f : ℝ → ℝ → ℝ} (hf : CirclePolynomial o f) :
    CirclePolynomial o (fun a b => -f a b) := by
  obtain ⟨p,hp⟩ := hf
  refine ⟨-p, fun a b h => ?_⟩
  change -f a b = _
  rw [hp a b h, Polynomial.eval_neg, mul_neg]

private theorem circle_mul {o u : Bool} {f g : ℝ → ℝ → ℝ}
    (hf : CirclePolynomial o f) (hg : CirclePolynomial u g) :
    CirclePolynomial (o ^^ u) (fun a b => f a b * g a b) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  cases o <;> cases u
  case true.true =>
    refine ⟨(1 - Polynomial.X ^ 2) * (p * q), fun a b h => ?_⟩
    change f a b * g a b = _
    rw [hp a b h, hq a b h]
    simp only [Bool.xor_self, circleFactor, Bool.false_eq_true, ↓reduceIte, one_mul,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [show 1 - a ^ 2 = b ^ 2 by linarith]
    ring
  all_goals
    refine ⟨p * q, fun a b h => ?_⟩
    change f a b * g a b = _
    rw [hp a b h, hq a b h, Polynomial.eval_mul]
  case false.false => simp [circleFactor]
  all_goals (simp [circleFactor]; ring)

private structure QuatCircle (o : Bool) (f : ℝ → ℝ → Quaternion ℝ) : Prop where
  re : CirclePolynomial o (fun a b => (f a b).re)
  imI : CirclePolynomial o (fun a b => (f a b).imI)
  imJ : CirclePolynomial o (fun a b => (f a b).imJ)
  imK : CirclePolynomial o (fun a b => (f a b).imK)

private theorem qCircle_add {o : Bool} {f g : ℝ → ℝ → Quaternion ℝ}
    (hf : QuatCircle o f) (hg : QuatCircle o g) : QuatCircle o (fun a b => f a b + g a b) :=
  ⟨circle_add hf.re hg.re, circle_add hf.imI hg.imI, circle_add hf.imJ hg.imJ, circle_add hf.imK hg.imK⟩

private theorem qCircle_sub {o : Bool} {f g : ℝ → ℝ → Quaternion ℝ}
    (hf : QuatCircle o f) (hg : QuatCircle o g) : QuatCircle o (fun a b => f a b - g a b) :=
  ⟨circle_sub hf.re hg.re, circle_sub hf.imI hg.imI, circle_sub hf.imJ hg.imJ, circle_sub hf.imK hg.imK⟩

private theorem qCircle_neg {o : Bool} {f : ℝ → ℝ → Quaternion ℝ}
    (hf : QuatCircle o f) : QuatCircle o (fun a b => -f a b) :=
  ⟨circle_neg hf.re, circle_neg hf.imI, circle_neg hf.imJ, circle_neg hf.imK⟩

private theorem qCircle_star {o : Bool} {f : ℝ → ℝ → Quaternion ℝ}
    (hf : QuatCircle o f) : QuatCircle o (fun a b => star (f a b)) :=
  ⟨by simpa only [Quaternion.re_star] using hf.re, circle_neg hf.imI, circle_neg hf.imJ, circle_neg hf.imK⟩

private theorem qCircle_mul {o u : Bool} {f g : ℝ → ℝ → Quaternion ℝ}
    (hf : QuatCircle o f) (hg : QuatCircle u g) : QuatCircle (o ^^ u) (fun a b => f a b * g a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Quaternion.re_mul]
    exact circle_sub (circle_sub (circle_sub (circle_mul hf.re hg.re) (circle_mul hf.imI hg.imI))
      (circle_mul hf.imJ hg.imJ)) (circle_mul hf.imK hg.imK)
  · simp only [Quaternion.imI_mul]
    exact circle_sub (circle_add (circle_add (circle_mul hf.re hg.imI) (circle_mul hf.imI hg.re))
      (circle_mul hf.imJ hg.imK)) (circle_mul hf.imK hg.imJ)
  · simp only [Quaternion.imJ_mul]
    exact circle_add (circle_add (circle_sub (circle_mul hf.re hg.imJ) (circle_mul hf.imI hg.imK))
      (circle_mul hf.imJ hg.re)) (circle_mul hf.imK hg.imI)
  · simp only [Quaternion.imK_mul]
    exact circle_add (circle_sub (circle_add (circle_mul hf.re hg.imK) (circle_mul hf.imI hg.imJ))
      (circle_mul hf.imJ hg.imI)) (circle_mul hf.imK hg.re)

private theorem qCircle_smul {o : Bool} {f : ℝ → ℝ → Quaternion ℝ}
    (r : ℝ) (hf : QuatCircle o f) : QuatCircle o (fun a b => r • f a b) := by
  cases o <;>
    exact ⟨circle_mul (circle_const r) hf.re, circle_mul (circle_const r) hf.imI,
      circle_mul (circle_const r) hf.imJ, circle_mul (circle_const r) hf.imK⟩

private def OctCircle (f : ℝ → ℝ → Octonion) : Prop :=
  QuatCircle false (fun a b => (f a b).1) ∧ QuatCircle true (fun a b => (f a b).2)

private theorem oCircle_add {f g : ℝ → ℝ → Octonion} (hf : OctCircle f) (hg : OctCircle g) :
    OctCircle (fun a b => f a b + g a b) :=
  ⟨qCircle_add hf.1 hg.1, qCircle_add hf.2 hg.2⟩

private theorem oCircle_sub {f g : ℝ → ℝ → Octonion} (hf : OctCircle f) (hg : OctCircle g) :
    OctCircle (fun a b => f a b - g a b) :=
  ⟨qCircle_sub hf.1 hg.1, qCircle_sub hf.2 hg.2⟩

private theorem oCircle_smul {f : ℝ → ℝ → Octonion} (r : ℝ) (hf : OctCircle f) :
    OctCircle (fun a b => r • f a b) :=
  ⟨qCircle_smul r hf.1, qCircle_smul r hf.2⟩

private theorem oCircle_conj {f : ℝ → ℝ → Octonion} (hf : OctCircle f) :
    OctCircle (fun a b => octonionConj (f a b)) :=
  ⟨qCircle_star hf.1, qCircle_neg hf.2⟩

private theorem oCircle_mul {f g : ℝ → ℝ → Octonion} (hf : OctCircle f) (hg : OctCircle g) :
    OctCircle (fun a b => octonionMul (f a b) (g a b)) :=
  ⟨qCircle_sub (qCircle_mul hf.1 hg.1) (qCircle_mul (qCircle_star hg.2) hf.2),
    qCircle_add (qCircle_mul hg.2 hf.1) (qCircle_mul hf.2 (qCircle_star hg.1))⟩

private theorem oCircle_scalar {f : ℝ → ℝ → ℝ} (hf : CirclePolynomial false f) :
    OctCircle (fun a b => octonionScalar (f a b)) :=
  ⟨⟨hf, circle_zero _, circle_zero _, circle_zero _⟩,
    ⟨circle_zero _, circle_zero _, circle_zero _, circle_zero _⟩⟩

private theorem oCircle_span (u x y z : ℝ) : OctCircle (fun a b => leftModelSpan a b u x y z) :=
  ⟨⟨circle_const u, circle_const x, circle_const y, circle_mul circle_a (circle_const z)⟩,
    ⟨circle_mul circle_b (circle_const z), circle_zero _, circle_zero _, circle_zero _⟩⟩

private def AlbertCircle (f : ℝ → ℝ → Albert) : Prop :=
  (∀ i, CirclePolynomial false (fun a b => (f a b).1 i)) ∧
    (∀ i, OctCircle (fun a b => (f a b).2 i))

private theorem aCircle_unit : AlbertCircle (fun _ _ => albertUnit) :=
  ⟨fun _ => circle_const 1, fun _ => ⟨⟨circle_zero _, circle_zero _, circle_zero _, circle_zero _⟩,
    ⟨circle_zero _, circle_zero _, circle_zero _, circle_zero _⟩⟩⟩

private theorem aCircle_sub {f g : ℝ → ℝ → Albert} (hf : AlbertCircle f) (hg : AlbertCircle g) :
    AlbertCircle (fun a b => f a b - g a b) :=
  ⟨fun i => circle_sub (hf.1 i) (hg.1 i), fun i => oCircle_sub (hf.2 i) (hg.2 i)⟩

private theorem aCircle_smul {f : ℝ → ℝ → Albert} (r : ℝ) (hf : AlbertCircle f) :
    AlbertCircle (fun a b => r • f a b) :=
  ⟨fun i => circle_mul (circle_const r) (hf.1 i), fun i => oCircle_smul r (hf.2 i)⟩

private theorem aCircle_matrix {f : ℝ → ℝ → Albert} (hf : AlbertCircle f) (i j : Fin 3) :
    OctCircle (fun a b => albertMatrix (f a b) i j) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact oCircle_scalar (hf.1 _)
    | exact hf.2 _
    | exact oCircle_conj (hf.2 _)

private theorem oCircle_sum (f : Fin 3 → ℝ → ℝ → Octonion) (hf : ∀ i, OctCircle (f i)) :
    OctCircle (fun a b => ∑ i, f i a b) := by
  simp only [Fin.sum_univ_three]
  exact oCircle_add (oCircle_add (hf 0) (hf 1)) (hf 2)

private theorem aCircle_jordanMul {f g : ℝ → ℝ → Albert} (hf : AlbertCircle f) (hg : AlbertCircle g) :
    AlbertCircle (fun a b => jordanMul (f a b) (g a b)) := by
  let m a b := octonionMatrixMul (albertMatrix (f a b)) (albertMatrix (g a b)) +
    octonionMatrixMul (albertMatrix (g a b)) (albertMatrix (f a b))
  have hm (i j : Fin 3) : OctCircle (fun a b => m a b i j) :=
    oCircle_add
      (oCircle_sum _ (fun k => oCircle_mul (aCircle_matrix hf i k) (aCircle_matrix hg k j)))
      (oCircle_sum _ (fun k => oCircle_mul (aCircle_matrix hg i k) (aCircle_matrix hf k j)))
  apply aCircle_smul
  refine ⟨fun i => (hm i i).1.re, ?_⟩
  intro i
  fin_cases i
  · exact hm 0 1
  · exact hm 0 2
  · exact hm 1 2

private theorem aCircle_trace {f : ℝ → ℝ → Albert} (hf : AlbertCircle f) :
    CirclePolynomial false (fun a b => albertTrace (f a b)) := by
  simp only [albertTrace, Fin.sum_univ_three]
  exact circle_add (circle_add (hf.1 0) (hf.1 1)) (hf.1 2)

private theorem oCircle_dyad {f : ℝ → ℝ → Fin 3 → Octonion}
    (hf : ∀ i, OctCircle (fun a b => f a b i)) : AlbertCircle (fun a b => octDyad (f a b)) := by
  refine ⟨fun i => (oCircle_mul (hf i) (oCircle_conj (hf i))).1.re, ?_⟩
  intro i
  fin_cases i
  · exact oCircle_mul (hf 0) (oCircle_conj (hf 1))
  · exact oCircle_mul (hf 0) (oCircle_conj (hf 2))
  · exact oCircle_mul (hf 1) (oCircle_conj (hf 2))

private theorem aCircle_quadratic {f g : ℝ → ℝ → Albert} (hf : AlbertCircle f) (hg : AlbertCircle g) :
    AlbertCircle (fun a b => quadraticMap (f a b) (g a b)) := by
  simpa only [quadraticMap, two_smul] using
    aCircle_sub (aCircle_smul 2 (aCircle_jordanMul hf (aCircle_jordanMul hf hg)))
      (aCircle_jordanMul (aCircle_jordanMul hf hf) hg)

private theorem aCircle_atoms (f : LeftModelNormalForm) (i : Fin 4) :
    AlbertCircle (fun a b => f.atoms a b i) := by
  simp only [f.atom_eq]
  exact oCircle_dyad (fun j => oCircle_span _ _ _ _)

private theorem aCircle_wordEffect (f : LeftModelNormalForm) (w : Word (Fin 4)) :
    AlbertCircle (fun a b => nativeWordEffect (f.atoms a b) w) := by
  induction w with
  | nil => exact aCircle_unit
  | cons letter w ih =>
    obtain ⟨i, yes⟩ := letter
    cases yes
    · exact aCircle_quadratic (aCircle_sub aCircle_unit (aCircle_atoms f i)) ih
    · exact aCircle_quadratic (aCircle_atoms f i) ih

theorem LeftModelNormalForm.nativeWord_polynomial_cos (f : LeftModelNormalForm)
    (w : Word (Fin 4)) :
    ∃ q : Polynomial ℝ, ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      nativeWordProbability (f.atoms a b) ((1 / 3 : ℝ) • albertUnit) w = q.eval a := by
  have h := aCircle_trace
    (aCircle_jordanMul (aCircle_smul (1 / 3) aCircle_unit) (aCircle_wordEffect f w))
  obtain ⟨q, hq⟩ := h
  refine ⟨q, fun a b h => ?_⟩
  rw [nativeWordProbability_eq_pairing, tracePairing]
  simpa only [circleFactor, Bool.false_eq_true, ↓reduceIte, one_mul] using hq a b h

theorem LeftModelNormalForm.nativeWord_even_sin (f : LeftModelNormalForm)
    (w : Word (Fin 4)) (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    nativeWordProbability (f.atoms a (-b)) ((1 / 3 : ℝ) • albertUnit) w =
      nativeWordProbability (f.atoms a b) ((1 / 3 : ℝ) • albertUnit) w := by
  obtain ⟨q, hq⟩ := f.nativeWord_polynomial_cos w
  rw [hq a (-b) (by simpa using h), hq a b h]

end AlbertSequential.NativeAnalysis
