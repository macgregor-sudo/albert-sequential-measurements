/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.Geometry
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The three quadratic Fourier bases in dimension3. Inner products are the
explicit finite sum conjugate(v_i)w_i, so no function-space norm is implicit.
For x=1,2, x²=1 in F3, hence the quadratic phases are diag(1,u,u).
The fixed three-term character identities below are the elementary root-of-
unity proof, not an external certificate or numerical computation. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped BigOperators

def qutritRoot : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

def qutritCharacter (b : Fin 3) : ℂ := ![1, qutritRoot, star qutritRoot] b

def qutritInner (v w : Fin 3 → ℂ) : ℂ := ∑ x, star (v x) * w x

theorem qutritCharacter_normSq (b : Fin 3) : Complex.normSq (qutritCharacter b) = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  fin_cases b <;>
    norm_num [qutritCharacter, qutritRoot, Complex.star_def, Complex.normSq] <;> nlinarith

theorem qutritCharacter_unit (b : Fin 3) : star (qutritCharacter b) * qutritCharacter b = 1 := by
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, qutritCharacter_normSq,
    Complex.ofReal_one] using (rfl : star (qutritCharacter b) * qutritCharacter b =
      star (qutritCharacter b) * qutritCharacter b)

theorem qutritCharacter_overlap (b c : Fin 3) :
    star (qutritCharacter b) * qutritCharacter c +
      qutritCharacter b * star (qutritCharacter c) = if b = c then 2 else -1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  fin_cases b <;> fin_cases c <;> apply Complex.ext <;>
    norm_num [qutritCharacter, qutritRoot, Complex.star_def,
      Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem qutritCharacter_distinct_re (a b : Fin 3) (hab : a ≠ b) :
    (star (qutritCharacter a) * qutritCharacter b).re = -1 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  fin_cases a <;> fin_cases b
  all_goals try contradiction
  all_goals norm_num [qutritCharacter, qutritRoot, Complex.star_def, Complex.mul_re] at hab ⊢
  all_goals nlinarith

def qutritRawFourierVector (u : ℂ) (b : Fin 3) : Fin 3 → ℂ :=
  fun x => match x.val with
    | 0 => 1
    | 1 => u * qutritCharacter b
    | _ => u * star (qutritCharacter b)

def qutritFourierVector (u : ℂ) (b : Fin 3) : Fin 3 → ℂ :=
  fun x => ((Real.sqrt (1 / 3) : ℝ) : ℂ) * qutritRawFourierVector u b x

theorem qutritRawFourierVector_inner (u v : ℂ) (b c : Fin 3) :
    qutritInner (qutritRawFourierVector u b) (qutritRawFourierVector v c) =
      1 + star u * v * (if b = c then 2 else -1) := by
  have h := qutritCharacter_overlap b c
  unfold qutritInner
  rw [Fin.sum_univ_three]
  change star (1 : ℂ) * 1 + star (u * qutritCharacter b) * (v * qutritCharacter c) +
    star (u * star (qutritCharacter b)) * (v * star (qutritCharacter c)) = _
  simp only [star_one, one_mul, star_mul, star_star]
  calc
    _ = 1 + star u * v *
        (star (qutritCharacter b) * qutritCharacter c +
          qutritCharacter b * star (qutritCharacter c)) := by ring
    _ = _ := by rw [h]

theorem qutritInner_scale (v w : Fin 3 → ℂ) (r : ℝ) :
    qutritInner (fun x => (r : ℂ) * v x) (fun x => (r : ℂ) * w x) =
      ((r : ℂ) * (r : ℂ)) * qutritInner v w := by
  simp only [qutritInner, Fin.sum_univ_three, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem qutritNormalization_square :
    ((Real.sqrt (1 / 3) : ℝ) : ℂ) * ((Real.sqrt (1 / 3) : ℝ) : ℂ) = (1 / 3 : ℂ) := by
  rw [← Complex.ofReal_mul]
  simpa using congrArg Complex.ofReal (Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 / 3 by norm_num))

theorem qutritFourierVector_inner (u v : ℂ) (b c : Fin 3) :
    qutritInner (qutritFourierVector u b) (qutritFourierVector v c) =
      (1 / 3 : ℂ) * (1 + star u * v * (if b = c then 2 else -1)) := by
  change qutritInner (fun x => _ * qutritRawFourierVector u b x)
    (fun x => _ * qutritRawFourierVector v c x) = _
  rw [qutritInner_scale, qutritNormalization_square, qutritRawFourierVector_inner]

theorem qutritFourierVector_orthonormal (a b c : Fin 3) :
    qutritInner (qutritFourierVector (qutritCharacter a) b)
      (qutritFourierVector (qutritCharacter a) c) = if b = c then 1 else 0 := by
  rw [qutritFourierVector_inner, qutritCharacter_unit]
  split_ifs <;> norm_num

theorem qutritFourierVector_coordinate_normSq (a b x : Fin 3) :
    Complex.normSq (qutritFourierVector (qutritCharacter a) b x) = 1 / 3 := by
  have hs : Real.sqrt (1 / 3) * Real.sqrt (1 / 3) = (1 / 3 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  fin_cases x <;>
    simp [qutritFourierVector, qutritRawFourierVector, Complex.normSq_mul,
      Complex.star_def, Complex.normSq_conj, qutritCharacter_normSq,
      Complex.normSq_ofReal, hs]

theorem complex_overlap_normSq {r : ℂ} (hre : r.re = -1 / 2) (hnorm : Complex.normSq r = 1) :
    Complex.normSq (1 + 2 * r) = 3 ∧ Complex.normSq (1 - r) = 3 := by
  rw [Complex.normSq_apply] at hnorm
  rw [hre] at hnorm
  constructor <;>
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, hre] <;> nlinarith

theorem qutritFourierVector_unbiased (a a' : Fin 3) (haa : a ≠ a') (b c : Fin 3) :
    Complex.normSq (qutritInner (qutritFourierVector (qutritCharacter a) b)
      (qutritFourierVector (qutritCharacter a') c)) = 1 / 3 := by
  have hre := qutritCharacter_distinct_re a a' haa
  have hnorm : Complex.normSq (star (qutritCharacter a) * qutritCharacter a') = 1 := by
    simp [Complex.normSq_mul, Complex.star_def, qutritCharacter_normSq]
  obtain ⟨hplus, hminus⟩ := complex_overlap_normSq hre hnorm
  rw [qutritFourierVector_inner, Complex.normSq_mul]
  by_cases hbc : b = c
  · simp only [hbc, ↓reduceIte]
    rw [mul_comm (star (qutritCharacter a) * qutritCharacter a') 2, hplus]
    norm_num
  · simp only [hbc, ↓reduceIte]
    have heq : 1 + star (qutritCharacter a) * qutritCharacter a' * (-1) =
        1 - star (qutritCharacter a) * qutritCharacter a' := by ring
    rw [heq, hminus]
    norm_num

end AlbertSequential
