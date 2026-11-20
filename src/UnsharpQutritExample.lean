/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ChoiCompletePositivity
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace AlbertSequential.UnsharpQutrit
open Matrix
open scoped ComplexOrder

def ray (i : Fin 3) : ComplexMatrix 3 := single i i 1

def rail (b : Bool) : Fin 3 := if b then 0 else 2

/-- Two identical transitions of amplitude 1/2 give the weight 1/2 on the middle ray. -/
def branchKraus (b : Bool) : List (ComplexMatrix 3) :=
  [ray (rail b), single (rail b) 1 (1/2), single (rail b) 1 (1/2)]

def weight (b : Bool) (X : ComplexMatrix 3) : ℂ := X (rail b) (rail b) + X 1 1/2

theorem branch_action (b : Bool) (X : ComplexMatrix 3) :
    krausAction (branchKraus b) X = weight b X • ray (rail b) := by
  ext i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [branchKraus, krausAction, ray, rail, weight, Matrix.mul_apply, Fin.sum_univ_three,
      conjTranspose_apply, single_apply] <;> ring

theorem branch_effect (b : Bool) :
    krausEffect (branchKraus b) = ray (rail b) + (1/2 : ℂ) • ray 1 := by
  ext i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [branchKraus, krausEffect, ray, rail, Matrix.mul_apply, Fin.sum_univ_three,
      conjTranspose_apply, single_apply]

theorem branch_cp (b : Bool) : IsCompletelyPositiveMatrixMap (krausAction (branchKraus b)) :=
  krausAction_completelyPositive _

theorem sum_effects : krausEffect (branchKraus true) + krausEffect (branchKraus false) = 1 := by
  rw [branch_effect, branch_effect]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ray, rail, single_apply, Matrix.one_apply]

theorem trace_branch (b : Bool) (X : ComplexMatrix 3) :
    trace (krausAction (branchKraus b) X) = weight b X := by
  rw [branch_action, Matrix.trace_smul]
  cases b <;> simp [ray,rail,Matrix.trace]

theorem ray_density (i : Fin 3) : IsMatrixDensity (ray i) := by
  constructor
  · have h := Matrix.posSemidef_vecMulVec_self_star (Pi.single i (1 : ℂ))
    convert h using 1
    ext a b
    by_cases ha : i = a <;> by_cases hb : i = b <;>
      simp [ray, single_apply, vecMulVec, Pi.single_apply, ha, hb, eq_comm]
  · fin_cases i <;> simp [ray,trace]

theorem weight_ray (a b : Bool) : weight a (ray (rail b)) = if a=b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [weight,ray,rail,single_apply]

theorem repeatable (b : Bool) (X : ComplexMatrix 3) :
    krausAction (branchKraus (!b)) (krausAction (branchKraus b) X) = 0 := by
  rw [branch_action, branch_action]
  cases b <;> simp [weight,ray,rail]

theorem effect_not_idempotent :
    krausEffect (branchKraus true) * krausEffect (branchKraus true) ≠ krausEffect (branchKraus true) := by
  rw [branch_effect]
  intro h
  have bad := congrArg (fun M : ComplexMatrix 3 => M 1 1) h
  norm_num [ray,rail,Matrix.mul_apply,Fin.sum_univ_three,single_apply] at bad

private theorem column_zero {X : ComplexMatrix 3} (hX : X.PosSemidef) (j : Fin 3)
    (hz : X j j = 0) : ∀ i, X i j = 0 := by
  let v : Fin 3 → ℂ := Pi.single j 1
  have hs : star v = v := by
    funext i; by_cases h : j = i <;> simp [v,h,eq_comm]
  have h := (hX.dotProduct_mulVec_zero_iff (x := v)).mp (by
    rw [hs]; simpa [v, Matrix.mulVec_single_one, single_one_dotProduct] using hz)
  intro i
  simpa [v, Matrix.mulVec_single_one] using congrFun h i

theorem weights_sum (b : Bool) (X : ComplexMatrix 3) : weight b X + weight (!b) X = trace X := by
  cases b <;> simp [weight,rail,trace,Fin.sum_univ_three] <;> ring

/-- The only density with a certain answer is the corresponding outer ray. -/
theorem certainty_face (b : Bool) {X : ComplexMatrix 3} (hX : IsMatrixDensity X) :
    weight b X = 1 ↔ X = ray (rail b) := by
  constructor
  · intro h
    have ho : weight (!b) X = 0 := by
      have hs := weights_sum b X
      rw [h,hX.2] at hs
      exact add_left_cancel (a := (1 : ℂ)) (b := weight (!b) X) (c := 0) (by simpa using hs)
    have hdiag (i : Fin 3) := Complex.nonneg_iff.mp (hX.1.diag_nonneg (i := i))
    have hr := congrArg Complex.re ho
    change (X (rail (!b)) (rail (!b)) + X 1 1/2).re = 0 at hr
    simp only [Complex.add_re, Complex.div_ofNat_re] at hr
    have hz1 : X 1 1 = 0 := Complex.ext (by simp only [Complex.zero_re]; linarith [(hdiag 1).1,(hdiag (rail (!b))).1]) (hdiag 1).2.symm
    have hzo : X (rail (!b)) (rail (!b)) = 0 :=
      Complex.ext (by simp only [Complex.zero_re]; linarith [(hdiag 1).1,(hdiag (rail (!b))).1]) (hdiag _).2.symm
    have hkeep : X (rail b) (rail b) = 1 := by simpa [weight,hz1] using h
    have zero_col (j : Fin 3) (hj : j ≠ rail b) : ∀ i, X i j = 0 := by
      apply column_zero hX.1
      have hcases : j = 1 ∨ j = rail (!b) := by cases b <;> fin_cases j <;> simp_all [rail]
      rcases hcases with rfl | rfl
      · exact hz1
      · exact hzo
    ext i j
    by_cases hj : j = rail b
    · subst j
      by_cases hi : i = rail b
      · subst i; simpa [ray,single_apply] using hkeep
      · have hrow := hX.1.isHermitian.apply i (rail b)
        rw [zero_col i hi (rail b),star_zero] at hrow
        simp [ray,Ne.symm hi,hrow.symm]
    · simp [ray,Ne.symm hj,zero_col j hj i]
  · rintro rfl; simp [weight_ray]

theorem certainty_fixed (b : Bool) {X : ComplexMatrix 3} (hX : IsMatrixDensity X)
    (h : trace (krausAction (branchKraus b) X) = 1) : krausAction (branchKraus b) X = X := by
  rw [trace_branch] at h
  rw [branch_action,h,one_smul,(certainty_face b hX).mp h]

/-- The middle projection accepts the middle density with certainty and vanishes
on both certainty faces. -/
theorem middle_distinguishes (b : Bool) {X : ComplexMatrix 3} (hX : IsMatrixDensity X)
    (h : weight b X = 1) :
    trace (ray 1 * ray 1) = 1 ∧ trace (ray 1 * X) = 0 := by
  rw [(certainty_face b hX).mp h]
  cases b <;> norm_num [ray,rail,trace,Fin.sum_univ_three,Matrix.mul_apply,single_apply]

theorem branch_printed (b : Bool) (X : ComplexMatrix 3) :
    krausAction (branchKraus b) X = ray (rail b) * X * ray (rail b) +
      (trace (ray 1 * X) / 2) • ray (rail b) := by
  rw [branch_action]
  ext i j
  cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [weight, ray, rail, trace, Matrix.mul_apply, Fin.sum_univ_three, single_apply]

theorem trace_preserved (X : ComplexMatrix 3) :
    trace (krausAction (branchKraus true) X + krausAction (branchKraus false) X) = trace X := by
  rw [Matrix.trace_add, trace_branch, trace_branch]
  exact weights_sum true X

theorem not_projective_luders : ¬ ∃ P : ComplexMatrix 3, P * P = P ∧
    ∀ X, krausAction (branchKraus true) X = P * X * P := by
  rintro ⟨P, hP, h⟩
  have h1 := h 1
  rw [Matrix.mul_one, hP, branch_action] at h1
  rw [← h1] at hP
  have bad := congrArg (fun M : ComplexMatrix 3 => M 0 0) hP
  norm_num [weight, rail, ray, Matrix.mul_apply, Fin.sum_univ_three, single_apply] at bad

end AlbertSequential.UnsharpQutrit
