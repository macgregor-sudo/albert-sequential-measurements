/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationBlockMatrices
public import FrameSlotNormalizers
public import NativeWordDuality
public import Mathlib.Data.Matrix.Composition
import Mathlib.Tactic.FinCases

/-! Ordinary real left representation of the quaternionic endpoint matrices. -/
@[expose] public section
noncomputable section
open scoped Matrix BigOperators
namespace AlbertSequential.NativeAnalysis

def leftQuaternionMatrix (q : Quaternion ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => leftModelQuaternionCoordinates (q * quaternionCoordinateUnit j) i

theorem leftQuaternionMatrix_mulVec (q p : Quaternion ℝ) :
    leftQuaternionMatrix q *ᵥ leftModelQuaternionCoordinates p =
      leftModelQuaternionCoordinates (q * p) := by
  funext i
  fin_cases i <;> norm_num [leftQuaternionMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four, quaternionCoordinateUnit, leftModelQuaternionCoordinates,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem quaternionCoordinate_surj :
    Function.Surjective leftModelQuaternionCoordinates := by
  intro x
  refine ⟨⟨x 0, x 1, x 2, x 3⟩, ?_⟩
  funext i
  fin_cases i <;> rfl

def leftQuaternionRingHom : Quaternion ℝ →+* Matrix (Fin 4) (Fin 4) ℝ where
  toFun := leftQuaternionMatrix
  map_zero' := by
    ext i j
    fin_cases i <;> simp [leftQuaternionMatrix, leftModelQuaternionCoordinates]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [leftQuaternionMatrix, leftModelQuaternionCoordinates, quaternionCoordinateUnit,
        Matrix.one_apply]
  map_add' q p := by
    ext i j
    fin_cases i <;> simp [leftQuaternionMatrix, leftModelQuaternionCoordinates, add_mul]
  map_mul' q p := by
    apply Matrix.mulVec_injective
    funext f
    obtain ⟨v, rfl⟩ := quaternionCoordinate_surj f
    rw [← Matrix.mulVec_mulVec, leftQuaternionMatrix_mulVec, leftQuaternionMatrix_mulVec,
      leftQuaternionMatrix_mulVec, mul_assoc]

theorem leftQuaternionMatrix_transpose (q : Quaternion ℝ) :
    (leftQuaternionMatrix q)ᵀ = leftQuaternionMatrix (star q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leftQuaternionMatrix, leftModelQuaternionCoordinates, quaternionCoordinateUnit,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]

theorem leftQuaternionMatrix_smul (r : ℝ) (q : Quaternion ℝ) :
    leftQuaternionMatrix (r • q) = r • leftQuaternionMatrix q := by
  ext i j
  fin_cases i <;> simp [leftQuaternionMatrix, leftModelQuaternionCoordinates]

theorem leftQuaternionMatrix_trace (q : Quaternion ℝ) :
    (leftQuaternionMatrix q).trace = 4 * q.re := by
  unfold Matrix.trace
  norm_num [Fin.sum_univ_four, leftQuaternionMatrix, leftModelQuaternionCoordinates,
    quaternionCoordinateUnit, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

def leftQuaternionMatrixRepresentation : QuatMatrix3 →+*
    Matrix QuaternionColumnCoordinate QuaternionColumnCoordinate ℝ :=
  (Matrix.compRingEquiv (Fin 3) (Fin 4) ℝ).toRingHom.comp
    (leftQuaternionRingHom.mapMatrix (m := Fin 3))

theorem leftQuaternionMatrixRepresentation_apply (A : QuatMatrix3)
    (i j : QuaternionColumnCoordinate) :
    leftQuaternionMatrixRepresentation A i j = leftQuaternionMatrix (A i.1 j.1) i.2 j.2 := rfl

theorem leftQuaternionMatrixRepresentation_star (A : QuatMatrix3) :
    leftQuaternionMatrixRepresentation (star A) = star (leftQuaternionMatrixRepresentation A) := by
  ext i j
  change leftQuaternionMatrix (star (A j.1 i.1)) i.2 j.2 =
    star (leftQuaternionMatrix (A j.1 i.1) j.2 i.2)
  rw [← leftQuaternionMatrix_transpose]
  rfl

theorem leftQuaternionMatrixRepresentation_trace (A : QuatMatrix3) :
    (leftQuaternionMatrixRepresentation A).trace = 4 * ∑ i, (A i i).re := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact leftQuaternionMatrix_trace (A i i)

def quaternionColumnDyad (q : Fin 3 → Quaternion ℝ) : QuatMatrix3 :=
  fun i j => q i * star (q j)

theorem leftQuaternionMatrixRepresentation_columnDyad (q : Fin 3 → Quaternion ℝ) (r : ℝ) :
    leftQuaternionMatrixRepresentation (r • quaternionColumnDyad q) =
      r • (quaternionRealLeftColumn q * (quaternionRealLeftColumn q)ᵀ) := by
  ext i j
  rw [leftQuaternionMatrixRepresentation_apply]
  change leftQuaternionMatrix (r • (q i.1 * star (q j.1))) i.2 j.2 =
      r * ((quaternionRealLeftColumn q * (quaternionRealLeftColumn q)ᵀ) i j)
  rw [leftQuaternionMatrix_smul, Matrix.smul_apply, smul_eq_mul]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i.2 j.2)
    (leftQuaternionRingHom.map_mul (q i.1) (star (q j.1)))
  change leftQuaternionMatrix (q i.1 * star (q j.1)) i.2 j.2 =
    (leftQuaternionMatrix (q i.1) * leftQuaternionMatrix (star (q j.1))) i.2 j.2 at h
  rw [h, ← leftQuaternionMatrix_transpose]
  rfl


private theorem quaternionicWindow_sandwich (Q : QuaternionicWindow) (A B C : QuatHermitian3)
    (hC : (C : QuatMatrix3) = (A : QuatMatrix3) * (B : QuatMatrix3) * (A : QuatMatrix3)) :
    Q.embedding C = quadraticMap (Q.embedding A) (Q.embedding B) := by
  obtain ⟨AB, hAB⟩ := quatHermitian_product_closed A B
  obtain ⟨AAB, hAAB⟩ := quatHermitian_product_closed A AB
  obtain ⟨ASq, hASq⟩ := quatHermitian_product_closed A A
  obtain ⟨ASqB, hASqB⟩ := quatHermitian_product_closed ASq B
  have hASq' : (ASq : QuatMatrix3) = (A : QuatMatrix3) * (A : QuatMatrix3) := by
    rw [hASq, ← two_smul ℝ, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
  have hC' : C = (2 : ℝ) • AAB - ASqB := by
    apply Subtype.ext
    change (C : QuatMatrix3) = (2 : ℝ) • (AAB : QuatMatrix3) - (ASqB : QuatMatrix3)
    rw [hC, hAAB, hASqB, hAB, hASq', Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul, smul_smul, ← mul_assoc,
      show (2 : ℝ) * (1 / 2) * (1 / 2) = 1 / 2 by norm_num,
      Matrix.mul_add, Matrix.add_mul, ← smul_sub]
    have he :
        (A : QuatMatrix3) * ((A : QuatMatrix3) * B) + (A : QuatMatrix3) * ((B : QuatMatrix3) * A) +
            ((A : QuatMatrix3) * B * A + (B : QuatMatrix3) * A * A) -
          ((A : QuatMatrix3) * A * B + (B : QuatMatrix3) * A * A) =
        (2 : ℝ) • ((A : QuatMatrix3) * B * A) := by
      simp only [Matrix.mul_assoc, two_smul]
      abel
    rw [he, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
  rw [hC', map_sub, map_smul, Q.preserves_product _ _ AAB hAAB,
    Q.preserves_product _ _ AB hAB, Q.preserves_product _ _ ASqB hASqB,
    Q.preserves_product _ _ ASq hASq]
  simp only [quadraticMap, two_smul]

private def quaternionicOutcome {ι : Type*} (P : ι → QuatHermitian3) (x : Outcome ι) :
    QuatHermitian3 := if x.2 then P x.1 else 1 - P x.1

private theorem quaternionicOutcome_val {ι : Type*} (P : ι → QuatHermitian3)
    (x : Outcome ι) : (quaternionicOutcome P x : QuatMatrix3) =
      algebraicOutcome (fun i => (P i : QuatMatrix3)) x := by
  obtain ⟨i,b⟩ := x
  cases b <;> rfl

private theorem quaternionicOutcome_embedding {ι : Type*} (Q : QuaternionicWindow)
    (P : ι → QuatHermitian3) (x : Outcome ι) :
    Q.embedding (quaternionicOutcome P x) = nativeOutcome (fun i => Q.embedding (P i)) x := by
  obtain ⟨i,b⟩ := x
  cases b
  · change Q.embedding (1 - P i) = albertUnit - Q.embedding (P i)
    rw [map_sub, Q.unit]
  · rfl

private def quaternionicWordEffect {ι : Type*} (P : ι → QuatHermitian3) (w : Word ι) :
    QuatHermitian3 :=
  ⟨wordOperator (fun i => (P i : QuatMatrix3)) w, by
    simp only [selfAdjoint.mem_iff, wordOperator, star_mul, star_star]⟩

private theorem quaternionicWordEffect_embedding {ι : Type*} (Q : QuaternionicWindow)
    (P : ι → QuatHermitian3) (w : Word ι) :
    Q.embedding (quaternionicWordEffect P w) = nativeWordEffect (fun i => Q.embedding (P i)) w := by
  induction w with
  | nil =>
    have he : quaternionicWordEffect P [] = 1 := by
      apply Subtype.ext
      exact wordOperator_nil _
    rw [he, Q.unit]
    rfl
  | cons x w ih =>
    have he := quaternionicWindow_sandwich Q (quaternionicOutcome P x) (quaternionicWordEffect P w)
      (quaternionicWordEffect P (x :: w)) (by
        change wordOperator (fun i => (P i : QuatMatrix3)) (x :: w) = _
        rw [quaternionicOutcome_val, wordOperator_cons _ (fun i => (P i).2)]
        rfl)
    rw [he, quaternionicOutcome_embedding, ih]
    rfl

theorem leftQuaternionMatrixRepresentation_wordProbability {ι : Type*}
    (Q : QuaternionicWindow) (P : ι → QuatHermitian3) (w : Word ι) :
    (wordOperator (fun i => leftQuaternionMatrixRepresentation (P i : QuatMatrix3)) w).trace / 12 =
      nativeWordProbability (fun i => Q.embedding (P i)) ((1 / 3 : ℝ) • albertUnit) w := by
  let E := quaternionicWordEffect P w
  have hout (x : Outcome ι) :
      algebraicOutcome (fun i => leftQuaternionMatrixRepresentation (P i : QuatMatrix3)) x =
        leftQuaternionMatrixRepresentation (algebraicOutcome (fun i => (P i : QuatMatrix3)) x) := by
    obtain ⟨i,b⟩ := x
    cases b
    · change (1 - leftQuaternionMatrixRepresentation (P i : QuatMatrix3)) =
        leftQuaternionMatrixRepresentation (1 - (P i : QuatMatrix3))
      rw [map_sub, map_one]
    · rfl
  have hword : wordOperator (fun i => leftQuaternionMatrixRepresentation (P i : QuatMatrix3)) w =
      leftQuaternionMatrixRepresentation (E : QuatMatrix3) := by
    change _ = leftQuaternionMatrixRepresentation (wordOperator (fun i => (P i : QuatMatrix3)) w)
    have hstar i : star (leftQuaternionMatrixRepresentation (P i : QuatMatrix3)) =
        leftQuaternionMatrixRepresentation (P i : QuatMatrix3) := by
      rw [← leftQuaternionMatrixRepresentation_star, (P i).2]
    induction w with
    | nil => simp
    | cons x w ih =>
      rw [wordOperator_cons _ hstar, wordOperator_cons _ (fun i => (P i).2), hout, ih, map_mul, map_mul]
  rw [hword, leftQuaternionMatrixRepresentation_trace,
    nativeWordProbability_eq_pairing, tracePairing_smul_left, tracePairing_comm albertUnit,
    tracePairing_unit_right, ← quaternionicWordEffect_embedding Q P, Q.preserves_trace,
    Fin.sum_univ_three]
  ring

end AlbertSequential.NativeAnalysis
