/- SPDX-License-Identifier: Apache-2.0 -/
module
public import InstrumentFactorization

/-! Lift a channel between isometric subspaces and complete it by an explicit
reset channel. All formulas are identities on arbitrary matrices. -/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential
open Matrix

def isometricLiftKraus {d D : ℕ} (K : List (ComplexMatrix d))
    (ι V : Matrix (Fin D) (Fin d) ℂ) : List (ComplexMatrix D) :=
  K.map (fun W => ι * W * Vᴴ)

theorem isometricLiftKraus_action {d D : ℕ} (K : List (ComplexMatrix d))
    (ι V : Matrix (Fin D) (Fin d) ℂ) (Z : ComplexMatrix D) :
    krausAction (isometricLiftKraus K ι V) Z =
      ι * krausAction K (Vᴴ * Z * V) * ιᴴ := by
  induction K with
  | nil => simp [isometricLiftKraus, krausAction]
  | cons W K ih =>
      simp only [isometricLiftKraus, List.map_cons, krausAction, List.sum_cons,
        List.map_map] at ih ⊢
      rw [ih]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem isometricLiftKraus_effect {d D : ℕ} (K : List (ComplexMatrix d))
    (ι V : Matrix (Fin D) (Fin d) ℂ) (hι : ιᴴ * ι = 1) :
    krausEffect (isometricLiftKraus K ι V) = V * krausEffect K * Vᴴ := by
  induction K with
  | nil => simp [isometricLiftKraus, krausEffect]
  | cons W K ih =>
      simp only [isometricLiftKraus, List.map_cons, krausEffect, List.sum_cons,
        List.map_map] at ih ⊢
      rw [ih]
      have hw : (ι * W * Vᴴ)ᴴ * (ι * W * Vᴴ) = V * (Wᴴ * W) * Vᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        calc
          _ = V * Wᴴ * (ιᴴ * ι) * W * Vᴴ := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hι, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      rw [hw, Matrix.mul_add, Matrix.add_mul]

theorem isometry_range_hermitian {d D : ℕ} (V : Matrix (Fin D) (Fin d) ℂ) :
    (V * Vᴴ)ᴴ = V * Vᴴ := by simp

theorem isometry_range_idempotent {d D : ℕ} (V : Matrix (Fin D) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
  calc
    _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one]

theorem isometry_range_complement_hermitian {d D : ℕ}
    (V : Matrix (Fin D) (Fin d) ℂ) :
    (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by simp

theorem isometry_range_complement_idempotent {d D : ℕ}
    (V : Matrix (Fin D) (Fin d) ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    isometry_range_idempotent V hV]
  abel

def isometricCompletedKraus {d D : ℕ} (K : List (ComplexMatrix d))
    (ι V : Matrix (Fin D) (Fin d) ℂ) (B : ComplexMatrix D) : List (ComplexMatrix D) :=
  isometricLiftKraus K ι V ++ measurePrepareKraus B (1 - V * Vᴴ)

theorem isometricCompletedKraus_effect {d D : ℕ} (K : List (ComplexMatrix d))
    (ι V : Matrix (Fin D) (Fin d) ℂ) (B : ComplexMatrix D)
    (hK : krausEffect K = 1) (hι : ιᴴ * ι = 1) (hV : Vᴴ * V = 1)
    (hB : Matrix.trace (B * Bᴴ) = 1) :
    krausEffect (isometricCompletedKraus K ι V B) = 1 := by
  rw [isometricCompletedKraus, krausEffect_append,
    isometricLiftKraus_effect K ι V hι, hK, Matrix.mul_one,
    measurePrepareKraus_effect, hB, one_smul,
    isometry_range_complement_hermitian,
    isometry_range_complement_idempotent V hV]
  abel

theorem isometricCompletedKraus_action {d D : ℕ} (K : List (ComplexMatrix d))
    (ι V : Matrix (Fin D) (Fin d) ℂ) (B Z : ComplexMatrix D)
    (hV : Vᴴ * V = 1) :
    krausAction (isometricCompletedKraus K ι V B) Z =
      ι * krausAction K (Vᴴ * Z * V) * ιᴴ +
        Matrix.trace ((1 - V * Vᴴ) * Z) • (B * Bᴴ) := by
  rw [isometricCompletedKraus, krausAction_append, isometricLiftKraus_action,
    measurePrepareKraus_action, isometry_range_complement_hermitian]
  congr 2
  rw [Matrix.trace_mul_cycle, isometry_range_complement_idempotent V hV]

theorem isometricCompletedKraus_compressed_action {d D : ℕ}
    (K : List (ComplexMatrix d)) (ι V : Matrix (Fin D) (Fin d) ℂ)
    (B Z : ComplexMatrix D) (hV : Vᴴ * V = 1) :
    krausAction (isometricCompletedKraus K ι V B) ((V * Vᴴ) * Z * (V * Vᴴ)) =
      ι * krausAction K (Vᴴ * Z * V) * ιᴴ := by
  have hl : Vᴴ * (V * Vᴴ) = Vᴴ := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hr : (V * Vᴴ) * V = V := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hzero : (1 - V * Vᴴ) * (V * Vᴴ) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, isometry_range_idempotent V hV, sub_self]
  rw [isometricCompletedKraus_action K ι V B _ hV]
  have hc : Vᴴ * ((V * Vᴴ) * Z * (V * Vᴴ)) * V = Vᴴ * Z * V := by
    calc
      _ = (Vᴴ * (V * Vᴴ)) * Z * ((V * Vᴴ) * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hl, hr]
  have hz : (1 - V * Vᴴ) * ((V * Vᴴ) * Z * (V * Vᴴ)) = 0 := by
    calc
      _ = ((1 - V * Vᴴ) * (V * Vᴴ)) * Z * (V * Vᴴ) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero]; simp
  rw [hc, hz, Matrix.trace_zero, zero_smul, add_zero]

#print axioms isometricCompletedKraus_effect
#print axioms isometricCompletedKraus_compressed_action
end AlbertSequential
