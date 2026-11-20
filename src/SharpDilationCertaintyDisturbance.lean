/- SPDX-License-Identifier: Apache-2.0 -/
module

public import DegenerateSharpDilation
public import RealFiniteKrausComplexification
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Exact certainty-face outputs for the paper's doubled binary dilation. -/

@[expose] public section
noncomputable section
open scoped Matrix ComplexOrder

namespace AlbertSequential

private theorem positiveRoot_mul_of_eigenvalue {d : ℕ} {A X : ComplexMatrix d}
    (s : FiniteSpectralSupport A) {a : ℝ} (ha : 0 < a) (hAX : A * X = a • X) :
    s.root * X = Real.sqrt a • X := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hp : ((1 : ComplexMatrix d)).PosDef := by
    simpa only [Nat.cast_one] using
      (Matrix.PosDef.natCast (n := Fin d) (R := ℂ) 1 (by norm_num))
  have hpos : (s.root + Real.sqrt a • (1 : ComplexMatrix d)).PosDef := by
    rw [add_comm]
    exact (hp.smul hs).add_posSemidef s.root_positive
  have hu := hpos.isUnit
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  rw [Matrix.mul_zero, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub,
    ← Matrix.mul_assoc s.root, s.root_sq, hAX]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul, Real.mul_self_sqrt ha.le]
  abel

private theorem root_sandwich_of_eigenvalue {d : ℕ} {A X : ComplexMatrix d}
    (s : FiniteSpectralSupport A) {a : ℝ} (ha : 0 < a)
    (hX : Xᴴ = X) (hAX : A * X = a • X) : s.root * X * s.root = a • X := by
  have hleft := positiveRoot_mul_of_eigenvalue s ha hAX
  have hright : X * s.root = Real.sqrt a • X := by
    simpa only [Matrix.conjTranspose_mul, s.root_hermitian, hX, Matrix.conjTranspose_smul,
      star_trivial] using congrArg Matrix.conjTranspose hleft
  rw [hleft, Matrix.smul_mul, hright, smul_smul, Real.mul_self_sqrt ha.le]

/-- No nonzero positive effect vanishes on both complementary projection corners. -/
theorem positiveEffect_eq_zero_of_complementaryCorners {d : ℕ} {P F : ComplexMatrix d}
    (hP : P * P = P) (hF : F.PosSemidef)
    (hy : P * F * P = 0) (hn : (1-P) * F * (1-P) = 0) : F = 0 := by
  have hQ : (1-P) * (1-P) = 1-P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]
    abel
  have htrace : P * F + (1-P) * F = F := by
    rw [← Matrix.add_mul, show P + (1-P) = 1 by abel, Matrix.one_mul]
  have ht := congrArg Matrix.trace htrace
  have htY := congrArg Matrix.trace hy
  have htN := congrArg Matrix.trace hn
  rw [Matrix.trace_mul_cycle, hP, Matrix.trace_zero] at htY
  rw [Matrix.trace_mul_cycle, hQ, Matrix.trace_zero] at htN
  rw [Matrix.trace_add, htY, htN, add_zero] at ht
  exact hF.trace_eq_zero_iff.mp ht.symm

/-- Lift an input to the yes face via the literal yes isometry of the doubled dilation. -/
def binaryYesFaceState {d : ℕ} {A : ComplexMatrix d} (s : BinarySpectralSupport A)
    (X : ComplexMatrix d) : ComplexMatrix (d + d) :=
  finiteBinaryYesIsometry s * X * (finiteBinaryYesIsometry s)ᴴ

theorem binaryYesFaceState_density {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) {X : ComplexMatrix d} (hX : IsMatrixDensity X) :
    IsMatrixDensity (binaryYesFaceState s X) := by
  refine ⟨hX.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [binaryYesFaceState, Matrix.trace_mul_cycle, finiteBinaryYesIsometry_isometry,
    Matrix.one_mul, hX.2]

theorem binaryYesFaceState_certain {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (X : ComplexMatrix d) :
    finiteBinaryProjection s * binaryYesFaceState s X = binaryYesFaceState s X := by
  unfold binaryYesFaceState finiteBinaryProjection
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc (finiteBinaryYesIsometry s) (finiteBinaryYesIsometry s)ᴴ,
    finiteBinaryYesIsometry_isometry, Matrix.mul_one]

theorem binaryYesFaceState_compression {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (X : ComplexMatrix d) :
    compressFirstBlock (binaryYesFaceState s X) = s.yes.root * X * s.yes.root := by
  have hleft : (firstBlockInclusion d)ᴴ * finiteBinaryYesIsometry s = s.yes.root := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, s.yes.root_hermitian] using
      congrArg Matrix.conjTranspose (finiteBinaryYesIsometry_inclusion s)
  unfold compressFirstBlock binaryYesFaceState
  calc
    _ = ((firstBlockInclusion d)ᴴ * finiteBinaryYesIsometry s) * X *
        ((finiteBinaryYesIsometry s)ᴴ * firstBlockInclusion d) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hleft, finiteBinaryYesIsometry_inclusion]

theorem binaryYesFaceState_not_first_corner {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) {X : ComplexMatrix d}
    (hX : IsMatrixDensity X) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hAX : A * X = a • X) :
    ∀ Y, binaryYesFaceState s X ≠ embedFirstBlock Y := by
  intro Y he
  have hcompress : compressFirstBlock (embedFirstBlock Y) = Y := by
    unfold compressFirstBlock embedFirstBlock
    calc
      _ = ((firstBlockInclusion d)ᴴ * firstBlockInclusion d) * Y *
          ((firstBlockInclusion d)ᴴ * firstBlockInclusion d) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [firstBlockInclusion_isometry, Matrix.one_mul, Matrix.mul_one]
  have hy : Y = a • X := by
    rw [← hcompress, ← he, binaryYesFaceState_compression,
      root_sandwich_of_eigenvalue s.yes ha hX.1.isHermitian hAX]
  have htrace : Matrix.trace (a • X) = 1 := by
    rw [← hy, ← trace_embedFirstBlock, ← he]
    exact (binaryYesFaceState_density s hX).2
  rw [Matrix.trace_smul, hX.2] at htrace
  change (a : ℂ) * 1 = 1 at htrace
  rw [mul_one] at htrace
  exact (ne_of_lt ha1) (congrArg Complex.re htrace)

/-- In the yes face the branch is the normalized original update whenever the
input lies in a positive eigenspace of the yes effect. -/
theorem binaryKrausDilation_branch_yesFace {d : ℕ} {I : Type*}
    (r : BinaryKrausRealization d I)
    (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
    (B : I → Bool → ComplexMatrix d) (C : I → Bool → ComplexMatrix (d + d))
    (i : I) {X Y : ComplexMatrix d} {a : ℝ} (ha : 0 < a) (hX : Xᴴ = X)
    (hAX : krausEffect (r.kraus i true) * X = a • X)
    (hY : krausAction (r.kraus i true) X = a • Y) :
    (binaryKrausDilation r s B C).branch i true (binaryYesFaceState (s i) X) =
      embedFirstBlock Y := by
  have hcomp : (finiteBinaryYesIsometry (s i))ᴴ * binaryYesFaceState (s i) X *
      finiteBinaryYesIsometry (s i) = X := by
    unfold binaryYesFaceState
    calc
      _ = ((finiteBinaryYesIsometry (s i))ᴴ * finiteBinaryYesIsometry (s i)) *
          X * ((finiteBinaryYesIsometry (s i))ᴴ * finiteBinaryYesIsometry (s i)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [finiteBinaryYesIsometry_isometry, Matrix.one_mul, Matrix.mul_one]
  have hs : (s i).yes.root * ((a⁻¹ : ℝ) • X) * (s i).yes.root = X := by
    rw [Matrix.mul_smul, Matrix.smul_mul, root_sandwich_of_eigenvalue (s i).yes ha hX hAX,
      smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  rw [binaryKrausDilation_branch]
  simp only [binaryOutcomeIsometry, ite_true, binaryOutcomeSupport]
  rw [hcomp, ← hs, completedKraus_factorization]
  congr 1
  rw [show ((a⁻¹ : ℝ) • X) = ((a⁻¹ : ℝ) : ℂ) • X by rfl]
  change rectangularKrausAction (r.kraus i true) (((a⁻¹ : ℝ) : ℂ) • X) = Y
  rw [rectangularKrausAction_smul,
    show rectangularKrausAction (r.kraus i true) X = (a : ℂ) • Y from hY,
    smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt ha), Complex.ofReal_one, one_smul]

/-- Exact two-block matrix of the yes-face lift of an eigenprojection. -/
theorem binaryYesFaceState_eigenprojection_formula {d : ℕ} {A X : ComplexMatrix d}
    (s : BinarySpectralSupport A) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hX : Xᴴ = X) (hXsq : X * X = X) (hAX : A * X = a • X) :
    let V := (Matrix.fromRows (Real.sqrt a • X) (Real.sqrt (1-a) • X)).submatrix
      (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d+d)).symm id
    binaryYesFaceState s X = V * Vᴴ := by
  have hc : (1 - A) * X = (1 - a) • X := by
    rw [Matrix.sub_mul, Matrix.one_mul, hAX, sub_smul, one_smul]
  have hleft : finiteBinaryYesIsometry s * X =
      (Matrix.fromRows (Real.sqrt a • X) (Real.sqrt (1-a) • X)).submatrix
        (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d+d)).symm id := by
    calc
      _ = (binaryYesIsometry s * X).submatrix
          (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d+d)).symm id :=
        (Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin d)) _).symm
      _ = _ := by
        rw [binaryYesIsometry, Matrix.fromRows_mul,
          positiveRoot_mul_of_eigenvalue _ ha hAX, positiveRoot_mul_of_eigenvalue _ (sub_pos.mpr ha1) hc]
  dsimp only
  rw [← hleft]
  simp only [binaryYesFaceState, Matrix.conjTranspose_mul, hX, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc X X, hXsq]

/-- The two yes-face lifts of a projection coincide when the corresponding yes
effects act there by the same strictly interior scalar. -/
theorem binaryYesFaceState_eq_of_common_eigenvalue {d : ℕ} {A D X : ComplexMatrix d}
    (s : BinarySpectralSupport A) (t : BinarySpectralSupport D)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hX : Xᴴ = X) (hXsq : X * X = X)
    (hAX : A * X = a • X) (hDX : D * X = a • X) :
    binaryYesFaceState s X = binaryYesFaceState t X :=
  (binaryYesFaceState_eigenprojection_formula s ha ha1 hX hXsq hAX).trans
    (binaryYesFaceState_eigenprojection_formula t ha ha1 hX hXsq hDX).symm

end AlbertSequential
