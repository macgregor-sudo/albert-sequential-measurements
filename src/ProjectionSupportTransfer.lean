/- SPDX-License-Identifier: Apache-2.0 -/
module
public import BinaryKrausDilation

/-! Support transfer through an orthogonal projection compression.
The key kernel argument is a zero Gram square, not a new spectral calculation. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential
open Matrix

theorem projection_compression_kernel {d D : ℕ}
    (P : ComplexMatrix D) (ι : Matrix (Fin D) (Fin d) ℂ) (Y : ComplexMatrix d)
    (hP : Pᴴ = P) (hPP : P * P = P)
    (hY : (ιᴴ * P * ι) * Y = 0) : P * ι * Y = 0 := by
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  calc
    (P * ι * Y)ᴴ * (P * ι * Y) =
        Yᴴ * ιᴴ * (P * P) * ι * Y := by
      simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
    _ = Yᴴ * ((ιᴴ * P * ι) * Y) := by
      rw [hPP]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hY, Matrix.mul_zero]

theorem projection_compression_one {d D : ℕ}
    (P : ComplexMatrix D) (ι : Matrix (Fin D) (Fin d) ℂ) (Y : ComplexMatrix d)
    (hP : Pᴴ = P) (hPP : P * P = P) (hι : ιᴴ * ι = 1)
    (hY : (ιᴴ * P * ι) * Y = Y) : P * ι * Y = ι * Y := by
  have hQc : ιᴴ * (1 - P) * ι = 1 - ιᴴ * P * ι := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hι]
  have hQY : (ιᴴ * (1 - P) * ι) * Y = 0 := by
    rw [hQc, Matrix.sub_mul, Matrix.one_mul, hY, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hz := projection_compression_kernel (1-P) ι Y (by simp [hP]) hQQ hQY
  have hz' : ι * Y = P * ι * Y := by
    simpa only [Matrix.sub_mul, Matrix.one_mul, sub_mul, sub_eq_zero] using hz
  exact hz'.symm

theorem projection_compression_supported_output {d D : ℕ}
    (P : ComplexMatrix D) (ι : Matrix (Fin D) (Fin d) ℂ) (Y : ComplexMatrix d)
    (hP : Pᴴ = P) (hPP : P * P = P) (hι : ιᴴ * ι = 1)
    (hYh : Yᴴ = Y) (hY : (ιᴴ * P * ι) * Y = Y) :
    P * (ι * Y * ιᴴ) * P = ι * Y * ιᴴ := by
  have hl := projection_compression_one P ι Y hP hPP hι hY
  have hr : Y * ιᴴ * P = Y * ιᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hP, hYh, Matrix.mul_assoc] using congrArg Matrix.conjTranspose hl
  calc
    _ = (P * ι * Y) * ιᴴ * P := by simp only [Matrix.mul_assoc]
    _ = ι * (Y * ιᴴ * P) := by rw [hl]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hr]; simp only [Matrix.mul_assoc]

theorem krausAction_positive {d : ℕ} (K : List (ComplexMatrix d))
    {Y : ComplexMatrix d} (hY : Y.PosSemidef) : (krausAction K Y).PosSemidef := by
  induction K with
  | nil => exact Matrix.PosSemidef.zero
  | cons V K ih =>
      exact (hY.mul_mul_conjTranspose_same V).add ih

/-- PSD trace zero is exactly the zero matrix, including empty index types. -/
theorem positive_trace_zero_iff {d : ℕ} {Y : ComplexMatrix d} (hY : Y.PosSemidef) :
    Matrix.trace Y = 0 ↔ Y = 0 := by
  obtain ⟨B, rfl⟩ := exists_complexPositiveFactor hY
  rw [Matrix.trace_mul_conjTranspose_self_eq_zero_iff,
    Matrix.self_mul_conjTranspose_eq_zero]

#print axioms projection_compression_supported_output
#print axioms positive_trace_zero_iff
end AlbertSequential

