/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ProjectionSupportTransfer

/-! Nonzero branches provide their own normalized output for channel completion.
Normalization concerns a fixed positive test input, never a history probability. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential
open Matrix

theorem nonzero_krausEffect_trace_re_pos {d : ℕ} (K : List (ComplexMatrix d))
    (hK : krausEffect K ≠ 0) : 0 < (Matrix.trace (krausEffect K)).re := by
  have hp := (krausEffect_positive K).trace_nonneg
  obtain ⟨hr, hi⟩ := Complex.nonneg_iff.mp hp
  have hn : (Matrix.trace (krausEffect K)).re ≠ 0 := by
    intro h
    apply hK
    apply (positive_trace_zero_iff (krausEffect_positive K)).mp
    apply Complex.ext
    · exact h
    · exact hi.symm
  exact lt_of_le_of_ne hr (Ne.symm hn)

def normalizedKrausOutput {d : ℕ} (K : List (ComplexMatrix d)) : ComplexMatrix d :=
  (Matrix.trace (krausEffect K)).re⁻¹ • krausAction K 1

theorem normalizedKrausOutput_density {d : ℕ} (K : List (ComplexMatrix d))
    (hK : krausEffect K ≠ 0) : IsMatrixDensity (normalizedKrausOutput K) := by
  have hp := nonzero_krausEffect_trace_re_pos K hK
  have htrace : Matrix.trace (krausEffect K) =
      ((Matrix.trace (krausEffect K)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (Complex.nonneg_iff.mp (krausEffect_positive K).trace_nonneg).2.symm
  refine ⟨(krausAction_positive K Matrix.PosSemidef.one).smul (inv_nonneg.mpr hp.le), ?_⟩
  rw [normalizedKrausOutput, Matrix.trace_smul, trace_krausAction, Matrix.mul_one, htrace]
  simp only [Complex.ofReal_re, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hp),
    Complex.ofReal_one]

theorem normalizedKrausOutput_supported {d : ℕ} (K : List (ComplexMatrix d))
    (A : ComplexMatrix d)
    (h : ∀ Y, Y.PosSemidef → A * krausAction K Y = krausAction K Y) :
    A * normalizedKrausOutput K = normalizedKrausOutput K := by
  rw [normalizedKrausOutput, Matrix.mul_smul, h 1 Matrix.PosSemidef.one]

theorem completedKraus_supported {d : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) (B A : ComplexMatrix d)
    (h : ∀ Y, Y.PosSemidef → A * krausAction K Y = krausAction K Y)
    (hB : A * (B * Bᴴ) = B * Bᴴ)
    {Y : ComplexMatrix d} (hY : Y.PosSemidef) :
    A * krausAction (completedKraus K s B) Y =
      krausAction (completedKraus K s B) Y := by
  have hy : (s.inverseRoot * Y * s.inverseRoot).PosSemidef := by
    simpa only [s.inverse_hermitian] using hY.mul_mul_conjTranspose_same s.inverseRoot
  rw [completedKraus_action, Matrix.mul_add, h _ hy, Matrix.mul_smul, hB]

theorem BinaryKrausRealization.outcome_supported {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (h : HasCertaintySupportedOutputs r)
    (x : X) (a : Bool) (Y : ComplexMatrix d) (hY : Y.PosSemidef) :
    krausEffect (r.kraus x a) * krausAction (r.kraus x a) Y =
      krausAction (r.kraus x a) Y := by
  cases a with
  | true => exact (h x Y hY).1
  | false =>
      rw [r.no_effect, Matrix.sub_mul, Matrix.one_mul, (h x Y hY).2, sub_zero]

#print axioms normalizedKrausOutput_density
#print axioms completedKraus_supported
end AlbertSequential

