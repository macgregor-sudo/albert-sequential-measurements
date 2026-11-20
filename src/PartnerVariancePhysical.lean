/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PartnerVarianceTraceBinding
public import ScheduleMatchingSectorMatrices

/-! The variance on the two literal six-dimensional complex sector realizations. -/
@[expose] public section
noncomputable section

open scoped Matrix ComplexOrder

namespace AlbertSequential.LengthSeven

open MatchingModels

def horizonMSectorParameter (s : Bool) : ℝ :=
  if s then (Real.sqrt 2)⁻¹ else -(Real.sqrt 2)⁻¹

theorem horizonMSectorParameter_sq (s : Bool) :
    horizonMSectorParameter s ^ 2 = 1 / 2 := by
  cases s <;> simp [horizonMSectorParameter]

/-- The actual complex sector projectors with their normalized trace state. -/
def horizonMVarianceModel (s : Bool) :
    AlgebraicProjectiveData (Fin 4) (Matrix (Fin 6) (Fin 6) ℂ) where
  projection := horizonSectorMatrix (Real.sqrt 2) (horizonMSectorParameter s)
  idempotent := horizonSectorMatrix_idempotent _ _ (horizonMSectorParameter_sq s)
  selfAdjoint := fun i => (horizonSectorMatrix_hermitian _ _ i).eq
  state := (1 / 6 : ℝ) •
    (Complex.reCLM.toLinearMap.comp (Matrix.traceLinearMap (Fin 6) ℝ ℂ))
  state_unit := by
    change (1 / 6 : ℝ) * (Matrix.trace (1 : Matrix (Fin 6) (Fin 6) ℂ)).re = 1
    norm_num
  state_star X := by
    change (1 / 6 : ℝ) * (Matrix.trace (star X)).re = (1 / 6 : ℝ) * (Matrix.trace X).re
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
  state_positive X := by
    change 0 ≤ (1 / 6 : ℝ) * (Matrix.trace (star X * X)).re
    apply mul_nonneg (by norm_num)
    rw [Matrix.star_eq_conjTranspose]
    exact (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

set_option maxHeartbeats 500000 in
theorem horizonMVarianceModel_matches (s : Bool) :
    (horizonMVarianceModel s).Matches (horizonMSector s) ((1 / 3 : ℝ) • albertUnit) := by
  intro w
  change (1 / 6 : ℝ) * (Matrix.trace
    (wordOperator (horizonSectorMatrix (Real.sqrt 2) (horizonMSectorParameter s)) w)).re = _
  exact horizonSectorMatrix_probability (Real.sqrt 2) (horizonMSectorParameter s) w

/-- The norm square of the printed alternating vector on each actual sector's
conditioned walk space. -/
theorem horizonMVarianceModel_printedPhi (s : Bool) :
    ∃ h : 0 < (horizonMVarianceModel s).probability [(0, true)],
      let W := WalkForm.ofAlgebraic (horizonMVarianceModel s) h
      W.form (printedPhi W) (printedPhi W) = 788 / 729 := by
  have hatom : ∀ i, IsAtom (horizonMSector s i) :=
    horizonQuaternionicSector_isAtom _ _ (horizonMSectorParameter_sq s)
  obtain ⟨h, hgram⟩ := printedGram_e3 (horizonMVarianceModel s) (horizonMSector s) hatom
    (fun w _ _ => horizonMVarianceModel_matches s w)
  exact ⟨h, (printedPhi_form _ hgram).trans (printedPhiValue_M_partner s)⟩

end AlbertSequential.LengthSeven
