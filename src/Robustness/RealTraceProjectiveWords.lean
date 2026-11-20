/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.SharpDisturbance
public import HilbertTraceRealIdeal
public import BoundedWordEffects

@[expose] public section
noncomputable section
namespace AlbertSequential.HilbertTrace
open scoped InnerProductSpace
variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis B ℝ H)

def realTraceProjectiveModel (P : I → H →L[ℝ] H) (hP : ∀ i, IsStarProjection (P i))
    (X : signedFiniteTrace b) (hX : IsRealDensity b X) : HilbertProjectiveData I ℝ H where
  projection i := (operatorValue ℝ H).symm (P i)
  isStarProjection i := (operatorValue_isStarProjection ℝ H _).mp (hP i)
  state :=
    { toFun := fun T => signedTracePairing b (operatorValue ℝ H T.val) X
      map_add' := by
        intro S T
        change signedTracePairing b (operatorValue ℝ H S.val + operatorValue ℝ H T.val) X = _
        unfold signedTracePairing
        rw [← ((real_summable_tracePairing b (operatorValue ℝ H S.val) X).of_norm).tsum_add
          (real_summable_tracePairing b (operatorValue ℝ H T.val) X).of_norm]
        congr 1; funext i; simp [inner_add_left]
      map_smul' := by
        intro r T
        change signedTracePairing b (r • operatorValue ℝ H T.val) X = r * _
        unfold signedTracePairing
        rw [← tsum_mul_left]
        congr 1; funext i; simp [real_inner_smul_left] }
  normalized := hX.2
  positive T h := (real_signedTracePairing_nonneg_zero_iff b _ _ h hX.1).1

theorem real_sandwich_word (P : I → H →L[ℝ] H) (w : Word I) (X : signedFiniteTrace b) :
    SharpDisturbance.wordMap (fun q => realSandwich b (algebraicOutcome P q)) w X =
      realSandwich b (wordAmplitude P w) X := by
  induction w generalizing X with
  | nil =>
    apply Subtype.ext
    change X.val = wordAmplitude P [] * X.val * star (wordAmplitude P [])
    simp
  | cons q w ih =>
    change SharpDisturbance.wordMap _ w (realSandwich b (algebraicOutcome P q) X) = _
    rw [ih,wordAmplitude_cons]
    apply Subtype.ext
    change _ * (_ * X.val * _) * _ = (_*_) * X.val * star (_*_)
    simp only [star_mul,mul_assoc]

theorem realTraceProjectiveModel_probability (P : I → H →L[ℝ] H) (hP : ∀ i, IsStarProjection (P i))
    (X : signedFiniteTrace b) (hX : IsRealDensity b X) (w : Word I) :
    (realTraceProjectiveModel b P hP X hX).probability w =
      signedTrace b (SharpDisturbance.wordMap (fun q => realSandwich b (algebraicOutcome P q)) w X) := by
  rw [real_sandwich_word, signedTrace_realSandwich]
  change signedTracePairing b (operatorValue ℝ H (wordOperator _ w)) X = _
  rw [operatorValue_wordOperator_eq_star_mul, boundedWordAmplitude_eq_wordAmplitude]
  rfl

end AlbertSequential.HilbertTrace
