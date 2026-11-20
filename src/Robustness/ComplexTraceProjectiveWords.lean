/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.SharpDisturbance
public import HilbertTraceComplexIdeal
public import BoundedWordEffects

@[expose] public section
noncomputable section
namespace AlbertSequential.HilbertTrace
open scoped InnerProductSpace
variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis B ℂ H)

def complexTraceProjectiveModel (P : I → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (X : signedFiniteTrace b) (hX : IsComplexDensity b X) : HilbertProjectiveData I ℂ H where
  projection i := (operatorValue ℂ H).symm (P i)
  isStarProjection i := (operatorValue_isStarProjection ℂ H _).mp (hP i)
  state :=
    { toFun := fun T => signedTracePairing b (operatorValue ℂ H T.val) X
      map_add' := by
        intro S T
        change signedTracePairing b (operatorValue ℂ H S.val + operatorValue ℂ H T.val) X = _
        unfold signedTracePairing
        rw [← ((complex_summable_tracePairing b (operatorValue ℂ H S.val) X).of_norm).tsum_add
          (complex_summable_tracePairing b (operatorValue ℂ H T.val) X).of_norm]
        congr 1; funext i; simp [inner_add_left]
      map_smul' := by
        intro r T
        change signedTracePairing b (r • operatorValue ℂ H T.val) X = r * _
        unfold signedTracePairing
        rw [← tsum_mul_left]
        congr 1; funext i; simp only [ContinuousLinearMap.smul_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r, inner_smul_real_left]
        simp }
  normalized := hX.2
  positive T h := (complex_signedTracePairing_nonneg_zero_iff b _ _ h hX.1).1

theorem complex_sandwich_word (P : I → H →L[ℂ] H) (w : Word I) (X : signedFiniteTrace b) :
    SharpDisturbance.wordMap (fun q => complexSandwich b (algebraicOutcome P q)) w X =
      complexSandwich b (wordAmplitude P w) X := by
  induction w generalizing X with
  | nil =>
    apply Subtype.ext
    change X.val = wordAmplitude P [] * X.val * star (wordAmplitude P [])
    simp
  | cons q w ih =>
    change SharpDisturbance.wordMap _ w (complexSandwich b (algebraicOutcome P q) X) = _
    rw [ih,wordAmplitude_cons]
    apply Subtype.ext
    change _ * (_ * X.val * _) * _ = (_*_) * X.val * star (_*_)
    simp only [star_mul,mul_assoc]

theorem complexTraceProjectiveModel_probability (P : I → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (X : signedFiniteTrace b) (hX : IsComplexDensity b X) (w : Word I) :
    (complexTraceProjectiveModel b P hP X hX).probability w =
      signedTrace b (SharpDisturbance.wordMap (fun q => complexSandwich b (algebraicOutcome P q)) w X) := by
  rw [complex_sandwich_word, signedTrace_complexSandwich]
  change signedTracePairing b (operatorValue ℂ H (wordOperator _ w)) X = _
  rw [operatorValue_wordOperator_eq_star_mul, boundedWordAmplitude_eq_wordAmplitude]
  rfl

end AlbertSequential.HilbertTrace
