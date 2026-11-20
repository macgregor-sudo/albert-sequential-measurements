/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.RealSharpDisturbance
public import HilbertTraceQuaternionicIdeal

@[expose] public section
noncomputable section
namespace AlbertSequential.HilbertTrace
variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis B ℝ H) (S : RightQuaternionicHilbertStructure H)
local notation "Op" => S.toOperatorStructure.operatorAlgebra
local notation "Carrier" => quaternionicSignedFiniteTrace b S

def quaternionicTraceNorm (X : Carrier) : ℝ := realTraceNorm b (quaternionicCarrierInclusion b S X) / 4

theorem quaternionic_signedTrace_jordan_decomposition (X : Carrier) :
    ∃ U V : Carrier, U.val.IsPositive ∧ V.val.IsPositive ∧ X = U-V ∧
      quaternionicSignedTrace b S U + quaternionicSignedTrace b S V = quaternionicTraceNorm b S X := by
  let Y := quaternionicCarrierInclusion b S X
  let D := Classical.choose (realModulus_exists b Y)
  obtain ⟨hp,hs⟩ := Classical.choose_spec (realModulus_exists b Y)
  obtain ⟨u,v,hu,hv,he,ht⟩ := real_signedTrace_jordan_decomposition b Y D hp hs
  have h := congrArg (quaternionicAverage b S) he
  change quaternionicAverage b S (quaternionicCarrierInclusion b S X) = _ at h
  rw [quaternionicAverage_inclusion, map_sub] at h
  refine ⟨_,_,quaternionicAverage_positive b S u hu,quaternionicAverage_positive b S v hv,h,?_⟩
  change _ = (positiveTrace b D).toReal / 4
  linarith [quaternionicAverage_trace b S u, quaternionicAverage_trace b S v]

def quaternionicTraceProjectiveModel (P : I → Op) (hP : ∀ i, IsStarProjection (P i))
    (X : Carrier) (hX : IsQuaternionicDensity b S X) : QuaternionicProjectiveData I S.toOperatorStructure where
  projection := P
  isStarProjection := hP
  state :=
    { toFun := fun T => quaternionicTracePairing b S T.val X
      map_add' := by
        intro T U
        let Y := quaternionicCarrierInclusion b S X
        change (1/4 : ℝ) * signedTracePairing b (T.val.val + U.val.val) Y =
          1/4 * signedTracePairing b T.val.val Y + 1/4 * signedTracePairing b U.val.val Y
        rw [← mul_add]
        congr 1
        unfold signedTracePairing
        rw [← ((real_summable_tracePairing b T.val.val Y).of_norm).tsum_add
          (real_summable_tracePairing b U.val.val Y).of_norm]
        congr 1; funext i; simp [inner_add_left]
      map_smul' := by
        intro r T
        let Y := quaternionicCarrierInclusion b S X
        change (1/4 : ℝ) * signedTracePairing b (r • T.val.val) Y =
          r * (1/4 * signedTracePairing b T.val.val Y)
        rw [mul_left_comm]
        congr 1
        unfold signedTracePairing
        rw [← tsum_mul_left]
        congr 1; funext i; simp [real_inner_smul_left] }
  normalized := hX.2
  positive T h := (quaternionic_pairing_nonneg_zero_iff b S _ _ h hX.1).1

theorem quaternionic_sandwich_word (P : I → Op) (w : Word I) (X : Carrier) :
    SharpDisturbance.wordMap (fun q => quaternionicSandwich b S (algebraicOutcome P q)) w X =
      quaternionicSandwich b S (wordAmplitude P w) X := by
  induction w generalizing X with
  | nil =>
    apply Subtype.ext
    change X.val = (wordAmplitude P []).val * X.val * star (wordAmplitude P []).val
    simp
  | cons q w ih =>
    change SharpDisturbance.wordMap _ w (quaternionicSandwich b S (algebraicOutcome P q) X) = _
    rw [ih,wordAmplitude_cons]
    apply Subtype.ext
    change _ * (_ * X.val * _) * _ = (_*_) * X.val * star (_*_)
    simp only [star_mul,mul_assoc]

theorem quaternionicTraceProjectiveModel_probability (P : I → Op) (hP : ∀ i, IsStarProjection (P i))
    (X : Carrier) (hX : IsQuaternionicDensity b S X) (w : Word I) :
    (quaternionicTraceProjectiveModel b S P hP X hX).state ((quaternionicTraceProjectiveModel b S P hP X hX).wordEffect w) =
      quaternionicSignedTrace b S (SharpDisturbance.wordMap (fun q => quaternionicSandwich b S (algebraicOutcome P q)) w X) := by
  rw [quaternionic_sandwich_word, signedTrace_quaternionicSandwich]
  rfl

end AlbertSequential.HilbertTrace
