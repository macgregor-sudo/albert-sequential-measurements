/- SPDX-License-Identifier: Apache-2.0 -/
module
public import HilbertTraceQuaternionicNorm
public import HilbertTraceCalibrationRounding
public import Robustness.OperatorTraceCalibration

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace

namespace AlbertSequential.HilbertTrace

section Common
variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
    (b : HilbertBasis ι 𝕜 H)

def signedTracePairingLeftLinear (X : signedFiniteTrace b)
    (hs : ∀ A : H →L[𝕜] H, Summable (fun i => RCLike.re ⟪A (X.val (b i)), b i⟫_𝕜)) :
    (H →L[𝕜] H) →ₗ[ℝ] ℝ where
  toFun A := signedTracePairing b A X
  map_add' A B := by
    unfold signedTracePairing
    rw [← (hs A).tsum_add (hs B)]
    refine tsum_congr fun i => ?_
    rw [add_apply, inner_add_left, map_add]
  map_smul' r A := by
    change (∑' i, RCLike.re ⟪(r • A) (X.val (b i)), b i⟫_𝕜) =
      r * ∑' i, RCLike.re ⟪A (X.val (b i)), b i⟫_𝕜
    rw [← (hs A).tsum_mul_left r]
    refine tsum_congr fun i => ?_
    rw [← algebraMap_smul 𝕜 r A, smul_apply, inner_smul_left,
      RCLike.conj_ofReal, RCLike.re_ofReal_mul]

end Common

section Real
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H)

local notation "T" => SignedTraceMassData.toTraceBaseNormData (realSignedTraceMass b)

def realOperatorTraceData : OperatorTraceData (A := H →L[ℝ] H) T where
  val := (signedFiniteTrace b).subtype
  injective := Subtype.val_injective
  sandwich := realSandwich b
  val_sandwich _ _ := rfl
  sandwich_positive := realSandwich_positive b
  pairing X := signedTracePairingLeftLinear b X (fun A => (real_summable_tracePairing b A X).of_norm)
  trace_sandwich := signedTrace_realSandwich b

def RealInstrument.traceNormInstrument (M : RealInstrument b) : PositiveBinaryInstrument T where
  branch k := if k then M.branchOne else M.branchZero
  positive := by
    intro k x hx
    cases k
    · exact M.zero_positive x hx
    · exact M.one_positive x hx
  normalized := M.trace_preserving

end Real

section Complex
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H)

local notation "T" => SignedTraceMassData.toTraceBaseNormData (complexSignedTraceMass b)

def complexOperatorTraceData : OperatorTraceData (A := H →L[ℂ] H) T where
  val := (signedFiniteTrace b).subtype
  injective := Subtype.val_injective
  sandwich := complexSandwich b
  val_sandwich _ _ := rfl
  sandwich_positive := complexSandwich_positive b
  pairing X := signedTracePairingLeftLinear b X (fun A => (complex_summable_tracePairing b A X).of_norm)
  trace_sandwich := signedTrace_complexSandwich b

def ComplexInstrument.traceNormInstrument (M : ComplexInstrument b) : PositiveBinaryInstrument T where
  branch k := if k then M.branchOne else M.branchZero
  positive := by
    intro k x hx
    cases k
    · exact M.zero_positive x hx
    · exact M.one_positive x hx
  normalized := M.trace_preserving

end Complex

section Quaternionic
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H)

local notation "T" => SignedTraceMassData.toTraceBaseNormData (quaternionicSignedTraceMass b S)
local notation "Carrier" => quaternionicSignedFiniteTrace b S
local notation "Op" => S.toOperatorStructure.operatorAlgebra

def quaternionicOperatorTraceData : OperatorTraceData (A := Op) T where
  val := {
    toFun X := ⟨(show Carrier from X).val, (show Carrier from X).property.2⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  injective := by
    intro X Y h
    have hv := congrArg (fun A : Op => A.val) h
    exact Subtype.ext hv
  sandwich := quaternionicSandwich b S
  val_sandwich _ _ := rfl
  sandwich_positive := quaternionicSandwich_positive b S
  pairing X :=
    let Y := quaternionicCarrierInclusion b S X
    (1 / 4 : ℝ) • (signedTracePairingLeftLinear b Y
      (fun A => (real_summable_tracePairing b A Y).of_norm)).comp
        S.toOperatorStructure.operatorAlgebra.val.toLinearMap
  trace_sandwich := signedTrace_quaternionicSandwich b S

def QuaternionicInstrument.traceNormInstrument
    (M : QuaternionicInstrument b S) : PositiveBinaryInstrument T where
  branch k := if k then M.branchOne else M.branchZero
  positive := by
    intro k x hx
    cases k
    · exact M.zero_positive x hx
    · exact M.one_positive x hx
  normalized := M.trace_preserving

end Quaternionic
end AlbertSequential.HilbertTrace
