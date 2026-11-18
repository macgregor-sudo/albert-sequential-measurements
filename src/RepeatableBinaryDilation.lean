/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NormalizedKrausOutput

/-! Supported reset outputs make the nondegenerate doubled construction
repeatable. The zero/unit-effect projection cases remain separate. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential
open Matrix

theorem binaryOutcomeProjection_compression {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (x : X)
    (s : BinarySpectralSupport (krausEffect (r.kraus x true))) (a : Bool) :
    compressFirstBlock (if a then finiteBinaryProjection s else 1-finiteBinaryProjection s) =
      krausEffect (r.kraus x a) := by
  cases a with
  | true => exact finiteBinaryProjection_compression s
  | false =>
      change (firstBlockInclusion d)ᴴ * (1-finiteBinaryProjection s) *
          firstBlockInclusion d = _
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
        firstBlockInclusion_isometry, r.no_effect]
      exact congrArg (fun A => 1-A) (finiteBinaryProjection_compression s)

theorem binaryKrausDilation_repeatable_of_supported_resets {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
    (B : X → Bool → ComplexMatrix d) (C : X → Bool → ComplexMatrix (d+d))
    (hs : HasCertaintySupportedOutputs r)
    (hB : ∀ x a, krausEffect (r.kraus x a) * (B x a * (B x a)ᴴ) =
      B x a * (B x a)ᴴ) :
    IsRepeatableSharpDilation (binaryKrausDilation r s B C) := by
  intro x a Z hZ
  let V := binaryOutcomeIsometry (s x) a
  let K := completedKraus (r.kraus x a) (binaryOutcomeSupport r x (s x) a) (B x a)
  let Y := krausAction K (Vᴴ * Z * V)
  have hinput : (Vᴴ * Z * V).PosSemidef := hZ.conjTranspose_mul_mul_same V
  have hY : Y.PosSemidef := krausAction_positive K hinput
  have hsupport : krausEffect (r.kraus x a) * Y = Y :=
    completedKraus_supported _ _ _ _ (r.outcome_supported hs x a) (hB x a) hinput
  let P := (binaryKrausDilation r s B C).outcomeProjection x a
  have hPh : Pᴴ = P := by
    cases a <;> simp [P, SharpDilationData.outcomeProjection, binaryKrausDilation,
      finiteBinaryProjection_hermitian]
  have hPP : P * P = P :=
    outcomeProjection_idempotent _ (fun i => finiteBinaryProjection_idempotent (s i)) x a
  have hPc : compressFirstBlock P = krausEffect (r.kraus x a) :=
    binaryOutcomeProjection_compression r x (s x) a
  have hfull : P * embedFirstBlock Y * P = embedFirstBlock Y :=
    projection_compression_supported_output P (firstBlockInclusion d) Y
      hPh hPP (firstBlockInclusion_isometry d) hY.isHermitian (by
        change compressFirstBlock P * Y = Y
        rw [hPc, hsupport])
  change (binaryKrausDilation r s B C).branch x a Z =
      P * (binaryKrausDilation r s B C).branch x a Z * P
  rw [binaryKrausDilation_branch]
  exact hfull.symm

#print axioms binaryKrausDilation_repeatable_of_supported_resets
end AlbertSequential

