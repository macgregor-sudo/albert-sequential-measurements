/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ReducedSharpDilationSemantics
public import RealSharpDilation

/-! Supported resets yield repeatability for the same reduced sharp dilation.
The auxiliary output is chosen from a fixed positive source input. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential

open Matrix
open scoped ComplexOrder

theorem sharpFrameChannelKraus_supported {d D : ℕ} (K : List (ComplexMatrix d))
    (s : FiniteSpectralSupport (krausEffect K)) {J : Matrix (Fin D) (Fin d) ℂ}
    {R : ComplexMatrix D} (f : SharpDilationChannelFrame J R s.root) (B : ComplexMatrix d)
    (hJ : Jᴴ * J = 1) (hRh : Rᴴ = R) (hRR : R * R = R)
    (hK : ∀ Y, Y.PosSemidef → krausEffect K * krausAction K Y = krausAction K Y)
    (hB : krausEffect K * (B * Bᴴ) = B * Bᴴ) (Z : ComplexMatrix D) (hZ : Z.PosSemidef) :
    krausAction (sharpFrameChannelKraus K s f B) (R * Z * R) =
      R * krausAction (sharpFrameChannelKraus K s f B) (R * Z * R) * R := by
  let Y := krausAction (completedKraus K s B) (f.frameᴴ * Z * f.frame)
  let c := Matrix.trace ((R - f.frame * f.frameᴴ) * Z)
  have hYin : (f.frameᴴ * Z * f.frame).PosSemidef := hZ.conjTranspose_mul_mul_same f.frame
  have hY : Y.PosSemidef := krausAction_positive _ hYin
  have hYs : krausEffect K * Y = Y :=
    completedKraus_supported K s B (krausEffect K) hK hB hYin
  have hcompress := sharpFrameChannelKraus_projection_compression K s f
  have hleft : R * (J * Y * Jᴴ) * R = J * Y * Jᴴ :=
    projection_compression_supported_output R J Y hRh hRR hJ hY.isHermitian (hcompress ▸ hYs)
  have hright : R * (J * (B * Bᴴ) * Jᴴ) * R = J * (B * Bᴴ) * Jᴴ :=
    projection_compression_supported_output R J (B * Bᴴ) hRh hRR hJ
      (by simp) (hcompress ▸ hB)
  rw [sharpFrameChannelKraus_branch K s f B hJ hRh hRR]
  change sharpFrameEmbed J (Y + c • (B * Bᴴ)) = R * sharpFrameEmbed J (Y + c • (B * Bᴴ)) * R
  simp only [sharpFrameEmbed, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    hleft, hright]

theorem reducedSharpDilationOfFrames_repeatable {d D : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (J : Matrix (Fin D) (Fin d) ℂ) (P : X → ComplexMatrix D)
    (s : ∀ x a, FiniteSpectralSupport (krausEffect (r.kraus x a)))
    (f : ∀ x a, SharpDilationChannelFrame J (sharpOutcomeProjection (P x) a) (s x a).root)
    (B : X → Bool → ComplexMatrix d) (hJ : Jᴴ * J = 1)
    (hP : ∀ x, (P x)ᴴ = P x ∧ P x * P x = P x)
    (hzero : ∀ x a, krausEffect (r.kraus x a) = 0 → sharpOutcomeProjection (P x) a = 0)
    (hB : ∀ x a, krausEffect (r.kraus x a) ≠ 0 →
      B x a * (B x a)ᴴ = normalizedKrausOutput (r.kraus x a))
    (h : HasCertaintySupportedOutputs r) :
    IsRepeatableReducedSharpDilation (reducedSharpDilationOfFrames r J P s f B) := by
  intro x a Z hZ
  let R := sharpOutcomeProjection (P x) a
  let K := sharpFrameChannelKraus (r.kraus x a) (s x a) (f x a) (B x a)
  change krausAction K (R * Z * R) = R * krausAction K (R * Z * R) * R
  by_cases he : krausEffect (r.kraus x a) = 0
  · rw [show R = 0 from hzero x a he, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul,
      Matrix.zero_mul, krausAction_zero_input]
  · have hBs : krausEffect (r.kraus x a) * (B x a * (B x a)ᴴ) = B x a * (B x a)ᴴ := by
      rw [hB x a he]
      exact normalizedKrausOutput_supported _ _ (r.outcome_supported h x a)
    exact sharpFrameChannelKraus_supported _ _ (f x a) _ hJ
      (sharpOutcomeProjection_orthogonal _ (hP x) a).1 (sharpOutcomeProjection_orthogonal _ (hP x) a).2
      (r.outcome_supported h x a) hBs Z hZ

/-- Transport the actual channels for a chosen frame family, including the same
choice of real data and conditional all-state repeatability. -/
theorem exists_reducedSharpDilation_of_frames {d D : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (J : Matrix (Fin D) (Fin d) ℂ) (P : X → ComplexMatrix D)
    (s : ∀ x a, FiniteSpectralSupport (krausEffect (r.kraus x a)))
    (f : ∀ x a, SharpDilationChannelFrame J (sharpOutcomeProjection (P x) a) (s x a).root)
    (hJ : Jᴴ * J = 1) (hP : ∀ x, (P x)ᴴ = P x ∧ P x * P x = P x)
    (hzero : ∀ x a, krausEffect (r.kraus x a) = 0 → sharpOutcomeProjection (P x) a = 0)
    (hJreal : ∀ i j, (J i j).im = 0)
    (hreal : IsRealKrausRealization r →
      (∀ x, HasRealEntries (P x)) ∧
      (∀ x a i j, ((f x a).frame i j).im = 0) ∧
      (∀ x a, HasRealEntries (s x a).inverseRoot ∧ HasRealEntries (s x a).support)) :
    ∃ M : ReducedSharpDilationData d D X, M.inclusion = J ∧ M.projection = P ∧
      IsReducedSharpDilation r M ∧
      (HasCertaintySupportedOutputs r → IsRepeatableReducedSharpDilation M) ∧
      (IsRealKrausRealization r → IsRealReducedSharpDilation M) := by
  classical
  let tau (x : X) (a : Bool) : ComplexMatrix d :=
    if krausEffect (r.kraus x a) = 0 then r.initial else normalizedKrausOutput (r.kraus x a)
  have htau (x : X) (a : Bool) : IsMatrixDensity (tau x a) := by
    unfold tau
    split
    · exact r.density
    · exact normalizedKrausOutput_density _ (by assumption)
  have htaur (hr : IsRealKrausRealization r) (x : X) (a : Bool) : HasRealEntries (tau x a) := by
    unfold tau
    split
    · exact hr.1
    · exact normalizedKrausOutput_real _ (hr.2 x a)
  have hfactors (x : X) (a : Bool) : ∃ B : ComplexMatrix d,
      B * Bᴴ = tau x a ∧ (IsRealKrausRealization r → HasRealEntries B) := by
    by_cases hr : IsRealKrausRealization r
    · obtain ⟨B, hBr, hB⟩ := exists_real_positiveFactor (htau x a).1 (htaur hr x a)
      exact ⟨B, hB, fun _ => hBr⟩
    · obtain ⟨B, hB⟩ := exists_complexPositiveFactor (htau x a).1
      exact ⟨B, hB.symm, fun h => False.elim (hr h)⟩
  choose B hB hBr using hfactors
  have htrace (x : X) (a : Bool) : Matrix.trace (B x a * (B x a)ᴴ) = 1 := by
    rw [hB]
    exact (htau x a).2
  refine ⟨reducedSharpDilationOfFrames r J P s f B, rfl, rfl,
    reducedSharpDilationOfFrames_correct r J P s f B hJ hP htrace, ?_, ?_⟩
  · apply reducedSharpDilationOfFrames_repeatable r J P s f B hJ hP hzero
    intro x a he
    rw [hB]
    simp [tau, he]
  · intro hr
    obtain ⟨hPr, hVr, hsr⟩ := hreal hr
    exact reducedSharpDilationOfFrames_real r J P s f B hr hJreal hPr hVr hsr
      (fun x a => hBr x a hr)

end AlbertSequential
