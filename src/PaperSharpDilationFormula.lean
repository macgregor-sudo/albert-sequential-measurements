/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompletelyPositiveFactorization
public import RealSupportedSharpDilation

/-! The displayed finite CP channel factor and the real-data version of the
doubled sharp dilation, stated for ordinary complex-linear CP maps. -/
set_option autoImplicit false
@[expose] public section
noncomputable section
open scoped Matrix ComplexOrder

namespace AlbertSequential

private theorem matrixMapEffect_eq_kraus {d : ℕ}
    (E : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d) (K : List (ComplexMatrix d))
    (hK : ∀ Y, E Y = krausAction K Y) :
    matrixMapEffect E = krausEffect K := by
  have h (Y : ComplexMatrix d) : choiAction (linearMapChoi E) Y = krausAction K Y := by
    rw [choiAction_linearMapChoi, hK]
  rw [matrixMapEffect, choi_kraus_effect_binding _ K h, Matrix.transpose_transpose]

/-- The printed factor channel for a supplied density, as a complex-linear
completely positive trace-preserving map on every input. -/
theorem exists_displayed_completelyPositive_channel_factorization {d : ℕ}
    (E : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d)
    (hE : IsCompletelyPositiveMatrixMap E) (τ : ComplexMatrix d) (hτ : IsMatrixDensity τ) :
    ∃ (s : FiniteSpectralSupport (matrixMapEffect E)) (F : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d),
      IsCompletelyPositiveMatrixMap F ∧
      (∀ Y, Matrix.trace (F Y) = Matrix.trace Y) ∧
      (∀ Y, F Y = E (s.inverseRoot * Y * s.inverseRoot) +
        Matrix.trace ((1 - s.support) * Y) • τ) ∧
      (∀ X, E X = F (s.root * X * s.root)) := by
  obtain ⟨K, hK⟩ := (choi_positive_iff_kraus (linearMapChoi E)).mp
    ((linearMapChoi_positive_iff E).mpr hE)
  have h (Y : ComplexMatrix d) : E Y = krausAction K Y :=
    (choiAction_linearMapChoi E Y).symm.trans (hK Y)
  rw [matrixMapEffect_eq_kraus E K h]
  obtain ⟨B, hB⟩ := exists_complexPositiveFactor hτ.1
  let s := finiteSpectralSupport (krausEffect_positive K)
  let L := completedKraus K s B
  let F := choiLinearMap (krausChoi L)
  have hF (Y : ComplexMatrix d) : F Y = krausAction L Y := krausChoi_action L Y
  have hL : krausEffect L = 1 := completedKraus_effect K s B (hB ▸ hτ.2)
  refine ⟨s, F, (choi_positive_iff_completelyPositive (krausChoi L)).mp (krausChoi_positive L),
    (choi_trace_preservation_iff (krausChoi L)).mp ?_, ?_, ?_⟩
  · rw [krausChoi_outputTrace, hL, Matrix.transpose_one]
  · intro Y
    rw [hF, h, hB]
    exact completedKraus_action K s B Y
  · intro X
    rw [h, hF, completedKraus_factorization]

/-- The complementary trace term in each of the two displayed doubled-space
channels, before sandwiching with its sharp outcome projection. -/
theorem binaryKrausDilation_channel_action {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
    (B : X → Bool → ComplexMatrix d) (C : X → Bool → ComplexMatrix (d+d))
    (x : X) (a : Bool) (Z : ComplexMatrix (d+d)) :
    let V := binaryOutcomeIsometry (s x) a
    let L := completedKraus (r.kraus x a) (binaryOutcomeSupport r x (s x) a) (B x a)
    let P := (binaryKrausDilation r s B C).outcomeProjection x a
    krausAction ((binaryKrausDilation r s B C).channelKraus x a) Z =
      embedFirstBlock (krausAction L (Vᴴ * Z * V)) +
        Matrix.trace ((1 - P) * Z) • (C x a * (C x a)ᴴ) := by
  dsimp only [binaryKrausDilation, SharpDilationData.outcomeProjection]
  rw [isometricCompletedKraus_action _ _ _ _ _ (binaryOutcomeIsometry_isometry (s x) a),
    binaryOutcomeIsometry_range]
  rfl

/-- Real initial matrix and real Kraus lists for the ordinary CP branch maps. -/
def HasRealCPBranchKraus {d : ℕ} {X : Type*} (ρ : ComplexMatrix d)
    (E : X → Bool → ComplexMatrix d →ₗ[ℂ] ComplexMatrix d) : Prop :=
  HasRealEntries ρ ∧
    ∀ x a, ∃ K : List (ComplexMatrix d), (∀ Y, E x a Y = krausAction K Y) ∧
      ∀ V ∈ K, HasRealEntries V

/-- The same sharp dilation handles the all-input simulation, the support
hypothesis for repeatability, and the real-data clause for an ordinary CP menu. -/
theorem exists_completelyPositive_same_choice_sharpDilation {d : ℕ} {X : Type*}
    (ρ : ComplexMatrix d) (hρ : IsMatrixDensity ρ)
    (E : X → Bool → ComplexMatrix d →ₗ[ℂ] ComplexMatrix d)
    (hE : ∀ x a, IsCompletelyPositiveMatrixMap (E x a))
    (hTP : ∀ x Y, Matrix.trace (E x true Y + E x false Y) = Matrix.trace Y) :
    ∃ (r : BinaryKrausRealization d X) (s : SharpDilationData d X),
      r.initial = ρ ∧ (∀ x a Y, krausAction (r.kraus x a) Y = E x a Y) ∧
      IsSharpDilation r s ∧
      (∀ x, compressFirstBlock (s.projection x) = matrixMapEffect (E x true)) ∧
      (∀ x a Y, s.branch x a (embedFirstBlock Y) = embedFirstBlock (E x a Y)) ∧
      (∀ w, s.wordProbability ρ w =
        (Matrix.trace (w.foldl (fun Y a => E a.1 a.2 Y) ρ)).re) ∧
      ((∀ x Y, Y.PosSemidef →
        matrixMapEffect (E x true) * E x true Y = E x true Y ∧
        matrixMapEffect (E x true) * E x false Y = 0) → IsRepeatableSharpDilation s) ∧
      (HasRealCPBranchKraus ρ E → HasRealEntries (embedFirstBlock ρ) ∧ IsRealSharpDilation s) := by
  classical
  have hex (x : X) (a : Bool) :
      ∃ K : List (ComplexMatrix d), (∀ Y, E x a Y = krausAction K Y) ∧
        (HasRealCPBranchKraus ρ E → ∀ V ∈ K, HasRealEntries V) := by
    by_cases hr : HasRealCPBranchKraus ρ E
    · obtain ⟨K, hK, hR⟩ := hr.2 x a
      exact ⟨K, hK, fun _ => hR⟩
    · obtain ⟨K, hK⟩ := (choi_positive_iff_kraus (linearMapChoi (E x a))).mp
        ((linearMapChoi_positive_iff (E x a)).mpr (hE x a))
      exact ⟨K, fun Y => (choiAction_linearMapChoi _ Y).symm.trans (hK Y),
        fun h => False.elim (hr h)⟩
  choose K hK hR using hex
  have hn (x : X) : krausEffect (K x true) + krausEffect (K x false) = 1 := by
    have hC : choiOutputTrace (krausChoi (K x true ++ K x false)) = 1 := by
      apply (choi_trace_preservation_iff _).mpr
      intro Y
      rw [krausChoi_action, krausAction_append, ← hK x true Y, ← hK x false Y]
      exact hTP x Y
    rw [krausChoi_outputTrace, krausEffect_append] at hC
    simpa only [Matrix.transpose_transpose, Matrix.transpose_one] using
      congrArg Matrix.transpose hC
  let r : BinaryKrausRealization d X := ⟨ρ, hρ, K, hn⟩
  have hreal (h : HasRealCPBranchKraus ρ E) : IsRealKrausRealization r :=
    ⟨h.1, fun x a V hV => hR x a h V hV⟩
  have heff (x : X) (a : Bool) : matrixMapEffect (E x a) = krausEffect (r.kraus x a) :=
    matrixMapEffect_eq_kraus _ _ (hK x a)
  obtain ⟨s, hsharp, hrepeat, hrealS⟩ := exists_same_choice_sharpDilation r
  refine ⟨r, s, rfl, fun x a Y => (hK x a Y).symm, hsharp,
    fun x => (hsharp.2.2.2.2.1 x).trans (heff x true).symm, ?_, ?_, ?_, ?_⟩
  · intro x a Y
    rw [hsharp.2.2.2.2.2.2.1 x a Y, hK x a Y]
  · intro w
    change s.wordProbability r.initial w = _
    rw [hsharp.2.2.2.2.2.2.2.2 w, binaryKrausProbability]
    have hw (v : Word X) (Y : ComplexMatrix d) :
        v.foldl (fun Z a => krausAction (r.kraus a.1 a.2) Z) Y =
          v.foldl (fun Z a => E a.1 a.2 Z) Y := by
      induction v generalizing Y with
      | nil => rfl
      | cons a v ih =>
        simp only [List.foldl_cons]
        rw [ih]
        congr 1
        exact (hK a.1 a.2 Y).symm
    rw [hw]
  · intro hs
    apply hrepeat
    intro x Y hY
    have hh := hs x Y hY
    rw [heff x true, hK x true Y, hK x false Y] at hh
    exact hh
  · intro h
    exact ⟨embedFirstBlock_real ρ h.1, hrealS (hreal h)⟩

end AlbertSequential
