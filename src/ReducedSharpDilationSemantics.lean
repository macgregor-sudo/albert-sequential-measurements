/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ReducedSharpDilationChannels
public import NormalizedKrausOutput
public import RealKrausBridge

/-! The exact operational conclusions of companion Proposition 6.4 at a
supplied dimension. No positivity premise enters the all-input identities. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential

open Matrix
open scoped ComplexOrder

structure ReducedSharpDilationData (d D : ℕ) (X : Type*) where
  inclusion : Matrix (Fin D) (Fin d) ℂ
  projection : X → ComplexMatrix D
  channelKraus : X → Bool → List (ComplexMatrix D)

def sharpOutcomeProjection {D : ℕ} (P : ComplexMatrix D) (a : Bool) : ComplexMatrix D :=
  if a then P else 1 - P

def ReducedSharpDilationData.outcomeProjection {d D : ℕ} {X : Type*}
    (s : ReducedSharpDilationData d D X) (x : X) (a : Bool) : ComplexMatrix D :=
  sharpOutcomeProjection (s.projection x) a

def ReducedSharpDilationData.branch {d D : ℕ} {X : Type*}
    (s : ReducedSharpDilationData d D X) (x : X) (a : Bool) (Z : ComplexMatrix D) :
    ComplexMatrix D :=
  krausAction (s.channelKraus x a) (s.outcomeProjection x a * Z * s.outcomeProjection x a)

def ReducedSharpDilationData.wordProbability {d D : ℕ} {X : Type*}
    (s : ReducedSharpDilationData d D X) (ρ : ComplexMatrix d) (w : Word X) : ℝ :=
  (Matrix.trace (w.foldl (fun Z a => s.branch a.1 a.2 Z) (sharpFrameEmbed s.inclusion ρ))).re

structure IsReducedSharpDilation {d D : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (s : ReducedSharpDilationData d D X) : Prop where
  inclusion_isometry : s.inclusionᴴ * s.inclusion = 1
  projection_orthogonal : ∀ x, (s.projection x)ᴴ = s.projection x ∧
    s.projection x * s.projection x = s.projection x
  channel_cp : ∀ x a, IsCompletelyPositiveMatrixMap (krausAction (s.channelKraus x a))
  channel_normalized : ∀ x a, krausEffect (s.channelKraus x a) = 1
  initial_density : IsMatrixDensity (sharpFrameEmbed s.inclusion r.initial)
  nonselective_trace : ∀ x Z, Matrix.trace (s.branch x true Z + s.branch x false Z) = Matrix.trace Z
  effect_compression : ∀ x a, s.inclusionᴴ * s.outcomeProjection x a * s.inclusion =
    krausEffect (r.kraus x a)
  branch_effect : ∀ x a Z, Matrix.trace (s.branch x a Z) = Matrix.trace (s.outcomeProjection x a * Z)
  intertwining : ∀ x a Y, s.branch x a (sharpFrameEmbed s.inclusion Y) =
    sharpFrameEmbed s.inclusion (krausAction (r.kraus x a) Y)
  output_first_corner : ∀ x a Z, ∃ Y : ComplexMatrix d, s.branch x a Z = sharpFrameEmbed s.inclusion Y
  word_probability : ∀ w, s.wordProbability r.initial w = binaryKrausProbability r w

def IsRepeatableReducedSharpDilation {d D : ℕ} {X : Type*} (s : ReducedSharpDilationData d D X) : Prop :=
  ∀ x a Z, Z.PosSemidef → s.branch x a Z =
    s.outcomeProjection x a * s.branch x a Z * s.outcomeProjection x a

def IsRealReducedSharpDilation {d D : ℕ} {X : Type*} (s : ReducedSharpDilationData d D X) : Prop :=
  (∀ x, HasRealEntries (s.projection x)) ∧
    ∀ x a K, K ∈ s.channelKraus x a → HasRealEntries K

theorem sharpOutcomeProjection_orthogonal {D : ℕ} (P : ComplexMatrix D)
    (hP : Pᴴ = P ∧ P * P = P) (a : Bool) :
    (sharpOutcomeProjection P a)ᴴ = sharpOutcomeProjection P a ∧
      sharpOutcomeProjection P a * sharpOutcomeProjection P a = sharpOutcomeProjection P a := by
  cases a
  · change (1 - P)ᴴ = 1 - P ∧ (1 - P) * (1 - P) = 1 - P
    constructor
    · simp [Matrix.conjTranspose_sub, hP.1]
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hP.2]
      abel
  · exact hP

theorem IsReducedSharpDilation.channel_trace_preserving {d D : ℕ} {X : Type*}
    {r : BinaryKrausRealization d X} {s : ReducedSharpDilationData d D X}
    (h : IsReducedSharpDilation r s) (x : X) (a : Bool) (Z : ComplexMatrix D) :
    Matrix.trace (krausAction (s.channelKraus x a) Z) = Matrix.trace Z := by
  rw [trace_krausAction, h.channel_normalized, Matrix.one_mul]

theorem IsReducedSharpDilation.branch_completelyPositive {d D : ℕ} {X : Type*}
    {r : BinaryKrausRealization d X} {s : ReducedSharpDilationData d D X}
    (h : IsReducedSharpDilation r s) (x : X) (a : Bool) :
    IsCompletelyPositiveMatrixMap (s.branch x a) := by
  let R := s.outcomeProjection x a
  have hR : Rᴴ = R := (sharpOutcomeProjection_orthogonal _ (h.projection_orthogonal x) a).1
  have hbranch : s.branch x a = krausAction ((s.channelKraus x a).map (fun K => K * R)) := by
    funext Z
    rw [krausAction_right_multiply, hR]
    rfl
  rw [hbranch]
  exact krausAction_completelyPositive _

def reducedSharpDilationOfFrames {d D : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (J : Matrix (Fin D) (Fin d) ℂ) (P : X → ComplexMatrix D)
    (s : ∀ x a, FiniteSpectralSupport (krausEffect (r.kraus x a)))
    (f : ∀ x a, SharpDilationChannelFrame J (sharpOutcomeProjection (P x) a) (s x a).root)
    (B : X → Bool → ComplexMatrix d) : ReducedSharpDilationData d D X where
  inclusion := J
  projection := P
  channelKraus x a := sharpFrameChannelKraus (r.kraus x a) (s x a) (f x a) (B x a)

theorem reducedSharpDilationOfFrames_correct {d D : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (J : Matrix (Fin D) (Fin d) ℂ) (P : X → ComplexMatrix D)
    (s : ∀ x a, FiniteSpectralSupport (krausEffect (r.kraus x a)))
    (f : ∀ x a, SharpDilationChannelFrame J (sharpOutcomeProjection (P x) a) (s x a).root)
    (B : X → Bool → ComplexMatrix d) (hJ : Jᴴ * J = 1)
    (hP : ∀ x, (P x)ᴴ = P x ∧ P x * P x = P x)
    (hB : ∀ x a, Matrix.trace (B x a * (B x a)ᴴ) = 1) :
    IsReducedSharpDilation r (reducedSharpDilationOfFrames r J P s f B) := by
  let M := reducedSharpDilationOfFrames r J P s f B
  have hK (x : X) (a : Bool) : krausEffect (M.channelKraus x a) = 1 :=
    sharpFrameChannelKraus_effect (r.kraus x a) (s x a) (f x a) (B x a) hJ (hB x a)
  have hI (x : X) (a : Bool) (Y : ComplexMatrix d) :
      M.branch x a (sharpFrameEmbed J Y) = sharpFrameEmbed J (krausAction (r.kraus x a) Y) :=
    sharpFrameChannelKraus_intertwining (r.kraus x a) (s x a) (f x a) (B x a) hJ
      (sharpOutcomeProjection_orthogonal _ (hP x) a).1 (sharpOutcomeProjection_orthogonal _ (hP x) a).2 Y
  have htrace (x : X) (a : Bool) (Z : ComplexMatrix D) :
      Matrix.trace (M.branch x a Z) = Matrix.trace (M.outcomeProjection x a * Z) := by
    rw [ReducedSharpDilationData.branch, trace_krausAction, hK, Matrix.one_mul, Matrix.trace_mul_cycle]
    change Matrix.trace (sharpOutcomeProjection (P x) a * sharpOutcomeProjection (P x) a * Z) =
       Matrix.trace (sharpOutcomeProjection (P x) a * Z)
    rw [(sharpOutcomeProjection_orthogonal _ (hP x) a).2]
  refine ⟨hJ, hP, fun x a => krausAction_completelyPositive (M.channelKraus x a), hK,
    sharpFrameEmbed_density J hJ r.density, ?_, ?_, htrace, hI, ?_, ?_⟩
  · intro x Z
    rw [Matrix.trace_add, htrace x true, htrace x false, ← Matrix.trace_add, ← Matrix.add_mul]
    change Matrix.trace ((P x + (1 - P x)) * Z) = _
    simp
  · intro x a
    exact sharpFrameChannelKraus_projection_compression (r.kraus x a) (s x a) (f x a)
  · intro x a Z
    exact ⟨_, sharpFrameChannelKraus_branch (r.kraus x a) (s x a) (f x a) (B x a) hJ
      (sharpOutcomeProjection_orthogonal _ (hP x) a).1 (sharpOutcomeProjection_orthogonal _ (hP x) a).2 Z⟩
  · intro w
    have hfold (v : Word X) (Y : ComplexMatrix d) :
        v.foldl (fun Z a => M.branch a.1 a.2 Z) (sharpFrameEmbed J Y) =
          sharpFrameEmbed J (v.foldl (fun Z a => krausAction (r.kraus a.1 a.2) Z) Y) := by
      induction v generalizing Y with
      | nil => rfl
      | cons a v ih => simp only [List.foldl_cons, hI, ih]
    change (Matrix.trace (w.foldl (fun Z a => M.branch a.1 a.2 Z)
      (sharpFrameEmbed J r.initial))).re = _
    rw [hfold, sharpFrameEmbed_trace J hJ]
    rfl

theorem reducedSharpDilationOfFrames_real {d D : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (J : Matrix (Fin D) (Fin d) ℂ) (P : X → ComplexMatrix D)
    (s : ∀ x a, FiniteSpectralSupport (krausEffect (r.kraus x a)))
    (f : ∀ x a, SharpDilationChannelFrame J (sharpOutcomeProjection (P x) a) (s x a).root)
    (B : X → Bool → ComplexMatrix d) (hr : IsRealKrausRealization r)
    (hJ : ∀ i j, (J i j).im = 0) (hP : ∀ x, HasRealEntries (P x))
    (hV : ∀ x a i j, ((f x a).frame i j).im = 0)
    (hs : ∀ x a, HasRealEntries (s x a).inverseRoot ∧ HasRealEntries (s x a).support)
    (hB : ∀ x a, HasRealEntries (B x a)) :
    IsRealReducedSharpDilation (reducedSharpDilationOfFrames r J P s f B) := by
  refine ⟨hP, ?_⟩
  intro x a W hW
  have hLift : HasRealEntries (sharpFrameEmbed J (B x a)) :=
    realEntries_mul _ _ (realEntries_mul _ _ hJ (hB x a)) (realEntries_conjTranspose _ hJ)
  exact isometricCompletion_list_hasRealEntries _ _ _ _
    (completedKraus_hasRealEntries _ _ _ (hr.2 x a) (hs x a).1 (hs x a).2 (hB x a))
    hJ (hV x a) hLift W hW

end AlbertSequential
