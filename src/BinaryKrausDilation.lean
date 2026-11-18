/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SharpDilationSemantics

/-! Explicit basic doubled-space dilation. The positive square roots are supplied
as an actual common binary spectral bundle; existence is proved below. Repeatable
and real choices are separate refinements of this construction. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential
open Matrix

theorem BinaryKrausRealization.no_effect {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (x : X) :
    krausEffect (r.kraus x false) = 1 - krausEffect (r.kraus x true) := by
  have h := r.normalized x
  rw [← h]
  abel

def realizationBinarySupport {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (x : X) :
    BinarySpectralSupport (krausEffect (r.kraus x true)) :=
  binarySpectralSupport (krausEffect_positive _) (by
    rw [← r.no_effect x]; exact krausEffect_positive _)

def FiniteSpectralSupport.retarget {d : ℕ} {A B : ComplexMatrix d}
    (s : FiniteSpectralSupport A) (h : A = B) : FiniteSpectralSupport B := h ▸ s

@[simp] theorem FiniteSpectralSupport.retarget_root {d : ℕ} {A B : ComplexMatrix d}
    (s : FiniteSpectralSupport A) (h : A = B) : (s.retarget h).root = s.root := by
  cases h
  rfl

def binaryOutcomeSupport {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (x : X) (s : BinarySpectralSupport (krausEffect (r.kraus x true)))
    (a : Bool) : FiniteSpectralSupport (krausEffect (r.kraus x a)) := by
  cases a with
  | true => exact s.yes
  | false => exact s.no.retarget (r.no_effect x).symm

def binaryOutcomeIsometry {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (a : Bool) : Matrix (Fin (d+d)) (Fin d) ℂ :=
  if a then finiteBinaryYesIsometry s else finiteBinaryNoIsometry s

theorem binaryOutcomeIsometry_isometry {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (a : Bool) :
    (binaryOutcomeIsometry s a)ᴴ * binaryOutcomeIsometry s a = 1 := by
  cases a with
  | true => exact finiteBinaryYesIsometry_isometry s
  | false => exact finiteBinaryNoIsometry_isometry s

theorem binaryOutcomeIsometry_range {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (a : Bool) :
    binaryOutcomeIsometry s a * (binaryOutcomeIsometry s a)ᴴ =
      if a then finiteBinaryProjection s else 1 - finiteBinaryProjection s := by
  cases a with
  | true => rfl
  | false => exact finiteBinaryNoIsometry_range s

theorem binaryOutcomeIsometry_inclusion {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (x : X)
    (s : BinarySpectralSupport (krausEffect (r.kraus x true))) (a : Bool) :
    (binaryOutcomeIsometry s a)ᴴ * firstBlockInclusion d =
      (binaryOutcomeSupport r x s a).root := by
  cases a with
  | true => exact finiteBinaryYesIsometry_inclusion s
  | false => simpa [binaryOutcomeSupport, binaryOutcomeIsometry] using
      finiteBinaryNoIsometry_inclusion s

def binaryKrausDilation {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
    (B : X → Bool → ComplexMatrix d) (C : X → Bool → ComplexMatrix (d+d)) :
    SharpDilationData d X where
  projection x := finiteBinaryProjection (s x)
  channelKraus x a := isometricCompletedKraus
    (completedKraus (r.kraus x a) (binaryOutcomeSupport r x (s x) a) (B x a))
    (firstBlockInclusion d) (binaryOutcomeIsometry (s x) a) (C x a)

theorem binaryKrausDilation_branch {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
    (B : X → Bool → ComplexMatrix d) (C : X → Bool → ComplexMatrix (d+d))
    (x : X) (a : Bool) (Z : ComplexMatrix (d+d)) :
    (binaryKrausDilation r s B C).branch x a Z =
      embedFirstBlock (krausAction
        (completedKraus (r.kraus x a) (binaryOutcomeSupport r x (s x) a) (B x a))
        ((binaryOutcomeIsometry (s x) a)ᴴ * Z * binaryOutcomeIsometry (s x) a)) := by
  change krausAction _ ((if a then finiteBinaryProjection (s x) else
      1 - finiteBinaryProjection (s x)) * Z *
      (if a then finiteBinaryProjection (s x) else 1 - finiteBinaryProjection (s x))) = _
  rw [← binaryOutcomeIsometry_range]
  exact isometricCompletedKraus_compressed_action _ _ _ _ _
    (binaryOutcomeIsometry_isometry (s x) a)

theorem binaryKrausDilation_intertwining {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
    (B : X → Bool → ComplexMatrix d) (C : X → Bool → ComplexMatrix (d+d))
    (x : X) (a : Bool) (Y : ComplexMatrix d) :
    (binaryKrausDilation r s B C).branch x a (embedFirstBlock Y) =
      embedFirstBlock (krausAction (r.kraus x a) Y) := by
  have hl := binaryOutcomeIsometry_inclusion r x (s x) a
  have hr : (firstBlockInclusion d)ᴴ * binaryOutcomeIsometry (s x) a =
      (binaryOutcomeSupport r x (s x) a).root := by
    simpa [(binaryOutcomeSupport r x (s x) a).root_hermitian] using
      congrArg Matrix.conjTranspose hl
  have hc : (binaryOutcomeIsometry (s x) a)ᴴ * embedFirstBlock Y *
      binaryOutcomeIsometry (s x) a =
      (binaryOutcomeSupport r x (s x) a).root * Y *
        (binaryOutcomeSupport r x (s x) a).root := by
    unfold embedFirstBlock
    calc
      _ = ((binaryOutcomeIsometry (s x) a)ᴴ * firstBlockInclusion d) * Y *
        ((firstBlockInclusion d)ᴴ * binaryOutcomeIsometry (s x) a) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hl, hr]
  rw [binaryKrausDilation_branch, hc, completedKraus_factorization]

theorem binaryKrausDilation_isSharpDilation {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
    (B : X → Bool → ComplexMatrix d) (C : X → Bool → ComplexMatrix (d+d))
    (hB : ∀ x a, Matrix.trace (B x a * (B x a)ᴴ) = 1)
    (hC : ∀ x a, Matrix.trace (C x a * (C x a)ᴴ) = 1) :
    IsSharpDilation r (binaryKrausDilation r s B C) := by
  apply isSharpDilation_of_algebraic_construction
  · intro x
    exact ⟨finiteBinaryProjection_hermitian _, finiteBinaryProjection_idempotent _⟩
  · intro x a
    exact isometricCompletedKraus_effect _ _ _ _
      (completedKraus_effect _ _ _ (hB x a)) (firstBlockInclusion_isometry d)
      (binaryOutcomeIsometry_isometry (s x) a) (hC x a)
  · intro x
    exact finiteBinaryProjection_compression _
  · exact binaryKrausDilation_intertwining r s B C
  · intro x a Z
    exact ⟨_, binaryKrausDilation_branch r s B C x a Z⟩

/-- The basic sharp dilation exists in exactly d+d dimensions. All histories
are unconditional; no positive branch probability or invertible effect is assumed.
The same-choice real and repeatable refinements are not asserted here. -/
theorem exists_basic_sharpDilation {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) :
    ∃ s : SharpDilationData d X, IsSharpDilation r s := by
  obtain ⟨B, hB⟩ := exists_complexPositiveFactor r.density.1
  obtain ⟨C, hC⟩ := exists_complexPositiveFactor (density_embedFirstBlock r.density).1
  exact ⟨binaryKrausDilation r (realizationBinarySupport r) (fun _ _ => B) (fun _ _ => C),
    binaryKrausDilation_isSharpDilation r _ _ _
      (fun _ _ => hB ▸ r.density.2)
      (fun _ _ => hC ▸ (density_embedFirstBlock r.density).2)⟩

#print axioms binaryKrausDilation_isSharpDilation
#print axioms exists_basic_sharpDilation
end AlbertSequential

