/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealFiniteKrausReindex
public import RealKrausBridge

/-! Literal conversion of finite real Kraus data to the existing public complex
model. Both normalization and all chronological probabilities are preserved. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem complexifyRectangularKrausAction {d : ℕ} (K : List (Matrix (Fin d) (Fin d) ℝ))
    (Y : Matrix (Fin d) (Fin d) ℝ) :
    complexifyMatrix (rectangularKrausAction K Y) =
      krausAction (K.map complexifyMatrix) (complexifyMatrix Y) := by
  simpa only [rectangularKrausAction, realKrausAction,
    Matrix.conjTranspose_eq_transpose_of_trivial] using complexify_realKrausAction K Y

theorem complexifyRectangularKrausEffect {d : ℕ} (K : List (Matrix (Fin d) (Fin d) ℝ)) :
    complexifyMatrix (rectangularKrausEffect K) = krausEffect (K.map complexifyMatrix) := by
  simpa only [rectangularKrausEffect, realKrausEffect,
    Matrix.conjTranspose_eq_transpose_of_trivial] using complexify_realKrausEffect K

def complexifyRealFiniteKrausModel {d : ℕ} {X : Type*}
    (r : RealFiniteKrausModel (Fin d) X) : BinaryKrausRealization d X where
  initial := complexifyMatrix r.initial
  density := (complexifyMatrix_density_iff _).mpr ⟨r.positive, r.trace_one⟩
  kraus x b := (r.kraus x b).map complexifyMatrix
  normalized x := by
    rw [← complexifyRectangularKrausEffect, ← complexifyRectangularKrausEffect,
      ← complexifyMatrix_add, r.normalized, complexifyMatrix_one]

theorem complexifyRealFiniteKrausModel_real {d : ℕ} {X : Type*}
    (r : RealFiniteKrausModel (Fin d) X) : IsRealKrausRealization (complexifyRealFiniteKrausModel r) := by
  refine ⟨complexifyMatrix_hasRealEntries _, ?_⟩
  intro x b K hK
  obtain ⟨M, _, rfl⟩ := List.mem_map.mp hK
  exact complexifyMatrix_hasRealEntries M

theorem complexifyRealKrausWordState {d : ℕ} {X : Type*}
    (K : X → Bool → List (Matrix (Fin d) (Fin d) ℝ)) (Y : Matrix (Fin d) (Fin d) ℝ)
    (w : Word X) :
    w.foldl (fun Z a => krausAction ((K a.1 a.2).map complexifyMatrix) Z) (complexifyMatrix Y) =
      complexifyMatrix (w.foldl (fun Z a => rectangularKrausAction (K a.1 a.2) Z) Y) := by
  induction w generalizing Y with
  | nil => rfl
  | cons a w ih =>
    simp only [List.foldl_cons]
    rw [← complexifyRectangularKrausAction, ih]

theorem complexifyRealFiniteKrausModel_probability {d : ℕ} {X : Type*}
    (r : RealFiniteKrausModel (Fin d) X) (w : Word X) :
    binaryKrausProbability (complexifyRealFiniteKrausModel r) w =
      realFiniteKrausProbability (Fin d) X r w := by
  change (Matrix.trace (w.foldl (fun Z a => krausAction ((r.kraus a.1 a.2).map complexifyMatrix) Z)
    (complexifyMatrix r.initial))).re = _
  rw [complexifyRealKrausWordState, complexifyMatrix_trace]
  rfl

theorem exists_complexFiniteKrausModel_of_card {I X : Type*} [Fintype I] [DecidableEq I]
    {d : ℕ} (hd : Fintype.card I = d) (r : RealFiniteKrausModel I X) :
    ∃ s : BinaryKrausRealization d X, IsRealKrausRealization s ∧
      ∀ w, binaryKrausProbability s w = realFiniteKrausProbability I X r w := by
  let e : I ≃ Fin d := Fintype.equivFinOfCardEq hd
  let renamed := renameRealFiniteKrausModel e r
  refine ⟨complexifyRealFiniteKrausModel renamed, complexifyRealFiniteKrausModel_real renamed, ?_⟩
  intro w
  rw [complexifyRealFiniteKrausModel_probability, renameRealFiniteKrausModel_probability]

end AlbertSequential
