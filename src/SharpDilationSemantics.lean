/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FiniteBinaryProjection
public import IsometricKrausCompletion

/-! Trace and chronological semantics for the literal common-corner dilation.
Intertwining is used on ALL matrices, so zero histories need no division. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix
open scoped ComplexOrder

theorem trace_krausAction {d : ℕ} (K : List (ComplexMatrix d)) (Y : ComplexMatrix d) :
    Matrix.trace (krausAction K Y) = Matrix.trace (krausEffect K * Y) := by
  induction K with
  | nil => simp [krausAction, krausEffect]
  | cons V K ih =>
      simp only [krausAction, krausEffect, List.map_cons, List.sum_cons,
        Matrix.add_mul, Matrix.trace_add] at ih ⊢
      rw [ih, Matrix.trace_mul_cycle]

theorem trace_embedFirstBlock {d : ℕ} (Y : ComplexMatrix d) :
    Matrix.trace (embedFirstBlock Y) = Matrix.trace Y := by
  rw [embedFirstBlock, Matrix.trace_mul_cycle, firstBlockInclusion_isometry, Matrix.one_mul]

theorem density_embedFirstBlock {d : ℕ} {ρ : ComplexMatrix d} (hρ : IsMatrixDensity ρ) :
    IsMatrixDensity (embedFirstBlock ρ) := by
  exact ⟨hρ.1.mul_mul_conjTranspose_same _, (trace_embedFirstBlock ρ).trans hρ.2⟩

theorem outcomeProjection_idempotent {d : ℕ} {X : Type*}
    (s : SharpDilationData d X) (hP : ∀ x, s.projection x * s.projection x = s.projection x)
    (x : X) (a : Bool) :
    s.outcomeProjection x a * s.outcomeProjection x a = s.outcomeProjection x a := by
  cases a with
  | true => exact hP x
  | false =>
      simp only [SharpDilationData.outcomeProjection, Bool.false_eq_true, ite_false,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]
      abel

theorem trace_sharpDilation_branch {d : ℕ} {X : Type*} (s : SharpDilationData d X)
    (hP : ∀ x, s.projection x * s.projection x = s.projection x)
    (hK : ∀ x a, krausEffect (s.channelKraus x a) = 1)
    (x : X) (a : Bool) (Z : ComplexMatrix (d+d)) :
    Matrix.trace (s.branch x a Z) = Matrix.trace (s.outcomeProjection x a * Z) := by
  rw [SharpDilationData.branch, trace_krausAction, hK, Matrix.one_mul,
    Matrix.trace_mul_cycle, outcomeProjection_idempotent s hP]

theorem trace_sharpDilation_nonselective {d : ℕ} {X : Type*} (s : SharpDilationData d X)
    (hP : ∀ x, s.projection x * s.projection x = s.projection x)
    (hK : ∀ x a, krausEffect (s.channelKraus x a) = 1)
    (x : X) (Z : ComplexMatrix (d+d)) :
    Matrix.trace (s.branch x true Z + s.branch x false Z) = Matrix.trace Z := by
  rw [Matrix.trace_add, trace_sharpDilation_branch s hP hK,
    trace_sharpDilation_branch s hP hK]
  simp only [SharpDilationData.outcomeProjection, Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.trace_add, ← Matrix.add_mul]
  simp

theorem SharpDilationData.wordProbability_eq_of_intertwining {d : ℕ} {X : Type*}
    (s : SharpDilationData d X) (r : BinaryKrausRealization d X)
    (h : ∀ x a Y, s.branch x a (embedFirstBlock Y) =
      embedFirstBlock (krausAction (r.kraus x a) Y)) (w : Word X) :
    s.wordProbability r.initial w = binaryKrausProbability r w := by
  have hf (v : Word X) (Y : ComplexMatrix d) :
      v.foldl (fun Z a => s.branch a.1 a.2 Z) (embedFirstBlock Y) =
        embedFirstBlock (v.foldl (fun Z a => krausAction (r.kraus a.1 a.2) Z) Y) := by
    induction v generalizing Y with
    | nil => rfl
    | cons a v ih => simp only [List.foldl_cons, h, ih]
  unfold SharpDilationData.wordProbability binaryKrausProbability
  rw [hf, trace_embedFirstBlock]

/-- The algebraic construction properties imply the entire basic dilation
contract. Repeatability and real-data preservation are treated separately. -/
theorem isSharpDilation_of_algebraic_construction {d : ℕ} {X : Type*}
    (s : SharpDilationData d X) (r : BinaryKrausRealization d X)
    (hP : ∀ x, (s.projection x)ᴴ = s.projection x ∧
      s.projection x * s.projection x = s.projection x)
    (hK : ∀ x a, krausEffect (s.channelKraus x a) = 1)
    (hC : ∀ x, compressFirstBlock (s.projection x) = krausEffect (r.kraus x true))
    (hI : ∀ x a Y, s.branch x a (embedFirstBlock Y) =
      embedFirstBlock (krausAction (r.kraus x a) Y))
    (hR : ∀ x a Z, ∃ Y : ComplexMatrix d, s.branch x a Z = embedFirstBlock Y) :
    IsSharpDilation r s := by
  refine ⟨hP, hK, density_embedFirstBlock r.density,
    trace_sharpDilation_nonselective s (fun x => (hP x).2) hK, hC,
    trace_sharpDilation_branch s (fun x => (hP x).2) hK, hI, hR, ?_⟩
  exact s.wordProbability_eq_of_intertwining r hI

#print axioms SharpDilationData.wordProbability_eq_of_intertwining
#print axioms isSharpDilation_of_algebraic_construction
end AlbertSequential
