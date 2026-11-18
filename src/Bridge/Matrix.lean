/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.Models
public import Bridge.Exclusion
public import MatchingModels.MatrixClassIBridge
public import ThreeAtomAndFourPoint
public import Mathlib.Analysis.Matrix.Order

/-!
# Finite matrix models in the Challenge's terms (three atoms; vanishing invariant)

The development states two "matching" results with an explicit density matrix `σ` and Hermitian
idempotent matrices `P_i` on `ℂ^d`, the word value being `Re tr(σ · Q₁⋯Q_m⋯Q₁)`:
`complexTripleContract_holds` (three atoms, `d = 3`, rank-one projections) and
`fourPoint_zero_c6_representation` (four atoms with `𝒜 = 0`, `d = 6`). Here such data becomes a
Challenge `ProjectiveRepresentation` on `EuclideanSpace ℂ (Fin d)`: the projections are the
matrices acting on `ℂ^d` (`MatchingModels.matToCLM`), and the state is `T ↦ tr(σ · [T])`, with
`[T]` the matrix of `T`. Positivity: for `T ≥ 0` the matrix `[T]` is positive semidefinite, and
`tr(σ X) = tr(√σ X √σ) ≥ 0`.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge AlbertSequential.MatchingModels
open scoped MatrixOrder ComplexOrder

variable {d : ℕ}

local notation "E" d => EuclideanSpace ℂ (Fin d)

/-- The matrix of a bounded operator on `ℂ^d`. -/
def clmMatrix (T : (E d) →L[ℂ] (E d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.toEuclideanLin.symm (T : (E d) →ₗ[ℂ] (E d))

theorem matToCLM_clmMatrix (T : (E d) →L[ℂ] (E d)) : matToCLM (clmMatrix T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  simp [matToCLM, clmMatrix]

theorem clmMatrix_matToCLM (A : Matrix (Fin d) (Fin d) ℂ) : clmMatrix (matToCLM A) = A := by
  simp [matToCLM, clmMatrix]

theorem clmMatrix_add (S T : (E d) →L[ℂ] (E d)) : clmMatrix (S + T) = clmMatrix S + clmMatrix T := by
  unfold clmMatrix
  rw [ContinuousLinearMap.toLinearMap_add, map_add]

theorem clmMatrix_smul (c : ℂ) (T : (E d) →L[ℂ] (E d)) : clmMatrix (c • T) = c • clmMatrix T := by
  unfold clmMatrix
  rw [ContinuousLinearMap.toLinearMap_smul, map_smul]

/-- The matrix action `A ↦ A` on `ℂ^d` as a ring homomorphism. -/
def matRingHom : Matrix (Fin d) (Fin d) ℂ →+* ((E d) →L[ℂ] (E d)) where
  toFun := matToCLM
  map_one' := matToCLM_one
  map_mul' A B := matToCLM_mul A B
  map_zero' := matToCLM_zero
  map_add' := matToCLM_add

/-- `tr(σ X) ≥ 0` (real and nonnegative) for positive semidefinite `σ` and `X`. -/
theorem trace_mul_nonneg {σ X : Matrix (Fin d) (Fin d) ℂ} (hσ : σ.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ Matrix.trace (σ * X) := by
  set S := CFC.sqrt σ
  have hS : 0 ≤ S := CFC.sqrt_nonneg σ
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  have hSh : S.conjTranspose = S := (Matrix.nonneg_iff_posSemidef.mp hS).isHermitian.eq
  have hpsd : (S * X * S.conjTranspose).PosSemidef := hX.mul_mul_conjTranspose_same S
  rw [hSh] at hpsd
  rw [← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have := hpsd.trace_nonneg
  rwa [Matrix.mul_assoc] at this

/-- The density-matrix state `T ↦ tr(σ · [T])`. -/
def densityState (σ : Matrix (Fin d) (Fin d) ℂ) : ((E d) →L[ℂ] (E d)) →ₗ[ℂ] ℂ where
  toFun T := Matrix.trace (σ * clmMatrix T)
  map_add' S T := by rw [clmMatrix_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' c T := by
    rw [clmMatrix_smul, Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul]

/-- Hermitian idempotent matrices and a density matrix as a Challenge representation. -/
def matrixRepresentation {n : ℕ} (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hherm : ∀ i, (P i).IsHermitian) (hidem : ∀ i, P i * P i = P i)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef) (htr : Matrix.trace σ = 1) :
    ProjectiveRepresentation n ℂ (E d) where
  projection i := matToCLM (P i)
  isStarProjection i := matToCLM_isStarProjection (hherm i) (hidem i)
  state := densityState σ
  state_one := by
    change Matrix.trace (σ * clmMatrix 1) = 1
    rw [← matToCLM_one, clmMatrix_matToCLM, Matrix.mul_one, htr]
  state_nonneg T hT := by
    have hX : (clmMatrix T).PosSemidef := by
      rw [← Matrix.isPositive_toEuclideanLin_iff]
      have hT' : (T : (E d) →ₗ[ℂ] (E d)).IsPositive := hT.toLinearMap
      simpa [clmMatrix] using hT'
    have h := trace_mul_nonneg hσ hX
    refine ⟨(Matrix.trace (σ * clmMatrix T)).re, ?_, ?_⟩
    · exact (RCLike.nonneg_iff.mp h).1
    · change Matrix.trace (σ * clmMatrix T) = _
      apply Complex.ext
      · simp
      · simpa using (RCLike.nonneg_iff.mp h).2

theorem matrixRepresentation_probability {n : ℕ} (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hherm : ∀ i, (P i).IsHermitian) (hidem : ∀ i, P i * P i = P i)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : σ.PosSemidef) (htr : Matrix.trace σ = 1) (w : Word n) :
    (matrixRepresentation P hherm hidem σ hσ htr).probability w =
      (Matrix.trace (σ * AlbertSequential.wordOperator P w)).re := by
  have hstar : ∀ i, star (P i) = P i := fun i => (hherm i).eq
  have hop : AlbertChallenge.wordOperator (fun i => matToCLM (P i)) w =
      matToCLM (AlbertSequential.wordOperator P w) := by
    rw [← wordOperator_palindrome P hidem hstar]
    exact (wordOperator_map (matRingHom (d := d)) P w).symm
  unfold ProjectiveRepresentation.probability
  change (Matrix.trace (σ * clmMatrix (AlbertChallenge.wordOperator (fun i => matToCLM (P i)) w))).re = _
  rw [hop, clmMatrix_matToCLM]

/-- A normalised rank-one matrix `v v*` is a Hermitian idempotent. -/
theorem rankOne_hermitian_idem {P : Matrix (Fin 3) (Fin 3) ℂ}
    (h : AlbertSequential.IsComplexRankOneProjection P) : P.IsHermitian ∧ P * P = P := by
  obtain ⟨v, hv, hP⟩ := h
  constructor
  · ext i j
    rw [Matrix.conjTranspose_apply, hP, hP, star_mul', star_star, mul_comm]
  · ext i j
    rw [Matrix.mul_apply, hP]
    simp only [hP]
    calc ∑ k, v i * star (v k) * (v k * star (v j))
        = v i * (∑ k, star (v k) * v k) * star (v j) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = v i * star (v j) := by rw [hv, mul_one]

/-- Three atoms: from every state, a representation on `ℂ³` reproduces every word. -/
theorem three_atoms_matching (p : Fin 3 → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert)
    (hρ : IsDensity ρ) :
    ∃ M : ProjectiveRepresentation 3 ℂ (E 3), ∀ w : Word 3, M.probability w = wordProbability p ρ w := by
  obtain ⟨P, σ, hP, ⟨hσ, htr⟩, hw⟩ :=
    AlbertSequential.complexTripleContract_holds.rank_one_statistics (fun i => toT (p i)) (toT ρ)
      (atoms_toT hp) ((isDensity_toT ρ).mpr hρ)
  refine ⟨matrixRepresentation P (fun i => (rankOne_hermitian_idem (hP i)).1)
    (fun i => (rankOne_hermitian_idem (hP i)).2) σ hσ htr, fun w => ?_⟩
  rw [matrixRepresentation_probability, ← wordProbability_toT]
  exact hw w

/-- An atom is a state. -/
theorem isDensity_of_isAtom {q : Albert} (hq : IsAtom q) : IsDensity q :=
  ⟨⟨q, hq.1.symm⟩, hq.2⟩

/-- Three atoms never generate `J`: otherwise no representation could reproduce their words. -/
theorem three_atoms_bridge (p : Fin 3 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ¬ Generates p ∧ ∀ ρ, IsDensity ρ →
      ∃ M : ProjectiveRepresentation 3 ℂ (E 3), ∀ w : Word 3, M.probability w = wordProbability p ρ w := by
  refine ⟨fun hg => ?_, three_atoms_matching p hp⟩
  obtain ⟨M, hM⟩ := three_atoms_matching p hp (p 0) (isDensity_of_isAtom (hp 0))
  exact (no_representation_bridge.{0} p hp hg (p 0)).1 ℂ (E 3) M (fun w _ => hM w)

/-- Four atoms with `𝒜 = 0`: from every state, a representation on `ℂ⁶` reproduces every word. -/
theorem zero_invariant_bridge (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (h0 : fourPointInvariant p = 0) :
    ∀ ρ, IsDensity ρ → ∃ M : ProjectiveRepresentation 4 ℂ (E 6),
      ∀ w : Word 4, M.probability w = wordProbability p ρ w := by
  intro ρ hρ
  have h0' : AlbertSequential.fourPointInvariant (fun i => toT (p i)) = 0 := by
    rw [fourPointInvariant_toT]; exact h0
  obtain ⟨P, hP, hρP⟩ := AlbertSequential.fourPoint_zero_c6_representation _ (atoms_toT hp) h0'
  obtain ⟨σ, ⟨hσ, htr⟩, hw⟩ := hρP (toT ρ) ((isDensity_toT ρ).mpr hρ)
  refine ⟨matrixRepresentation P (fun i => (hP i).1) (fun i => (hP i).2.1) σ hσ htr, fun w => ?_⟩
  rw [matrixRepresentation_probability, ← wordProbability_toT]
  exact hw w

end AlbertChallenge.Bridge
