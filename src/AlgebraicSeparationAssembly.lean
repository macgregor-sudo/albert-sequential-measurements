/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ProjectionMomentRealization
public import CompactMomentSeparation
public import NativeSquareCone

/-! Exact assembly at the algebraic comparison boundary. Native exclusion and
concrete R/C/H operator realization remain separate obligations. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis
universe u

theorem noMomentMatch_iff_noUniversalProjectionMatch {n : ℕ}
    (p : Fin n → Albert) (states : Set Albert) :
    NoMomentMatch p states ↔
      ∀ M : AlgebraicProjectiveData (Fin n) (UniversalProjectionAlgebra n),
        ∀ ρ ∈ states, ¬ M.Matches p ρ := by
  constructor
  · intro h M ρ hρ hmatch
    obtain ⟨w, hw⟩ := h (momentsOfProjectiveData M)
      (momentsOfProjectiveData_admissible M) ρ hρ
    apply hw
    rw [momentWordProbability_eq_probability]
    exact hmatch w
  · intro h m hm ρ hρ
    by_contra! hmatch
    apply h (momentsToProjectiveData m hm) ρ hρ
    intro w
    rw [realizedMoments_probability]
    exact hmatch w

theorem uniformDensitySeparator_of_noMomentMatch {n : ℕ}
    (p : Fin n → Albert) (hnone : NoMomentMatch p nativeDensitySet) :
    UniformMomentSeparator p nativeDensitySet := by
  apply uniformMomentSeparator_of_compact_noMatch p nativeDensitySet
    isCompact_density_set convex_density_set
  · intro ρ hρ
    exact hρ.2
  · exact hnone

theorem uniformDensitySeparator_of_noUniversalProjectionMatch {n : ℕ}
    (p : Fin n → Albert)
    (hnone : ∀ M : AlgebraicProjectiveData (Fin n) (UniversalProjectionAlgebra n),
      ∀ ρ ∈ nativeDensitySet, ¬ M.Matches p ρ) :
    UniformMomentSeparator p nativeDensitySet :=
  uniformDensitySeparator_of_noMomentMatch p
    ((noMomentMatch_iff_noUniversalProjectionMatch p nativeDensitySet).mpr hnone)

/-- Soundness of one already chosen functional on every algebraic comparator. -/
theorem wordFunctional_nonnegative_on_algebraic_models {n : ℕ}
    (c : FiniteRealWordFunctional n)
    (hc : ∀ m, AdmissibleProjectionMoments n m →
      0 ≤ c.evaluate (momentWordProbability m))
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A) : 0 ≤ c.evaluate M.probability := by
  have h := hc (momentsOfProjectiveData M) (momentsOfProjectiveData_admissible M)
  have heq : momentWordProbability (momentsOfProjectiveData M) = M.probability := by
    funext w
    exact momentWordProbability_eq_probability M w
  rw [heq] at h
  exact h

/-- The common finite coefficients precede the comparator carrier and model. -/
theorem UniformMomentSeparator.algebraic {n : ℕ} {p : Fin n → Albert}
    {states : Set Albert} (h : UniformMomentSeparator p states) :
    ∃ L : ℕ, ∃ c : FiniteRealWordFunctional n, ∃ γ : ℝ,
      0 < γ ∧ c.HasHorizon L ∧
      (∀ (A : Type u) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin n) A), 0 ≤ c.evaluate M.probability) ∧
      (∀ ρ ∈ states, c.evaluate (nativeWordProbability p ρ) ≤ -γ) := by
  obtain ⟨L, c, γ, hγ, hL, hc, hnative⟩ := h
  refine ⟨L, c, γ, hγ, hL, ?_, hnative⟩
  intro A _ _ _ _ _ _ M
  exact wordFunctional_nonnegative_on_algebraic_models c hc M

end AlbertSequential
