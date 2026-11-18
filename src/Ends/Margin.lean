/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ProjectionMomentRealization
public import MomentTopology
public import CompactConstraints

/-! # A positive margin from exclusion, by compactness of the moment domain

Generic composition of earlier modules (no new mathematics):

* `isCompact_projectionMomentDomain` (MomentTopology): admissible all-word projection moments
  form a compact set; `continuous_momentWordProbability`: every word probability is continuous;
* `exists_finite_positive_error_gap` (CompactConstraints): continuous coordinates that cannot all
  match have a finite collection with a strictly positive maximum-error gap on a compact set;
* `momentsToProjectiveData` / `realizedMoments_probability` (ProjectionMomentRealization): every
  admissible moment family is realised by an `AlgebraicProjectiveData` on the universal
  projection algebra with the same word probabilities;
* `momentsOfProjectiveData_admissible` / `momentWordProbability_eq_probability`
  (AlgebraicMomentBinding): every algebraic projective model has admissible moments with the same
  word probabilities.

So exclusion of every algebraic model on a word set `S` (tested only on the universal projection
algebra) gives one `δ > 0` such that every algebraic model, over any star ring, misses the table by
at least `δ` on some word of `S`; the witness words can be taken from one finite subset of `S`. -/

@[expose] public section

namespace AlbertSequential.Ends

open AlbertSequential

/-- Moment-level margin: exclusion on the universal projection algebra gives a uniform gap on the
compact moment domain, witnessed in one finite subset of `S`. -/
theorem moment_margin_of_noMatch {n : ℕ} (S : Set (Word (Fin n))) (t : Word (Fin n) → ℝ)
    (hno : ∀ M : AlgebraicProjectiveData (Fin n) (UniversalProjectionAlgebra n),
      ¬ ∀ w ∈ S, M.probability w = t w) :
    ∃ (F : Finset (Word (Fin n))) (δ : ℝ), (∀ w ∈ F, w ∈ S) ∧ 0 < δ ∧
      ∀ m ∈ projectionMomentDomain n, ∃ w ∈ F, δ ≤ |momentWordProbability m w - t w| := by
  classical
  obtain ⟨F, δ, hδ, h⟩ := exists_finite_positive_error_gap (isCompact_projectionMomentDomain n)
    (fun (w : S) m => momentWordProbability m w.1)
    (fun w => continuous_momentWordProbability w.1) (fun w => t w.1)
    (by
      rintro ⟨m, hm, hall⟩
      have hm' : AdmissibleProjectionMoments n m := hm
      exact hno (momentsToProjectiveData m hm') fun w hw => by
        rw [realizedMoments_probability]
        exact hall ⟨w, hw⟩)
  refine ⟨F.map (Function.Embedding.subtype _), δ, ?_, hδ, ?_⟩
  · intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hw
    exact i.2
  · intro m hm
    obtain ⟨i, hi, hgap⟩ := h m hm
    exact ⟨i.1, Finset.mem_map.mpr ⟨i, hi, rfl⟩, hgap⟩

/-- Transfer of a moment-level gap to any algebraic model (universe-polymorphic). -/
theorem algebraic_gap_of_moment {n : ℕ} {F : Finset (Word (Fin n))} {δ : ℝ}
    {t : Word (Fin n) → ℝ}
    (h : ∀ m ∈ projectionMomentDomain n, ∃ w ∈ F, δ ≤ |momentWordProbability m w - t w|)
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin n) A) :
    ∃ w ∈ F, δ ≤ |M.probability w - t w| := by
  obtain ⟨w, hw, hgap⟩ := h (momentsOfProjectiveData M) (momentsOfProjectiveData_admissible M)
  exact ⟨w, hw, by rwa [momentWordProbability_eq_probability] at hgap⟩

/-- Algebraic-model margin (any star ring, any universe), with one finite witness set. -/
theorem algebraic_margin_of_noMatch {n : ℕ} (S : Set (Word (Fin n))) (t : Word (Fin n) → ℝ)
    (hno : ∀ M : AlgebraicProjectiveData (Fin n) (UniversalProjectionAlgebra n),
      ¬ ∀ w ∈ S, M.probability w = t w) :
    ∃ (F : Finset (Word (Fin n))) (δ : ℝ), (∀ w ∈ F, w ∈ S) ∧ 0 < δ ∧
      ∀ (A : Type*) [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
        [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin n) A),
        ∃ w ∈ F, δ ≤ |M.probability w - t w| := by
  obtain ⟨F, δ, hFS, hδ, h⟩ := moment_margin_of_noMatch S t hno
  exact ⟨F, δ, hFS, hδ, fun A _ _ _ _ _ _ M => algebraic_gap_of_moment h M⟩

end AlbertSequential.Ends
