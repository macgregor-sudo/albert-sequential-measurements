module

public import CompactConstraints
public import ChoiWordContinuity

/-! Finite-menu and error-gap consequences for concrete stationary Choi words.
The parameter compactness premise in this intermediate module is discharged by
the positive-matrix module (`PositiveMatrixCompactness`).
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem finite_menu_iff_of_parameter_compact
    {d : ℕ} {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)]
    (hK : IsCompact {r : RawFiniteCPModel d P X A | IsNormalizedFiniteCPModel r})
    (t : P → InstrumentWord A → ℝ) :
    (∃ r : RawFiniteCPModel d P X A, IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t) ↔
    (∀ (ps : Finset P) (xs : Finset X), ∃ r : RawFiniteCPModel d P X A,
      IsNormalizedFiniteCPModel r ∧ MatchesFiniteMenu r t ps xs) := by
  classical
  constructor
  · rintro ⟨r, hr, hmatch⟩ ps xs
    exact ⟨r, hr, fun p _ w _ => hmatch p w⟩
  · intro hmenus
    let E : (P × InstrumentWord A) → Set (RawFiniteCPModel d P X A) :=
      fun q => {r | finiteCPWordProbability r q.1 q.2 = t q.1 q.2}
    have hE : ∀ q, IsClosed (E q) := fun q =>
      isClosed_eq (continuous_finiteCPWordProbability q.1 q.2) continuous_const
    have hf : ∀ F : Finset (P × InstrumentWord A),
        ∃ r ∈ {r : RawFiniteCPModel d P X A | IsNormalizedFiniteCPModel r},
          ∀ q ∈ F, r ∈ E q := by
      intro F
      let ps : Finset P := F.image Prod.fst
      let xs : Finset X := F.biUnion (fun q => q.2.toFinset.image Sigma.fst)
      obtain ⟨r, hr, hm⟩ := hmenus ps xs
      refine ⟨r, hr, fun q hq => ?_⟩
      apply hm q.1 (Finset.mem_image.mpr ⟨q, hq, rfl⟩) q.2
      intro a ha
      exact Finset.mem_biUnion.mpr ⟨q, hq,
        Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, rfl⟩⟩
    obtain ⟨r, hr, hall⟩ := exists_mem_of_finite_constraints hK E hE hf
    exact ⟨r, hr, fun p w => hall (p, w)⟩

theorem finite_error_gap_of_parameter_compact
    {d : ℕ} {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)]
    (hK : IsCompact {r : RawFiniteCPModel d P X A | IsNormalizedFiniteCPModel r})
    (t : P → InstrumentWord A → ℝ)
    (hnone : ¬ ∃ r : RawFiniteCPModel d P X A,
      IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t) :
    ∃ (F : Finset (P × InstrumentWord A)) (δ : ℝ), 0 < δ ∧
      ∀ r : RawFiniteCPModel d P X A, IsNormalizedFiniteCPModel r →
        ∃ q ∈ F, δ ≤ |finiteCPWordProbability r q.1 q.2 - t q.1 q.2| := by
  apply exists_finite_positive_error_gap hK
    (fun (q : P × InstrumentWord A) r => finiteCPWordProbability r q.1 q.2)
    (fun q => continuous_finiteCPWordProbability q.1 q.2) (fun q => t q.1 q.2)
  rintro ⟨r, hr, hall⟩
  exact hnone ⟨r, hr, fun p w => hall (p, w)⟩

end AlbertSequential
