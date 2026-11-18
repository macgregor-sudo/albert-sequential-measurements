/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PentadArityAndHelly
public import AlbertUniformSeparation
public import Bridge.Criterion

/-!
# cor:helly without hypotheses

Core `cor:helly`, operational sentence: "a finite family of tests of atoms of `J` has a
sequential projective representation (from some, equivalently every, state of `J`) if and only if
each subfamily of at most five of its tests does."

* `cor_helly_operational_iff_unconditional`: the development's algebraic-model form
  `cor_helly_operational_iff`, with its separation hypothesis discharged by
  `albertUniformSeparation 5`.
* `cor_helly_classI`: the model-class (I) form in the vocabulary of `Challenge`: "has a sequential
  projective representation from some state" is `∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn p ρ univ`
  (a real, complex or quaternionic representation, or an algebraic model, on a space in `Type`,
  reproducing every word); "from every state" is the same with `∀ ρ`. Route: the Albert criterion
  (`Bridge.albert_criterion_bridge`) reduces both sides to non-generation, and the geometric Helly
  theorem `cor_helly_geometric` (Helly number five) closes the gap.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

/-- **cor:helly, algebraic-model form, unconditional.** -/
theorem cor_helly_operational_iff_unconditional {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) :
    (∃ (d : ℕ) (P : Fin n → HermitianEmbeddingMatrix d),
      d ∈ ({6, 24} : Set ℕ) ∧
      ∀ ρ : Albert, IsDensity ρ →
        ∃ (σ : HermitianEmbeddingMatrix d)
          (M : AlgebraicProjectiveData (Fin n) (HermitianEmbeddingMatrix d)),
          IsEmbeddingDensity d σ ∧
          M.projection = P ∧
          (∀ X, M.state X = (Matrix.trace (σ * X)).re) ∧
          AlgebraicMomentBinding M ∧
          M.Matches p ρ) ↔
      (∀ (k : ℕ), k ≤ 5 → ∀ (f : Fin k → Fin n), Function.Injective f →
        ∃ (A : Type) (_ : Ring A) (_ : StarRing A) (_ : Module ℝ A)
          (_ : IsScalarTower ℝ A A) (_ : SMulCommClass ℝ A A) (_ : StarModule ℝ A)
          (M : AlgebraicProjectiveData (Fin k) A) (ρ : Albert),
          IsDensity ρ ∧ AlgebraicMomentBinding M ∧ M.Matches (p ∘ f) ρ) :=
  cor_helly_operational_iff (albertUniformSeparation 5) p hp

end AlbertSequential

namespace AlbertChallenge.Bridge

open AlbertChallenge

/-- Non-generation passes to subfamilies. -/
theorem not_generates_comp {n k : ℕ} (p : Fin n → Albert) (f : Fin k → Fin n)
    (hg : ¬ Generates p) : ¬ Generates (p ∘ f) := by
  intro hgf
  apply hg
  intro B hB
  exact hgf B fun i => hB (f i)

/-- Non-generation, by Helly number five: atoms fail to generate `J` as soon as every subfamily
of at most five of them does. -/
theorem not_generates_of_small {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (h : ∀ k ≤ 5, ∀ f : Fin k → Fin n, Function.Injective f → ¬ Generates (p ∘ f)) :
    ¬ Generates p := by
  classical
  have hS : ∀ s ∈ Set.range (fun i => toT (p i)), AlbertSequential.IsAtom s := by
    rintro _ ⟨i, rfl⟩
    exact (isAtom_toT (p i)).mpr (hp i)
  have h5 : ∀ T : Finset AlbertSequential.Albert,
      (T : Set AlbertSequential.Albert) ⊆ Set.range (fun i => toT (p i)) → T.card ≤ 5 →
      ∃ B : AlbertSequential.NativeJordanSubalgebra, B ≠ ⊤ ∧
        (T : Set AlbertSequential.Albert) ⊆ (B.carrier : Set AlbertSequential.Albert) := by
    intro T hTp hTcard
    have hidx : ∀ t : T, ∃ i : Fin n, toT (p i) = t.1 := fun t => hTp t.2
    choose idx hidx_eq using hidx
    let T' : Finset (Fin n) := T.attach.image idx
    have hT'card : T'.card ≤ 5 := by
      have hle := Finset.card_image_le (f := idx) (s := T.attach)
      rw [Finset.card_attach] at hle
      exact hle.trans hTcard
    let f : Fin T'.card → Fin n := fun j => T'.orderEmbOfFin rfl j
    have hf : Function.Injective f := (T'.orderEmbOfFin rfl).injective
    have hng := h T'.card hT'card f hf
    obtain ⟨B, hlt, hpB⟩ := exists_proper_native_of_not_generates (p ∘ f) hng
    refine ⟨B, ?_, fun t ht => ?_⟩
    · rintro rfl
      rw [AlbertSequential.H3Subalgebra_O_eq_top] at hlt
      exact lt_irrefl _ hlt
    · have hmem : idx ⟨t, ht⟩ ∈ T' := Finset.mem_image_of_mem idx (Finset.mem_attach T ⟨t, ht⟩)
      have hrange : idx ⟨t, ht⟩ ∈ Set.range f := by
        rw [show Set.range f = (T' : Set (Fin n)) from by
          simp only [f, Finset.range_orderEmbOfFin]]
        exact hmem
      obtain ⟨j, hj⟩ := hrange
      have := hpB j
      simp only [Function.comp_apply, hj, hidx_eq] at this
      exact this
  obtain ⟨B, hB_ne, hSB⟩ :=
    (AlbertSequential.cor_helly_geometric (Set.range fun i => toT (p i)) hS).mpr h5
  intro hg
  apply hB_ne
  apply AlbertSequential.nativeJordanSubalgebra_ext
  have := hg (ofNative B) (fun i => hSB ⟨i, rfl⟩)
  exact this

/-- **cor:helly, model class (I), operational sentence, in the Challenge's terms.** For atoms
`p₁, …, p_n`: a representation from some state exists iff one exists from every state, iff for
every subfamily of at most five tests one exists from some state. -/
theorem cor_helly_classI {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    ((∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn.{0} p ρ Set.univ) ↔
        ∀ ρ, IsDensity ρ → ¬ NoRepresentationOn.{0} p ρ Set.univ) ∧
      ((∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn.{0} p ρ Set.univ) ↔
        ∀ k ≤ 5, ∀ f : Fin k → Fin n, Function.Injective f →
          ∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn.{0} (p ∘ f) ρ Set.univ) := by
  have hcrit := (albert_criterion_bridge p hp)
  have hsub : ∀ {k : ℕ} (f : Fin k → Fin n), (∀ i, IsAtom ((p ∘ f) i)) :=
    fun f i => hp (f i)
  refine ⟨⟨fun h ρ hρ => ?_, fun h => ?_⟩, ⟨fun h k hk f hf => ?_, fun h => ?_⟩⟩
  · -- every state, from the common family of the criterion
    obtain ⟨d, _, _, hrep⟩ := hcrit.2.1.mp (hcrit.2.2.mpr h)
    obtain ⟨M, _, _, hw⟩ := hrep ρ hρ
    exact fun hno => hno.1 ℂ (EuclideanSpace ℂ (Fin d)) M (fun w _ => hw w)
  · obtain ⟨ρ, hρ⟩ := exists_isDensity
    exact ⟨ρ, hρ, h ρ hρ⟩
  · exact ((albert_criterion_bridge (p ∘ f) (hsub f)).2.2.mp
      (not_generates_comp p f (hcrit.2.2.mpr h)))
  · apply hcrit.2.2.mp
    apply not_generates_of_small p hp
    intro k hk f hf
    exact (albert_criterion_bridge (p ∘ f) (hsub f)).2.2.mpr (h k hk f hf)

end AlbertChallenge.Bridge
