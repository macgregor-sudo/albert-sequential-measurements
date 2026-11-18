/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.Models

/-!
# No representation for generating atoms; the finite separating inequality

Theorem 1 rests on `AlbertSequential.algebraicProjective_not_matches_generating_atoms`
(`AlgebraicProjectiveNoGo`); theorem 2 on `uniformMomentSeparator_generating_atoms`
(`AlbertUniformSeparation`) and `wordFunctional_nonnegative_on_algebraic_models`
(`AlgebraicSeparationAssembly`), the same two results from which the development derives
`HilbertModelSeparation.uniformHilbertSeparator_generating_atoms`. Each Challenge model is first
turned into the development's algebraic comparator by `Bridge.Models`.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge

universe v

/-- An algebraic comparator whose word probabilities are `g` cannot reproduce generating atoms. -/
theorem not_matches_of_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] {n : ℕ}
    (M : AlbertSequential.AlgebraicProjectiveData (Fin n) A) (g : Word n → ℝ)
    (hM : ∀ w, M.probability w = g w) (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hgen : Generates p) (ρ : Albert) :
    ¬ ∀ w ∈ (Set.univ : Set (Word n)), g w = wordProbability p ρ w := by
  intro h
  apply AlbertSequential.algebraicProjective_not_matches_generating_atoms M (fun i => toT (p i))
    (atoms_toT hp) ((generates_toT p).2 hgen) (toT ρ)
  intro w
  rw [hM w, h w (Set.mem_univ w), wordProbability_toT]

theorem no_representation_bridge {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) (ρ : Albert) : NoRepresentationOn.{v} p ρ Set.univ := by
  refine ⟨fun 𝕜 H _ _ _ _ M => ?_, fun H _ _ _ S M => ?_, fun A _ _ _ _ M => ?_⟩
  · exact not_matches_of_algebraic (ofProjectiveRepresentation M) M.probability
      (ofProjectiveRepresentation_probability M) p hp hg ρ
  · exact not_matches_of_algebraic (ofQuaternionicRepresentation M) M.probability
      (ofQuaternionicRepresentation_probability M) p hp hg ρ
  · exact not_matches_of_algebraic (ofAlgebraicModel M) M.probability
      (ofAlgebraicModel_probability M) p hp hg ρ

/-! ### Lists of weighted words versus finite sums with coefficients -/

/-- The coefficient of the word `w` in a list of weighted words (duplicates merged). -/
def coefficient {n : ℕ} (l : List (ℝ × Word n)) (w : Word n) : ℝ :=
  (l.map (fun t => if t.2 = w then t.1 else 0)).sum

theorem sum_coefficient {n : ℕ} (f : Word n → ℝ) (l : List (ℝ × Word n)) (W : Finset (Word n))
    (hW : ∀ t ∈ l, t.2 ∈ W) :
    ∑ w ∈ W, coefficient l w * f w = (l.map (fun t => t.1 * f t.2)).sum := by
  induction l with
  | nil => simp [coefficient]
  | cons t l ih =>
    have ht : t.2 ∈ W := hW t (List.mem_cons_self ..)
    have ih' := ih (fun s hs => hW s (List.mem_cons_of_mem _ hs))
    simp only [coefficient, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib] at ih' ⊢
    rw [ih']
    congr 1
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, ite_eq_left ht]

theorem evaluate_eq_sum {n : ℕ} (c : AlbertSequential.FiniteRealWordFunctional n)
    (f : Word n → ℝ) :
    c.evaluate f = ∑ w ∈ (c.terms.map Prod.snd).toFinset, coefficient c.terms w * f w := by
  rw [sum_coefficient f c.terms _ (fun t ht => List.mem_toFinset.2 (List.mem_map_of_mem ht))]
  rfl

/-- A development separator functional is nonnegative on every algebraic comparator, written as
a finite sum with merged coefficients. Instance arguments are implicit (read off `M`'s type). -/
theorem nonneg_of_algebraic {n : ℕ} (c : AlbertSequential.FiniteRealWordFunctional n)
    (hc : ∀ m, AlbertSequential.AdmissibleProjectionMoments n m →
      0 ≤ c.evaluate (AlbertSequential.momentWordProbability m))
    {A : Type*} {_ : Ring A} {_ : StarRing A} {_ : Module ℝ A}
    {_ : IsScalarTower ℝ A A} {_ : SMulCommClass ℝ A A} {_ : StarModule ℝ A}
    (M : AlbertSequential.AlgebraicProjectiveData (Fin n) A) (g : Word n → ℝ)
    (hM : ∀ w, M.probability w = g w) :
    0 ≤ ∑ w ∈ (c.terms.map Prod.snd).toFinset, coefficient c.terms w * g w := by
  rw [← evaluate_eq_sum]
  have h := AlbertSequential.wordFunctional_nonnegative_on_algebraic_models c hc M
  rwa [show M.probability = g from funext hM] at h

theorem linear_separator_bridge {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) :
    ∃ (L : ℕ) (W : Finset (Word n)) (c : Word n → ℝ) (γ : ℝ), 0 < γ ∧ (∀ w ∈ W, w.length ≤ L) ∧
      (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (M : ProjectiveRepresentation n ℝ H), 0 ≤ ∑ w ∈ W, c w * M.probability w) ∧
      (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : ProjectiveRepresentation n ℂ H), 0 ≤ ∑ w ∈ W, c w * M.probability w) ∧
      (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation n S),
        0 ≤ ∑ w ∈ W, c w * M.probability w) ∧
      (∀ ρ, IsDensity ρ → ∑ w ∈ W, c w * wordProbability p ρ w ≤ -γ) := by
  obtain ⟨L, c, γ, hγ, hL, hc, hnative⟩ :=
    AlbertSequential.uniformMomentSeparator_generating_atoms (fun i => toT (p i))
      (atoms_toT hp) ((generates_toT p).2 hg)
  refine ⟨L, (c.terms.map Prod.snd).toFinset, coefficient c.terms, γ, hγ, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hw)
    exact hL t ht
  · intro H _ _ _ M
    exact nonneg_of_algebraic c hc (ofProjectiveRepresentation M) _ (ofProjectiveRepresentation_probability M)
  · intro H _ _ _ M
    exact nonneg_of_algebraic c hc (ofProjectiveRepresentation M) _ (ofProjectiveRepresentation_probability M)
  · intro H _ _ _ S M
    exact nonneg_of_algebraic c hc (ofQuaternionicRepresentation M) _ (ofQuaternionicRepresentation_probability M)
  · intro ρ hρ
    rw [← evaluate_eq_sum]
    have hmem : toT ρ ∈ AlbertSequential.nativeDensitySet := by
      unfold AlbertSequential.nativeDensitySet
      exact Set.mem_ofPred.2 ((isDensity_toT ρ).2 hρ)
    have h := hnative (toT ρ) hmem
    rwa [show AlbertSequential.nativeWordProbability (fun i => toT (p i)) (toT ρ) =
      wordProbability p ρ from funext (wordProbability_toT p ρ)] at h

end AlbertChallenge.Bridge
