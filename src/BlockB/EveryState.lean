/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.StateSupport
public import Uniform.Main
public import WordRelabelling
public import FixedSNativeLeaves
public import ChronologicalWords
public import MatchingModels.UniversalSix

/-! # Seven Steps from Every State (`cor:cer:everystate`)

Formalizes Corollary `cor:cer:everystate`:
- Section 1 (using ONLY `BlockB.StateSupport`, `Uniform.Main`, and the modules they import,
  without invoking `MatchingModels`):
  For any four atoms `p : Fin 4 → Albert` with `0 < fourPointInvariant p` and ANY density
  `ρ : Albert` (`IsDensity ρ`), no `AlgebraicProjectiveData (Fin 4) A`, no real or complex
  `HilbertProjectiveData (Fin 4) 𝕜 H` (`[RCLike 𝕜]`), and no `QuaternionicProjectiveData (Fin 4) Q`
  reproduces `nativeWordProbability p ρ w` for all words `w : Word (Fin 4)` of length `≤ 7`
  whose first outcome is `"yes"` (`w.head?.map Prod.snd = some true`, and equivalently
  `∃ j : Fin 4, w.head? = some (j, true)`).
  Proof route: choose `j : Fin 4` with `0 < tracePairing ρ (p j)` (`exists_atom_pairing_pos`),
  condition the representation on `(j, true)` (`conditionOnYes`), relabel via `Equiv.swap 0 j`
  (`AlgebraicProjectiveData.comap`), and apply `Uniform.Main.uniform_lengthSix_pA_algebraic`.
- Section 2 (using `MatchingModels.UniversalSix`):
  For `ρ = (1 / 3 : ℝ) • albertUnit`, length `7` cannot be replaced by `6`: there exist
  Class-(I) matching models over `ℝ`, `ℂ` (explicit `ℂ¹²` block mixture), `ℍ`, and
  `AlgebraicProjectiveData` reproducing `nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)`
  on all words of length `≤ 6` (and hence in particular on all `"yes"`-initial words of length `≤ 6`).
  Packages the combined challenge theorems `cor_cer_everystate` and `cor_cer_everystate_algebraic`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.BlockB

open AlbertSequential
open AlbertSequential.LengthSeven
open AlbertSequential.LengthSeven.Uniform

/- Lean 4.36 / Mathlib v4.36.0: `Real.lt` is no longer an `irreducible_def`; in this non-module file
defeq checks of `0 < fourPointInvariant p` would evaluate the invariant. No proof here needs its body. -/
attribute [local irreducible] fourPointInvariant

/-! ## Section 1: First Sentence (`cor:cer:everystate`) via Conditioning and Relabelling -/

section ConditionedModel

variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- Condition an algebraic projective model on obtaining outcome `"yes"` on test `j`,
with positive probability `0 < M.probability [(j, true)]`: `φ_j(X) = φ(P_j X P_j) / φ(P_j)`. -/
def conditionOnYes (M : AlgebraicProjectiveData ι A) (j : ι)
    (hj : 0 < M.probability [(j, true)]) : AlgebraicProjectiveData ι A where
  projection := M.projection
  idempotent := M.idempotent
  selfAdjoint := M.selfAdjoint
  state :=
    { toFun := fun X =>
        (M.probability [(j, true)])⁻¹ * M.state (M.projection j * X * M.projection j)
      map_add' := fun X Y => by
        rw [mul_add, add_mul, map_add, mul_add]
      map_smul' := fun r X => by
        rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]
        ring }
  state_unit := by
    have hprob : M.probability [(j, true)] = M.state (M.projection j * 1 * M.projection j) := by
      rw [AlgebraicProjectiveData.probability,
        wordOperator_singleton M.projection M.idempotent M.selfAdjoint (j, true)]
      simp only [algebraicOutcome, ↓reduceIte, mul_one, M.idempotent j]
    change (M.probability [(j, true)])⁻¹ * M.state (M.projection j * 1 * M.projection j) = 1
    rw [← hprob]
    exact inv_mul_cancel₀ hj.ne'
  state_star := fun X => by
    have hs : star (M.projection j * X * M.projection j) =
        M.projection j * star X * M.projection j := by
      rw [star_mul, star_mul, M.selfAdjoint j, mul_assoc]
    change (M.probability [(j, true)])⁻¹ * M.state (M.projection j * star X * M.projection j) =
      (M.probability [(j, true)])⁻¹ * M.state (M.projection j * X * M.projection j)
    rw [← hs, M.state_star]
  state_positive := fun X => by
    have hpos : M.projection j * (star X * X) * M.projection j =
        star (X * M.projection j) * (X * M.projection j) := by
      rw [star_mul, M.selfAdjoint j]
      simp only [mul_assoc]
    change 0 ≤ (M.probability [(j, true)])⁻¹ *
      M.state (M.projection j * (star X * X) * M.projection j)
    rw [hpos]
    exact mul_nonneg (inv_nonneg.mpr hj.le) (M.state_positive (X * M.projection j))

theorem conditionOnYes_probability (M : AlgebraicProjectiveData ι A) (j : ι)
    (hj : 0 < M.probability [(j, true)]) (v : Word ι) :
    (conditionOnYes M j hj).probability v =
      M.probability ((j, true) :: v) / M.probability [(j, true)] := by
  rw [AlgebraicProjectiveData.probability, AlgebraicProjectiveData.probability]
  change (M.probability [(j, true)])⁻¹ *
    M.state (M.projection j * wordOperator M.projection v * M.projection j) =
    M.state (wordOperator M.projection ((j, true) :: v)) / M.probability [(j, true)]
  rw [wordOperator_cons M.projection M.selfAdjoint (j, true) v]
  simp only [algebraicOutcome, ↓reduceIte, div_eq_inv_mul]

end ConditionedModel

section FirstSentence

/-- **cor:cer:everystate` (first sentence), algebraic comparator class**:
for four Albert atoms `p` with `0 < fourPointInvariant p` and any density `ρ` (`IsDensity ρ`),
no `AlgebraicProjectiveData (Fin 4) A` reproduces `nativeWordProbability p ρ` on all words of
length `≤ 7` whose first outcome is `"yes"` (`w.head?.map Prod.snd = some true`). -/
theorem everystate_lengthSeven_algebraic
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head?.map Prod.snd = some true →
      M.probability w = nativeWordProbability p ρ w) : False := by
  obtain ⟨j, hj_pos⟩ := exists_atom_pairing_pos p hp hA ρ hρ
  have h1_eq : M.probability [(j, true)] = tracePairing ρ (p j) := by
    rw [hM [(j, true)] (by simp) rfl, nativeWordProbability_singleton_yes p ρ j (hp j)]
  have hj_prob : 0 < M.probability [(j, true)] := by
    rw [h1_eq]
    exact hj_pos
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 j
  let M' : AlgebraicProjectiveData (Fin 4) A :=
    AlgebraicProjectiveData.comap σ (conditionOnYes M j hj_prob)
  have hp' : ∀ i : Fin 4, IsAtom ((p ∘ σ) i) := fun i => hp (σ i)
  have hA' : 0 < fourPointInvariant (p ∘ σ) := fourPointInvariant_swap_pos p hA j
  refine uniform_lengthSix_pA_algebraic (p ∘ σ) hp' hA' M' (fun u hu => ?_)
  have hlen : ((j, true) :: relabelWord σ u).length ≤ 7 := by
    simp only [List.length_cons, relabelWord_length]
    omega
  have hhead : ((j, true) :: relabelWord σ u).head?.map Prod.snd = some true := rfl
  have hmatch := hM ((j, true) :: relabelWord σ u) hlen hhead
  rw [AlgebraicProjectiveData.comap_probability, conditionOnYes_probability, hmatch, h1_eq]
  rw [nativeWordProbability_cons_yes p ρ j (hp j) (relabelWord σ u),
    nativeWordProbability_relabel p σ (p j) u]
  have hp0 : (p ∘ σ) 0 = p j := by
    simp only [Function.comp_apply, σ, Equiv.swap_apply_left]
  rw [hp0, mul_div_cancel_left₀ _ hj_pos.ne']

/-- Variant of `everystate_lengthSeven_algebraic` phrasing the `"yes"`-initial condition as
`∃ j : Fin 4, w.head? = some (j, true)`. -/
theorem everystate_lengthSeven_algebraic_existsHead
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → (∃ j : Fin 4, w.head? = some (j, true)) →
      M.probability w = nativeWordProbability p ρ w) : False :=
  everystate_lengthSeven_algebraic p hp hA ρ hρ M fun w hw hhead =>
    hM w hw (by
      cases h : w.head? with
      | none => simp [h] at hhead
      | some a =>
        rcases a with ⟨j, b⟩
        simp only [h, Option.map_some] at hhead
        cases hhead
        exact ⟨j, rfl⟩)

/-- **`cor:cer:everystate` (first sentence), real or complex Hilbert space (`[RCLike 𝕜]`)**:
no sequential projective representation on a real or complex Hilbert space reproduces from any
density `ρ` every word of length `≤ 7` beginning with `"yes"`. -/
theorem everystate_lengthSeven_hilbert
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : HilbertProjectiveData (Fin 4) 𝕜 H)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head?.map Prod.snd = some true →
      M.probability w = nativeWordProbability p ρ w) : False :=
  everystate_lengthSeven_algebraic p hp hA ρ hρ M.toAlgebraic fun w hw hhead => by
    rw [M.toAlgebraic_probability]
    exact hM w hw hhead

/-- Variant of `everystate_lengthSeven_hilbert` with `∃ j : Fin 4, w.head? = some (j, true)`. -/
theorem everystate_lengthSeven_hilbert_existsHead
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : HilbertProjectiveData (Fin 4) 𝕜 H)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → (∃ j : Fin 4, w.head? = some (j, true)) →
      M.probability w = nativeWordProbability p ρ w) : False :=
  everystate_lengthSeven_algebraic_existsHead p hp hA ρ hρ M.toAlgebraic fun w hw hhead => by
    rw [M.toAlgebraic_probability]
    exact hM w hw hhead

/-- **`cor:cer:everystate` (first sentence), quaternionic Hilbert model**:
no quaternionic sequential projective representation reproduces from any density `ρ` every word
of length `≤ 7` beginning with `"yes"`. -/
theorem everystate_lengthSeven_quaternionic
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H}
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : QuaternionicProjectiveData (Fin 4) Q)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head?.map Prod.snd = some true →
      M.state (M.wordEffect w) = nativeWordProbability p ρ w) : False :=
  everystate_lengthSeven_algebraic p hp hA ρ hρ M.toAlgebraic fun w hw hhead => by
    rw [M.toAlgebraic_probability]
    exact hM w hw hhead

/-- Variant of `everystate_lengthSeven_quaternionic` with `∃ j : Fin 4, w.head? = some (j, true)`. -/
theorem everystate_lengthSeven_quaternionic_existsHead
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H}
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : QuaternionicProjectiveData (Fin 4) Q)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → (∃ j : Fin 4, w.head? = some (j, true)) →
      M.state (M.wordEffect w) = nativeWordProbability p ρ w) : False :=
  everystate_lengthSeven_algebraic_existsHead p hp hA ρ hρ M.toAlgebraic fun w hw hhead => by
    rw [M.toAlgebraic_probability]
    exact hM w hw hhead

end FirstSentence

/-! ## Section 2: Length-Six Counterexample for `ρ = e / 3` and Full `cor:cer:everystate` -/

section UniversalSixAndCombined

open AlbertSequential.MatchingModels

/-- For `ρ = e / 3`, a `ℂ¹²` complex Hilbert model reproduces all words of length `≤ 6`. -/
theorem everystate_e3_six_fails_c12 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w : Word (Fin 4), w.length ≤ 6 →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w :=
  prop_cer_universalsix_c12 p hp hA

/-- For `ρ = e / 3`, a real Hilbert model reproduces all words of length `≤ 6`. -/
theorem everystate_e3_six_fails_real (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (M : HilbertProjectiveData (Fin 4) ℝ H),
      ∀ w : Word (Fin 4), w.length ≤ 6 →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w :=
  prop_cer_universalsix_real p hp hA

/-- For `ρ = e / 3`, a quaternionic Hilbert model reproduces all words of length `≤ 6`. -/
theorem everystate_e3_six_fails_quaternionic (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (Q : QuaternionicOperatorStructure H) (M : QuaternionicProjectiveData (Fin 4) Q),
      ∀ w : Word (Fin 4), w.length ≤ 6 →
        M.state (M.wordEffect w) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w :=
  prop_cer_universalsix_quaternionic p hp hA

/-- For `ρ = e / 3`, an `AlgebraicProjectiveData` model reproduces all words of length `≤ 6`. -/
theorem everystate_e3_six_fails_algebraic (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (A : Type) (_ : Ring A) (_ : StarRing A) (_ : Module ℝ A)
      (_ : IsScalarTower ℝ A A) (_ : SMulCommClass ℝ A A) (_ : StarModule ℝ A)
      (M : AlgebraicProjectiveData (Fin 4) A),
      ∀ w : Word (Fin 4), w.length ≤ 6 →
        M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w :=
  prop_cer_universalsix_algebraic p hp hA

/-- **Complete `cor:cer:everystate`, Class (I) (`ℝ`, `ℂ`, `ℍ`)**:
For any four atoms `p` of `Albert` with `0 < fourPointInvariant p`:
1. For every state `ρ : Albert` (`IsDensity ρ`), no sequential projective representation over
   `ℝ`, `ℂ`, or `ℍ` (in any dimension, with projections of any rank and any state) reproduces
   from `ρ` the probability of every word of length `≤ 7` whose first outcome is `"yes"`.
2. For `ρ = (1 / 3 : ℝ) • albertUnit` (`IsDensity ((1 / 3 : ℝ) • albertUnit)`), length `7` cannot
   be replaced by `6`: matching representations over `ℝ`, `ℂ` (`ℂ¹²`), and `ℍ` exist reproducing
   every word of length `≤ 6` (and hence in particular every word of length `≤ 6` whose first
   outcome is `"yes"`). -/
theorem cor_cer_everystate (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    (∀ ρ : Albert, IsDensity ρ →
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (M : HilbertProjectiveData (Fin 4) ℝ H),
        ¬ (∀ w : Word (Fin 4), w.length ≤ 7 → w.head?.map Prod.snd = some true →
          M.probability w = nativeWordProbability p ρ w)) ∧
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : HilbertProjectiveData (Fin 4) ℂ H),
        ¬ (∀ w : Word (Fin 4), w.length ≤ 7 → w.head?.map Prod.snd = some true →
          M.probability w = nativeWordProbability p ρ w)) ∧
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (Q : QuaternionicOperatorStructure H) (M : QuaternionicProjectiveData (Fin 4) Q),
        ¬ (∀ w : Word (Fin 4), w.length ≤ 7 → w.head?.map Prod.snd = some true →
          M.state (M.wordEffect w) = nativeWordProbability p ρ w))) ∧
    (IsDensity ((1 / 3 : ℝ) • albertUnit) ∧
      (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (M : HilbertProjectiveData (Fin 4) ℝ H),
        ∀ w : Word (Fin 4), w.length ≤ 6 →
          M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) ∧
      (∃ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
        ∀ w : Word (Fin 4), w.length ≤ 6 →
          M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) ∧
      (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (Q : QuaternionicOperatorStructure H) (M : QuaternionicProjectiveData (Fin 4) Q),
        ∀ w : Word (Fin 4), w.length ≤ 6 →
          M.state (M.wordEffect w) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)) := by
  refine ⟨fun ρ hρ => ⟨?_, ?_, ?_⟩, native_maximally_mixed_density,
    everystate_e3_six_fails_real p hp hA,
    everystate_e3_six_fails_c12 p hp hA,
    everystate_e3_six_fails_quaternionic p hp hA⟩
  · intro H _ _ _ M hM
    exact everystate_lengthSeven_hilbert p hp hA ρ hρ M hM
  · intro H _ _ _ M hM
    exact everystate_lengthSeven_hilbert p hp hA ρ hρ M hM
  · intro H _ _ _ Q M hM
    exact everystate_lengthSeven_quaternionic p hp hA ρ hρ M hM

/-- Algebraic comparator version of `cor_cer_everystate`:
for every density `ρ`, no `AlgebraicProjectiveData (Fin 4) A` matches all `"yes"`-initial words
of length `≤ 7`, while at `ρ = (1 / 3 : ℝ) • albertUnit` an `AlgebraicProjectiveData (Fin 4) A`
matches all words of length `≤ 6`. -/
theorem cor_cer_everystate_algebraic (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    (∀ ρ : Albert, IsDensity ρ →
      ∀ (A : Type) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin 4) A),
        ¬ (∀ w : Word (Fin 4), w.length ≤ 7 → w.head?.map Prod.snd = some true →
          M.probability w = nativeWordProbability p ρ w)) ∧
    (IsDensity ((1 / 3 : ℝ) • albertUnit) ∧
      ∃ (A : Type) (_ : Ring A) (_ : StarRing A) (_ : Module ℝ A)
        (_ : IsScalarTower ℝ A A) (_ : SMulCommClass ℝ A A) (_ : StarModule ℝ A)
        (M : AlgebraicProjectiveData (Fin 4) A),
        ∀ w : Word (Fin 4), w.length ≤ 6 →
          M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) := by
  refine ⟨fun ρ hρ A _ _ _ _ _ _ M hM => ?_, native_maximally_mixed_density,
    everystate_e3_six_fails_algebraic p hp hA⟩
  exact everystate_lengthSeven_algebraic p hp hA ρ hρ M hM

end UniversalSixAndCombined

end AlbertSequential.BlockB

#print axioms AlbertSequential.BlockB.conditionOnYes
#print axioms AlbertSequential.BlockB.conditionOnYes_probability
#print axioms AlbertSequential.BlockB.everystate_lengthSeven_algebraic
#print axioms AlbertSequential.BlockB.everystate_lengthSeven_algebraic_existsHead
#print axioms AlbertSequential.BlockB.everystate_lengthSeven_hilbert
#print axioms AlbertSequential.BlockB.everystate_lengthSeven_hilbert_existsHead
#print axioms AlbertSequential.BlockB.everystate_lengthSeven_quaternionic
#print axioms AlbertSequential.BlockB.everystate_lengthSeven_quaternionic_existsHead
#print axioms AlbertSequential.BlockB.everystate_e3_six_fails_c12
#print axioms AlbertSequential.BlockB.everystate_e3_six_fails_real
#print axioms AlbertSequential.BlockB.everystate_e3_six_fails_quaternionic
#print axioms AlbertSequential.BlockB.everystate_e3_six_fails_algebraic
#print axioms AlbertSequential.BlockB.cor_cer_everystate
#print axioms AlbertSequential.BlockB.cor_cer_everystate_algebraic
