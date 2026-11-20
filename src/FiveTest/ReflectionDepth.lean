/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.Budget
public import BlockB.ElevenTheorem

/-! The finite reflection-depth obstruction for arbitrary atom menus.
A signed orbit corner costs at most twice its reflection depth plus one. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

open AlbertSequential.NativeAnalysis

section Lift

variable {ι A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

/-- A reflection word of length k adds at most k original outcomes. -/
theorem liftSpace_reflectionWord (P : ι → A) (θ : Word ι → J) (U : Outcome ι → Module.End ℝ J)
    (hstar : ∀ i, star (P i) = P i) (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (g : List ι) {L : ℕ} {Z : A} {x : J} (h : (Z, x) ∈ liftSpace P θ L) :
    (projectionReflectionWord P g * Z * star (projectionReflectionWord P g),
      reflectionWordUpdate U g x) ∈ liftSpace P θ (L + g.length) := by
  induction g with
  | nil => simpa only [List.length_nil, Nat.add_zero, projectionReflectionWord, reflectionWordUpdate,
      star_one, one_mul, mul_one, one_apply_eq_self] using h
  | cons i g ih =>
    have hs := liftSpace_reflection P θ U hstar hθ i ih
    simpa only [List.length_cons, ← Nat.add_assoc, projectionReflectionWord, reflectionWordUpdate,
      LinearMap.comp_apply, star_mul, projectionReflection_star P hstar, mul_assoc] using hs

end Lift

section Orbit

variable {ι κ A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

private theorem orbitOutcome_factorization (P : ι → A)
    (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (α : κ → ReflectionOrbitLabel ι) (a : Outcome κ) :
    algebraicOutcome (fun k => orbitProjection P (α k).1 (α k).2) a =
      projectionReflectionWord P (α a.1).1 * algebraicOutcome P ((α a.1).2, a.2) *
        star (projectionReflectionWord P (α a.1).1) := by
  rcases a with ⟨k, b⟩
  cases b
  · simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte, orbitProjection,
      mul_sub, sub_mul, mul_one, projectionReflectionWord_mul_star P hp hstar]
  · rfl

private theorem nativeOrbitOutcome_factorization (p : ι → Albert) (hp : ∀ i, IsAtom (p i))
    (α : κ → ReflectionOrbitLabel ι) (a : Outcome κ) (x : Albert) :
    reflectionWordUpdate (nativeOutcomeUpdate p) (α a.1).1
      (nativeOutcomeUpdate p ((α a.1).2, a.2)
        (reflectionWordUpdate (nativeOutcomeUpdate p) (α a.1).1.reverse x)) =
      quadraticMap (nativeOutcome (nativeOrbitPoint p hp ∘ α) a) x := by
  simp only [reflectionWordUpdate_native p hp, nativeOutcomeUpdate, quadraticMapLinear_apply]
  rw [nativeAutomorphism_quadraticMap, nativeReflectionWord_reverse_right]
  congr 1
  rcases a with ⟨k, b⟩
  cases b
  · simp only [nativeOutcome, Bool.false_eq_true, ↓reduceIte, map_sub,
      (nativeReflectionWordAutomorphism p hp (α k).1).preserves_unit, Function.comp_apply,
      nativeOrbitPoint]
  · rfl

/-- Both signed corners for an orbit label admit paired lifts at cost (2|g|+1). -/
theorem liftSpace_orbitOutcome (P : ι → A)
    (hP : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (p : ι → Albert) (hp : ∀ i, IsAtom (p i)) (α : κ → ReflectionOrbitLabel ι) (a : Outcome κ)
    {L : ℕ} {Z : A} {x : Albert} (h : (Z, x) ∈ liftSpace P (nativeWordEffect p) L) :
    let q := algebraicOutcome (fun i => orbitProjection P (α i).1 (α i).2) a
    (q * Z * q, quadraticMap (nativeOutcome (nativeOrbitPoint p hp ∘ α) a) x) ∈
      liftSpace P (nativeWordEffect p) (L + 2 * (α a.1).1.length + 1) := by
  let g := (α a.1).1
  let U := nativeOutcomeUpdate p
  have hstep : ∀ b w, nativeWordEffect p (b :: w) = U b (nativeWordEffect p w) := fun _ _ => rfl
  have hr := liftSpace_reflectionWord P (nativeWordEffect p) U hstar hstep g.reverse h
  have hc := liftSpace_prefix P (nativeWordEffect p) U hstar hstep ((α a.1).2, a.2) hr
  have hf := liftSpace_reflectionWord P (nativeWordEffect p) U hstar hstep g hc
  have hL : L + g.reverse.length + 1 + g.length = L + 2 * g.length + 1 := by
    rw [List.length_reverse]; omega
  rw [hL] at hf
  dsimp only
  rw [orbitOutcome_factorization P hP hstar, ← nativeOrbitOutcome_factorization p hp α a x]
  simpa only [g, U, projectionReflectionWord_reverse P hstar, star_star, mul_assoc] using hf

/-- Use the actual orbit projections with the original normalized positive state. -/
def reflectionOrbitModel (M : AlgebraicProjectiveData ι A) (α : κ → ReflectionOrbitLabel ι) :
    AlgebraicProjectiveData κ A where
  projection k := orbitProjection M.projection (α k).1 (α k).2
  idempotent k := orbitProjection_idempotent M.projection M.idempotent M.selfAdjoint (α k).1 (α k).2
  selfAdjoint k := orbitProjection_star M.projection M.selfAdjoint (α k).1 (α k).2
  state := M.state
  state_unit := M.state_unit
  state_star := M.state_star
  state_positive := M.state_positive

/-- An m-letter word on orbit points of depth at most d has paired original
lifts of length at most m(2d+1). -/
theorem liftSpace_reflectionOrbitWord (M : AlgebraicProjectiveData ι A) (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (α : κ → ReflectionOrbitLabel ι) (d : ℕ)
    (hdepth : ∀ k, (α k).1.length ≤ d) (w : Word κ) :
    (wordOperator (reflectionOrbitModel M α).projection w, nativeWordEffect (nativeOrbitPoint p hp ∘ α) w) ∈
      liftSpace M.projection (nativeWordEffect p) (w.length * (2 * d + 1)) := by
  induction w with
  | nil => exact liftSpace_word M.projection (nativeWordEffect p) [] (by simp)
  | cons a w ih =>
    rw [wordOperator_cons _ (reflectionOrbitModel M α).selfAdjoint]
    have hx := liftSpace_orbitOutcome M.projection M.idempotent M.selfAdjoint p hp α a ih
    have hL : w.length * (2 * d + 1) + 2 * (α a.1).1.length + 1 ≤ (a :: w).length * (2 * d + 1) := by
      rw [List.length_cons, Nat.add_mul]
      have hd := hdepth a.1
      omega
    exact liftSpace_mono M.projection (nativeWordEffect p) hL hx

/-- Agreement through the original horizon transfers to the reflected menus. -/
theorem reflectionOrbitModel_probability (M : AlgebraicProjectiveData ι A)
    (p : ι → Albert) (hp : ∀ i, IsAtom (p i)) (α : κ → ReflectionOrbitLabel ι)
    (d : ℕ) (hdepth : ∀ k, (α k).1.length ≤ d) (ρ : Albert) (L : ℕ)
    (hM : ∀ w : Word ι, w.length ≤ L → M.probability w = nativeWordProbability p ρ w)
    (w : Word κ) (hw : w.length * (2 * d + 1) ≤ L) :
    (reflectionOrbitModel M α).probability w = nativeWordProbability (nativeOrbitPoint p hp ∘ α) ρ w := by
  have hpairs := liftSpace_mono M.projection (nativeWordEffect p) hw
    (liftSpace_reflectionOrbitWord M p hp α d hdepth w)
  have hm : ∀ z : Word ι, z.length ≤ L →
      M.state (wordOperator M.projection z) = tracePairingLin ρ (nativeWordEffect p z) := by
    intro z hz
    exact (hM z hz).trans (nativeWordProbability_eq_pairing p ρ z)
  exact (liftSpace_expectation M.projection (nativeWordEffect p) M.state (tracePairingLin ρ) hm hpairs).trans
    (nativeWordProbability_eq_pairing (nativeOrbitPoint p hp ∘ α) ρ w).symm

end Orbit

/-- Explicit list of original words through the given horizon. It includes
all expansions needed by the reflection-depth certificate. -/
def boundedReflectionWords (n : ℕ) : ℕ → List (Word (Fin n))
  | 0 => [[]]
  | L + 1 => [] :: (List.ofFn (fun i : Fin n => i)).flatMap (fun i =>
      (boundedReflectionWords n L).map ((i, false) :: ·) ++
        (boundedReflectionWords n L).map ((i, true) :: ·))

theorem mem_boundedReflectionWords {n L : ℕ} (w : Word (Fin n)) :
    w ∈ boundedReflectionWords n L ↔ w.length ≤ L := by
  induction L generalizing w with
  | zero => simp [boundedReflectionWords]
  | succ L ih =>
    cases w with
    | nil => simp [boundedReflectionWords]
    | cons a w =>
      rcases a with ⟨i, b⟩
      cases b <;> simp [boundedReflectionWords, List.mem_ofFn, ih]

/-- The e/3 clause of the reflection-depth obstruction on an explicit finite list. -/
theorem reflectionDepth_maximallyMixed_no_algebraicModel {n d : ℕ} {A : Type*}
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (α : Fin 4 → ReflectionOrbitLabel (Fin n))
    (hdepth : ∀ k, (α k).1.length ≤ d) (hpos : 0 < fourPointInvariant (nativeOrbitPoint p hp ∘ α))
    (M : AlgebraicProjectiveData (Fin n) A) :
    ¬ ∀ w ∈ boundedReflectionWords n (11 * (2 * d + 1)),
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  intro hM
  apply BlockB.thm_eleven_a_algebraic _ (fun k => nativeOrbitPoint_isAtom p hp (α k)) hpos
    (reflectionOrbitModel M α)
  intro w hw
  exact reflectionOrbitModel_probability M p hp α d hdepth _ _
    (fun w hw => hM w ((mem_boundedReflectionWords w).mpr hw)) w
    (Nat.mul_le_mul_right _ (Ends.Eleven.elevenBase_shape w hw).2.2)

/-- The companion reflection-depth obstruction for every native density. -/
theorem reflectionDepth_no_algebraicModel {n d : ℕ} {A : Type*}
    [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (α : Fin 4 → ReflectionOrbitLabel (Fin n))
    (hdepth : ∀ k, (α k).1.length ≤ d) (hpos : 0 < fourPointInvariant (nativeOrbitPoint p hp ∘ α))
    (ρ : Albert) (hρ : IsDensity ρ) (M : AlgebraicProjectiveData (Fin n) A) :
    ¬ ∀ w ∈ boundedReflectionWords n (11 * (2 * d + 1)),
      M.probability w = nativeWordProbability p ρ w := by
  intro hM
  apply BlockB.thm_eleven_b_algebraic _ (fun k => nativeOrbitPoint_isAtom p hp (α k)) hpos ρ hρ
    (reflectionOrbitModel M α)
  intro w hw
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
  exact reflectionOrbitModel_probability M p hp α d hdepth ρ _
    (fun w hw => hM w ((mem_boundedReflectionWords w).mpr hw)) w
    (Nat.mul_le_mul_right _ (BlockB.elevenFamily_shape i hi).2.2)

/-- Real and complex Hilbert-space models, with arbitrary dimensions and states. -/
theorem reflectionDepth_no_hilbertModel {n d : ℕ} {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (α : Fin 4 → ReflectionOrbitLabel (Fin n))
    (hdepth : ∀ k, (α k).1.length ≤ d) (hpos : 0 < fourPointInvariant (nativeOrbitPoint p hp ∘ α))
    (ρ : Albert) (hρ : IsDensity ρ) (M : HilbertProjectiveData (Fin n) 𝕜 H) :
    ¬ ∀ w ∈ boundedReflectionWords n (11 * (2 * d + 1)),
      M.probability w = nativeWordProbability p ρ w := by
  intro hmatch
  apply reflectionDepth_no_algebraicModel p hp α hdepth hpos ρ hρ M.toAlgebraic
  intro w hw
  rw [M.toAlgebraic_probability]
  exact hmatch w hw

/-- Right-quaternionic Hilbert-space models, with arbitrary dimensions and states. -/
theorem reflectionDepth_no_quaternionicModel {n d : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H}
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (α : Fin 4 → ReflectionOrbitLabel (Fin n))
    (hdepth : ∀ k, (α k).1.length ≤ d) (hpos : 0 < fourPointInvariant (nativeOrbitPoint p hp ∘ α))
    (ρ : Albert) (hρ : IsDensity ρ) (M : QuaternionicProjectiveData (Fin n) Q) :
    ¬ ∀ w ∈ boundedReflectionWords n (11 * (2 * d + 1)),
      M.state (M.wordEffect w) = nativeWordProbability p ρ w := by
  intro hmatch
  apply reflectionDepth_no_algebraicModel p hp α hdepth hpos ρ hρ M.toAlgebraic
  intro w hw
  rw [M.toAlgebraic_probability]
  exact hmatch w hw

end AlbertSequential.FiveTest
