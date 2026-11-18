/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.Quad
public import SequentialEffectLifts
public import NativeReflectionOrbit
public import NativeWordDuality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Reflection transfer with cost (companion lem:five:reflect (b)–(d))

**General part** (`liftSpace`): the span of the paired evaluations
`(wordOperator P w, θ w)` over the words with `|w| ≤ L`, a length-bounded refinement of
`sequentialEffectLiftSpace`.  Prefixing one outcome costs one letter
(`liftSpace_prefix`); conjugation by `Σ_c = 2P_c − 1` costs one letter
(`liftSpace_reflection`: `ΣXΣ = 2PXP + 2(1−P)X(1−P) − X`, i.e. "nothing or one outcome of
`p_c`" at one place, with coefficients `2, 2, −1`); matching on all words with `|w| ≤ L`
extends to the whole space (`liftSpace_expectation`).

**Five tests** (`quadProj`, `quadCost`, `quad_lift`): with `P : Fin 5 → A` the projections of
the five tests and `Σ = 2P₂ − 1`, the quadruple projections are
`(P₀, P₁, ΣP₃Σ, ΣP₄Σ)` (letters `A,B,C,D = 0,1,2,3`, `C`, `D` reflected), on the native side
`(p₀, p₁, U_r p₃, U_r p₄) = reflQuad`.  For every quadruple word `u`, the pair
(model effect of `u`, native effect of `u`) lies in the span of the five-test pairs of length
at most `(quadCost u).1`, and `(quadCost u).1 = |u| + ν(u)` (proved in `FiveTest.Budget`
against the budget function of Lemma A).  This is lem:five:reflect(c) in the form used by
prop:five:short(a): the expansion words are not listed, their span membership is proved, with
the same length bound `|w_k| ≤ |u| + ν(u)` (route difference: no explicit `N ≤ 3^ν` list;
the count is not needed for (a)). -/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

open AlbertSequential.NativeAnalysis

/-! ## Length-bounded paired lift spaces -/

section Lift

variable {ι A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

/-- Span of the paired evaluations of the words of length at most `L`. -/
def liftSpace (P : ι → A) (θ : Word ι → J) (L : ℕ) : Submodule ℝ (A × J) :=
  Submodule.span ℝ {z | ∃ w : Word ι, w.length ≤ L ∧ z = (wordOperator P w, θ w)}

theorem liftSpace_word (P : ι → A) (θ : Word ι → J) {L : ℕ} (w : Word ι) (hw : w.length ≤ L) :
    (wordOperator P w, θ w) ∈ liftSpace P θ L :=
  Submodule.subset_span ⟨w, hw, rfl⟩

theorem liftSpace_mono (P : ι → A) (θ : Word ι → J) {L L' : ℕ} (h : L ≤ L') :
    liftSpace P θ L ≤ liftSpace P θ L' :=
  Submodule.span_mono (fun _ ⟨w, hw, hz⟩ => ⟨w, hw.trans h, hz⟩)

theorem liftSpace_prefix (P : ι → A) (θ : Word ι → J) (U : Outcome ι → Module.End ℝ J)
    (hstar : ∀ i, star (P i) = P i) (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (a : Outcome ι) {L : ℕ} {Z : A} {x : J} (h : (Z, x) ∈ liftSpace P θ L) :
    (algebraicOutcome P a * Z * algebraicOutcome P a, U a x) ∈ liftSpace P θ (L + 1) := by
  have hclosed : ∀ z ∈ liftSpace P θ L,
      sequentialLiftCorner P U a z ∈ liftSpace P θ (L + 1) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨w, hw, rfl⟩ := hz
        change (algebraicOutcome P a * wordOperator P w * algebraicOutcome P a, U a (θ w)) ∈ _
        rw [← wordOperator_cons P hstar, ← hθ]
        exact liftSpace_word P θ (a :: w) (by simp only [List.length_cons]; omega)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add z w _ _ ihz ihw => rw [map_add]; exact Submodule.add_mem _ ihz ihw
    | smul r z _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih
  exact hclosed (Z, x) h

theorem liftSpace_reflection (P : ι → A) (θ : Word ι → J) (U : Outcome ι → Module.End ℝ J)
    (hstar : ∀ i, star (P i) = P i) (hθ : ∀ a w, θ (a :: w) = U a (θ w))
    (i : ι) {L : ℕ} {Z : A} {x : J} (h : (Z, x) ∈ liftSpace P θ L) :
    (projectionReflection P i * Z * projectionReflection P i, sequentialReflectionUpdate U i x) ∈
      liftSpace P θ (L + 1) := by
  have hy := liftSpace_prefix P θ U hstar hθ (i, true) h
  have hn := liftSpace_prefix P θ U hstar hθ (i, false) h
  have h' := liftSpace_mono P θ (Nat.le_succ L) h
  have hc := Submodule.sub_mem _ (Submodule.smul_mem _ (2 : ℝ) (Submodule.add_mem _ hy hn)) h'
  have he : (2 : ℝ) •
      (algebraicOutcome P (i, true) * Z * algebraicOutcome P (i, true) +
        algebraicOutcome P (i, false) * Z * algebraicOutcome P (i, false)) - Z =
      projectionReflection P i * Z * projectionReflection P i := by
    simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte, projectionReflection, two_smul]
    noncomm_ring
  have hx : (2 : ℝ) • (U (i, true) x + U (i, false) x) - x = sequentialReflectionUpdate U i x := by
    simp only [sequentialReflectionUpdate, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.add_apply, one_apply_eq_self]
  have hpair : (2 : ℝ) • ((algebraicOutcome P (i, true) * Z * algebraicOutcome P (i, true),
      U (i, true) x) + (algebraicOutcome P (i, false) * Z * algebraicOutcome P (i, false),
      U (i, false) x)) - (Z, x) =
      (projectionReflection P i * Z * projectionReflection P i, sequentialReflectionUpdate U i x) := by
    rw [← he, ← hx]; rfl
  rw [hpair] at hc
  exact hc

theorem liftSpace_expectation (P : ι → A) (θ : Word ι → J)
    (φ : A →ₗ[ℝ] ℝ) (ω : J →ₗ[ℝ] ℝ) {L : ℕ}
    (hmatch : ∀ w : Word ι, w.length ≤ L → φ (wordOperator P w) = ω (θ w))
    {Z : A} {x : J} (h : (Z, x) ∈ liftSpace P θ L) : φ Z = ω x := by
  have he : ∀ y ∈ liftSpace P θ L, φ y.1 = ω y.2 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        exact hmatch w hw
    | zero => simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
    | add y z _ _ ihy ihz => simp only [Prod.fst_add, Prod.snd_add, map_add, ihy, ihz]
    | smul r y _ ih => simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ih]
  exact he (Z, x) h

end Lift

/-! ## Native facts about `r = 2p₂ − e` -/

theorem qr_sq : qr.jmul qr = QA.unit := by decide +kernel

theorem reflR_sq : jordanMul reflR reflR = albertUnit := by
  rw [reflR_eq_cast, ← castA_jmul, qr_sq, castA_unit]

theorem reflR_unit : quadraticMap reflR albertUnit = albertUnit := by
  rw [NativeAnalysis.quadraticMap_unit_argument, reflR_sq]

/-- `U_r` as the reflection automorphism (`atomReflectionAutomorphism`). -/
theorem reflR_apply (x : Albert) :
    (atomReflectionAutomorphism (pentadF 2) (pentadF_isAtom 2)).linearEquiv x =
      quadraticMap reflR x :=
  atomReflectionAutomorphism_apply _ _ x

theorem reflR_involutive (x : Albert) : quadraticMap reflR (quadraticMap reflR x) = x :=
  atomReflection_involutive (pentadF 2) (pentadF_isAtom 2) x

/-- `U_{U_r q} = U_r U_q U_r` (lem:five:reflect(a)). -/
theorem quadraticMap_reflected (q y : Albert) :
    quadraticMap (quadraticMap reflR q) y =
      quadraticMap reflR (quadraticMap q (quadraticMap reflR y)) := by
  have h := nativeAutomorphism_quadraticMap
    (atomReflectionAutomorphism (pentadF 2) (pentadF_isAtom 2)) q (quadraticMap reflR y)
  rw [reflR_apply, reflR_apply, reflR_apply, reflR_involutive] at h
  exact h.symm

/-- `e − U_r q = U_r (e − q)` (lem:five:reflect(a)). -/
theorem unit_sub_reflected (q : Albert) :
    albertUnit - quadraticMap reflR q = quadraticMap reflR (albertUnit - q) := by
  rw [show quadraticMap reflR (albertUnit - q) =
      quadraticMapLinear reflR (albertUnit - q) from rfl, map_sub]
  simp only [quadraticMapLinear_apply, reflR_unit]

theorem seqReflection_native (x : Albert) :
    sequentialReflectionUpdate (nativeOutcomeUpdate pentadF) 2 x = quadraticMap reflR x :=
  sequentialReflectionUpdate_native pentadF 2 x

/-! ## Quadruple letters and costs -/

/-- Five-test index of each quadruple letter: `A,B,C,D ↦ 0,1,3,4`. -/
def quadLetter : Fin 4 → Fin 5 := ![0, 1, 3, 4]

/-- Reflected quadruple letters: `C` and `D`. -/
def quadRefl (x : Fin 4) : Bool := x == 2 || x == 3

/-- `(cost, cost of the Σ-conjugated effect)` of a quadruple word. -/
def quadCost : Word (Fin 4) → ℕ × ℕ
  | [] => (0, 0)
  | a :: w => if quadRefl a.1 then ((quadCost w).2 + 2, (quadCost w).2 + 1)
      else ((quadCost w).1 + 1, (quadCost w).1 + 2)

theorem reflQuad_outcome (x : Fin 4) (b : Bool) :
    nativeOutcome reflQuad (x, b) =
      if quadRefl x then quadraticMap reflR (nativeOutcome pentadF (quadLetter x, b))
      else nativeOutcome pentadF (quadLetter x, b) := by
  fin_cases x <;> cases b <;>
    simp [nativeOutcome, reflQuad, quadRefl, quadLetter, unit_sub_reflected]

/-! ## Model side -/

section Model

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- The quadruple projections `(P₀, P₁, ΣP₃Σ, ΣP₄Σ)`, `Σ = 2P₂ − 1`. -/
def quadProj (P : Fin 5 → A) (x : Fin 4) : A :=
  if quadRefl x then projectionReflection P 2 * P (quadLetter x) * projectionReflection P 2
  else P (quadLetter x)

variable (P : Fin 5 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
include hp hstar
set_option linter.unusedSectionVars false

theorem sig_sq : projectionReflection P 2 * projectionReflection P 2 = 1 :=
  projectionReflection_square P hp 2

theorem conj_conj (X : A) :
    projectionReflection P 2 * (projectionReflection P 2 * X * projectionReflection P 2) *
      projectionReflection P 2 = X := by
  have h := sig_sq P hp hstar
  calc _ = (projectionReflection P 2 * projectionReflection P 2) * X *
        (projectionReflection P 2 * projectionReflection P 2) := by simp only [mul_assoc]
    _ = X := by rw [h, one_mul, mul_one]

theorem quadProj_idem (x : Fin 4) : quadProj P x * quadProj P x = quadProj P x := by
  unfold quadProj
  split
  · have h := sig_sq P hp hstar
    calc _ = projectionReflection P 2 * P (quadLetter x) *
          (projectionReflection P 2 * projectionReflection P 2) * P (quadLetter x) *
          projectionReflection P 2 := by simp only [mul_assoc]
      _ = _ := by rw [h, mul_one]; simp only [mul_assoc]; rw [← mul_assoc (P _), hp]
  · exact hp _

theorem quadProj_star (x : Fin 4) : star (quadProj P x) = quadProj P x := by
  unfold quadProj
  split
  · rw [star_mul, star_mul, projectionReflection_star P hstar, hstar, mul_assoc]
  · exact hstar _

theorem quadProj_outcome (x : Fin 4) (b : Bool) :
    algebraicOutcome (quadProj P) (x, b) =
      if quadRefl x then
        projectionReflection P 2 * algebraicOutcome P (quadLetter x, b) * projectionReflection P 2
      else algebraicOutcome P (quadLetter x, b) := by
  unfold quadProj
  cases hx : quadRefl x <;> cases b <;> simp only [algebraicOutcome, hx, ↓reduceIte,
    Bool.false_eq_true]
  rw [mul_sub, sub_mul, mul_one, sig_sq P hp hstar]

/-- **Reflection transfer with cost.**  The model and native effects of a quadruple word
`u` lie in the span of five-test pairs of length `≤ (quadCost u).1`; their `Σ`-conjugates
in the span of length `≤ (quadCost u).2`. -/
theorem quad_lift (u : Word (Fin 4)) :
    (wordOperator (quadProj P) u, nativeWordEffect reflQuad u) ∈
        liftSpace P (nativeWordEffect pentadF) (quadCost u).1 ∧
      (projectionReflection P 2 * wordOperator (quadProj P) u * projectionReflection P 2,
        quadraticMap reflR (nativeWordEffect reflQuad u)) ∈
        liftSpace P (nativeWordEffect pentadF) (quadCost u).2 := by
  have hθ : ∀ (a : Outcome (Fin 5)) (w : Word (Fin 5)),
      nativeWordEffect pentadF (a :: w) = nativeOutcomeUpdate pentadF a (nativeWordEffect pentadF w) :=
    fun _ _ => rfl
  have hQ := quadProj_star P hp hstar
  induction u with
  | nil =>
      refine ⟨?_, ?_⟩
      · simpa [quadCost, nativeWordEffect] using
          liftSpace_word P (nativeWordEffect pentadF) (L := 0) [] le_rfl
      · have h0 := liftSpace_word P (nativeWordEffect pentadF) (L := 0) [] le_rfl
        simp only [wordOperator_nil, mul_one, sig_sq P hp hstar, nativeWordEffect,
          reflR_unit] at h0 ⊢
        simpa [quadCost, nativeWordEffect] using h0
  | cons a w ih =>
      obtain ⟨x, b⟩ := a
      have hcons : wordOperator (quadProj P) ((x, b) :: w) =
          algebraicOutcome (quadProj P) (x, b) * wordOperator (quadProj P) w *
            algebraicOutcome (quadProj P) (x, b) := wordOperator_cons (quadProj P) hQ (x, b) w
      have hnat : nativeWordEffect reflQuad ((x, b) :: w) =
          quadraticMap (nativeOutcome reflQuad (x, b)) (nativeWordEffect reflQuad w) := rfl
      rw [hcons, hnat, quadProj_outcome P hp hstar, reflQuad_outcome]
      cases hx : quadRefl x
      · -- unreflected letter
        simp only [quadCost, hx, Bool.false_eq_true, ↓reduceIte]
        have h1 := liftSpace_prefix P (nativeWordEffect pentadF) (nativeOutcomeUpdate pentadF)
          hstar hθ (quadLetter x, b) ih.1
        refine ⟨h1, ?_⟩
        have h2 := liftSpace_reflection P (nativeWordEffect pentadF) (nativeOutcomeUpdate pentadF)
          hstar hθ 2 h1
        rw [seqReflection_native] at h2
        exact h2
      · -- reflected letter
        simp only [quadCost, hx, ↓reduceIte]
        have h1 := liftSpace_prefix P (nativeWordEffect pentadF) (nativeOutcomeUpdate pentadF)
          hstar hθ (quadLetter x, b) ih.2
        have h2 := liftSpace_reflection P (nativeWordEffect pentadF) (nativeOutcomeUpdate pentadF)
          hstar hθ 2 h1
        rw [seqReflection_native] at h2
        have eA : projectionReflection P 2 * algebraicOutcome P (quadLetter x, b) *
              projectionReflection P 2 * wordOperator (quadProj P) w *
            (projectionReflection P 2 * algebraicOutcome P (quadLetter x, b) *
              projectionReflection P 2) =
            projectionReflection P 2 * (algebraicOutcome P (quadLetter x, b) *
              (projectionReflection P 2 * wordOperator (quadProj P) w *
                projectionReflection P 2) * algebraicOutcome P (quadLetter x, b)) *
              projectionReflection P 2 := by simp only [mul_assoc]
        have eN : quadraticMap (quadraticMap reflR (nativeOutcome pentadF (quadLetter x, b)))
              (nativeWordEffect reflQuad w) =
            quadraticMap reflR (nativeOutcomeUpdate pentadF (quadLetter x, b)
              (quadraticMap reflR (nativeWordEffect reflQuad w))) := by
          rw [quadraticMap_reflected]; rfl
        refine ⟨?_, ?_⟩
        · rw [eA, eN]
          exact h2
        · rw [eA, eN, conj_conj P hp hstar, reflR_involutive]
          exact h1

end Model

end AlbertSequential.FiveTest
