/- SPDX-License-Identifier: Apache-2.0 -/
module

public import EqualityKernel
public import HorizonFive.Symbols
public import GeneralEJAWordTransport
import Mathlib.Tactic.Module

@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

/-- Evaluation of a unital Jordan term in an arbitrary real unital Jordan algebra. -/
def JTerm.evalJordan {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E) : JTerm n → E
  | .var i => p i
  | .one => P.unit
  | .add s t => evalJordan P p s + evalJordan P p t
  | .smul r s => r • evalJordan P p s
  | .mul s t => P.product (evalJordan P p s) (evalJordan P p t)

theorem evalJordan_native {n : ℕ} (p : Fin n → Albert) (T : JTerm n) :
    T.evalJordan HorizonFive.albertJordanProduct p = T.evalAlbert p := by
  induction T <;> simp_all [JTerm.evalJordan, JTerm.evalAlbert, HorizonFive.albertJordanProduct]

theorem evalJordan_wordJTerm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E) (w : Word (Fin n)) :
    (wordJTerm w).evalJordan P p = P.sequentialWordEffect p w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : (outcomeJTerm a).evalJordan P p = P.sequentialOutcome p a := by
      rcases a with ⟨i, b⟩
      cases b <;> simp [outcomeJTerm, JTerm.evalJordan, UnitalJordanProduct.sequentialOutcome,
        sub_eq_add_neg]
    rw [wordJTerm, UnitalJordanProduct.sequentialWordEffect]
    simp only [quadJTerm, JTerm.evalJordan, ha, ih, neg_one_smul,
      UnitalJordanProduct.quadraticRepresentation_apply, sub_eq_add_neg]

private theorem evalJordan_wordListJTerm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E) (L : List (ℝ × Word (Fin n))) :
    (wordListJTerm L).evalJordan P p =
      (L.map fun x => x.1 • P.sequentialWordEffect p x.2).sum := by
  induction L with
  | nil => simp [wordListJTerm, JTerm.evalJordan]
  | cons c L ih =>
    rcases c with ⟨a,w⟩
    simp [wordListJTerm, JTerm.evalJordan, evalJordan_wordJTerm, ih]

theorem evalJordan_wordCombination {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E) (c : Word (Fin n) →₀ ℝ) :
    (wordCombinationJTerm c).evalJordan P p = c.sum (fun w a => a • P.sequentialWordEffect p w) := by
  rw [wordCombinationJTerm, evalJordan_wordListJTerm, List.map_map, Finsupp.sum]
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

def specialProduct (A : Type) [Ring A] [Algebra ℝ A] : UnitalJordanProduct A where
  product := LinearMap.mk₂ ℝ (fun x y => (1 / 2 : ℝ) • (x * y + y * x))
    (by intros; simp only [add_mul, mul_add, smul_add]; abel)
    (by intros; simp only [smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]; module)
    (by intros; simp only [add_mul, mul_add, smul_add]; abel)
    (by intros; simp only [smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]; module)
  unit := 1
  commutative x y := by
    change (1 / 2 : ℝ) • (x * y + y * x) = (1 / 2 : ℝ) • (y * x + x * y)
    rw [add_comm]
  unit_left x := by change (1 / 2 : ℝ) • (1 * x + x * 1) = x; rw [one_mul, mul_one]; module
  jordan_identity x y := by
    simp only [LinearMap.mk₂_apply, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_add,
      smul_smul, mul_assoc]
    abel

private theorem evalJordan_special {A : Type} [Ring A] [Algebra ℝ A]
    {n : ℕ} (p : Fin n → A) (T : JTerm n) :
    T.evalJordan (specialProduct A) p = T.evalS p := by
  induction T <;> simp_all [JTerm.evalJordan, JTerm.evalS, specialProduct]

private theorem specialProduct_apply_self {A : Type} [Ring A] [Algebra ℝ A] (x : A) :
    (specialProduct A).product x x = x * x := by
  change (1 / 2 : ℝ) • (x * x + x * x) = x * x
  module

/-- Semantic congruence for the free unital real Jordan algebra with idempotent generators. -/
def idempotentJordanSetoid (n : ℕ) : Setoid (JTerm n) where
  r s t := ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E) (p : Fin n → E),
    (∀ i, P.product (p i) (p i) = p i) → s.evalJordan P p = t.evalJordan P p
  iseqv := ⟨fun _ _ _ _ _ _ _ => rfl,
    fun h E _ _ P p hp => (h E P p hp).symm,
    fun h₁ h₂ E _ _ P p hp => (h₁ E P p hp).trans (h₂ E P p hp)⟩

/-- The free idempotent Jordan algebra as term equivalence classes, evaluated in arbitrary
unital real Jordan algebras in the model universe. -/
def FreeIdempotentJordan (n : ℕ) := Quotient (idempotentJordanSetoid n)

def freeJordanOfTerm {n : ℕ} (T : JTerm n) : FreeIdempotentJordan n :=
  Quotient.mk _ T

def freeJordanZero (n : ℕ) : FreeIdempotentJordan n :=
  freeJordanOfTerm (.smul 0 .one)

def freeJordanUnit (n : ℕ) : FreeIdempotentJordan n :=
  freeJordanOfTerm .one

def freeJordanGenerator {n : ℕ} (i : Fin n) : FreeIdempotentJordan n :=
  freeJordanOfTerm (.var i)

def freeJordanAdd {n : ℕ} : FreeIdempotentJordan n → FreeIdempotentJordan n → FreeIdempotentJordan n :=
  Quotient.map₂ JTerm.add (fun _ _ h₁ _ _ h₂ E _ _ P p hp => by
    simp only [JTerm.evalJordan, h₁ E P p hp, h₂ E P p hp])

def freeJordanSmul {n : ℕ} (r : ℝ) : FreeIdempotentJordan n → FreeIdempotentJordan n :=
  Quotient.map (JTerm.smul r) (fun _ _ h E _ _ P p hp => by simp only [JTerm.evalJordan, h E P p hp])

def freeJordanProduct {n : ℕ} : FreeIdempotentJordan n → FreeIdempotentJordan n → FreeIdempotentJordan n :=
  Quotient.map₂ JTerm.mul (fun _ _ h₁ _ _ h₂ E _ _ P p hp => by
    simp only [JTerm.evalJordan, h₁ E P p hp, h₂ E P p hp])

theorem freeJordanGenerator_idempotent {n : ℕ} (i : Fin n) :
    freeJordanProduct (freeJordanGenerator i) (freeJordanGenerator i) = freeJordanGenerator i :=
  Quotient.sound (fun _ _ _ _ _ hp => hp i)

def freeJordanEvaluation {E : Type} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) : FreeIdempotentJordan n → E :=
  Quotient.lift (JTerm.evalJordan P p) (fun _ _ h => h E P p hp)

theorem freeJordanEvaluation_preserves_operations {E : Type} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) :
    let f := freeJordanEvaluation P p hp
    f (freeJordanUnit n) = P.unit ∧ (∀ i, f (freeJordanGenerator i) = p i) ∧
    (∀ x y, f (freeJordanAdd x y) = f x + f y) ∧
    (∀ r x, f (freeJordanSmul r x) = r • f x) ∧
    (∀ x y, f (freeJordanProduct x y) = P.product (f x) (f y)) := by
  refine ⟨rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro x y
    exact Quotient.inductionOn₂ x y (fun _ _ => rfl)
  · intro r x
    exact Quotient.inductionOn x (fun _ => rfl)
  · intro x y
    exact Quotient.inductionOn₂ x y (fun _ _ => rfl)

/-- Terms generated by the unit and the designated idempotents exhaust the quotient. -/
theorem freeJordanEvaluation_unique {E : Type} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) (f : FreeIdempotentJordan n → E)
    (hu : f (freeJordanUnit n) = P.unit) (hv : ∀ i, f (freeJordanGenerator i) = p i)
    (ha : ∀ x y, f (freeJordanAdd x y) = f x + f y)
    (hs : ∀ r x, f (freeJordanSmul r x) = r • f x)
    (hm : ∀ x y, f (freeJordanProduct x y) = P.product (f x) (f y)) :
    f = freeJordanEvaluation P p hp := by
  funext x
  refine Quotient.inductionOn x ?_
  intro T
  change f (freeJordanOfTerm T) = T.evalJordan P p
  induction T with
  | var i => exact hv i
  | one => exact hu
  | add s t h₁ h₂ =>
    change f (freeJordanAdd (freeJordanOfTerm s) (freeJordanOfTerm t)) = _
    rw [ha, h₁, h₂]
    rfl
  | smul r t ht =>
    change f (freeJordanSmul r (freeJordanOfTerm t)) = _
    rw [hs, ht]
    rfl
  | mul s t h₁ h₂ =>
    change f (freeJordanProduct (freeJordanOfTerm s) (freeJordanOfTerm t)) = _
    rw [hm, h₁, h₂]
    rfl

def freeJordanToGroup {n : ℕ} : FreeIdempotentJordan n → GroupAlgebra n :=
  freeJordanEvaluation (specialProduct (GroupAlgebra n)) (groupProj n)
    (by intro i; rw [specialProduct_apply_self, groupProj_mul_self])

def freeJordanToNative {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) : FreeIdempotentJordan n → Albert :=
  freeJordanEvaluation HorizonFive.albertJordanProduct p hp

theorem freeJordanToGroup_ofTerm {n : ℕ} (T : JTerm n) :
    freeJordanToGroup (freeJordanOfTerm T) = idempotentJordanGroupValue T :=
  evalJordan_special (groupProj n) T

theorem freeJordanToNative_ofTerm {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (T : JTerm n) :
    freeJordanToNative p hp (freeJordanOfTerm T) = T.evalAlbert p :=
  evalJordan_native p T

def freeWordCombination {n : ℕ} (c : Word (Fin n) →₀ ℝ) : FreeIdempotentJordan n :=
  freeJordanOfTerm (wordCombinationJTerm c)

/-- The elements of Vₙ are precisely the finite real linear combinations of word terms. -/
def freeJordanWordSpan (n : ℕ) : Set (FreeIdempotentJordan n) :=
  Set.range freeWordCombination

/-- The first claim of 6.17(b) for actual idempotent Jordan relations. -/
theorem freeWordCombination_zero {n : ℕ} (c : Word (Fin n) →₀ ℝ)
    (h : freeWordCombination c = freeJordanZero n) :
    IsProjectiveEquality c ∧
    ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E) (p : Fin n → E),
      (∀ i, P.product (p i) (p i) = p i) → (wordCombinationJTerm c).evalJordan P p = 0 := by
  have hvan : ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E) (p : Fin n → E),
      (∀ i, P.product (p i) (p i) = p i) → (wordCombinationJTerm c).evalJordan P p = 0 := by
    intro E _ _ P p hp
    exact (congrArg (freeJordanEvaluation P p hp) h).trans (zero_smul ℝ P.unit)
  refine ⟨(isProjectiveEquality_iff_freeProductZero c).mpr ?_, hvan⟩
  rw [← idempotentJordanGroupValue_wordCombination, ← freeJordanToGroup_ofTerm,
    ← show freeWordCombination c = freeJordanOfTerm (wordCombinationJTerm c) from rfl, h]
  rw [freeJordanZero, freeJordanToGroup_ofTerm]
  exact zero_smul ℝ _

/-- A free-zero combination vanishes in every Jordan word table from every linear state. -/
theorem freeWordCombination_zero_readout {E : Type} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) (φ : E →ₗ[ℝ] ℝ)
    (c : Word (Fin n) →₀ ℝ) (h : freeWordCombination c = freeJordanZero n) :
    c.sum (fun w a => a * φ (P.sequentialWordEffect p w)) = 0 := by
  have hval := congrArg φ ((freeWordCombination_zero c h).2 E P p hp)
  rw [evalJordan_wordCombination, Finsupp.sum, map_sum, map_zero] at hval
  simpa only [Finsupp.sum, map_smul, smul_eq_mul] using hval

/-- Proposition 6.17(c), first assertion, on the semantic free-algebra quotient. -/
theorem projectiveViolation_iff_freeWordSpanKernel {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) :
    (∃ (c : Word (Fin n) →₀ ℝ) (ρ : Albert), IsProjectiveEquality c ∧ IsDensity ρ ∧
      c.sum (fun w a => a * nativeWordProbability p ρ w) ≠ 0) ↔
    ∃ T ∈ freeJordanWordSpan n, freeJordanToGroup T = 0 ∧ freeJordanToNative p hp T ≠ 0 := by
  constructor
  · rintro ⟨c, ρ, hc, hd, hn⟩
    refine ⟨freeWordCombination c, ⟨c, rfl⟩, ?_⟩
    rw [freeWordCombination, freeJordanToGroup_ofTerm, freeJordanToNative_ofTerm]
    exact (wordCombination_projectiveViolation_iff p c).mp ⟨hc, ρ, hd, hn⟩
  · rintro ⟨T, ⟨c, rfl⟩, hG, hN⟩
    rw [freeWordCombination, freeJordanToGroup_ofTerm] at hG
    rw [freeWordCombination, freeJordanToNative_ofTerm] at hN
    obtain ⟨hc, ρ, hd, hn⟩ := (wordCombination_projectiveViolation_iff p c).mpr ⟨hG, hN⟩
    exact ⟨c, ρ, hc, hd, hn⟩

theorem exists_freeJordanKernel_of_generates {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (hg : GeneratesAlbert p) :
    ∃ T : FreeIdempotentJordan n, freeJordanToGroup T = 0 ∧ freeJordanToNative p hp T ≠ 0 := by
  obtain ⟨T, hG, hN⟩ := exists_idempotentJordanKernel_of_generates p hg
  exact ⟨freeJordanOfTerm T, (freeJordanToGroup_ofTerm T).trans hG,
    (freeJordanToNative_ofTerm p hp T).trans_ne hN⟩

theorem exists_projectiveViolation_of_freeWordSpan_eq_univ {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, jordanMul (p i) (p i) = p i) (hg : GeneratesAlbert p)
    (hspan : freeJordanWordSpan n = Set.univ) :
    ∃ (c : Word (Fin n) →₀ ℝ) (ρ : Albert), IsProjectiveEquality c ∧ IsDensity ρ ∧
      c.sum (fun w a => a * nativeWordProbability p ρ w) ≠ 0 := by
  obtain ⟨T, hG, hN⟩ := exists_freeJordanKernel_of_generates p hp hg
  exact (projectiveViolation_iff_freeWordSpanKernel p hp).mpr ⟨T, hspan ▸ Set.mem_univ T, hG, hN⟩

end AlbertSequential.AppF
