/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.JordanReflection
public import FiveTest.Transfer
public import GeneralEJAWordTransport
public import QuaternionicProjectiveData

/-! The explicit signed reflection transfer for a mixed menu. Switching between
unreflected and reflected lines marks a reflection location. The terminal
frame fixes the unit, so there is no reflection to insert after the last letter. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.FiveTest

variable {ι : Type*}

/-- The Boolean in the test label marks the reflected copy. The outcome Boolean
remains separate. -/
abbrev MarkedWord (ι : Type*) := Word (ι × Bool)

/-- Outcome corners and uncancelled reflection locations, in word order. -/
def reflectionSteps : Bool → MarkedWord ι → List (Option (Outcome ι))
  | _, [] => []
  | prev, ((i, mark), b) :: w =>
      (if prev = mark then [] else [none]) ++ some (i, b) :: reflectionSteps mark w

def reflectionSwitchCount : Bool → MarkedWord ι → ℕ
  | _, [] => 0
  | prev, ((_, mark), _) :: w => (if prev = mark then 0 else 1) + reflectionSwitchCount mark w

def reflectionRunsFrom : Bool → MarkedWord ι → ℕ
  | _, [] => 0
  | prev, ((_, mark), _) :: w => (if !prev && mark then 1 else 0) + reflectionRunsFrom mark w

def lastReflectionMark : Bool → MarkedWord ι → Bool
  | prev, [] => prev
  | _, ((_, mark), _) :: w => lastReflectionMark mark w

theorem reflectionSwitchCount_runs (prev : Bool) (w : MarkedWord ι) :
    reflectionSwitchCount prev w + (if lastReflectionMark prev w then 1 else 0) =
      2 * reflectionRunsFrom prev w + (if prev then 1 else 0) := by
  induction w generalizing prev with
  | nil => cases prev <;> rfl
  | cons a w ih =>
    rcases a with ⟨⟨i, mark⟩, b⟩
    have h := ih mark
    cases hlast : lastReflectionMark mark w <;> cases prev <;> cases mark <;>
      simp [reflectionSwitchCount, reflectionRunsFrom, lastReflectionMark, hlast] at h ⊢ <;> omega

/-- With the initial default unreflected, the transition count is the displayed
run formula (2\#\mathrm{runs}-[\mathrm{last\ reflected}]). -/
theorem reflectionSwitchCount_eq_nu (w : MarkedWord ι) :
    reflectionSwitchCount false w =
      2 * reflectionRunsFrom false w - (if lastReflectionMark false w then 1 else 0) := by
  have h := reflectionSwitchCount_runs false w
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h
  omega

theorem reflectionSteps_length (prev : Bool) (w : MarkedWord ι) :
    (reflectionSteps prev w).length = w.length + reflectionSwitchCount prev w := by
  induction w generalizing prev with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨⟨i, mark⟩, b⟩
    simp only [reflectionSteps, reflectionSwitchCount, List.length_append, List.length_cons, ih]
    split <;> simp_all <;> omega

theorem reflectionSteps_count (prev : Bool) (w : MarkedWord ι) :
    (reflectionSteps prev w).countP Option.isNone = reflectionSwitchCount prev w := by
  induction w generalizing prev with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨⟨i, mark⟩, b⟩
    simp only [reflectionSteps, reflectionSwitchCount, List.countP_append]
    split <;> simp [ih]

/-- A word of original tests obtained by choosing one of the three allowed
operations at every marked reflection location. -/
inductive ResolvesReflectionSteps (c : ι) : List (Option (Outcome ι)) → Word ι → Prop
  | nil : ResolvesReflectionSteps c [] []
  | retain (a : Outcome ι) {steps : List (Option (Outcome ι))} {w : Word ι}
      (h : ResolvesReflectionSteps c steps w) : ResolvesReflectionSteps c (some a :: steps) (a :: w)
  | skip {steps : List (Option (Outcome ι))} {w : Word ι}
      (h : ResolvesReflectionSteps c steps w) : ResolvesReflectionSteps c (none :: steps) w
  | insert (b : Bool) {steps : List (Option (Outcome ι))} {w : Word ι}
      (h : ResolvesReflectionSteps c steps w) : ResolvesReflectionSteps c (none :: steps) ((c, b) :: w)

theorem ResolvesReflectionSteps.length_le {c : ι} {steps : List (Option (Outcome ι))} {w : Word ι}
    (h : ResolvesReflectionSteps c steps w) : w.length ≤ steps.length := by
  induction h with
  | nil => simp
  | retain _ _ ih => simpa only [List.length_cons] using Nat.succ_le_succ ih
  | skip _ ih => exact Nat.le_succ_of_le ih
  | insert _ _ ih => simpa only [List.length_cons] using Nat.succ_le_succ ih

def prefixReflectionTerms (a : Outcome ι) (terms : List (ℤ × Word ι)) : List (ℤ × Word ι) :=
  terms.map fun t => (t.1, a :: t.2)

def scaleReflectionTerms (r : ℤ) (terms : List (ℤ × Word ι)) : List (ℤ × Word ι) :=
  terms.map fun t => (r * t.1, t.2)

/-- Identical integer coefficients and words for the native and model evaluators. -/
def signedReflectionExpansion (c : ι) : List (Option (Outcome ι)) → List (ℤ × Word ι)
  | [] => [(1, [])]
  | some a :: steps => prefixReflectionTerms a (signedReflectionExpansion c steps)
  | none :: steps =>
      let ts := signedReflectionExpansion c steps
      scaleReflectionTerms 2 (prefixReflectionTerms (c, true) ts) ++
        scaleReflectionTerms 2 (prefixReflectionTerms (c, false) ts) ++ scaleReflectionTerms (-1) ts

theorem signedReflectionExpansion_count (c : ι) (steps : List (Option (Outcome ι))) :
    (signedReflectionExpansion c steps).length = 3 ^ (steps.countP Option.isNone) := by
  induction steps with
  | nil => rfl
  | cons a steps ih =>
    cases a with
    | some a => simp [signedReflectionExpansion, prefixReflectionTerms, ih]
    | none =>
      simp [signedReflectionExpansion, prefixReflectionTerms, scaleReflectionTerms, ih, pow_succ]
      omega

theorem signedReflectionExpansion_resolves (c : ι) (steps : List (Option (Outcome ι)))
    (t : ℤ × Word ι) (ht : t ∈ signedReflectionExpansion c steps) :
    ResolvesReflectionSteps c steps t.2 := by
  induction steps generalizing t with
  | nil =>
    simp only [signedReflectionExpansion, List.mem_singleton] at ht
    subst t
    exact .nil
  | cons a steps ih =>
    cases a with
    | some a =>
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact .retain a (ih u hu)
    | none =>
      simp only [signedReflectionExpansion, scaleReflectionTerms, prefixReflectionTerms, List.mem_append] at ht
      rcases ht with (ht | ht) | ht
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact .insert true (ih u hu)
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact .insert false (ih u hu)
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
        exact .skip (ih u hu)

/-- Compute the common coefficient list for a word in the enlarged menu. -/
def signedReflectionTerms (c : ι) (w : MarkedWord ι) : List (ℤ × Word ι) :=
  signedReflectionExpansion c (reflectionSteps false w)

theorem signedReflectionTerms_count (c : ι) (w : MarkedWord ι) :
    (signedReflectionTerms c w).length = 3 ^ reflectionSwitchCount false w := by
  rw [signedReflectionTerms, signedReflectionExpansion_count, reflectionSteps_count]

theorem signedReflectionTerms_support (c : ι) (w : MarkedWord ι) (t : ℤ × Word ι)
    (ht : t ∈ signedReflectionTerms c w) :
    ResolvesReflectionSteps c (reflectionSteps false w) t.2 ∧
      t.2.length ≤ w.length + reflectionSwitchCount false w := by
  have h := signedReflectionExpansion_resolves c (reflectionSteps false w) t ht
  exact ⟨h, (reflectionSteps_length false w) ▸ h.length_le⟩

section Evaluation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Original signed word, evaluated by the indicated quadratic corners. -/
def evalCornerWord (U : Outcome ι → Module.End ℝ E) (e : E) (w : Word ι) : E :=
  w.foldr (fun a x => U a x) e

/-- Evaluate the marked word with the actual conjugated update at each marked letter. -/
def evalMarkedWord (U : Outcome ι → Module.End ℝ E) (R : Module.End ℝ E) (e : E)
    (w : MarkedWord ι) : E :=
  w.foldr (fun a x => if a.1.2 then R (U (a.1.1, a.2) (R x)) else U (a.1.1, a.2) x) e

def evalReflectionSteps (U : Outcome ι → Module.End ℝ E) (R : Module.End ℝ E) (e : E)
    (steps : List (Option (Outcome ι))) : E :=
  steps.foldr (fun o x => match o with | none => R x | some a => U a x) e

theorem evalReflectionSteps_eq_marked (U : Outcome ι → Module.End ℝ E) (R : Module.End ℝ E)
    (e : E) (he : R e = e) (hR : Function.Involutive R) (prev : Bool) (w : MarkedWord ι) :
    evalReflectionSteps U R e (reflectionSteps prev w) =
      if prev then R (evalMarkedWord U R e w) else evalMarkedWord U R e w := by
  induction w generalizing prev with
  | nil => cases prev <;> simp [reflectionSteps, evalReflectionSteps, evalMarkedWord, he]
  | cons a w ih =>
    rcases a with ⟨⟨i, mark⟩, b⟩
    cases prev <;> cases mark
    · change U (i, b) (evalReflectionSteps U R e (reflectionSteps false w)) =
        U (i, b) (evalMarkedWord U R e w)
      rw [ih false]
      rfl
    · change R (U (i, b) (evalReflectionSteps U R e (reflectionSteps true w))) =
        R (U (i, b) (R (evalMarkedWord U R e w)))
      rw [ih true]
      rfl
    · change R (U (i, b) (evalReflectionSteps U R e (reflectionSteps false w))) =
        R (U (i, b) (evalMarkedWord U R e w))
      rw [ih false]
      rfl
    · change U (i, b) (evalReflectionSteps U R e (reflectionSteps true w)) =
        R (R (U (i, b) (R (evalMarkedWord U R e w))))
      rw [hR, ih true]
      rfl

/-- Real-module sum with the literal integer coefficients of the expansion. -/
def evalSignedTerms (U : Outcome ι → Module.End ℝ E) (e : E)
    (terms : List (ℤ × Word ι)) : E :=
  (terms.map fun t => (t.1 : ℝ) • evalCornerWord U e t.2).sum

private theorem evalSignedTerms_append (U : Outcome ι → Module.End ℝ E) (e : E)
    (s t : List (ℤ × Word ι)) : evalSignedTerms U e (s ++ t) =
      evalSignedTerms U e s + evalSignedTerms U e t := by
  rw [evalSignedTerms, List.map_append, List.sum_append]
  rfl

private theorem evalSignedTerms_prefix (U : Outcome ι → Module.End ℝ E) (e : E)
    (a : Outcome ι) (ts : List (ℤ × Word ι)) :
    evalSignedTerms U e (prefixReflectionTerms a ts) = U a (evalSignedTerms U e ts) := by
  simp only [evalSignedTerms, prefixReflectionTerms, List.map_map, Function.comp_def, evalCornerWord,
    List.foldr_cons, map_list_sum, map_smul]

private theorem evalSignedTerms_scale (U : Outcome ι → Module.End ℝ E) (e : E)
    (r : ℤ) (ts : List (ℤ × Word ι)) :
    evalSignedTerms U e (scaleReflectionTerms r ts) = (r : ℝ) • evalSignedTerms U e ts := by
  induction ts with
  | nil => simp [evalSignedTerms, scaleReflectionTerms]
  | cons t ts ih =>
    simp only [scaleReflectionTerms, evalSignedTerms, List.map_cons, List.sum_cons, Int.cast_mul,
      mul_smul, smul_add] at ih ⊢
    rw [ih]

theorem evalSignedReflectionExpansion (U : Outcome ι → Module.End ℝ E) (e : E) (c : ι)
    (steps : List (Option (Outcome ι))) :
    evalSignedTerms U e (signedReflectionExpansion c steps) =
      evalReflectionSteps U (sequentialReflectionUpdate U c) e steps := by
  induction steps with
  | nil => simp [signedReflectionExpansion, evalSignedTerms, evalCornerWord, evalReflectionSteps]
  | cons a steps ih =>
    cases a with
    | some a =>
      rw [signedReflectionExpansion, evalSignedTerms_prefix, ih]
      rfl
    | none =>
      simp only [signedReflectionExpansion, evalSignedTerms_append, evalSignedTerms_scale,
        evalSignedTerms_prefix, ih, evalReflectionSteps, List.foldr_cons, sequentialReflectionUpdate,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, one_apply_eq_self]
      norm_num; module

/-- One constructive signed polynomial evaluates any model of the reflection law. -/
theorem evalSignedReflectionTerms (U : Outcome ι → Module.End ℝ E) (e : E) (c : ι)
    (he : sequentialReflectionUpdate U c e = e) (hR : Function.Involutive (sequentialReflectionUpdate U c))
    (w : MarkedWord ι) :
    evalSignedTerms U e (signedReflectionTerms c w) =
      evalMarkedWord U (sequentialReflectionUpdate U c) e w := by
  rw [signedReflectionTerms, evalSignedReflectionExpansion, evalReflectionSteps_eq_marked U _ e he hR]
  rfl

end Evaluation

section Jordan

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The original tests and copies reflected in the selected test. -/
def markedJordanMenu (P : UnitalJordanProduct E) (p : ι → E) (c : ι) (i : ι × Bool) : E :=
  if i.2 then P.idempotentReflection (p c) (p i.1) else p i.1

def jordanCornerUpdate (P : UnitalJordanProduct E) (p : ι → E) (a : Outcome ι) : Module.End ℝ E :=
  P.quadraticRepresentation (P.sequentialOutcome p a)

theorem evalCornerWord_jordan (P : UnitalJordanProduct E) (p : ι → E) (w : Word ι) :
    evalCornerWord (jordanCornerUpdate P p) P.unit w = P.sequentialWordEffect p w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change jordanCornerUpdate P p a (evalCornerWord (jordanCornerUpdate P p) P.unit w) =
      P.quadraticRepresentation (P.sequentialOutcome p a) (P.sequentialWordEffect p w)
    rw [ih]
    rfl

theorem markedJordanMenu_idempotent (P : UnitalJordanProduct E) (p : ι → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) (c : ι) (i : ι × Bool) :
    P.product (markedJordanMenu P p c i) (markedJordanMenu P p c i) = markedJordanMenu P p c i := by
  obtain ⟨i, b⟩ := i
  cases b
  · exact hp i
  · exact P.idempotentReflection_idempotent (p c) (hp c) (hp i)

/-- Lemma 4.1(c) on the actual Jordan effects, for every normalized choice
of original labels and arbitrary subsets encoded by marking the reflected copy. -/
theorem signedReflectionTransfer_jordan (P : UnitalJordanProduct E) (p : ι → E) (c : ι)
    (hc : P.product (p c) (p c) = p c) (w : MarkedWord ι) :
    P.sequentialWordEffect (markedJordanMenu P p c) w =
      ((signedReflectionTerms c w).map fun t => (t.1 : ℝ) • P.sequentialWordEffect p t.2).sum := by
  let U := jordanCornerUpdate P p
  let R := P.idempotentReflection (p c)
  have hR : sequentialReflectionUpdate U c = R := by
    ext x
    simp only [sequentialReflectionUpdate, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.add_apply, one_apply_eq_self, U, jordanCornerUpdate,
      UnitalJordanProduct.sequentialOutcome, Bool.false_eq_true, ↓reduceIte, R,
      P.idempotentReflection_apply]
  have hE : evalMarkedWord U R P.unit w = P.sequentialWordEffect (markedJordanMenu P p c) w := by
    induction w with
    | nil => rfl
    | cons a w ih =>
      obtain ⟨⟨i, mark⟩, b⟩ := a
      change (if mark then R (U (i, b) (R (evalMarkedWord U R P.unit w)))
        else U (i, b) (evalMarkedWord U R P.unit w)) = _
      rw [ih]
      cases mark <;> cases b <;>
        simp only [Bool.false_eq_true, ↓reduceIte, UnitalJordanProduct.sequentialWordEffect,
          U, jordanCornerUpdate, UnitalJordanProduct.sequentialOutcome, markedJordanMenu, R,
          ← P.idempotentReflection_complement (p c) hc, P.idempotentReflection_quadratic]
  have h := evalSignedReflectionTerms U P.unit c
    (by rw [hR]; exact P.idempotentReflection_unit _ hc)
    (by rw [hR]; exact P.idempotentReflection_involutive _ hc) w
  rw [hR, hE] at h
  simpa only [evalSignedTerms, U, evalCornerWord_jordan] using h.symm

end Jordan

section Operator

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- Literal conjugation as a real-linear map on all bounded operators. -/
def sandwichUpdate (P : A) : Module.End ℝ A where
  toFun x := P * x * P
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' r x := by rw [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

omit [StarRing A] [StarModule ℝ A] in
/-- The bounded-operator reflection identity on every input operator. -/
theorem reflection_sandwich_apply (P : ι → A) (c : ι) (X : A) :
    projectionReflection P c * X * projectionReflection P c =
      (2 : ℝ) • (P c * X * P c + (1 - P c) * X * (1 - P c)) - X := by
  simp only [projectionReflection, two_smul]
  noncomm_ring

/-- The original projections and the literally conjugated copies. -/
def markedProjectionMenu (P : ι → A) (c : ι) (k : ι × Bool) : A :=
  orbitProjection P (if k.2 then [c] else []) k.1

theorem markedProjectionMenu_apply (P : ι → A) (hstar : ∀ i, star (P i) = P i) (c : ι) (k : ι × Bool) :
    markedProjectionMenu P c k = if k.2 then
      projectionReflection P c * P k.1 * projectionReflection P c else P k.1 := by
  obtain ⟨i, b⟩ := k
  cases b <;> simp [markedProjectionMenu, orbitProjection,
    projectionReflectionWord, projectionReflection_star P hstar]

theorem markedProjectionMenu_star (P : ι → A) (hstar : ∀ i, star (P i) = P i) (c : ι) (k : ι × Bool) :
    star (markedProjectionMenu P c k) = markedProjectionMenu P c k :=
  orbitProjection_star P hstar _ _

theorem markedProjectionMenu_idempotent (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (c : ι) (k : ι × Bool) :
    markedProjectionMenu P c k * markedProjectionMenu P c k = markedProjectionMenu P c k :=
  orbitProjection_idempotent P hp hstar _ _

theorem markedProjectionMenu_outcome (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (c : ι) (a : Outcome (ι × Bool)) :
    algebraicOutcome (markedProjectionMenu P c) a = if a.1.2 then
      projectionReflection P c * algebraicOutcome P (a.1.1, a.2) * projectionReflection P c
      else algebraicOutcome P (a.1.1, a.2) := by
  obtain ⟨⟨i, b⟩, outcome⟩ := a
  cases b <;> cases outcome <;> simp only [algebraicOutcome, markedProjectionMenu_apply P hstar,
    Bool.false_eq_true, ↓reduceIte]
  rw [mul_sub, sub_mul, mul_one, projectionReflection_square P hp]

omit [StarModule ℝ A] in
theorem evalCornerWord_operator (P : ι → A) (hstar : ∀ i, star (P i) = P i) (w : Word ι) :
    evalCornerWord (fun a => sandwichUpdate (algebraicOutcome P a)) 1 w = wordOperator P w := by
  induction w with
  | nil => exact (wordOperator_nil P).symm
  | cons a w ih =>
    rw [wordOperator_cons P hstar]
    change algebraicOutcome P a * evalCornerWord (fun a => sandwichUpdate (algebraicOutcome P a)) 1 w *
      algebraicOutcome P a = _
    rw [ih]

/-- The same signed terms evaluate actual projective operators, including
real, complex and right-quaternionic operators through their algebraic adapters. -/
theorem signedReflectionTransfer_operator (P : ι → A) (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (c : ι) (w : MarkedWord ι) :
    wordOperator (markedProjectionMenu P c) w =
      ((signedReflectionTerms c w).map fun t => (t.1 : ℝ) • wordOperator P t.2).sum := by
  let U := fun a => sandwichUpdate (algebraicOutcome P a)
  let σ := projectionReflection P c
  let R := sandwichUpdate σ
  have hσ : σ * σ = 1 := projectionReflection_square P hp c
  have hR : sequentialReflectionUpdate U c = R := by
    ext X
    exact (reflection_sandwich_apply P c X).symm
  have he : R 1 = 1 := by change σ * 1 * σ = 1; rw [mul_one, hσ]
  have hinv : Function.Involutive R := by
    intro X
    change σ * (σ * X * σ) * σ = X
    calc
      _ = (σ * σ) * X * (σ * σ) := by simp only [mul_assoc]
      _ = X := by rw [hσ, one_mul, mul_one]
  have hE : evalMarkedWord U R 1 w = wordOperator (markedProjectionMenu P c) w := by
    induction w with
    | nil => exact (wordOperator_nil _).symm
    | cons a w ih =>
      rw [wordOperator_cons _ (markedProjectionMenu_star P hstar c), markedProjectionMenu_outcome P hp hstar]
      change (if a.1.2 then R (U (a.1.1, a.2) (R (evalMarkedWord U R 1 w)))
        else U (a.1.1, a.2) (evalMarkedWord U R 1 w)) = _
      rw [ih]
      cases a.1.2 <;> simp only [ Bool.false_eq_true, ↓reduceIte, U, sandwichUpdate, LinearMap.coe_mk,
        AddHom.coe_mk, R, σ, mul_assoc]
  have h := evalSignedReflectionTerms U (1 : A) c (hR.symm ▸ he) (hR.symm ▸ hinv) w
  rw [hR, hE] at h
  simpa only [evalSignedTerms, U, evalCornerWord_operator P hstar] using h.symm

/-- Transport the same normalized positive state to the enlarged family. -/
def markedProjectiveModel (M : AlgebraicProjectiveData ι A) (c : ι) :
    AlgebraicProjectiveData (ι × Bool) A where
  projection := markedProjectionMenu M.projection c
  idempotent := markedProjectionMenu_idempotent M.projection M.idempotent M.selfAdjoint c
  selfAdjoint := markedProjectionMenu_star M.projection M.selfAdjoint c
  state := M.state
  state_unit := M.state_unit
  state_star := M.state_star
  state_positive := M.state_positive

/-- Transfer a word whenever the original table matches its actual signed support. -/
theorem signedReflectionTransfer_probability {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) (p : ι → E) (c : ι) (hc : P.product (p c) (p c) = p c)
    (ω : E →ₗ[ℝ] ℝ) (M : AlgebraicProjectiveData ι A) (w : MarkedWord ι)
    (h : ∀ t ∈ signedReflectionTerms c w, M.probability t.2 = ω (P.sequentialWordEffect p t.2)) :
    (markedProjectiveModel M c).probability w = ω (P.sequentialWordEffect (markedJordanMenu P p c) w) := by
  change M.state (wordOperator (markedProjectionMenu M.projection c) w) = _
  rw [signedReflectionTransfer_operator M.projection M.idempotent M.selfAdjoint,
    signedReflectionTransfer_jordan P p c hc, map_list_sum, map_list_sum]
  apply congrArg List.sum
  simp only [List.map_map, Function.comp_def, map_smul]
  exact List.map_congr_left fun t ht => congrArg (fun x : ℝ => (t.1 : ℝ) • x) (h t ht)

end Operator

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Keep the actual Hilbert carrier and state while adjoining the reflected projections. -/
def markedHilbertProjectiveModel (M : HilbertProjectiveData ι 𝕜 H) (c : ι) :
    HilbertProjectiveData (ι × Bool) 𝕜 H where
  projection := markedProjectionMenu M.projection c
  isStarProjection i := ⟨markedProjectionMenu_idempotent M.projection
    (fun j => (M.isStarProjection j).isIdempotentElem) (fun j => (M.isStarProjection j).isSelfAdjoint) c i,
    markedProjectionMenu_star M.projection (fun j => (M.isStarProjection j).isSelfAdjoint) c i⟩
  state := M.state
  normalized := M.normalized
  positive := M.positive

/-- Reflection transfer with literal outcome probabilities on real or complex Hilbert space. -/
theorem signedReflectionTransfer_hilbert {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) (p : ι → E) (c : ι) (hc : P.product (p c) (p c) = p c)
    (ω : E →ₗ[ℝ] ℝ) (M : HilbertProjectiveData ι 𝕜 H) (w : MarkedWord ι)
    (h : ∀ t ∈ signedReflectionTerms c w, M.probability t.2 = ω (P.sequentialWordEffect p t.2)) :
    (markedHilbertProjectiveModel M c).probability w =
      ω (P.sequentialWordEffect (markedJordanMenu P p c) w) := by
  rw [← (markedHilbertProjectiveModel M c).toAlgebraic_probability]
  change (markedProjectiveModel M.toAlgebraic c).probability w = _
  refine signedReflectionTransfer_probability P p c hc ω M.toAlgebraic w fun t ht => ?_
  rw [M.toAlgebraic_probability]
  exact h t ht

end Hilbert

section Quaternionic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Q : QuaternionicOperatorStructure H}

/-- Keep the right-quaternionic structure and the original state. -/
def markedQuaternionicProjectiveModel (M : QuaternionicProjectiveData ι Q) (c : ι) :
    QuaternionicProjectiveData (ι × Bool) Q where
  projection := markedProjectionMenu M.projection c
  isStarProjection i := ⟨markedProjectionMenu_idempotent M.projection
    (fun j => (M.isStarProjection j).isIdempotentElem) (fun j => (M.isStarProjection j).isSelfAdjoint) c i,
    markedProjectionMenu_star M.projection (fun j => (M.isStarProjection j).isSelfAdjoint) c i⟩
  state := M.state
  normalized := M.normalized
  positive := M.positive

/-- Reflection transfer for the actual right-quaternionic model. -/
theorem signedReflectionTransfer_quaternionic {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) (p : ι → E) (c : ι) (hc : P.product (p c) (p c) = p c)
    (ω : E →ₗ[ℝ] ℝ) (M : QuaternionicProjectiveData ι Q) (w : MarkedWord ι)
    (h : ∀ t ∈ signedReflectionTerms c w,
      M.state (M.wordEffect t.2) = ω (P.sequentialWordEffect p t.2)) :
    (markedQuaternionicProjectiveModel M c).state ((markedQuaternionicProjectiveModel M c).wordEffect w) =
      ω (P.sequentialWordEffect (markedJordanMenu P p c) w) := by
  rw [← (markedQuaternionicProjectiveModel M c).toAlgebraic_probability]
  change (markedProjectiveModel M.toAlgebraic c).probability w = _
  refine signedReflectionTransfer_probability P p c hc ω M.toAlgebraic w fun t ht => ?_
  rw [M.toAlgebraic_probability]
  exact h t ht

end Quaternionic

end AlbertSequential.FiveTest
