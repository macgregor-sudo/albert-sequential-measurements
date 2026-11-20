/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.AlgebraicWalkSpace
public import Mathlib.Algebra.MvPolynomial.Eval

/-! A checked exhaustive reduction for the four-letter walks of core Lemma 6.6.
A candidate records its original word, two possible descendants and the exact
scalar identity justifying the substitution. -/

set_option autoImplicit false
@[expose] public section

namespace AlbertSequential.LengthSeven

/-- Six overlaps, four unordered triple values, and the three middle-letter values. -/
noncomputable def walkTraceCoordinates (τ : TraceData) : Fin 13 → ℝ :=
  ![τ.o 0 1, τ.o 0 2, τ.o 0 3, τ.o 1 2, τ.o 1 3, τ.o 2 3,
    τ.R 0 1 2, τ.R 0 1 3, τ.R 0 2 3, τ.R 1 2 3, τ.om 1, τ.om 2, τ.om 3]

def overlapCoordinate (i j : Letter) : Fin 13 :=
  if i = 0 ∨ j = 0 then
    if i = 1 ∨ j = 1 then 0 else if i = 2 ∨ j = 2 then 1 else 2
  else if i = 1 ∨ j = 1 then if i = 2 ∨ j = 2 then 3 else 4
  else 5

def triangleCoordinate (i j k : Letter) : Fin 13 :=
  if i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 then 9
  else if i ≠ 3 ∧ j ≠ 3 ∧ k ≠ 3 then 6
  else if i ≠ 2 ∧ j ≠ 2 ∧ k ≠ 2 then 7
  else 8

def middleCoordinate (i : Letter) : Fin 13 :=
  if i = 1 then 10 else if i = 2 then 11 else 12

theorem walkTraceCoordinates_overlap (τ : TraceData) (i j : Letter) (h : i ≠ j) :
    walkTraceCoordinates τ (overlapCoordinate i j) = τ.o i j := by
  fin_cases i <;> fin_cases j <;>
    first | exact (h rfl).elim | rfl | exact τ.o_symm _ _

theorem walkTraceCoordinates_triangle (τ : TraceData) (i j k : Letter)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    walkTraceCoordinates τ (triangleCoordinate i j k) = τ.R i j k := by
  have h₃ (a b c : Letter) : τ.R a b c = τ.R b c a :=
    (τ.R_symm12 a b c).trans (τ.R_symm23 b a c)
  have h₄ (a b c : Letter) : τ.R a b c = τ.R c a b := (h₃ c a b).symm
  have h₅ (a b c : Letter) : τ.R a b c = τ.R c b a :=
    (τ.R_symm12 a b c).trans (h₄ b a c)
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact (hij rfl).elim | exact (hjk rfl).elim | exact (hik rfl).elim |
      rfl | exact τ.R_symm12 _ _ _ | exact τ.R_symm23 _ _ _ |
      exact h₃ _ _ _ | exact h₄ _ _ _ | exact h₅ _ _ _

theorem walkTraceCoordinates_middle (τ : TraceData) (i : Letter) (hi : i ≠ 0) :
    walkTraceCoordinates τ (middleCoordinate i) = τ.om i := by
  fin_cases i <;> first | exact (hi rfl).elim | rfl

/-- Reified integer polynomial, evaluated only after certificate construction. -/
inductive WalkPolynomial where
  | integer (z : ℤ)
  | input (i : Fin 13)
  | mul (a b : WalkPolynomial)
  | sub (a b : WalkPolynomial)

namespace WalkPolynomial

noncomputable def eval (values : Fin 13 → ℝ) : WalkPolynomial → ℝ
  | .integer z => z
  | .input i => values i
  | .mul a b => eval values a * eval values b
  | .sub a b => eval values a - eval values b

noncomputable def toMvPolynomial : WalkPolynomial → MvPolynomial (Fin 13) ℤ
  | .integer z => MvPolynomial.C z
  | .input i => MvPolynomial.X i
  | .mul a b => toMvPolynomial a * toMvPolynomial b
  | .sub a b => toMvPolynomial a - toMvPolynomial b

theorem eval_toMvPolynomial (values : Fin 13 → ℝ) (p : WalkPolynomial) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) values p.toMvPolynomial = p.eval values := by
  induction p with
  | integer z => rw [toMvPolynomial, MvPolynomial.eval₂_C]; rfl
  | input i => rw [toMvPolynomial, MvPolynomial.eval₂_X]; rfl
  | mul a b ia ib => rw [toMvPolynomial, MvPolynomial.eval₂_mul, ia, ib]; rfl
  | sub a b ia ib =>
    rw [toMvPolynomial]
    exact (map_sub (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) values) _ _).trans
      (congrArg₂ (fun x y : ℝ => x - y) ia ib)

def overlap (i j : Letter) : WalkPolynomial := .input (overlapCoordinate i j)
def triangle (i j k : Letter) : WalkPolynomial := .input (triangleCoordinate i j k)
def middle (i : Letter) : WalkPolynomial := .input (middleCoordinate i)

end WalkPolynomial

/-- A single checked reduction step with at most two descendant words. -/
inductive WalkReductionStep where
  | value (p : WalkPolynomial)
  | scaled (p : WalkPolynomial) (u : List Letter)
  | exchanged (p : WalkPolynomial) (u v : List Letter)

noncomputable def WalkReductionStep.eval (τ : TraceData) (L : List Letter → ℝ) : WalkReductionStep → ℝ
  | .value p => p.eval (walkTraceCoordinates τ)
  | .scaled p u => p.eval (walkTraceCoordinates τ) * L u
  | .exchanged p u v => 2 * p.eval (walkTraceCoordinates τ) * L u - L v

structure WalkCandidate (w : List Letter) where
  step : WalkReductionStep
  sound : ∀ (τ : TraceData) (L : List Letter → ℝ),
    AlgebraicWalkRules τ L → L w = step.eval τ L

namespace WalkCandidate

/-- Transport the source side of a reduction along a walk identity. -/
def view {u w : List Letter} (c : WalkCandidate u)
    (hL : ∀ (τ : TraceData) (L : List Letter → ℝ), AlgebraicWalkRules τ L → L w = L u) :
    WalkCandidate w where
  step := c.step
  sound τ L h := (hL τ L h).trans (c.sound τ L h)

end WalkCandidate

open WalkPolynomial

def walkEndCandidates : (w : List Letter) → List (WalkCandidate w)
  | [] => [⟨.value (.integer 1), fun _ _ h => by simpa [WalkReductionStep.eval, eval] using h.empty⟩]
  | i :: w =>
    if hi : i = 0 then
      [⟨.scaled (.integer 1) w, fun _ L h => by
        subst i
        simpa [WalkReductionStep.eval, eval] using h.dropLeftA w⟩]
    else
      match w with
      | [] => [⟨.value (overlap 0 i), fun τ L h => by
          simpa [WalkReductionStep.eval, eval, overlap, walkTraceCoordinates_overlap τ 0 i (Ne.symm hi)] using
            h.singleton i hi⟩]
      | j :: v => if hj : j = 0 then
          [⟨.scaled (overlap 0 i) v, fun τ L h => by
            subst j
            simpa [WalkReductionStep.eval, eval, overlap, walkTraceCoordinates_overlap τ 0 i (Ne.symm hi)] using
              h.secondA i hi v⟩]
        else []

def walkValueCandidates : (w : List Letter) → List (WalkCandidate w)
  | [i, j] =>
    if h : i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j then [⟨.value (triangle 0 i j), fun τ L hW => by
      simpa [WalkReductionStep.eval, eval, triangle, walkTraceCoordinates_triangle τ 0 i j (Ne.symm h.1) h.2.2 (Ne.symm h.2.1)]
        using hW.pair i j h.1 h.2.1 h.2.2⟩] else []
  | [i, j, k] =>
    if h : IsOrderingBCD i j k then [⟨.value (middle j), fun τ L hW => by
      have hh := hW.r3Base i j k h
      have hre : L [k, j, i] = L [i, j, k] := hW.reverse [i, j, k]
      rw [hre] at hh
      change L [i, j, k] = walkTraceCoordinates τ (middleCoordinate j)
      rw [walkTraceCoordinates_middle τ j h.2.1]
      linarith only [hh]⟩] else []
  | [i, j, a, k, j', i'] =>
    if h : IsOrderingBCD i j k ∧ a = 0 ∧ j' = j ∧ i' = i then
      [⟨.value (.mul (.mul (overlap 0 i) (overlap i j)) (triangle 0 j k)), fun τ L hW => by
        obtain ⟨hijk, ha, hj', hi'⟩ := h
        subst a j' i'
        rcases hijk with ⟨hi, hj, hk, hij, hjk, hik⟩
        simpa [WalkReductionStep.eval, eval, overlap, triangle, walkTraceCoordinates_overlap τ 0 i (Ne.symm hi),
          walkTraceCoordinates_overlap τ i j hij, walkTraceCoordinates_triangle τ 0 j k (Ne.symm hj) hjk (Ne.symm hk)]
          using hW.six i j k ⟨hi, hj, hk, hij, hjk, hik⟩⟩] else []
  | _ => []

def walkLocalMerge (u : List Letter) : (v : List Letter) → List (WalkCandidate (u ++ v))
  | i :: j :: v => if h : i = j then [⟨.scaled (.integer 1) (u ++ i :: v), fun _ L h => by
      subst j
      simpa [WalkReductionStep.eval, eval] using h.merge u i v⟩] else []
  | _ => []

def walkLocalR1 (u : List Letter) : (v : List Letter) → List (WalkCandidate (u ++ v))
  | i :: j :: k :: v =>
    if h : i = k ∧ i ≠ j ∧ v.length ≤ 2 then
      [⟨.scaled (overlap i j) (u ++ i :: v), fun τ L hW => by
        obtain ⟨hik, hij, hv⟩ := h
        subst k
        simpa [WalkReductionStep.eval, eval, overlap, walkTraceCoordinates_overlap τ i j hij, List.append_assoc]
          using hW.r1 u v i j hij hv⟩] else []
  | _ => []

def walkLocalR2 (u : List Letter) : (v : List Letter) → List (WalkCandidate (u ++ v))
  | i :: j :: k :: l :: v =>
    if h : i = l ∧ i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ v.length ≤ 1 then
      let longer := u ++ i :: k :: j :: l :: v
      let shorter := u ++ i :: v
      if hre : longer = (u ++ i :: j :: k :: l :: v).reverse then
        [⟨.scaled (triangle i j k) shorter, fun τ L hW => by
          obtain ⟨hil, hij, hjk, hik, hv⟩ := h
          subst l
          have hh := hW.r2 u v i j k hij hjk hik hv
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hh
          change L (u ++ i :: j :: k :: i :: v) + L longer = 2 * τ.R i j k * L shorter at hh
          rw [hre, hW.reverse] at hh
          simpa [WalkReductionStep.eval, eval, triangle, walkTraceCoordinates_triangle τ i j k hij hjk hik]
            using (show L (u ++ i :: j :: k :: i :: v) = τ.R i j k * L shorter by linarith only [hh])⟩]
      else
        [⟨.exchanged (triangle i j k) shorter longer, fun τ L hW => by
          obtain ⟨hil, hij, hjk, hik, hv⟩ := h
          subst l
          have hh := hW.r2 u v i j k hij hjk hik hv
          simpa [WalkReductionStep.eval, eval, triangle, walkTraceCoordinates_triangle τ i j k hij hjk hik,
            shorter, longer, List.append_assoc] using eq_sub_of_add_eq hh⟩]
    else []
  | _ => []

def walkLocalR3 (u : List Letter) : (v : List Letter) → List (WalkCandidate (u ++ v))
  | [a, i, j, k] =>
    if h : a = 0 ∧ IsOrderingBCD i j k then
      [⟨.exchanged (middle j) u (u ++ [a, k, j, i]), fun τ L hW => by
        obtain ⟨rfl, hijk⟩ := h
        have hh := hW.r3AfterA u i j k hijk
        rw [hW.dropRightA] at hh
        simpa [WalkReductionStep.eval, eval, middle, walkTraceCoordinates_middle τ j hijk.2.1]
          using eq_sub_of_add_eq hh⟩] else []
  | _ => []

/-- Check one orientation and offset. When using a padded word, skip steps
whose only effect is undoing the harmless padding. -/
def walkContextCandidates (padded : Bool) (u : List Letter) :
    (v : List Letter) → List (WalkCandidate (u ++ v))
  | [] => []
  | i :: v =>
    (if padded then [] else walkLocalMerge u (i :: v)) ++ walkLocalR1 u (i :: v) ++
      walkLocalR2 u (i :: v) ++ (if padded then [] else walkLocalR3 u (i :: v)) ++
      (walkContextCandidates padded (u ++ [i]) v).map (fun c => c.view fun _ _ _ => by
        rw [List.append_assoc]; rfl)

def walkOrientedCandidates (w : List Letter) : List (WalkCandidate w) :=
  walkEndCandidates w ++ walkValueCandidates w ++ (show List (WalkCandidate w) from walkContextCandidates false [] w) ++
    if w.getLast? = some 0 then []
    else (walkContextCandidates true [] (w ++ [0])).map (fun c => c.view fun _ _ h => (h.dropRightA w).symm)

def walkCandidates (w : List Letter) : List (WalkCandidate w) :=
  walkOrientedCandidates w ++ (walkOrientedCandidates w.reverse).map
    (fun c => c.view fun _ _ h => (h.reverse w).symm)

/-- Bounded deterministic certificate search. Only the discrete structure of
words enters the search, never the actual values of the thirteen traces. -/
def reduceWalk (fuel : ℕ) (w : List Letter) : Option WalkPolynomial :=
  match fuel with
  | 0 => none
  | n + 1 => (walkCandidates w).findSome? fun c =>
    match c.step with
    | .value p => some p
    | .scaled p u => (reduceWalk n u).map (.mul p)
    | .exchanged p u v => do
        let q ← reduceWalk n u
        let r ← reduceWalk n v
        return .sub (.mul (.mul (.integer 2) p) q) r

theorem reduceWalk_sound (τ : TraceData) (L : List Letter → ℝ) (h : AlgebraicWalkRules τ L)
    (fuel : ℕ) (w : List Letter) (p : WalkPolynomial) (hp : reduceWalk fuel w = some p) :
    L w = p.eval (walkTraceCoordinates τ) := by
  induction fuel generalizing w p with
  | zero => simp [reduceWalk] at hp
  | succ fuel ih =>
    simp only [reduceWalk] at hp
    obtain ⟨_, c, _, _, hc, _⟩ := List.findSome?_eq_some_iff.mp hp
    have hs := c.sound τ L h
    cases hstep : c.step with
    | value q =>
      simp only [hstep, Option.some.injEq] at hc
      subst q
      simpa only [hstep, WalkReductionStep.eval] using hs
    | scaled q u =>
      cases hu : reduceWalk fuel u with
      | none => simp [hstep, hu] at hc
      | some r =>
        simp [hstep, hu] at hc
        subst p
        simpa [hstep, WalkReductionStep.eval, WalkPolynomial.eval, ih u r hu] using hs
    | exchanged q u v =>
      cases hu : reduceWalk fuel u <;> cases hv : reduceWalk fuel v <;> simp [hstep, hu, hv] at hc
      subst p
      simpa [hstep, WalkReductionStep.eval, WalkPolynomial.eval, ih _ _ hu, ih _ _ hv] using hs

end AlbertSequential.LengthSeven
