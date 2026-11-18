/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SupportedPurityLeaves
public import Mathlib.Tactic.NoncommRing

/-! Actual signed skip/yes/no words for the primitive R1--R3 expansions.
Scalar access identities are visible hypotheses. No native purity, relation
ledger, measured-word count or universal telescope is inferred here. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def signedAccessChoices : List (ℝ × Option Bool) :=
  [(1, none), (1, some true), (-1, some false)]

def accessPrefix {ι : Type*} (i : ι) (choice : Option Bool) (w : Word ι) : Word ι :=
  match choice with
  | none => w
  | some b => (i, b) :: w

def accessWordTerms {ι : Type*} (i : ι) (w : Word ι) : List (ℝ × Word ι) :=
  signedAccessChoices.map (fun t => (t.1, accessPrefix i t.2 w))

def scaleWordTerms {ι : Type*} (r : ℝ) (ts : List (ℝ × Word ι)) : List (ℝ × Word ι) :=
  ts.map (fun t => (r * t.1, t.2))

def accessLiftWordTerms {ι : Type*} (i : ι) (ts : List (ℝ × Word ι)) : List (ℝ × Word ι) :=
  ts.flatMap (fun t => scaleWordTerms t.1 (accessWordTerms i t.2))

def doubleAccessWordTerms {ι : Type*} (k l m : ι) : List (ℝ × Word ι) :=
  accessLiftWordTerms k (accessWordTerms l [(m, true)])

def polarizedTripleWordTerms {ι : Type*} (k l m : ι) : List (ℝ × Word ι) :=
  doubleAccessWordTerms k l m ++ doubleAccessWordTerms m k l ++
    scaleWordTerms (-1) (doubleAccessWordTerms l k m)

def weightedWordOperator {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (P : ι → A) (ts : List (ℝ × Word ι)) : A :=
  (ts.map (fun t => t.1 • wordOperator P t.2)).sum

def weightedWordScalar {ι : Type*} (c : Word ι → ℝ) (ts : List (ℝ × Word ι)) : ℝ :=
  (ts.map (fun t => t.1 * c t.2)).sum

def weightedPurityResidual {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (P : ι → A) (a : ι) (c : Word ι → ℝ) (ts : List (ℝ × Word ι)) : A :=
  (ts.map (fun t => t.1 • outcomePurityElement P (a, true) t.2 (c t.2))).sum

section Algebra
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  (P : ι → A)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem weightedWordOperator_nil : weightedWordOperator P [] = 0 := rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem weightedWordOperator_cons (r : ℝ) (w : Word ι) (ts : List (ℝ × Word ι)) :
    weightedWordOperator P ((r, w) :: ts) = r • wordOperator P w + weightedWordOperator P ts := rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem weightedWordOperator_append (ts us : List (ℝ × Word ι)) :
    weightedWordOperator P (ts ++ us) = weightedWordOperator P ts + weightedWordOperator P us := by
  simp only [weightedWordOperator, List.map_append, List.sum_append]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem weightedWordOperator_scale (r : ℝ) (ts : List (ℝ × Word ι)) :
    weightedWordOperator P (scaleWordTerms r ts) = r • weightedWordOperator P ts := by
  induction ts with
  | nil => simp only [scaleWordTerms, List.map_nil, weightedWordOperator_nil, smul_zero]
  | cons t ts ih =>
      rcases t with ⟨b, w⟩
      simp only [scaleWordTerms, List.map_cons, weightedWordOperator_cons] at ih ⊢
      rw [ih, mul_smul, smul_add]

theorem weightedPurityResidual_distribution (a : ι) (c : Word ι → ℝ)
    (ts : List (ℝ × Word ι)) :
    weightedPurityResidual P a c ts =
      P a * weightedWordOperator P ts * P a - weightedWordScalar c ts • P a := by
  induction ts with
  | nil => simp only [weightedPurityResidual, weightedWordOperator_nil,
      weightedWordScalar, List.map_nil, List.sum_nil, mul_zero, zero_mul, zero_smul, sub_zero]
  | cons t ts ih =>
      rcases t with ⟨r, w⟩
      change r • outcomePurityElement P (a, true) w (c w) + weightedPurityResidual P a c ts = _
      rw [ih]
      simp only [weightedWordOperator_cons, weightedWordScalar, List.map_cons, List.sum_cons,
        outcomePurityElement, algebraicOutcome, ite_true, mul_add, add_mul,
        mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul, add_smul]
      module

omit [SMulCommClass ℝ A A] in
theorem weightedPurityResidual_mul_amplitude (a : ι) (c : Word ι → ℝ)
    (ts : List (ℝ × Word ι)) (t : Word ι) :
    weightedPurityResidual P a c ts * wordAmplitude P t =
      (ts.map (fun u => u.1 •
        (outcomePurityElement P (a, true) u.2 (c u.2) * wordAmplitude P t))).sum := by
  induction ts with
  | nil => simp only [weightedPurityResidual, List.map_nil, List.sum_nil, zero_mul]
  | cons u ts ih =>
      change (u.1 • outcomePurityElement P (a, true) u.2 (c u.2) +
          weightedPurityResidual P a c ts) * wordAmplitude P t = _
      rw [add_mul, smul_mul_assoc, ih]
      rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem accessWordTerms_operator (hstar : ∀ i, star (P i) = P i) (i : ι) (w : Word ι) :
    weightedWordOperator P (accessWordTerms i w) =
      P i * wordOperator P w + wordOperator P w * P i := by
  simp only [accessWordTerms, signedAccessChoices, List.map_cons, List.map_nil,
    accessPrefix, weightedWordOperator_cons, weightedWordOperator_nil,
    one_smul, neg_one_smul, add_zero, wordOperator_cons P hstar,
    algebraicOutcome, Bool.false_eq_true, ite_true, ite_false]
  noncomm_ring

theorem accessLiftWordTerms_operator (hstar : ∀ i, star (P i) = P i)
    (i : ι) (ts : List (ℝ × Word ι)) :
    weightedWordOperator P (accessLiftWordTerms i ts) =
      P i * weightedWordOperator P ts + weightedWordOperator P ts * P i := by
  induction ts with
  | nil => simp only [accessLiftWordTerms, List.flatMap_nil,
      weightedWordOperator_nil, mul_zero, zero_mul, add_zero]
  | cons t ts ih =>
      simp only [accessLiftWordTerms, List.flatMap_cons] at ih ⊢
      rw [weightedWordOperator_append, weightedWordOperator_scale,
        accessWordTerms_operator P hstar, ih]
      rcases t with ⟨r, w⟩
      rw [weightedWordOperator_cons]
      simp only [smul_add, mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
      abel

theorem doubleAccessWordTerms_operator (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (k l m : ι) :
    weightedWordOperator P (doubleAccessWordTerms k l m) =
      P k * (P l * P m + P m * P l) + (P l * P m + P m * P l) * P k := by
  rw [doubleAccessWordTerms, accessLiftWordTerms_operator P hstar,
    accessWordTerms_operator P hstar, wordOperator_singleton P hp hstar]
  rfl

theorem polarizedTripleWordTerms_operator (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (k l m : ι) :
    weightedWordOperator P (polarizedTripleWordTerms k l m) =
      (2 : ℝ) • (P k * P l * P m + P m * P l * P k) := by
  rw [polarizedTripleWordTerms, weightedWordOperator_append, weightedWordOperator_append,
    weightedWordOperator_scale, neg_one_smul]
  rw [doubleAccessWordTerms_operator P hp hstar, doubleAccessWordTerms_operator P hp hstar,
    doubleAccessWordTerms_operator P hp hstar]
  rw [two_smul ℝ]
  noncomm_ring

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem pairDefect_primitive_decomposition (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (a b : ι) (o : ℝ) :
    P a * P b * P a - o • P a = outcomePurityElement P (a, true) [(b, true)] o := by
  rw [outcomePurityElement, wordOperator_singleton P hp hstar]
  rfl

theorem triangleDefect_primitive_decomposition (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (a b d : ι) (c : Word ι → ℝ) (R : ℝ)
    (hscalar : c [(d, true)] + c [(b, true), (d, true)] -
      c [(b, false), (d, true)] = 2 * R) :
    P a * (P b * P d + P d * P b) * P a - (2 * R) • P a =
      weightedPurityResidual P a c (accessWordTerms b [(d, true)]) := by
  have hs : weightedWordScalar c (accessWordTerms b [(d, true)]) = 2 * R := by
    simp only [weightedWordScalar, accessWordTerms, signedAccessChoices,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      accessPrefix, one_mul, neg_one_mul, add_zero]
    linarith [hscalar]
  rw [weightedPurityResidual_distribution, accessWordTerms_operator P hstar,
    wordOperator_singleton P hp hstar, hs]
  rfl

theorem symmetricTripleDefect_primitive_decomposition (hp : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (a k l m : ι)
    (c : Word ι → ℝ) (Q : ℝ)
    (hscalar : weightedWordScalar c (polarizedTripleWordTerms k l m) = 4 * Q) :
    P a * (P k * P l * P m + P m * P l * P k) * P a - (2 * Q) • P a =
      (1 / 2 : ℝ) • weightedPurityResidual P a c (polarizedTripleWordTerms k l m) := by
  rw [weightedPurityResidual_distribution, polarizedTripleWordTerms_operator P hp hstar,
    hscalar]
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul]
  module

end Algebra
end AlbertSequential
