/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.AlbertHeadlines
public import HilbertOperatorAlgebra
public import SelfAdjointStateGram
public import ChronologicalWords
public import AlbertUniformSeparation

/-!
# Representation-side bridge: every Challenge model is a development algebraic model

The development's exclusion theorems are proved for its algebraic comparator class
`AlbertSequential.AlgebraicProjectiveData` (self-adjoint idempotents in a real `*`-algebra, a
Hermitian, positive, normalised real functional). Each of the Challenge's three model classes yields
such data with the same word probabilities:

* `AlgebraicModel n A`: the same data (`ofAlgebraicModel`).
* `ProjectiveRepresentation n 𝕜 H`: the bounded operators regarded as a real algebra
  (`HilbertOperatorAlgebra 𝕜 H`), with the functional `T ↦ Re φ(T)` symmetrised through the
  self-adjoint part (`ofProjectiveRepresentation`). A positive `𝕜`-linear state need not be
  Hermitian on all operators when `𝕜 = ℝ`; only its values on self-adjoint elements are used, and
  word operators are self-adjoint.
* `QuaternionicRepresentation n S`: the `ℍ`-linear operators themselves, a real `*`-algebra, with
  the given state symmetrised the same way (`ofQuaternionicRepresentation`). No identification of
  the commutant with the development's `QuaternionicOperatorStructure` is needed.

The only algebraic identity used is the palindrome identity `Q₁⋯Q_m⋯Q₁ = (Q_m⋯Q₁)* (Q_m⋯Q₁)` for
self-adjoint idempotents (`wordOperator_palindrome`).
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge

/-! ### The palindrome identity -/

section Palindrome

variable {A : Type*} [Ring A] [StarRing A] {n : ℕ}

omit [StarRing A] in
theorem outcomeOperator_eq (P : Fin n → A) (a : Fin n × Bool) :
    outcomeOperator P a = AlbertSequential.algebraicOutcome P a := rfl

omit [StarRing A] in
theorem foldl_amplitude (P : Fin n → A) (w : Word n) (x : A) :
    w.foldl (fun x a => AlbertSequential.algebraicOutcome P a * x) x =
      (w.map (outcomeOperator P)).reverse.prod * x := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc, outcomeOperator_eq]

omit [StarRing A] in
theorem wordAmplitude_eq (P : Fin n → A) (w : Word n) :
    AlbertSequential.wordAmplitude P w = (w.map (outcomeOperator P)).reverse.prod := by
  unfold AlbertSequential.wordAmplitude
  rw [foldl_amplitude, mul_one]

variable (P : Fin n → A) (hidem : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
include hidem hstar

theorem outcomeOperator_star (a : Fin n × Bool) : star (outcomeOperator P a) = outcomeOperator P a := by
  unfold outcomeOperator
  split
  · exact hstar _
  · rw [star_sub, star_one, hstar]

theorem outcomeOperator_idem (a : Fin n × Bool) :
    outcomeOperator P a * outcomeOperator P a = outcomeOperator P a := by
  unfold outcomeOperator
  split
  · exact hidem _
  · rw [sub_mul, one_mul, mul_sub, mul_one, hidem]
    abel

theorem star_reverse_prod (u : Word n) :
    star ((u.map (outcomeOperator P)).reverse.prod) = (u.map (outcomeOperator P)).prod := by
  induction u with
  | nil => simp
  | cons b u ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_cons,
      List.prod_nil, mul_one, star_mul, ih, outcomeOperator_star P hidem hstar]

/-- `Q₁⋯Q_{m−1} Q_m Q_{m−1}⋯Q₁ = (Q_m⋯Q₁)* (Q_m⋯Q₁)` for self-adjoint idempotent tests. -/
theorem wordOperator_palindrome (w : Word n) :
    AlbertChallenge.wordOperator P w = AlbertSequential.wordOperator P w := by
  unfold AlbertChallenge.wordOperator AlbertSequential.wordOperator
  rw [wordAmplitude_eq]
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u a _ =>
    have hrev : ((u ++ [a]).map (outcomeOperator P)).reverse.prod =
        outcomeOperator P a * (u.map (outcomeOperator P)).reverse.prod := by
      rw [List.map_append, List.reverse_append, List.prod_append]
      simp
    rw [hrev, star_mul, star_reverse_prod P hidem hstar, outcomeOperator_star P hidem hstar,
      List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [List.dropLast_concat, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc _ (outcomeOperator P a) (outcomeOperator P a * _),
      ← mul_assoc (outcomeOperator P a) (outcomeOperator P a), outcomeOperator_idem P hidem hstar,
      ← mul_assoc]

end Palindrome

/-- A ring homomorphism carries the Challenge's word operator to the word operator of the
image projections. -/
theorem wordOperator_map {A B F : Type*} [Ring A] [Ring B] [FunLike F A B] [RingHomClass F A B]
    (φ : F) {n : ℕ} (P : Fin n → A) (w : Word n) :
    φ (AlbertChallenge.wordOperator P w) = AlbertChallenge.wordOperator (fun i => φ (P i)) w := by
  have hQ : ∀ a, φ (outcomeOperator P a) = outcomeOperator (fun i => φ (P i)) a := by
    intro a
    unfold outcomeOperator
    split
    · rfl
    · rw [map_sub, map_one]
  unfold AlbertChallenge.wordOperator
  rw [map_mul, map_list_prod, map_list_prod, List.map_reverse, List.map_dropLast, List.map_map]
  simp only [Function.comp_def, hQ]

/-! ### From a real functional to the development's algebraic comparator -/

section Functional

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [StarModule ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {n : ℕ}

/-- Restriction of a real functional to the self-adjoint elements. -/
def restrictSelfAdjoint (f : A →ₗ[ℝ] ℝ) : selfAdjoint A →ₗ[ℝ] ℝ where
  toFun T := f T.val
  map_add' x y := by
    rw [show ((x + y : selfAdjoint A) : A) = x + y from rfl, map_add]
  map_smul' r x := by
    rw [show ((r • x : selfAdjoint A) : A) = r • (x : A) from rfl, map_smul]
    rfl

/-- Self-adjoint idempotents and a normalised real functional, nonnegative on `x* x`, give the
development's algebraic comparator data (the functional is replaced by its value on the
self-adjoint part, which changes nothing on self-adjoint elements). -/
def ofFunctional (P : Fin n → A) (hidem : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (f : A →ₗ[ℝ] ℝ) (h1 : f 1 = 1) (hpos : ∀ x, 0 ≤ f (star x * x)) :
    AlbertSequential.AlgebraicProjectiveData (Fin n) A :=
  AlbertSequential.algebraicProjectiveDataOfSelfAdjointState P hidem hstar
    (restrictSelfAdjoint f) h1 hpos

theorem ofFunctional_probability (P : Fin n → A) (hidem : ∀ i, P i * P i = P i)
    (hstar : ∀ i, star (P i) = P i) (f : A →ₗ[ℝ] ℝ) (h1 : f 1 = 1)
    (hpos : ∀ x, 0 ≤ f (star x * x)) (w : Word n) :
    (ofFunctional P hidem hstar f h1 hpos).probability w =
      f (AlbertChallenge.wordOperator P w) := by
  unfold ofFunctional
  refine (AlbertSequential.algebraicProjectiveDataOfSelfAdjointState_probability _ _ _ _ _ _ w).trans
    ?_
  show f (AlbertSequential.wordOperator P w) = _
  rw [wordOperator_palindrome P hidem hstar]

end Functional

/-! ### Algebraic models -/

section Algebraic

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] {n : ℕ}

def ofAlgebraicModel (M : AlgebraicModel n A) : AlbertSequential.AlgebraicProjectiveData (Fin n) A where
  projection := M.projection
  idempotent := M.idempotent
  selfAdjoint := M.selfAdjoint
  state := M.state
  state_unit := M.state_one
  state_star := M.state_star
  state_positive := M.state_nonneg

theorem ofAlgebraicModel_probability (M : AlgebraicModel n A) (w : Word n) :
    (ofAlgebraicModel M).probability w = M.probability w := by
  show M.state (AlbertSequential.wordOperator M.projection w) =
    M.state (AlbertChallenge.wordOperator M.projection w)
  rw [wordOperator_palindrome M.projection M.idempotent M.selfAdjoint]

end Algebraic

/-! ### Real and complex Hilbert-space representations -/

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] {n : ℕ}

open AlbertSequential in
/-- `T ↦ Re φ(T)` on the bounded operators regarded as a real algebra. -/
def reState (M : ProjectiveRepresentation n 𝕜 H) : HilbertOperatorAlgebra 𝕜 H →ₗ[ℝ] ℝ where
  toFun T := RCLike.re (M.state (operatorValue 𝕜 H T))
  map_add' S T := by rw [map_add, map_add, map_add]
  map_smul' r T := by
    rw [operatorValue_real_smul, map_smul, smul_eq_mul, RCLike.re_ofReal_mul]
    rfl

open AlbertSequential in
def ofProjectiveRepresentation (M : ProjectiveRepresentation n 𝕜 H) :
    AlgebraicProjectiveData (Fin n) (HilbertOperatorAlgebra 𝕜 H) :=
  ofFunctional (fun i => (operatorValue 𝕜 H).symm (M.projection i))
    (fun i => by rw [← map_mul, (M.isStarProjection i).isIdempotentElem.eq])
    (fun i => by
      change (operatorValue 𝕜 H).symm (star (M.projection i)) = _
      rw [(M.isStarProjection i).isSelfAdjoint.star_eq])
    (reState M)
    (by
      change RCLike.re (M.state (operatorValue 𝕜 H 1)) = 1
      rw [map_one, M.state_one, RCLike.one_re])
    (fun x => by
      obtain ⟨r, hr, he⟩ := M.state_nonneg _ (operatorValue_star_mul_positive 𝕜 H x)
      change 0 ≤ RCLike.re (M.state (operatorValue 𝕜 H (star x * x)))
      rw [he, RCLike.ofReal_re]
      exact hr)

open AlbertSequential in
theorem ofProjectiveRepresentation_probability (M : ProjectiveRepresentation n 𝕜 H) (w : Word n) :
    (ofProjectiveRepresentation M).probability w = M.probability w := by
  unfold ofProjectiveRepresentation
  rw [ofFunctional_probability]
  change RCLike.re (M.state (operatorValue 𝕜 H (AlbertChallenge.wordOperator _ w))) = _
  rw [wordOperator_map]
  simp only [RingEquiv.apply_symm_apply]
  rfl

end Hilbert

/-! ### Quaternionic representations -/

section Quaternionic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {S : RightQuaternionicStructure H} {n : ℕ}

def ofQuaternionicRepresentation (M : QuaternionicRepresentation n S) :
    AlbertSequential.AlgebraicProjectiveData (Fin n) S.linearOperators :=
  ofFunctional M.projection (fun i => (M.isStarProjection i).isIdempotentElem.eq)
    (fun i => (M.isStarProjection i).isSelfAdjoint.star_eq) M.state M.state_one
    (fun x => M.state_nonneg _ (by
      change (ContinuousLinearMap.adjoint (x : H →L[ℝ] H) ∘L (x : H →L[ℝ] H)).IsPositive
      exact ContinuousLinearMap.isPositive_adjoint_comp_self _))

theorem ofQuaternionicRepresentation_probability (M : QuaternionicRepresentation n S)
    (w : Word n) : (ofQuaternionicRepresentation M).probability w = M.probability w := by
  unfold ofQuaternionicRepresentation
  rw [ofFunctional_probability]
  rfl

end Quaternionic

end AlbertChallenge.Bridge
