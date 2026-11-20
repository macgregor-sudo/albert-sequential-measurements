/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CyclicNullHistories
public import CornerPrimitiveBinding
public import NativeScalarAccess
public import NativeDensityCompactness
public import TetrahedronRelabeling

/-! The native corner contractions in the actual all-word matching cyclic representation. -/
@[expose] public section
noncomputable section

namespace AlbertSequential

open NativeAnalysis

variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

private theorem purityCombination_eval {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Word ι → V) (q : Outcome ι) (v : Word ι) (c : ℝ) :
    let E := Finsupp.single ([q] ++ v ++ purityMirror v ++ [q]) (1 : ℝ) +
      Finsupp.single ([q] ++ v) (- (2 * c)) + Finsupp.single [q] (c ^ 2)
    E.sum (fun w a => a • f w) =
      f ([q] ++ v ++ purityMirror v ++ [q]) - (2 * c) • f ([q] ++ v) +
        c ^ 2 • f [q] := by
  change Finsupp.linearCombination ℝ f _ = _
  simp only [map_add, Finsupp.linearCombination_single, one_smul, neg_smul, sub_eq_add_neg]

/-- Atomic purity on the actual cyclic Hilbert space, including zero-probability histories. -/
theorem cyclic_nativePurityElement_eq_zero (M : AlgebraicProjectiveData ι A)
    (p : ι → Albert) (ρ : Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (hmatch : M.Matches p ρ) (q : Outcome ι) (hq : IsAtom (nativeOutcome p q)) (v : Word ι) :
    outcomePurityElement (cyclicHilbertProjection M) q v
      (tracePairing (nativeOutcome p q) (nativeWordEffect p v)) = 0 := by
  let c := tracePairing (nativeOutcome p q) (nativeWordEffect p v)
  let Q := cyclicWordElement M [q]
  let T := cyclicWordElement M v
  let Z : CyclicWordAlgebra M := Q * (star T * T) * Q - c • Q
  have hZ : (Z : A) = outcomePurityElement M.projection q v c := by
    change wordAmplitude M.projection [q] * wordOperator M.projection v *
      wordAmplitude M.projection [q] - c • wordAmplitude M.projection [q] = _
    simp only [wordAmplitude_singleton, outcomePurityElement]
  have hself : star (Z : A) = Z := by rw [hZ, outcomePurityElement_star M.projection M.selfAdjoint]
  let E := Finsupp.single ([q] ++ v ++ purityMirror v ++ [q]) (1 : ℝ) +
    Finsupp.single ([q] ++ v) (- (2 * c)) + Finsupp.single [q] (c ^ 2)
  have hE : E.sum (fun w a => a • wordOperator M.projection w) = (Z : A) * Z := by
    rw [purityCombination_eval, hZ]
    symm
    simpa only [List.nil_append, wordAmplitude_nil, mul_one,
      outcomePurityElement_star M.projection M.selfAdjoint] using
      purityResidual_operator M.projection M.idempotent M.selfAdjoint q v [] c
  have hθ : AppF.nativeWordCombinationEffect E p = 0 := by
    let θ := AppF.nativeWordCombinationEffect E p
    change θ = 0
    apply (tracePairing_self_eq_zero θ).mp
    change tracePairing θ (AppF.nativeWordCombinationEffect E p) = 0
    rw [AppF.nativeWordCombinationEffect, purityCombination_eval, ← AppF.tracePairingLM_apply,
      map_add, map_sub, map_smul, map_smul]
    simp only [AppF.tracePairingLM_apply, smul_eq_mul, ← nativeWordProbability_eq_pairing]
    have hmid := native_corner_middle_probability p θ [] v q hq
    have hlong := native_corner_long_probability p hp θ [] v q hq
    simp only [List.nil_append] at hmid hlong
    rw [hmid, hlong]
    change c ^ 2 * _ - (2 * c) * (c * _) + c ^ 2 * _ = 0
    ring
  have h := cyclic_null_operator_of_matches M p ρ E Z hself hE hθ hmatch
  simpa only [Z, Q, T, map_sub, map_mul, map_star, map_smul,
    cyclicHilbertRepresentation_outcome, cyclicHilbertRepresentation_word,
    wordOperator, outcomePurityElement, wordAmplitude_singleton, c] using h

/-- Core Lemma 5.8. The three operator relations hold for every ordered choice of labels. -/
theorem cyclic_native_corner_relations (M : AlgebraicProjectiveData (Fin 4) A)
    (p : Fin 4 → Albert) (ρ : Albert) (hp : ∀ i, IsAtom (p i)) (hmatch : M.Matches p ρ) :
    let P := cyclicHilbertProjection M
    (∀ a b, P a * P b * P a = nativeOverlaps p a b • P a) ∧
    (∀ a b c, P a * (P b * P c + P c * P b) * P a = (2 * nativeTriangles p a b c) • P a) ∧
    (∀ a b c d, P a * (P b * P c * P d + P d * P c * P b) * P a =
      (2 * tracePairing (p a) (jordanTriple (p b) (p c) (p d))) • P a) := by
  let P := cyclicHilbertProjection M
  have hP i : P i * P i = P i := (cyclicHilbertProjection_isStarProjection M i).isIdempotentElem.eq
  have hstar i : star (P i) = P i := (cyclicHilbertProjection_isStarProjection M i).isSelfAdjoint.star_eq
  have he := fun i => (hp i).1
  have hpurity (a : Fin 4) (v : Word (Fin 4)) :
      outcomePurityElement P (a, true) v (nativeWordProbability p (p a) v) = 0 := by
    rw [nativeWordProbability_eq_pairing]
    exact cyclic_nativePurityElement_eq_zero M p ρ he hmatch (a, true) (hp a) v
  have hweighted (a : Fin 4) (ts : List (ℝ × Word (Fin 4))) :
      weightedPurityResidual P a (nativeWordProbability p (p a)) ts = 0 := by
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      change t.1 • outcomePurityElement P (a, true) t.2
        (nativeWordProbability p (p a) t.2) +
          weightedPurityResidual P a (nativeWordProbability p (p a)) ts = 0
      rw [hpurity, smul_zero, zero_add, ih]
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have heq : nativeWordProbability p (p a) [(b, true)] = nativeOverlaps p a b := by
      rw [nativeWordProbability_eq_pairing, nativeWordEffect_singleton p he]
      rfl
    apply sub_eq_zero.mp
    change pairDefectElement (P a) (P b) (nativeOverlaps p a b) = 0
    rw [pairDefectElement_primitive P hP hstar, ← heq, hpurity]
  · intro a b c
    have hs := native_scalar_triangle_access p he (p a) b c
    have hscalar : nativeWordProbability p (p a) [(c, true)] +
        nativeWordProbability p (p a) [(b, true), (c, true)] -
        nativeWordProbability p (p a) [(b, false), (c, true)] =
          2 * nativeTriangles p a b c := by
      simpa [weightedWordScalar, accessWordTerms, signedAccessChoices, accessPrefix,
        sub_eq_add_neg, add_assoc, nativeTriangles] using hs
    apply sub_eq_zero.mp
    change triangleDefectElement (P a) (P b) (P c) (nativeTriangles p a b c) = 0
    rw [triangleDefectElement_primitive P hP hstar _ _ _ _ _ hscalar, hweighted]
  · intro a b c d
    let Q := tracePairing (p a) (jordanTriple (p b) (p c) (p d))
    have htriple : jordanMul (p b) (jordanMul (p c) (p d)) +
        jordanMul (p d) (jordanMul (p b) (p c)) -
        jordanMul (p c) (jordanMul (p b) (p d)) = jordanTriple (p b) (p c) (p d) := by
      rw [jordanTriple, jordanMul_comm (p b) (jordanMul (p c) (p d)),
        jordanMul_comm (p d) (jordanMul (p b) (p c)),
        jordanMul_comm (p c) (jordanMul (p b) (p d)), jordanMul_comm (p c) (p d), add_comm]
    have hscalar : weightedWordScalar (nativeWordProbability p (p a))
        (polarizedTripleWordTerms b c d) = 4 * Q := by
      rw [native_scalar_polarizedTriple_access p he, htriple]
    apply sub_eq_zero.mp
    change tripleDefectElement (P a) (P b) (P c) (P d) Q = 0
    rw [tripleDefectElement_primitive P hP hstar _ _ _ _ _ _ hscalar, hweighted, smul_zero]

/-- The ordered tetrahedron interface for the same bounded cyclic projections. -/
theorem cyclic_native_corner_relations_at_order (M : AlgebraicProjectiveData (Fin 4) A)
    (p : Fin 4 → Albert) (ρ : Albert) (hp : ∀ i, IsAtom (p i)) (hmatch : M.Matches p ρ)
    (j k l m : Fin 4) (horder : Function.Injective (![j, k, l, m] : Fin 4 → Fin 4)) :
    CornerRelationsAtOrder (cyclicHilbertProjection M) (nativeOverlaps p) (nativeTriangles p)
      j k l m ![tracePairing (p j) (jordanTriple (p k) (p l) (p m)),
        tracePairing (p j) (jordanTriple (p l) (p m) (p k)),
        tracePairing (p j) (jordanTriple (p m) (p k) (p l))] := by
  obtain ⟨ho, hR, hQ⟩ := cyclic_native_corner_relations M p ρ hp hmatch
  exact {
    distinct := horder
    idempotent := fun i => (cyclicHilbertProjection_isStarProjection M i).isIdempotentElem.eq
    overlap_symmetric := fun a b => tracePairing_comm (p a) (p b)
    triangle_swap := fun a b c => by
      constructor
      · simp only [nativeTriangles, ← tracePairing_associative, jordanMul_comm (p a) (p b)]
      · simp only [nativeTriangles, jordanMul_comm (p b) (p c)]
    pair := fun a b _ => ho a b
    triangle_jkl := hR j k l
    triangle_jlm := hR j l m
    triangle_jmk := hR j m k
    triangle_klm := hR k l m
    quadruple_klm := hQ j k l m
    quadruple_lmk := hQ j l m k
    quadruple_mkl := hQ j m k l }

end AlbertSequential
