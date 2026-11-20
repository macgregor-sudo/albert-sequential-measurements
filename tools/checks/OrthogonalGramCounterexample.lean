module

import Bridge.PrintedCriterion
import FourTraceWordRelation

open AlbertSequential Matrix
open AlbertSequential.NativeAnalysis
open scoped Matrix ComplexOrder

noncomputable section

namespace PrintedOrthogonalPeer

def P (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun j => if i = j then 1 else 0

theorem P_eq_dyad (i : Fin 4) :
    P i = vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))) := by
  ext j k
  by_cases h : j = k
  · subst k
    by_cases h' : i = j <;> simp [P, vecMulVec_apply, Pi.star_single, h', Ne.symm]
  · by_cases h' : i = j
    · subst j
      simp [P, vecMulVec_apply, Pi.star_single, h, Ne.symm h]
    · simp [P, vecMulVec_apply, Pi.star_single, Pi.single_apply, h, Ne.symm h']

theorem P_idempotent (i : Fin 4) : P i * P i = P i := by
  rw [P, diagonal_mul_diagonal]
  congr 1
  funext j
  by_cases h : i = j <;> simp [h]

theorem P_hermitian (i : Fin 4) : (P i).IsHermitian := by
  apply isHermitian_diagonal_of_self_adjoint
  change star (fun j : Fin 4 => if i = j then (1 : ℂ) else 0) = _
  funext j
  by_cases h : i = j <;> simp [h]

theorem P_orthogonal {i j : Fin 4} (hij : i ≠ j) : P i * P j = 0 := by
  rw [P, P, diagonal_mul_diagonal, ← diagonal_zero]
  congr 1
  funext k
  by_cases h : i = k
  · subst k
    simp [Ne.symm hij]
  · simp [h]

private theorem P_commutes_amplitude (i : Fin 4) (w : Word (Fin 4)) :
    Commute (P i) (wordAmplitude P w) := by
  have h (j : Fin 4) : Commute (P i) (P j) := Matrix.commute_diagonal _ _
  induction w with
  | nil => rw [wordAmplitude_nil]; exact Commute.one_right _
  | cons a w ih =>
    rw [wordAmplitude_cons]
    apply ih.mul_right
    obtain ⟨j,b⟩ := a
    cases b
    · exact (Commute.one_right (P i)).sub_right (h j)
    · exact h j

def uniformDensity : Matrix (Fin 4) (Fin 4) ℂ := (1/4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

private theorem uniformDensity_positive : uniformDensity.PosSemidef := by
  exact Matrix.PosSemidef.one.smul (by norm_num : 0 ≤ (1/4 : ℝ))

private theorem uniformDensity_trace : uniformDensity.trace = 1 := by
  norm_num [uniformDensity, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]

def orthogonalModel : AlbertChallenge.ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (Fin 4)) :=
  AlbertChallenge.Bridge.matrixRepresentation P P_hermitian P_idempotent uniformDensity
    uniformDensity_positive uniformDensity_trace

private theorem orthogonal_probability_zeros (i j : Fin 4) (hij : i ≠ j) (w : Word (Fin 4)) :
    orthogonalModel.probability ((i,true) :: (w ++ [(j,true)])) = 0 := by
  have ho : wordAmplitude P ((i,true) :: (w ++ [(j,true)])) = 0 := by
    rw [← List.cons_append, wordAmplitude_append_singleton, wordAmplitude_cons]
    change P j * (wordAmplitude P w * P i) = 0
    rw [← Matrix.mul_assoc, (P_commutes_amplitude j w).eq, Matrix.mul_assoc,
      P_orthogonal (Ne.symm hij), Matrix.mul_zero]
  have hp := AlbertChallenge.Bridge.matrixRepresentation_probability
    P P_hermitian P_idempotent uniformDensity uniformDensity_positive uniformDensity_trace
    ((i,true) :: (w ++ [(j,true)]))
  change orthogonalModel.probability ((i,true) :: (w ++ [(j,true)])) = _ at hp
  rw [hp, wordOperator, ho]
  simp

private theorem access_zeros (i j k : Fin 4) (hik : i ≠ k) :
    weightedWordScalar (conditionalFour orthogonalModel.probability i) (accessWordTerms j [(k,true)]) = 0 := by
  have h (w : Word (Fin 4)) :
      conditionalFour orthogonalModel.probability i (w ++ [(k,true)]) = 0 := by
    rw [conditionalFour, orthogonal_probability_zeros _ _ hik, mul_zero]
  have h0 : conditionalFour orthogonalModel.probability i [(k,true)] = 0 := h []
  have h1 : conditionalFour orthogonalModel.probability i [(j,true),(k,true)] = 0 := h [(j,true)]
  have h2 : conditionalFour orthogonalModel.probability i [(j,false),(k,true)] = 0 := h [(j,false)]
  simp [weightedWordScalar, accessWordTerms, signedAccessChoices, accessPrefix, h0, h1, h2]

private theorem double_access_zeros (i j k l : Fin 4) (hil : i ≠ l) :
    weightedWordScalar (conditionalFour orthogonalModel.probability i) (doubleAccessWordTerms j k l) = 0 := by
  have h (w : Word (Fin 4)) :
      conditionalFour orthogonalModel.probability i (w ++ [(l,true)]) = 0 := by
    rw [conditionalFour, orthogonal_probability_zeros _ _ hil, mul_zero]
  have h0 : conditionalFour orthogonalModel.probability i [(l,true)] = 0 := h []
  have h1 (b : Bool) : conditionalFour orthogonalModel.probability i [(j,b),(l,true)] = 0 := h [(j,b)]
  have h2 (b : Bool) : conditionalFour orthogonalModel.probability i [(k,b),(l,true)] = 0 := h [(k,b)]
  have h3 (b c : Bool) : conditionalFour orthogonalModel.probability i [(j,b),(k,c),(l,true)] = 0 :=
    h [(j,b),(k,c)]
  simp [weightedWordScalar, doubleAccessWordTerms, accessLiftWordTerms, scaleWordTerms,
    accessWordTerms, signedAccessChoices, accessPrefix, h0, h1, h2, h3]

/-- The actual orthogonal projection model with uniform density has trace
relation sides zero and one half when evaluated from words. -/
theorem orthogonal_probability_trace_sides :
    let f := orthogonalModel.probability
    let o := fun i j => conditionalFour f i [(j,true)]
    let R := fun i j k => weightedWordScalar (conditionalFour f i) (accessWordTerms j [(k,true)]) / 2
    let t := fun i j k l => weightedWordScalar (conditionalFour f i) (doubleAccessWordTerms j k l) / 4
    (t 0 1 2 3 + t 0 2 1 3 + t 0 3 1 2 = 0) ∧
    (1/2 - 1/2*(o 0 1+o 0 2+o 0 3+o 1 2+o 1 3+o 2 3) +
      1/2*(o 0 1*o 2 3+o 0 2*o 1 3+o 0 3*o 1 2) +
      R 0 1 2+R 0 1 3+R 0 2 3+R 1 2 3 = 1/2) := by
  dsimp only
  have hOverlap (i j : Fin 4) (hij : i ≠ j) :
      conditionalFour orthogonalModel.probability i [(j,true)] = 0 := by
    rw [conditionalFour, show orthogonalModel.probability [(i,true),(j,true)] = 0 from
      orthogonal_probability_zeros i j hij [], mul_zero]
  rw [hOverlap 0 1 (by decide), hOverlap 0 2 (by decide), hOverlap 0 3 (by decide),
    hOverlap 1 2 (by decide), hOverlap 1 3 (by decide), hOverlap 2 3 (by decide),
    access_zeros 0 1 2 (by decide), access_zeros 0 1 3 (by decide),
    access_zeros 0 2 3 (by decide), access_zeros 1 2 3 (by decide),
    double_access_zeros 0 1 2 3 (by decide), double_access_zeros 0 2 1 3 (by decide),
    double_access_zeros 0 3 1 2 (by decide)]
  norm_num

/-- The orthogonal model cannot reproduce the mixed Albert table through length four. -/
theorem orthogonal_probability_not_matching (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ¬ (∀ w : Word (Fin 4), w.length ≤ 4 →
      orthogonalModel.probability w = nativeWordProbability p ((1/3 : ℝ) • albertUnit) w) := by
  intro h
  have bad := matching_four_words_trace_relation p hp orthogonalModel.probability h
  obtain ⟨hl,hr⟩ := orthogonal_probability_trace_sides
  dsimp only at bad hl hr
  rw [hl,hr] at bad
  norm_num at bad

#print axioms P_eq_dyad
#print axioms orthogonal_probability_trace_sides
#print axioms orthogonal_probability_not_matching

end PrintedOrthogonalPeer
