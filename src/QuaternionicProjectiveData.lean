/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QuaternionicOperatorAlgebra
public import BoundedWordEffects

/-! Arbitrary positive normalized real-linear states on the concrete
quaternionic commutant. No extension to all real operators is assumed. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

structure QuaternionicProjectiveData (ι : Type*) (Q : QuaternionicOperatorStructure H) where
  projection : ι → Q.operatorAlgebra
  isStarProjection : ∀ i, IsStarProjection (projection i)
  state : selfAdjoint Q.operatorAlgebra →ₗ[ℝ] ℝ
  normalized : state 1 = 1
  positive : ∀ T : selfAdjoint Q.operatorAlgebra,
    (Q.operatorValue T.val).IsPositive → 0 ≤ state T

namespace QuaternionicProjectiveData
variable {Q : QuaternionicOperatorStructure H}

def toAlgebraic (M : QuaternionicProjectiveData ι Q) :
    AlgebraicProjectiveData ι Q.operatorAlgebra :=
  algebraicProjectiveDataOfSelfAdjointState M.projection
    (fun i => (M.isStarProjection i).isIdempotentElem)
    (fun i => (M.isStarProjection i).isSelfAdjoint)
    M.state M.normalized
    (fun X => M.positive ⟨star X * X, IsSelfAdjoint.star_mul_self X⟩
      (Q.operatorValue_star_mul_positive X))

def operatorProjection (M : QuaternionicProjectiveData ι Q) (i : ι) : H →L[ℝ] H :=
  Q.operatorValue (M.projection i)

theorem operatorProjection_isStarProjection (M : QuaternionicProjectiveData ι Q) (i : ι) :
    IsStarProjection (M.operatorProjection i) :=
  (M.isStarProjection i).map Q.operatorValue

theorem operatorProjection_eq_starProjection (M : QuaternionicProjectiveData ι Q) (i : ι) :
    ∃ (U : Submodule ℝ H) (_ : U.HasOrthogonalProjection),
      M.operatorProjection i = U.starProjection :=
  isStarProjection_iff_eq_starProjection.mp (M.operatorProjection_isStarProjection i)

theorem operatorValue_outcome (P : ι → Q.operatorAlgebra) (a : Outcome ι) :
    Q.operatorValue (algebraicOutcome P a) = boundedOutcome (fun i => Q.operatorValue (P i)) a := by
  rcases a with ⟨i,b⟩
  cases b <;> simp only [algebraicOutcome, boundedOutcome, Bool.false_eq_true,
    ↓reduceIte, map_sub, map_one] <;> rfl

theorem operatorValue_wordOperator (P : ι → Q.operatorAlgebra)
    (hstar : ∀ i, star (P i) = P i) (w : Word ι) :
    Q.operatorValue (wordOperator P w) =
      boundedWordEffect (fun i => Q.operatorValue (P i)) w := by
  induction w with
  | nil => rw [wordOperator_nil, map_one]; rfl
  | cons a w ih =>
    rw [wordOperator_cons P hstar, map_mul, map_mul, ih,
      operatorValue_outcome, boundedWordEffect]
    rfl

def wordEffect (M : QuaternionicProjectiveData ι Q) (w : Word ι) :
    selfAdjoint Q.operatorAlgebra :=
  ⟨wordOperator M.projection w, wordOperator_star M.projection w⟩

theorem wordEffect_operatorValue (M : QuaternionicProjectiveData ι Q) (w : Word ι) :
    Q.operatorValue (M.wordEffect w).val = boundedWordEffect M.operatorProjection w :=
  operatorValue_wordOperator M.projection (fun i => (M.isStarProjection i).isSelfAdjoint) w

theorem toAlgebraic_probability (M : QuaternionicProjectiveData ι Q) (w : Word ι) :
    M.toAlgebraic.probability w = M.state (M.wordEffect w) :=
  algebraicProjectiveDataOfSelfAdjointState_probability M.projection
    (fun i => (M.isStarProjection i).isIdempotentElem)
    (fun i => (M.isStarProjection i).isSelfAdjoint) M.state M.normalized
    (fun X => M.positive ⟨star X * X, IsSelfAdjoint.star_mul_self X⟩
      (Q.operatorValue_star_mul_positive X)) w

theorem toAlgebraic_matches_iff (M : QuaternionicProjectiveData ι Q)
    (p : ι → Albert) (ρ : Albert) :
    M.toAlgebraic.Matches p ρ ↔
      ∀ w, M.state (M.wordEffect w) = nativeWordProbability p ρ w := by
  simp only [AlgebraicProjectiveData.Matches, M.toAlgebraic_probability]

end QuaternionicProjectiveData
end AlbertSequential
