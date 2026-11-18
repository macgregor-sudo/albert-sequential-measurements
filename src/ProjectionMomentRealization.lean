/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ProjectionMomentDescent
public import AlgebraicMomentBinding

/-! Every admissible all-word moment function has an actual algebraic
projective realization. This is not a Hilbert-space completion theorem. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def momentsToProjectiveData {n : ℕ} (m : ProjectionMoments n)
    (hm : AdmissibleProjectionMoments n m) :
    AlgebraicProjectiveData (Fin n) (UniversalProjectionAlgebra n) where
  projection := universalProjection
  idempotent := universalProjection_idempotent
  selfAdjoint := universalProjection_selfAdjoint
  state := projectionMomentState hm
  state_unit := projectionMomentState_one hm
  state_star := projectionMomentState_star hm
  state_positive := projectionMomentState_positive hm

theorem projectionQuotient_monomial {n : ℕ} (w : ProjectionMonomial n) :
    projectionQuotient n (evaluateMonomial (FreeAlgebra.ι ℝ) w) =
      evaluateMonomial universalProjection w := by
  induction w with
  | nil => exact map_one _
  | cons i w ih =>
      simp only [evaluateMonomial_cons, map_mul, ih]
      rfl

theorem momentsOf_realizedMoments {n : ℕ} (m : ProjectionMoments n)
    (hm : AdmissibleProjectionMoments n m) :
    momentsOfProjectiveData (momentsToProjectiveData m hm) = m := by
  funext w
  change projectionMomentState hm (evaluateMonomial universalProjection w) = m w
  rw [← projectionQuotient_monomial, projectionMomentState_quotient,
    freeMomentFunctional_monomial]

theorem realizedMoments_probability {n : ℕ} (m : ProjectionMoments n)
    (hm : AdmissibleProjectionMoments n m) (w : Word (Fin n)) :
    (momentsToProjectiveData m hm).probability w = momentWordProbability m w := by
  rw [← momentWordProbability_eq_probability, momentsOf_realizedMoments]

/-- Exact characterization in a fixed, state-independent presented algebra. -/
theorem admissible_iff_universalProjectionModel {n : ℕ} (m : ProjectionMoments n) :
    AdmissibleProjectionMoments n m ↔
      ∃ M : AlgebraicProjectiveData (Fin n) (UniversalProjectionAlgebra n),
        momentsOfProjectiveData M = m := by
  constructor
  · intro hm
    exact ⟨momentsToProjectiveData m hm, momentsOf_realizedMoments m hm⟩
  · rintro ⟨M, rfl⟩
    exact momentsOfProjectiveData_admissible M

/-- No faithful, tracial, finite-dimensional or nonzero-history assumption. -/
theorem realizedMoments_probability_eq_original
    {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A) (w : Word (Fin n)) :
    (momentsToProjectiveData (momentsOfProjectiveData M)
      (momentsOfProjectiveData_admissible M)).probability w = M.probability w := by
  rw [realizedMoments_probability, momentWordProbability_eq_probability]

end AlbertSequential
