/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerScalarResidualBounds
public import ScalarCliffordTelescope

/-! The actual state-independent one-base finite residual constructor.
Only scalar access and normalizer conditions are assumed. No field supplies
the telescope, zero residuals, native geometry, a rank or a prescribed ledger. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder

def gramRowAtBase (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3) :
    List (ResidualTelescopeOccurrence 4) := ResidualOccurrenceExpression.combine
  [ResidualOccurrenceExpression.scale (-d.scalarParameters.q i * d.scalarParameters.q 0) (gramAtBase d C i 0),
    ResidualOccurrenceExpression.scale (-d.scalarParameters.q i * d.scalarParameters.q 1) (gramAtBase d C i 1),
    ResidualOccurrenceExpression.scale (-d.scalarParameters.q i * d.scalarParameters.q 2) (gramAtBase d C i 2)]

end CornerResidualBuilder

/-- Finite list defined before quantifying over any algebra, projection menu
or state. Repeated occurrences and all nine ordered Gram entries are retained. -/
def cornerResidualTelescopeOccurrences (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) : List (ResidualTelescopeOccurrence 4) :=
  ResidualOccurrenceExpression.combine
  [PurityVectorExpression.pairAgainst (CornerOperatorPolynomial.dataLeftVector d)
      (CornerResidualBuilder.dataAtBase d C),
    ResidualOccurrenceExpression.scale (-1)
      (PurityVectorExpression.pairAgainst (CornerOperatorPolynomial.volumeLeftVector d)
        (CornerResidualBuilder.volumeAtBase d C)),
    ResidualOccurrenceExpression.scale (-1) (CornerResidualBuilder.normAtBase d C),
    ResidualOccurrenceExpression.scale (-2 * d.scalarParameters.q 0) (CornerResidualBuilder.crossAtBase d C 0),
    ResidualOccurrenceExpression.scale (-2 * d.scalarParameters.q 1) (CornerResidualBuilder.crossAtBase d C 1),
    ResidualOccurrenceExpression.scale (-2 * d.scalarParameters.q 2) (CornerResidualBuilder.crossAtBase d C 2),
    CornerResidualBuilder.gramRowAtBase d C 0,
    CornerResidualBuilder.gramRowAtBase d C 1,
    CornerResidualBuilder.gramRowAtBase d C 2]

section Identity
open CornerResidualBuilder CornerHolonomy
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

theorem cornerResidualTelescope_linearIdentity (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)
    (P : Fin 4 → A) (hp : ∀ i, P i * P i = P i) (hstar : ∀ i, star (P i) = P i)
    (φ : A →ₗ[ℝ] ℝ) (hφ : ∀ x, φ (star x) = φ x) :
    d.scalarParameters.discriminant * φ (P 0) =
      ResidualOccurrenceExpression.value φ P (cornerResidualTelescopeOccurrences d C) := by
  let N := fun i => skewHermitianPart
    (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i)
  have he := scalarCliffordDefect_telescope φ hφ N (P 0) d.scalarParameters
  rw [realStarPairing_symmetric φ hφ (cliffordDataError N (P 0) d.scalarParameters),
    realStarPairing_symmetric φ hφ (cliffordVolumeError N (P 0) d.scalarParameters)] at he
  have hξ : realStarPairing φ (P 0) (P 0) = φ (P 0) := by
    simp only [realStarPairing, hstar 0, hp 0]
  rw [hξ] at he
  rw [he]
  simp only [cornerResidualTelescopeOccurrences, gramRowAtBase,
    ResidualOccurrenceExpression.value_combine, ResidualOccurrenceExpression.value_scale,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    ResidualOccurrenceExpression.value_pairAgainst φ P hstar,
    CornerOperatorPolynomial.dataLeftVector_value P hp hstar d,
    CornerOperatorPolynomial.volumeLeftVector_value P hp hstar d,
    dataAtBase_value P hp hstar d C hc, volumeAtBase_value P hp hstar d C hc,
    normAtBase_value φ P hp hstar d C hc, crossAtBase_value φ hφ P hp hstar d C hc,
    gramAtBase_value φ hφ P hp hstar d C hc, Fin.sum_univ_three]
  dsimp only [N]
  ring

/-- The exact algebraic-projective endpoint, including all zero histories. -/
theorem cornerResidualTelescope_identity (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)
    (M : AlgebraicProjectiveData (Fin 4) A) :
    d.scalarParameters.discriminant * M.probability [(0, true)] =
      ((cornerResidualTelescopeOccurrences d C).map (fun o => M.state
        (star (o.leftElement M.projection) * o.leaf.residualElement M.projection))).sum := by
  have hs : M.probability [(0, true)] = M.state (M.projection 0) := by
    simp only [AlgebraicProjectiveData.probability, wordOperator, wordAmplitude_singleton,
      algebraicOutcome, ite_true, M.selfAdjoint 0, M.idempotent 0]
  rw [hs]
  exact cornerResidualTelescope_linearIdentity d C hc M.projection M.idempotent
    M.selfAdjoint M.state M.state_star

end Identity

namespace CornerResidualBuilder
theorem gramRowAtBase_horizon (d : CornerNumericalData) (C : Fin 4 → Word (Fin 4) → ℝ) (i : Fin 3) :
    ResidualOccurrenceExpression.HasHorizon (gramRowAtBase d C i) 11 := by
  apply ResidualOccurrenceExpression.hasHorizon_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl
  all_goals exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (gramAtBase_horizon d C _ _)
end CornerResidualBuilder

/-- A structural upper bound for this constructor, not a prescribed word census
or a minimality assertion. No native or sharp-bound input is required. -/
theorem cornerResidualTelescope_horizon (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) :
    ∀ o ∈ cornerResidualTelescopeOccurrences d C, o.leaf.wordFunctional.HasHorizon 11 := by
  apply ResidualOccurrenceExpression.hasHorizon_combine
  intro es hes
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PurityVectorExpression.hasHorizon_pairAgainst _ _ _ (CornerResidualBuilder.dataAtBase_horizon d C)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _
      (PurityVectorExpression.hasHorizon_pairAgainst _ _ _ (CornerResidualBuilder.volumeAtBase_horizon d C))
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (CornerResidualBuilder.normAtBase_horizon d C)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (CornerResidualBuilder.crossAtBase_horizon d C 0)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (CornerResidualBuilder.crossAtBase_horizon d C 1)
  · exact ResidualOccurrenceExpression.hasHorizon_scale _ _ _ (CornerResidualBuilder.crossAtBase_horizon d C 2)
  · exact CornerResidualBuilder.gramRowAtBase_horizon d C 0
  · exact CornerResidualBuilder.gramRowAtBase_horizon d C 1
  · exact CornerResidualBuilder.gramRowAtBase_horizon d C 2

end AlbertSequential
