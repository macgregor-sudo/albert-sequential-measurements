/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceBasis
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! Positive trace and positive trace-class decompositions on a complex Hilbert space. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι κ : Type*}

theorem exists_selfAdjoint_factor {T : H →L[ℂ] H} (hT : T.IsPositive) :
    ∃ A : H →L[ℂ] H, IsSelfAdjoint A ∧
      ContinuousLinearMap.adjoint A ∘L A = T ∧ A ∘L ContinuousLinearMap.adjoint A = T := by
  obtain ⟨A, hA, _, hSq⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hT.isSelfAdjoint hT.spectrumRestricts
  refine ⟨A, hA, ?_, ?_⟩
  · change star A * A = T
    rw [hA.star_eq, hSq]
  · change A * star A = T
    rw [hA.star_eq, hSq]

/-- Every bounded positive operator has the same extended trace in every Hilbert basis. -/
theorem positiveTrace_basis_independent (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    {T : H →L[ℂ] H} (hT : T.IsPositive) : positiveTrace b T = positiveTrace c T := by
  obtain ⟨A, _, hA, _⟩ := exists_selfAdjoint_factor hT
  rw [← hA, positiveTrace_adjoint_comp_self, positiveTrace_adjoint_comp_self]
  exact hilbertSchmidtMassSq_basis_independent b c A

/-- A positive operator of finite trace admits an absolute sum of positive rank-one dyads. -/
theorem positiveTrace_hasSum_rankOne (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hT : T.IsPositive) (hfin : positiveTrace b T ≠ ∞) :
    ∃ u : ι → H, Summable (fun i => ‖u i‖ ^ 2) ∧
      HasSum (fun i => InnerProductSpace.rankOne ℂ (u i) (u i)) T := by
  obtain ⟨A, _, hleft, hright⟩ := exists_selfAdjoint_factor hT
  rw [← hleft, positiveTrace_adjoint_comp_self] at hfin
  refine ⟨fun i => A (b i), ?_, hright ▸ hasSum_rankOne_of_hilbertSchmidt b A hfin⟩
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using (ENNReal.summable_toReal hfin)

end AlbertSequential.HilbertTrace
