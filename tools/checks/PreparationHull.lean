module

import Robustness.PreparationCoordinates
import Robustness.PreparationHullDensity

open AlbertSequential AlbertSequential.SharpDisturbance AlbertSequential.PreparationHull
open AlbertSequential.HilbertTrace

example {E I : Type*} [AddCommGroup E] [Module ℝ E]
    (p : I → Albert) (tr : E →ₗ[ℝ] ℝ) (F : Outcome I → E →ₗ[ℝ] E) (initial : E)
    (hmatch : ∀ w, tr (wordMap F w initial) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (v : Word I) (hv : 0 < tr (wordMap F v initial)) :
    ∃ ρ ∈ nativeReachableStates p, ∀ u,
      tr (wordMap F u ((tr (wordMap F v initial))⁻¹ • wordMap F v initial)) =
        nativeWordProbability p ρ u :=
  prepared_native_table p tr F initial hmatch ⟨v, hv, rfl⟩

section Real

variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

example (b : HilbertBasis B ℝ H) (M : Fin 4 → RealInstrument b)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : signedFiniteTrace b) (hd : IsRealDensity b initial)
    (hmatch : ∀ w, signedTrace b (wordMap (realBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ y ∈ convexHull ℝ (preparedStates (signedTrace b) (realBranch b M) initial),
      realTraceNorm b (y - z) < ε) :
    IsRealDensity b z ∧
    (∃ ρ ∈ nativeReachableStateSpace p, ∀ w,
      signedTrace b (wordMap (realBranch b M) w z) = nativeWordProbability p ρ w) ∧
    ∀ q, signedTrace b (realBranch b M q z) = 1 → ∀ u,
      signedTrace b (wordMap (realBranch b M) (q :: u) z) = signedTrace b (wordMap (realBranch b M) u z) :=
  ⟨real_preparationHull_density b M p initial z hd hmatch hlim,
    real_native_table_of_preparationHull b M p initial z hmatch hlim,
    fun q hq u => real_preparationHull_certainty b M p hp initial z hmatch hlim q hq u⟩

end Real

section Complex

variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (b : HilbertBasis B ℂ H) (M : Fin 4 → ComplexInstrument b)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : signedFiniteTrace b) (hd : IsComplexDensity b initial)
    (hmatch : ∀ w, signedTrace b (wordMap (complexBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ y ∈ convexHull ℝ (preparedStates (signedTrace b) (complexBranch b M) initial),
      complexTraceNorm b (y - z) < ε) :
    IsComplexDensity b z ∧
    (∃ ρ ∈ nativeReachableStateSpace p, ∀ w,
      signedTrace b (wordMap (complexBranch b M) w z) = nativeWordProbability p ρ w) ∧
    ∀ q, signedTrace b (complexBranch b M q z) = 1 → ∀ u,
      signedTrace b (wordMap (complexBranch b M) (q :: u) z) = signedTrace b (wordMap (complexBranch b M) u z) :=
  ⟨complex_preparationHull_density b M p initial z hd hmatch hlim,
    complex_native_table_of_preparationHull b M p initial z hmatch hlim,
    fun q hq u => complex_preparationHull_certainty b M p hp initial z hmatch hlim q hq u⟩

end Complex

section Quaternionic

variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

example (b : HilbertBasis B ℝ H) (S : RightQuaternionicHilbertStructure H) (M : Fin 4 → QuaternionicInstrument b S)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : quaternionicSignedFiniteTrace b S) (hd : IsQuaternionicDensity b S initial)
    (hmatch : ∀ w, quaternionicSignedTrace b S (wordMap (quaternionicBranch b S M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ y ∈ convexHull ℝ
        (preparedStates (quaternionicSignedTrace b S) (quaternionicBranch b S M) initial),
      quaternionicTraceNorm b S (y - z) < ε) :
    IsQuaternionicDensity b S z ∧
    (∃ ρ ∈ nativeReachableStateSpace p, ∀ w,
      quaternionicSignedTrace b S (wordMap (quaternionicBranch b S M) w z) = nativeWordProbability p ρ w) ∧
    ∀ q, quaternionicSignedTrace b S (quaternionicBranch b S M q z) = 1 → ∀ u,
      quaternionicSignedTrace b S (wordMap (quaternionicBranch b S M) (q :: u) z) =
        quaternionicSignedTrace b S (wordMap (quaternionicBranch b S M) u z) :=
  ⟨quaternionic_preparationHull_density b S M p initial z hd hmatch hlim,
    quaternionic_native_table_of_preparationHull b S M p initial z hmatch hlim,
    fun q hq u => quaternionic_preparationHull_certainty b S M p hp initial z hmatch hlim q hq u⟩

end Quaternionic

#print axioms initial_mem_preparedStates
#print axioms prepared_native_table
#print axioms traceNormPreparationHull_eq_closure
#print axioms native_table_of_mem_traceNormPreparationHull
#print axioms exists_native_word_coordinates_of_positive_invariant
#print axioms native_representative_tendsto_of_traceNorm
#print axioms real_word_readout_lipschitz
#print axioms complex_word_readout_lipschitz
#print axioms quaternionic_word_readout_lipschitz
#print axioms real_preparationHull_density
#print axioms complex_preparationHull_density
#print axioms quaternionic_preparationHull_density
#print axioms real_certain_disturbed_not_mem_preparationHull
#print axioms complex_certain_disturbed_not_mem_preparationHull
#print axioms quaternionic_certain_disturbed_not_mem_preparationHull
