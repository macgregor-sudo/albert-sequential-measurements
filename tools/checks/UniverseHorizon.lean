module

import Bridge.UniverseHorizon
import Bridge.Least

open AlbertSequential AlbertSequential.MatchingModels AlbertSequential.FiveTest
open AlbertChallenge (ProjectiveRepresentation)

universe carrier

attribute [local irreducible] fourPointInvariant

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    classIMinimum.{carrier} (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) = 7 ∧
      classIMinimum.{carrier} (nativeWordProbability p (p 0)) = 6 :=
  ⟨classI_minimum_e3.{carrier} p hp hA, classI_minimum_pA.{carrier} p hp hA⟩

example : classIMinimum.{2} (nativeWordProbability pentadF (pentadF 0)) = 10 ∧
    classIMinimum.{2} (nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit)) = 11 :=
  ⟨classI_minimum_F_p0, classI_minimum_F_e3⟩

example : classIMinimum.{1} (nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit)) = 7 ∧
    classIMinimum.{1} (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) = 7 :=
  classI_minimum_MS

example : ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (ULift.{2} (Fin 12))),
    (∀ w : Word (Fin 4), M.probability w =
      (horizonC12Model (Real.sqrt 2) (Real.sqrt 2)⁻¹ horizon_sign_square).probability w) ∧
    (∀ w : Word (Fin 4), w.length ≤ 6 →
      M.probability w = nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w) := by
  obtain ⟨M, hM⟩ := exists_liftedFiniteComplexModel.{2}
    (horizonC12Model (Real.sqrt 2) (Real.sqrt 2)⁻¹ horizon_sign_square)
  exact ⟨M, hM, fun w hw => (hM w).trans (horizon_M_matrix w hw)⟩

example : ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (ULift.{1} (Fin 12))),
    (∀ w : Word (Fin 4), M.probability w =
      (horizonC12Model 1 (Real.sqrt 2)⁻¹ horizon_sign_square).probability w) ∧
    (∀ w : Word (Fin 4), w.length ≤ 6 →
      M.probability w = nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w) := by
  obtain ⟨M, hM⟩ := exists_liftedFiniteComplexModel.{1}
    (horizonC12Model 1 (Real.sqrt 2)⁻¹ horizon_sign_square)
  exact ⟨M, hM, fun w hw => (hM w).trans (horizon_S_matrix w hw)⟩

example (p : Fin 4 → AlbertChallenge.Albert) (hp : ∀ i, AlbertChallenge.IsAtom (p i))
    (hg : AlbertChallenge.Generates p) :
    IsLeast {L : ℕ | ClassISeparatesAt.{0} (AlbertChallenge.wordProbability p AlbertChallenge.maximallyMixed) L} 7 :=
  AlbertChallenge.Bridge.least_separating_bridge p hp hg

example (p : Fin 4 → AlbertChallenge.Albert) (hp : ∀ i, AlbertChallenge.IsAtom (p i))
    (hg : AlbertChallenge.Generates p) :
    IsLeast {L : ℕ | ClassISeparatesAt.{carrier} (AlbertChallenge.wordProbability p AlbertChallenge.maximallyMixed) L} 7 :=
  AlbertChallenge.Bridge.least_separating_length_all_universes p hp hg

#print axioms AlbertChallenge.Bridge.exists_liftFiniteProjectiveRepresentation
#print axioms AlbertChallenge.Bridge.hasClassIModel_of_finite
#print axioms AlbertChallenge.Bridge.least_separating_length_all_universes
#print axioms classI_minimum_e3
#print axioms classI_pA_five_step_model
#print axioms classI_minimum_pA
#print axioms classI_minimum_MS
#print axioms classI_minimum_F_p0
#print axioms classI_minimum_F_e3
