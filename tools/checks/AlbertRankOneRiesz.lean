module

import WindowProbabilityAlbertRieszHomogeneity

open AlbertSequential AlbertSequential.WindowProbability
open MeasureTheory Real Set
open scoped AlbertSequential.WindowProbability ENNReal

noncomputable section

example : SigmaFinite albertRankOneRiesz := inferInstance

example : IsFiniteMeasureOnCompacts albertRankOneRiesz := inferInstance

example : closure (interior {X : Albert | IsPositive X}) = {X : Albert | IsPositive X} :=
  closure_albertOpenPositiveCone

example : ∀ᵐ X ∂albertRankOneRiesz, ∃ t : ℝ, 0 < t ∧ ∃ p : Albert, IsAtom p ∧ X = t • p :=
  ae_albertRankOneRiesz_rankOne

example {Y : Albert} (hY : Y ∈ interior {X : Albert | IsPositive X}) :
    (∫ X in closure (interior {X : Albert | IsPositive X}),
      exp (-(tracePairing Y X)) ∂albertRankOneRiesz) = ((albertCubicNorm Y)^4)⁻¹ := by
  change (∫ X in closure albertOpenPositiveCone, exp (-(tracePairing Y X)) ∂albertRankOneRiesz) = _
  rw [Measure.restrict_eq_self_of_ae_mem ae_albertRankOneRiesz_mem_closedCone]
  exact (albertRankOneRiesz_laplace hY).2

example : albertRankOneRiesz.withDensity (fun X => ENNReal.ofReal (exp (-albertTrace X))) =
    albertChartRayMeasure :=
  albertRankOneRiesz_traceTilt

example (g : NativeAlbertAutomorphism) :
    albertRankOneRiesz.map g.linearEquiv = albertRankOneRiesz :=
  map_nativeAutomorphism_albertRankOneRiesz g

example {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ 12) • (albertRankOneRiesz.map (fun X => r • X)) = albertRankOneRiesz :=
  albertRankOneRiesz_smul_map hr

#print axioms albertStrictPositive_iff_atoms
#print axioms albertStrictPositive_mem_openCone
#print axioms closure_albertOpenPositiveCone
#print axioms albertRankOneRiesz_traceTilt
#print axioms ae_albertRankOneRiesz_rankOne
#print axioms ae_albertRankOneRiesz_mem_closedCone
#print axioms albertRankOneRiesz_laplace
#print axioms map_nativeAutomorphism_albertRankOneRiesz
#print axioms eq_albertRankOneRiesz_of_laplace
#print axioms albertRankOneRiesz_smul_map
