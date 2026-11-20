/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.CliffordCoordinates
import LocalVolume
import Mathlib.Tactic.Module

public section
noncomputable section

namespace LemmaB

open scoped BigOperators

variable (p : Params ℝ)

theorem cliffordGenerator_anticommutator (i j : Fin 3) :
    cliffordGenerator p i * cliffordGenerator p j + cliffordGenerator p j * cliffordGenerator p i =
      (-2 * comparisonMatrix p i j) • (1 : ComparisonClifford p) := by
  unfold cliffordGenerator
  rw [CliffordAlgebra.ι_mul_ι_add_swap, Algebra.algebraMap_eq_smul_one]
  have hsym : comparisonMatrix p j i = comparisonMatrix p i j := by
    fin_cases i <;> fin_cases j <;> rfl
  have hB (a b : Fin 3) : Matrix.toLinearMap₂' ℝ (S₁ := ℝ) (S₂ := ℝ) (comparisonMatrix p)
      (Pi.single a 1) (Pi.single b 1) = comparisonMatrix p a b := by
    rw [Matrix.toLinearMap₂'_apply', Matrix.mulVec_single_one, single_dotProduct, one_mul]
    rfl
  congr 1
  simp [QuadraticMap.polar, comparisonQuadratic, LinearMap.BilinMap.toQuadraticMap_apply,
    map_add, LinearMap.add_apply, hB, hsym]
  ring

theorem cliffordVolume_eq_half_reverse :
    cliffordVolume p = (1 / 2 : ℝ) •
      (cliffordGenerator p 0 * cliffordGenerator p 1 * cliffordGenerator p 2 -
        cliffordGenerator p 2 * cliffordGenerator p 1 * cliffordGenerator p 0) := by
  have h01 := cliffordGenerator_anticommutator p 0 1
  have h02 := cliffordGenerator_anticommutator p 0 2
  have h12 := cliffordGenerator_anticommutator p 1 2
  change _ = (-2 * p.M12) • (1 : ComparisonClifford p) at h01
  change _ = (-2 * p.M13) • (1 : ComparisonClifford p) at h02
  change _ = (-2 * p.M23) • (1 : ComparisonClifford p) at h12
  rw [neg_mul] at h01 h02 h12
  have h := AlbertSequential.localUnit_volume_eq_half_reverse
    (1 : ComparisonClifford p) (cliffordGenerator p 0) (cliffordGenerator p 1) (cliffordGenerator p 2)
    (-p.M12) (-p.M13) (-p.M23) (one_mul _) (mul_one _) (one_mul _)
    (by rw [mul_neg]; exact h01) (by rw [mul_neg]; exact h02) (by rw [mul_neg]; exact h12)
  rw [← h]
  simp only [cliffordVolume, mul_assoc, neg_smul]
  module

theorem cliffordCoordinates_volume_mul (a : ComparisonClifford p) :
    cliffordCoordinates p (cliffordVolume p * a) = Gam p (cliffordCoordinates p a) := by
  simp [cliffordVolume, add_mul, sub_mul, mul_assoc, Gam,
    cliffordCoordinates_generator_mul]

theorem cliffordVolume_square :
    cliffordVolume p * cliffordVolume p = p.detM • (1 : ComparisonClifford p) := by
  apply (cliffordCoordinateEquiv p).injective
  have h := cliffordCoordinates_volume_mul p 1
  rw [mul_one, cliffordCoordinates_one] at h
  simp only [cliffordCoordinateEquiv_apply, cliffordCoordinates_volume_mul, map_smul,
    cliffordCoordinates_one]
  rw [h, Gam_sq]

theorem cliffordVolume_commutes_generator (i : Fin 3) :
    Commute (cliffordVolume p) (cliffordGenerator p i) := by
  change cliffordVolume p * cliffordGenerator p i = cliffordGenerator p i * cliffordVolume p
  apply (cliffordCoordinateEquiv p).injective
  have he := cliffordCoordinates_generator_mul p i 1
  have hv := cliffordCoordinates_volume_mul p 1
  rw [mul_one, cliffordCoordinates_one] at he hv
  rw [cliffordCoordinateEquiv_apply, cliffordCoordinateEquiv_apply, cliffordCoordinates_volume_mul,
    cliffordCoordinates_generator_mul, he, hv]
  fin_cases i <;> simp [Gam_comm1, Gam_comm2, Gam_comm3]

theorem cliffordVolume_central (a : ComparisonClifford p) : Commute (cliffordVolume p) a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r _).symm
  | ι v =>
    have hvec : (∑ i, v i • Pi.single i (1 : ℝ)) = v := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
    have he : CliffordAlgebra.ι (comparisonQuadratic p) v = ∑ i, v i • cliffordGenerator p i := by
      conv_lhs => rw [← hvec]
      rw [map_sum]
      simp only [map_smul, cliffordGenerator]
    rw [he]
    change cliffordVolume p * (∑ i, v i • cliffordGenerator p i) =
      (∑ i, v i • cliffordGenerator p i) * cliffordVolume p
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (fun z : ComparisonClifford p => v i • z)
        (cliffordVolume_commutes_generator p i).eq
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

theorem cliffordConjugate_volume : cliffordConjugate p (cliffordVolume p) = cliffordVolume p := by
  rw [cliffordVolume_eq_half_reverse]
  simp only [map_smul, map_sub, cliffordConjugate_mul, cliffordConjugate_generator,
    neg_mul, mul_neg, mul_assoc]
  module

theorem cliffordPairing_ghost (a : ComparisonClifford p) :
    cliffordPairing p a (cliffordGhost p) = p.Dhat * cliffordCoordinates p a 7 := by
  rw [cliffordPairing_eq_W, cliffordCoordinates_ghost]
  have he : Pi.single (7 : Fin 8) (1 : ℝ) = (gee : C8 ℝ) := by
    funext i; fin_cases i <;> simp [gee]
  rw [he, W_gee]

end LemmaB
