/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.CliffordVolumeCoordinates
public import TableModel.CliffordGramFactor
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.Module

public section
noncomputable section

namespace LemmaB

open scoped BigOperators

local notation "γ" => standardComparisonGenerator
local notation "ιs" => CliffordAlgebra.ι standardComparisonQuadratic

private def halfReverse (x y z : Fin 3 → ℝ) : StandardComparisonClifford :=
  (1 / 2 : ℝ) • (ιs x * ιs y * ιs z - ιs z * ιs y * ιs x)

private theorem halfReverse_repeated (x y z : Fin 3 → ℝ)
    (h : x = y ∨ x = z ∨ y = z) : halfReverse x y z = 0 := by
  rcases h with rfl | rfl | rfl
  · have he : ιs x * ιs x * ιs z = ιs z * ιs x * ιs x := by
      rw [mul_assoc (ιs z) (ιs x) (ιs x), CliffordAlgebra.ι_sq_scalar]
      exact Algebra.commutes _ _
    unfold halfReverse
    rw [he, sub_self, smul_zero]
  · simp [halfReverse]
  · have he : ιs x * ιs y * ιs y = ιs y * ιs y * ιs x := by
      rw [mul_assoc (ιs x) (ιs y) (ιs y), CliffordAlgebra.ι_sq_scalar]
      exact (Algebra.commutes _ _).symm
    unfold halfReverse
    rw [he, sub_self, smul_zero]

private theorem fin03_ne : (0 : Fin 3) ≠ 1 := by decide
private theorem fin02_ne : (0 : Fin 3) ≠ 2 := by decide
private theorem fin12_ne : (1 : Fin 3) ≠ 2 := by decide

private def standardVolumeMap : (Fin 3 → ℝ) [⋀^Fin 3]→ₗ[ℝ] StandardComparisonClifford where
  toFun v := halfReverse (v 0) (v 1) (v 2)
  map_update_add' v i x y := by
    fin_cases i <;> simp only [halfReverse, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Function.update_self, Function.update_of_ne fin03_ne, Function.update_of_ne fin03_ne.symm,
      Function.update_of_ne fin02_ne, Function.update_of_ne fin02_ne.symm,
      Function.update_of_ne fin12_ne, Function.update_of_ne fin12_ne.symm,
      map_add, add_mul, mul_add] <;> module
  map_update_smul' v i c x := by
    fin_cases i <;> simp only [halfReverse, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Function.update_self, Function.update_of_ne fin03_ne, Function.update_of_ne fin03_ne.symm,
      Function.update_of_ne fin02_ne, Function.update_of_ne fin02_ne.symm,
      Function.update_of_ne fin12_ne, Function.update_of_ne fin12_ne.symm,
      map_smul, RingHom.id_apply, smul_mul_assoc, mul_smul_comm] <;> module
  map_eq_zero_of_eq' := by
    intro v i j h hij
    apply halfReverse_repeated
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | exact Or.inl h
      | exact Or.inl h.symm
      | exact Or.inr (Or.inl h)
      | exact Or.inr (Or.inl h.symm)
      | exact Or.inr (Or.inr h)
      | exact Or.inr (Or.inr h.symm)

private theorem reverse_standard_triple : γ 2 * γ 1 * γ 0 = -(γ 0 * γ 1 * γ 2) := by
  rw [standardComparisonGenerator_anti (by decide : (2 : Fin 3) ≠ 1), neg_mul]
  rw [mul_assoc (γ 1) (γ 2) (γ 0),
    standardComparisonGenerator_anti (by decide : (2 : Fin 3) ≠ 0), mul_neg, neg_neg, ← mul_assoc]
  rw [standardComparisonGenerator_anti (by decide : (1 : Fin 3) ≠ 0), neg_mul]

private theorem standardVolume_on_basis :
    standardVolumeMap (Pi.basisFun ℝ (Fin 3)) = γ 0 * γ 1 * γ 2 := by
  change halfReverse ((Pi.basisFun ℝ (Fin 3)) 0) ((Pi.basisFun ℝ (Fin 3)) 1)
    ((Pi.basisFun ℝ (Fin 3)) 2) = _
  simp only [Pi.basisFun_apply, halfReverse]
  change (1 / 2 : ℝ) • (γ 0 * γ 1 * γ 2 - γ 2 * γ 1 * γ 0) = _
  rw [reverse_standard_triple]
  module

private theorem standardVolumeMap_eq_det :
    standardVolumeMap =
      (Pi.basisFun ℝ (Fin 3)).det.smulRight (γ 0 * γ 1 * γ 2) := by
  let e := Pi.basisFun ℝ (Fin 3)
  apply e.ext_alternating
  intro v hv
  let σ := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
  change standardVolumeMap (e ∘ σ) = (e.det.smulRight (γ 0 * γ 1 * γ 2)) (e ∘ σ)
  rw [AlternatingMap.map_perm, AlternatingMap.map_perm, AlternatingMap.smulRight_apply,
    Module.Basis.det_self, one_smul]
  rw [show standardVolumeMap e = γ 0 * γ 1 * γ 2 from standardVolume_on_basis]

theorem cliffordGramFactorEquiv_volume (p : Params ℝ) (Λ : Matrix (Fin 3) (Fin 3) ℝ)
    (hΛ : comparisonMatrix p = Λ * Λ.transpose) (hd : IsUnit Λ.det) :
    cliffordGramFactorEquiv p Λ hΛ hd (cliffordVolume p) =
      Λ.det • (γ 0 * γ 1 * γ 2) := by
  have hgen (i : Fin 3) :
      cliffordGramFactorEquiv p Λ hΛ hd (cliffordGenerator p i) = ιs (Λ i) := by
    have hrow : (∑ j, Λ i j • (Pi.single j (1 : ℝ))) = Λ i := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
    rw [cliffordGramFactorEquiv_generator]
    conv_rhs => rw [← hrow]
    rw [map_sum]
    simp only [map_smul, standardComparisonGenerator]
  rw [cliffordVolume_eq_half_reverse]
  simp only [map_smul, map_sub, map_mul, hgen]
  change standardVolumeMap (fun i j => Λ i j) = _
  rw [standardVolumeMap_eq_det, AlternatingMap.smulRight_apply, Module.Basis.det_apply]
  have hmat : (Pi.basisFun ℝ (Fin 3)).toMatrix (fun i j => Λ i j) = Λ.transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.transpose_apply]
  rw [hmat, Matrix.det_transpose]

end LemmaB
