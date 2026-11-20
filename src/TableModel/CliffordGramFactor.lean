/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.CliffordCoordinates
public import GramFactor
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

public section
noncomputable section

namespace LemmaB

open scoped BigOperators

def standardComparisonQuadratic : QuadraticForm ℝ (Fin 3 → ℝ) :=
  -LinearMap.BilinMap.toQuadraticMap
    (Matrix.toLinearMap₂' ℝ (S₁ := ℝ) (S₂ := ℝ) (1 : Matrix (Fin 3) (Fin 3) ℝ))

abbrev StandardComparisonClifford := CliffordAlgebra standardComparisonQuadratic

@[expose] def standardComparisonGenerator (i : Fin 3) : StandardComparisonClifford :=
  CliffordAlgebra.ι standardComparisonQuadratic (Pi.single i 1)

private theorem standardBilinear_single (i j : Fin 3) :
    Matrix.toLinearMap₂' ℝ (S₁ := ℝ) (S₂ := ℝ) (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0 := by
  rw [Matrix.toLinearMap₂'_apply', Matrix.one_mulVec, single_dotProduct, one_mul]
  simp [Pi.single_apply]

theorem standardComparisonGenerator_sq (i : Fin 3) :
    standardComparisonGenerator i * standardComparisonGenerator i = -1 := by
  unfold standardComparisonGenerator
  rw [CliffordAlgebra.ι_sq_scalar]
  simp only [standardComparisonQuadratic, neg_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    standardBilinear_single]
  exact (map_neg (algebraMap ℝ StandardComparisonClifford) (1 : ℝ)).trans
    (congrArg Neg.neg (map_one (algebraMap ℝ StandardComparisonClifford)))

theorem standardComparisonGenerator_anti {i j : Fin 3} (hij : i ≠ j) :
    standardComparisonGenerator i * standardComparisonGenerator j =
      -(standardComparisonGenerator j * standardComparisonGenerator i) := by
  unfold standardComparisonGenerator
  apply CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
  rw [QuadraticMap.isOrtho_def]
  simp [standardComparisonQuadratic, LinearMap.BilinMap.toQuadraticMap_apply, map_add,
    LinearMap.add_apply, standardBilinear_single, hij, Ne.symm hij]

theorem comparisonMatrix_det (p : Params ℝ) : (comparisonMatrix p).det = p.detM := by
  rw [Matrix.det_fin_three]
  simp [comparisonMatrix, Params.detM]
  ring

theorem comparisonMatrix_factor (p : Params ℝ) (hM : (comparisonMatrix p).PosSemidef)
    (hD : 0 < p.Dhat) :
    ∃ Λ : Matrix (Fin 3) (Fin 3) ℝ, comparisonMatrix p = Λ * Λ.transpose ∧ IsUnit Λ.det := by
  obtain ⟨B, hB⟩ := AlbertSequential.exists_realGramFactor hM
  have hMdet : IsUnit (comparisonMatrix p).det := by
    rw [comparisonMatrix_det]
    have h : 0 < p.detM := by
      rw [Params.Dhat] at hD
      nlinarith [sq_nonneg p.b]
    exact isUnit_iff_ne_zero.mpr h.ne'
  refine ⟨B.transpose, by simpa using hB, ?_⟩
  rw [hB, Matrix.det_mul] at hMdet
  exact isUnit_of_mul_isUnit_left hMdet

private def factorIsometry (p : Params ℝ) (Λ : Matrix (Fin 3) (Fin 3) ℝ)
    (hΛ : comparisonMatrix p = Λ * Λ.transpose) (hd : IsUnit Λ.det) :
    (comparisonQuadratic p).IsometryEquiv standardComparisonQuadratic where
  toLinearEquiv := Λ.transpose.toLinearEquiv' (Λ.transpose.invertibleOfIsUnitDet
    (Matrix.isUnit_det_transpose Λ hd))
  map_app' x := by
    change standardComparisonQuadratic (Matrix.toLin' Λ.transpose x) = comparisonQuadratic p x
    have h := LinearMap.congr_fun₂
      (Matrix.toLinearMap₂'_comp (1 : Matrix (Fin 3) (Fin 3) ℝ) Λ.transpose Λ.transpose) x x
    simpa only [standardComparisonQuadratic, comparisonQuadratic, neg_apply,
      LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₁₂_apply,
      Matrix.transpose_transpose, mul_one, ← hΛ] using
      congrArg Neg.neg h

def cliffordGramFactorEquiv (p : Params ℝ) (Λ : Matrix (Fin 3) (Fin 3) ℝ)
    (hΛ : comparisonMatrix p = Λ * Λ.transpose) (hd : IsUnit Λ.det) :
    ComparisonClifford p ≃ₐ[ℝ] StandardComparisonClifford :=
  CliffordAlgebra.equivOfIsometry (factorIsometry p Λ hΛ hd)

theorem cliffordGramFactorEquiv_generator (p : Params ℝ) (Λ : Matrix (Fin 3) (Fin 3) ℝ)
    (hΛ : comparisonMatrix p = Λ * Λ.transpose) (hd : IsUnit Λ.det) (i : Fin 3) :
    cliffordGramFactorEquiv p Λ hΛ hd (cliffordGenerator p i) =
      ∑ j, Λ i j • standardComparisonGenerator j := by
  unfold cliffordGramFactorEquiv
  change CliffordAlgebra.map (factorIsometry p Λ hΛ hd).toIsometry
      (CliffordAlgebra.ι (comparisonQuadratic p) (Pi.single i 1)) = _
  rw [CliffordAlgebra.map_apply_ι]
  have hvec : factorIsometry p Λ hΛ hd (Pi.single i 1) = ∑ j, Λ i j • Pi.single j 1 := by
    change Matrix.toLin' Λ.transpose (Pi.single i 1) = _
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    funext k
    simp [Matrix.col, Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  change CliffordAlgebra.ι standardComparisonQuadratic
    (factorIsometry p Λ hΛ hd (Pi.single i 1)) = _
  rw [hvec, map_sum]
  simp only [map_smul, standardComparisonGenerator]

end LemmaB
