/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.CliffordGramFactor
public import Uniform.Main
public import MatchingModels.QuatPair
public import Mathlib.Algebra.Order.Star.Real

public section
noncomputable section

namespace AlbertSequential.LengthSeven.TableModel

open LemmaB AlbertSequential.MatchingModels

private def edgeScale (a b u : ℝ) : ℝ := Real.sqrt (a * u * b) / (a * b)

private theorem scale_diag (a b u r : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    edgeScale a b u * (1 - (r / Real.sqrt (a * u * b)) ^ 2) * edgeScale a b u =
      u * a⁻¹ * b⁻¹ - (r * a⁻¹ * b⁻¹)^2 := by
  have hpos : 0 < a * u * b := by positivity
  have hd : Real.sqrt (a * u * b) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  calc
    _ = ((Real.sqrt (a * u * b)) ^ 2 - r ^ 2) / (a * b)^2 := by
      unfold edgeScale
      field_simp
    _ = _ := by
      rw [Real.sq_sqrt hpos.le]
      field_simp

private theorem scale_offdiag (a b c u v r s w : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hu : 0 < u) (hv : 0 < v) :
    edgeScale a b u * (r / Real.sqrt (a * u * b) * (s / Real.sqrt (b * v * c)) -
      w / Real.sqrt (a * u * v * c)) * edgeScale b c v =
      (r * a⁻¹ * b⁻¹) * (s * b⁻¹ * c⁻¹) - w * (a⁻¹ * b⁻¹ * c⁻¹) := by
  let d₁ := Real.sqrt (a * u * b)
  let d₂ := Real.sqrt (b * v * c)
  let d₃ := Real.sqrt (a * u * v * c)
  have h₁ : 0 < d₁ := by dsimp [d₁]; positivity
  have h₂ : 0 < d₂ := by dsimp [d₂]; positivity
  have h₃ : 0 < d₃ := by dsimp [d₃]; positivity
  have hmul : d₁ * d₂ = b * d₃ := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    dsimp [d₁, d₂, d₃]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    ring
  change (d₁ / (a*b)) * (r/d₁ * (s/d₂) - w/d₃) * (d₂ / (b*c)) = _
  calc
    _ = (r*s - w*(d₁*d₂)/d₃) / ((a*b)*(b*c)) := by
      field_simp
    _ = _ := by
      rw [hmul]
      field_simp

private theorem scale_eq_paper (a b u : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    edgeScale a b u = Real.sqrt (u * a⁻¹ * b⁻¹) := by
  unfold edgeScale
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

@[expose] def nativeCliffordParams (q : Fin 4 → Albert) : Params ℝ :=
  (toTraces (nativeTraceData q)).toParams

def comparisonScale (q : Fin 4 → Albert) : Fin 3 → ℝ :=
  ![edgeScale (fpOverlap q 0 1) (fpOverlap q 0 2) (fpOverlap q 1 2),
    edgeScale (fpOverlap q 0 2) (fpOverlap q 0 3) (fpOverlap q 2 3),
    edgeScale (fpOverlap q 0 3) (fpOverlap q 0 1) (fpOverlap q 1 3)]

attribute [local irreducible] fourPointInvariant

theorem comparisonScale_eq_paper (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (hA : 0 < fourPointInvariant q) :
    comparisonScale q =
      ![Real.sqrt (fpOverlap q 1 2 * (fpOverlap q 0 1)⁻¹ * (fpOverlap q 0 2)⁻¹),
        Real.sqrt (fpOverlap q 2 3 * (fpOverlap q 0 2)⁻¹ * (fpOverlap q 0 3)⁻¹),
        Real.sqrt (fpOverlap q 1 3 * (fpOverlap q 0 3)⁻¹ * (fpOverlap q 0 1)⁻¹)] := by
  have h (i j : Fin 4) (hij : i ≠ j) : 0 < fpOverlap q i j :=
    (overlap_bounds_of_fourPoint_pos q hq hA i j hij).1
  funext i
  fin_cases i
  · exact scale_eq_paper _ _ _ (h 0 1 (by decide)) (h 0 2 (by decide)) (h 1 2 (by decide))
  · exact scale_eq_paper _ _ _ (h 0 2 (by decide)) (h 0 3 (by decide)) (h 2 3 (by decide))
  · exact scale_eq_paper _ _ _ (h 0 3 (by decide)) (h 0 1 (by decide)) (h 1 3 (by decide))

theorem comparisonMatrix_native_normalization (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (hA : 0 < fourPointInvariant q) :
    comparisonMatrix (nativeCliffordParams q) =
      Matrix.diagonal (comparisonScale q) * M_mat (fpOverlap q) (fpTriangle q) (tVec q) *
        Matrix.diagonal (comparisonScale q) := by
  have h (i j : Fin 4) (hij : i ≠ j) : 0 < fpOverlap q i j :=
    (overlap_bounds_of_fourPoint_pos q hq hA i j hij).1
  have hQ12 : tetraQOfTraces (tVec q) 0 1 2 3 = fpOmega2 q := by
    simp [tetraQOfTraces, tVec, unorderedPairClass, fpOmega2]
    ring
  have hQ23 : tetraQOfTraces (tVec q) 0 2 3 1 = fpOmega3 q := by
    simp [tetraQOfTraces, tVec, unorderedPairClass, fpOmega3]
  have hQ31 : tetraQOfTraces (tVec q) 0 3 1 2 = fpOmega1 q := by
    simp [tetraQOfTraces, tVec, unorderedPairClass, fpOmega1]
  have e0 := scale_diag _ _ _ (fpTriangle q 0 1 2) (h 0 1 (by decide))
    (h 0 2 (by decide)) (h 1 2 (by decide))
  have e1 := scale_diag _ _ _ (fpTriangle q 0 2 3) (h 0 2 (by decide))
    (h 0 3 (by decide)) (h 2 3 (by decide))
  have e2 := scale_diag _ _ _ (fpTriangle q 0 1 3) (h 0 3 (by decide))
    (h 0 1 (by decide)) (h 1 3 (by decide))
  have e01 := scale_offdiag _ _ _ _ _ (fpTriangle q 0 1 2) (fpTriangle q 0 2 3)
    (fpOmega2 q) (h 0 1 (by decide)) (h 0 2 (by decide)) (h 0 3 (by decide))
    (h 1 2 (by decide)) (h 2 3 (by decide))
  have e12 := scale_offdiag _ _ _ _ _ (fpTriangle q 0 2 3) (fpTriangle q 0 1 3)
    (fpOmega3 q) (h 0 2 (by decide)) (h 0 3 (by decide)) (h 0 1 (by decide))
    (h 2 3 (by decide)) (h 1 3 (by decide))
  have e20 := scale_offdiag _ _ _ _ _ (fpTriangle q 0 1 3) (fpTriangle q 0 1 2)
    (fpOmega1 q) (h 0 3 (by decide)) (h 0 1 (by decide)) (h 0 2 (by decide))
    (h 1 3 (by decide)) (h 1 2 (by decide))
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp only [nativeCliffordParams, toParams_toTraces, LemmaB.TableModel.paramsN, comparisonMatrix,
      comparisonScale, nativeTraceData, M_mat, tetraC1, tetraC2, tetraC3, tetraK12, tetraK23, tetraK31,
      hQ12, hQ23, hQ31, fpOverlap_symm q 2 0, fpOverlap_symm q 3 0, fpOverlap_symm q 1 0,
      fpOverlap_symm q 3 1, fpTriangle_swap23 q 0 3 1, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  all_goals first
    | exact e0.symm
    | exact e1.symm
    | exact e2.symm
    | linear_combination e01.symm
    | linear_combination e12.symm
    | linear_combination e20.symm

theorem comparison_Dhat_native (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (hA : 0 < fourPointInvariant q) :
    0 < (nativeCliffordParams q).Dhat := by
  have h (i : Fin 4) (hi : 0 ≠ i) : 0 < fpOverlap q 0 i :=
    (overlap_bounds_of_fourPoint_pos q hq hA 0 i hi).1
  unfold nativeCliffordParams
  rw [Traces.Dhat_toParams _ (h 1 (by decide)).ne' (h 2 (by decide)).ne' (h 3 (by decide)).ne',
    Uniform.native_Acal]
  change 0 < (((fpOverlap q 0 1)⁻¹ * (fpOverlap q 0 2)⁻¹ *
    (fpOverlap q 0 3)⁻¹)^3 * fourPointInvariant q)
  have h₁ := h 1 (by decide)
  have h₂ := h 2 (by decide)
  have h₃ := h 3 (by decide)
  positivity

theorem comparisonMatrix_native_posDef (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (hA : 0 < fourPointInvariant q) :
    (comparisonMatrix (nativeCliffordParams q)).PosDef := by
  have hM := M_mat_posSemidef_of_atoms q hq hA
  have hσ : (Matrix.diagonal (comparisonScale q)).conjTranspose =
      Matrix.diagonal (comparisonScale q) := by simp
  have hP : (comparisonMatrix (nativeCliffordParams q)).PosSemidef := by
    rw [comparisonMatrix_native_normalization q hq hA]
    simpa only [hσ, Matrix.mul_assoc] using hM.conjTranspose_mul_mul_same
      (Matrix.diagonal (comparisonScale q))
  apply hP.posDef_iff_det_ne_zero.mpr
  rw [comparisonMatrix_det]
  have hD := comparison_Dhat_native q hq hA
  rw [Params.Dhat] at hD
  have hdet : 0 < (nativeCliffordParams q).detM := by
    nlinarith [sq_nonneg (nativeCliffordParams q).b]
  exact hdet.ne'

theorem native_comparison_gram_factor (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (hA : 0 < fourPointInvariant q) :
    ∃ Λ : Matrix (Fin 3) (Fin 3) ℝ,
      comparisonMatrix (nativeCliffordParams q) = Λ * Λ.transpose ∧ IsUnit Λ.det :=
  comparisonMatrix_factor _ (comparisonMatrix_native_posDef q hq hA).posSemidef
    (comparison_Dhat_native q hq hA)

end AlbertSequential.LengthSeven.TableModel
