/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CyclicCornerSevenObstruction
public import ScheduleMatchingSectorMatrices

@[expose] public section
noncomputable section

open scoped Matrix ComplexOrder

namespace AlbertSequential.LengthSeven

open MatchingModels

/-- The displayed C12 projection matrices with the literal normalized matrix trace. -/
def horizonC12AlgebraicTraceModel (b d : ℝ) (hd : d ^ 2 = 1 / 2) :
    AlgebraicProjectiveData (Fin 4) (Matrix (Fin 12) (Fin 12) ℂ) where
  projection := horizonC12Projection b d
  idempotent := horizonC12Projection_idempotent b d hd
  selfAdjoint := fun i => (horizonC12Projection_hermitian b d i).eq
  state := (1 / 12 : ℝ) • (Complex.reCLM.toLinearMap.comp (Matrix.traceLinearMap (Fin 12) ℝ ℂ))
  state_unit := by
    change (1 / 12 : ℝ) * (Matrix.trace (1 : Matrix (Fin 12) (Fin 12) ℂ)).re = 1
    norm_num
  state_star X := by
    change (1 / 12 : ℝ) * (Matrix.trace (star X)).re = (1 / 12 : ℝ) * (Matrix.trace X).re
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
  state_positive X := by
    change 0 ≤ (1 / 12 : ℝ) * (Matrix.trace (star X * X)).re
    apply mul_nonneg (by norm_num)
    rw [Matrix.star_eq_conjTranspose]
    exact (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

theorem horizonC12AlgebraicTraceModel_probability (b d : ℝ) (hd : d ^ 2 = 1 / 2) (w : Word (Fin 4)) :
    (horizonC12AlgebraicTraceModel b d hd).probability w = (horizonC12Model b d hd).probability w := by
  change (1 / 12 : ℝ) * (Matrix.trace (wordOperator (horizonC12Projection b d) w)).re = _
  unfold horizonC12Model
  rw [c12TraceModel_probability]

theorem horizonC12AlgebraicTraceModel_anchorTracial (b d : ℝ) (hd : d ^ 2 = 1 / 2) :
    CyclicAnchorStateTracial (horizonC12AlgebraicTraceModel b d hd) := by
  apply cyclicAnchorStateTracial_of_source_trace
  intro X Y
  change (1 / 12 : ℝ) * (Matrix.trace (X * Y)).re = (1 / 12 : ℝ) * (Matrix.trace (Y * X)).re
  rw [Matrix.trace_mul_comm]

attribute [local irreducible] fourPointInvariant

/-- The normalized-trace C12 model already fails a word of length at most
seven beginning with affirmative A for any target with positive discriminant. -/
theorem horizonC12Model_fails_anchoredSeven (b d : ℝ) (hd : d ^ 2 = 1 / 2)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    ∃ w : Word (Fin 4), w.length ≤ 7 ∧ w.head? = some (0, true) ∧
      (horizonC12Model b d hd).probability w ≠ nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  by_contra! h
  apply cyclic_anchoredSeven_e3_not_match_of_faithful_or_tracial
    (horizonC12AlgebraicTraceModel b d hd) p hp hA
    (.inr (horizonC12AlgebraicTraceModel_anchorTracial b d hd))
  intro w hw hh
  rw [horizonC12AlgebraicTraceModel_probability]
  exact h w hw hh

private theorem horizonC12Model_fails_exactlySeven (b d : ℝ) (hd : d ^ 2 = 1 / 2)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (hsix : ∀ w : Word (Fin 4), w.length ≤ 6 →
      (horizonC12Model b d hd).probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :
    ∃ w : Word (Fin 4), w.length = 7 ∧ w.head? = some (0, true) ∧
      (horizonC12Model b d hd).probability w ≠ nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  obtain ⟨w, hlen, hhead, hbad⟩ := horizonC12Model_fails_anchoredSeven b d hd p hp hA
  have hn : ¬ w.length ≤ 6 := fun hs => hbad (hsix w hs)
  exact ⟨w, by omega, hhead, hbad⟩

theorem horizon_M_matrix_fails_at_anchoredSeven :
    ∃ w : Word (Fin 4), w.length = 7 ∧ w.head? = some (0, true) ∧
      (horizonC12Model (Real.sqrt 2) (Real.sqrt 2)⁻¹ horizon_sign_square).probability w ≠
        nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w :=
  horizonC12Model_fails_exactlySeven _ _ horizon_sign_square _ maximizerConfig_isAtom
    (by rw [fourPointInvariant_maximizerConfig]; norm_num) horizon_M_matrix

theorem horizon_S_matrix_fails_at_anchoredSeven :
    ∃ w : Word (Fin 4), w.length = 7 ∧ w.head? = some (0, true) ∧
      (horizonC12Model 1 (Real.sqrt 2)⁻¹ horizon_sign_square).probability w ≠
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w :=
  horizonC12Model_fails_exactlySeven _ _ horizon_sign_square _ fixedS_isAtom
    (by rw [fourPointInvariant_fixedS]; norm_num) horizon_S_matrix

end AlbertSequential.LengthSeven
