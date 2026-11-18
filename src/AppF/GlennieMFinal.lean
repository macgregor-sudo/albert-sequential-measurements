/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.GlennieM

/-! # `thm:glennie` at `M`: transport of the exact value (see `AppF.GlennieM`). -/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem octJ_fst : octJ.1 = ⟨0, 0, 1, 0⟩ := rfl
theorem octJ_snd : octJ.2 = 0 := rfl
theorem octL_fst : octL.1 = 0 := rfl
theorem octL_snd : octL.2 = ⟨1, 0, 0, 0⟩ := rfl

noncomputable section

theorem castA_eaUnitQ2 : castA eaUnitQ2 = albertUnit := by
  apply albert_ext' <;> simp [castA, eaUnitQ2, eoq0, eoq, oq, qq, castO, castQ, toR_q2, albertUnit]
    <;> rfl

theorem castA_symQ2 (x : EA Q2) : castA (symQ2 x) = symmetryOf (castA x) := by
  rw [symQ2, castA_sub, castA_add, castA_eaUnitQ2, symmetryOf, two_smul]

theorem oct_zero_fst' : (0 : Octonion).1 = 0 := rfl
theorem oct_zero_snd' : (0 : Octonion).2 = 0 := rfl

private theorem s3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
private theorem s2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
private theorem haa : (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = 1 / 3 := by
  rw [div_mul_div_comm, one_mul, s3]
private theorem hab : (1 / Real.sqrt 3) * (Real.sqrt 2 / Real.sqrt 3) = Real.sqrt 2 / 3 := by
  rw [div_mul_div_comm, one_mul, s3]
private theorem hbb : (Real.sqrt 2 / Real.sqrt 3) * (Real.sqrt 2 / Real.sqrt 3) = 2 / 3 := by
  rw [div_mul_div_comm, s3, s2]

theorem castA_MA : castA MA = maximizerConfig 0 := by
  have h : maximizerConfig 0 = octDyad ![octonionScalar 1, 0, 0] := rfl
  rw [h]
  apply albert_ext' <;> try (apply oct_ext)
  all_goals simp [castA, MA, eoq0, eoq, oq, qq, castO, castQ, toR_q2, octDyad, octNormSq, octDot, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, oct_zero_fst', oct_zero_snd', oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd]

theorem castA_MB : castA MB = maximizerConfig 1 := by
  have h : maximizerConfig 1 = octDyad ![octonionScalar (1 / Real.sqrt 3),
      octonionScalar (Real.sqrt 2 / Real.sqrt 3), 0] := rfl
  rw [h]
  have h1 := haa
  have h2 := hab
  have h3 := hbb
  generalize 1 / Real.sqrt 3 = a at h1 h2 ⊢
  generalize Real.sqrt 2 / Real.sqrt 3 = b at h2 h3 ⊢
  apply albert_ext' <;> try (apply oct_ext)
  all_goals simp [castA, MB, eoq0, eoq, oq, qq, castO, castQ, toR_q2, octDyad, octNormSq, octDot, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, oct_zero_fst', oct_zero_snd', oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd]
  all_goals linarith

theorem castA_MC : castA MC = maximizerConfig 2 := by
  have h : maximizerConfig 2 = octDyad ![octonionScalar (1 / Real.sqrt 3),
      octonionScalar 0 + (1 / Real.sqrt 3) • octI, octonionScalar (1 / Real.sqrt 3)] := rfl
  rw [h]
  have h1 := haa
  generalize 1 / Real.sqrt 3 = a at h1 ⊢
  apply albert_ext' <;> try (apply oct_ext)
  all_goals simp [castA, MC, eoq0, eoq, oq, qq, castO, castQ, toR_q2, octDyad, octNormSq, octDot, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, oct_zero_fst', oct_zero_snd', oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd]
  all_goals linarith

theorem castA_MD : castA MD = maximizerConfig 3 := by
  have h : maximizerConfig 3 = octDyad ![octonionScalar (1 / Real.sqrt 3),
      octonionScalar 0 + (0 : ℝ) • octI + (1 / Real.sqrt 3) • octJ,
      (1 / Real.sqrt 3) • octL] := rfl
  rw [h]
  have h1 := haa
  generalize 1 / Real.sqrt 3 = a at h1 ⊢
  apply albert_ext' <;> try (apply oct_ext)
  all_goals simp [castA, MD, eoq0, eoq, oq, qq, castO, castQ, toR_q2, octDyad, octNormSq, octDot, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, octJ_fst, octJ_snd, octL_fst, octL_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, oct_zero_fst', oct_zero_snd', oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd]
  all_goals linarith

/-- `thm:glennie` at `M`, value: `‖F(r_A,r_B,r_C,r_D)‖² = 2²⁴/3⁹`. -/
theorem glennie_maximizer_value :
    tracePairing
        (nativeGlennieF (symmetryOf (maximizerConfig 0)) (symmetryOf (maximizerConfig 1))
          (symmetryOf (maximizerConfig 2)) (symmetryOf (maximizerConfig 3)))
        (nativeGlennieF (symmetryOf (maximizerConfig 0)) (symmetryOf (maximizerConfig 1))
          (symmetryOf (maximizerConfig 2)) (symmetryOf (maximizerConfig 3))) = 2 ^ 24 / 3 ^ 9 := by
  rw [← castA_MA, ← castA_MB, ← castA_MC, ← castA_MD, ← castA_symQ2, ← castA_symQ2,
    ← castA_symQ2, ← castA_symQ2, ← castA_glennieF, ← castA_tp]
  rw [glM_eq, glM_normSq, toR_q2]
  simp [qq]
  try norm_num

theorem albertCubicNorm_maximizer_ABC :
    albertCubicNorm (maximizerConfig 0 + maximizerConfig 1 + maximizerConfig 2) = 2 / 9 := by
  rw [← castA_MA, ← castA_MB, ← castA_MC, ← castA_add, ← castA_add, ← castA_cubicNorm,
    cubicNorm_M_ABC, toR_q2]
  simp [qq]
  try norm_num

/-- `thm:glennie` holds at `M` in the printed form. -/
theorem glennie_maximizer :
    tracePairing
        (nativeGlennieF (symmetryOf (maximizerConfig 0)) (symmetryOf (maximizerConfig 1))
          (symmetryOf (maximizerConfig 2)) (symmetryOf (maximizerConfig 3)))
        (nativeGlennieF (symmetryOf (maximizerConfig 0)) (symmetryOf (maximizerConfig 1))
          (symmetryOf (maximizerConfig 2)) (symmetryOf (maximizerConfig 3))) =
      9 * 2 ^ 21 * albertCubicNorm (maximizerConfig 0 + maximizerConfig 1 + maximizerConfig 2) *
        fourPointInvariant maximizerConfig := by
  rw [glennie_maximizer_value, albertCubicNorm_maximizer_ABC, fourPointInvariant_maximizerConfig]
  norm_num

end

end AlbertSequential.AppF
