/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.GlennieS
-- build order only: keeps large modules from compiling concurrently (memory)
import AppF.SecondOrderKernel

/-! # `thm:glennie` at `S` for the other choices of the fourth atom

Windows `(A,B,D; C)`, `(A,C,D; B)`, `(B,C,D; A)`: `‖F‖² = 2¹⁷/3⁵, 2¹⁹/3⁶, 2¹⁹/3⁶`, each equal to
`9·2²¹·N(sum of the three window atoms)·𝒜(S)` (`𝒜` is symmetric). -/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term0 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SA) (symQ SB) (symQ SB) (symQ SA) (symQ SD) (symQ SD) =
    (⟨(0), (0), (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term1 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SA) (symQ SB) (symQ SB) (symQ SD) (symQ SA) (symQ SD) =
    (⟨(-176/27), (-128/27), (-368/81), eo (8/9) (160/27) (-8/9) (-128/81) (-80/81) (-80/81) (-16/27) (-80/81), eo (-64/81) (16/9) (128/81) (16/9) (-136/81) (-80/81) (136/81) (16/27), eo (16/9) (224/81) (16/9) (-128/81) (136/81) (-80/81) (-88/27) (-80/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term2 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SA) (symQ SB) (symQ SB) (symQ SD) (symQ SD) (symQ SA) =
    (⟨(112/81), (128/27), (784/81), eo (136/81) (-32/81) (-136/81) (-128/81) (-16/9) (-16/9) (272/81) (-16/9), eo (64/81) (80/81) (128/81) (80/81) (-8/9) (-16/9) (8/9) (-272/81), eo (80/81) (224/81) (80/81) (-128/81) (8/9) (-16/9) (56/81) (-16/9)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term3 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SB) (symQ SA) (symQ SB) (symQ SA) (symQ SD) (symQ SD) =
    (⟨(176/27), (112/81), (640/81), eo (-208/81) (-320/81) (-64/81) (-128/81) (80/81) (80/81) (208/81) (80/81), eo (224/81) (-224/81) (128/81) (-64/81) (136/81) (80/81) (-136/81) (-208/81), eo (-224/81) (-224/81) (-64/81) (-128/81) (-136/81) (80/81) (-8/81) (80/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term4 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SB) (symQ SA) (symQ SB) (symQ SD) (symQ SA) (symQ SD) =
    (⟨(0), (80/27), (-80/27), eo (40/27) (-64/27) (-16/27) (-64/27) (16/27) (16/27) (-16/9) (-16/27), eo (-64/27) (32/27) (64/27) (-16/27) (20/27) (16/27) (20/27) (16/9), eo (32/27) (0) (-16/27) (-64/27) (-20/27) (16/27) (20/9) (-16/27)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term5 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SB) (symQ SA) (symQ SB) (symQ SD) (symQ SD) (symQ SA) =
    (⟨(-128/27), (-352/81), (-544/81), eo (16/81) (224/81) (184/81) (64/81) (16/81) (16/81) (-208/81) (112/81), eo (-32/81) (-16/81) (-64/81) (-32/81) (-124/81) (16/81) (4/81) (208/81), eo (-16/81) (-64/81) (-32/81) (64/81) (124/81) (16/81) (-100/81) (112/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term6 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SB) (symQ SB) (symQ SA) (symQ SA) (symQ SD) (symQ SD) =
    (⟨(-112/81), (-176/27), (-640/81), eo (-208/81) (320/81) (64/81) (-128/81) (16/9) (16/9) (16/81) (16/9), eo (224/81) (-224/81) (128/81) (64/81) (8/9) (16/9) (-8/9) (-16/81), eo (-224/81) (-224/81) (64/81) (-128/81) (-8/9) (16/9) (-200/81) (16/9)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term7 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SB) (symQ SB) (symQ SA) (symQ SD) (symQ SA) (symQ SD) =
    (⟨(128/27), (32/9), (608/81), eo (-16/27) (-32/9) (40/27) (64/81) (-112/81) (-112/81) (16/27) (-16/81), eo (-32/81) (16/27) (-64/81) (-32/27) (4/81) (-112/81) (-124/81) (-16/27), eo (16/27) (64/81) (-32/27) (64/81) (-4/81) (-112/81) (52/27) (-16/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_term8 : glennieTerm (eaOps ℚ) (symQ SC) (symQ SB) (symQ SB) (symQ SA) (symQ SD) (symQ SD) (symQ SA) =
    (⟨(0), (80/27), (-80/27), eo (40/27) (-64/27) (-16/27) (-64/27) (16/27) (16/27) (-16/9) (-16/27), eo (-64/27) (32/27) (64/27) (-16/27) (20/27) (16/27) (20/27) (16/9), eo (32/27) (0) (-16/27) (-64/27) (-20/27) (16/27) (20/9) (-16/27)⟩ : EA ℚ) := by
  decide +kernel
def glS_ABD_C_val : EA ℚ := ⟨(0), (0), (0), eo (0) (0) (0) (-256/27) (0) (0) (0) (0), eo (0) (0) (256/27) (0) (0) (0) (0) (0), eo (0) (0) (0) (-256/27) (0) (0) (0) (0)⟩
set_option maxHeartbeats 400000000 in
theorem glS_ABD_C_eq : glennieF (eaOps ℚ) (symQ SA) (symQ SB) (symQ SD) (symQ SC) = glS_ABD_C_val := by
  simp only [glennieF]
  rw [glS_ABD_C_term0, glS_ABD_C_term1, glS_ABD_C_term2, glS_ABD_C_term3, glS_ABD_C_term4, glS_ABD_C_term5, glS_ABD_C_term6, glS_ABD_C_term7, glS_ABD_C_term8]
  decide +kernel

theorem glS_ABD_C_normSq : glS_ABD_C_val.tp glS_ABD_C_val = 131072 / 243 := by
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem cubicNorm_S_ABD_C : ((SA.add SB).add SD).cubicNorm = 1 / 6 := by
  decide +kernel

noncomputable section

theorem glennie_fixedS_ABD_C :
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 2)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 2))) = 2 ^ 17 / 3 ^ 5 ∧
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 2)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 2))) =
      9 * 2 ^ 21 * albertCubicNorm (fixedS 0 + fixedS 1 + fixedS 3) * fourPointInvariant fixedS := by
  have hN : albertCubicNorm (fixedS 0 + fixedS 1 + fixedS 3) = 1 / 6 := by
    rw [← castA_SA, ← castA_SB, ← castA_SD, ← castA_add, ← castA_add,
      ← castA_cubicNorm, cubicNorm_S_ABD_C, toR_rat]
    norm_num
  have hv : tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 2)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 2))) = 2 ^ 17 / 3 ^ 5 := by
    rw [← castA_SA, ← castA_SB, ← castA_SD, ← castA_SC, ← castA_symQ,
      ← castA_symQ, ← castA_symQ, ← castA_symQ, ← castA_glennieF, ← castA_tp, glS_ABD_C_eq,
      glS_ABD_C_normSq, toR_rat]
    norm_num
  refine ⟨hv, ?_⟩
  rw [hv, hN, fourPointInvariant_fixedS]
  norm_num

end

set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term0 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SA) (symQ SC) (symQ SC) (symQ SA) (symQ SD) (symQ SD) =
    (⟨(0), (0), (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term1 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SA) (symQ SC) (symQ SC) (symQ SD) (symQ SA) (symQ SD) =
    (⟨(-64/9), (0), (-832/81), eo (-512/81) (-32/27) (-64/27) (0) (0) (0) (-32/27) (0), eo (0) (-64/81) (0) (-64/81) (0) (256/81) (-64/27) (64/81), eo (32/27) (-128/81) (-64/27) (64/81) (-64/27) (-64/81) (0) (32/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term2 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SA) (symQ SC) (symQ SC) (symQ SD) (symQ SD) (symQ SA) =
    (⟨(64/81), (640/81), (448/81), eo (128/81) (-32/27) (-64/27) (0) (0) (0) (-32/27) (0), eo (0) (-64/81) (0) (64/81) (0) (256/81) (-64/27) (-64/81), eo (32/27) (-128/81) (-64/27) (-64/81) (-64/27) (-64/81) (0) (160/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term3 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SC) (symQ SA) (symQ SC) (symQ SA) (symQ SD) (symQ SD) =
    (⟨(64/9), (0), (832/81), eo (512/81) (64/27) (32/27) (0) (0) (-32/27) (0) (0), eo (0) (-64/27) (256/81) (64/81) (0) (0) (-64/81) (-64/81), eo (-64/27) (0) (-64/81) (32/81) (32/27) (-64/27) (-128/81) (64/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term4 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SC) (symQ SA) (symQ SC) (symQ SD) (symQ SA) (symQ SD) =
    (⟨(0), (0), (0), eo (0) (-32/27) (32/27) (0) (0) (0) (0) (0), eo (16/27) (16/9) (64/27) (0) (16/27) (64/27) (16/9) (0), eo (16/27) (80/27) (-64/27) (0) (16/27) (-64/27) (80/27) (0)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term5 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SC) (symQ SA) (symQ SC) (symQ SD) (symQ SD) (symQ SA) =
    (⟨(-128/27), (-128/27), (-256/81), eo (-128/81) (0) (0) (0) (0) (32/27) (32/27) (0), eo (-16/27) (-16/81) (0) (-64/81) (-16/27) (-128/81) (80/27) (64/81), eo (16/27) (16/81) (0) (-32/81) (16/27) (128/81) (-80/27) (-160/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term6 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SC) (symQ SC) (symQ SA) (symQ SA) (symQ SD) (symQ SD) =
    (⟨(-64/81), (-640/81), (-448/81), eo (-128/81) (64/27) (32/27) (0) (0) (-32/27) (0) (0), eo (0) (-64/27) (256/81) (-64/81) (0) (0) (-64/81) (64/81), eo (-64/27) (0) (-64/81) (160/81) (32/27) (-64/27) (-128/81) (-64/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term7 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SC) (symQ SC) (symQ SA) (symQ SD) (symQ SA) (symQ SD) =
    (⟨(128/27), (128/27), (256/81), eo (128/81) (0) (0) (0) (0) (32/27) (32/27) (0), eo (-16/27) (80/27) (-128/81) (64/81) (-16/27) (0) (-16/81) (-64/81), eo (16/27) (-80/27) (128/81) (-160/81) (16/27) (0) (16/81) (-32/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_term8 : glennieTerm (eaOps ℚ) (symQ SB) (symQ SC) (symQ SC) (symQ SA) (symQ SD) (symQ SD) (symQ SA) =
    (⟨(0), (0), (0), eo (0) (-32/27) (32/27) (0) (0) (0) (0) (0), eo (16/27) (16/9) (64/27) (0) (16/27) (64/27) (16/9) (0), eo (16/27) (80/27) (-64/27) (0) (16/27) (-64/27) (80/27) (0)⟩ : EA ℚ) := by
  decide +kernel
def glS_ACD_B_val : EA ℚ := ⟨(0), (0), (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (256/27) (0) (0) (256/27) (0) (0), eo (0) (0) (-256/27) (0) (0) (-256/27) (0) (0)⟩
set_option maxHeartbeats 400000000 in
theorem glS_ACD_B_eq : glennieF (eaOps ℚ) (symQ SA) (symQ SC) (symQ SD) (symQ SB) = glS_ACD_B_val := by
  simp only [glennieF]
  rw [glS_ACD_B_term0, glS_ACD_B_term1, glS_ACD_B_term2, glS_ACD_B_term3, glS_ACD_B_term4, glS_ACD_B_term5, glS_ACD_B_term6, glS_ACD_B_term7, glS_ACD_B_term8]
  decide +kernel

theorem glS_ACD_B_normSq : glS_ACD_B_val.tp glS_ACD_B_val = 524288 / 729 := by
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem cubicNorm_S_ACD_B : ((SA.add SC).add SD).cubicNorm = 2 / 9 := by
  decide +kernel

noncomputable section

theorem glennie_fixedS_ACD_B :
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 1)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 1))) = 2 ^ 19 / 3 ^ 6 ∧
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 1)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 1))) =
      9 * 2 ^ 21 * albertCubicNorm (fixedS 0 + fixedS 2 + fixedS 3) * fourPointInvariant fixedS := by
  have hN : albertCubicNorm (fixedS 0 + fixedS 2 + fixedS 3) = 2 / 9 := by
    rw [← castA_SA, ← castA_SC, ← castA_SD, ← castA_add, ← castA_add,
      ← castA_cubicNorm, cubicNorm_S_ACD_B, toR_rat]
    norm_num
  have hv : tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 1)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 1))) = 2 ^ 19 / 3 ^ 6 := by
    rw [← castA_SA, ← castA_SC, ← castA_SD, ← castA_SB, ← castA_symQ,
      ← castA_symQ, ← castA_symQ, ← castA_symQ, ← castA_glennieF, ← castA_tp, glS_ACD_B_eq,
      glS_ACD_B_normSq, toR_rat]
    norm_num
  refine ⟨hv, ?_⟩
  rw [hv, hN, fourPointInvariant_fixedS]
  norm_num

end

set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term0 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SB) (symQ SC) (symQ SC) (symQ SB) (symQ SD) (symQ SD) =
    (⟨(0), (0), (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term1 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SB) (symQ SC) (symQ SC) (symQ SD) (symQ SB) (symQ SD) =
    (⟨(-800/81), (224/81), (-832/81), eo (-32/9) (-32/27) (-64/27) (0) (16/27) (16/27) (-16/27) (16/27), eo (-16/27) (16/9) (32/27) (-32/27) (-64/27) (-16/27) (0) (16/9), eo (-16/81) (-80/81) (-160/81) (32/81) (0) (-16/9) (64/27) (176/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term2 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SB) (symQ SC) (symQ SC) (symQ SD) (symQ SD) (symQ SB) =
    (⟨(160/27), (224/81), (448/81), eo (-32/9) (-32/27) (-64/27) (0) (16/27) (16/27) (-16/27) (16/27), eo (-16/27) (16/9) (32/27) (-32/27) (-64/27) (-16/27) (0) (16/9), eo (-16/81) (-80/81) (-32/81) (160/81) (0) (-272/81) (64/27) (16/27)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term3 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SC) (symQ SB) (symQ SC) (symQ SB) (symQ SD) (symQ SD) =
    (⟨(800/81), (-224/81), (832/81), eo (32/9) (64/27) (32/27) (0) (16/27) (-16/27) (16/27) (16/27), eo (-64/27) (0) (-16/27) (16/9) (-16/27) (32/27) (16/9) (-32/27), eo (0) (64/27) (-16/9) (176/81) (-16/81) (-160/81) (-80/81) (32/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term4 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SC) (symQ SB) (symQ SC) (symQ SD) (symQ SB) (symQ SD) =
    (⟨(0), (0), (0), eo (0) (-32/27) (32/27) (0) (0) (0) (0) (0), eo (80/27) (-16/9) (0) (0) (80/27) (0) (-16/9) (0), eo (-16/27) (16/27) (-64/27) (64/27) (-16/27) (-64/27) (16/27) (64/27)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term5 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SC) (symQ SB) (symQ SC) (symQ SD) (symQ SD) (symQ SB) =
    (⟨(-512/81), (-256/81), (-256/81), eo (0) (0) (0) (0) (-32/27) (0) (0) (-32/27), eo (0) (0) (-16/27) (-16/27) (0) (-16/27) (0) (-16/27), eo (-64/81) (-32/81) (-16/81) (-16/81) (64/27) (80/27) (-32/9) (-16/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term6 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SC) (symQ SC) (symQ SB) (symQ SB) (symQ SD) (symQ SD) =
    (⟨(-160/27), (-224/81), (-448/81), eo (32/9) (64/27) (32/27) (0) (16/27) (-16/27) (16/27) (16/27), eo (-64/27) (0) (-16/27) (16/9) (-16/27) (32/27) (16/9) (-32/27), eo (0) (64/27) (-272/81) (16/27) (-16/81) (-32/81) (-80/81) (160/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term7 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SC) (symQ SC) (symQ SB) (symQ SD) (symQ SB) (symQ SD) =
    (⟨(512/81), (256/81), (256/81), eo (0) (0) (0) (0) (-32/27) (0) (0) (-32/27), eo (0) (0) (-16/27) (-16/27) (0) (-16/27) (0) (-16/27), eo (64/27) (-32/9) (80/27) (-16/81) (-64/81) (-16/81) (-32/81) (-16/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_term8 : glennieTerm (eaOps ℚ) (symQ SA) (symQ SC) (symQ SC) (symQ SB) (symQ SD) (symQ SD) (symQ SB) =
    (⟨(0), (0), (0), eo (0) (-32/27) (32/27) (0) (0) (0) (0) (0), eo (80/27) (-16/9) (0) (0) (80/27) (0) (-16/9) (0), eo (-16/27) (16/27) (-64/27) (64/27) (-16/27) (-64/27) (16/27) (64/27)⟩ : EA ℚ) := by
  decide +kernel
def glS_BCD_A_val : EA ℚ := ⟨(0), (0), (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (-256/27) (256/27) (0) (-256/27) (0) (256/27)⟩
set_option maxHeartbeats 400000000 in
theorem glS_BCD_A_eq : glennieF (eaOps ℚ) (symQ SB) (symQ SC) (symQ SD) (symQ SA) = glS_BCD_A_val := by
  simp only [glennieF]
  rw [glS_BCD_A_term0, glS_BCD_A_term1, glS_BCD_A_term2, glS_BCD_A_term3, glS_BCD_A_term4, glS_BCD_A_term5, glS_BCD_A_term6, glS_BCD_A_term7, glS_BCD_A_term8]
  decide +kernel

theorem glS_BCD_A_normSq : glS_BCD_A_val.tp glS_BCD_A_val = 524288 / 729 := by
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem cubicNorm_S_BCD_A : ((SB.add SC).add SD).cubicNorm = 2 / 9 := by
  decide +kernel

noncomputable section

theorem glennie_fixedS_BCD_A :
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 0)))
        (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 0))) = 2 ^ 19 / 3 ^ 6 ∧
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 0)))
        (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 0))) =
      9 * 2 ^ 21 * albertCubicNorm (fixedS 1 + fixedS 2 + fixedS 3) * fourPointInvariant fixedS := by
  have hN : albertCubicNorm (fixedS 1 + fixedS 2 + fixedS 3) = 2 / 9 := by
    rw [← castA_SB, ← castA_SC, ← castA_SD, ← castA_add, ← castA_add,
      ← castA_cubicNorm, cubicNorm_S_BCD_A, toR_rat]
    norm_num
  have hv : tracePairing
        (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 0)))
        (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))
          (symmetryOf (fixedS 0))) = 2 ^ 19 / 3 ^ 6 := by
    rw [← castA_SB, ← castA_SC, ← castA_SD, ← castA_SA, ← castA_symQ,
      ← castA_symQ, ← castA_symQ, ← castA_symQ, ← castA_glennieF, ← castA_tp, glS_BCD_A_eq,
      glS_BCD_A_normSq, toR_rat]
    norm_num
  refine ⟨hv, ?_⟩
  rw [hv, hN, fourPointInvariant_fixedS]
  norm_num

end

end AlbertSequential.AppF
