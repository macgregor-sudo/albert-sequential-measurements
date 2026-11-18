/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.ExactModel
public import ThirteenTracesAndAform
-- build order only: keeps large modules from compiling concurrently (memory)
import PentadArityAndHelly

/-! # `thm:glennie` at the configuration `S` (exact instance)

`fixedS = (p_A, p_B, p_C, p_D)`.  With `r_x = 2p_x − e`:
`‖F(r_A,r_B,r_C,r_D)‖² = 2¹⁷/3⁵ = 9·2²¹·N(p_A+p_B+p_C)·𝒜(S)`, where `‖x‖² = ⟨x,x⟩ = tr(x∘x)`
(`tracePairing`), `N = albertCubicNorm` and `𝒜 = fourPointInvariant` (`= 1/5832` at `S`).
The value of `F` is computed in the exact rational mirror by kernel evaluation and transported. -/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem toR_rat (a : ℚ) : ExactScalar.toR a = (a : ℝ) := rfl

/-- Rational octonion literal from eight coordinates. -/
def eo (a0 a1 a2 a3 b0 b1 b2 b3 : ℚ) : EO ℚ := ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩

def eaUnit : EA ℚ := ⟨1, 1, 1, eo 0 0 0 0 0 0 0 0, eo 0 0 0 0 0 0 0 0, eo 0 0 0 0 0 0 0 0⟩
def symQ (x : EA ℚ) : EA ℚ := (x.add x).sub eaUnit

/-- The four atoms of `S` over `ℚ`. -/
def SA : EA ℚ := ⟨1, 0, 0, eo 0 0 0 0 0 0 0 0, eo 0 0 0 0 0 0 0 0, eo 0 0 0 0 0 0 0 0⟩
def eo0' : EO ℚ := eo 0 0 0 0 0 0 0 0
def eoOne : EO ℚ := eo 1 0 0 0 0 0 0 0
def eoI : EO ℚ := eo 0 1 0 0 0 0 0 0
def eoJ : EO ℚ := eo 0 0 1 0 0 0 0 0
def eoL : EO ℚ := eo 0 0 0 0 1 0 0 0
def SBraw : EA ℚ := ⟨1, 1, 0, eoOne, eo0', eo0'⟩
def SCraw : EA ℚ := ⟨1, 1, 1, eoI.neg, eoOne, eoI⟩
def SDraw : EA ℚ := ⟨1, 1, 1, eoJ.neg, eoL.neg, (eoJ.mul eoL).neg⟩
def SB : EA ℚ := SBraw.smul (1 / 2)
def SC : EA ℚ := SCraw.smul (1 / 3)
def SD : EA ℚ := SDraw.smul (1 / 3)

noncomputable section

theorem castA_eaUnit : castA eaUnit = albertUnit := by
  apply albert_ext' <;> simp [castA, eaUnit, eo, castO, castQ, toR_rat, albertUnit] <;> rfl

theorem castA_symQ (x : EA ℚ) : castA (symQ x) = symmetryOf (castA x) := by
  rw [symQ, castA_sub, castA_add, castA_eaUnit, symmetryOf, two_smul]

theorem oct_ext {x y : Octonion} (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
    (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK) (h5 : x.2.re = y.2.re)
    (h6 : x.2.imI = y.2.imI) (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

theorem castA_SA : castA SA = fixedS 0 := by
  apply albert_ext' <;> simp [castA, SA, eo, castO, castQ, toR_rat, fixedS, atomA, diagAtom] <;> rfl

theorem oct_smul_fst' (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
theorem oct_smul_snd' (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl
theorem oct_neg_fst' (x : Octonion) : (-x).1 = -x.1 := rfl
theorem oct_neg_snd' (x : Octonion) : (-x).2 = -x.2 := rfl

theorem castO_eo0' : castO eo0' = 0 := by
  apply oct_ext <;> simp [castO, castQ, eo0', eo, toR_rat] <;> rfl
theorem castO_eoOne : castO eoOne = octonionScalar 1 := by
  apply oct_ext <;> simp [castO, castQ, eoOne, eo, toR_rat, octonionScalar]
theorem castO_eoI : castO eoI = octI := by
  apply oct_ext <;> simp [castO, castQ, eoI, eo, toR_rat, octI]
theorem castO_eoJ : castO eoJ = octJ := by
  apply oct_ext <;> simp [castO, castQ, eoJ, eo, toR_rat, octJ]
theorem castO_eoL : castO eoL = octL := by
  apply oct_ext <;> simp [castO, castQ, eoL, eo, toR_rat, octL] <;> rfl

theorem castA_SBraw : castA SBraw = ((![1, 1, 0], ![octonionScalar 1, 0, 0]) : Albert) := by
  apply albert_ext' <;>
    simp only [castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, SBraw, castO_eo0',
      castO_eoOne, toR_rat, albert_mk_fst, albert_mk_snd, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> norm_num
theorem castA_SCraw : castA SCraw = ((![1, 1, 1], ![-octI, octonionScalar 1, octI]) : Albert) := by
  apply albert_ext' <;>
    simp only [castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, SCraw, castO_neg,
      castO_eoI, castO_eoOne, toR_rat, albert_mk_fst, albert_mk_snd, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> norm_num
theorem castA_SDraw : castA SDraw =
    ((![1, 1, 1], ![-octJ, -octL, -octonionMul octJ octL]) : Albert) := by
  apply albert_ext' <;>
    simp only [castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, SDraw, castO_neg,
      castO_mul, castO_eoJ, castO_eoL, toR_rat, albert_mk_fst, albert_mk_snd,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] <;> norm_num

theorem castA_SB : castA SB = fixedS 1 := by
  have h : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
  rw [fixedS_one, SB, castA_smul, castA_SBraw, toR_rat, h]
  rfl

theorem castA_SC : castA SC = fixedS 2 := by
  have h : ((1 / 3 : ℚ) : ℝ) = (1 / 3 : ℝ) := by norm_num
  rw [fixedS_two, SC, castA_smul, castA_SCraw, toR_rat, h]
  rfl

theorem castA_SD : castA SD = fixedS 3 := by
  have h : ((1 / 3 : ℚ) : ℝ) = (1 / 3 : ℝ) := by norm_num
  rw [fixedS_three, SD, castA_smul, castA_SDraw, toR_rat, h]
  rfl

end

/-! Exact polarised Glennie value at `S` (window `A, B, C`, fourth atom `D`), computed term by
term (nine placements) by kernel evaluation. -/

set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term0 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SA) (symQ SB) (symQ SB) (symQ SA) (symQ SC) (symQ SC) =
    (⟨(0), (0), (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (0)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term1 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SA) (symQ SB) (symQ SB) (symQ SC) (symQ SA) (symQ SC) =
    (⟨(-176/27), (-128/27), (-368/81), eo (8/9) (-8/9) (160/27) (-128/81) (80/81) (16/27) (80/81) (80/81), eo (136/81) (-136/81) (80/81) (-16/27) (64/81) (-128/81) (-16/9) (-16/9), eo (-136/81) (88/27) (80/81) (80/81) (-16/9) (-16/9) (-224/81) (128/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term2 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SA) (symQ SB) (symQ SB) (symQ SC) (symQ SC) (symQ SA) =
    (⟨(112/81), (128/27), (784/81), eo (136/81) (-136/81) (-32/81) (-128/81) (16/9) (-272/81) (16/9) (16/9), eo (8/9) (-8/9) (16/9) (272/81) (-64/81) (-128/81) (-80/81) (-80/81), eo (-8/9) (-56/81) (16/9) (16/9) (-80/81) (-80/81) (-224/81) (128/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term3 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SB) (symQ SA) (symQ SB) (symQ SA) (symQ SC) (symQ SC) =
    (⟨(176/27), (112/81), (640/81), eo (-208/81) (-64/81) (-320/81) (-128/81) (-80/81) (-208/81) (-80/81) (-80/81), eo (-136/81) (136/81) (-80/81) (208/81) (-224/81) (-128/81) (224/81) (64/81), eo (136/81) (8/81) (-80/81) (-80/81) (224/81) (64/81) (224/81) (128/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term4 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SB) (symQ SA) (symQ SB) (symQ SC) (symQ SA) (symQ SC) =
    (⟨(0), (80/27), (-80/27), eo (40/27) (-16/27) (-64/27) (-64/27) (-16/27) (16/9) (-16/27) (16/27), eo (-20/27) (-20/27) (-16/27) (-16/9) (64/27) (-64/27) (-32/27) (16/27), eo (20/27) (-20/9) (-16/27) (16/27) (-32/27) (16/27) (0) (64/27)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term5 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SB) (symQ SA) (symQ SB) (symQ SC) (symQ SC) (symQ SA) =
    (⟨(-128/27), (-352/81), (-544/81), eo (16/81) (184/81) (224/81) (64/81) (-16/81) (208/81) (-16/81) (-112/81), eo (124/81) (-4/81) (-16/81) (-208/81) (32/81) (64/81) (16/81) (32/81), eo (-124/81) (100/81) (-16/81) (-112/81) (16/81) (32/81) (64/81) (-64/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term6 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SB) (symQ SB) (symQ SA) (symQ SA) (symQ SC) (symQ SC) =
    (⟨(-112/81), (-176/27), (-640/81), eo (-208/81) (64/81) (320/81) (-128/81) (-16/9) (-16/81) (-16/9) (-16/9), eo (-8/9) (8/9) (-16/9) (16/81) (-224/81) (-128/81) (224/81) (-64/81), eo (8/9) (200/81) (-16/9) (-16/9) (224/81) (-64/81) (224/81) (128/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term7 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SB) (symQ SB) (symQ SA) (symQ SC) (symQ SA) (symQ SC) =
    (⟨(128/27), (32/9), (608/81), eo (-16/27) (40/27) (-32/9) (64/81) (112/81) (-16/27) (112/81) (16/81), eo (-4/81) (124/81) (112/81) (16/27) (32/81) (64/81) (-16/27) (32/27), eo (4/81) (-52/27) (112/81) (16/81) (-16/27) (32/27) (-64/81) (-64/81)⟩ : EA ℚ) := by
  decide +kernel
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_term8 : glennieTerm (eaOps ℚ) (symQ SD) (symQ SB) (symQ SB) (symQ SA) (symQ SC) (symQ SC) (symQ SA) =
    (⟨(0), (80/27), (-80/27), eo (40/27) (-16/27) (-64/27) (-64/27) (-16/27) (16/9) (-16/27) (16/27), eo (-20/27) (-20/27) (-16/27) (-16/9) (64/27) (-64/27) (-32/27) (16/27), eo (20/27) (-20/9) (-16/27) (16/27) (-32/27) (16/27) (0) (64/27)⟩ : EA ℚ) := by
  decide +kernel
def glS_ABC_D_val : EA ℚ := ⟨(0), (0), (0), eo (0) (0) (0) (-256/27) (0) (0) (0) (0), eo (0) (0) (0) (0) (0) (-256/27) (0) (0), eo (0) (0) (0) (0) (0) (0) (0) (256/27)⟩
set_option maxHeartbeats 400000000 in
theorem glS_ABC_D_eq : glennieF (eaOps ℚ) (symQ SA) (symQ SB) (symQ SC) (symQ SD) = glS_ABC_D_val := by
  simp only [glennieF]
  rw [glS_ABC_D_term0, glS_ABC_D_term1, glS_ABC_D_term2, glS_ABC_D_term3, glS_ABC_D_term4, glS_ABC_D_term5, glS_ABC_D_term6, glS_ABC_D_term7, glS_ABC_D_term8]
  decide +kernel

theorem glS_ABC_D_normSq : glS_ABC_D_val.tp glS_ABC_D_val = 131072 / 243 := by
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem cubicNorm_S_ABC : ((SA.add SB).add SC).cubicNorm = 1 / 6 := by
  decide +kernel

noncomputable section

/-- `thm:glennie` at `S`, value: `‖F(r_A,r_B,r_C,r_D)‖² = 2¹⁷/3⁵`. -/
theorem glennie_fixedS_value :
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2))
          (symmetryOf (fixedS 3)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2))
          (symmetryOf (fixedS 3))) = 2 ^ 17 / 3 ^ 5 := by
  rw [← castA_SA, ← castA_SB, ← castA_SC, ← castA_SD, ← castA_symQ, ← castA_symQ, ← castA_symQ,
    ← castA_symQ, ← castA_glennieF, ← castA_tp]
  rw [glS_ABC_D_eq, glS_ABC_D_normSq, toR_rat]
  norm_num

theorem albertCubicNorm_fixedS_ABC : albertCubicNorm (fixedS 0 + fixedS 1 + fixedS 2) = 1 / 6 := by
  rw [← castA_SA, ← castA_SB, ← castA_SC, ← castA_add, ← castA_add, ← castA_cubicNorm,
    cubicNorm_S_ABC, toR_rat]
  norm_num

/-- `thm:glennie` holds at `S` in the printed form
`‖F(r_A,r_B,r_C,r_D)‖² = 9·2²¹·N(p_A+p_B+p_C)·𝒜(p_A,p_B,p_C,p_D)`. -/
theorem glennie_fixedS :
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2))
          (symmetryOf (fixedS 3)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2))
          (symmetryOf (fixedS 3))) =
      9 * 2 ^ 21 * albertCubicNorm (fixedS 0 + fixedS 1 + fixedS 2) * fourPointInvariant fixedS := by
  rw [glennie_fixedS_value, albertCubicNorm_fixedS_ABC, fourPointInvariant_fixedS]
  norm_num

end

end AlbertSequential.AppF
