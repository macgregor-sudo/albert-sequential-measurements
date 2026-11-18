/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockA.GlennieGeneral
public import BlockA.SecondOrderResidual
public import AppF.GlennieSOrders
public import AppF.GlennieMFinal
public import Pending.GlennieGeneral
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Verification, Axiom Audit, and Non-Vacuity / Sharpness Controls (`BlockA`)

Consumer and audit module covering every headline declaration of
(`BlockA.GlennieBimodule`, `BlockA.GlennieWindowTrace`, `BlockA.GlennieDefect`,
`BlockA.GlennieGeneral`, `BlockA.SecondOrderResidual`, and `Pending.GlennieGeneral`)
plus non-vacuity and sharpness controls:

1. Agreement with exact rational/quadratic-field computations `AppF.glennie_fixedS`
   (`2^17/3^5`), `AppF.glennie_fixedS_{ABD_C, ACD_B, BCD_A}` (`2^17/3^5`, `2^19/3^6`),
   and `AppF.glennie_maximizer` (`2^24/3^9`).
2. Degenerate 4-atom controls (`diagAtom 0, diagAtom 0, diagAtom 1, diagAtom 2` and four
   distinct quaternionic atoms in `standardQuaternionicWindow`) with `LHS = 0 = RHS`.
3. `cor:so:residual` non-vacuity on actual projective equalities (`eq:cer:extraeq` and
   repetition equality) along explicit `C³` curves of atoms leaving `standardComplexWindow`.
4. Off-window state sharpness (`Q ≠ 0`, `ρ ∉ W`, `IsDensity ρ`) for `cor:so:residual`,
   showing why `ρ ∈ W` is genuinely required to improve `O(t²)` to `O(t³)`.
-/

@[expose] public section

namespace AlbertSequential.AppF.Checks

open AlbertSequential
open AlbertSequential.AppF
open scoped AlbertSequential.AppF
open scoped Topology Matrix
open Asymptotics Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

/-! ## Local coordinate helpers -/

private theorem oct_ext_chk {x y : Octonion}
    (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
    (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK)
    (h5 : x.2.re = y.2.re) (h6 : x.2.imI = y.2.imI)
    (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y :=
  apply_oct_ext h1 h2 h3 h4 h5 h6 h7 h8
where
  apply_oct_ext {x y : Octonion}
      (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
      (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK)
      (h5 : x.2.re = y.2.re) (h6 : x.2.imI = y.2.imI)
      (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y := by
    apply Prod.ext <;> apply Quaternion.ext <;> assumption

private theorem albert_ext_chk {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> assumption

private theorem octNormSq_zero_chk : octNormSq (0 : Octonion) = 0 := by
  rw [octNormSq_coords]; simp

private theorem octNormSq_scalar_chk (r : ℝ) : octNormSq (octonionScalar r) = r ^ 2 := by
  rw [octNormSq_coords]
  change r ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = r ^ 2
  ring

private theorem octNormSq_J_chk : octNormSq octJ = 1 := by
  rw [octNormSq_coords]
  change 0 ^ 2 + 0 ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
  ring

private theorem octNormSq_K_chk : octNormSq octK = 1 := by
  rw [octNormSq_coords]
  change 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
  ring

private theorem octNormSq_L_chk : octNormSq octL = 1 := by
  rw [octNormSq_coords]
  change 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
  ring

private theorem octNormSq_conj_chk (x : Octonion) : octNormSq (octonionConj x) = octNormSq x := by
  rw [octNormSq_coords, octNormSq_coords]
  dsimp [octonionConj]
  simp

private theorem oct_smul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem oct_smul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl
private theorem oct_add_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem oct_add_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem oct_sub_fst (x y : Octonion) : (x - y).1 = x.1 - y.1 := rfl
private theorem oct_sub_snd (x y : Octonion) : (x - y).2 = x.2 - y.2 := rfl
private theorem oct_neg_fst (x : Octonion) : (-x).1 = -x.1 := rfl
private theorem oct_neg_snd (x : Octonion) : (-x).2 = -x.2 := rfl
private theorem oct_zero_fst : (0 : Octonion).1 = 0 := rfl
private theorem oct_zero_snd : (0 : Octonion).2 = 0 := rfl

private theorem quat_smul_re (r : ℝ) (q : Quaternion ℝ) : (r • q).re = r * q.re := rfl
private theorem quat_smul_imI (r : ℝ) (q : Quaternion ℝ) : (r • q).imI = r * q.imI := rfl
private theorem quat_smul_imJ (r : ℝ) (q : Quaternion ℝ) : (r • q).imJ = r * q.imJ := rfl
private theorem quat_smul_imK (r : ℝ) (q : Quaternion ℝ) : (r • q).imK = r * q.imK := rfl

private theorem albert_add_fst_chk (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd_chk (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_smul_fst_chk (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd_chk (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

private theorem octonionMul_snd_eq_zero {x y : Octonion} (hx : x.2 = 0) (hy : y.2 = 0) :
    (octonionMul x y).2 = 0 := by
  change y.2 * x.1 + x.2 * star y.1 = 0
  rw [hx, hy, zero_mul, zero_mul, add_zero]

private theorem octonionConj_snd_eq_zero {x : Octonion} (hx : x.2 = 0) :
    (octonionConj x).2 = 0 := by
  change -x.2 = 0
  rw [hx, neg_zero]

private theorem mem_standardQuaternionicWindow_of_snd_zero (x : Albert)
    (hx : ∀ k : Fin 3, (x.2 k).2 = 0) :
    x ∈ standardQuaternionicWindow.subalgebra.carrier := by
  let M : QuatMatrix3 := fun i j => match i.val, j.val with
    | 0, 0 => ⟨x.1 0, 0, 0, 0⟩
    | 1, 1 => ⟨x.1 1, 0, 0, 0⟩
    | 2, 2 => ⟨x.1 2, 0, 0, 0⟩
    | 0, 1 => (x.2 0).1
    | 0, 2 => (x.2 1).1
    | 1, 2 => (x.2 2).1
    | 1, 0 => star (x.2 0).1
    | 2, 0 => star (x.2 1).1
    | 2, 1 => star (x.2 2).1
    | _, _ => 0
  have hM_sa : M ∈ selfAdjoint QuatMatrix3 := by
    rw [selfAdjoint.mem_iff]
    funext i j
    rw [Matrix.star_apply]
    fin_cases i <;> fin_cases j <;> dsimp only [M]
    · apply Quaternion.ext <;> simp
    · exact star_star _
    · exact star_star _
    · rfl
    · apply Quaternion.ext <;> simp
    · exact star_star _
    · rfl
    · rfl
    · apply Quaternion.ext <;> simp
  refine ⟨⟨M, hM_sa⟩, ?_⟩
  apply albert_ext_chk
  · rfl
  · rfl
  · rfl
  · apply Prod.ext; rfl; exact (hx 0).symm
  · apply Prod.ext; rfl; exact (hx 1).symm
  · apply Prod.ext; rfl; exact (hx 2).symm

private theorem octNormSq_scalar_add_J (a b : ℝ) :
    octNormSq (a • octonionScalar 1 + b • octJ) = a ^ 2 + b ^ 2 := by
  rw [octNormSq_coords]
  change (a * 1 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 + (a * 0 + b * 1) ^ 2 + (a * 0 + b * 0) ^ 2 +
    (a * 0 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 =
    a ^ 2 + b ^ 2
  ring

private theorem octNormSq_scalar_add_L (a b : ℝ) :
    octNormSq (a • octonionScalar 1 + b • octL) = a ^ 2 + b ^ 2 := by
  rw [octNormSq_coords]
  change (a * 1 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 +
    (a * 0 + b * 1) ^ 2 + (a * 0 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 + (a * 0 + b * 0) ^ 2 =
    a ^ 2 + b ^ 2
  ring

/-! ## Section 1: Exact-Instance Agreement (`S`, `S` Permutations, `M`) and Degenerate Controls -/

theorem glennie_fixedS_general_agrees :
    tracePairing
        (nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit)
          ((2 : ℝ) • fixedS 2 - albertUnit) ((2 : ℝ) • fixedS 3 - albertUnit))
        (nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit)
          ((2 : ℝ) • fixedS 2 - albertUnit) ((2 : ℝ) • fixedS 3 - albertUnit)) =
      2 ^ 17 / 3 ^ 5 ∧
    tracePairing
        (nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit)
          ((2 : ℝ) • fixedS 3 - albertUnit) ((2 : ℝ) • fixedS 2 - albertUnit))
        (nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit)
          ((2 : ℝ) • fixedS 3 - albertUnit) ((2 : ℝ) • fixedS 2 - albertUnit)) =
      2 ^ 17 / 3 ^ 5 ∧
    tracePairing
        (nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 2 - albertUnit)
          ((2 : ℝ) • fixedS 3 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit))
        (nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 2 - albertUnit)
          ((2 : ℝ) • fixedS 3 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit)) =
      2 ^ 19 / 3 ^ 6 ∧
    tracePairing
        (nativeGlennieF ((2 : ℝ) • fixedS 1 - albertUnit) ((2 : ℝ) • fixedS 2 - albertUnit)
          ((2 : ℝ) • fixedS 3 - albertUnit) ((2 : ℝ) • fixedS 0 - albertUnit))
        (nativeGlennieF ((2 : ℝ) • fixedS 1 - albertUnit) ((2 : ℝ) • fixedS 2 - albertUnit)
          ((2 : ℝ) • fixedS 3 - albertUnit) ((2 : ℝ) • fixedS 0 - albertUnit)) =
      2 ^ 19 / 3 ^ 6 := by
  have hABCD :
      tracePairing
          (nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit)
            ((2 : ℝ) • fixedS 2 - albertUnit) ((2 : ℝ) • fixedS 3 - albertUnit))
          (nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit)
            ((2 : ℝ) • fixedS 2 - albertUnit) ((2 : ℝ) • fixedS 3 - albertUnit)) =
        2 ^ 17 / 3 ^ 5 := by
    have hgen := thm_glennie_normSq (fixedS 0) (fixedS 1) (fixedS 2) (fixedS 3)
      (fixedS_isAtom 0) (fixedS_isAtom 1) (fixedS_isAtom 2) (fixedS_isAtom 3)
    have hvec : ![fixedS 0, fixedS 1, fixedS 2, fixedS 3] = fixedS := by
      ext i; fin_cases i <;> rfl
    rw [hvec, albertCubicNorm_fixedS_ABC, fourPointInvariant_fixedS] at hgen
    rw [hgen]; norm_num
  have hstmt :
      tracePairing
          (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
            (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3)))
          (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
            (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))) =
        9 * 2 ^ 21 * albertCubicNorm (fixedS 0 + fixedS 1 + fixedS 2) * fourPointInvariant fixedS :=
    glennieViolationStatement_holds fixedS fixedS_isAtom
  have hABCD_eq :
      9 * 2 ^ 21 * albertCubicNorm (fixedS 0 + fixedS 1 + fixedS 2) * fourPointInvariant fixedS =
        2 ^ 17 / 3 ^ 5 := by
    rw [albertCubicNorm_fixedS_ABC, fourPointInvariant_fixedS]; norm_num
  have _ : tracePairing
      (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
        (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3)))
      (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
        (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))) = 2 ^ 17 / 3 ^ 5 :=
    hstmt.trans hABCD_eq
  exact ⟨hABCD, glennie_fixedS_ABD_C.1, glennie_fixedS_ACD_B.1, glennie_fixedS_BCD_A.1⟩

theorem glennie_fixedS_general_matches_all_orders :
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
          (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
          (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))) = 2 ^ 17 / 3 ^ 5 ∧
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
          (symmetryOf (fixedS 3)) (symmetryOf (fixedS 2)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
          (symmetryOf (fixedS 3)) (symmetryOf (fixedS 2))) = 2 ^ 17 / 3 ^ 5 ∧
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2))
          (symmetryOf (fixedS 3)) (symmetryOf (fixedS 1)))
        (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2))
          (symmetryOf (fixedS 3)) (symmetryOf (fixedS 1))) = 2 ^ 19 / 3 ^ 6 ∧
    tracePairing
        (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2))
          (symmetryOf (fixedS 3)) (symmetryOf (fixedS 0)))
        (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2))
          (symmetryOf (fixedS 3)) (symmetryOf (fixedS 0))) = 2 ^ 19 / 3 ^ 6 := by
  have hperm := thm_glennie_perm (fixedS 0) (fixedS 1) (fixedS 2) (fixedS 3)
    (fixedS_isAtom 0) (fixedS_isAtom 1) (fixedS_isAtom 2) (fixedS_isAtom 3)
  have hvec : ![fixedS 0, fixedS 1, fixedS 2, fixedS 3] = fixedS := by
    ext i; fin_cases i <;> rfl
  have hABCD :
      tracePairing
          (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
            (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3)))
          (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
            (symmetryOf (fixedS 2)) (symmetryOf (fixedS 3))) = 2 ^ 17 / 3 ^ 5 := by
    have h0 := hperm (Equiv.refl (Fin 4))
    dsimp only [Equiv.refl_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0
    rw [hvec, albertCubicNorm_fixedS_ABC, fourPointInvariant_fixedS] at h0
    change tracePairing _ _ = _
    rw [show symmetryOf (fixedS 0) = (2 : ℝ) • fixedS 0 - albertUnit from rfl,
      show symmetryOf (fixedS 1) = (2 : ℝ) • fixedS 1 - albertUnit from rfl,
      show symmetryOf (fixedS 2) = (2 : ℝ) • fixedS 2 - albertUnit from rfl,
      show symmetryOf (fixedS 3) = (2 : ℝ) • fixedS 3 - albertUnit from rfl, h0]
    norm_num
  have hABDC :
      tracePairing
          (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
            (symmetryOf (fixedS 3)) (symmetryOf (fixedS 2)))
          (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 1))
            (symmetryOf (fixedS 3)) (symmetryOf (fixedS 2))) = 2 ^ 17 / 3 ^ 5 := by
    let σ1 : Equiv.Perm (Fin 4) := Equiv.swap 2 3
    have hs0 : σ1 0 = 0 := by decide
    have hs1 : σ1 1 = 1 := by decide
    have hs2 : σ1 2 = 3 := by decide
    have hs3 : σ1 3 = 2 := by decide
    have h1 := hperm σ1
    dsimp only at h1
    rw [hs0, hs1, hs2, hs3, hvec] at h1
    have hRHS :
        9 * 2 ^ 21 * albertCubicNorm (fixedS 0 + fixedS 1 + fixedS 3) * fourPointInvariant fixedS =
          2 ^ 17 / 3 ^ 5 := by
      have h2 := glennie_fixedS_ABD_C.2
      rw [glennie_fixedS_ABD_C.1] at h2
      exact h2.symm
    exact h1.trans hRHS
  have hACDB :
      tracePairing
          (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2))
            (symmetryOf (fixedS 3)) (symmetryOf (fixedS 1)))
          (nativeGlennieF (symmetryOf (fixedS 0)) (symmetryOf (fixedS 2))
            (symmetryOf (fixedS 3)) (symmetryOf (fixedS 1))) = 2 ^ 19 / 3 ^ 6 := by
    let σ2 : Equiv.Perm (Fin 4) := (Equiv.swap 2 3).trans (Equiv.swap 1 2)
    have hs0 : σ2 0 = 0 := by decide
    have hs1 : σ2 1 = 2 := by decide
    have hs2 : σ2 2 = 3 := by decide
    have hs3 : σ2 3 = 1 := by decide
    have h1 := hperm σ2
    dsimp only at h1
    rw [hs0, hs1, hs2, hs3, hvec] at h1
    have hRHS :
        9 * 2 ^ 21 * albertCubicNorm (fixedS 0 + fixedS 2 + fixedS 3) * fourPointInvariant fixedS =
          2 ^ 19 / 3 ^ 6 := by
      have h2 := glennie_fixedS_ACD_B.2
      rw [glennie_fixedS_ACD_B.1] at h2
      exact h2.symm
    exact h1.trans hRHS
  have hBCDA :
      tracePairing
          (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2))
            (symmetryOf (fixedS 3)) (symmetryOf (fixedS 0)))
          (nativeGlennieF (symmetryOf (fixedS 1)) (symmetryOf (fixedS 2))
            (symmetryOf (fixedS 3)) (symmetryOf (fixedS 0))) = 2 ^ 19 / 3 ^ 6 := by
    let σ3 : Equiv.Perm (Fin 4) := ((Equiv.swap 2 3).trans (Equiv.swap 1 2)).trans (Equiv.swap 0 1)
    have hs0 : σ3 0 = 1 := by decide
    have hs1 : σ3 1 = 2 := by decide
    have hs2 : σ3 2 = 3 := by decide
    have hs3 : σ3 3 = 0 := by decide
    have h1 := hperm σ3
    dsimp only at h1
    rw [hs0, hs1, hs2, hs3, hvec] at h1
    have hRHS :
        9 * 2 ^ 21 * albertCubicNorm (fixedS 1 + fixedS 2 + fixedS 3) * fourPointInvariant fixedS =
          2 ^ 19 / 3 ^ 6 := by
      have h2 := glennie_fixedS_BCD_A.2
      rw [glennie_fixedS_BCD_A.1] at h2
      exact h2.symm
    exact h1.trans hRHS
  exact ⟨hABCD, hABDC, hACDB, hBCDA⟩

theorem glennie_maximizer_general_agrees :
    tracePairing
        (nativeGlennieF ((2 : ℝ) • maximizerConfig 0 - albertUnit)
          ((2 : ℝ) • maximizerConfig 1 - albertUnit)
          ((2 : ℝ) • maximizerConfig 2 - albertUnit)
          ((2 : ℝ) • maximizerConfig 3 - albertUnit))
        (nativeGlennieF ((2 : ℝ) • maximizerConfig 0 - albertUnit)
          ((2 : ℝ) • maximizerConfig 1 - albertUnit)
          ((2 : ℝ) • maximizerConfig 2 - albertUnit)
          ((2 : ℝ) • maximizerConfig 3 - albertUnit)) = 2 ^ 24 / 3 ^ 9 := by
  have hgen := thm_glennie_normSq (maximizerConfig 0) (maximizerConfig 1)
    (maximizerConfig 2) (maximizerConfig 3)
    (maximizerConfig_isAtom 0) (maximizerConfig_isAtom 1)
    (maximizerConfig_isAtom 2) (maximizerConfig_isAtom 3)
  have hvec : ![maximizerConfig 0, maximizerConfig 1, maximizerConfig 2, maximizerConfig 3] =
      maximizerConfig := by
    ext i; fin_cases i <;> rfl
  rw [hvec, albertCubicNorm_maximizer_ABC, fourPointInvariant_maximizerConfig] at hgen
  rw [hgen]
  norm_num

/-- Degenerate 4-atom witness `(diagAtom 0, diagAtom 0, diagAtom 1, diagAtom 2)`:
repeated atoms inside `standardQuaternionicWindow` with `N(p_A + p_B + p_C) = 0`, `𝒜 = 0`,
`F = 0`, and `LHS = 0 = RHS` (`N_W = 0` degenerate boundary check). -/
theorem glennie_degenerate_diagonal_control :
    let pDeg : Fin 4 → Albert := ![diagAtom 0, diagAtom 0, diagAtom 1, diagAtom 2]
    (∀ i, IsAtom (pDeg i)) ∧
      albertCubicNorm (pDeg 0 + pDeg 1 + pDeg 2) = 0 ∧
      fourPointInvariant pDeg = 0 ∧
      nativeGlennieF ((2 : ℝ) • pDeg 0 - albertUnit) ((2 : ℝ) • pDeg 1 - albertUnit)
        ((2 : ℝ) • pDeg 2 - albertUnit) ((2 : ℝ) • pDeg 3 - albertUnit) = 0 ∧
      tracePairing
        (nativeGlennieF ((2 : ℝ) • pDeg 0 - albertUnit) ((2 : ℝ) • pDeg 1 - albertUnit)
          ((2 : ℝ) • pDeg 2 - albertUnit) ((2 : ℝ) • pDeg 3 - albertUnit))
        (nativeGlennieF ((2 : ℝ) • pDeg 0 - albertUnit) ((2 : ℝ) • pDeg 1 - albertUnit)
          ((2 : ℝ) • pDeg 2 - albertUnit) ((2 : ℝ) • pDeg 3 - albertUnit)) = 0 ∧
      9 * 2 ^ 21 * albertCubicNorm (pDeg 0 + pDeg 1 + pDeg 2) * fourPointInvariant pDeg = 0 := by
  intro pDeg
  have hatom : ∀ i, IsAtom (pDeg i) := fun i => by
    fin_cases i
    · exact diagAtom_isAtom 0
    · exact diagAtom_isAtom 0
    · exact diagAtom_isAtom 1
    · exact diagAtom_isAtom 2
  have hN : albertCubicNorm (pDeg 0 + pDeg 1 + pDeg 2) = 0 := by
    have hd0 : (pDeg 0 + pDeg 1 + pDeg 2).1 0 = 2 := by
      simp only [pDeg, albert_add_fst_chk, diagAtom]
      norm_num
    have hd1 : (pDeg 0 + pDeg 1 + pDeg 2).1 1 = 1 := by
      simp only [pDeg, albert_add_fst_chk, diagAtom]
      norm_num
    have hd2 : (pDeg 0 + pDeg 1 + pDeg 2).1 2 = 0 := by
      simp only [pDeg, albert_add_fst_chk, diagAtom]
      norm_num
    have ho : ∀ k : Fin 3, (pDeg 0 + pDeg 1 + pDeg 2).2 k = 0 := fun k => by
      change (pDeg 0).2 k + (pDeg 1).2 k + (pDeg 2).2 k = 0
      simp [pDeg, diagAtom]
    unfold albertCubicNorm
    rw [hd0, hd1, hd2, ho 0, ho 1, ho 2, octNormSq_zero_chk, octonionMul_zero_left,
      octDot_zero_left]
    norm_num
  have hquat : ∀ i, pDeg i ∈ standardQuaternionicWindow.subalgebra.carrier := fun i =>
    mem_standardQuaternionicWindow_of_snd_zero (pDeg i) fun k => by
      fin_cases i <;> rfl
  have hF0 :
      nativeGlennieF ((2 : ℝ) • pDeg 0 - albertUnit) ((2 : ℝ) • pDeg 1 - albertUnit)
        ((2 : ℝ) • pDeg 2 - albertUnit) ((2 : ℝ) • pDeg 3 - albertUnit) = 0 :=
    glennie_of_quatWindow standardQuaternionicWindow pDeg hquat
  have hA0 : fourPointInvariant pDeg = 0 := by
    have hvec : ![pDeg 0, pDeg 1, pDeg 2, pDeg 3] = pDeg := by
      ext i; fin_cases i <;> rfl
    rw [← hvec]
    exact (thm_glennie_eq_zero_iff (pDeg 0) (pDeg 1) (pDeg 2) (pDeg 3)
      (hatom 0) (hatom 1) (hatom 2) (hatom 3)).1 hF0
  have hLHS :
      tracePairing
        (nativeGlennieF ((2 : ℝ) • pDeg 0 - albertUnit) ((2 : ℝ) • pDeg 1 - albertUnit)
          ((2 : ℝ) • pDeg 2 - albertUnit) ((2 : ℝ) • pDeg 3 - albertUnit))
        (nativeGlennieF ((2 : ℝ) • pDeg 0 - albertUnit) ((2 : ℝ) • pDeg 1 - albertUnit)
          ((2 : ℝ) • pDeg 2 - albertUnit) ((2 : ℝ) • pDeg 3 - albertUnit)) = 0 := by
    rw [hF0, ← zero_smul ℝ (0 : Albert), tracePairing_smul_left, zero_mul]
  refine ⟨hatom, hN, hA0, hF0, hLHS, ?_⟩
  rw [hA0, mul_zero]

/-- Non-repeated degenerate 4-atom control: four distinct non-orthogonal atoms
`fixedS 0, fixedS 1, fixedS 2, qD` inside `standardQuaternionicWindow`, where `N(p_A+p_B+p_C) = 1/6 ≠ 0`
and `tripleDelta ≠ 0`, yet `𝒜 = 0`, `F = 0`, and `LHS = 0 = RHS`. -/
theorem glennie_degenerate_quaternionic_control :
    let qD : Albert := octDyad ![octonionScalar (1 / Real.sqrt 3),
      (1 / Real.sqrt 3) • octJ, (1 / Real.sqrt 3) • octK]
    let pQuat : Fin 4 → Albert := ![fixedS 0, fixedS 1, fixedS 2, qD]
    (∀ i, IsAtom (pQuat i)) ∧
      (∀ i j, i ≠ j → pQuat i ≠ pQuat j) ∧
      albertCubicNorm (pQuat 0 + pQuat 1 + pQuat 2) = 1 / 6 ∧
      fourPointInvariant pQuat = 0 ∧
      nativeGlennieF ((2 : ℝ) • pQuat 0 - albertUnit) ((2 : ℝ) • pQuat 1 - albertUnit)
        ((2 : ℝ) • pQuat 2 - albertUnit) ((2 : ℝ) • pQuat 3 - albertUnit) = 0 := by
  intro qD pQuat
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnormD : (1 / Real.sqrt 3) ^ 2 + octNormSq ((1 / Real.sqrt 3) • octJ) +
      octNormSq ((1 / Real.sqrt 3) • octK) = 1 := by
    rw [octNormSq_smul, octNormSq_smul, octNormSq_J_chk, octNormSq_K_chk, div_pow, one_pow, hs3]
    norm_num
  have hqD_atom : IsAtom qD := octDyad_real0_isAtom _ _ _ hnormD
  have hatom : ∀ i, IsAtom (pQuat i) := fun i => by
    fin_cases i
    · exact fixedS_isAtom 0
    · exact fixedS_isAtom 1
    · exact fixedS_isAtom 2
    · exact hqD_atom
  have hp_mem : ∀ i, pQuat i ∈ standardQuaternionicWindow.subalgebra.carrier := fun i => by
    apply mem_standardQuaternionicWindow_of_snd_zero
    intro k
    fin_cases i
    · rfl
    · fin_cases k
      · change ((1 / 2 : ℝ) • (octonionScalar 1 : Octonion)).2 = 0
        rw [oct_smul_snd]; exact smul_zero _
      · change ((1 / 2 : ℝ) • (0 : Octonion)).2 = 0
        rw [oct_smul_snd]; exact smul_zero _
      · change ((1 / 2 : ℝ) • (0 : Octonion)).2 = 0
        rw [oct_smul_snd]; exact smul_zero _
    · fin_cases k
      · change ((1 / 3 : ℝ) • (-octI : Octonion)).2 = 0
        rw [oct_smul_snd, oct_neg_snd]; simp [octI]
      · change ((1 / 3 : ℝ) • (octonionScalar 1 : Octonion)).2 = 0
        rw [oct_smul_snd]; simp [octonionScalar]
      · change ((1 / 3 : ℝ) • (octI : Octonion)).2 = 0
        rw [oct_smul_snd]; simp [octI]
    · fin_cases k
      · apply octonionMul_snd_eq_zero rfl
        apply octonionConj_snd_eq_zero
        change ((1 / Real.sqrt 3) • octJ).2 = 0
        rw [oct_smul_snd]; exact smul_zero _
      · apply octonionMul_snd_eq_zero rfl
        apply octonionConj_snd_eq_zero
        change ((1 / Real.sqrt 3) • octK).2 = 0
        rw [oct_smul_snd]; exact smul_zero _
      · apply octonionMul_snd_eq_zero
        · change ((1 / Real.sqrt 3) • octJ).2 = 0
          rw [oct_smul_snd]; exact smul_zero _
        · apply octonionConj_snd_eq_zero
          change ((1 / Real.sqrt 3) • octK).2 = 0
          rw [oct_smul_snd]; exact smul_zero _
  have hF0 :
      nativeGlennieF ((2 : ℝ) • pQuat 0 - albertUnit) ((2 : ℝ) • pQuat 1 - albertUnit)
        ((2 : ℝ) • pQuat 2 - albertUnit) ((2 : ℝ) • pQuat 3 - albertUnit) = 0 :=
    glennie_of_quatWindow standardQuaternionicWindow pQuat hp_mem
  have hA0 : fourPointInvariant pQuat = 0 := by
    have hvec : ![pQuat 0, pQuat 1, pQuat 2, pQuat 3] = pQuat := by
      ext i; fin_cases i <;> rfl
    rw [← hvec]
    exact (thm_glennie_eq_zero_iff (pQuat 0) (pQuat 1) (pQuat 2) (pQuat 3)
      (hatom 0) (hatom 1) (hatom 2) (hatom 3)).1 hF0
  have h0d : (pQuat 0).1 0 = 1 := rfl
  have h1d0 : (pQuat 1).1 0 = 1 / 2 := by
    change (1 / 2 : ℝ) * 1 = 1 / 2; norm_num
  have h1d2 : (pQuat 1).1 2 = 0 := by
    change (1 / 2 : ℝ) * 0 = 0; norm_num
  have h2d0 : (pQuat 2).1 0 = 1 / 3 := by
    change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
  have h2d2 : (pQuat 2).1 2 = 1 / 3 := by
    change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
  have h3d0 : (pQuat 3).1 0 = 1 / 3 := by
    change octNormSq (octonionScalar (1 / Real.sqrt 3)) = 1 / 3
    rw [octNormSq_scalar_chk, div_pow, one_pow, hs3]
  have h3d2 : (pQuat 3).1 2 = 1 / 3 := by
    change octNormSq ((1 / Real.sqrt 3) • octK) = 1 / 3
    rw [octNormSq_smul, octNormSq_K_chk, div_pow, one_pow, hs3]; norm_num
  have h2im : ((pQuat 2).2 0).1.imI = -1 / 3 := by
    change ((1 / 3 : ℝ) * (-octI.1.imI)) = -1 / 3
    simp [octI]; norm_num
  have h3im : ((pQuat 3).2 0).1.imI = 0 := by
    change (octonionMul (octonionScalar (1 / Real.sqrt 3))
      (octonionConj ((1 / Real.sqrt 3) • octJ))).1.imI = 0
    rw [octonionMul_scalar_left, octonionConj_smul, oct_smul_fst, oct_smul_fst,
      quat_smul_imI, quat_smul_imI]
    have hj : (octonionConj octJ).1.imI = 0 := by simp [octonionConj, octJ]
    rw [hj, mul_zero, mul_zero]
  have h01 : pQuat 0 ≠ pQuat 1 := fun h => by
    have hc := congrArg (fun a : Albert => a.1 0) h; linarith [h0d, h1d0]
  have h02 : pQuat 0 ≠ pQuat 2 := fun h => by
    have hc := congrArg (fun a : Albert => a.1 0) h; linarith [h0d, h2d0]
  have h03 : pQuat 0 ≠ pQuat 3 := fun h => by
    have hc := congrArg (fun a : Albert => a.1 0) h; linarith [h0d, h3d0]
  have h12 : pQuat 1 ≠ pQuat 2 := fun h => by
    have hc := congrArg (fun a : Albert => a.1 2) h; linarith [h1d2, h2d2]
  have h13 : pQuat 1 ≠ pQuat 3 := fun h => by
    have hc := congrArg (fun a : Albert => a.1 2) h; linarith [h1d2, h3d2]
  have h23 : pQuat 2 ≠ pQuat 3 := fun h => by
    have hc := congrArg (fun a : Albert => (a.2 0).1.imI) h; linarith [h2im, h3im]
  have hdist : ∀ i j, i ≠ j → pQuat i ≠ pQuat j := by
    intro i j hij
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> simp
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
    · exact absurd rfl hij
    · exact h01
    · exact h02
    · exact h03
    · exact h01.symm
    · exact absurd rfl hij
    · exact h12
    · exact h13
    · exact h02.symm
    · exact h12.symm
    · exact absurd rfl hij
    · exact h23
    · exact h03.symm
    · exact h13.symm
    · exact h23.symm
    · exact absurd rfl hij
  exact ⟨hatom, hdist, albertCubicNorm_fixedS_ABC, hA0, hF0⟩

/-! ## Section 2: `cor:so:residual` Non-Vacuity on Actual Projective Equalities (`eq:cer:extraeq`) -/

/-- Repetition equality `Pr(0, 0) - Pr(0) = 0`. -/
def cRep : Word (Fin 2) →₀ ℝ :=
  Finsupp.single [(0, true), (0, true)] 1 - Finsupp.single [(0, true)] 1

/-- Second `eq:cer:extraeq` equality: `Pr(0, 1, 0̄) - Pr(0, 1̄, 0̄) = 0`. -/
def cExtra2 : Word (Fin 2) →₀ ℝ :=
  Finsupp.single [(0, true), (1, true), (0, false)] 1 -
    Finsupp.single [(0, true), (1, false), (0, false)] 1

/-- First `eq:cer:extraeq` equality:
`(Pr(0̄, 1) - Pr(0, 1) - Pr(1)) - (Pr(1̄, 0) - Pr(1, 0) - Pr(0)) = 0`. -/
def cExtra1 : Word (Fin 2) →₀ ℝ :=
  Finsupp.single [(0, false), (1, true)] 1 - Finsupp.single [(0, true), (1, true)] 1 -
    Finsupp.single [(1, true)] 1 - Finsupp.single [(1, false), (0, true)] 1 +
    Finsupp.single [(1, true), (0, true)] 1 + Finsupp.single [(0, true)] 1

private theorem isProjectiveEquality_of_wordSum {n : ℕ} (c : Word (Fin n) →₀ ℝ)
    (h : ∀ (N : ℕ) (P : Fin n → Matrix (Fin N) (Fin N) ℝ),
      (∀ k, (P k)ᵀ = P k ∧ P k * P k = P k) →
      c.sum (fun w a => a • wordOperator P w) = 0) :
    IsProjectiveEquality c := by
  intro N P hP v _
  have hsum : c.sum (fun w a => a * dotProduct v (wordOperator P w *ᵥ v)) =
      dotProduct v ((c.sum (fun w a => a • wordOperator P w)) *ᵥ v) := by
    rw [Finsupp.sum, Finsupp.sum]
    clear h
    have hmul : (∑ x ∈ c.support, c x • wordOperator P x) *ᵥ v =
        ∑ x ∈ c.support, (c x • wordOperator P x) *ᵥ v := by
      induction c.support using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Matrix.add_mulVec, ih, Finset.sum_insert ha]
    rw [hmul, dotProduct_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hsum, h N P hP, Matrix.zero_mulVec, dotProduct_zero]

private theorem wordOperator_matrix_eq_wordQuad {n N : ℕ}
    (P : Fin n → Matrix (Fin N) (Fin N) ℝ)
    (hT : ∀ k, (P k)ᵀ = P k) (w : Word (Fin n)) :
    wordOperator P w = wordQuadOperator P w := by
  refine (wordQuadOperator_eq_wordOperator P (fun k => ?_) w).symm
  ext i j
  simpa [Matrix.star_apply] using congrFun (congrFun (hT k) i) j

theorem cRep_isProjectiveEquality : IsProjectiveEquality cRep := by
  apply isProjectiveEquality_of_wordSum
  intro N P hP
  have hT : ∀ k, (P k)ᵀ = P k := fun k => (hP k).1
  have h00 : P 0 * P 0 = P 0 := (hP 0).2
  rw [cRep, Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _)]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  rw [one_smul, one_smul, wordOperator_matrix_eq_wordQuad P hT,
    wordOperator_matrix_eq_wordQuad P hT]
  simp only [wordQuadOperator, algebraicOutcome, ite_true, ite_false, Bool.false_eq_true,
    mul_one, one_mul, h00, sub_self]

theorem cExtra2_isProjectiveEquality : IsProjectiveEquality cExtra2 := by
  apply isProjectiveEquality_of_wordSum
  intro N P hP
  have hT : ∀ k, (P k)ᵀ = P k := fun k => (hP k).1
  have h00 : P 0 * P 0 = P 0 := (hP 0).2
  have h11 : P 1 * P 1 = P 1 := (hP 1).2
  rw [cExtra2, Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _)]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  rw [one_smul, one_smul, wordOperator_matrix_eq_wordQuad P hT,
    wordOperator_matrix_eq_wordQuad P hT]
  simp only [wordQuadOperator, algebraicOutcome, ite_true, ite_false, Bool.false_eq_true,
    mul_one, one_mul]
  have h0_sub : (1 - P 0) * (1 - P 0) = 1 - P 0 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h00]; abel
  have h1_sub : (1 - P 1) * (1 - P 1) = 1 - P 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h11]; abel
  have hinnerL : P 1 * ((1 - P 0) * (1 - P 0)) * P 1 = P 1 - P 1 * P 0 * P 1 := by
    rw [h0_sub]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h11]
  have hinnerR : (1 - P 1) * ((1 - P 0) * (1 - P 0)) * (1 - P 1) =
      (1 - P 1) - (1 - P 1) * P 0 * (1 - P 1) := by
    rw [h0_sub, Matrix.mul_sub (1 - P 1) 1 (P 0), Matrix.mul_one, Matrix.sub_mul, h1_sub]
  have hL :
      P 0 * (P 1 * ((1 - P 0) * (1 - P 0)) * P 1) * P 0 =
        P 0 * P 1 * P 0 - P 0 * P 1 * P 0 * P 1 * P 0 := by
    rw [hinnerL]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hR :
      P 0 * ((1 - P 1) * ((1 - P 0) * (1 - P 0)) * (1 - P 1)) * P 0 =
        P 0 * P 1 * P 0 - P 0 * P 1 * P 0 * P 1 * P 0 := by
    rw [hinnerR]
    have hA : P 0 * (1 - P 1) * P 0 = P 0 - P 0 * P 1 * P 0 := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h00]
    have hB : P 0 * ((1 - P 1) * P 0 * (1 - P 1)) * P 0 =
        (P 0 - P 0 * P 1 * P 0) - (P 0 * P 1 * P 0 - P 0 * P 1 * P 0 * P 1 * P 0) := by
      have hm1 : P 0 * ((1 - P 1) * P 0) = P 0 - P 0 * P 1 * P 0 := by
        rw [← Matrix.mul_assoc]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h00]
      have h10 : (1 - P 1) * P 0 = P 0 - P 1 * P 0 := by
        rw [Matrix.sub_mul, Matrix.one_mul]
      have hm_aux : (P 0 * P 1 * P 0) * P 0 = P 0 * P 1 * P 0 := by
        rw [Matrix.mul_assoc (P 0 * P 1) (P 0) (P 0), h00]
      have hm2 : (P 0 - P 0 * P 1 * P 0) * ((1 - P 1) * P 0) =
          (P 0 - P 0 * P 1 * P 0) - (P 0 * P 1 * P 0 - P 0 * P 1 * P 0 * P 1 * P 0) := by
        calc
          (P 0 - P 0 * P 1 * P 0) * ((1 - P 1) * P 0)
            = (P 0 - P 0 * P 1 * P 0) * (P 0 - P 1 * P 0) := by rw [h10]
          _ = P 0 * P 0 - P 0 * (P 1 * P 0) - (P 0 * P 1 * P 0) * P 0 +
                (P 0 * P 1 * P 0) * (P 1 * P 0) := by
                simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
          _ = (P 0 - P 0 * P 1 * P 0) - (P 0 * P 1 * P 0 - P 0 * P 1 * P 0 * P 1 * P 0) := by
                rw [h00, hm_aux]; simp only [Matrix.mul_assoc]; abel
      calc
        P 0 * ((1 - P 1) * P 0 * (1 - P 1)) * P 0
          = P 0 * ((1 - P 1) * P 0) * ((1 - P 1) * P 0) := by simp only [Matrix.mul_assoc]
        _ = (P 0 - P 0 * P 1 * P 0) * ((1 - P 1) * P 0) := by rw [hm1]
        _ = _ := hm2
    calc
      P 0 * ((1 - P 1) - (1 - P 1) * P 0 * (1 - P 1)) * P 0
        = P 0 * (1 - P 1) * P 0 - P 0 * ((1 - P 1) * P 0 * (1 - P 1)) * P 0 := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = (P 0 - P 0 * P 1 * P 0) -
          ((P 0 - P 0 * P 1 * P 0) - (P 0 * P 1 * P 0 - P 0 * P 1 * P 0 * P 1 * P 0)) := by
          rw [hA, hB]
      _ = P 0 * P 1 * P 0 - P 0 * P 1 * P 0 * P 1 * P 0 := by abel
  rw [hL, hR, sub_self]

theorem cExtra1_isProjectiveEquality : IsProjectiveEquality cExtra1 := by
  apply isProjectiveEquality_of_wordSum
  intro N P hP
  have hT : ∀ k, (P k)ᵀ = P k := fun k => (hP k).1
  have h00 : P 0 * P 0 = P 0 := (hP 0).2
  have h11 : P 1 * P 1 = P 1 := (hP 1).2
  rw [cExtra1,
    Finsupp.sum_add_index (fun _ => by simp) (fun _ a b => by simp [add_smul]),
    Finsupp.sum_add_index (fun _ => by simp) (fun _ a b => by simp [add_smul]),
    Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _),
    Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _),
    Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp only [one_smul, wordOperator_matrix_eq_wordQuad P hT, wordQuadOperator, algebraicOutcome,
    ite_true, ite_false, Bool.false_eq_true, mul_one, one_mul, h00, h11]
  have hs0 : (1 - P 0) * P 1 * (1 - P 0) = P 1 - P 0 * P 1 - P 1 * P 0 + P 0 * P 1 * P 0 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hs1 : (1 - P 1) * P 0 * (1 - P 1) = P 0 - P 1 * P 0 - P 0 * P 1 + P 1 * P 0 * P 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [hs0, hs1]
  abel

/-- Smooth curve of atoms `(p₀, p₁(t))` based in `standardComplexWindow` and leaving it for `t ≠ 0`. -/
def extraEqCurve : Fin 2 → ℝ → Albert
  | 0, _ => diagAtom 0
  | 1, t =>
    let c := (1 - t ^ 2) / (1 + t ^ 2)
    let s := (2 * t) / (1 + t ^ 2)
    octDyad ![octonionScalar c, s • octL, 0]

private theorem weierstrass_normSq (t : ℝ) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + ((2 * t) / (1 + t ^ 2)) ^ 2 = 1 := by
  have hpos : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem contDiff_weierstrass_c : ContDiff ℝ 3 (fun t : ℝ => (1 - t ^ 2) / (1 + t ^ 2)) :=
  (contDiff_const.sub (contDiff_id.pow 2)).div (contDiff_const.add (contDiff_id.pow 2))
    (fun t => by positivity)

private theorem contDiff_weierstrass_s : ContDiff ℝ 3 (fun t : ℝ => (2 * t) / (1 + t ^ 2)) :=
  (contDiff_const.mul contDiff_id).div (contDiff_const.add (contDiff_id.pow 2))
    (fun t => by positivity)

theorem extraEqCurve_isAtom (k : Fin 2) (t : ℝ) : IsAtom (extraEqCurve k t) := by
  fin_cases k
  · exact diagAtom_isAtom 0
  · apply octDyad_real0_isAtom
    rw [octNormSq_smul, octNormSq_L_chk, octNormSq_zero_chk]
    simpa [mul_one, add_zero] using weierstrass_normSq t

theorem extraEqCurve_contDiff (k : Fin 2) : ContDiff ℝ 3 (extraEqCurve k) := by
  have hk_cases : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  rcases hk_cases with rfl | rfl
  · exact contDiff_const
  · let eL : Albert := (0, ![octL, 0, 0])
    have hconjL : octonionConj octL = -octL := by
      have h1 : (-octL).1 = 0 := by rw [oct_neg_fst]; simp [octL]
      have h2 : (-octL).2 = -octL.2 := oct_neg_snd octL
      apply oct_ext_chk <;> (simp only [h1, h2]; simp [octonionConj, octL])
    have hdecomp : extraEqCurve 1 = fun t : ℝ =>
        (((1 - t ^ 2) / (1 + t ^ 2)) ^ 2) • diagAtom 0 +
        (((2 * t) / (1 + t ^ 2)) ^ 2) • diagAtom 1 +
        (-(((1 - t ^ 2) / (1 + t ^ 2)) * ((2 * t) / (1 + t ^ 2)))) • eL := by
      funext t
      apply albert_ext_chk
      · rw [albert_add_fst_chk, albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
          albert_smul_fst_chk]
        change octNormSq (octonionScalar ((1 - t ^ 2) / (1 + t ^ 2))) =
          ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 * 1 + ((2 * t) / (1 + t ^ 2)) ^ 2 * 0 +
            -(((1 - t ^ 2) / (1 + t ^ 2)) * ((2 * t) / (1 + t ^ 2))) * 0
        rw [octNormSq_scalar_chk]; ring
      · rw [albert_add_fst_chk, albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
          albert_smul_fst_chk]
        change octNormSq (((2 * t) / (1 + t ^ 2)) • octL) =
          ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 * 0 + ((2 * t) / (1 + t ^ 2)) ^ 2 * 1 +
            -(((1 - t ^ 2) / (1 + t ^ 2)) * ((2 * t) / (1 + t ^ 2))) * 0
        rw [octNormSq_smul, octNormSq_L_chk]; ring
      · rw [albert_add_fst_chk, albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
          albert_smul_fst_chk]
        change octNormSq (0 : Octonion) =
          ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 * 0 + ((2 * t) / (1 + t ^ 2)) ^ 2 * 0 +
            -(((1 - t ^ 2) / (1 + t ^ 2)) * ((2 * t) / (1 + t ^ 2))) * 0
        rw [octNormSq_zero_chk]; ring
      · rw [albert_add_snd_chk, albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
          albert_smul_snd_chk]
        change octonionMul (octonionScalar ((1 - t ^ 2) / (1 + t ^ 2)))
            (octonionConj (((2 * t) / (1 + t ^ 2)) • octL)) =
          ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 • (0 : Octonion) +
            ((2 * t) / (1 + t ^ 2)) ^ 2 • (0 : Octonion) +
            (-(((1 - t ^ 2) / (1 + t ^ 2)) * ((2 * t) / (1 + t ^ 2)))) • octL
        rw [octonionMul_scalar_left, octonionConj_smul, hconjL]
        module
      · rw [albert_add_snd_chk, albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
          albert_smul_snd_chk]
        change octonionMul (octonionScalar ((1 - t ^ 2) / (1 + t ^ 2))) (octonionConj (0 : Octonion)) =
          ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 • (0 : Octonion) +
            ((2 * t) / (1 + t ^ 2)) ^ 2 • (0 : Octonion) +
            (-(((1 - t ^ 2) / (1 + t ^ 2)) * ((2 * t) / (1 + t ^ 2)))) • (0 : Octonion)
        rw [octonionConj_zero, octonionMul_zero_right]
        module
      · rw [albert_add_snd_chk, albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
          albert_smul_snd_chk]
        change octonionMul (((2 * t) / (1 + t ^ 2)) • octL) (octonionConj (0 : Octonion)) =
          ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 • (0 : Octonion) +
            ((2 * t) / (1 + t ^ 2)) ^ 2 • (0 : Octonion) +
            (-(((1 - t ^ 2) / (1 + t ^ 2)) * ((2 * t) / (1 + t ^ 2)))) • (0 : Octonion)
        rw [octonionConj_zero, octonionMul_zero_right]
        module
    rw [hdecomp]
    exact ((contDiff_weierstrass_c.pow 2).smul contDiff_const).add
      ((contDiff_weierstrass_s.pow 2).smul contDiff_const) |>.add
      (((contDiff_weierstrass_c.mul contDiff_weierstrass_s).neg).smul contDiff_const)

theorem extraEqCurve_base (k : Fin 2) : standardComplexWindow.Contains (extraEqCurve k 0) := by
  fin_cases k
  · rw [standardComplexWindow_contains_iff]
    simp [extraEqCurve, diagAtom]
  · rw [standardComplexWindow_contains_iff]
    have hs0 : ((2 * (0 : ℝ)) / (1 + (0 : ℝ) ^ 2)) • octL = 0 := by
      rw [mul_zero, zero_div, zero_smul]
    have h0 : (extraEqCurve 1 0).2 0 = 0 := by
      change octonionMul (octonionScalar ((1 - (0 : ℝ) ^ 2) / (1 + (0 : ℝ) ^ 2)))
        (octonionConj (((2 * (0 : ℝ)) / (1 + (0 : ℝ) ^ 2)) • octL)) = 0
      rw [hs0, octonionConj_zero, octonionMul_zero_right]
    have h1 : (extraEqCurve 1 0).2 1 = 0 := by
      change octonionMul (octonionScalar ((1 - (0 : ℝ) ^ 2) / (1 + (0 : ℝ) ^ 2)))
        (octonionConj 0) = 0
      rw [octonionConj_zero, octonionMul_zero_right]
    have h2 : (extraEqCurve 1 0).2 2 = 0 := by
      change octonionMul (((2 * (0 : ℝ)) / (1 + (0 : ℝ) ^ 2)) • octL) (octonionConj 0) = 0
      rw [octonionConj_zero, octonionMul_zero_right]
    simp [h0, h1, h2]

theorem cor_so_residual_nonvacuity_extraeq :
    (∀ k, standardComplexWindow.Contains (extraEqCurve k 0)) ∧
      ¬ standardComplexWindow.Contains (extraEqCurve 1 (1 / 2)) ∧
      (∀ c ∈ [cRep, cExtra1, cExtra2],
        let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => extraEqCurve k t)
        let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
        ContDiff ℝ 3 r ∧ r 0 = 0 ∧ deriv r 0 = 0 ∧
          (∀ w : Albert, standardComplexWindow.Contains w → tracePairing w Q = 0) ∧
          ((fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3)) ∧
          (∀ ρ : Albert, standardComplexWindow.Contains ρ →
            (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => extraEqCurve k t) ρ w)) =O[𝓝 0]
              (fun t => t ^ 3))) := by
  refine ⟨extraEqCurve_base, ?_, ?_⟩
  · intro hmem
    rw [standardComplexWindow_contains_iff] at hmem
    have h0 := hmem.2.2.1
    have hv := congrArg (fun q : Quaternion ℝ => q.re) h0
    change (octonionMul (octonionScalar ((1 - (1 / 2 : ℝ) ^ 2) / (1 + (1 / 2 : ℝ) ^ 2)))
      (octonionConj (((2 * (1 / 2 : ℝ)) / (1 + (1 / 2 : ℝ) ^ 2)) • octL))).2.re = 0 at hv
    rw [octonionMul_scalar_left, octonionConj_smul, oct_smul_snd, oct_smul_snd,
      quat_smul_re, quat_smul_re] at hv
    have hLre : (octonionConj octL).2.re = -1 := by
      change (-(octL.2)).re = -1
      norm_num [octL]
    rw [hLre] at hv
    norm_num at hv
  · intro c hc
    have hproj : IsProjectiveEquality c := by
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact cRep_isProjectiveEquality
      · rcases List.mem_cons.mp hc1 with rfl | hc2
        · exact cExtra1_isProjectiveEquality
        · rcases List.mem_cons.mp hc2 with rfl | hc3
          · exact cExtra2_isProjectiveEquality
          · exact absurd hc3 (List.not_mem_nil)
    obtain ⟨hr, hr0, hdr0, hQ, hbigO, _, hprob⟩ :=
      cor_so_residual_of_atoms standardComplexWindow c hproj extraEqCurve
        extraEqCurve_contDiff extraEqCurve_isAtom extraEqCurve_base
    exact ⟨hr, hr0, hdr0, hQ, hbigO, hprob⟩

/-! ## Section 3: Off-Window State Sharpness (`Q ≠ 0`, `ρ ∉ W`, `⟨ρ, r(t)⟩ ≠ O(t³)`) -/

def subJ {n : ℕ} (x y : JTerm n) : JTerm n := .add x (.smul (-1) y)
def twoJ {n : ℕ} (x : JTerm n) : JTerm n := .add x x
def threeJ {n : ℕ} (x : JTerm n) : JTerm n := .add (.add x x) x
def fourJ {n : ℕ} (x : JTerm n) : JTerm n := .add (.add x x) (.add x x)

def dopJ {n : ℕ} (x y z : JTerm n) : JTerm n :=
  fourJ (subJ (.mul x (.mul y z)) (.mul y (.mul x z)))

def upolJ {n : ℕ} (w w' z : JTerm n) : JTerm n :=
  subJ (.add (.mul w (.mul w' z)) (.mul w' (.mul w z))) (.mul (.mul w w') z)

def ubrJ {n : ℕ} (x1 x2 y1 y2 z : JTerm n) : JTerm n :=
  subJ (fourJ (upolJ (.mul x1 y1) (.mul x2 y2) z))
    (twoJ (.add (upolJ x1 x2 (upolJ y1 y2 z)) (upolJ y1 y2 (upolJ x1 x2 z))))

def phiJ {n : ℕ} (x1 x2 x3 y1 y2 y3 z : JTerm n) : JTerm n :=
  .add (dopJ x1 y1 (dopJ x2 y2 (dopJ x3 y3 z))) (threeJ (dopJ x1 y1 (ubrJ x2 x3 y2 y3 z)))

def glennieTermJ {n : ℕ} (d x1 x2 x3 y1 y2 y3 : JTerm n) : JTerm n :=
  subJ (phiJ x1 x2 x3 y1 y2 y3 (.mul d d)) (twoJ (.mul d (phiJ x1 x2 x3 y1 y2 y3 d)))

def glennieFJ {n : ℕ} (a b c d : JTerm n) : JTerm n :=
  .add (.add (.add (glennieTermJ d a b b a c c) (glennieTermJ d a b b c a c))
      (.add (glennieTermJ d a b b c c a) (glennieTermJ d b a b a c c)))
    (.add (.add (glennieTermJ d b a b c a c) (glennieTermJ d b a b c c a))
      (.add (.add (glennieTermJ d b b a a c c) (glennieTermJ d b b a c a c))
        (glennieTermJ d b b a c c a)))

private theorem evalAlbert_subJ {n : ℕ} (p : Fin n → Albert) (x y : JTerm n) :
    (subJ x y).evalAlbert p = nativeOps.sub (x.evalAlbert p) (y.evalAlbert p) := by
  simp only [subJ, JTerm.evalAlbert, neg_one_smul, ← sub_eq_add_neg]; rfl

private theorem evalAlbert_twoJ {n : ℕ} (p : Fin n → Albert) (x : JTerm n) :
    (twoJ x).evalAlbert p = two nativeOps (x.evalAlbert p) := rfl

private theorem evalAlbert_threeJ {n : ℕ} (p : Fin n → Albert) (x : JTerm n) :
    (threeJ x).evalAlbert p = three nativeOps (x.evalAlbert p) := rfl

private theorem evalAlbert_fourJ {n : ℕ} (p : Fin n → Albert) (x : JTerm n) :
    (fourJ x).evalAlbert p = four nativeOps (x.evalAlbert p) := rfl

private theorem evalAlbert_dopJ {n : ℕ} (p : Fin n → Albert) (x y z : JTerm n) :
    (dopJ x y z).evalAlbert p =
      Dop nativeOps (x.evalAlbert p) (y.evalAlbert p) (z.evalAlbert p) := by
  simp only [dopJ, Dop, evalAlbert_fourJ, evalAlbert_subJ, JTerm.evalAlbert]; rfl

private theorem evalAlbert_upolJ {n : ℕ} (p : Fin n → Albert) (w w' z : JTerm n) :
    (upolJ w w' z).evalAlbert p =
      Upol nativeOps (w.evalAlbert p) (w'.evalAlbert p) (z.evalAlbert p) := by
  simp only [upolJ, Upol, evalAlbert_subJ, JTerm.evalAlbert]; rfl

private theorem evalAlbert_ubrJ {n : ℕ} (p : Fin n → Albert) (x1 x2 y1 y2 z : JTerm n) :
    (ubrJ x1 x2 y1 y2 z).evalAlbert p =
      Ubr nativeOps (x1.evalAlbert p) (x2.evalAlbert p) (y1.evalAlbert p) (y2.evalAlbert p)
        (z.evalAlbert p) := by
  simp only [ubrJ, Ubr, evalAlbert_subJ, evalAlbert_fourJ, evalAlbert_twoJ, evalAlbert_upolJ,
    JTerm.evalAlbert]; rfl

private theorem evalAlbert_phiJ {n : ℕ} (p : Fin n → Albert) (x1 x2 x3 y1 y2 y3 z : JTerm n) :
    (phiJ x1 x2 x3 y1 y2 y3 z).evalAlbert p =
      Phi nativeOps (x1.evalAlbert p) (x2.evalAlbert p) (x3.evalAlbert p)
        (y1.evalAlbert p) (y2.evalAlbert p) (y3.evalAlbert p) (z.evalAlbert p) := by
  simp only [phiJ, Phi, evalAlbert_dopJ, evalAlbert_threeJ, evalAlbert_ubrJ, JTerm.evalAlbert]; rfl

private theorem evalAlbert_glennieTermJ {n : ℕ} (p : Fin n → Albert)
    (d x1 x2 x3 y1 y2 y3 : JTerm n) :
    (glennieTermJ d x1 x2 x3 y1 y2 y3).evalAlbert p =
      glennieTerm nativeOps (d.evalAlbert p) (x1.evalAlbert p) (x2.evalAlbert p)
        (x3.evalAlbert p) (y1.evalAlbert p) (y2.evalAlbert p) (y3.evalAlbert p) := by
  simp only [glennieTermJ, glennieTerm, evalAlbert_subJ, evalAlbert_twoJ, evalAlbert_phiJ,
    JTerm.evalAlbert]; rfl

private theorem evalAlbert_glennieFJ {n : ℕ} (p : Fin n → Albert) (a b c d : JTerm n) :
    (glennieFJ a b c d).evalAlbert p =
      glennieF nativeOps (a.evalAlbert p) (b.evalAlbert p) (c.evalAlbert p) (d.evalAlbert p) := by
  simp only [glennieFJ, glennieF, evalAlbert_glennieTermJ, JTerm.evalAlbert]; rfl

private theorem evalS_subJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A)
    (x y : JTerm n) :
    (subJ x y).evalS P = (specialOps A).sub (x.evalS P) (y.evalS P) := by
  simp only [subJ, JTerm.evalS, neg_one_smul, ← sub_eq_add_neg]; rfl

private theorem evalS_twoJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A) (x : JTerm n) :
    (twoJ x).evalS P = two (specialOps A) (x.evalS P) := rfl

private theorem evalS_threeJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A) (x : JTerm n) :
    (threeJ x).evalS P = three (specialOps A) (x.evalS P) := rfl

private theorem evalS_fourJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A) (x : JTerm n) :
    (fourJ x).evalS P = four (specialOps A) (x.evalS P) := rfl

private theorem evalS_dopJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A)
    (x y z : JTerm n) :
    (dopJ x y z).evalS P = Dop (specialOps A) (x.evalS P) (y.evalS P) (z.evalS P) := by
  simp only [dopJ, Dop, evalS_fourJ, evalS_subJ, JTerm.evalS]; rfl

private theorem evalS_upolJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A)
    (w w' z : JTerm n) :
    (upolJ w w' z).evalS P = Upol (specialOps A) (w.evalS P) (w'.evalS P) (z.evalS P) := by
  simp only [upolJ, Upol, evalS_subJ, JTerm.evalS]; rfl

private theorem evalS_ubrJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A)
    (x1 x2 y1 y2 z : JTerm n) :
    (ubrJ x1 x2 y1 y2 z).evalS P =
      Ubr (specialOps A) (x1.evalS P) (x2.evalS P) (y1.evalS P) (y2.evalS P) (z.evalS P) := by
  simp only [ubrJ, Ubr, evalS_subJ, evalS_fourJ, evalS_twoJ, evalS_upolJ, JTerm.evalS]; rfl

private theorem evalS_phiJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A)
    (x1 x2 x3 y1 y2 y3 z : JTerm n) :
    (phiJ x1 x2 x3 y1 y2 y3 z).evalS P =
      Phi (specialOps A) (x1.evalS P) (x2.evalS P) (x3.evalS P)
        (y1.evalS P) (y2.evalS P) (y3.evalS P) (z.evalS P) := by
  simp only [phiJ, Phi, evalS_dopJ, evalS_threeJ, evalS_ubrJ, JTerm.evalS]; rfl

private theorem evalS_glennieTermJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A)
    (d x1 x2 x3 y1 y2 y3 : JTerm n) :
    (glennieTermJ d x1 x2 x3 y1 y2 y3).evalS P =
      glennieTerm (specialOps A) (d.evalS P) (x1.evalS P) (x2.evalS P)
        (x3.evalS P) (y1.evalS P) (y2.evalS P) (y3.evalS P) := by
  simp only [glennieTermJ, glennieTerm, evalS_subJ, evalS_twoJ, evalS_phiJ, JTerm.evalS]; rfl

private theorem evalS_glennieFJ {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A)
    (a b c d : JTerm n) :
    (glennieFJ a b c d).evalS P =
      glennieF (specialOps A) (a.evalS P) (b.evalS P) (c.evalS P) (d.evalS P) := by
  simp only [glennieFJ, glennieF, evalS_glennieTermJ, JTerm.evalS]; rfl

/-- `JTerm 4` encoding `F(2p₀ - e, 2p₁ - e, 2p₂ - e, 2p₃ - e)`. -/
def glennieSymmJTerm : JTerm 4 :=
  glennieFJ
    (subJ (.smul 2 (.var 0)) .one)
    (subJ (.smul 2 (.var 1)) .one)
    (subJ (.smul 2 (.var 2)) .one)
    (subJ (.smul 2 (.var 3)) .one)

theorem evalAlbert_glennieSymmJTerm (p : Fin 4 → Albert) :
    glennieSymmJTerm.evalAlbert p =
      nativeGlennieF ((2 : ℝ) • p 0 - albertUnit) ((2 : ℝ) • p 1 - albertUnit)
        ((2 : ℝ) • p 2 - albertUnit) ((2 : ℝ) • p 3 - albertUnit) := by
  rw [glennieSymmJTerm, evalAlbert_glennieFJ]
  simp only [evalAlbert_subJ, JTerm.evalAlbert]
  rfl

theorem glennieSymmJTerm_vanishes : glennieSymmJTerm.VanishesOnSpecialIdempotents := by
  intro A _ _ P _
  have hev :
      glennieSymmJTerm.evalS P =
        glennieF (specialOps A)
          ((2 : ℝ) • P 0 - 1) ((2 : ℝ) • P 1 - 1)
          ((2 : ℝ) • P 2 - 1) ((2 : ℝ) • P 3 - 1) := by
    rw [glennieSymmJTerm, evalS_glennieFJ]
    simp only [evalS_subJ, JTerm.evalS]
    rfl
  rw [hev]
  exact special_glennieF_eq_zero _ _ _ _

private def sc4A1 : Albert := (0, ![octonionScalar 1, octonionScalar 1, 0])
private def sc4A2 : Albert := (0, ![octJ, octL, 0])
private def sc4A3 : Albert := (0, ![0, 0, octonionScalar 1])
private def sc4A4 : Albert := (0, ![0, 0, octJ - octL])
private def sc4A5 : Albert := (0, ![0, 0, octonionMul octJ octL])

/-- Smooth curve of 4 atoms based in `standardComplexWindow` at `t = 0`:
`(fixedS 0, fixedS 1, fixedS 2, p₃(t))`, with `p₃(t)` rotating out of `W` into `ℝ⟨j, ℓ⟩`. -/
def sharpnessCurve4 : Fin 4 → ℝ → Albert
  | 0, _ => fixedS 0
  | 1, _ => fixedS 1
  | 2, _ => fixedS 2
  | 3, t =>
    let c := (1 - t ^ 2) / (1 + t ^ 2)
    let s := (2 * t) / (1 + t ^ 2)
    let v1 : Octonion := (c / Real.sqrt 3) • octonionScalar 1 + (s / Real.sqrt 3) • octJ
    let v2 : Octonion := (c / Real.sqrt 3) • octonionScalar 1 + (s / Real.sqrt 3) • octL
    octDyad ![octonionScalar (1 / Real.sqrt 3), v1, v2]

private theorem sharpnessCurve4_three_eq (t : ℝ) :
    let c := (1 - t ^ 2) / (1 + t ^ 2)
    let s := (2 * t) / (1 + t ^ 2)
    sharpnessCurve4 3 t =
      (1 / 3 : ℝ) • albertUnit + (c / 3) • sc4A1 + (-(s / 3)) • sc4A2 +
        (c ^ 2 / 3) • sc4A3 + (c * s / 3) • sc4A4 + (-(s ^ 2 / 3)) • sc4A5 := by
  intro c s
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, hs3]
  have hw := weierstrass_normSq t
  have h13 : (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = 1 / 3 := by
    rw [div_mul_div_comm, one_mul, hsq3]
  have hc1 : ∀ a : ℝ, (1 / Real.sqrt 3) * (a / Real.sqrt 3) = a / 3 := fun a => by
    rw [div_mul_div_comm, one_mul, hsq3]
  have hc2 : ∀ a b : ℝ, (a / Real.sqrt 3) * (b / Real.sqrt 3) = a * b / 3 := fun a b => by
    rw [div_mul_div_comm, hsq3]
  have hdiv : ∀ x y : ℝ, (x / Real.sqrt 3) ^ 2 + (y / Real.sqrt 3) ^ 2 = (x ^ 2 + y ^ 2) / 3 := by
    intro x y; rw [div_pow, div_pow, hs3]; ring
  have hconj1 : octonionConj (octonionScalar 1) = octonionScalar 1 := by
    apply oct_ext_chk <;> simp [octonionConj, octonionScalar]
  have hconjJ : octonionConj octJ = -octJ := by
    have h1 : (-octJ).1 = -octJ.1 := oct_neg_fst octJ
    have h2 : (-octJ).2 = 0 := by rw [oct_neg_snd]; simp [octJ]
    apply oct_ext_chk <;> (simp only [h1, h2]; simp [octonionConj, octJ])
  have hconjL : octonionConj octL = -octL := by
    have h1 : (-octL).1 = 0 := by rw [oct_neg_fst]; simp [octL]
    have h2 : (-octL).2 = -octL.2 := oct_neg_snd octL
    apply oct_ext_chk <;> (simp only [h1, h2]; simp [octonionConj, octL])
  have hmul11 : octonionMul (octonionScalar 1) (octonionScalar 1) = octonionScalar 1 := by
    rw [octonionMul_scalar_left, one_smul]
  have hmul1L : octonionMul (octonionScalar 1) (-octL) = -octL := by
    rw [octonionMul_scalar_left, one_smul]
  have hmulJ1 : octonionMul octJ (octonionScalar 1) = octJ := by
    apply oct_ext_chk <;> simp [octonionMul, octonionScalar, octJ]
  have hmulJL : octonionMul octJ (-octL) = -octonionMul octJ octL := by
    have h1 : (-octonionMul octJ octL).1 = -(octonionMul octJ octL).1 :=
      oct_neg_fst (octonionMul octJ octL)
    have h2 : (-octonionMul octJ octL).2 = -(octonionMul octJ octL).2 :=
      oct_neg_snd (octonionMul octJ octL)
    have hnl1 : (-octL).1 = 0 := by rw [oct_neg_fst]; simp [octL]
    have hnl2 : (-octL).2 = -octL.2 := oct_neg_snd octL
    apply oct_ext_chk <;>
      (simp only [h1, h2]; simp only [octonionMul, hnl1, hnl2]; simp [octJ, octL])
  apply albert_ext_chk
  · rw [albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk,
      albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
      albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk]
    change octNormSq (octonionScalar (1 / Real.sqrt 3)) =
      1 / 3 * 1 + c / 3 * 0 + -(s / 3) * 0 + c ^ 2 / 3 * 0 + c * s / 3 * 0 + -(s ^ 2 / 3) * 0
    rw [octNormSq_scalar_chk, div_pow, one_pow, hs3]; ring
  · rw [albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk,
      albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
      albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk]
    change octNormSq ((c / Real.sqrt 3) • octonionScalar 1 + (s / Real.sqrt 3) • octJ) =
      1 / 3 * 1 + c / 3 * 0 + -(s / 3) * 0 + c ^ 2 / 3 * 0 + c * s / 3 * 0 + -(s ^ 2 / 3) * 0
    rw [octNormSq_scalar_add_J, hdiv c s, hw]; ring
  · rw [albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk,
      albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
      albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk]
    change octNormSq ((c / Real.sqrt 3) • octonionScalar 1 + (s / Real.sqrt 3) • octL) =
      1 / 3 * 1 + c / 3 * 0 + -(s / 3) * 0 + c ^ 2 / 3 * 0 + c * s / 3 * 0 + -(s ^ 2 / 3) * 0
    rw [octNormSq_scalar_add_L, hdiv c s, hw]; ring
  · rw [albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk,
      albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
      albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk]
    change octonionMul (octonionScalar (1 / Real.sqrt 3))
        (octonionConj ((c / Real.sqrt 3) • octonionScalar 1 + (s / Real.sqrt 3) • octJ)) =
      (1 / 3 : ℝ) • (0 : Octonion) + (c / 3) • octonionScalar 1 + (-(s / 3)) • octJ +
        (c ^ 2 / 3) • (0 : Octonion) + (c * s / 3) • (0 : Octonion) +
        (-(s ^ 2 / 3)) • (0 : Octonion)
    rw [octonionMul_scalar_left, octonionConj_add, octonionConj_smul, octonionConj_smul,
      hconj1, hconjJ, smul_add, smul_smul, smul_smul, hc1 c, hc1 s]
    module
  · rw [albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk,
      albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
      albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk]
    change octonionMul (octonionScalar (1 / Real.sqrt 3))
        (octonionConj ((c / Real.sqrt 3) • octonionScalar 1 + (s / Real.sqrt 3) • octL)) =
      (1 / 3 : ℝ) • (0 : Octonion) + (c / 3) • octonionScalar 1 + (-(s / 3)) • octL +
        (c ^ 2 / 3) • (0 : Octonion) + (c * s / 3) • (0 : Octonion) +
        (-(s ^ 2 / 3)) • (0 : Octonion)
    rw [octonionMul_scalar_left, octonionConj_add, octonionConj_smul, octonionConj_smul,
      hconj1, hconjL, smul_add, smul_smul, smul_smul, hc1 c, hc1 s]
    module
  · rw [albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk,
      albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
      albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk]
    change octonionMul ((c / Real.sqrt 3) • octonionScalar 1 + (s / Real.sqrt 3) • octJ)
        (octonionConj ((c / Real.sqrt 3) • octonionScalar 1 + (s / Real.sqrt 3) • octL)) =
      (1 / 3 : ℝ) • (0 : Octonion) + (c / 3) • (0 : Octonion) + (-(s / 3)) • (0 : Octonion) +
        (c ^ 2 / 3) • octonionScalar 1 + (c * s / 3) • (octJ - octL) +
        (-(s ^ 2 / 3)) • octonionMul octJ octL
    rw [octonionConj_add, octonionConj_smul, octonionConj_smul, hconj1, hconjL,
      octonionMul_add_left, octonionMul_add_right, octonionMul_add_right,
      octonionMul_smul_left, octonionMul_smul_right, octonionMul_smul_left, octonionMul_smul_right,
      octonionMul_smul_left, octonionMul_smul_right, octonionMul_smul_left, octonionMul_smul_right,
      hmul11, hmul1L, hmulJ1, hmulJL,
      smul_smul, smul_smul, smul_smul, smul_smul, hc2 c c, hc2 c s, hc2 s c, hc2 s s]
    have hpow2 : c * c / 3 = c ^ 2 / 3 := by ring
    have hspow2 : s * s / 3 = s ^ 2 / 3 := by ring
    have hmulsc : s * c / 3 = c * s / 3 := by ring
    rw [hpow2, hspow2, hmulsc]
    module

theorem sharpnessCurve4_isAtom (k : Fin 4) (t : ℝ) : IsAtom (sharpnessCurve4 k t) := by
  fin_cases k
  · exact fixedS_isAtom 0
  · exact fixedS_isAtom 1
  · exact fixedS_isAtom 2
  · apply octDyad_real0_isAtom
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hnorm :
        ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + ((2 * t) / (1 + t ^ 2)) ^ 2 = 1 :=
      weierstrass_normSq t
    rw [octNormSq_scalar_add_J, octNormSq_scalar_add_L]
    have hdiv : ∀ x y : ℝ, (x / Real.sqrt 3) ^ 2 + (y / Real.sqrt 3) ^ 2 = (x ^ 2 + y ^ 2) / 3 := by
      intro x y; rw [div_pow, div_pow, hs3]; ring
    rw [hdiv, hnorm]
    norm_num

theorem sharpnessCurve4_contDiff (k : Fin 4) : ContDiff ℝ 3 (sharpnessCurve4 k) := by
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
  rcases hk_cases with rfl | rfl | rfl | rfl
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const
  · have hdecomp : sharpnessCurve4 3 = fun t : ℝ =>
        let c := (1 - t ^ 2) / (1 + t ^ 2)
        let s := (2 * t) / (1 + t ^ 2)
        (1 / 3 : ℝ) • albertUnit + (c / 3) • sc4A1 + (-(s / 3)) • sc4A2 +
          (c ^ 2 / 3) • sc4A3 + (c * s / 3) • sc4A4 + (-(s ^ 2 / 3)) • sc4A5 :=
      funext sharpnessCurve4_three_eq
    rw [hdecomp]
    have hc := contDiff_weierstrass_c
    have hs := contDiff_weierstrass_s
    have h0 : ContDiff ℝ 3 (fun _ : ℝ => (1 / 3 : ℝ) • albertUnit) := contDiff_const
    have h1 : ContDiff ℝ 3 (fun t : ℝ => (((1 - t ^ 2) / (1 + t ^ 2)) / 3) • sc4A1) :=
      (hc.div_const 3).smul contDiff_const
    have h2 : ContDiff ℝ 3 (fun t : ℝ => (-(((2 * t) / (1 + t ^ 2)) / 3)) • sc4A2) :=
      ((hs.div_const 3).neg).smul contDiff_const
    have h3 : ContDiff ℝ 3 (fun t : ℝ => (((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 / 3) • sc4A3) :=
      ((hc.pow 2).div_const 3).smul contDiff_const
    have h4 : ContDiff ℝ 3
        (fun t : ℝ => (((1 - t ^ 2) / (1 + t ^ 2)) * ((2 * t) / (1 + t ^ 2)) / 3) • sc4A4) :=
      ((hc.mul hs).div_const 3).smul contDiff_const
    have h5 : ContDiff ℝ 3 (fun t : ℝ => (-(((2 * t) / (1 + t ^ 2)) ^ 2 / 3)) • sc4A5) :=
      (((hs.pow 2).div_const 3).neg).smul contDiff_const
    exact ((((h0.add h1).add h2).add h3).add h4).add h5

theorem sharpnessCurve4_base (k : Fin 4) : standardComplexWindow.Contains (sharpnessCurve4 k 0) := by
  rw [standardComplexWindow_contains_iff]
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
  rcases hk_cases with rfl | rfl | rfl | rfl
  · simp [sharpnessCurve4, fixedS, atomA, diagAtom]
  · dsimp only [sharpnessCurve4]
    have hb0 : (fixedS 1).2 0 = (1 / 2 : ℝ) • octonionScalar 1 := rfl
    have hb1 : (fixedS 1).2 1 = 0 := by
      change ((1 / 2 : ℝ) • (0 : Octonion)) = 0; exact smul_zero _
    have hb2 : (fixedS 1).2 2 = 0 := by
      change ((1 / 2 : ℝ) • (0 : Octonion)) = 0; exact smul_zero _
    rw [hb0, hb1, hb2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [oct_smul_fst, oct_smul_snd, oct_zero_fst, oct_zero_snd,
          quat_smul_imJ, quat_smul_imK];
        try simp [octonionScalar])
  · dsimp only [sharpnessCurve4]
    have hc0 : (fixedS 2).2 0 = (1 / 3 : ℝ) • (-octI) := rfl
    have hc1 : (fixedS 2).2 1 = (1 / 3 : ℝ) • octonionScalar 1 := rfl
    have hc2 : (fixedS 2).2 2 = (1 / 3 : ℝ) • octI := rfl
    rw [hc0, hc1, hc2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [oct_smul_fst, oct_smul_snd, oct_neg_fst, oct_neg_snd,
          quat_smul_imJ, quat_smul_imK];
        simp [octonionScalar, octI])
  · rw [sharpnessCurve4_three_eq 0]
    have hc0 : (1 - (0 : ℝ) ^ 2) / (1 + (0 : ℝ) ^ 2) = 1 := by norm_num
    have hs0 : (2 * (0 : ℝ)) / (1 + (0 : ℝ) ^ 2) = 0 := by norm_num
    rw [hc0, hs0]
    simp only [mul_zero, zero_div, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_smul, add_zero]
    rw [albert_add_snd_chk, albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
      albert_smul_snd_chk]
    rw [albert_add_snd_chk, albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
      albert_smul_snd_chk]
    rw [albert_add_snd_chk, albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
      albert_smul_snd_chk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [albertUnit, sc4A1, sc4A3, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd,
          oct_zero_fst, oct_zero_snd, quat_smul_imJ, quat_smul_imK];
        simp [octonionScalar])

private theorem complexToOctonion_fst (z : ℂ) :
    (complexToOctonion z).1 = ⟨z.re, z.im, 0, 0⟩ := rfl

private theorem complexToOctonion_snd (z : ℂ) :
    (complexToOctonion z).2 = 0 := rfl

private theorem fixedS_tripleDelta : tripleDelta (fixedS 0) (fixedS 1) (fixedS 2) = 1 / 216 := by
  have h0 : standardComplexWindow.Contains (fixedS 0) := sharpnessCurve4_base 0
  have h1 : standardComplexWindow.Contains (fixedS 1) := sharpnessCurve4_base 1
  have h2 : standardComplexWindow.Contains (fixedS 2) := sharpnessCurve4_base 2
  have hdet := prop_windowdet standardComplexWindow
    (fixedS_isAtom 0) (fixedS_isAtom 1) (fixedS_isAtom 2) (fixedS_isAtom 3) h0 h1 h2
  have hvec : ![fixedS 0, fixedS 1, fixedS 2, fixedS 3] = fixedS := by
    ext i; fin_cases i <;> rfl
  rw [hvec, fourPointInvariant_fixedS, windowDelta_eq_tripleDelta] at hdet
  let P3_mat : ComplexMatrix3 := mkHerm3Matrix (fun _ => (1 / 3 : ℝ)) (fun _ => 0)
  have hP3_sa : P3_mat ∈ selfAdjoint ComplexMatrix3 := by
    rw [selfAdjoint.mem_iff]
    funext i j
    rw [Matrix.star_apply]
    fin_cases i <;> fin_cases j <;> simp [P3_mat, mkHerm3Matrix] <;> apply Complex.ext <;> simp
  let P3 : Hermitian3 := ⟨P3_mat, hP3_sa⟩
  have hproj : windowProj standardComplexWindow (fixedS 3) = P3 := by
    apply standardComplexWindow.injective
    rw [standardComplexWindow_embedding_windowProj, standardComplexWindow_apply]
    dsimp only [complexHermToAlbert]
    have hd0 : (fixedS 3).1 0 = 1 / 3 := by change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
    have hd1 : (fixedS 3).1 1 = 1 / 3 := by change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
    have hd2 : (fixedS 3).1 2 = 1 / 3 := by change (1 / 3 : ℝ) * 1 = 1 / 3; norm_num
    have hu0 : (fixedS 3).2 0 = (1 / 3 : ℝ) • (-octJ) := rfl
    have hu1 : (fixedS 3).2 1 = (1 / 3 : ℝ) • (-octL) := rfl
    have hu2 : (fixedS 3).2 2 = (1 / 3 : ℝ) • (-octonionMul octJ octL) := rfl
    apply albert_ext_chk
    · change (fixedS 3).1 0 = (P3_mat 0 0).re
      rw [hd0]; simp [P3_mat, mkHerm3Matrix]
    · change (fixedS 3).1 1 = (P3_mat 1 1).re
      rw [hd1]; simp [P3_mat, mkHerm3Matrix]
    · change (fixedS 3).1 2 = (P3_mat 2 2).re
      rw [hd2]; simp [P3_mat, mkHerm3Matrix]
    · change projC ((fixedS 3).2 0) = complexToOctonion (P3_mat 0 1)
      have hp : P3_mat 0 1 = 0 := by simp [P3_mat, mkHerm3Matrix]
      rw [hp, map_zero, hu0]
      apply oct_ext_chk <;>
        (simp only [projC, oct_smul_fst, oct_neg_fst, quat_smul_re, quat_smul_imI]; simp [octJ])
    · change projC ((fixedS 3).2 1) = complexToOctonion (P3_mat 0 2)
      have hp : P3_mat 0 2 = 0 := by simp [P3_mat, mkHerm3Matrix]
      rw [hp, map_zero, hu1]
      apply oct_ext_chk <;>
        (simp only [projC, oct_smul_fst, oct_neg_fst, quat_smul_re, quat_smul_imI]; simp [octL])
    · change projC ((fixedS 3).2 2) = complexToOctonion (P3_mat 1 2)
      have hp : P3_mat 1 2 = 0 := by simp [P3_mat, mkHerm3Matrix]
      rw [hp, map_zero, hu2]
      have hjL_fst : (octonionMul octJ octL).1 = 0 := by
        change octJ.1 * octL.1 - star octL.2 * octJ.2 = 0
        have hL1 : octL.1 = 0 := rfl
        have hJ2 : octJ.2 = 0 := rfl
        rw [hL1, hJ2, mul_zero, mul_zero, sub_zero]
      apply oct_ext_chk <;>
        (simp only [projC, oct_smul_fst, oct_neg_fst, quat_smul_re, quat_smul_imI, hjL_fst]; simp)
  have hdet3 : (windowProj standardComplexWindow (fixedS 3) : ComplexMatrix3).det.re = 1 / 27 := by
    rw [hproj]
    change P3_mat.det.re = 1 / 27
    rw [Matrix.det_fin_three]
    have hm : ∀ i j : Fin 3, P3_mat i j = if i = j then (1 / 3 : ℂ) else 0 := by
      intro i j; fin_cases i <;> fin_cases j <;>
        simp [P3_mat, mkHerm3Matrix] <;> apply Complex.ext <;> simp
    simp [hm]
    norm_num
  rw [hdet3] at hdet
  linarith

private theorem sharpnessCurve4_proj_det (t : ℝ) :
    (windowProj standardComplexWindow (sharpnessCurve4 3 t) : ComplexMatrix3).det.re =
      16 * t ^ 4 / (27 * (1 + t ^ 2) ^ 4) := by
  let c := (1 - t ^ 2) / (1 + t ^ 2)
  let s := (2 * t) / (1 + t ^ 2)
  have hnorm : c ^ 2 + s ^ 2 = 1 := weierstrass_normSq t
  let P_mat : ComplexMatrix3 :=
    mkHerm3Matrix (fun _ => (1 / 3 : ℝ)) ![(c / 3 : ℂ), (c / 3 : ℂ), (c ^ 2 / 3 : ℂ)]
  have hP_sa : P_mat ∈ selfAdjoint ComplexMatrix3 := by
    rw [selfAdjoint.mem_iff]
    funext i j
    rw [Matrix.star_apply]
    fin_cases i <;> fin_cases j <;> simp [P_mat, mkHerm3Matrix] <;> apply Complex.ext <;> simp
  let P : Hermitian3 := ⟨P_mat, hP_sa⟩
  have hemb : standardComplexWindow.embedding (windowProj standardComplexWindow (sharpnessCurve4 3 t)) =
      standardComplexWindow.embedding P := by
    rw [standardComplexWindow_embedding_windowProj, standardComplexWindow_apply]
    dsimp only [complexHermToAlbert]
    rw [sharpnessCurve4_three_eq t]
    apply albert_ext_chk
    · change ((1 / 3 : ℝ) • albertUnit + (c / 3) • sc4A1 + (-(s / 3)) • sc4A2 +
          (c ^ 2 / 3) • sc4A3 + (c * s / 3) • sc4A4 + (-(s ^ 2 / 3)) • sc4A5).1 0 =
        (P_mat 0 0).re
      rw [albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk,
        albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
        albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk]
      simp [albertUnit, sc4A1, sc4A2, sc4A3, sc4A4, sc4A5, P_mat, mkHerm3Matrix]
    · change ((1 / 3 : ℝ) • albertUnit + (c / 3) • sc4A1 + (-(s / 3)) • sc4A2 +
          (c ^ 2 / 3) • sc4A3 + (c * s / 3) • sc4A4 + (-(s ^ 2 / 3)) • sc4A5).1 1 =
        (P_mat 1 1).re
      rw [albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk,
        albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
        albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk]
      simp [albertUnit, sc4A1, sc4A2, sc4A3, sc4A4, sc4A5, P_mat, mkHerm3Matrix]
    · change ((1 / 3 : ℝ) • albertUnit + (c / 3) • sc4A1 + (-(s / 3)) • sc4A2 +
          (c ^ 2 / 3) • sc4A3 + (c * s / 3) • sc4A4 + (-(s ^ 2 / 3)) • sc4A5).1 2 =
        (P_mat 2 2).re
      rw [albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk, albert_add_fst_chk,
        albert_add_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk,
        albert_smul_fst_chk, albert_smul_fst_chk, albert_smul_fst_chk]
      simp [albertUnit, sc4A1, sc4A2, sc4A3, sc4A4, sc4A5, P_mat, mkHerm3Matrix]
    · change projC (((1 / 3 : ℝ) • albertUnit + (c / 3) • sc4A1 + (-(s / 3)) • sc4A2 +
          (c ^ 2 / 3) • sc4A3 + (c * s / 3) • sc4A4 + (-(s ^ 2 / 3)) • sc4A5).2 0) =
        complexToOctonion (P_mat 0 1)
      have hp : P_mat 0 1 = (c / 3 : ℂ) := by simp [P_mat, mkHerm3Matrix]
      rw [hp, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk,
        albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
        albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk]
      apply oct_ext_chk <;>
        (simp only [projC, albertUnit, sc4A1, sc4A2, sc4A3, sc4A4, sc4A5,
            oct_add_fst, oct_smul_fst, oct_zero_fst, quat_smul_re, quat_smul_imI,
            complexToOctonion_fst, complexToOctonion_snd];
          try simp [octonionScalar, octJ])
    · change projC (((1 / 3 : ℝ) • albertUnit + (c / 3) • sc4A1 + (-(s / 3)) • sc4A2 +
          (c ^ 2 / 3) • sc4A3 + (c * s / 3) • sc4A4 + (-(s ^ 2 / 3)) • sc4A5).2 1) =
        complexToOctonion (P_mat 0 2)
      have hp : P_mat 0 2 = (c / 3 : ℂ) := by simp [P_mat, mkHerm3Matrix]
      rw [hp, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk,
        albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
        albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk]
      apply oct_ext_chk <;>
        (simp only [projC, albertUnit, sc4A1, sc4A2, sc4A3, sc4A4, sc4A5,
            oct_add_fst, oct_smul_fst, oct_zero_fst, quat_smul_re, quat_smul_imI,
            complexToOctonion_fst, complexToOctonion_snd];
          try simp [octonionScalar, octL])
    · change projC (((1 / 3 : ℝ) • albertUnit + (c / 3) • sc4A1 + (-(s / 3)) • sc4A2 +
          (c ^ 2 / 3) • sc4A3 + (c * s / 3) • sc4A4 + (-(s ^ 2 / 3)) • sc4A5).2 2) =
        complexToOctonion (P_mat 1 2)
      have hp : P_mat 1 2 = ((c ^ 2 / 3 : ℝ) : ℂ) := by
        simp [P_mat, mkHerm3Matrix]
      have hs0_2 : albertUnit.2 2 = 0 := rfl
      have hs1_2 : sc4A1.2 2 = 0 := rfl
      have hs2_2 : sc4A2.2 2 = 0 := rfl
      have hs3_2 : sc4A3.2 2 = octonionScalar 1 := rfl
      have hs4_2 : sc4A4.2 2 = octJ - octL := rfl
      have hs5_2 : sc4A5.2 2 = octonionMul octJ octL := rfl
      rw [hp, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk, albert_add_snd_chk,
        albert_add_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
        albert_smul_snd_chk, albert_smul_snd_chk, albert_smul_snd_chk,
        hs0_2, hs1_2, hs2_2, hs3_2, hs4_2, hs5_2]
      have hjL_fst : (octonionMul octJ octL).1 = 0 := by
        change octJ.1 * octL.1 - star octL.2 * octJ.2 = 0
        have hL1 : octL.1 = 0 := rfl
        have hJ2 : octJ.2 = 0 := rfl
        rw [hL1, hJ2, mul_zero, mul_zero, sub_zero]
      apply oct_ext_chk <;>
        (simp only [projC, oct_add_fst, oct_sub_fst, oct_smul_fst, oct_zero_fst,
            quat_smul_re, quat_smul_imI, hjL_fst, complexToOctonion_fst, complexToOctonion_snd,
            Complex.ofReal_re, Complex.ofReal_im];
          try simp [octonionScalar, octJ, octL])
  have hPeq : (windowProj standardComplexWindow (sharpnessCurve4 3 t) : ComplexMatrix3) = P_mat :=
    congrArg Subtype.val (standardComplexWindow.injective hemb)
  rw [hPeq, Matrix.det_fin_three]
  have h00 : P_mat 0 0 = ((1 / 3 : ℝ) : ℂ) := by apply Complex.ext <;> simp [P_mat, mkHerm3Matrix]
  have h11 : P_mat 1 1 = ((1 / 3 : ℝ) : ℂ) := by apply Complex.ext <;> simp [P_mat, mkHerm3Matrix]
  have h22 : P_mat 2 2 = ((1 / 3 : ℝ) : ℂ) := by apply Complex.ext <;> simp [P_mat, mkHerm3Matrix]
  have h01 : P_mat 0 1 = ((c / 3 : ℝ) : ℂ) := by simp [P_mat, mkHerm3Matrix]
  have h10 : P_mat 1 0 = ((c / 3 : ℝ) : ℂ) := by simp [P_mat, mkHerm3Matrix]
  have h02 : P_mat 0 2 = ((c / 3 : ℝ) : ℂ) := by simp [P_mat, mkHerm3Matrix]
  have h20 : P_mat 2 0 = ((c / 3 : ℝ) : ℂ) := by simp [P_mat, mkHerm3Matrix]
  have h12 : P_mat 1 2 = ((c ^ 2 / 3 : ℝ) : ℂ) := by simp [P_mat, mkHerm3Matrix]
  have h21 : P_mat 2 1 = ((c ^ 2 / 3 : ℝ) : ℂ) := by simp [P_mat, mkHerm3Matrix]
  rw [h00, h11, h22, h01, h10, h02, h20, h12, h21]
  norm_cast
  have hpoly :
      (1 / 3 : ℝ) * (1 / 3) * (1 / 3) - (1 / 3) * (c ^ 2 / 3) * (c ^ 2 / 3) -
        (c / 3) * (c / 3) * (1 / 3) + (c / 3) * (c ^ 2 / 3) * (c / 3) +
        (c / 3) * (c / 3) * (c ^ 2 / 3) - (c / 3) * (1 / 3) * (c / 3) =
        (1 - c ^ 2) ^ 2 / 27 := by
    ring
  rw [hpoly]
  have h1c : 1 - c ^ 2 = s ^ 2 := by linarith
  rw [h1c]
  dsimp only [s]
  have hpos : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem tracePairing_sharpnessCurve4 (t : ℝ) :
    let r : ℝ → Albert := fun s => glennieSymmJTerm.evalAlbert (fun k => sharpnessCurve4 k s)
    tracePairing (r t) (r t) = (2 ^ 21 / 3 ^ 5) * t ^ 4 / (1 + t ^ 2) ^ 4 := by
  intro r
  have hr : r t =
      nativeGlennieF ((2 : ℝ) • fixedS 0 - albertUnit) ((2 : ℝ) • fixedS 1 - albertUnit)
        ((2 : ℝ) • fixedS 2 - albertUnit) ((2 : ℝ) • sharpnessCurve4 3 t - albertUnit) := by
    dsimp [r]
    rw [evalAlbert_glennieSymmJTerm]
    rfl
  rw [hr]
  have hgl := thm_glennie_normSq (fixedS 0) (fixedS 1) (fixedS 2) (sharpnessCurve4 3 t)
    (fixedS_isAtom 0) (fixedS_isAtom 1) (fixedS_isAtom 2) (sharpnessCurve4_isAtom 3 t)
  have h0 : standardComplexWindow.Contains (fixedS 0) := sharpnessCurve4_base 0
  have h1 : standardComplexWindow.Contains (fixedS 1) := sharpnessCurve4_base 1
  have h2 : standardComplexWindow.Contains (fixedS 2) := sharpnessCurve4_base 2
  have hdet := prop_windowdet standardComplexWindow
    (fixedS_isAtom 0) (fixedS_isAtom 1) (fixedS_isAtom 2) (sharpnessCurve4_isAtom 3 t) h0 h1 h2
  rw [windowDelta_eq_tripleDelta, fixedS_tripleDelta, sharpnessCurve4_proj_det t] at hdet
  rw [hgl, albertCubicNorm_fixedS_ABC, hdet]
  have hpos : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem tracePairing_isBigO_cube_of_isBigO_sq {f g : ℝ → Albert}
    (hf : f =O[𝓝 0] (fun t => t ^ 3)) (hg : g =O[𝓝 0] (fun t => t ^ 2)) :
    (fun t => tracePairing (f t) (g t)) =O[𝓝 0] (fun t => t ^ 5) := by
  let mkRow : Albert → Albert →ₗ[ℝ] ℝ := fun x =>
    { toFun := tracePairing x
      map_add' := tracePairing_add_right x
      map_smul' := fun r y => by
        unfold tracePairing
        rw [jordanMul_smul_right, albertTrace_smul]
        rfl }
  let B_lin : Albert →ₗ[ℝ] Albert →L[ℝ] ℝ :=
    { toFun := fun x => (mkRow x).toContinuousLinearMap
      map_add' := fun x y => by
        ext z
        exact tracePairing_add_left x y z
      map_smul' := fun r x => by
        ext z
        change tracePairing (r • x) z = r * tracePairing x z
        unfold tracePairing
        rw [jordanMul_smul_left, albertTrace_smul] }
  let B : Albert →L[ℝ] Albert →L[ℝ] ℝ := B_lin.toContinuousLinearMap
  have hbound : ∀ x y : Albert, |tracePairing x y| ≤ ‖B‖ * ‖x‖ * ‖y‖ := fun x y => by
    have h := B.le_opNorm₂ x y
    simpa [B, B_lin, mkRow, Real.norm_eq_abs] using h
  obtain ⟨Cf, hCf_ev⟩ := hf.bound
  obtain ⟨Cg, hCg_ev⟩ := hg.bound
  set Cf' : ℝ := max Cf 0
  have hCf0 : 0 ≤ Cf' := le_max_right _ _
  refine IsBigO.of_bound (‖B‖ * Cf' * Cg) ?_
  filter_upwards [hCf_ev, hCg_ev] with t htf htg
  have htf' : ‖f t‖ ≤ Cf' * ‖t ^ 3‖ :=
    htf.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h1 : ‖tracePairing (f t) (g t)‖ ≤ ‖B‖ * ‖f t‖ * ‖g t‖ := hbound (f t) (g t)
  have h2 : ‖B‖ * ‖f t‖ * ‖g t‖ ≤ ‖B‖ * (Cf' * ‖t ^ 3‖) * (Cg * ‖t ^ 2‖) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left htf' (norm_nonneg B)) htg (norm_nonneg (g t)) ?_
    exact mul_nonneg (norm_nonneg B) (mul_nonneg hCf0 (norm_nonneg (t ^ 3)))
  refine h1.trans (h2.trans_eq ?_)
  simp only [Real.norm_eq_abs, abs_pow]
  ring

private theorem slot_nonzero_atom_pairing (Q : Albert) (hQ : Q ∈ Wperp) (hQ_ne : Q ≠ 0) :
    ∃ ρ : Albert, IsDensity ρ ∧ ¬ standardComplexWindow.Contains ρ ∧ tracePairing ρ Q ≠ 0 := by
  have hnot : ¬ (∀ k : Fin 3, Q.2 k = 0) := by
    intro hk
    apply hQ_ne
    apply Prod.ext <;> funext i
    · exact hQ.1 i
    · exact hk i
  push Not at hnot
  rcases hnot with ⟨k, hk⟩
  have hnk : 0 < octNormSq (Q.2 k) := by
    rcases lt_trichotomy (octNormSq (Q.2 k)) 0 with hlt | heq | hgt
    · exact absurd hlt (not_lt_of_ge (octNormSq_nonneg _))
    · exact absurd ((octNormSq_eq_zero _).1 heq) hk
    · exact hgt
  let s : ℝ := Real.sqrt (octNormSq (Q.2 k))
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hnk
  have hs_sq : s ^ 2 = octNormSq (Q.2 k) := Real.sq_sqrt hnk.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let u : Octonion := (1 / (Real.sqrt 2 * s)) • octonionConj (Q.2 k)
  have hu_norm : octNormSq u = 1 / 2 := by
    dsimp only [u]
    rw [octNormSq_smul, octNormSq_conj_chk, div_pow, one_pow, mul_pow, hs2, hs_sq]
    field_simp [hs_pos.ne']
  let v : Fin 3 → Octonion := match k with
    | 0 => ![octonionScalar (1 / Real.sqrt 2), u, 0]
    | 1 => ![octonionScalar (1 / Real.sqrt 2), 0, u]
    | 2 => ![0, octonionScalar (1 / Real.sqrt 2), u]
  let ρ : Albert := octDyad v
  have hρ_atom : IsAtom ρ := by
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hk_cases with rfl | rfl | rfl
    · apply octDyad_real0_isAtom
      rw [hu_norm, octNormSq_zero_chk, div_pow, one_pow, hs2]; norm_num
    · apply octDyad_real0_isAtom
      rw [octNormSq_zero_chk, hu_norm, div_pow, one_pow, hs2]; norm_num
    · obtain ⟨φ, hφ, h1_mem, hu_mem⟩ :=
        exists_quatEmbedding_containing_pair (octonionScalar (1 / Real.sqrt 2)) u
      refine octDyad_isAtom φ hφ ![0, octonionScalar (1 / Real.sqrt 2), u] ?_ ?_
      · intro i
        fin_cases i
        · exact ⟨0, map_zero φ⟩
        · exact h1_mem
        · exact hu_mem
      · rw [Fin.sum_univ_three]
        change octNormSq (0 : Octonion) + octNormSq (octonionScalar (1 / Real.sqrt 2)) +
          octNormSq u = 1
        rw [octNormSq_zero_chk, octNormSq_scalar_chk, div_pow, one_pow, hs2, hu_norm]
        norm_num
  have hρ_dens : IsDensity ρ := ⟨⟨ρ, hρ_atom.1.symm⟩, hρ_atom.2⟩
  have hpair : tracePairing ρ Q = s := by
    rw [tracePairing_eq_coords, hQ.1 0, hQ.1 1, hQ.1 2]
    have hconj2 : ∀ q : Octonion, octonionConj (octonionConj q) = q := fun q => by
      apply oct_ext_chk <;> simp [octonionConj]
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hk_cases with rfl | rfl | rfl
    · have h0 : ρ.2 0 = (1 / (2 * s)) • Q.2 0 := by
        change octonionMul (octonionScalar (1 / Real.sqrt 2))
            (octonionConj ((1 / (Real.sqrt 2 * s)) • octonionConj (Q.2 0))) = _
        rw [octonionConj_smul, hconj2, octonionMul_scalar_left, smul_smul]
        congr 1
        field_simp [hs_pos.ne']
        exact hs2.symm
      have h1 : ρ.2 1 = 0 := by
        change octonionMul (octonionScalar (1 / Real.sqrt 2)) (octonionConj 0) = 0
        rw [octonionConj_zero, octonionMul_zero_right]
      have h2 : ρ.2 2 = 0 := by
        change octonionMul u (octonionConj 0) = 0
        rw [octonionConj_zero, octonionMul_zero_right]
      rw [h0, h1, h2, octDot_zero_left, octDot_zero_left, octDot_smul_left]
      simp only [mul_zero, zero_add, add_zero, octDot_self]
      field_simp [hs_pos.ne']
      linarith [hs_sq]
    · have h0 : ρ.2 0 = 0 := by
        change octonionMul (octonionScalar (1 / Real.sqrt 2)) (octonionConj 0) = 0
        rw [octonionConj_zero, octonionMul_zero_right]
      have h1 : ρ.2 1 = (1 / (2 * s)) • Q.2 1 := by
        change octonionMul (octonionScalar (1 / Real.sqrt 2))
            (octonionConj ((1 / (Real.sqrt 2 * s)) • octonionConj (Q.2 1))) = _
        rw [octonionConj_smul, hconj2, octonionMul_scalar_left, smul_smul]
        congr 1
        field_simp [hs_pos.ne']
        exact hs2.symm
      have h2 : ρ.2 2 = 0 := by
        change octonionMul 0 (octonionConj u) = 0
        rw [octonionMul_zero_left]
      rw [h0, h1, h2, octDot_zero_left, octDot_zero_left, octDot_smul_left]
      simp only [mul_zero, zero_add, add_zero, octDot_self]
      field_simp [hs_pos.ne']
      linarith [hs_sq]
    · have h0 : ρ.2 0 = 0 := by
        change octonionMul 0 (octonionConj (octonionScalar (1 / Real.sqrt 2))) = 0
        rw [octonionMul_zero_left]
      have h1 : ρ.2 1 = 0 := by
        change octonionMul 0 (octonionConj u) = 0
        rw [octonionMul_zero_left]
      have h2 : ρ.2 2 = (1 / (2 * s)) • Q.2 2 := by
        change octonionMul (octonionScalar (1 / Real.sqrt 2))
            (octonionConj ((1 / (Real.sqrt 2 * s)) • octonionConj (Q.2 2))) = _
        rw [octonionConj_smul, hconj2, octonionMul_scalar_left, smul_smul]
        congr 1
        field_simp [hs_pos.ne']
        exact hs2.symm
      rw [h0, h1, h2, octDot_zero_left, octDot_zero_left, octDot_smul_left]
      simp only [mul_zero, zero_add, add_zero, octDot_self]
      field_simp [hs_pos.ne']
      linarith [hs_sq]
  have hnotW : ¬ standardComplexWindow.Contains ρ := by
    intro hW
    have h0 := (mem_Wperp_iff_tracePairing_zero Q).1 hQ ρ hW
    linarith [hpair, hs_pos]
  exact ⟨ρ, hρ_dens, hnotW, by rw [hpair]; exact hs_pos.ne'⟩

private theorem tracePairing_sq_diff_id (a b : Albert) :
    tracePairing (a - b) a + tracePairing (a - b) b = tracePairing a a - tracePairing b b := by
  rw [tracePairing_sub_left, tracePairing_sub_left, tracePairing_comm a b]
  ring

/-- Sharpness control for `cor:so:residual`: along `sharpnessCurve4` (atoms in `J`, based in `W` at
`t = 0`), the special-algebra-vanishing residual `r(t) = glennieSymmJTerm.evalAlbert (p t)` has
second-order term `Q ∈ W^⊥` with `‖Q‖² = 2^21/3^5 > 0` (`Q ≠ 0`), and there exists a fixed state
`ρ ∉ W` (`IsDensity ρ`) for which `⟨ρ, r(t)⟩` fails to be `O(t³)` (genuinely `Θ(t²)`). -/
theorem cor_so_residual_off_window_sharpness :
    let r : ℝ → Albert := fun t => glennieSymmJTerm.evalAlbert (fun k => sharpnessCurve4 k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    Q ∈ Wperp ∧
      tracePairing Q Q = 2 ^ 21 / 3 ^ 5 ∧
      Q ≠ 0 ∧
      ∃ ρ : Albert, IsDensity ρ ∧ ¬ standardComplexWindow.Contains ρ ∧
        tracePairing ρ Q ≠ 0 ∧
        ¬ ((fun t => tracePairing ρ (r t)) =O[𝓝 0] (fun t => t ^ 3)) := by
  intro r Q
  obtain ⟨hr_diff, hr0, hdr0, hQ_perp, _, hbigO, hbigO_l⟩ :=
    standardWindow_residual_of_specialVanishing glennieSymmJTerm glennieSymmJTerm_vanishes
      sharpnessCurve4 sharpnessCurve4_contDiff
      (fun k t => (sharpnessCurve4_isAtom k t).1) sharpnessCurve4_base
  have hr_bigO_sq : r =O[𝓝 0] (fun t => t ^ 2) := by
    have hQ2 : (fun t : ℝ => t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 2) := by
      refine IsBigO.of_bound ‖Q‖ (Eventually.of_forall fun t => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]
    have h32 : (fun t : ℝ => t ^ 3) =O[𝓝 0] (fun t => t ^ 2) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      simp only [Real.norm_eq_abs, abs_pow]
      nlinarith [sq_nonneg |t|, abs_nonneg t]
    have hsum := (hbigO.trans h32).add hQ2
    refine hsum.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
    dsimp only
    abel
  have hQ2 : (fun t : ℝ => t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 2) := by
    refine IsBigO.of_bound ‖Q‖ (Eventually.of_forall fun t => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_pow, mul_comm]
  have hdiff_sq : (fun t => tracePairing (r t) (r t) - t ^ 4 * tracePairing Q Q) =O[𝓝 0]
      (fun t => t ^ 5) := by
    have h1 := tracePairing_isBigO_cube_of_isBigO_sq hbigO hr_bigO_sq
    have h2 := tracePairing_isBigO_cube_of_isBigO_sq hbigO hQ2
    have hsum := h1.add h2
    refine hsum.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
    change tracePairing (r t - t ^ 2 • Q) (r t) + tracePairing (r t - t ^ 2 • Q) (t ^ 2 • Q) =
      tracePairing (r t) (r t) - t ^ 4 * tracePairing Q Q
    rw [tracePairing_sq_diff_id (r t) (t ^ 2 • Q), tracePairing_smul_left,
      tracePairing_smul_right]
    ring
  have hQQ : tracePairing Q Q = 2 ^ 21 / 3 ^ 5 := by
    obtain ⟨C, hC_ev⟩ := hdiff_sq.bound
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp hC_ev
    by_contra hne
    set K : ℝ := 2 ^ 21 / 3 ^ 5
    set gap : ℝ := |tracePairing Q Q - K|
    have hgap_pos : 0 < gap := abs_pos.mpr (sub_ne_zero.mpr hne)
    set M : ℝ := |C| + 15 * K + 1
    have hM_pos : 0 < M := by positivity
    set t : ℝ := min (δ / 2) (min (1 / 2) (gap / (2 * M)))
    have ht_pos : 0 < t := lt_min (half_pos hδ_pos) (lt_min (by norm_num) (div_pos hgap_pos (by positivity)))
    have ht_delta : t < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
    have ht_one : t ≤ 1 := (min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num))
    have ht_gap : t ≤ gap / (2 * M) := (min_le_right _ _).trans (min_le_right _ _)
    have hball_t : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht_pos]
      exact ht_delta
    have hdiff_t : |tracePairing (r t) (r t) - t ^ 4 * tracePairing Q Q| ≤ C * t ^ 5 := by
      have h0 := hball hball_t
      change |tracePairing (r t) (r t) - t ^ 4 * tracePairing Q Q| ≤ C * |t ^ 5| at h0
      rwa [abs_pow, abs_of_pos ht_pos] at h0
    have hr_val : tracePairing (r t) (r t) = K * t ^ 4 / (1 + t ^ 2) ^ 4 :=
      tracePairing_sharpnessCurve4 t
    have ht4_pos : 0 < t ^ 4 := pow_pos ht_pos 4
    have hbound1 : |K / (1 + t ^ 2) ^ 4 - tracePairing Q Q| ≤ C * t := by
      have hdiv : |tracePairing (r t) (r t) - t ^ 4 * tracePairing Q Q| =
          t ^ 4 * |K / (1 + t ^ 2) ^ 4 - tracePairing Q Q| := by
        rw [hr_val]
        have hfac : K * t ^ 4 / (1 + t ^ 2) ^ 4 - t ^ 4 * tracePairing Q Q =
            t ^ 4 * (K / (1 + t ^ 2) ^ 4 - tracePairing Q Q) := by ring
        rw [hfac, abs_mul, abs_of_pos ht4_pos]
      rw [hdiv] at hdiff_t
      have hct : C * t ^ 5 = t ^ 4 * (C * t) := by ring
      rw [hct] at hdiff_t
      exact le_of_mul_le_mul_left hdiff_t ht4_pos
    have hbound2 : |K / (1 + t ^ 2) ^ 4 - K| ≤ 15 * K * t ^ 2 := by
      have hpos1 : 0 < (1 + t ^ 2) ^ 4 := by positivity
      have hdiff_id : K / (1 + t ^ 2) ^ 4 - K =
          -K * (t ^ 2 * (4 + 6 * t ^ 2 + 4 * t ^ 4 + t ^ 6)) / (1 + t ^ 2) ^ 4 := by
        field_simp
        ring
      have hpoly : 4 + 6 * t ^ 2 + 4 * t ^ 4 + t ^ 6 ≤ 15 := by
        have h2 : t ^ 2 ≤ 1 := by nlinarith
        have h4 : t ^ 4 ≤ 1 := by nlinarith
        have h6 : t ^ 6 ≤ 1 := by nlinarith
        linarith
      have hnum : |K / (1 + t ^ 2) ^ 4 - K| =
          K * (t ^ 2 * (4 + 6 * t ^ 2 + 4 * t ^ 4 + t ^ 6)) / (1 + t ^ 2) ^ 4 := by
        rw [hdiff_id, abs_div, abs_of_pos hpos1]
        have hnonneg : 0 ≤ K * (t ^ 2 * (4 + 6 * t ^ 2 + 4 * t ^ 4 + t ^ 6)) := by positivity
        rw [show |-K * (t ^ 2 * (4 + 6 * t ^ 2 + 4 * t ^ 4 + t ^ 6))| =
            |-(K * (t ^ 2 * (4 + 6 * t ^ 2 + 4 * t ^ 4 + t ^ 6)))| by ring, abs_neg,
          abs_of_nonneg hnonneg]
      have hden : 1 ≤ (1 + t ^ 2) ^ 4 := by
        have : 1 ≤ 1 + t ^ 2 := by linarith [sq_nonneg t]
        exact one_le_pow₀ this
      calc
        |K / (1 + t ^ 2) ^ 4 - K|
          ≤ K * (t ^ 2 * (4 + 6 * t ^ 2 + 4 * t ^ 4 + t ^ 6)) := by
            rw [hnum]
            exact div_le_self (by positivity) hden
        _ ≤ K * (t ^ 2 * 15) := by
            gcongr
        _ = 15 * K * t ^ 2 := by ring
    have htri : gap ≤ C * t + 15 * K * t ^ 2 := by
      have hsplit : tracePairing Q Q - K =
          (K / (1 + t ^ 2) ^ 4 - K) - (K / (1 + t ^ 2) ^ 4 - tracePairing Q Q) := by ring
      calc
        gap = |(K / (1 + t ^ 2) ^ 4 - K) - (K / (1 + t ^ 2) ^ 4 - tracePairing Q Q)| := by
            dsimp [gap]; rw [hsplit]
        _ ≤ |K / (1 + t ^ 2) ^ 4 - K| + |K / (1 + t ^ 2) ^ 4 - tracePairing Q Q| :=
            abs_sub _ _
        _ ≤ 15 * K * t ^ 2 + C * t := add_le_add hbound2 hbound1
        _ = C * t + 15 * K * t ^ 2 := by ring
    have ht2 : t ^ 2 ≤ t := by nlinarith
    have hMt : C * t + 15 * K * t ^ 2 ≤ M * t := by
      have hC_le : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) ht_pos.le
      have hK_le : 15 * K * t ^ 2 ≤ 15 * K * t := mul_le_mul_of_nonneg_left ht2 (by positivity)
      dsimp [M]
      linarith
    have hM_gap : M * t ≤ gap / 2 := by
      calc
        M * t ≤ M * (gap / (2 * M)) := mul_le_mul_of_nonneg_left ht_gap hM_pos.le
        _ = gap / 2 := by field_simp [hM_pos.ne']
    linarith
  have hQ_ne : Q ≠ 0 := by
    intro h0
    rw [h0, ← zero_smul ℝ (0 : Albert), tracePairing_smul_left, zero_mul] at hQQ
    norm_num at hQQ
  obtain ⟨ρ, hρ_dens, hρ_notW, hρ_pair⟩ := slot_nonzero_atom_pairing Q hQ_perp hQ_ne
  refine ⟨hQ_perp, hQQ, hQ_ne, ρ, hρ_dens, hρ_notW, hρ_pair, ?_⟩
  intro hbad
  have hQ_bigO : (fun t => t ^ 2 * tracePairing ρ Q) =O[𝓝 0] (fun t => t ^ 3) := by
    have hlin := hbigO_l (tracePairingLM ρ)
    have hsub := hbad.sub hlin
    refine hsub.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
    dsimp only
    rw [tracePairingLM_apply, tracePairing_sub_right, tracePairing_smul_right]
    ring
  obtain ⟨C, hC_ev⟩ := hQ_bigO.bound
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp hC_ev
  set c_val : ℝ := |tracePairing ρ Q|
  have hc_pos : 0 < c_val := abs_pos.mpr hρ_pair
  set M : ℝ := |C| + 1
  have hM_pos : 0 < M := by positivity
  set t : ℝ := min (δ / 2) (c_val / (2 * M))
  have ht_pos : 0 < t := lt_min (half_pos hδ_pos) (div_pos hc_pos (by positivity))
  have ht_delta : t < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
  have hball_t : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht_pos]
    exact ht_delta
  have hdt : t ^ 2 * c_val ≤ C * t ^ 3 := by
    have h0 := hball hball_t
    change |t ^ 2 * tracePairing ρ Q| ≤ C * |t ^ 3| at h0
    rwa [abs_mul, abs_pow, abs_pow, abs_of_pos ht_pos] at h0
  have ht2_pos : 0 < t ^ 2 := pow_pos ht_pos 2
  have hle_C : t ^ 2 * c_val ≤ t ^ 2 * (M * t) := by
    have hCM : C * t ^ 3 ≤ M * t ^ 3 := by
      have : C ≤ M := (le_abs_self C).trans (le_add_of_nonneg_right zero_le_one)
      exact mul_le_mul_of_nonneg_right this (pow_nonneg ht_pos.le 3)
    have ht3 : M * t ^ 3 = t ^ 2 * (M * t) := by ring
    linarith
  have hc_le : c_val ≤ M * t := le_of_mul_le_mul_left hle_C ht2_pos
  have hMt : M * t ≤ c_val / 2 := by
    calc
      M * t ≤ M * (c_val / (2 * M)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM_pos.le
      _ = c_val / 2 := by field_simp [hM_pos.ne']
  linarith

end

end AlbertSequential.AppF.Checks

section NormFreeAndAxiomAudit

open AlbertSequential

/-! ## Section 4: Norm-free signature check and exhaustive `#check` / `#print axioms` audit -/

example {n : ℕ} (W : ComplexWindow) (c : Word (Fin n) →₀ ℝ)
    (hc : AppF.IsProjectiveEquality c) (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k (l : Albert →ₗ[ℝ] ℝ), ContDiff ℝ 3 (fun t => l (p k t)))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, W.Contains (p k 0)) :=
  AppF.cor_so_residual_linearFunctional W c hc p hp_diff hp_idem hp_base

-- `Pending.GlennieGeneral` (statements and the any-order reduction)
#check @AlbertSequential.AppF.Pending.anyOrder_of_statement
#print axioms AlbertSequential.AppF.Pending.anyOrder_of_statement

-- BlockA.GlennieBimodule
#check @AlbertSequential.AppF.extractT2U2_nativePsi
#check @AlbertSequential.AppF.nativeGlennieF_standardComplexWindow
#check @AlbertSequential.AppF.glennieF_of_skew_eq_four_lambda_def
#check @AlbertSequential.AppF.glennieF_window_eq_four_lambda_def
#check @AlbertSequential.AppF.glennieF_window_symm_eq_four_lambda_def
#print axioms AlbertSequential.AppF.extractT2U2_nativePsi
#print axioms AlbertSequential.AppF.nativeGlennieF_standardComplexWindow
#print axioms AlbertSequential.AppF.glennieF_of_skew_eq_four_lambda_def
#print axioms AlbertSequential.AppF.glennieF_window_eq_four_lambda_def
#print axioms AlbertSequential.AppF.glennieF_window_symm_eq_four_lambda_def

-- BlockA.GlennieWindowTrace
#check @AlbertSequential.AppF.exists_rankOneHermitian_of_isAtom
#check @AlbertSequential.AppF.albertCubicNorm_sum_rankOneHermitian
#check @AlbertSequential.AppF.windowLambda_symm_rankOne
#check @AlbertSequential.AppF.tripleDelta_rankOne
#check @AlbertSequential.AppF.windowLambda_symm_sq_of_isAtom
#print axioms AlbertSequential.AppF.exists_rankOneHermitian_of_isAtom
#print axioms AlbertSequential.AppF.albertCubicNorm_sum_rankOneHermitian
#print axioms AlbertSequential.AppF.windowLambda_symm_rankOne
#print axioms AlbertSequential.AppF.tripleDelta_rankOne
#print axioms AlbertSequential.AppF.windowLambda_symm_sq_of_isAtom

-- BlockA.GlennieDefect
#check @AlbertSequential.AppF.defectVec_eq_three_defectAdI_sq
#check @AlbertSequential.AppF.tracePairing_defectVec_eq_72_det
#check @AlbertSequential.AppF.tracePairing_defect_transport
#check @AlbertSequential.AppF.tracePairing_defect_window
#print axioms AlbertSequential.AppF.defectVec_eq_three_defectAdI_sq
#print axioms AlbertSequential.AppF.tracePairing_defectVec_eq_72_det
#print axioms AlbertSequential.AppF.tracePairing_defect_transport
#print axioms AlbertSequential.AppF.tracePairing_defect_window

-- BlockA.GlennieGeneral
#check @AlbertSequential.AppF.nativeGlennieF_aut
#check @AlbertSequential.AppF.tracePairing_nativeGlennieF_aut
#check @AlbertSequential.AppF.special_glennieF_eq_zero
#check @AlbertSequential.AppF.glennieF_quatWindow_eq_zero
#check @AlbertSequential.AppF.glennie_of_quatWindow
#check @AlbertSequential.AppF.glennie_degenerate
#check @AlbertSequential.AppF.glennie_of_standardComplexWindow
#check @AlbertSequential.AppF.glennie_nondegenerate
#check @AlbertSequential.AppF.glennieViolationStatement_holds
#check @AlbertSequential.AppF.glennieViolationAnyOrder_holds
#check @AlbertSequential.AppF.thm_glennie_normSq
#check @AlbertSequential.AppF.thm_glennie_perm
#check @AlbertSequential.AppF.thm_glennie_eq_zero_iff
#check @AlbertSequential.AppF.thm_glennie
#print axioms AlbertSequential.AppF.nativeGlennieF_aut
#print axioms AlbertSequential.AppF.tracePairing_nativeGlennieF_aut
#print axioms AlbertSequential.AppF.special_glennieF_eq_zero
#print axioms AlbertSequential.AppF.glennieF_quatWindow_eq_zero
#print axioms AlbertSequential.AppF.glennie_of_quatWindow
#print axioms AlbertSequential.AppF.glennie_degenerate
#print axioms AlbertSequential.AppF.glennie_of_standardComplexWindow
#print axioms AlbertSequential.AppF.glennie_nondegenerate
#print axioms AlbertSequential.AppF.glennieViolationStatement_holds
#print axioms AlbertSequential.AppF.glennieViolationAnyOrder_holds
#print axioms AlbertSequential.AppF.thm_glennie_normSq
#print axioms AlbertSequential.AppF.thm_glennie_perm
#print axioms AlbertSequential.AppF.thm_glennie_eq_zero_iff
#print axioms AlbertSequential.AppF.thm_glennie

-- BlockA.SecondOrderResidual
#check @AlbertSequential.AppF.taylor_two_isBigO_cube
#check @AlbertSequential.AppF.jet2_evalAlbert
#check @AlbertSequential.AppF.jet2_idempotent
#check @AlbertSequential.AppF.mem_Wperp_iff_tracePairing_zero
#check @AlbertSequential.AppF.standardWindow_residual_of_specialVanishing
#check @AlbertSequential.AppF.tracePairing_nativeWordCombinationEffect
#check @AlbertSequential.AppF.prop_cer_noequality_a
#check @AlbertSequential.AppF.isProjectiveEquality_iff_specialVanishing
#check @AlbertSequential.AppF.isProjectiveEquality_iff_freeProductZero
#check @AlbertSequential.AppF.isProjectiveEquality_iff_universalAlgebraZero
#check @AlbertSequential.AppF.isProjectiveEquality_iff_algebraicProjectiveData
#check @AlbertSequential.AppF.cor_so_residual_from_specialVanishing
#check @AlbertSequential.AppF.cor_so_residual
#check @AlbertSequential.AppF.cor_so_residual_of_atoms
#check @AlbertSequential.AppF.cor_so_residual_from_universalAlgebra
#check @AlbertSequential.AppF.cor_so_residual_from_algebraicProjectiveData
#check @AlbertSequential.AppF.cor_so_residual_standardWindow
#check @AlbertSequential.AppF.cor_so_residual_linearFunctional
#print axioms AlbertSequential.AppF.taylor_two_isBigO_cube
#print axioms AlbertSequential.AppF.jet2_evalAlbert
#print axioms AlbertSequential.AppF.jet2_idempotent
#print axioms AlbertSequential.AppF.mem_Wperp_iff_tracePairing_zero
#print axioms AlbertSequential.AppF.standardWindow_residual_of_specialVanishing
#print axioms AlbertSequential.AppF.tracePairing_nativeWordCombinationEffect
#print axioms AlbertSequential.AppF.prop_cer_noequality_a
#print axioms AlbertSequential.AppF.isProjectiveEquality_iff_specialVanishing
#print axioms AlbertSequential.AppF.isProjectiveEquality_iff_freeProductZero
#print axioms AlbertSequential.AppF.isProjectiveEquality_iff_universalAlgebraZero
#print axioms AlbertSequential.AppF.isProjectiveEquality_iff_algebraicProjectiveData
#print axioms AlbertSequential.AppF.cor_so_residual_from_specialVanishing
#print axioms AlbertSequential.AppF.cor_so_residual
#print axioms AlbertSequential.AppF.cor_so_residual_of_atoms
#print axioms AlbertSequential.AppF.cor_so_residual_from_universalAlgebra
#print axioms AlbertSequential.AppF.cor_so_residual_from_algebraicProjectiveData
#print axioms AlbertSequential.AppF.cor_so_residual_standardWindow
#print axioms AlbertSequential.AppF.cor_so_residual_linearFunctional

-- BlockA.Checks (controls & sharpness)
#check @AlbertSequential.AppF.Checks.glennie_fixedS_general_agrees
#check @AlbertSequential.AppF.Checks.glennie_fixedS_general_matches_all_orders
#check @AlbertSequential.AppF.Checks.glennie_maximizer_general_agrees
#check @AlbertSequential.AppF.Checks.glennie_degenerate_diagonal_control
#check @AlbertSequential.AppF.Checks.glennie_degenerate_quaternionic_control
#check @AlbertSequential.AppF.Checks.cRep_isProjectiveEquality
#check @AlbertSequential.AppF.Checks.cExtra1_isProjectiveEquality
#check @AlbertSequential.AppF.Checks.cExtra2_isProjectiveEquality
#check @AlbertSequential.AppF.Checks.cor_so_residual_nonvacuity_extraeq
#check @AlbertSequential.AppF.Checks.glennieSymmJTerm_vanishes
#check @AlbertSequential.AppF.Checks.cor_so_residual_off_window_sharpness
#print axioms AlbertSequential.AppF.Checks.glennie_fixedS_general_agrees
#print axioms AlbertSequential.AppF.Checks.glennie_fixedS_general_matches_all_orders
#print axioms AlbertSequential.AppF.Checks.glennie_maximizer_general_agrees
#print axioms AlbertSequential.AppF.Checks.glennie_degenerate_diagonal_control
#print axioms AlbertSequential.AppF.Checks.glennie_degenerate_quaternionic_control
#print axioms AlbertSequential.AppF.Checks.cRep_isProjectiveEquality
#print axioms AlbertSequential.AppF.Checks.cExtra1_isProjectiveEquality
#print axioms AlbertSequential.AppF.Checks.cExtra2_isProjectiveEquality
#print axioms AlbertSequential.AppF.Checks.cor_so_residual_nonvacuity_extraeq
#print axioms AlbertSequential.AppF.Checks.glennieSymmJTerm_vanishes
#print axioms AlbertSequential.AppF.Checks.cor_so_residual_off_window_sharpness

end NormFreeAndAxiomAudit
