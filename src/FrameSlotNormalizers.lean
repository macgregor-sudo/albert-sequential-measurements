/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OctonionGeometry
public import Interfaces.Geometry
public import DiagPeirceAnchor
public import NativePeircePropagation
public import NativeMatrixTrace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Native Freudenthal Geometry, Slot Embeddings, Moufang Normalizers, and Windows

Formalizes:
1. Native Freudenthal adjoint `albertSharp`, bilinearization `albertCross`, cubic norm
   `albertCubicNorm`, `NativeAlbertAutomorphism` covariance, `jordanMul x (albertSharp x) =
   albertCubicNorm x • albertUnit`, and vanishing on atoms.
2. Slot embeddings `slotElem01`, `slotElem02`, `slotElem12` (`lem:A:slots` (a)–(c)), `octDyad`
   rank-one dyads, and atom coordinate characterization.
3. Native automorphism groupoid, entrywise `octAutoToAlbertAuto` (including `complexTransposeAuto`),
   `O(3)` orthogonal conjugation (`permFrameAlbertAuto`, `swap01AlbertAuto`, `swap02AlbertAuto`,
   `swap12AlbertAuto`), and Moufang frame-stabilizing normalizers F2 (`middleMoufangAlbertAuto`)
   and F3 (double `familyCMoufangAlbertAuto`).
4. `standardComplexWindow` ($H_3(\mathbb{C}_i)$, finrank 9), `QuaternionicWindow` ($H_3(\mathbb{H})$,
   finrank 15), `AtomAndRankOneBridge`, and conjugacy of frames, `ComplexWindow`s, and
   `QuaternionicWindow`s, plus zero-pairing support lemmas.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

/-! ## Section 0: Coordinate Helpers and Off-Diagonal Jordan Product -/

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

private theorem albert_zero_fst (j : Fin 3) : (0 : Albert).1 j = 0 := rfl
private theorem albert_zero_snd (k : Fin 3) : (0 : Albert).2 k = 0 := rfl
private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem albert_neg_fst (x : Albert) (j : Fin 3) : (-x).1 j = -x.1 j := rfl
private theorem albert_neg_snd (x : Albert) (k : Fin 3) : (-x).2 k = -x.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

private theorem albertUnit_fst (j : Fin 3) : albertUnit.1 j = 1 := rfl
private theorem albertUnit_snd (k : Fin 3) : albertUnit.2 k = 0 := rfl

private theorem diagAtom_fst (i j : Fin 3) : (diagAtom i).1 j = if j = i then 1 else 0 := rfl
private theorem diagAtom_snd (i k : Fin 3) : (diagAtom i).2 k = 0 := rfl

private theorem octNormSq_zero : octNormSq 0 = 0 := by
  rw [octNormSq, octDot_zero_left]

private theorem octonionConj_sub (x y : Octonion) :
    octonionConj (x - y) = octonionConj x - octonionConj y := by
  rw [sub_eq_add_neg, octonionConj_add, octonionConj_neg, ← sub_eq_add_neg]

private theorem albertTrace_albertUnit : albertTrace albertUnit = 3 := by
  unfold albertTrace albertUnit
  rw [Fin.sum_univ_three]
  norm_num

private theorem albertTrace_neg (x : Albert) : albertTrace (-x) = -albertTrace x := by
  have h := albertTrace_smul (-1 : ℝ) x
  simpa only [neg_one_smul, neg_one_mul] using h

private theorem tracePairing_self_eq (x : Albert) :
    tracePairing x x =
      (x.1 0) ^ 2 + (x.1 1) ^ 2 + (x.1 2) ^ 2 +
        2 * (octNormSq (x.2 0) + octNormSq (x.2 1) + octNormSq (x.2 2)) := by
  rw [tracePairing_eq_coords]
  unfold octNormSq
  ring

private theorem albertMatrix_00' (x : Albert) : albertMatrix x 0 0 = octonionScalar (x.1 0) := rfl
private theorem albertMatrix_01' (x : Albert) : albertMatrix x 0 1 = x.2 0 := rfl
private theorem albertMatrix_02' (x : Albert) : albertMatrix x 0 2 = x.2 1 := rfl
private theorem albertMatrix_10' (x : Albert) : albertMatrix x 1 0 = octonionConj (x.2 0) := rfl
private theorem albertMatrix_11' (x : Albert) : albertMatrix x 1 1 = octonionScalar (x.1 1) := rfl
private theorem albertMatrix_12' (x : Albert) : albertMatrix x 1 2 = x.2 2 := rfl
private theorem albertMatrix_20' (x : Albert) : albertMatrix x 2 0 = octonionConj (x.2 1) := rfl
private theorem albertMatrix_21' (x : Albert) : albertMatrix x 2 1 = octonionConj (x.2 2) := rfl
private theorem albertMatrix_22' (x : Albert) : albertMatrix x 2 2 = octonionScalar (x.1 2) := rfl

theorem jordanMul_off_0 (x y : Albert) :
    (jordanMul x y).2 0 = (1 / 2 : ℝ) •
      ((x.1 0 + x.1 1) • y.2 0 + (y.1 0 + y.1 1) • x.2 0 +
        octonionMul (x.2 1) (octonionConj (y.2 2)) +
        octonionMul (y.2 1) (octonionConj (x.2 2))) := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) •
      (octonionMatrixMul (albertMatrix x) (albertMatrix y) 0 1 +
        octonionMatrixMul (albertMatrix y) (albertMatrix x) 0 1) = _
  unfold octonionMatrixMul
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [albertMatrix_00', albertMatrix_01', albertMatrix_02',
    albertMatrix_11', albertMatrix_21',
    octonionMul_scalar_left, octonionMul_scalar_right]
  module

theorem jordanMul_off_1 (x y : Albert) :
    (jordanMul x y).2 1 = (1 / 2 : ℝ) •
      ((x.1 0 + x.1 2) • y.2 1 + (y.1 0 + y.1 2) • x.2 1 +
        octonionMul (x.2 0) (y.2 2) +
        octonionMul (y.2 0) (x.2 2)) := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) •
      (octonionMatrixMul (albertMatrix x) (albertMatrix y) 0 2 +
        octonionMatrixMul (albertMatrix y) (albertMatrix x) 0 2) = _
  unfold octonionMatrixMul
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [albertMatrix_00', albertMatrix_01', albertMatrix_02',
    albertMatrix_12', albertMatrix_22',
    octonionMul_scalar_left, octonionMul_scalar_right]
  module

theorem jordanMul_off_2 (x y : Albert) :
    (jordanMul x y).2 2 = (1 / 2 : ℝ) •
      ((x.1 1 + x.1 2) • y.2 2 + (y.1 1 + y.1 2) • x.2 2 +
        octonionMul (octonionConj (x.2 0)) (y.2 1) +
        octonionMul (octonionConj (y.2 0)) (x.2 1)) := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) •
      (octonionMatrixMul (albertMatrix x) (albertMatrix y) 1 2 +
        octonionMatrixMul (albertMatrix y) (albertMatrix x) 1 2) = _
  unfold octonionMatrixMul
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [albertMatrix_10', albertMatrix_11', albertMatrix_12',
    albertMatrix_02', albertMatrix_22',
    octonionMul_scalar_left, octonionMul_scalar_right]
  module

/-! ## Section 1: Native Freudenthal Adjoint, Cross Product, and Cubic Norm -/

def albertSharp (x : Albert) : Albert :=
  (![x.1 1 * x.1 2 - octNormSq (x.2 2),
     x.1 0 * x.1 2 - octNormSq (x.2 1),
     x.1 0 * x.1 1 - octNormSq (x.2 0)],
   ![octonionMul (x.2 1) (octonionConj (x.2 2)) - x.1 2 • x.2 0,
     octonionMul (x.2 0) (x.2 2) - x.1 1 • x.2 1,
     octonionMul (octonionConj (x.2 0)) (x.2 1) - x.1 0 • x.2 2])

private theorem albertSharp_fst_0 (x : Albert) :
    (albertSharp x).1 0 = x.1 1 * x.1 2 - octNormSq (x.2 2) := rfl
private theorem albertSharp_fst_1 (x : Albert) :
    (albertSharp x).1 1 = x.1 0 * x.1 2 - octNormSq (x.2 1) := rfl
private theorem albertSharp_fst_2 (x : Albert) :
    (albertSharp x).1 2 = x.1 0 * x.1 1 - octNormSq (x.2 0) := rfl
private theorem albertSharp_snd_0 (x : Albert) :
    (albertSharp x).2 0 = octonionMul (x.2 1) (octonionConj (x.2 2)) - x.1 2 • x.2 0 := rfl
private theorem albertSharp_snd_1 (x : Albert) :
    (albertSharp x).2 1 = octonionMul (x.2 0) (x.2 2) - x.1 1 • x.2 1 := rfl
private theorem albertSharp_snd_2 (x : Albert) :
    (albertSharp x).2 2 = octonionMul (octonionConj (x.2 0)) (x.2 1) - x.1 0 • x.2 2 := rfl

def albertCross (x y : Albert) : Albert :=
  albertSharp (x + y) - albertSharp x - albertSharp y

def albertCubicNorm (x : Albert) : ℝ :=
  x.1 0 * x.1 1 * x.1 2 - x.1 0 * octNormSq (x.2 2) - x.1 1 * octNormSq (x.2 1) -
    x.1 2 * octNormSq (x.2 0) + 2 * octDot (octonionMul (x.2 0) (x.2 2)) (x.2 1)

theorem albertSharp_eq_jordanMul (x : Albert) :
    albertSharp x = jordanMul x x - albertTrace x • x +
      ((1 / 2 : ℝ) * ((albertTrace x) ^ 2 - tracePairing x x)) • albertUnit := by
  have htr : albertTrace x = x.1 0 + x.1 1 + x.1 2 := by
    unfold albertTrace
    exact Fin.sum_univ_three _
  apply albert_ext
  · rw [albertSharp_fst_0, albert_add_fst, albert_sub_fst, albert_smul_fst, albert_smul_fst,
      jordanMul_diag_0, htr, tracePairing_self_eq, albertUnit_fst]
    unfold octNormSq
    ring
  · rw [albertSharp_fst_1, albert_add_fst, albert_sub_fst, albert_smul_fst, albert_smul_fst,
      jordanMul_diag_1, htr, tracePairing_self_eq, albertUnit_fst]
    unfold octNormSq
    ring
  · rw [albertSharp_fst_2, albert_add_fst, albert_sub_fst, albert_smul_fst, albert_smul_fst,
      jordanMul_diag_2, htr, tracePairing_self_eq, albertUnit_fst]
    unfold octNormSq
    ring
  · rw [albertSharp_snd_0, albert_add_snd, albert_sub_snd, albert_smul_snd, albert_smul_snd,
      jordanMul_off_0, htr, albertUnit_snd, smul_zero, add_zero]
    module
  · rw [albertSharp_snd_1, albert_add_snd, albert_sub_snd, albert_smul_snd, albert_smul_snd,
      jordanMul_off_1, htr, albertUnit_snd, smul_zero, add_zero]
    module
  · rw [albertSharp_snd_2, albert_add_snd, albert_sub_snd, albert_smul_snd, albert_smul_snd,
      jordanMul_off_2, htr, albertUnit_snd, smul_zero, add_zero]
    module

private theorem octDot_triple_012 (u01 u02 u12 : Octonion) :
    octDot u01 (octonionMul u02 (octonionConj u12)) =
      octDot (octonionMul u01 u12) u02 :=
  (octDot_mul_right u01 u12 u02).symm

private theorem octDot_triple_120 (u01 u02 u12 : Octonion) :
    octDot u12 (octonionMul (octonionConj u01) u02) =
      octDot (octonionMul u01 u12) u02 := by
  rw [octDot_comm u12 _, octDot_mul_left (octonionConj u01) u02 u12,
    octonionConj_conj, octDot_comm (octonionMul u01 u12) u02]

theorem albertCubicNorm_eq_tracePairing (x : Albert) :
    albertCubicNorm x = (1 / 3 : ℝ) * tracePairing x (albertSharp x) := by
  rw [tracePairing_eq_coords, albertSharp_fst_0, albertSharp_fst_1, albertSharp_fst_2,
    albertSharp_snd_0, albertSharp_snd_1, albertSharp_snd_2]
  have h1 : octDot (x.2 0) (octonionMul (x.2 1) (octonionConj (x.2 2)) - x.1 2 • x.2 0) =
      octDot (octonionMul (x.2 0) (x.2 2)) (x.2 1) - x.1 2 * octNormSq (x.2 0) := by
    rw [octDot_sub_right, octDot_smul_right, octDot_self, octDot_triple_012]
  have h2 : octDot (x.2 1) (octonionMul (x.2 0) (x.2 2) - x.1 1 • x.2 1) =
      octDot (octonionMul (x.2 0) (x.2 2)) (x.2 1) - x.1 1 * octNormSq (x.2 1) := by
    rw [octDot_sub_right, octDot_smul_right, octDot_self, octDot_comm (x.2 1)]
  have h3 : octDot (x.2 2) (octonionMul (octonionConj (x.2 0)) (x.2 1) - x.1 0 • x.2 2) =
      octDot (octonionMul (x.2 0) (x.2 2)) (x.2 1) - x.1 0 * octNormSq (x.2 2) := by
    rw [octDot_sub_right, octDot_smul_right, octDot_self, octDot_triple_120]
  rw [h1, h2, h3]
  unfold albertCubicNorm
  ring

theorem albertSharp_albertUnit : albertSharp albertUnit = albertUnit := by
  apply albert_ext
  · simp [albertSharp_fst_0, albertUnit_fst, albertUnit_snd, octNormSq_zero]
  · simp [albertSharp_fst_1, albertUnit_fst, albertUnit_snd, octNormSq_zero]
  · simp [albertSharp_fst_2, albertUnit_fst, albertUnit_snd, octNormSq_zero]
  · simp [albertSharp_snd_0, albertUnit_fst, albertUnit_snd, octonionMul_zero_left]
  · simp [albertSharp_snd_1, albertUnit_fst, albertUnit_snd, octonionMul_zero_left]
  · simp [albertSharp_snd_2, albertUnit_fst, albertUnit_snd, octonionMul_zero_right]

theorem albertCubicNorm_albertUnit : albertCubicNorm albertUnit = 1 := by
  simp [albertCubicNorm, albertUnit_fst, albertUnit_snd, octNormSq_zero,
    octonionMul_zero_left, octDot_zero_left]

theorem albertSharp_smul (r : ℝ) (x : Albert) :
    albertSharp (r • x) = (r ^ 2) • albertSharp x := by
  apply albert_ext
  · rw [albertSharp_fst_0, albert_smul_fst, albert_smul_fst, albert_smul_snd, octNormSq_smul,
      albert_smul_fst, albertSharp_fst_0]
    ring
  · rw [albertSharp_fst_1, albert_smul_fst, albert_smul_fst, albert_smul_snd, octNormSq_smul,
      albert_smul_fst, albertSharp_fst_1]
    ring
  · rw [albertSharp_fst_2, albert_smul_fst, albert_smul_fst, albert_smul_snd, octNormSq_smul,
      albert_smul_fst, albertSharp_fst_2]
    ring
  · rw [albertSharp_snd_0, albert_smul_snd, albert_smul_snd, albert_smul_fst, albert_smul_snd,
      octonionConj_smul, octonionMul_smul_left, octonionMul_smul_right,
      albert_smul_snd, albertSharp_snd_0, smul_sub, smul_smul, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring
  · rw [albertSharp_snd_1, albert_smul_snd, albert_smul_snd, albert_smul_fst, albert_smul_snd,
      octonionMul_smul_left, octonionMul_smul_right,
      albert_smul_snd, albertSharp_snd_1, smul_sub, smul_smul, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring
  · rw [albertSharp_snd_2, albert_smul_snd, albert_smul_snd, albert_smul_fst, albert_smul_snd,
      octonionConj_smul, octonionMul_smul_left, octonionMul_smul_right,
      albert_smul_snd, albertSharp_snd_2, smul_sub, smul_smul, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring

theorem albertCubicNorm_smul (r : ℝ) (x : Albert) :
    albertCubicNorm (r • x) = r ^ 3 * albertCubicNorm x := by
  rw [albertCubicNorm_eq_tracePairing, albertCubicNorm_eq_tracePairing,
    albertSharp_smul, tracePairing_smul_left, tracePairing_smul_right]
  ring

theorem jordanMul_albertSharp (x : Albert) :
    jordanMul x (albertSharp x) = albertCubicNorm x • albertUnit := by
  apply albert_ext
  · rw [jordanMul_diag_0, albert_smul_fst, albertSharp_fst_0, albertSharp_snd_0,
      albertSharp_snd_1, albertUnit_fst, mul_one,
      octDot_sub_right, octDot_smul_right, octDot_self,
      octDot_sub_right, octDot_smul_right, octDot_self,
      octDot_triple_012, octDot_comm (x.2 1) (octonionMul (x.2 0) (x.2 2))]
    unfold albertCubicNorm
    ring
  · rw [jordanMul_diag_1, albert_smul_fst, albertSharp_fst_1, albertSharp_snd_0,
      albertSharp_snd_2, albertUnit_fst, mul_one,
      octDot_sub_right, octDot_smul_right, octDot_self,
      octDot_sub_right, octDot_smul_right, octDot_self,
      octDot_triple_012, octDot_triple_120]
    unfold albertCubicNorm
    ring
  · rw [jordanMul_diag_2, albert_smul_fst, albertSharp_fst_2, albertSharp_snd_1,
      albertSharp_snd_2, albertUnit_fst, mul_one,
      octDot_sub_right, octDot_smul_right, octDot_self,
      octDot_sub_right, octDot_smul_right, octDot_self,
      octDot_comm (x.2 1) (octonionMul (x.2 0) (x.2 2)), octDot_triple_120]
    unfold albertCubicNorm
    ring
  · rw [jordanMul_off_0, albert_smul_snd, albertUnit_snd, smul_zero,
      albertSharp_snd_0, albertSharp_fst_0, albertSharp_fst_1,
      albertSharp_snd_2, albertSharp_snd_1,
      octonionConj_sub, octonionConj_smul, octonionConj_mul, octonionConj_conj,
      octonionMul_sub_right, octonionMul_smul_right, octMul_left_conj_cancel,
      octonionMul_sub_left, octonionMul_smul_left, octMul_conj_right_cancel]
    module
  · rw [jordanMul_off_1, albert_smul_snd, albertUnit_snd, smul_zero,
      albertSharp_snd_1, albertSharp_fst_0, albertSharp_fst_2,
      albertSharp_snd_2, albertSharp_snd_0,
      octonionMul_sub_right, octonionMul_smul_right, octMul_left_conj_cancel,
      octonionMul_sub_left, octonionMul_smul_left, octMul_right_conj_cancel]
    module
  · rw [jordanMul_off_2, albert_smul_snd, albertUnit_snd, smul_zero,
      albertSharp_snd_2, albertSharp_fst_1, albertSharp_fst_2,
      albertSharp_snd_1, albertSharp_snd_0,
      octonionConj_sub, octonionConj_smul, octonionConj_mul, octonionConj_conj,
      octonionMul_sub_right, octonionMul_smul_right, octMul_conj_left_cancel,
      octonionMul_sub_left, octonionMul_smul_left, octMul_right_conj_cancel]
    module

theorem albertSharp_of_isAtom {p : Albert} (hp : IsAtom p) : albertSharp p = 0 := by
  have htr2 : tracePairing p p = 1 := by
    unfold tracePairing
    rw [hp.1, hp.2]
  rw [albertSharp_eq_jordanMul, hp.1, hp.2, one_smul, htr2]
  norm_num

theorem albertSharp_diag (d : Fin 3 → ℝ) :
    albertSharp ((d, fun _ => 0) : Albert) =
      ((![d 1 * d 2, d 0 * d 2, d 0 * d 1], fun _ => 0) : Albert) := by
  let x : Albert := (d, fun _ => 0)
  change albertSharp x = ((![d 1 * d 2, d 0 * d 2, d 0 * d 1], fun _ => 0) : Albert)
  have hx1 : ∀ i : Fin 3, x.1 i = d i := fun _ => rfl
  have hx2 : ∀ i : Fin 3, x.2 i = 0 := fun _ => rfl
  apply albert_ext
  · rw [albertSharp_fst_0]; simp [hx1, hx2, octNormSq_zero]
  · rw [albertSharp_fst_1]; simp [hx1, hx2, octNormSq_zero]
  · rw [albertSharp_fst_2]; simp [hx1, hx2, octNormSq_zero]
  · rw [albertSharp_snd_0]; simp [hx1, hx2, octonionConj_zero, octonionMul_zero_left]
  · rw [albertSharp_snd_1]; simp [hx1, hx2, octonionMul_zero_left]
  · rw [albertSharp_snd_2]; simp [hx1, hx2, octonionConj_zero, octonionMul_zero_left]

theorem albertCubicNorm_diag (d : Fin 3 → ℝ) :
    albertCubicNorm ((d, fun _ => 0) : Albert) = d 0 * d 1 * d 2 := by
  let x : Albert := (d, fun _ => 0)
  change albertCubicNorm x = d 0 * d 1 * d 2
  have hx1 : ∀ i : Fin 3, x.1 i = d i := fun _ => rfl
  have hx2 : ∀ i : Fin 3, x.2 i = 0 := fun _ => rfl
  unfold albertCubicNorm
  simp only [hx1, hx2, octNormSq_zero, octDot_zero_right]
  ring

/-! ## Section 2: `NativeAlbertAutomorphism` Groupoid & Covariance -/

namespace NativeAlbertAutomorphism

def refl : NativeAlbertAutomorphism where
  linearEquiv := LinearEquiv.refl ℝ Albert
  preserves_product _ _ := rfl
  preserves_unit := rfl
  preserves_trace _ := rfl

def comp (g h : NativeAlbertAutomorphism) : NativeAlbertAutomorphism where
  linearEquiv := h.linearEquiv.trans g.linearEquiv
  preserves_product x y := by
    simp only [LinearEquiv.trans_apply, h.preserves_product, g.preserves_product]
  preserves_unit := by
    simp only [LinearEquiv.trans_apply, h.preserves_unit, g.preserves_unit]
  preserves_trace x := by
    simp only [LinearEquiv.trans_apply, g.preserves_trace, h.preserves_trace]

def symm (g : NativeAlbertAutomorphism) : NativeAlbertAutomorphism where
  linearEquiv := g.linearEquiv.symm
  preserves_product x y := by
    apply g.linearEquiv.injective
    simp only [LinearEquiv.apply_symm_apply, g.preserves_product]
  preserves_unit := by
    apply g.linearEquiv.injective
    simp only [LinearEquiv.apply_symm_apply, g.preserves_unit]
  preserves_trace x := by
    conv_rhs => rw [← g.linearEquiv.apply_symm_apply x, g.preserves_trace]

theorem map_quadraticMap (g : NativeAlbertAutomorphism) (a x : Albert) :
    g.linearEquiv (quadraticMap a x) = quadraticMap (g.linearEquiv a) (g.linearEquiv x) := by
  unfold quadraticMap
  simp only [two_smul, map_sub, map_add, g.preserves_product]

theorem map_tracePairing (g : NativeAlbertAutomorphism) (x y : Albert) :
    tracePairing (g.linearEquiv x) (g.linearEquiv y) = tracePairing x y := by
  unfold tracePairing
  rw [← g.preserves_product, g.preserves_trace]

theorem map_isPositive (g : NativeAlbertAutomorphism) {x : Albert} (hx : IsPositive x) :
    IsPositive (g.linearEquiv x) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨g.linearEquiv y, g.preserves_product y y⟩

theorem map_isPositive_iff (g : NativeAlbertAutomorphism) (x : Albert) :
    IsPositive (g.linearEquiv x) ↔ IsPositive x := by
  refine ⟨fun h => ?_, g.map_isPositive⟩
  have hs := g.symm.map_isPositive h
  simpa only [show g.symm.linearEquiv = g.linearEquiv.symm from rfl, LinearEquiv.symm_apply_apply] using hs

theorem map_isAtom (g : NativeAlbertAutomorphism) {p : Albert} (hp : IsAtom p) :
    IsAtom (g.linearEquiv p) :=
  ⟨by rw [← g.preserves_product, hp.1], by rw [g.preserves_trace, hp.2]⟩

theorem map_isAtom_iff (g : NativeAlbertAutomorphism) (p : Albert) :
    IsAtom (g.linearEquiv p) ↔ IsAtom p := by
  refine ⟨fun h => ?_, g.map_isAtom⟩
  have hs := g.symm.map_isAtom h
  simpa only [show g.symm.linearEquiv = g.linearEquiv.symm from rfl, LinearEquiv.symm_apply_apply] using hs

theorem map_isDensity (g : NativeAlbertAutomorphism) {ρ : Albert} (hρ : IsDensity ρ) :
    IsDensity (g.linearEquiv ρ) :=
  ⟨g.map_isPositive hρ.1, by rw [g.preserves_trace, hρ.2]⟩

def mapFrame (g : NativeAlbertAutomorphism) (F : NativeJordanFrame) : NativeJordanFrame where
  atom i := g.linearEquiv (F.atom i)
  atoms i := g.map_isAtom (F.atoms i)
  orthogonal i j hij := by
    rw [← g.preserves_product, F.orthogonal i j hij, map_zero]
  sum_unit := by
    rw [← map_sum, F.sum_unit, g.preserves_unit]

theorem map_inGeneratedAlgebra (g : NativeAlbertAutomorphism) {ι : Type*} (p : ι → Albert)
    {x : Albert} (hx : InGeneratedAlgebra p x) :
    InGeneratedAlgebra (fun i => g.linearEquiv (p i)) (g.linearEquiv x) := by
  intro B hB
  let B' : NativeJordanSubalgebra :=
    { carrier := B.carrier.comap g.linearEquiv.toLinearMap
      unit_mem := by simp [B.unit_mem, g.preserves_unit]
      product_mem := fun a ha b hb => by
        change g.linearEquiv (jordanMul a b) ∈ B.carrier
        rw [g.preserves_product]
        exact B.product_mem _ ha _ hb }
  exact hx B' (fun i => hB i)

theorem map_generatesAlbert (g : NativeAlbertAutomorphism) {ι : Type*} (p : ι → Albert)
    (hp : GeneratesAlbert p) :
    GeneratesAlbert (fun i => g.linearEquiv (p i)) := by
  intro y
  have hy := g.map_inGeneratedAlgebra p (hp (g.linearEquiv.symm y))
  simpa only [LinearEquiv.apply_symm_apply] using hy

theorem map_sharp (g : NativeAlbertAutomorphism) (x : Albert) :
    g.linearEquiv (albertSharp x) = albertSharp (g.linearEquiv x) := by
  rw [albertSharp_eq_jordanMul, albertSharp_eq_jordanMul,
    map_add, map_sub, map_smul, map_smul, g.preserves_product, g.preserves_trace,
    g.map_tracePairing, g.preserves_unit]

theorem map_cross (g : NativeAlbertAutomorphism) (x y : Albert) :
    g.linearEquiv (albertCross x y) = albertCross (g.linearEquiv x) (g.linearEquiv y) := by
  unfold albertCross
  rw [map_sub, map_sub, g.map_sharp, g.map_sharp, g.map_sharp, map_add]

theorem map_cubicNorm (g : NativeAlbertAutomorphism) (x : Albert) :
    albertCubicNorm (g.linearEquiv x) = albertCubicNorm x := by
  rw [albertCubicNorm_eq_tracePairing, albertCubicNorm_eq_tracePairing,
    ← g.map_sharp, g.map_tracePairing]

end NativeAlbertAutomorphism

/-! ## Section 3: Slot Embeddings (`lem:A:slots`), Peirce Extraction, and `octDyad` -/

def slotElem01 : Octonion →ₗ[ℝ] Albert where
  toFun := upperSlot 0
  map_add' _ _ := by
    apply albert_ext <;> [rw [albert_add_fst]; rw [albert_add_fst]; rw [albert_add_fst];
      rw [albert_add_snd]; rw [albert_add_snd]; rw [albert_add_snd]] <;> simp [upperSlot]
  map_smul' _ _ := by
    apply albert_ext <;> [rw [albert_smul_fst]; rw [albert_smul_fst]; rw [albert_smul_fst];
      rw [albert_smul_snd]; rw [albert_smul_snd]; rw [albert_smul_snd]] <;> simp [upperSlot]

def slotElem02 : Octonion →ₗ[ℝ] Albert where
  toFun := upperSlot 1
  map_add' _ _ := by
    apply albert_ext <;> [rw [albert_add_fst]; rw [albert_add_fst]; rw [albert_add_fst];
      rw [albert_add_snd]; rw [albert_add_snd]; rw [albert_add_snd]] <;> simp [upperSlot]
  map_smul' _ _ := by
    apply albert_ext <;> [rw [albert_smul_fst]; rw [albert_smul_fst]; rw [albert_smul_fst];
      rw [albert_smul_snd]; rw [albert_smul_snd]; rw [albert_smul_snd]] <;> simp [upperSlot]

def slotElem12 : Octonion →ₗ[ℝ] Albert where
  toFun := upperSlot 2
  map_add' _ _ := by
    apply albert_ext <;> [rw [albert_add_fst]; rw [albert_add_fst]; rw [albert_add_fst];
      rw [albert_add_snd]; rw [albert_add_snd]; rw [albert_add_snd]] <;> simp [upperSlot]
  map_smul' _ _ := by
    apply albert_ext <;> [rw [albert_smul_fst]; rw [albert_smul_fst]; rw [albert_smul_fst];
      rw [albert_smul_snd]; rw [albert_smul_snd]; rw [albert_smul_snd]] <;> simp [upperSlot]

@[simp] private theorem slotElem01_fst (a : Octonion) (j : Fin 3) : (slotElem01 a).1 j = 0 := rfl
@[simp] private theorem slotElem01_snd_0 (a : Octonion) : (slotElem01 a).2 0 = a := rfl
@[simp] private theorem slotElem01_snd_1 (a : Octonion) : (slotElem01 a).2 1 = 0 := rfl
@[simp] private theorem slotElem01_snd_2 (a : Octonion) : (slotElem01 a).2 2 = 0 := rfl

private theorem slotElem01_apply (a : Octonion) :
    slotElem01 a = ((fun _ => 0, ![a, 0, 0]) : Albert) := by
  apply albert_ext <;> simp

@[simp] private theorem slotElem02_fst (a : Octonion) (j : Fin 3) : (slotElem02 a).1 j = 0 := rfl
@[simp] private theorem slotElem02_snd_0 (a : Octonion) : (slotElem02 a).2 0 = 0 := rfl
@[simp] private theorem slotElem02_snd_1 (a : Octonion) : (slotElem02 a).2 1 = a := rfl
@[simp] private theorem slotElem02_snd_2 (a : Octonion) : (slotElem02 a).2 2 = 0 := rfl

@[simp] private theorem slotElem12_fst (a : Octonion) (j : Fin 3) : (slotElem12 a).1 j = 0 := rfl
@[simp] private theorem slotElem12_snd_0 (a : Octonion) : (slotElem12 a).2 0 = 0 := rfl
@[simp] private theorem slotElem12_snd_1 (a : Octonion) : (slotElem12 a).2 1 = 0 := rfl
@[simp] private theorem slotElem12_snd_2 (a : Octonion) : (slotElem12 a).2 2 = a := rfl

theorem jordanMul_slotElem01_slotElem12 (a b : Octonion) :
    jordanMul (slotElem01 a) (slotElem12 b) = (1 / 2 : ℝ) • slotElem02 (octonionMul a b) := by
  apply albert_ext
  · simp [jordanMul_diag_0, albert_smul_fst, octDot_zero_right]
  · simp [jordanMul_diag_1, albert_smul_fst, octDot_zero_left, octDot_zero_right]
  · simp [jordanMul_diag_2, albert_smul_fst, octDot_zero_left, octDot_zero_right]
  · simp [jordanMul_off_0, albert_smul_snd, octonionMul_zero_left]
  · simp [jordanMul_off_1, albert_smul_snd, octonionMul_zero_left]
  · simp [jordanMul_off_2, albert_smul_snd, octonionConj_zero, octonionMul_zero_right]

theorem jordanMul_slotElem02_slotElem12 (a b : Octonion) :
    jordanMul (slotElem02 a) (slotElem12 b) =
      (1 / 2 : ℝ) • slotElem01 (octonionMul a (octonionConj b)) := by
  apply albert_ext
  · simp [jordanMul_diag_0, albert_smul_fst, octDot_zero_right]
  · simp [jordanMul_diag_1, albert_smul_fst, octDot_zero_left, octDot_zero_right]
  · simp [jordanMul_diag_2, albert_smul_fst, octDot_zero_left, octDot_zero_right]
  · simp [jordanMul_off_0, albert_smul_snd, octonionMul_zero_left]
  · simp [jordanMul_off_1, albert_smul_snd, octonionMul_zero_left, octonionMul_zero_right]
  · simp [jordanMul_off_2, albert_smul_snd, octonionConj_zero, octonionMul_zero_left,
      octonionMul_zero_right]

theorem jordanMul_slotElem01_slotElem02 (a b : Octonion) :
    jordanMul (slotElem01 a) (slotElem02 b) =
      (1 / 2 : ℝ) • slotElem12 (octonionMul (octonionConj a) b) := by
  apply albert_ext
  · simp [jordanMul_diag_0, albert_smul_fst, octDot_zero_left, octDot_zero_right]
  · simp [jordanMul_diag_1, albert_smul_fst, octDot_zero_right]
  · simp [jordanMul_diag_2, albert_smul_fst, octDot_zero_left, octDot_zero_right]
  · simp [jordanMul_off_0, albert_smul_snd, octonionConj_zero, octonionMul_zero_right]
  · simp [jordanMul_off_1, albert_smul_snd, octonionMul_zero_right]
  · simp [jordanMul_off_2, albert_smul_snd, octonionConj_zero, octonionMul_zero_left]

theorem jordanMul_slotElem01_self (a : Octonion) :
    jordanMul (slotElem01 a) (slotElem01 a) = octNormSq a • (diagAtom 0 + diagAtom 1) := by
  apply albert_ext
  · simp [jordanMul_diag_0, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_diag_1, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_diag_2, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_off_0, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionConj_zero,
      octonionMul_zero_left]
  · simp [jordanMul_off_1, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionMul_zero_right]
  · simp [jordanMul_off_2, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionMul_zero_right]

theorem jordanMul_slotElem02_self (a : Octonion) :
    jordanMul (slotElem02 a) (slotElem02 a) = octNormSq a • (diagAtom 0 + diagAtom 2) := by
  apply albert_ext
  · simp [jordanMul_diag_0, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_diag_1, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_diag_2, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_off_0, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionConj_zero,
      octonionMul_zero_right]
  · simp [jordanMul_off_1, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionMul_zero_left]
  · simp [jordanMul_off_2, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionConj_zero,
      octonionMul_zero_left]

theorem jordanMul_slotElem12_self (a : Octonion) :
    jordanMul (slotElem12 a) (slotElem12 a) = octNormSq a • (diagAtom 1 + diagAtom 2) := by
  apply albert_ext
  · simp [jordanMul_diag_0, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_diag_1, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_diag_2, albert_smul_fst, albert_add_fst, diagAtom_fst, octDot_self,
      octNormSq_zero]
  · simp [jordanMul_off_0, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionMul_zero_left]
  · simp [jordanMul_off_1, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionMul_zero_left]
  · simp [jordanMul_off_2, albert_smul_snd, albert_add_snd, diagAtom_snd, octonionConj_zero,
      octonionMul_zero_left]

private theorem jordanMul_diagAtom0_fst_0 (x : Albert) : (jordanMul (diagAtom 0) x).1 0 = x.1 0 := by
  rw [jordanMul_diag_0, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom0_fst_1 (x : Albert) : (jordanMul (diagAtom 0) x).1 1 = 0 := by
  rw [jordanMul_diag_1, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom0_fst_2 (x : Albert) : (jordanMul (diagAtom 0) x).1 2 = 0 := by
  rw [jordanMul_diag_2, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom0_snd_0 (x : Albert) :
    (jordanMul (diagAtom 0) x).2 0 = (1 / 2 : ℝ) • x.2 0 := by
  rw [jordanMul_off_0, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right]
  norm_num

private theorem jordanMul_diagAtom0_snd_1 (x : Albert) :
    (jordanMul (diagAtom 0) x).2 1 = (1 / 2 : ℝ) • x.2 1 := by
  rw [jordanMul_off_1, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionMul_zero_left, octonionMul_zero_right]
  norm_num

private theorem jordanMul_diagAtom0_snd_2 (x : Albert) : (jordanMul (diagAtom 0) x).2 2 = 0 := by
  rw [jordanMul_off_2, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right]
  norm_num

private theorem jordanMul_diagAtom1_fst_0 (x : Albert) : (jordanMul (diagAtom 1) x).1 0 = 0 := by
  rw [jordanMul_diag_0, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom1_fst_1 (x : Albert) : (jordanMul (diagAtom 1) x).1 1 = x.1 1 := by
  rw [jordanMul_diag_1, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom1_fst_2 (x : Albert) : (jordanMul (diagAtom 1) x).1 2 = 0 := by
  rw [jordanMul_diag_2, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom1_snd_0 (x : Albert) :
    (jordanMul (diagAtom 1) x).2 0 = (1 / 2 : ℝ) • x.2 0 := by
  rw [jordanMul_off_0, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right]
  norm_num

private theorem jordanMul_diagAtom1_snd_1 (x : Albert) : (jordanMul (diagAtom 1) x).2 1 = 0 := by
  rw [jordanMul_off_1, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionMul_zero_left, octonionMul_zero_right]
  norm_num

private theorem jordanMul_diagAtom1_snd_2 (x : Albert) :
    (jordanMul (diagAtom 1) x).2 2 = (1 / 2 : ℝ) • x.2 2 := by
  rw [jordanMul_off_2, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right]
  norm_num

private theorem jordanMul_diagAtom2_fst_0 (x : Albert) : (jordanMul (diagAtom 2) x).1 0 = 0 := by
  rw [jordanMul_diag_0, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom2_fst_1 (x : Albert) : (jordanMul (diagAtom 2) x).1 1 = 0 := by
  rw [jordanMul_diag_1, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom2_fst_2 (x : Albert) : (jordanMul (diagAtom 2) x).1 2 = x.1 2 := by
  rw [jordanMul_diag_2, diagAtom_fst, diagAtom_snd, diagAtom_snd, octDot_zero_left, octDot_zero_left]
  norm_num

private theorem jordanMul_diagAtom2_snd_0 (x : Albert) : (jordanMul (diagAtom 2) x).2 0 = 0 := by
  rw [jordanMul_off_0, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right]
  norm_num

private theorem jordanMul_diagAtom2_snd_1 (x : Albert) :
    (jordanMul (diagAtom 2) x).2 1 = (1 / 2 : ℝ) • x.2 1 := by
  rw [jordanMul_off_1, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionMul_zero_left, octonionMul_zero_right]
  norm_num

private theorem jordanMul_diagAtom2_snd_2 (x : Albert) :
    (jordanMul (diagAtom 2) x).2 2 = (1 / 2 : ℝ) • x.2 2 := by
  rw [jordanMul_off_2, diagAtom_fst, diagAtom_fst, diagAtom_snd, diagAtom_snd, diagAtom_snd,
    octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right]
  norm_num

theorem jordanMul_diagAtom0 (x : Albert) :
    jordanMul (diagAtom 0) x =
      ((![x.1 0, 0, 0], ![(1 / 2 : ℝ) • x.2 0, (1 / 2 : ℝ) • x.2 1, 0]) : Albert) := by
  apply albert_ext
  · exact jordanMul_diagAtom0_fst_0 x
  · exact jordanMul_diagAtom0_fst_1 x
  · exact jordanMul_diagAtom0_fst_2 x
  · exact jordanMul_diagAtom0_snd_0 x
  · exact jordanMul_diagAtom0_snd_1 x
  · exact jordanMul_diagAtom0_snd_2 x

theorem jordanMul_diagAtom1 (x : Albert) :
    jordanMul (diagAtom 1) x =
      ((![0, x.1 1, 0], ![(1 / 2 : ℝ) • x.2 0, 0, (1 / 2 : ℝ) • x.2 2]) : Albert) := by
  apply albert_ext
  · exact jordanMul_diagAtom1_fst_0 x
  · exact jordanMul_diagAtom1_fst_1 x
  · exact jordanMul_diagAtom1_fst_2 x
  · exact jordanMul_diagAtom1_snd_0 x
  · exact jordanMul_diagAtom1_snd_1 x
  · exact jordanMul_diagAtom1_snd_2 x

theorem jordanMul_diagAtom2 (x : Albert) :
    jordanMul (diagAtom 2) x =
      ((![0, 0, x.1 2], ![0, (1 / 2 : ℝ) • x.2 1, (1 / 2 : ℝ) • x.2 2]) : Albert) := by
  apply albert_ext
  · exact jordanMul_diagAtom2_fst_0 x
  · exact jordanMul_diagAtom2_fst_1 x
  · exact jordanMul_diagAtom2_fst_2 x
  · exact jordanMul_diagAtom2_snd_0 x
  · exact jordanMul_diagAtom2_snd_1 x
  · exact jordanMul_diagAtom2_snd_2 x

theorem peirce01_extract (x : Albert) :
    (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 1) x) = slotElem01 (x.2 0) := by
  apply albert_ext
  · rw [albert_smul_fst, jordanMul_diagAtom0_fst_0, jordanMul_diagAtom1_fst_0, slotElem01_fst]; ring
  · rw [albert_smul_fst, jordanMul_diagAtom0_fst_1, slotElem01_fst]; ring
  · rw [albert_smul_fst, jordanMul_diagAtom0_fst_2, slotElem01_fst]; ring
  · rw [albert_smul_snd, jordanMul_diagAtom0_snd_0, jordanMul_diagAtom1_snd_0, slotElem01_snd_0,
      smul_smul, smul_smul]
    norm_num
  · rw [albert_smul_snd, jordanMul_diagAtom0_snd_1, jordanMul_diagAtom1_snd_1, slotElem01_snd_1]
    simp
  · rw [albert_smul_snd, jordanMul_diagAtom0_snd_2, slotElem01_snd_2]; simp

theorem peirce02_extract (x : Albert) :
    (4 : ℝ) • jordanMul (diagAtom 0) (jordanMul (diagAtom 2) x) = slotElem02 (x.2 1) := by
  apply albert_ext
  · rw [albert_smul_fst, jordanMul_diagAtom0_fst_0, jordanMul_diagAtom2_fst_0, slotElem02_fst]; ring
  · rw [albert_smul_fst, jordanMul_diagAtom0_fst_1, slotElem02_fst]; ring
  · rw [albert_smul_fst, jordanMul_diagAtom0_fst_2, slotElem02_fst]; ring
  · rw [albert_smul_snd, jordanMul_diagAtom0_snd_0, jordanMul_diagAtom2_snd_0, slotElem02_snd_0]
    simp
  · rw [albert_smul_snd, jordanMul_diagAtom0_snd_1, jordanMul_diagAtom2_snd_1, slotElem02_snd_1,
      smul_smul, smul_smul]
    norm_num
  · rw [albert_smul_snd, jordanMul_diagAtom0_snd_2, slotElem02_snd_2]; simp

theorem peirce12_extract (x : Albert) :
    (4 : ℝ) • jordanMul (diagAtom 1) (jordanMul (diagAtom 2) x) = slotElem12 (x.2 2) := by
  apply albert_ext
  · rw [albert_smul_fst, jordanMul_diagAtom1_fst_0, slotElem12_fst]; ring
  · rw [albert_smul_fst, jordanMul_diagAtom1_fst_1, jordanMul_diagAtom2_fst_1, slotElem12_fst]; ring
  · rw [albert_smul_fst, jordanMul_diagAtom1_fst_2, slotElem12_fst]; ring
  · rw [albert_smul_snd, jordanMul_diagAtom1_snd_0, jordanMul_diagAtom2_snd_0, slotElem12_snd_0]
    simp
  · rw [albert_smul_snd, jordanMul_diagAtom1_snd_1, slotElem12_snd_1]; simp
  · rw [albert_smul_snd, jordanMul_diagAtom1_snd_2, jordanMul_diagAtom2_snd_2, slotElem12_snd_2,
      smul_smul, smul_smul]
    norm_num

private theorem eq_slotElem01_of_peirce {x : Albert}
    (h0 : jordanMul (diagAtom 0) x = (1 / 2 : ℝ) • x)
    (h1 : jordanMul (diagAtom 1) x = (1 / 2 : ℝ) • x) :
    x = slotElem01 (x.2 0) := by
  have hp := peirce01_extract x
  rw [h1, jordanMul_smul_right, h0, smul_smul, smul_smul] at hp
  norm_num at hp
  exact hp

private theorem eq_slotElem02_of_peirce {x : Albert}
    (h0 : jordanMul (diagAtom 0) x = (1 / 2 : ℝ) • x)
    (h2 : jordanMul (diagAtom 2) x = (1 / 2 : ℝ) • x) :
    x = slotElem02 (x.2 1) := by
  have hp := peirce02_extract x
  rw [h2, jordanMul_smul_right, h0, smul_smul, smul_smul] at hp
  norm_num at hp
  exact hp

private theorem eq_slotElem12_of_peirce {x : Albert}
    (h1 : jordanMul (diagAtom 1) x = (1 / 2 : ℝ) • x)
    (h2 : jordanMul (diagAtom 2) x = (1 / 2 : ℝ) • x) :
    x = slotElem12 (x.2 2) := by
  have hp := peirce12_extract x
  rw [h2, jordanMul_smul_right, h1, smul_smul, smul_smul] at hp
  norm_num at hp
  exact hp

theorem slotElem01_mem_02_of_mem {B : NativeJordanSubalgebra}
    (hs12 : slotElem12 octOne ∈ B.carrier) {a : Octonion}
    (ha : slotElem01 a ∈ B.carrier) : slotElem02 a ∈ B.carrier := by
  have hmul := B.product_mem _ ha _ hs12
  rw [jordanMul_slotElem01_slotElem12, octonionMul_one_right] at hmul
  have hs := B.carrier.smul_mem (2 : ℝ) hmul
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul] using hs

theorem slotElem02_mem_12_of_mem {B : NativeJordanSubalgebra}
    (hs01 : slotElem01 octOne ∈ B.carrier) {a : Octonion}
    (ha : slotElem02 a ∈ B.carrier) : slotElem12 a ∈ B.carrier := by
  have hmul := B.product_mem _ hs01 _ ha
  rw [jordanMul_slotElem01_slotElem02, octonionConj_one, octonionMul_one_left] at hmul
  have hs := B.carrier.smul_mem (2 : ℝ) hmul
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul] using hs

theorem slotElem12_mem_01_of_mem {B : NativeJordanSubalgebra}
    (hs02 : slotElem02 octOne ∈ B.carrier) {a : Octonion}
    (ha : slotElem12 a ∈ B.carrier) : slotElem01 (octonionConj a) ∈ B.carrier := by
  have hmul := B.product_mem _ hs02 _ ha
  rw [jordanMul_slotElem02_slotElem12, octonionMul_one_left] at hmul
  have hs := B.carrier.smul_mem (2 : ℝ) hmul
  simpa only [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul] using hs

def slotSubalgebraOfJordanSubalgebra (B : NativeJordanSubalgebra)
    (_hd0 : diagAtom 0 ∈ B.carrier) (_hd1 : diagAtom 1 ∈ B.carrier) (_hd2 : diagAtom 2 ∈ B.carrier)
    (hs01 : slotElem01 octOne ∈ B.carrier) (hs02 : slotElem02 octOne ∈ B.carrier)
    (hs12 : slotElem12 octOne ∈ B.carrier) : OctSubalgebra where
  carrier := B.carrier.comap slotElem01
  one_mem := hs01
  conj_mem a ha := octSubalgebra_conj_mem_auto _ hs01 a ha
  mul_mem a ha b hb := by
    change slotElem01 a ∈ B.carrier at ha
    change slotElem01 b ∈ B.carrier at hb
    have hb02 : slotElem02 b ∈ B.carrier := slotElem01_mem_02_of_mem hs12 hb
    have hb12 : slotElem12 b ∈ B.carrier := slotElem02_mem_12_of_mem hs01 hb02
    have h02 : slotElem02 (octonionMul a b) ∈ B.carrier := by
      have hmul := B.product_mem _ ha _ hb12
      rw [jordanMul_slotElem01_slotElem12] at hmul
      simpa only [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 from by norm_num, one_smul] using
        B.carrier.smul_mem (2 : ℝ) hmul
    have h12 : slotElem12 (octonionMul a b) ∈ B.carrier := slotElem02_mem_12_of_mem hs01 h02
    have hconj : slotElem01 (octonionConj (octonionMul a b)) ∈ B.carrier :=
      slotElem12_mem_01_of_mem hs02 h12
    have hre : octonionReal (octonionMul a b) • octOne =
        octonionScalar (octonionReal (octonionMul a b)) := by
      simpa only [octOne] using (octonionScalar_eq_smul (octonionReal (octonionMul a b))).symm
    have htwo : (2 : ℝ) • octonionScalar (octonionReal (octonionMul a b)) -
        octonionConj (octonionMul a b) = octonionMul a b := by
      rw [← octAdd_conj]
      abel
    change slotElem01 (octonionMul a b) ∈ B.carrier
    rw [← htwo, map_sub, map_smul, ← hre, map_smul]
    exact B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (B.carrier.smul_mem _ hs01)) hconj

theorem mem_slotSubalgebra_iff_slotElem01 (B : NativeJordanSubalgebra)
    (hd0 : diagAtom 0 ∈ B.carrier) (hd1 : diagAtom 1 ∈ B.carrier) (hd2 : diagAtom 2 ∈ B.carrier)
    (hs01 : slotElem01 octOne ∈ B.carrier) (hs02 : slotElem02 octOne ∈ B.carrier)
    (hs12 : slotElem12 octOne ∈ B.carrier) (a : Octonion) :
    a ∈ (slotSubalgebraOfJordanSubalgebra B hd0 hd1 hd2 hs01 hs02 hs12).carrier ↔
      slotElem01 a ∈ B.carrier :=
  Iff.rfl

theorem mem_slotSubalgebra_iff_slotElem02 (B : NativeJordanSubalgebra)
    (hd0 : diagAtom 0 ∈ B.carrier) (hd1 : diagAtom 1 ∈ B.carrier) (hd2 : diagAtom 2 ∈ B.carrier)
    (hs01 : slotElem01 octOne ∈ B.carrier) (hs02 : slotElem02 octOne ∈ B.carrier)
    (hs12 : slotElem12 octOne ∈ B.carrier) (a : Octonion) :
    a ∈ (slotSubalgebraOfJordanSubalgebra B hd0 hd1 hd2 hs01 hs02 hs12).carrier ↔
      slotElem02 a ∈ B.carrier := by
  rw [mem_slotSubalgebra_iff_slotElem01]
  constructor
  · exact slotElem01_mem_02_of_mem hs12
  · intro h02
    have h12 : slotElem12 a ∈ B.carrier := slotElem02_mem_12_of_mem hs01 h02
    have hconj : slotElem01 (octonionConj a) ∈ B.carrier := slotElem12_mem_01_of_mem hs02 h12
    have hre : (2 : ℝ) • octonionScalar (octonionReal a) - octonionConj a = a := by
      rw [← octAdd_conj]; abel
    have hsc : octonionScalar (octonionReal a) = octonionReal a • octOne :=
      octonionScalar_eq_smul (octonionReal a)
    rw [← hre, map_sub, map_smul, hsc, map_smul]
    exact B.carrier.sub_mem (B.carrier.smul_mem (2 : ℝ) (B.carrier.smul_mem _ hs01)) hconj

theorem mem_slotSubalgebra_iff_slotElem12 (B : NativeJordanSubalgebra)
    (hd0 : diagAtom 0 ∈ B.carrier) (hd1 : diagAtom 1 ∈ B.carrier) (hd2 : diagAtom 2 ∈ B.carrier)
    (hs01 : slotElem01 octOne ∈ B.carrier) (hs02 : slotElem02 octOne ∈ B.carrier)
    (hs12 : slotElem12 octOne ∈ B.carrier) (a : Octonion) :
    a ∈ (slotSubalgebraOfJordanSubalgebra B hd0 hd1 hd2 hs01 hs02 hs12).carrier ↔
      slotElem12 a ∈ B.carrier := by
  constructor
  · intro ha
    exact slotElem02_mem_12_of_mem hs01
      ((mem_slotSubalgebra_iff_slotElem02 B hd0 hd1 hd2 hs01 hs02 hs12 a).mp ha)
  · intro h12
    have hconj : slotElem01 (octonionConj a) ∈ B.carrier := slotElem12_mem_01_of_mem hs02 h12
    have hc := octSubalgebra_conj_mem_auto (B.carrier.comap slotElem01) hs01 _ hconj
    rw [octonionConj_conj] at hc
    exact hc

def slotSubalgebraOfJordanSubalgebra_01_12 (B : NativeJordanSubalgebra)
    (hd0 : diagAtom 0 ∈ B.carrier) (hd1 : diagAtom 1 ∈ B.carrier) (hd2 : diagAtom 2 ∈ B.carrier)
    (hs01 : slotElem01 octOne ∈ B.carrier) (hs12 : slotElem12 octOne ∈ B.carrier) :
    OctSubalgebra :=
  slotSubalgebraOfJordanSubalgebra B hd0 hd1 hd2 hs01 (slotElem01_mem_02_of_mem hs12 hs01) hs12

def slotSubalgebraOfJordanSubalgebra_01_02 (B : NativeJordanSubalgebra)
    (hd0 : diagAtom 0 ∈ B.carrier) (hd1 : diagAtom 1 ∈ B.carrier) (hd2 : diagAtom 2 ∈ B.carrier)
    (hs01 : slotElem01 octOne ∈ B.carrier) (hs02 : slotElem02 octOne ∈ B.carrier) :
    OctSubalgebra :=
  slotSubalgebraOfJordanSubalgebra B hd0 hd1 hd2 hs01 hs02 (slotElem02_mem_12_of_mem hs01 hs02)

def slotSubalgebraOfJordanSubalgebra_02_12 (B : NativeJordanSubalgebra)
    (hd0 : diagAtom 0 ∈ B.carrier) (hd1 : diagAtom 1 ∈ B.carrier) (hd2 : diagAtom 2 ∈ B.carrier)
    (hs02 : slotElem02 octOne ∈ B.carrier) (hs12 : slotElem12 octOne ∈ B.carrier) :
    OctSubalgebra :=
  slotSubalgebraOfJordanSubalgebra B hd0 hd1 hd2
    (by simpa [octonionConj_one] using slotElem12_mem_01_of_mem hs02 hs12) hs02 hs12

def octDyad (v : Fin 3 → Octonion) : Albert :=
  (fun i => octNormSq (v i),
   ![octonionMul (v 0) (octonionConj (v 1)),
     octonionMul (v 0) (octonionConj (v 2)),
     octonionMul (v 1) (octonionConj (v 2))])

private theorem octDyad_fst (v : Fin 3 → Octonion) (i : Fin 3) :
    (octDyad v).1 i = octNormSq (v i) := rfl
private theorem octDyad_snd_0 (v : Fin 3 → Octonion) :
    (octDyad v).2 0 = octonionMul (v 0) (octonionConj (v 1)) := rfl
private theorem octDyad_snd_1 (v : Fin 3 → Octonion) :
    (octDyad v).2 1 = octonionMul (v 0) (octonionConj (v 2)) := rfl
private theorem octDyad_snd_2 (v : Fin 3 → Octonion) :
    (octDyad v).2 2 = octonionMul (v 1) (octonionConj (v 2)) := rfl

theorem octDyad_eq_quatDyad (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (u : Fin 3 → Quaternion ℝ) :
    octDyad (fun i => φ (u i)) = quatDyad φ u 1 := by
  have hmul : ∀ a b : Quaternion ℝ,
      octonionMul (φ a) (octonionConj (φ b)) = φ (a * star b) := fun a b => by
    rw [← hφ.map_star, ← hφ.map_mul]
  have hns : ∀ a : Quaternion ℝ, octNormSq (φ a) = (a * star a).re := fun a => by
    rw [octNormSq, octDot, hmul a a, hφ.map_re]
  apply albert_ext
  · rw [octDyad_fst, hns]; simp [quatDyad]
  · rw [octDyad_fst, hns]; simp [quatDyad]
  · rw [octDyad_fst, hns]; simp [quatDyad]
  · rw [octDyad_snd_0, hmul]; simp [quatDyad]
  · rw [octDyad_snd_1, hmul]; simp [quatDyad]
  · rw [octDyad_snd_2, hmul]; simp [quatDyad]

private theorem octNormSq_quatEmbedding (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (q : Quaternion ℝ) : octNormSq (φ q) = quatNormSq q := by
  rw [octNormSq, octDot, ← hφ.map_star, ← hφ.map_mul, hφ.map_re]
  change (q * star q).re = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2
  rw [Quaternion.re_mul]
  simp only [Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

theorem octDyad_isAtom (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (v : Fin 3 → Octonion) (hv : ∀ i, v i ∈ Set.range φ)
    (hnorm : ∑ i : Fin 3, octNormSq (v i) = 1) : IsAtom (octDyad v) := by
  choose u hu using hv
  have hveq : v = fun i => φ (u i) := funext (fun i => (hu i).symm)
  rw [hveq, octDyad_eq_quatDyad φ hφ u]
  refine quatDyad_isAtom φ hφ u 1 one_ne_zero ?_
  have hvi : ∀ i : Fin 3, φ (u i) = v i := fun i => (congrFun hveq i).symm
  calc
    ∑ i : Fin 3, quatNormSq (u i) = ∑ i : Fin 3, octNormSq (φ (u i)) :=
      Finset.sum_congr rfl fun i _ => (octNormSq_quatEmbedding φ hφ (u i)).symm
    _ = 1 := by simp_rw [hvi]; exact hnorm

theorem albertSharp_octDyad_eq_zero (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (v : Fin 3 → Octonion) (hv : ∀ i, v i ∈ Set.range φ)
    (hnorm : ∑ i : Fin 3, octNormSq (v i) = 1) : albertSharp (octDyad v) = 0 :=
  albertSharp_of_isAtom (octDyad_isAtom φ hφ v hv hnorm)

theorem isAtom_diag_nonneg {p : Albert} (hp : IsAtom p) (i : Fin 3) : 0 ≤ p.1 i := by
  fin_cases i <;> dsimp
  · have h := congrArg (fun a : Albert => a.1 0) hp.1
    rw [jordanMul_diag_0, octDot_self, octDot_self] at h
    nlinarith [sq_nonneg (p.1 0), octNormSq_nonneg (p.2 0), octNormSq_nonneg (p.2 1)]
  · have h := congrArg (fun a : Albert => a.1 1) hp.1
    rw [jordanMul_diag_1, octDot_self, octDot_self] at h
    nlinarith [sq_nonneg (p.1 1), octNormSq_nonneg (p.2 0), octNormSq_nonneg (p.2 2)]
  · have h := congrArg (fun a : Albert => a.1 2) hp.1
    rw [jordanMul_diag_2, octDot_self, octDot_self] at h
    nlinarith [sq_nonneg (p.1 2), octNormSq_nonneg (p.2 1), octNormSq_nonneg (p.2 2)]

theorem isAtom_diag_le_one {p : Albert} (hp : IsAtom p) (i : Fin 3) : p.1 i ≤ 1 := by
  have htr : p.1 0 + p.1 1 + p.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three] using hp.2
  have h0 := isAtom_diag_nonneg hp 0
  have h1 := isAtom_diag_nonneg hp 1
  have h2 := isAtom_diag_nonneg hp 2
  fin_cases i <;> dsimp <;> linarith

theorem isAtom_zero_row0 {p : Albert} (hp : IsAtom p) (h0 : p.1 0 = 0) :
    p.2 0 = 0 ∧ p.2 1 = 0 := by
  have h := congrArg (fun a : Albert => a.1 0) hp.1
  rw [jordanMul_diag_0, octDot_self, octDot_self, h0] at h
  have ha := octNormSq_nonneg (p.2 0)
  have hb := octNormSq_nonneg (p.2 1)
  exact ⟨(octNormSq_eq_zero _).mp (by linarith), (octNormSq_eq_zero _).mp (by linarith)⟩

theorem isAtom_zero_row1 {p : Albert} (hp : IsAtom p) (h1 : p.1 1 = 0) :
    p.2 0 = 0 ∧ p.2 2 = 0 := by
  have h := congrArg (fun a : Albert => a.1 1) hp.1
  rw [jordanMul_diag_1, octDot_self, octDot_self, h1] at h
  have ha := octNormSq_nonneg (p.2 0)
  have hb := octNormSq_nonneg (p.2 2)
  exact ⟨(octNormSq_eq_zero _).mp (by linarith), (octNormSq_eq_zero _).mp (by linarith)⟩

theorem isAtom_zero_row2 {p : Albert} (hp : IsAtom p) (h2 : p.1 2 = 0) :
    p.2 1 = 0 ∧ p.2 2 = 0 := by
  have h := congrArg (fun a : Albert => a.1 2) hp.1
  rw [jordanMul_diag_2, octDot_self, octDot_self, h2] at h
  have ha := octNormSq_nonneg (p.2 1)
  have hb := octNormSq_nonneg (p.2 2)
  exact ⟨(octNormSq_eq_zero _).mp (by linarith), (octNormSq_eq_zero _).mp (by linarith)⟩

theorem isAtom_eq_octDyad {p : Albert} (hp : IsAtom p) (h0 : 0 < p.1 0) :
    let s := Real.sqrt (p.1 0)
    let v : Fin 3 → Octonion :=
      ![octonionScalar s, (1 / s) • octonionConj (p.2 0), (1 / s) • octonionConj (p.2 1)]
    p = octDyad v ∧ ∑ i : Fin 3, octNormSq (v i) = 1 := by
  intro s v
  have hspos : 0 < s := Real.sqrt_pos.mpr h0
  have hsne : s ≠ 0 := hspos.ne'
  have hs2 : s ^ 2 = p.1 0 := Real.sq_sqrt h0.le
  have hsharp := albertSharp_of_isAtom hp
  have hd2 : octNormSq (p.2 0) = p.1 0 * p.1 1 := by
    have hz := congrArg (fun a : Albert => a.1 2) hsharp
    rw [albertSharp_fst_2, albert_zero_fst] at hz
    linarith
  have hd1 : octNormSq (p.2 1) = p.1 0 * p.1 2 := by
    have hz := congrArg (fun a : Albert => a.1 1) hsharp
    rw [albertSharp_fst_1, albert_zero_fst] at hz
    linarith
  have ho2 : p.1 0 • p.2 2 = octonionMul (octonionConj (p.2 0)) (p.2 1) := by
    have hz := congrArg (fun a : Albert => a.2 2) hsharp
    rw [albertSharp_snd_2, albert_zero_snd] at hz
    exact (sub_eq_zero.mp hz).symm
  have hv0 : v 0 = octonionScalar s := rfl
  have hv1 : v 1 = (1 / s) • octonionConj (p.2 0) := rfl
  have hv2 : v 2 = (1 / s) • octonionConj (p.2 1) := rfl
  have hnorm0 : octNormSq (v 0) = p.1 0 := by
    rw [hv0, octonionScalar_eq_smul, ← octOne, octNormSq_smul, octNormSq_one, mul_one]
    exact hs2
  have hnorm1 : octNormSq (v 1) = p.1 1 := by
    rw [hv1, octNormSq_smul, octNormSq_conj, hd2, one_div, inv_pow, hs2]
    field_simp [h0.ne']
  have hnorm2 : octNormSq (v 2) = p.1 2 := by
    rw [hv2, octNormSq_smul, octNormSq_conj, hd1, one_div, inv_pow, hs2]
    field_simp [h0.ne']
  refine ⟨?_, ?_⟩
  · apply albert_ext
    · rw [octDyad_fst]; exact hnorm0.symm
    · rw [octDyad_fst]; exact hnorm1.symm
    · rw [octDyad_fst]; exact hnorm2.symm
    · rw [octDyad_snd_0, hv0, hv1, octonionConj_smul, octonionConj_conj,
        octonionMul_smul_right, octonionMul_scalar_left, smul_smul]
      have hss : (1 / s) * s = 1 := by field_simp [hsne]
      rw [hss, one_smul]
    · rw [octDyad_snd_1, hv0, hv2, octonionConj_smul, octonionConj_conj,
        octonionMul_smul_right, octonionMul_scalar_left, smul_smul]
      have hss : (1 / s) * s = 1 := by field_simp [hsne]
      rw [hss, one_smul]
    · rw [octDyad_snd_2, hv1, hv2, octonionConj_smul, octonionConj_conj,
        octonionMul_smul_left, octonionMul_smul_right, smul_smul, ← ho2, smul_smul]
      have hinv : (1 / s) * (1 / s) * p.1 0 = 1 := by
        rw [← hs2]
        field_simp [hsne]
      rw [hinv, one_smul]
  · rw [Fin.sum_univ_three, hnorm0, hnorm1, hnorm2]
    simpa [albertTrace, Fin.sum_univ_three] using hp.2

/-! ## Section 4: Octonionic, Orthogonal, Permutation, and Moufang Automorphisms -/

def octAutoFun (α : OctonionAutomorphism) (x : Albert) : Albert :=
  (x.1, fun k => α.equiv (x.2 k))

def octAutoInvFun (α : OctonionAutomorphism) (x : Albert) : Albert :=
  (x.1, fun k => α.equiv.symm (x.2 k))

private theorem octAutoFun_fst (α : OctonionAutomorphism) (x : Albert) (j : Fin 3) :
    (octAutoFun α x).1 j = x.1 j := rfl
private theorem octAutoFun_snd (α : OctonionAutomorphism) (x : Albert) (k : Fin 3) :
    (octAutoFun α x).2 k = α.equiv (x.2 k) := rfl

def octAutoEquiv (α : OctonionAutomorphism) : Albert ≃ₗ[ℝ] Albert where
  toFun := octAutoFun α
  invFun := octAutoInvFun α
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext k; exact α.equiv.symm_apply_apply _
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext k; exact α.equiv.apply_symm_apply _
  map_add' x y := by
    apply albert_ext
    · rw [octAutoFun_fst, albert_add_fst, albert_add_fst, octAutoFun_fst, octAutoFun_fst]
    · rw [octAutoFun_fst, albert_add_fst, albert_add_fst, octAutoFun_fst, octAutoFun_fst]
    · rw [octAutoFun_fst, albert_add_fst, albert_add_fst, octAutoFun_fst, octAutoFun_fst]
    · rw [octAutoFun_snd, albert_add_snd, albert_add_snd, octAutoFun_snd, octAutoFun_snd,
        α.equiv.map_add]
    · rw [octAutoFun_snd, albert_add_snd, albert_add_snd, octAutoFun_snd, octAutoFun_snd,
        α.equiv.map_add]
    · rw [octAutoFun_snd, albert_add_snd, albert_add_snd, octAutoFun_snd, octAutoFun_snd,
        α.equiv.map_add]
  map_smul' r x := by
    apply albert_ext
    · rw [octAutoFun_fst, albert_smul_fst, albert_smul_fst, octAutoFun_fst]; rfl
    · rw [octAutoFun_fst, albert_smul_fst, albert_smul_fst, octAutoFun_fst]; rfl
    · rw [octAutoFun_fst, albert_smul_fst, albert_smul_fst, octAutoFun_fst]; rfl
    · rw [octAutoFun_snd, albert_smul_snd, albert_smul_snd, octAutoFun_snd, α.equiv.map_smul]; rfl
    · rw [octAutoFun_snd, albert_smul_snd, albert_smul_snd, octAutoFun_snd, α.equiv.map_smul]; rfl
    · rw [octAutoFun_snd, albert_smul_snd, albert_smul_snd, octAutoFun_snd, α.equiv.map_smul]; rfl

private theorem octAutoEquiv_fst (α : OctonionAutomorphism) (x : Albert) (j : Fin 3) :
    (octAutoEquiv α x).1 j = x.1 j := rfl
private theorem octAutoEquiv_snd (α : OctonionAutomorphism) (x : Albert) (k : Fin 3) :
    (octAutoEquiv α x).2 k = α.equiv (x.2 k) := rfl

def octAutoToAlbertAuto (α : OctonionAutomorphism) : NativeAlbertAutomorphism where
  linearEquiv := octAutoEquiv α
  preserves_product x y := by
    apply albert_ext
    · rw [octAutoEquiv_fst, jordanMul_diag_0, jordanMul_diag_0,
        octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_snd, octAutoEquiv_snd,
        octAutoEquiv_snd, octAutoEquiv_snd, α.map_dot, α.map_dot]
    · rw [octAutoEquiv_fst, jordanMul_diag_1, jordanMul_diag_1,
        octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_snd, octAutoEquiv_snd,
        octAutoEquiv_snd, octAutoEquiv_snd, α.map_dot, α.map_dot]
    · rw [octAutoEquiv_fst, jordanMul_diag_2, jordanMul_diag_2,
        octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_snd, octAutoEquiv_snd,
        octAutoEquiv_snd, octAutoEquiv_snd, α.map_dot, α.map_dot]
    · rw [octAutoEquiv_snd, jordanMul_off_0, jordanMul_off_0,
        octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_fst,
        octAutoEquiv_snd, octAutoEquiv_snd, octAutoEquiv_snd, octAutoEquiv_snd,
        octAutoEquiv_snd, octAutoEquiv_snd]
      simp only [map_smul, map_add, α.map_mul, α.map_conj]
    · rw [octAutoEquiv_snd, jordanMul_off_1, jordanMul_off_1,
        octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_fst,
        octAutoEquiv_snd, octAutoEquiv_snd, octAutoEquiv_snd, octAutoEquiv_snd,
        octAutoEquiv_snd, octAutoEquiv_snd]
      simp only [map_smul, map_add, α.map_mul]
    · rw [octAutoEquiv_snd, jordanMul_off_2, jordanMul_off_2,
        octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_fst, octAutoEquiv_fst,
        octAutoEquiv_snd, octAutoEquiv_snd, octAutoEquiv_snd, octAutoEquiv_snd,
        octAutoEquiv_snd, octAutoEquiv_snd]
      simp only [map_smul, map_add, α.map_mul, α.map_conj]
  preserves_unit := by
    apply albert_ext
    · exact octAutoEquiv_fst α albertUnit 0
    · exact octAutoEquiv_fst α albertUnit 1
    · exact octAutoEquiv_fst α albertUnit 2
    · rw [octAutoEquiv_snd, albertUnit_snd, map_zero]
    · rw [octAutoEquiv_snd, albertUnit_snd, map_zero]
    · rw [octAutoEquiv_snd, albertUnit_snd, map_zero]
  preserves_trace _ := rfl

@[simp] theorem octAutoToAlbertAuto_diagAtom (α : OctonionAutomorphism) (i : Fin 3) :
    (octAutoToAlbertAuto α).linearEquiv (diagAtom i) = diagAtom i := by
  dsimp only [octAutoToAlbertAuto]
  apply albert_ext <;> [exact octAutoEquiv_fst α _ 0; exact octAutoEquiv_fst α _ 1;
    exact octAutoEquiv_fst α _ 2; rw [octAutoEquiv_snd, diagAtom_snd, map_zero];
    rw [octAutoEquiv_snd, diagAtom_snd, map_zero]; rw [octAutoEquiv_snd, diagAtom_snd, map_zero]]

@[simp] theorem octAutoToAlbertAuto_slotElem01 (α : OctonionAutomorphism) (a : Octonion) :
    (octAutoToAlbertAuto α).linearEquiv (slotElem01 a) = slotElem01 (α.equiv a) := by
  dsimp only [octAutoToAlbertAuto]
  apply albert_ext
  · exact octAutoEquiv_fst α _ 0
  · exact octAutoEquiv_fst α _ 1
  · exact octAutoEquiv_fst α _ 2
  · exact octAutoEquiv_snd α _ 0
  · rw [octAutoEquiv_snd, slotElem01_snd_1, map_zero]; rfl
  · rw [octAutoEquiv_snd, slotElem01_snd_2, map_zero]; rfl

@[simp] theorem octAutoToAlbertAuto_slotElem02 (α : OctonionAutomorphism) (a : Octonion) :
    (octAutoToAlbertAuto α).linearEquiv (slotElem02 a) = slotElem02 (α.equiv a) := by
  dsimp only [octAutoToAlbertAuto]
  apply albert_ext
  · exact octAutoEquiv_fst α _ 0
  · exact octAutoEquiv_fst α _ 1
  · exact octAutoEquiv_fst α _ 2
  · rw [octAutoEquiv_snd, slotElem02_snd_0, map_zero]; rfl
  · exact octAutoEquiv_snd α _ 1
  · rw [octAutoEquiv_snd, slotElem02_snd_2, map_zero]; rfl

@[simp] theorem octAutoToAlbertAuto_slotElem12 (α : OctonionAutomorphism) (a : Octonion) :
    (octAutoToAlbertAuto α).linearEquiv (slotElem12 a) = slotElem12 (α.equiv a) := by
  dsimp only [octAutoToAlbertAuto]
  apply albert_ext
  · exact octAutoEquiv_fst α _ 0
  · exact octAutoEquiv_fst α _ 1
  · exact octAutoEquiv_fst α _ 2
  · rw [octAutoEquiv_snd, slotElem12_snd_0, map_zero]; rfl
  · rw [octAutoEquiv_snd, slotElem12_snd_1, map_zero]; rfl
  · exact octAutoEquiv_snd α _ 2

def complexTransposeAuto : NativeAlbertAutomorphism :=
  octAutoToAlbertAuto conjIAutomorphism

section OrthogonalMatrices

def realConjMatrix (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (M : Fin 3 → Fin 3 → Octonion) : Fin 3 → Fin 3 → Octonion :=
  fun i j => ∑ k : Fin 3, ∑ l : Fin 3, (Q i k * Q j l) • M k l

private theorem realConjMatrix_hermitian (Q : Matrix (Fin 3) (Fin 3) ℝ) (x : Albert)
    (i j : Fin 3) :
    octonionConj (realConjMatrix Q (albertMatrix x) i j) =
      realConjMatrix Q (albertMatrix x) j i := by
  simp only [realConjMatrix, NativeAnalysis.octonionConj_finsetSum, octonionConj_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [NativeAnalysis.albertMatrix_conjugate, mul_comm (Q i l) (Q j k)]

private theorem realConjMatrix_mul (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQtQ : Q.transpose * Q = 1) (M N : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul (realConjMatrix Q M) (realConjMatrix Q N) =
      realConjMatrix Q (octonionMatrixMul M N) := by
  funext i j
  unfold octonionMatrixMul realConjMatrix
  simp only [NativeAnalysis.octonionMul_finsetSum_left, NativeAnalysis.octonionMul_finsetSum_right,
    octonionMul_smul_left, octonionMul_smul_right, Finset.smul_sum, smul_smul]
  have hinner : ∀ k l k' l' : Fin 3,
      (∑ r : Fin 3, ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l')) =
      (if l = k' then (Q i k * Q j l') • octonionMul (M k l) (N k' l') else 0) := by
    intro k l k' l'
    have hs : ∀ r : Fin 3, ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l') =
        ((Q r l * Q r k') * (Q i k * Q j l')) • octonionMul (M k l) (N k' l') := fun r => by
      congr 1; ring
    simp_rw [hs, ← Finset.sum_smul, ← Finset.sum_mul]
    have hdot : ∑ r : Fin 3, Q r l * Q r k' = (Q.transpose * Q) l k' := by
      simp [Matrix.mul_apply]
    rw [hdot, hQtQ, Matrix.one_apply]
    split_ifs with h
    · simp
    · simp
  have hswap1 : ∀ r : Fin 3,
      (∑ k' : Fin 3, ∑ l' : Fin 3,
        (∑ k : Fin 3, ∑ l : Fin 3, ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l'))) =
      ∑ k : Fin 3, ∑ l : Fin 3, ∑ k' : Fin 3, ∑ l' : Fin 3,
        ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l') := fun r => by
    have hstep1 : ∀ k' : Fin 3,
        (∑ l' : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l')) =
        ∑ k : Fin 3, ∑ l' : Fin 3, ∑ l : Fin 3,
          ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l') := fun _ => Finset.sum_comm
    simp_rw [hstep1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hstep2 : ∀ k' : Fin 3,
        (∑ l' : Fin 3, ∑ l : Fin 3,
          ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l')) =
        ∑ l : Fin 3, ∑ l' : Fin 3,
          ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l') := fun _ => Finset.sum_comm
    simp_rw [hstep2]
    exact Finset.sum_comm
  calc
    ∑ r : Fin 3, ∑ k' : Fin 3, ∑ l' : Fin 3,
        ∑ k : Fin 3, ∑ l : Fin 3,
          ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l')
      = ∑ r : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ k' : Fin 3, ∑ l' : Fin 3,
          ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l') :=
        Finset.sum_congr rfl fun r _ => hswap1 r
    _ = ∑ k : Fin 3, ∑ l : Fin 3, ∑ k' : Fin 3, ∑ l' : Fin 3, ∑ r : Fin 3,
          ((Q r k' * Q j l') * (Q i k * Q r l)) • octonionMul (M k l) (N k' l') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k' _ => ?_
        exact Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ l : Fin 3, ∑ k' : Fin 3, ∑ l' : Fin 3,
          (if l = k' then (Q i k * Q j l') • octonionMul (M k l) (N k' l') else 0) := by
        simp_rw [hinner]
    _ = ∑ k : Fin 3, ∑ l' : Fin 3, ∑ l : Fin 3,
          (Q i k * Q j l') • octonionMul (M k l) (N l l') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hdrop : ∀ l : Fin 3,
            (∑ k' : Fin 3, ∑ l' : Fin 3,
              (if l = k' then (Q i k * Q j l') • octonionMul (M k l) (N k' l') else 0)) =
            ∑ l' : Fin 3, (Q i k * Q j l') • octonionMul (M k l) (N l l') := fun l => by
          have hite : ∀ k' : Fin 3,
              (∑ l' : Fin 3, if l = k' then (Q i k * Q j l') • octonionMul (M k l) (N k' l') else 0) =
              if k' = l then ∑ l' : Fin 3, (Q i k * Q j l') • octonionMul (M k l) (N l l') else 0 := fun k' => by
            by_cases h : k' = l
            · subst h; simp
            · simp [h, Ne.symm h]
          simp_rw [hite, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        simp_rw [hdrop]
        exact Finset.sum_comm

private theorem realConjMatrix_trace (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQtQ : Q.transpose * Q = 1) (M : Fin 3 → Fin 3 → Octonion) :
    NativeAnalysis.matrixRealTrace (realConjMatrix Q M) =
      NativeAnalysis.matrixRealTrace M := by
  unfold NativeAnalysis.matrixRealTrace realConjMatrix
  simp only [NativeAnalysis.octonionReal_finsetSum, octonionReal_smul]
  rw [Finset.sum_comm]
  calc
    ∑ k : Fin 3, ∑ i : Fin 3, ∑ l : Fin 3, Q i k * Q i l * octonionReal (M k l)
      = ∑ k : Fin 3, ∑ l : Fin 3, (∑ i : Fin 3, Q i k * Q i l) * octonionReal (M k l) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k : Fin 3, ∑ l : Fin 3, (Q.transpose * Q) k l * octonionReal (M k l) := by
        simp [Matrix.mul_apply]
    _ = ∑ k : Fin 3, octonionReal (M k k) := by
        simp [hQtQ, Matrix.one_apply]

private theorem realConjMatrix_one (M : Fin 3 → Fin 3 → Octonion) :
    realConjMatrix (1 : Matrix (Fin 3) (Fin 3) ℝ) M = M := by
  funext i j
  unfold realConjMatrix
  simp [Matrix.one_apply]

private theorem realConjMatrix_comp (Q P : Matrix (Fin 3) (Fin 3) ℝ)
    (M : Fin 3 → Fin 3 → Octonion) :
    realConjMatrix Q (realConjMatrix P M) = realConjMatrix (Q * P) M := by
  funext i j
  unfold realConjMatrix
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply]
  have hreorder : ∀ k l : Fin 3,
      (∑ a : Fin 3, ∑ b : Fin 3, (Q i k * Q j l * (P k a * P l b)) • M a b) =
      ∑ a : Fin 3, ∑ b : Fin 3, ((Q i k * P k a) * (Q j l * P l b)) • M a b := fun k l =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by congr 1; ring
  simp_rw [hreorder]
  have hswapl : ∀ k : Fin 3,
      (∑ l : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ((Q i k * P k a) * (Q j l * P l b)) • M a b) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3, ((Q i k * P k a) * (Q j l * P l b)) • M a b := fun k => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
  calc
    ∑ k : Fin 3, ∑ l : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        ((Q i k * P k a) * (Q j l * P l b)) • M a b
      = ∑ k : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
          ((Q i k * P k a) * (Q j l * P l b)) • M a b :=
        Finset.sum_congr rfl fun k _ => hswapl k
    _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ((Q i k * P k a) * (Q j l * P l b)) • M a b := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : Fin 3, ∑ b : Fin 3,
          ((∑ k : Fin 3, Q i k * P k a) * (∑ l : Fin 3, Q j l * P l b)) • M a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have hs : (∑ k : Fin 3, ∑ l : Fin 3, ((Q i k * P k a) * (Q j l * P l b)) • M a b) =
            (∑ k : Fin 3, ∑ l : Fin 3, (Q i k * P k a) * (Q j l * P l b)) • M a b := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_smul]
        rw [hs]
        congr 1
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

private theorem albertMatrix_inj {a b : Albert} (h : albertMatrix a = albertMatrix b) : a = b := by
  apply albert_ext
  · have h00 := congrArg (fun m => octonionReal (m 0 0)) h
    simpa [albertMatrix, octonionReal_scalar] using h00
  · have h11 := congrArg (fun m => octonionReal (m 1 1)) h
    simpa [albertMatrix, octonionReal_scalar] using h11
  · have h22 := congrArg (fun m => octonionReal (m 2 2)) h
    simpa [albertMatrix, octonionReal_scalar] using h22
  · exact congrArg (fun m => m 0 1) h
  · exact congrArg (fun m => m 0 2) h
  · exact congrArg (fun m => m 1 2) h

private theorem albertMatrix_add_apply (x y : Albert) (i j : Fin 3) :
    albertMatrix (x + y) i j = albertMatrix x i j + albertMatrix y i j := by
  fin_cases i <;> fin_cases j <;> simp [albertMatrix, albert_add_fst, albert_add_snd,
    octonionScalar_add, octonionConj_add]

private theorem albertMatrix_smul_apply (r : ℝ) (x : Albert) (i j : Fin 3) :
    albertMatrix (r • x) i j = r • albertMatrix x i j := by
  fin_cases i <;> fin_cases j <;> simp [albertMatrix, albert_smul_fst, albert_smul_snd,
    octonionScalar_smul, octonionConj_smul]

def realConjAlbert (Q : Matrix (Fin 3) (Fin 3) ℝ) (x : Albert) : Albert :=
  albertCoordinates (realConjMatrix Q (albertMatrix x))

private theorem albertMatrix_realConjAlbert (Q : Matrix (Fin 3) (Fin 3) ℝ) (x : Albert) :
    albertMatrix (realConjAlbert Q x) = realConjMatrix Q (albertMatrix x) :=
  NativeAnalysis.albertMatrix_reconstruct _ (realConjMatrix_hermitian Q x)

def realConjLinearEquiv (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) : Albert ≃ₗ[ℝ] Albert where
  toFun := realConjAlbert Q
  invFun := realConjAlbert Q.transpose
  left_inv := fun x => by
    apply albertMatrix_inj
    rw [albertMatrix_realConjAlbert, albertMatrix_realConjAlbert, realConjMatrix_comp,
      hQtQ, realConjMatrix_one]
  right_inv := fun x => by
    apply albertMatrix_inj
    rw [albertMatrix_realConjAlbert, albertMatrix_realConjAlbert, realConjMatrix_comp,
      hQQt, realConjMatrix_one]
  map_add' := fun x y => by
    apply albertMatrix_inj
    funext i j
    rw [albertMatrix_add_apply, albertMatrix_realConjAlbert, albertMatrix_realConjAlbert,
      albertMatrix_realConjAlbert]
    simp only [realConjMatrix, albertMatrix_add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' := fun r x => by
    apply albertMatrix_inj
    funext i j
    simp only [RingHom.id_apply]
    rw [albertMatrix_smul_apply, albertMatrix_realConjAlbert, albertMatrix_realConjAlbert]
    simp only [realConjMatrix, albertMatrix_smul_apply, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1; ring

private theorem realConjLinearEquiv_apply (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) (x : Albert) :
    realConjLinearEquiv Q hQtQ hQQt x = realConjAlbert Q x := rfl

def realOrthogonalAlbertAuto (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) :
    NativeAlbertAutomorphism where
  linearEquiv := realConjLinearEquiv Q hQtQ hQQt
  preserves_product x y := by
    apply albertMatrix_inj
    funext i j
    simp only [realConjLinearEquiv_apply, albertMatrix_realConjAlbert,
      NativeAnalysis.albertMatrix_jordanMul]
    simp only [Pi.smul_apply, Pi.add_apply, realConjMatrix_mul Q hQtQ]
    simp only [realConjMatrix, Pi.smul_apply, Pi.add_apply, smul_add, smul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      congr 1; ring
    · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      congr 1; ring
  preserves_unit := by
    apply albertMatrix_inj
    simp only [realConjLinearEquiv_apply, albertMatrix_realConjAlbert]
    funext i j
    have hunit : ∀ a b : Fin 3, albertMatrix albertUnit a b = if a = b then octOne else 0 := by
      intro a b
      fin_cases a <;> fin_cases b <;>
        simp [albertMatrix, albertUnit_fst, albertUnit_snd, octOne, octonionConj_zero]
    simp only [realConjMatrix, hunit]
    have hs : ∀ a : Fin 3,
        (∑ b : Fin 3, (Q i a * Q j b) • (if a = b then octOne else 0)) =
          (Q i a * Q j a) • octOne := fun a => by
      simp
    simp_rw [hs, ← Finset.sum_smul]
    have hdot : ∑ a : Fin 3, Q i a * Q j a = (Q * Q.transpose) i j := by
      simp [Matrix.mul_apply]
    rw [hdot, hQQt, Matrix.one_apply]
    split_ifs with hij
    · subst hij; simp
    · simp
  preserves_trace x := by
    simp only [realConjLinearEquiv_apply]
    rw [← NativeAnalysis.matrixRealTrace_albertMatrix, albertMatrix_realConjAlbert,
      realConjMatrix_trace Q hQtQ, NativeAnalysis.matrixRealTrace_albertMatrix]

def permMatrix (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if σ j = i then 1 else 0

theorem permMatrix_transpose_mul (σ : Equiv.Perm (Fin 3)) :
    (permMatrix σ).transpose * permMatrix σ = 1 := by
  funext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, permMatrix, Matrix.one_apply]
  have hterm : ∀ r : Fin 3, (if σ i = r then (1 : ℝ) else 0) * (if σ j = r then 1 else 0) =
      if r = σ i then (if i = j then 1 else 0) else 0 := fun r => by
    by_cases hij : i = j
    · subst hij
      by_cases hr : r = σ i <;> simp [hr, eq_comm]
    · have hsne : σ i ≠ σ j := fun h => hij (σ.injective h)
      by_cases hr : r = σ i
      · subst hr; simp [hij, hsne.symm]
      · simp [hr, Ne.symm hr]
  rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_ite_eq']
  simp

theorem permMatrix_mul_transpose (σ : Equiv.Perm (Fin 3)) :
    permMatrix σ * (permMatrix σ).transpose = 1 := by
  funext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, permMatrix, Matrix.one_apply]
  have hterm : ∀ r : Fin 3, (if σ r = i then (1 : ℝ) else 0) * (if σ r = j then 1 else 0) =
      if r = σ.symm i then (if i = j then 1 else 0) else 0 := fun r => by
    by_cases hr : σ r = i
    · have hrs : r = σ.symm i := by rw [← hr, Equiv.symm_apply_apply]
      subst hrs
      simp [hr]
    · have hrs : r ≠ σ.symm i := fun h => hr (by rw [h, Equiv.apply_symm_apply])
      simp [hr, hrs]
  simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

def permFrameAlbertAuto (σ : Equiv.Perm (Fin 3)) : NativeAlbertAutomorphism :=
  realOrthogonalAlbertAuto (permMatrix σ) (permMatrix_transpose_mul σ)
    (permMatrix_mul_transpose σ)

theorem permFrameAlbertAuto_diagAtom (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (permFrameAlbertAuto σ).linearEquiv (diagAtom k) = diagAtom (σ k) := by
  apply albertMatrix_inj
  change albertMatrix (realConjLinearEquiv (permMatrix σ) (permMatrix_transpose_mul σ)
    (permMatrix_mul_transpose σ) (diagAtom k)) = albertMatrix (diagAtom (σ k))
  rw [realConjLinearEquiv_apply, albertMatrix_realConjAlbert]
  funext i j
  have hda : ∀ m a b : Fin 3,
      albertMatrix (diagAtom m) a b = if a = m ∧ b = m then octOne else 0 := fun m a b => by
    fin_cases m <;> fin_cases a <;> fin_cases b <;>
      simp [albertMatrix, diagAtom_fst, diagAtom_snd, octOne, octonionScalar_zero, octonionConj_zero]
  simp only [realConjMatrix, permMatrix, hda]
  have hi : ∀ a : Fin 3, (∑ b : Fin 3, ((if σ a = i then (1 : ℝ) else 0) *
      (if σ b = j then 1 else 0)) • (if a = k ∧ b = k then octOne else 0)) =
      if a = k then (if σ k = i ∧ σ k = j then octOne else 0) else 0 := fun a => by
    by_cases hak : a = k
    · subst hak
      simp only [true_and]
      have hterm : ∀ b : Fin 3, ((if σ a = i then (1 : ℝ) else 0) * (if σ b = j then 1 else 0)) •
          (if b = a then octOne else 0) =
          if b = a then (if σ a = i ∧ σ a = j then octOne else 0) else 0 := fun b => by
        by_cases hba : b = a
        · subst hba
          by_cases hsi : σ b = i <;> by_cases hsj : σ b = j <;> simp [hsi, hsj]
        · simp [hba]
      simp_rw [hterm]; simp
    · simp [hak]
  simp_rw [hi]; simp [eq_comm (a := σ k)]

def swap01AlbertAuto : NativeAlbertAutomorphism :=
  permFrameAlbertAuto (Equiv.swap 0 1)

def swap02AlbertAuto : NativeAlbertAutomorphism :=
  permFrameAlbertAuto (Equiv.swap 0 2)

def swap12AlbertAuto : NativeAlbertAutomorphism :=
  permFrameAlbertAuto (Equiv.swap 1 2)

theorem swap01AlbertAuto_apply (x : Albert) :
    swap01AlbertAuto.linearEquiv x =
      ((![x.1 1, x.1 0, x.1 2], ![octonionConj (x.2 0), x.2 2, x.2 1]) : Albert) := by
  have hm : albertMatrix (swap01AlbertAuto.linearEquiv x) =
      realConjMatrix (permMatrix (Equiv.swap 0 1)) (albertMatrix x) := by
    unfold swap01AlbertAuto permFrameAlbertAuto realOrthogonalAlbertAuto
    rw [realConjLinearEquiv_apply, albertMatrix_realConjAlbert]
  apply albertMatrix_inj
  rw [hm]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realConjMatrix, permMatrix, Fin.sum_univ_three, albertMatrix,
      Equiv.swap_apply_def, octonionConj_conj]

theorem swap02AlbertAuto_apply (x : Albert) :
    swap02AlbertAuto.linearEquiv x =
      ((![x.1 2, x.1 1, x.1 0],
        ![octonionConj (x.2 2), octonionConj (x.2 1), octonionConj (x.2 0)]) : Albert) := by
  have hm : albertMatrix (swap02AlbertAuto.linearEquiv x) =
      realConjMatrix (permMatrix (Equiv.swap 0 2)) (albertMatrix x) := by
    unfold swap02AlbertAuto permFrameAlbertAuto realOrthogonalAlbertAuto
    rw [realConjLinearEquiv_apply, albertMatrix_realConjAlbert]
  apply albertMatrix_inj
  rw [hm]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realConjMatrix, permMatrix, Fin.sum_univ_three, albertMatrix,
      Equiv.swap_apply_def, octonionConj_conj]

theorem swap12AlbertAuto_apply (x : Albert) :
    swap12AlbertAuto.linearEquiv x =
      ((![x.1 0, x.1 2, x.1 1], ![x.2 1, x.2 0, octonionConj (x.2 2)]) : Albert) := by
  have hm : albertMatrix (swap12AlbertAuto.linearEquiv x) =
      realConjMatrix (permMatrix (Equiv.swap 1 2)) (albertMatrix x) := by
    unfold swap12AlbertAuto permFrameAlbertAuto realOrthogonalAlbertAuto
    rw [realConjLinearEquiv_apply, albertMatrix_realConjAlbert]
  apply albertMatrix_inj
  rw [hm]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [realConjMatrix, permMatrix, Fin.sum_univ_three, albertMatrix,
      Equiv.swap_apply_def, octonionConj_conj]

theorem swap01AlbertAuto_diagAtom (i : Fin 3) :
    swap01AlbertAuto.linearEquiv (diagAtom i) = diagAtom (Equiv.swap 0 1 i) :=
  permFrameAlbertAuto_diagAtom _ i

theorem swap02AlbertAuto_diagAtom (i : Fin 3) :
    swap02AlbertAuto.linearEquiv (diagAtom i) = diagAtom (Equiv.swap 0 2 i) :=
  permFrameAlbertAuto_diagAtom _ i

theorem swap12AlbertAuto_diagAtom (i : Fin 3) :
    swap12AlbertAuto.linearEquiv (diagAtom i) = diagAtom (Equiv.swap 1 2 i) :=
  permFrameAlbertAuto_diagAtom _ i

def realRotation12 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, 0, 0], ![0, c, s], ![0, -s, c]]

theorem realRotation12_transpose_mul (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (realRotation12 c s).transpose * realRotation12 c s = 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.mul_apply, Fin.sum_univ_three]; simp only [Matrix.transpose_apply];
      simp [realRotation12]; try nlinarith)

theorem realRotation12_mul_transpose (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    realRotation12 c s * (realRotation12 c s).transpose = 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.mul_apply, Fin.sum_univ_three]; simp only [Matrix.transpose_apply];
      simp [realRotation12]; try nlinarith)

def realRotation12AlbertAuto (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : NativeAlbertAutomorphism :=
  realOrthogonalAlbertAuto (realRotation12 c s)
    (realRotation12_transpose_mul c s h) (realRotation12_mul_transpose c s h)

end OrthogonalMatrices

section MoufangNormalizers

private theorem octDot_unit_mul_left (u a b : Octonion) (hu : octNormSq u = 1) :
    octDot (octonionMul u a) (octonionMul u b) = octDot a b := by
  rw [octDot_mul_left, octMul_conj_left_cancel, hu, one_smul]

private theorem octDot_unit_mul_right (u a b : Octonion) (hu : octNormSq u = 1) :
    octDot (octonionMul a u) (octonionMul b u) = octDot a b := by
  rw [octDot_mul_right, octMul_conj_right_cancel, hu, one_smul]

private theorem octMul_conj_middle_cancel (u b : Octonion) (hu : octNormSq u = 1) :
    octonionMul (octonionMul (octonionConj u) (octonionMul (octonionMul u b) u))
      (octonionConj u) = b := by
  obtain ⟨φ, hφ, ⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := exists_quatEmbedding_containing_pair u b
  have hcu : octonionConj u = φ (star q1) := by rw [← hq1, hφ.map_star]
  have hu1 : φ (star q1 * q1) = octOne := by
    rw [hφ.map_mul, ← hcu, hq1, octMul_conj_self, hu]
    rfl
  have hu2 : φ (q1 * star q1) = octOne := by
    rw [hφ.map_mul, hq1, ← hcu, octMul_self_conj, hu]
    rfl
  rw [hcu, ← hq1, ← hq2]
  simp only [← hφ.map_mul, mul_assoc]
  have hassoc : star q1 * (q1 * (q2 * (q1 * star q1))) = (star q1 * q1) * (q2 * (q1 * star q1)) := by
    simp only [mul_assoc]
  rw [hassoc, hφ.map_mul, hu1, hφ.map_mul, hu2, octonionMul_one_right, octonionMul_one_left]

private theorem middleMoufang_slot12 (u a01 a02 : Octonion) (hu : octNormSq u = 1) :
    octonionMul (octonionConj (octonionMul u a01)) (octonionMul (octonionMul u a02) u) =
      octonionMul (octonionMul (octonionConj a01) a02) u := by
  have h := octMul_moufang_unit_conj (octonionConj u) (octonionConj a02) a01
    (by simpa only [octNormSq_conj] using hu)
  have hconj := congrArg octonionConj h
  simp only [octonionConj_mul, octonionConj_conj] at hconj
  rw [← octMul_flexible u a02] at hconj
  simp only [octonionConj_mul]
  exact hconj

def middleMoufangEquiv (u : Octonion) (hu : octNormSq u = 1) : Albert ≃ₗ[ℝ] Albert where
  toFun x :=
    ((x.1, ![octonionMul u (x.2 0), octonionMul (octonionMul u (x.2 1)) u,
      octonionMul (x.2 2) u]) : Albert)
  invFun x :=
    ((x.1, ![octonionMul (octonionConj u) (x.2 0),
      octonionMul (octonionMul (octonionConj u) (x.2 1)) (octonionConj u),
      octonionMul (x.2 2) (octonionConj u)]) : Albert)
  left_inv x := by
    apply albert_ext
    · rfl
    · rfl
    · rfl
    · simp [octMul_conj_left_cancel, hu]
    · simp [octMul_conj_middle_cancel u (x.2 1) hu]
    · simp [octMul_conj_right_cancel, hu]
  right_inv x := by
    have hcu : octNormSq (octonionConj u) = 1 := by simpa only [octNormSq_conj] using hu
    apply albert_ext
    · rfl
    · rfl
    · rfl
    · simp [octMul_left_conj_cancel, hu]
    · have hres := octMul_conj_middle_cancel (octonionConj u) (x.2 1) hcu
      rw [octonionConj_conj] at hres
      exact hres
    · simp [octMul_right_conj_cancel, hu]
  map_add' x y := by
    apply albert_ext
    · rw [albert_add_fst]; rfl
    · rw [albert_add_fst]; rfl
    · rw [albert_add_fst]; rfl
    · dsimp; rw [albert_add_snd, octonionMul_add_right]; rfl
    · dsimp; rw [albert_add_snd, octonionMul_add_right, octonionMul_add_left]; rfl
    · dsimp; rw [albert_add_snd, octonionMul_add_left]; rfl
  map_smul' r x := by
    apply albert_ext
    · rw [albert_smul_fst]; rfl
    · rw [albert_smul_fst]; rfl
    · rw [albert_smul_fst]; rfl
    · dsimp; rw [albert_smul_snd, octonionMul_smul_right]; rfl
    · dsimp; rw [albert_smul_snd, octonionMul_smul_right, octonionMul_smul_left]; rfl
    · dsimp; rw [albert_smul_snd, octonionMul_smul_left]; rfl

@[simp] private theorem middleMoufangEquiv_fst (u : Octonion) (hu : octNormSq u = 1) (x : Albert)
    (j : Fin 3) : (middleMoufangEquiv u hu x).1 j = x.1 j := rfl
@[simp] private theorem middleMoufangEquiv_snd_0 (u : Octonion) (hu : octNormSq u = 1) (x : Albert) :
    (middleMoufangEquiv u hu x).2 0 = octonionMul u (x.2 0) := rfl
@[simp] private theorem middleMoufangEquiv_snd_1 (u : Octonion) (hu : octNormSq u = 1) (x : Albert) :
    (middleMoufangEquiv u hu x).2 1 = octonionMul (octonionMul u (x.2 1)) u := rfl
@[simp] private theorem middleMoufangEquiv_snd_2 (u : Octonion) (hu : octNormSq u = 1) (x : Albert) :
    (middleMoufangEquiv u hu x).2 2 = octonionMul (x.2 2) u := rfl

def middleMoufangAlbertAuto (u : Octonion) (hu : octNormSq u = 1) : NativeAlbertAutomorphism where
  linearEquiv := middleMoufangEquiv u hu
  preserves_product x y := by
    apply albert_ext
    · simp [jordanMul_diag_0, octDot_unit_mul_left u _ _ hu, octDot_unit_mul_right u _ _ hu]
    · simp [jordanMul_diag_1, octDot_unit_mul_left u _ _ hu, octDot_unit_mul_right u _ _ hu]
    · simp [jordanMul_diag_2, octDot_unit_mul_left u _ _ hu, octDot_unit_mul_right u _ _ hu]
    · simp only [middleMoufangEquiv_snd_0, middleMoufangEquiv_snd_1, middleMoufangEquiv_snd_2,
        middleMoufangEquiv_fst, jordanMul_off_0, octonionMul_smul_right, octonionMul_add_right,
        octonionConj_mul, octMul_moufang_unit_conj u _ _ hu]
    · simp only [middleMoufangEquiv_snd_0, middleMoufangEquiv_snd_1, middleMoufangEquiv_snd_2,
        middleMoufangEquiv_fst, jordanMul_off_1, octonionMul_smul_left, octonionMul_smul_right,
        octonionMul_add_left, octonionMul_add_right, ← octMul_moufang_middle u]
    · simp only [middleMoufangEquiv_snd_0, middleMoufangEquiv_snd_1, middleMoufangEquiv_snd_2,
        middleMoufangEquiv_fst, jordanMul_off_2, octonionMul_smul_left, octonionMul_add_left,
        middleMoufang_slot12 u _ _ hu]
  preserves_unit := by
    apply albert_ext
    · rfl
    · rfl
    · rfl
    · simp [albertUnit_snd, octonionMul_zero_right]
    · simp [albertUnit_snd, octonionMul_zero_right, octonionMul_zero_left]
    · simp [albertUnit_snd, octonionMul_zero_left]
  preserves_trace _ := rfl

theorem middleMoufangAlbertAuto_apply (u : Octonion) (hu : octNormSq u = 1) (x : Albert) :
    (middleMoufangAlbertAuto u hu).linearEquiv x =
      (x.1, ![octonionMul u (x.2 0), octonionMul (octonionMul u (x.2 1)) u, octonionMul (x.2 2) u]) :=
  rfl

@[simp] theorem middleMoufangAlbertAuto_diagAtom (u : Octonion) (hu : octNormSq u = 1) (i : Fin 3) :
    (middleMoufangAlbertAuto u hu).linearEquiv (diagAtom i) = diagAtom i := by
  rw [middleMoufangAlbertAuto_apply]
  apply albert_ext
  · rfl
  · rfl
  · rfl
  · simp [diagAtom_snd, octonionMul_zero_right]
  · simp [diagAtom_snd, octonionMul_zero_left, octonionMul_zero_right]
  · simp [diagAtom_snd, octonionMul_zero_left]

def familyCMoufangAlbertAuto (u : Octonion) (hu : octNormSq u = 1) : NativeAlbertAutomorphism :=
  (swap12AlbertAuto.comp (middleMoufangAlbertAuto u hu)).comp swap12AlbertAuto

theorem familyCMoufangAlbertAuto_apply (u : Octonion) (hu : octNormSq u = 1) (x : Albert) :
    (familyCMoufangAlbertAuto u hu).linearEquiv x =
      (x.1, ![octonionMul (octonionMul u (x.2 0)) u, octonionMul u (x.2 1),
        octonionMul (octonionConj u) (x.2 2)]) := by
  change swap12AlbertAuto.linearEquiv ((middleMoufangAlbertAuto u hu).linearEquiv
    (swap12AlbertAuto.linearEquiv x)) = _
  rw [swap12AlbertAuto_apply, middleMoufangAlbertAuto_apply, swap12AlbertAuto_apply]
  apply albert_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [octonionConj_mul, octonionConj_conj]

@[simp] theorem familyCMoufangAlbertAuto_diagAtom (u : Octonion) (hu : octNormSq u = 1) (i : Fin 3) :
    (familyCMoufangAlbertAuto u hu).linearEquiv (diagAtom i) = diagAtom i := by
  rw [familyCMoufangAlbertAuto_apply]
  apply albert_ext
  · rfl
  · rfl
  · rfl
  · simp [diagAtom_snd, octonionMul_zero_left, octonionMul_zero_right]
  · simp [diagAtom_snd, octonionMul_zero_right]
  · simp [diagAtom_snd, octonionMul_zero_right]

private theorem exists_unit_mul_scalar (w : Octonion) :
    ∃ (u : Octonion) (_hu : octNormSq u = 1) (r : ℝ),
      0 ≤ r ∧ octonionMul u w = octonionScalar r ∧ octonionMul w u = octonionScalar r := by
  by_cases hw : w = 0
  · refine ⟨octOne, octNormSq_one, 0, le_rfl, ?_, ?_⟩
    · simp [hw, octonionMul_zero_right, octonionScalar_zero]
    · simp [hw, octonionMul_zero_left, octonionScalar_zero]
  · have hpos : 0 < octNormSq w :=
      lt_of_le_of_ne (octNormSq_nonneg w) (Ne.symm fun h => hw ((octNormSq_eq_zero w).mp h))
    let r : ℝ := Real.sqrt (octNormSq w)
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hrne : r ≠ 0 := hrpos.ne'
    have hr2 : r ^ 2 = octNormSq w := Real.sq_sqrt hpos.le
    let u : Octonion := (1 / r) • octonionConj w
    have hu : octNormSq u = 1 := by
      simp only [u, octNormSq_smul, octNormSq_conj, one_div, inv_pow, hr2]
      field_simp [hrne]
    refine ⟨u, hu, r, hrpos.le, ?_, ?_⟩
    · dsimp only [u]
      rw [octonionMul_smul_left, octMul_conj_self, ← hr2, ← octonionScalar_smul]
      congr 1; field_simp [hrne]
    · dsimp only [u]
      rw [octonionMul_smul_right, octMul_self_conj, ← hr2, ← octonionScalar_smul]
      congr 1; field_simp [hrne]

theorem exists_frameStab_slot01_real (x : Albert) :
    ∃ g : NativeAlbertAutomorphism, (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 0 = octonionScalar r := by
  obtain ⟨u, hu, r, hr, hmul, _⟩ := exists_unit_mul_scalar (x.2 0)
  exact ⟨middleMoufangAlbertAuto u hu, middleMoufangAlbertAuto_diagAtom u hu, r, hr,
    by simpa [middleMoufangAlbertAuto_apply] using hmul⟩

theorem exists_frameStab_slot02_real (x : Albert) :
    ∃ g : NativeAlbertAutomorphism, (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 1 = octonionScalar r := by
  obtain ⟨u, hu, r, hr, hmul, _⟩ := exists_unit_mul_scalar (x.2 1)
  exact ⟨familyCMoufangAlbertAuto u hu, familyCMoufangAlbertAuto_diagAtom u hu, r, hr,
    by simpa [familyCMoufangAlbertAuto_apply] using hmul⟩

theorem exists_frameStab_slot12_real (x : Albert) :
    ∃ g : NativeAlbertAutomorphism, (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 2 = octonionScalar r := by
  obtain ⟨u, hu, r, hr, _, hmul⟩ := exists_unit_mul_scalar (x.2 2)
  exact ⟨middleMoufangAlbertAuto u hu, middleMoufangAlbertAuto_diagAtom u hu, r, hr,
    by simpa [middleMoufangAlbertAuto_apply] using hmul⟩

private theorem exists_unit_imag_ortho (a : Octonion) :
    ∃ u : Octonion, octonionReal u = 0 ∧ octNormSq u = 1 ∧ octDot u (octIm a) = 0 := by
  let p1 : ℝ := octDot octI (octIm a)
  let p2 : ℝ := octDot octJ (octIm a)
  by_cases h1 : p1 = 0
  · exact ⟨octI, by simp [octI, octonionReal], by rw [octNormSq_eq_coords]; simp [octI], h1⟩
  · by_cases h2 : p2 = 0
    · exact ⟨octJ, by simp [octJ, octonionReal], by rw [octNormSq_eq_coords]; simp [octJ], h2⟩
    · let v : Octonion := p2 • octI - p1 • octJ
      have hv_re : octonionReal v = 0 := by
        dsimp [v]
        rw [sub_eq_add_neg, octonionReal_add, octonionReal_neg, octonionReal_smul,
          octonionReal_smul]
        simp [octonionReal, octI, octJ]
      have hv_ns : octNormSq v = p2 ^ 2 + p1 ^ 2 := by
        rw [octNormSq_sub, octNormSq_smul, octNormSq_smul]
        have hi : octNormSq octI = 1 := by rw [octNormSq_eq_coords]; simp [octI]
        have hj : octNormSq octJ = 1 := by rw [octNormSq_eq_coords]; simp [octJ]
        have hij : octDot octI octJ = 0 := by rw [octDot_eq_coords]; simp [octI, octJ]
        rw [hi, hj, octDot_smul_left, octDot_smul_right, hij]
        ring
      have hv_pos : 0 < octNormSq v := by
        rw [hv_ns]
        nlinarith [sq_pos_iff.mpr h1, sq_pos_iff.mpr h2]
      let n : ℝ := Real.sqrt (octNormSq v)
      have hn : 0 < n := Real.sqrt_pos.mpr hv_pos
      have hn2 : n ^ 2 = octNormSq v := Real.sq_sqrt hv_pos.le
      refine ⟨(1 / n) • v, by simp [octonionReal_smul, hv_re], ?_, ?_⟩
      · rw [octNormSq_smul, one_div, inv_pow, hn2]; field_simp [hn.ne']
      · rw [octDot_smul_left, octDot_sub_left, octDot_smul_left, octDot_smul_left]
        change (1 / n) * (p2 * p1 - p1 * p2) = 0
        ring

private theorem familyCMoufang_imag_slot01_one {u : Octonion}
    (hre : octonionReal u = 0) (hu : octNormSq u = 1) :
    (familyCMoufangAlbertAuto u hu).linearEquiv (slotElem01 octOne) = -slotElem01 octOne := by
  have hsq : octonionMul (octonionMul u octOne) u = -octOne := by
    rw [octonionMul_one_right, octonionMul_imag_sq hre, hu, neg_smul, one_smul]
  rw [familyCMoufangAlbertAuto_apply]
  apply albert_ext
  · exact neg_zero.symm
  · exact neg_zero.symm
  · exact neg_zero.symm
  · simp only [Matrix.cons_val_zero, albert_neg_snd, slotElem01_snd_0]; exact hsq
  · simp [albert_neg_snd, octonionMul_zero_right]
  · simp [albert_neg_snd, octonionMul_zero_right]

theorem exists_frameAnd01OneStab_slot02_real (x : Albert) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      g.linearEquiv (slotElem01 octOne) = slotElem01 octOne ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 1 = octonionScalar r := by
  by_cases hx : x.2 1 = 0
  · exact ⟨NativeAlbertAutomorphism.refl, fun _ => rfl, rfl, 0, le_rfl,
      by simp [NativeAlbertAutomorphism.refl, hx, octonionScalar_zero]⟩
  · have hpos : 0 < octNormSq (x.2 1) :=
      lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => hx ((octNormSq_eq_zero _).mp h))
    let r : ℝ := Real.sqrt (octNormSq (x.2 1))
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = octNormSq (x.2 1) := Real.sq_sqrt hpos.le
    let a : Octonion := (1 / r) • x.2 1
    have ha : octNormSq a = 1 := by
      simp only [a, octNormSq_smul, one_div, inv_pow, hr2]
      field_simp [hrpos.ne']
    obtain ⟨u1, hu1_re, hu1_ns, hu1_ortho⟩ := exists_unit_imag_ortho a
    let u2 : Octonion := -octonionMul u1 a
    have hu2_re : octonionReal u2 = 0 := by
      simp only [u2, octonionReal_neg]
      have hre : octonionReal (octonionMul u1 a) = octDot u1 (octonionConj a) := by
        rw [octDot, octonionConj_conj]
      rw [hre, octConj_eq_two_real_sub a]
      have hsc : octDot u1 ((2 * octonionReal a) • octOne) = 0 := by
        rw [octDot_smul_right, octDot_comm, show octOne = octonionScalar 1 from rfl,
          octDot_scalar_left, hu1_re, mul_zero, mul_zero]
      rw [octDot_sub_right, hsc, zero_sub]
      have him : octDot u1 a = octDot u1 (octIm a) := by
        conv_lhs => rw [oct_eq_scalar_add_octIm a, octDot_add_right, octDot_comm u1 (octonionScalar _),
          octDot_scalar_left, hu1_re, mul_zero, zero_add]
      linarith
    have hu2_ns : octNormSq u2 = 1 := by
      simp [u2, octNormSq_neg, octNormSq_mul, hu1_ns, ha]
    let g1 := familyCMoufangAlbertAuto u1 hu1_ns
    let g2 := familyCMoufangAlbertAuto u2 hu2_ns
    let g := g2.comp g1
    refine ⟨g, ?_, ?_, r, hrpos.le, ?_⟩
    · intro i
      simp [g, NativeAlbertAutomorphism.comp, g1, g2]
    · simp only [g, NativeAlbertAutomorphism.comp, LinearEquiv.trans_apply, g1, g2]
      rw [familyCMoufang_imag_slot01_one hu1_re hu1_ns, map_neg,
        familyCMoufang_imag_slot01_one hu2_re hu2_ns, neg_neg]
    · change (g2.linearEquiv (g1.linearEquiv x)).2 1 = octonionScalar r
      dsimp only [g1, g2]
      have hs1 : ∀ (v : Octonion) (hv : octNormSq v = 1) (y : Albert),
          ((familyCMoufangAlbertAuto v hv).linearEquiv y).2 1 = octonionMul v (y.2 1) :=
        fun v hv y => by rw [familyCMoufangAlbertAuto_apply]; rfl
      rw [hs1, hs1]
      have hxa : x.2 1 = r • a := by
        dsimp only [a]
        rw [smul_smul, show r * (1 / r) = 1 from by field_simp [hrpos.ne'], one_smul]
      rw [hxa, octonionMul_smul_right, octonionMul_smul_right]
      have hprod : octonionMul u2 (octonionMul u1 a) = octOne := by
        have hconj : u2 = octonionConj (octonionMul u1 a) := by
          rw [octonionConj_eq_neg_of_real_zero (by simpa [u2, octonionReal_neg] using hu2_re)]
        rw [hconj, octMul_conj_self, octNormSq_mul, hu1_ns, ha, mul_one]
        rfl
      rw [hprod, octonionScalar_eq_smul]; rfl

theorem exists_frameAnd01OneStab_slot12_real (x : Albert) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      g.linearEquiv (slotElem01 octOne) = slotElem01 octOne ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 2 = octonionScalar r := by
  obtain ⟨h, hdiag, h01, r, hr, hslot⟩ :=
    exists_frameAnd01OneStab_slot02_real (swap01AlbertAuto.linearEquiv x)
  let g := (swap01AlbertAuto.comp h).comp swap01AlbertAuto
  refine ⟨g, ?_, ?_, r, hr, ?_⟩
  · intro i
    change swap01AlbertAuto.linearEquiv (h.linearEquiv (swap01AlbertAuto.linearEquiv (diagAtom i))) =
      diagAtom i
    rw [swap01AlbertAuto_diagAtom, hdiag, swap01AlbertAuto_diagAtom]
    simp
  · have hswap01_one : swap01AlbertAuto.linearEquiv (slotElem01 octOne) = slotElem01 octOne := by
      apply albert_ext <;> simp [swap01AlbertAuto_apply, octOne, octonionConj_scalar]
    change swap01AlbertAuto.linearEquiv (h.linearEquiv (swap01AlbertAuto.linearEquiv (slotElem01 octOne))) =
      slotElem01 octOne
    rw [hswap01_one, h01, hswap01_one]
  · change (swap01AlbertAuto.linearEquiv (h.linearEquiv (swap01AlbertAuto.linearEquiv x))).2 2 =
      octonionScalar r
    conv_lhs => rw [swap01AlbertAuto_apply]
    exact hslot

end MoufangNormalizers

/-! ## Section 5: Complex and Quaternionic Windows -/

def complexToOctonion : ℂ →ₗ[ℝ] Octonion where
  toFun z := (⟨z.re, z.im, 0, 0⟩, 0)
  map_add' z w := by
    apply Prod.ext <;> apply Quaternion.ext
    · exact Complex.add_re z w
    · exact Complex.add_im z w
    all_goals exact (add_zero (0 : ℝ)).symm
  map_smul' r z := by
    have hsm : (r • z).re = r * z.re ∧ (r • z).im = r * z.im := by
      simp [Complex.real_smul]
    apply Prod.ext <;> apply Quaternion.ext
    · exact hsm.1
    · exact hsm.2
    all_goals exact (mul_zero r).symm

@[simp] theorem complexToOctonion_apply (z : ℂ) :
    complexToOctonion z = (⟨z.re, z.im, 0, 0⟩, 0) :=
  rfl

@[simp] theorem complexToOctonion_one : complexToOctonion 1 = octOne := rfl

private def complexToQuat : ℂ →ₗ[ℝ] Quaternion ℝ where
  toFun z := ⟨z.re, z.im, 0, 0⟩
  map_add' _ _ := by apply Quaternion.ext <;> simp
  map_smul' _ _ := by apply Quaternion.ext <;> simp

private theorem complexToOctonion_eq_quatEmbed1 (z : ℂ) :
    complexToOctonion z = quatEmbed1 (complexToQuat z) := rfl

private theorem complexToQuat_one : complexToQuat 1 = 1 := by apply Quaternion.ext <;> simp [complexToQuat]
private theorem complexToQuat_mul (z w : ℂ) : complexToQuat (z * w) = complexToQuat z * complexToQuat w := by
  (apply Quaternion.ext <;> simp [complexToQuat]); all_goals ring
private theorem complexToQuat_star (z : ℂ) : complexToQuat (star z) = star (complexToQuat z) := by
  apply Quaternion.ext <;> simp [complexToQuat]

private def complexHermitianToQuatMatrix (M : Hermitian3) : Matrix (Fin 3) (Fin 3) (Quaternion ℝ) :=
  fun i j => complexToQuat ((M : ComplexMatrix3) i j)

private theorem complexHermitianToQuatMatrix_herm (M : Hermitian3) (i j : Fin 3) :
    star (complexHermitianToQuatMatrix M j i) = complexHermitianToQuatMatrix M i j := by
  change star (complexToQuat ((M : ComplexMatrix3) j i)) = complexToQuat ((M : ComplexMatrix3) i j)
  rw [← complexToQuat_star]
  have hM : star (M : ComplexMatrix3) = M := M.prop
  have hij := congrArg (fun N : ComplexMatrix3 => N i j) hM
  change star ((M : ComplexMatrix3) j i) = (M : ComplexMatrix3) i j at hij
  rw [hij]

def quatMatrixToAlbert (φ : Quaternion ℝ →ₗ[ℝ] Octonion)
    (M : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) : Albert :=
  (fun i => (M i i).re, ![φ (M 0 1), φ (M 0 2), φ (M 1 2)])

theorem quat_eq_re_smul_one {q : Quaternion ℝ} (hq : star q = q) :
    q = q.re • (1 : Quaternion ℝ) := by
  have hi : -q.imI = q.imI := congrArg (fun x : Quaternion ℝ => x.imI) hq
  have hj : -q.imJ = q.imJ := congrArg (fun x : Quaternion ℝ => x.imJ) hq
  have hk : -q.imK = q.imK := congrArg (fun x : Quaternion ℝ => x.imK) hq
  apply Quaternion.ext <;> simp <;> linarith

private theorem albertMatrix_quatMatrixToAlbert (φ : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hφ : IsQuatEmbedding φ) {M : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)}
    (hM : ∀ i j, star (M j i) = M i j) (i j : Fin 3) :
    albertMatrix (quatMatrixToAlbert φ M) i j = φ (M i j) := by
  have hdiag : ∀ k : Fin 3, octonionScalar (M k k).re = φ (M k k) := fun k => by
    have hk := quat_eq_re_smul_one (hM k k)
    rw [octonionScalar_eq_smul, ← hφ.map_one, ← φ.map_smul, ← hk]
  fin_cases i <;> fin_cases j
  · exact hdiag 0
  · rfl
  · rfl
  · change octonionConj (φ (M 0 1)) = φ (M 1 0)
    rw [← hφ.map_star, hM]
  · exact hdiag 1
  · rfl
  · change octonionConj (φ (M 0 2)) = φ (M 2 0)
    rw [← hφ.map_star, hM]
  · change octonionConj (φ (M 1 2)) = φ (M 2 1)
    rw [← hφ.map_star, hM]
  · exact hdiag 2

theorem jordanMul_quatMatrixToAlbert (φ : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hφ : IsQuatEmbedding φ) {M N P : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)}
    (hM : ∀ i j, star (M j i) = M i j) (hN : ∀ i j, star (N j i) = N i j)
    (hP : P = (1 / 2 : ℝ) • (M * N + N * M)) :
    quatMatrixToAlbert φ P = jordanMul (quatMatrixToAlbert φ M) (quatMatrixToAlbert φ N) := by
  have hmul : ∀ A B : Matrix (Fin 3) (Fin 3) (Quaternion ℝ),
      (∀ i j, star (A j i) = A i j) → (∀ i j, star (B j i) = B i j) → ∀ i j : Fin 3,
      octonionMatrixMul (albertMatrix (quatMatrixToAlbert φ A))
        (albertMatrix (quatMatrixToAlbert φ B)) i j = φ ((A * B) i j) := fun A B hA hB i j => by
    unfold octonionMatrixMul
    simp only [albertMatrix_quatMatrixToAlbert φ hφ hA, albertMatrix_quatMatrixToAlbert φ hφ hB,
      ← hφ.map_mul, ← map_sum, Matrix.mul_apply]
  unfold jordanMul albertCoordinates
  apply albert_ext
  · change (P 0 0).re = (1 / 2 : ℝ) * octonionReal _
    simp only [Pi.add_apply]
    rw [hmul M N hM hN 0 0, hmul N M hN hM 0 0, ← map_add, hφ.map_re, hP, Matrix.smul_apply]
    rfl
  · change (P 1 1).re = (1 / 2 : ℝ) * octonionReal _
    simp only [Pi.add_apply]
    rw [hmul M N hM hN 1 1, hmul N M hN hM 1 1, ← map_add, hφ.map_re, hP, Matrix.smul_apply]
    rfl
  · change (P 2 2).re = (1 / 2 : ℝ) * octonionReal _
    simp only [Pi.add_apply]
    rw [hmul M N hM hN 2 2, hmul N M hN hM 2 2, ← map_add, hφ.map_re, hP, Matrix.smul_apply]
    rfl
  · change φ (P 0 1) = (1 / 2 : ℝ) • (_ + _)
    rw [hmul M N hM hN 0 1, hmul N M hN hM 0 1, ← map_add, ← φ.map_smul, hP]
    rfl
  · change φ (P 0 2) = (1 / 2 : ℝ) • (_ + _)
    rw [hmul M N hM hN 0 2, hmul N M hN hM 0 2, ← map_add, ← φ.map_smul, hP]
    rfl
  · change φ (P 1 2) = (1 / 2 : ℝ) • (_ + _)
    rw [hmul M N hM hN 1 2, hmul N M hN hM 1 2, ← map_add, ← φ.map_smul, hP]
    rfl

def complexHermToAlbert (M : Hermitian3) : Albert :=
  (fun i => ((M : ComplexMatrix3) i i).re,
    ![complexToOctonion ((M : ComplexMatrix3) 0 1),
      complexToOctonion ((M : ComplexMatrix3) 0 2),
      complexToOctonion ((M : ComplexMatrix3) 1 2)])

def standardComplexWindow : ComplexWindow where
  embedding :=
    { toFun := complexHermToAlbert
      map_add' := fun M N => by
        let xM := complexHermToAlbert M
        let xN := complexHermToAlbert N
        change complexHermToAlbert (M + N) = xM + xN
        apply albert_ext
        · rw [albert_add_fst]; rfl
        · rw [albert_add_fst]; rfl
        · rw [albert_add_fst]; rfl
        · rw [albert_add_snd]
          change complexToOctonion ((↑(M + N) : ComplexMatrix3) 0 1) =
            complexToOctonion ((M : ComplexMatrix3) 0 1) + complexToOctonion ((N : ComplexMatrix3) 0 1)
          exact map_add complexToOctonion ((M : ComplexMatrix3) 0 1) ((N : ComplexMatrix3) 0 1)
        · rw [albert_add_snd]
          change complexToOctonion ((↑(M + N) : ComplexMatrix3) 0 2) =
            complexToOctonion ((M : ComplexMatrix3) 0 2) + complexToOctonion ((N : ComplexMatrix3) 0 2)
          exact map_add complexToOctonion ((M : ComplexMatrix3) 0 2) ((N : ComplexMatrix3) 0 2)
        · rw [albert_add_snd]
          change complexToOctonion ((↑(M + N) : ComplexMatrix3) 1 2) =
            complexToOctonion ((M : ComplexMatrix3) 1 2) + complexToOctonion ((N : ComplexMatrix3) 1 2)
          exact map_add complexToOctonion ((M : ComplexMatrix3) 1 2) ((N : ComplexMatrix3) 1 2)
      map_smul' := fun r M => by
        let xM := complexHermToAlbert M
        change complexHermToAlbert (r • M) = r • xM
        apply albert_ext
        · rw [albert_smul_fst]; dsimp [xM, complexHermToAlbert]; simp
        · rw [albert_smul_fst]; dsimp [xM, complexHermToAlbert]; simp
        · rw [albert_smul_fst]; dsimp [xM, complexHermToAlbert]; simp
        · rw [albert_smul_snd]
          change complexToOctonion ((↑(r • M) : ComplexMatrix3) 0 1) =
            r • complexToOctonion ((M : ComplexMatrix3) 0 1)
          rw [selfAdjoint.val_smul, Matrix.smul_apply, map_smul]
        · rw [albert_smul_snd]
          change complexToOctonion ((↑(r • M) : ComplexMatrix3) 0 2) =
            r • complexToOctonion ((M : ComplexMatrix3) 0 2)
          rw [selfAdjoint.val_smul, Matrix.smul_apply, map_smul]
        · rw [albert_smul_snd]
          change complexToOctonion ((↑(r • M) : ComplexMatrix3) 1 2) =
            r • complexToOctonion ((M : ComplexMatrix3) 1 2)
          rw [selfAdjoint.val_smul, Matrix.smul_apply, map_smul] }
  injective := fun M N h => by
    apply Subtype.ext
    funext i j
    have hdiag : ∀ k : Fin 3, ((M : ComplexMatrix3) k k).re = ((N : ComplexMatrix3) k k).re := fun k =>
      congrArg (fun a : Albert => a.1 k) h
    have hM := M.prop
    have hN := N.prop
    have h01 : complexToOctonion ((M : ComplexMatrix3) 0 1) = complexToOctonion ((N : ComplexMatrix3) 0 1) :=
      congrArg (fun a : Albert => a.2 0) h
    have h02 : complexToOctonion ((M : ComplexMatrix3) 0 2) = complexToOctonion ((N : ComplexMatrix3) 0 2) :=
      congrArg (fun a : Albert => a.2 1) h
    have h12 : complexToOctonion ((M : ComplexMatrix3) 1 2) = complexToOctonion ((N : ComplexMatrix3) 1 2) :=
      congrArg (fun a : Albert => a.2 2) h
    have hinj : ∀ z w : ℂ, complexToOctonion z = complexToOctonion w → z = w := fun z w hzw => by
      apply Complex.ext
      · exact congrArg (fun o : Octonion => o.1.re) hzw
      · exact congrArg (fun o : Octonion => o.1.imI) hzw
    have hcd : ∀ k : Fin 3, ((M : ComplexMatrix3) k k).im = 0 ∧ ((N : ComplexMatrix3) k k).im = 0 := fun k => by
      have hm := congrArg (fun A : ComplexMatrix3 => (A k k).im) hM
      have hn := congrArg (fun A : ComplexMatrix3 => (A k k).im) hN
      simp only [Matrix.star_apply, Complex.star_def, Complex.conj_im] at hm hn
      constructor <;> linarith
    fin_cases i <;> fin_cases j <;> dsimp
    · exact Complex.ext (hdiag 0) (by rw [(hcd 0).1, (hcd 0).2])
    · exact hinj _ _ h01
    · exact hinj _ _ h02
    · have hm := congrArg (fun A : ComplexMatrix3 => A 1 0) hM
      have hn := congrArg (fun A : ComplexMatrix3 => A 1 0) hN
      simp only [Matrix.star_apply] at hm hn
      rw [← hm, ← hn, hinj _ _ h01]
    · exact Complex.ext (hdiag 1) (by rw [(hcd 1).1, (hcd 1).2])
    · exact hinj _ _ h12
    · have hm := congrArg (fun A : ComplexMatrix3 => A 2 0) hM
      have hn := congrArg (fun A : ComplexMatrix3 => A 2 0) hN
      simp only [Matrix.star_apply] at hm hn
      rw [← hm, ← hn, hinj _ _ h02]
    · have hm := congrArg (fun A : ComplexMatrix3 => A 2 1) hM
      have hn := congrArg (fun A : ComplexMatrix3 => A 2 1) hN
      simp only [Matrix.star_apply] at hm hn
      rw [← hm, ← hn, hinj _ _ h12]
    · exact Complex.ext (hdiag 2) (by rw [(hcd 2).1, (hcd 2).2])
  unit := by
    apply albert_ext <;> simp [albertUnit] <;> rfl
  product_closed M N := by
    refine ⟨⟨(1 / 2 : ℝ) • ((M : ComplexMatrix3) * (N : ComplexMatrix3) +
      (N : ComplexMatrix3) * (M : ComplexMatrix3)), ?_⟩, rfl⟩
    rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial]
    have hM : star (M : ComplexMatrix3) = M := M.prop
    have hN : star (N : ComplexMatrix3) = N := N.prop
    rw [hM, hN, add_comm]
  preserves_product M N P hP := by
    change quatMatrixToAlbert quatEmbed1 (complexHermitianToQuatMatrix P) =
      jordanMul (quatMatrixToAlbert quatEmbed1 (complexHermitianToQuatMatrix M))
        (quatMatrixToAlbert quatEmbed1 (complexHermitianToQuatMatrix N))
    refine jordanMul_quatMatrixToAlbert quatEmbed1 quatEmbed1_isQuatEmbedding
      (complexHermitianToQuatMatrix_herm M) (complexHermitianToQuatMatrix_herm N) ?_
    funext i j
    have hPc := congrArg (fun A : ComplexMatrix3 => A i j) hP
    simp only [complexHermitianToQuatMatrix, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
      hPc, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Fin.sum_univ_three]
    (apply Quaternion.ext <;> simp [complexToQuat]); all_goals ring
  preserves_trace M := by
    change albertTrace (complexHermToAlbert M) = (Matrix.trace (M : ComplexMatrix3)).re
    dsimp only [complexHermToAlbert, Matrix.trace, Matrix.diag]
    unfold albertTrace
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [Complex.add_re]

@[simp] theorem standardComplexWindow_apply (M : Hermitian3) :
    standardComplexWindow.embedding M = complexHermToAlbert M :=
  rfl

def ComplexWindow.transport (W : ComplexWindow) (g : NativeAlbertAutomorphism) : ComplexWindow where
  embedding := g.linearEquiv.toLinearMap.comp W.embedding
  injective := g.linearEquiv.injective.comp W.injective
  unit := by simp [W.unit, g.preserves_unit]
  product_closed := W.product_closed
  preserves_product x y z hz := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [W.preserves_product x y z hz, g.preserves_product]
  preserves_trace x := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, g.preserves_trace]
    exact W.preserves_trace x

theorem ComplexWindow.contains_transport_iff (W : ComplexWindow) (g : NativeAlbertAutomorphism)
    (p : Albert) :
    (W.transport g).Contains p ↔ W.Contains (g.linearEquiv.symm p) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by apply g.linearEquiv.injective; simpa [ComplexWindow.transport] using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simp [ComplexWindow.transport, hx]⟩

def ComplexWindow.toSubalgebra (W : ComplexWindow) : NativeJordanSubalgebra where
  carrier := LinearMap.range W.embedding
  unit_mem := ⟨1, W.unit⟩
  product_mem _ hx _ hy := by
    rcases hx with ⟨mx, rfl⟩
    rcases hy with ⟨my, rfl⟩
    obtain ⟨mz, hmz⟩ := W.product_closed mx my
    exact ⟨mz, W.preserves_product mx my mz hmz⟩

def mkHerm3Matrix (d : Fin 3 → ℝ) (v : Fin 3 → ℂ) : ComplexMatrix3 :=
  fun i j =>
    if i = 0 ∧ j = 0 then ⟨d 0, 0⟩
    else if i = 1 ∧ j = 1 then ⟨d 1, 0⟩
    else if i = 2 ∧ j = 2 then ⟨d 2, 0⟩
    else if i = 0 ∧ j = 1 then v 0
    else if i = 1 ∧ j = 0 then star (v 0)
    else if i = 0 ∧ j = 2 then v 1
    else if i = 2 ∧ j = 0 then star (v 1)
    else if i = 1 ∧ j = 2 then v 2
    else star (v 2)

def hermitian3Equiv : Hermitian3 ≃ₗ[ℝ] ((Fin 3 → ℝ) × (Fin 3 → ℂ)) where
  toFun M := (fun i => ((M : ComplexMatrix3) i i).re,
    ![(M : ComplexMatrix3) 0 1, (M : ComplexMatrix3) 0 2, (M : ComplexMatrix3) 1 2])
  invFun p :=
    ⟨mkHerm3Matrix p.1 p.2, by
      dsimp only [Hermitian3]
      rw [selfAdjoint.mem_iff]
      funext i j
      fin_cases i <;> fin_cases j <;> simp [mkHerm3Matrix, Matrix.star_apply] <;>
        apply Complex.ext <;> simp⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    have hM := M.prop
    have hdiag : ∀ k : Fin 3, ((M : ComplexMatrix3) k k).im = 0 := fun k => by
      have hm := congrArg (fun A : ComplexMatrix3 => (A k k).im) hM
      simp only [Matrix.star_apply, Complex.star_def, Complex.conj_im] at hm
      linarith
    fin_cases i <;> fin_cases j <;> simp [mkHerm3Matrix]
    · exact Complex.ext rfl (hdiag 0).symm
    · exact congrArg (fun A : ComplexMatrix3 => A 1 0) hM
    · exact Complex.ext rfl (hdiag 1).symm
    · exact congrArg (fun A : ComplexMatrix3 => A 2 0) hM
    · exact congrArg (fun A : ComplexMatrix3 => A 2 1) hM
    · exact Complex.ext rfl (hdiag 2).symm
  right_inv p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext k; fin_cases k <;> rfl
  map_add' M N := by apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' r M := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> dsimp <;> simp

private theorem hermitian3Equiv_symm_diag (d : Fin 3 → ℝ) (v : Fin 3 → ℂ) (k : Fin 3) :
    ((hermitian3Equiv.symm (d, v) : ComplexMatrix3) k k).re = d k := by
  fin_cases k <;> rfl
private theorem hermitian3Equiv_symm_01 (d : Fin 3 → ℝ) (v : Fin 3 → ℂ) :
    (hermitian3Equiv.symm (d, v) : ComplexMatrix3) 0 1 = v 0 := rfl
private theorem hermitian3Equiv_symm_02 (d : Fin 3 → ℝ) (v : Fin 3 → ℂ) :
    (hermitian3Equiv.symm (d, v) : ComplexMatrix3) 0 2 = v 1 := rfl
private theorem hermitian3Equiv_symm_12 (d : Fin 3 → ℝ) (v : Fin 3 → ℂ) :
    (hermitian3Equiv.symm (d, v) : ComplexMatrix3) 1 2 = v 2 := rfl

private def complexEquivRealProd : ℂ ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv z := Complex.ext rfl rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := by rw [Complex.real_smul]; apply Prod.ext <;> simp

private theorem complex_finrank : Module.finrank ℝ ℂ = 2 := by
  rw [LinearEquiv.finrank_eq complexEquivRealProd, Module.finrank_prod, Module.finrank_self]

theorem hermitian3_finrank : Module.finrank ℝ Hermitian3 = 9 := by
  rw [LinearEquiv.finrank_eq hermitian3Equiv, Module.finrank_prod, Module.finrank_pi_fintype,
    Module.finrank_pi_fintype, complex_finrank]
  simp

theorem standardComplexWindow_finrank :
    Module.finrank ℝ standardComplexWindow.toSubalgebra.carrier = 9 := by
  change Module.finrank ℝ ↥(LinearMap.range standardComplexWindow.embedding) = 9
  have heq := LinearEquiv.ofInjective standardComplexWindow.embedding standardComplexWindow.injective
  rw [← LinearEquiv.finrank_eq heq]
  exact hermitian3_finrank

theorem standardComplexWindow_contains_iff (x : Albert) :
    standardComplexWindow.Contains x ↔
      (x.2 0).1.imJ = 0 ∧ (x.2 0).1.imK = 0 ∧ (x.2 0).2 = 0 ∧
      (x.2 1).1.imJ = 0 ∧ (x.2 1).1.imK = 0 ∧ (x.2 1).2 = 0 ∧
      (x.2 2).1.imJ = 0 ∧ (x.2 2).1.imK = 0 ∧ (x.2 2).2 = 0 := by
  constructor
  · rintro ⟨M, rfl⟩
    simp [complexHermToAlbert]
  · rintro ⟨h0j, h0k, h0s, h1j, h1k, h1s, h2j, h2k, h2s⟩
    let M01 : ℂ := ⟨(x.2 0).1.re, (x.2 0).1.imI⟩
    let M02 : ℂ := ⟨(x.2 1).1.re, (x.2 1).1.imI⟩
    let M12 : ℂ := ⟨(x.2 2).1.re, (x.2 2).1.imI⟩
    refine ⟨hermitian3Equiv.symm (x.1, ![M01, M02, M12]), ?_⟩
    apply albert_ext <;> rw [standardComplexWindow_apply] <;> dsimp only [complexHermToAlbert]
    · rw [hermitian3Equiv_symm_diag]
    · rw [hermitian3Equiv_symm_diag]
    · rw [hermitian3Equiv_symm_diag]
    · rw [hermitian3Equiv_symm_01]
      dsimp [complexToOctonion, M01]
      apply Prod.ext <;> [apply Quaternion.ext <;> [rfl; rfl; exact h0j.symm; exact h0k.symm];
        exact h0s.symm]
    · rw [hermitian3Equiv_symm_02]
      dsimp [complexToOctonion, M02]
      apply Prod.ext <;> [apply Quaternion.ext <;> [rfl; rfl; exact h1j.symm; exact h1k.symm];
        exact h1s.symm]
    · rw [hermitian3Equiv_symm_12]
      dsimp [complexToOctonion, M12]
      apply Prod.ext <;> [apply Quaternion.ext <;> [rfl; rfl; exact h2j.symm; exact h2k.symm];
        exact h2s.symm]

abbrev QuatMatrix3 := Matrix (Fin 3) (Fin 3) (Quaternion ℝ)
abbrev QuatHermitian3 := selfAdjoint QuatMatrix3

instance : StarModule ℝ (Quaternion ℝ) where
  star_smul r q := by apply Quaternion.ext <;> simp

structure QuaternionicWindow where
  subalgebra : NativeJordanSubalgebra
  embedding : QuatHermitian3 →ₗ[ℝ] Albert
  injective : Function.Injective embedding
  range_eq : LinearMap.range embedding = subalgebra.carrier
  unit : embedding 1 = albertUnit
  preserves_product : ∀ x y z : QuatHermitian3,
    (z : QuatMatrix3) = (1 / 2 : ℝ) • ((x : QuatMatrix3) * (y : QuatMatrix3) +
      (y : QuatMatrix3) * (x : QuatMatrix3)) →
    embedding z = jordanMul (embedding x) (embedding y)
  preserves_trace : ∀ x : QuatHermitian3,
    albertTrace (embedding x) =
      ((x : QuatMatrix3) 0 0).re + ((x : QuatMatrix3) 1 1).re + ((x : QuatMatrix3) 2 2).re

theorem quatHermitian_product_closed (M N : QuatHermitian3) :
    ∃ P : QuatHermitian3, (P : QuatMatrix3) =
      (1 / 2 : ℝ) • ((M : QuatMatrix3) * (N : QuatMatrix3) + (N : QuatMatrix3) * (M : QuatMatrix3)) := by
  refine ⟨⟨(1 / 2 : ℝ) • ((M : QuatMatrix3) * (N : QuatMatrix3) + (N : QuatMatrix3) * (M : QuatMatrix3)), ?_⟩, rfl⟩
  rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial]
  have hM : star (M : QuatMatrix3) = M := M.prop
  have hN : star (N : QuatMatrix3) = N := N.prop
  rw [hM, hN, add_comm]

def quaternionicWindowOfQuatEmbedding (φ : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hφ : IsQuatEmbedding φ) : QuaternionicWindow :=
  let emb : QuatHermitian3 →ₗ[ℝ] Albert :=
    { toFun := fun M => quatMatrixToAlbert φ (M : QuatMatrix3)
      map_add' := fun M N => by
        let xM := quatMatrixToAlbert φ (M : QuatMatrix3)
        let xN := quatMatrixToAlbert φ (N : QuatMatrix3)
        change quatMatrixToAlbert φ ((M + N : QuatHermitian3) : QuatMatrix3) = xM + xN
        apply albert_ext
        · rw [albert_add_fst]; rfl
        · rw [albert_add_fst]; rfl
        · rw [albert_add_fst]; rfl
        · rw [albert_add_snd]; dsimp [xM, xN, quatMatrixToAlbert]; rw [← map_add]
        · rw [albert_add_snd]; dsimp [xM, xN, quatMatrixToAlbert]; rw [← map_add]
        · rw [albert_add_snd]; dsimp [xM, xN, quatMatrixToAlbert]; rw [← map_add]
      map_smul' := fun r M => by
        let xM := quatMatrixToAlbert φ (M : QuatMatrix3)
        change quatMatrixToAlbert φ ((r • M : QuatHermitian3) : QuatMatrix3) = r • xM
        apply albert_ext
        · rw [albert_smul_fst]; dsimp [xM, quatMatrixToAlbert]
        · rw [albert_smul_fst]; dsimp [xM, quatMatrixToAlbert]
        · rw [albert_smul_fst]; dsimp [xM, quatMatrixToAlbert]
        · rw [albert_smul_snd]; dsimp [xM, quatMatrixToAlbert]; rw [map_smul]
        · rw [albert_smul_snd]; dsimp [xM, quatMatrixToAlbert]; rw [map_smul]
        · rw [albert_smul_snd]; dsimp [xM, quatMatrixToAlbert]; rw [map_smul] }
  have hinj : Function.Injective emb := fun M N h => by
    apply Subtype.ext
    funext i j
    have hdiag : ∀ k : Fin 3, ((M : QuatMatrix3) k k).re = ((N : QuatMatrix3) k k).re := fun k =>
      congrArg (fun a : Albert => a.1 k) h
    have hM := M.prop
    have hN := N.prop
    have hM' : ∀ a b, star ((M : QuatMatrix3) b a) = (M : QuatMatrix3) a b := fun a b =>
      congrArg (fun A : QuatMatrix3 => A a b) hM
    have hN' : ∀ a b, star ((N : QuatMatrix3) b a) = (N : QuatMatrix3) a b := fun a b =>
      congrArg (fun A : QuatMatrix3 => A a b) hN
    have h01 := hφ.injective (congrArg (fun a : Albert => a.2 0) h)
    have h02 := hφ.injective (congrArg (fun a : Albert => a.2 1) h)
    have h12 := hφ.injective (congrArg (fun a : Albert => a.2 2) h)
    fin_cases i <;> fin_cases j <;> dsimp
    · rw [quat_eq_re_smul_one (hM' 0 0), quat_eq_re_smul_one (hN' 0 0), hdiag 0]
    · exact h01
    · exact h02
    · rw [← hM' 1 0, ← hN' 1 0, h01]
    · rw [quat_eq_re_smul_one (hM' 1 1), quat_eq_re_smul_one (hN' 1 1), hdiag 1]
    · exact h12
    · rw [← hM' 2 0, ← hN' 2 0, h02]
    · rw [← hM' 2 1, ← hN' 2 1, h12]
    · rw [quat_eq_re_smul_one (hM' 2 2), quat_eq_re_smul_one (hN' 2 2), hdiag 2]
  have hunit : emb 1 = albertUnit := by
    change quatMatrixToAlbert φ ((1 : QuatHermitian3) : QuatMatrix3) = albertUnit
    apply albert_ext <;> dsimp [quatMatrixToAlbert] <;>
      simp [albertUnit_fst, albertUnit_snd, map_zero]
  have hprod : ∀ x y z : QuatHermitian3,
      (z : QuatMatrix3) = (1 / 2 : ℝ) • ((x : QuatMatrix3) * (y : QuatMatrix3) +
        (y : QuatMatrix3) * (x : QuatMatrix3)) →
      emb z = jordanMul (emb x) (emb y) := fun x y z hz => by
    exact jordanMul_quatMatrixToAlbert φ hφ
      (fun a b => congrArg (fun A : QuatMatrix3 => A a b) x.prop)
      (fun a b => congrArg (fun A : QuatMatrix3 => A a b) y.prop) hz
  { subalgebra :=
      { carrier := LinearMap.range emb
        unit_mem := ⟨1, hunit⟩
        product_mem := fun _ hx _ hy => by
          rcases hx with ⟨mx, rfl⟩
          rcases hy with ⟨my, rfl⟩
          obtain ⟨mz, hmz⟩ := quatHermitian_product_closed mx my
          exact ⟨mz, hprod mx my mz hmz⟩ }
    embedding := emb
    injective := hinj
    range_eq := rfl
    unit := hunit
    preserves_product := hprod
    preserves_trace := fun x => by
      dsimp only [emb, LinearMap.coe_mk, AddHom.coe_mk, quatMatrixToAlbert]
      unfold albertTrace
      rw [Fin.sum_univ_three]
      rfl }

@[simp] theorem quaternionicWindowOfQuatEmbedding_apply (φ : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hφ : IsQuatEmbedding φ) (M : QuatHermitian3) :
    (quaternionicWindowOfQuatEmbedding φ hφ).embedding M = quatMatrixToAlbert φ (M : QuatMatrix3) :=
  rfl

def standardQuaternionicWindow : QuaternionicWindow :=
  quaternionicWindowOfQuatEmbedding quatEmbed1 quatEmbed1_isQuatEmbedding

def QuaternionicWindow.transport (Q : QuaternionicWindow) (g : NativeAlbertAutomorphism) :
    QuaternionicWindow where
  subalgebra :=
    { carrier := Q.subalgebra.carrier.map g.linearEquiv.toLinearMap
      unit_mem := ⟨albertUnit, Q.subalgebra.unit_mem, g.preserves_unit⟩
      product_mem := fun _ hx _ hy => by
        rcases hx with ⟨a, ha, rfl⟩
        rcases hy with ⟨b, hb, rfl⟩
        exact ⟨jordanMul a b, Q.subalgebra.product_mem a ha b hb, g.preserves_product a b⟩ }
  embedding := g.linearEquiv.toLinearMap.comp Q.embedding
  injective := g.linearEquiv.injective.comp Q.injective
  range_eq := by
    rw [LinearMap.range_comp, Q.range_eq]
  unit := by simp [Q.unit, g.preserves_unit]
  preserves_product x y z hz := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [Q.preserves_product x y z hz, g.preserves_product]
  preserves_trace x := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, g.preserves_trace]
    exact Q.preserves_trace x

private def quatEquivFin4 : Quaternion ℝ ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun q := ![q.re, q.imI, q.imJ, q.imK]
  invFun v := ⟨v 0, v 1, v 2, v 3⟩
  left_inv q := by apply Quaternion.ext <;> rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' p q := by funext i; fin_cases i <;> rfl
  map_smul' r q := by funext i; fin_cases i <;> rfl

private theorem quat_finrank : Module.finrank ℝ (Quaternion ℝ) = 4 := by
  rw [LinearEquiv.finrank_eq quatEquivFin4, Module.finrank_fin_fun]

def mkQuatHerm3Matrix (d : Fin 3 → ℝ) (v : Fin 3 → Quaternion ℝ) : QuatMatrix3 :=
  fun i j =>
    if i = 0 ∧ j = 0 then ⟨d 0, 0, 0, 0⟩
    else if i = 1 ∧ j = 1 then ⟨d 1, 0, 0, 0⟩
    else if i = 2 ∧ j = 2 then ⟨d 2, 0, 0, 0⟩
    else if i = 0 ∧ j = 1 then v 0
    else if i = 1 ∧ j = 0 then star (v 0)
    else if i = 0 ∧ j = 2 then v 1
    else if i = 2 ∧ j = 0 then star (v 1)
    else if i = 1 ∧ j = 2 then v 2
    else star (v 2)

def quatHermitian3Equiv : QuatHermitian3 ≃ₗ[ℝ] ((Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ)) where
  toFun M := (fun i => ((M : QuatMatrix3) i i).re,
    ![(M : QuatMatrix3) 0 1, (M : QuatMatrix3) 0 2, (M : QuatMatrix3) 1 2])
  invFun p :=
    ⟨mkQuatHerm3Matrix p.1 p.2, by
      dsimp only [QuatHermitian3]
      rw [selfAdjoint.mem_iff]
      funext i j
      fin_cases i <;> fin_cases j <;> simp [mkQuatHerm3Matrix, Matrix.star_apply]⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    have hM : ∀ a b, star ((M : QuatMatrix3) b a) = (M : QuatMatrix3) a b := fun a b =>
      congrArg (fun A : QuatMatrix3 => A a b) M.prop
    fin_cases i <;> fin_cases j <;> simp [mkQuatHerm3Matrix]
    · exact (quat_eq_re_smul_one (hM 0 0)).symm ▸ by apply Quaternion.ext <;> simp
    · exact hM 1 0
    · exact (quat_eq_re_smul_one (hM 1 1)).symm ▸ by apply Quaternion.ext <;> simp
    · exact hM 2 0
    · exact hM 2 1
    · exact (quat_eq_re_smul_one (hM 2 2)).symm ▸ by apply Quaternion.ext <;> simp
  right_inv p := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext k; fin_cases k <;> rfl
  map_add' M N := by apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' r M := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> dsimp

private theorem quatHermitian3Equiv_symm_diag (d : Fin 3 → ℝ) (v : Fin 3 → Quaternion ℝ) (k : Fin 3) :
    ((quatHermitian3Equiv.symm (d, v) : QuatMatrix3) k k).re = d k := by
  fin_cases k <;> rfl
private theorem quatHermitian3Equiv_symm_01 (d : Fin 3 → ℝ) (v : Fin 3 → Quaternion ℝ) :
    (quatHermitian3Equiv.symm (d, v) : QuatMatrix3) 0 1 = v 0 := rfl
private theorem quatHermitian3Equiv_symm_02 (d : Fin 3 → ℝ) (v : Fin 3 → Quaternion ℝ) :
    (quatHermitian3Equiv.symm (d, v) : QuatMatrix3) 0 2 = v 1 := rfl
private theorem quatHermitian3Equiv_symm_12 (d : Fin 3 → ℝ) (v : Fin 3 → Quaternion ℝ) :
    (quatHermitian3Equiv.symm (d, v) : QuatMatrix3) 1 2 = v 2 := rfl

theorem quatHermitian3_finrank : Module.finrank ℝ QuatHermitian3 = 15 := by
  rw [LinearEquiv.finrank_eq quatHermitian3Equiv, Module.finrank_prod, Module.finrank_pi_fintype,
    Module.finrank_pi_fintype, quat_finrank]
  simp

theorem QuaternionicWindow.finrank_eq (Q : QuaternionicWindow) :
    Module.finrank ℝ Q.subalgebra.carrier = 15 := by
  rw [← Q.range_eq]
  have heq := LinearEquiv.ofInjective Q.embedding Q.injective
  rw [← LinearEquiv.finrank_eq heq]
  exact quatHermitian3_finrank

theorem mem_standardQuaternionicWindow_iff (x : Albert) :
    x ∈ standardQuaternionicWindow.subalgebra.carrier ↔
      (x.2 0).2 = 0 ∧ (x.2 1).2 = 0 ∧ (x.2 2).2 = 0 := by
  rw [← standardQuaternionicWindow.range_eq]
  constructor
  · rintro ⟨M, rfl⟩
    simp [standardQuaternionicWindow, quatMatrixToAlbert, quatEmbed1_apply]
  · rintro ⟨h0, h1, h2⟩
    refine ⟨quatHermitian3Equiv.symm (x.1, ![(x.2 0).1, (x.2 1).1, (x.2 2).1]), ?_⟩
    apply albert_ext <;> dsimp only [standardQuaternionicWindow] <;>
      rw [quaternionicWindowOfQuatEmbedding_apply] <;> dsimp only [quatMatrixToAlbert]
    · rw [quatHermitian3Equiv_symm_diag]
    · rw [quatHermitian3Equiv_symm_diag]
    · rw [quatHermitian3Equiv_symm_diag]
    · rw [quatHermitian3Equiv_symm_01, quatEmbed1_apply]; apply Prod.ext <;> [rfl; exact h0.symm]
    · rw [quatHermitian3Equiv_symm_02, quatEmbed1_apply]; apply Prod.ext <;> [rfl; exact h1.symm]
    · rw [quatHermitian3Equiv_symm_12, quatEmbed1_apply]; apply Prod.ext <;> [rfl; exact h2.symm]

theorem standardComplexWindow_le_standardQuaternionicWindow :
    standardComplexWindow.toSubalgebra.carrier ≤ standardQuaternionicWindow.subalgebra.carrier := by
  intro x hx
  have hc : standardComplexWindow.Contains x := hx
  rw [standardComplexWindow_contains_iff] at hc
  rw [mem_standardQuaternionicWindow_iff]
  exact ⟨hc.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2⟩

/-! ## Section 6: `AtomAndRankOneBridge`, Frame/Window Conjugacy, and Zero-Pairing Support -/

structure AtomAndRankOneBridge : Prop where
  atom_to_diagAtom0 : ∀ p : Albert, IsAtom p →
    ∃ g : NativeAlbertAutomorphism, g.linearEquiv p = diagAtom 0
  corner12_zero_fixing_diagAtom0 : ∀ x : Albert,
    ∃ g : NativeAlbertAutomorphism,
      g.linearEquiv (diagAtom 0) = diagAtom 0 ∧ (g.linearEquiv x).2 2 = 0
  quadraticMap_atom : ∀ p x : Albert, IsAtom p →
    quadraticMap p x = tracePairing p x • p
  albertSharp_atom_eq_zero : ∀ p : Albert, IsAtom p →
    albertSharp p = 0

theorem frame_to_standardFrame (hB : AtomAndRankOneBridge) (F : NativeJordanFrame) :
    ∃ g : NativeAlbertAutomorphism, ∀ i : Fin 3, g.linearEquiv (F.atom i) = diagAtom i := by
  obtain ⟨g0, hg0⟩ := hB.atom_to_diagAtom0 (F.atom 0) (F.atoms 0)
  let p1 := g0.linearEquiv (F.atom 1)
  obtain ⟨g1, hg1_fix, hg1_corner⟩ := hB.corner12_zero_fixing_diagAtom0 p1
  let g01 := g1.comp g0
  let q1 := g01.linearEquiv (F.atom 1)
  have hq1_atom : IsAtom q1 := g01.map_isAtom (F.atoms 1)
  have hq0_eq : g01.linearEquiv (F.atom 0) = diagAtom 0 := by
    change g1.linearEquiv (g0.linearEquiv (F.atom 0)) = diagAtom 0
    rw [hg0, hg1_fix]
  have horth : jordanMul (diagAtom 0) q1 = 0 := by
    rw [← hq0_eq, ← g01.preserves_product, F.orthogonal 0 1 (by decide), map_zero]
  rw [jordanMul_diagAtom0] at horth
  have hq1_0 : q1.1 0 = 0 := congrArg (fun a : Albert => a.1 0) horth
  have hq1_01 : q1.2 0 = 0 := by
    have hs : (1 / 2 : ℝ) • q1.2 0 = 0 := congrArg (fun a : Albert => a.2 0) horth
    simpa [smul_smul] using congrArg ((2 : ℝ) • ·) hs
  have hq1_02 : q1.2 1 = 0 := by
    have hs : (1 / 2 : ℝ) • q1.2 1 = 0 := congrArg (fun a : Albert => a.2 1) horth
    simpa [smul_smul] using congrArg ((2 : ℝ) • ·) hs
  have hq1_12 : q1.2 2 = 0 := hg1_corner
  have htr : q1.1 1 + q1.1 2 = 1 := by
    have ht : q1.1 0 + q1.1 1 + q1.1 2 = 1 := by
      simpa [albertTrace, Fin.sum_univ_three] using hq1_atom.2
    linarith
  have hsq1 : q1.1 1 = (q1.1 1) ^ 2 := by
    have h := congrArg (fun a : Albert => a.1 1) hq1_atom.1
    rw [jordanMul_diag_1, hq1_01, hq1_12, octDot_zero_left, add_zero, add_zero] at h
    nlinarith
  have h1_cases : q1.1 1 = 0 ∨ q1.1 1 = 1 := by
    have hf : q1.1 1 * (q1.1 1 - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have finish : ∀ g : NativeAlbertAutomorphism,
      g.linearEquiv (F.atom 0) = diagAtom 0 → g.linearEquiv (F.atom 1) = diagAtom 1 →
      ∀ i : Fin 3, g.linearEquiv (F.atom i) = diagAtom i := fun g h0 h1 i => by
    fin_cases i
    · exact h0
    · exact h1
    · have hsum : g.linearEquiv (F.atom 0) + g.linearEquiv (F.atom 1) + g.linearEquiv (F.atom 2) =
          albertUnit := by
        rw [← map_add, ← map_add, ← Fin.sum_univ_three, F.sum_unit, g.preserves_unit]
      rw [h0, h1] at hsum
      have hds := diagAtom_sum_eq_unit
      rw [Fin.sum_univ_three] at hds
      apply add_left_cancel (hsum.trans hds.symm)
  rcases h1_cases with hq11 | hq11
  · have hq12 : q1.1 2 = 1 := by linarith
    have hq1_eq : q1 = diagAtom 2 := by
      apply albert_ext <;> simp [diagAtom, hq1_0, hq11, hq12, hq1_01, hq1_02, hq1_12]
    refine ⟨swap12AlbertAuto.comp g01, finish _ ?_ ?_⟩
    · change swap12AlbertAuto.linearEquiv (g01.linearEquiv (F.atom 0)) = diagAtom 0
      rw [hq0_eq, swap12AlbertAuto_diagAtom]
      rfl
    · change swap12AlbertAuto.linearEquiv q1 = diagAtom 1
      rw [hq1_eq, swap12AlbertAuto_diagAtom]
      rfl
  · have hq12 : q1.1 2 = 0 := by linarith
    have hq1_eq : q1 = diagAtom 1 := by
      apply albert_ext <;> simp [diagAtom, hq1_0, hq11, hq12, hq1_01, hq1_02, hq1_12]
    exact ⟨g01, finish g01 hq0_eq hq1_eq⟩

section WindowBasis

private def hDiag (k : Fin 3) : Hermitian3 :=
  hermitian3Equiv.symm (fun i => if i = k then 1 else 0, 0)

private def hReal (k : Fin 3) : Hermitian3 :=
  hermitian3Equiv.symm (0, fun i => if i = k then 1 else 0)

private def hImag (k : Fin 3) : Hermitian3 :=
  hermitian3Equiv.symm (0, fun i => if i = k then Complex.I else 0)

private theorem half_smul_inj {a b : Albert} (h : (1 / 2 : ℝ) • a = (1 / 2 : ℝ) • b) : a = b := by
  have h2 := congrArg ((2 : ℝ) • ·) h
  simpa [smul_smul] using h2

private theorem hermitian3_span (M : Hermitian3) :
    M = ((M : ComplexMatrix3) 0 0).re • hDiag 0 +
        ((M : ComplexMatrix3) 1 1).re • hDiag 1 +
        ((M : ComplexMatrix3) 2 2).re • hDiag 2 +
        ((M : ComplexMatrix3) 0 1).re • hReal 0 +
        ((M : ComplexMatrix3) 0 1).im • hImag 0 +
        ((M : ComplexMatrix3) 0 2).re • hReal 1 +
        ((M : ComplexMatrix3) 0 2).im • hImag 1 +
        ((M : ComplexMatrix3) 1 2).re • hReal 2 +
        ((M : ComplexMatrix3) 1 2).im • hImag 2 := by
  apply hermitian3Equiv.injective
  simp only [map_add, map_smul, hDiag, hReal, hImag, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i; fin_cases i <;> simp [hermitian3Equiv]
  · funext k; fin_cases k <;> apply Complex.ext <;> simp [hermitian3Equiv]

private theorem standardComplexWindow_hDiag (k : Fin 3) :
    standardComplexWindow.embedding (hDiag k) = diagAtom k := by
  apply albert_ext <;> fin_cases k <;>
    simp [complexHermToAlbert, hDiag, hermitian3Equiv, diagAtom_fst, diagAtom_snd,
      complexToOctonion] <;> rfl

private theorem standardComplexWindow_hReal0 :
    standardComplexWindow.embedding (hReal 0) = slotElem01 octOne := by
  apply albert_ext <;> simp [complexHermToAlbert, hReal, hermitian3Equiv,
    complexToOctonion] <;> rfl

private theorem standardComplexWindow_hReal1 :
    standardComplexWindow.embedding (hReal 1) = slotElem02 octOne := by
  apply albert_ext <;> simp [complexHermToAlbert, hReal, hermitian3Equiv,
    complexToOctonion] <;> rfl

private theorem standardComplexWindow_hReal2 :
    standardComplexWindow.embedding (hReal 2) = slotElem12 octOne := by
  apply albert_ext <;> simp [complexHermToAlbert, hReal, hermitian3Equiv,
    complexToOctonion] <;> rfl

private theorem standardComplexWindow_hImag0 :
    standardComplexWindow.embedding (hImag 0) = slotElem01 octI := by
  apply albert_ext <;> simp [complexHermToAlbert, hImag, hermitian3Equiv,
    complexToOctonion] <;> rfl

private theorem standardComplexWindow_hImag1 :
    standardComplexWindow.embedding (hImag 1) = slotElem02 octI := by
  apply albert_ext <;> simp [complexHermToAlbert, hImag, hermitian3Equiv,
    complexToOctonion] <;> rfl

private theorem standardComplexWindow_hImag2 :
    standardComplexWindow.embedding (hImag 2) = slotElem12 octI := by
  apply albert_ext <;> simp [complexHermToAlbert, hImag, hermitian3Equiv,
    complexToOctonion] <;> rfl

private def hermitian3MulEq (A B C : Hermitian3) : Prop :=
  (C : ComplexMatrix3) = (1 / 2 : ℝ) •
    ((A : ComplexMatrix3) * (B : ComplexMatrix3) + (B : ComplexMatrix3) * (A : ComplexMatrix3))

private theorem hDiag_mul_self (i : Fin 3) : hermitian3MulEq (hDiag i) (hDiag i) (hDiag i) := by
  unfold hermitian3MulEq
  funext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three];
      simp [hDiag, hermitian3Equiv, mkHerm3Matrix]; try apply Complex.ext <;> simp <;> norm_num)

private theorem hDiag_mul_orth {i j : Fin 3} (hij : i ≠ j) :
    hermitian3MulEq (hDiag i) (hDiag j) 0 := by
  unfold hermitian3MulEq
  funext a b
  fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
  all_goals fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hermitian3Equiv, mkHerm3Matrix])

private theorem hDiag_sum_one : hDiag 0 + hDiag 1 + hDiag 2 = 1 := by
  apply Subtype.ext
  funext a b
  fin_cases a <;> fin_cases b <;> apply Complex.ext <;> simp [hDiag, hermitian3Equiv, mkHerm3Matrix]

private theorem hermitian3_rel_01_diag0 :
    hermitian3MulEq (hDiag 0) (hReal 0) ((1 / 2 : ℝ) • hReal 0) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hReal, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_01_diag1 :
    hermitian3MulEq (hDiag 1) (hReal 0) ((1 / 2 : ℝ) • hReal 0) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hReal, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_01_sq :
    hermitian3MulEq (hReal 0) (hReal 0) (hDiag 0 + hDiag 1) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hReal, hermitian3Equiv, mkHerm3Matrix] <;> norm_num)

private theorem hermitian3_rel_02_diag0 :
    hermitian3MulEq (hDiag 0) (hReal 1) ((1 / 2 : ℝ) • hReal 1) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hReal, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_02_diag2 :
    hermitian3MulEq (hDiag 2) (hReal 1) ((1 / 2 : ℝ) • hReal 1) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hReal, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_02_sq :
    hermitian3MulEq (hReal 1) (hReal 1) (hDiag 0 + hDiag 2) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hReal, hermitian3Equiv, mkHerm3Matrix] <;> norm_num)

private theorem hermitian3_rel_01_02 :
    hermitian3MulEq (hReal 0) (hReal 1) ((1 / 2 : ℝ) • hReal 2) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hReal, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_i0_diag0 :
    hermitian3MulEq (hDiag 0) (hImag 0) ((1 / 2 : ℝ) • hImag 0) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hImag, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_i0_diag1 :
    hermitian3MulEq (hDiag 1) (hImag 0) ((1 / 2 : ℝ) • hImag 0) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hImag, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_r0_i0 :
    hermitian3MulEq (hReal 0) (hImag 0) 0 := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hReal, hImag, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_i0_sq :
    hermitian3MulEq (hImag 0) (hImag 0) (hDiag 0 + hDiag 1) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hDiag, hImag, hermitian3Equiv, mkHerm3Matrix] <;> norm_num)

private theorem hermitian3_rel_i0_r2 :
    hermitian3MulEq (hImag 0) (hReal 2) ((1 / 2 : ℝ) • hImag 1) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hReal, hImag, hermitian3Equiv, mkHerm3Matrix])

private theorem hermitian3_rel_r0_i1 :
    hermitian3MulEq (hReal 0) (hImag 1) ((1 / 2 : ℝ) • hImag 2) := by
  unfold hermitian3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Complex.ext <;> simp [hReal, hImag, hermitian3Equiv, mkHerm3Matrix])

theorem complexWindow_conjugate_standard (hB : AtomAndRankOneBridge) (W : ComplexWindow) :
    ∃ g : NativeAlbertAutomorphism, ∀ M : Hermitian3,
      g.linearEquiv (W.embedding M) = standardComplexWindow.embedding M := by
  let F : NativeJordanFrame :=
    { atom := fun i => W.embedding (hDiag i)
      atoms := fun i =>
        ⟨(W.preserves_product _ _ _ (hDiag_mul_self i)).symm, by
          rw [W.preserves_trace]
          dsimp only [Matrix.trace, Matrix.diag]
          rw [Fin.sum_univ_three]
          fin_cases i <;> simp [hDiag, hermitian3Equiv, mkHerm3Matrix]⟩
      orthogonal := fun i j hij => by
        rw [← W.preserves_product _ _ 0 (hDiag_mul_orth hij), map_zero]
      sum_unit := by
        rw [Fin.sum_univ_three, ← map_add, ← map_add, hDiag_sum_one, W.unit] }
  obtain ⟨g0, hg0⟩ := frame_to_standardFrame hB F
  let W1 := W.transport g0
  have hw1_diag : ∀ i, W1.embedding (hDiag i) = diagAtom i := hg0
  have hc01_slot : W1.embedding (hReal 0) = slotElem01 ((W1.embedding (hReal 0)).2 0) := by
    apply eq_slotElem01_of_peirce
    · rw [← hw1_diag 0, ← W1.preserves_product _ _ _ hermitian3_rel_01_diag0, map_smul]
    · rw [← hw1_diag 1, ← W1.preserves_product _ _ _ hermitian3_rel_01_diag1, map_smul]
  have hc01_ns : octNormSq ((W1.embedding (hReal 0)).2 0) = 1 := by
    have hsq := W1.preserves_product (hReal 0) (hReal 0) (hDiag 0 + hDiag 1) hermitian3_rel_01_sq
    rw [map_add, hw1_diag 0, hw1_diag 1] at hsq
    conv_rhs at hsq => rw [hc01_slot, jordanMul_slotElem01_self]
    have h0 := congrArg (fun a : Albert => a.1 0) hsq
    simpa [albert_add_fst, albert_smul_fst, diagAtom_fst] using h0.symm
  obtain ⟨g1, hg1_diag, r1, hr1_nn, hr1_slot⟩ := exists_frameStab_slot01_real (W1.embedding (hReal 0))
  have hr1_eq : r1 = 1 := by
    have hns : octNormSq ((g1.linearEquiv (W1.embedding (hReal 0))).2 0) = 1 := by
      have hsq : jordanMul (g1.linearEquiv (W1.embedding (hReal 0)))
          (g1.linearEquiv (W1.embedding (hReal 0))) = diagAtom 0 + diagAtom 1 := by
        rw [← g1.preserves_product, ← W1.preserves_product _ _ _ hermitian3_rel_01_sq,
          map_add, map_add, hw1_diag 0, hw1_diag 1, hg1_diag 0, hg1_diag 1]
      have h0 : g1.linearEquiv (W1.embedding (hReal 0)) =
          slotElem01 ((g1.linearEquiv (W1.embedding (hReal 0))).2 0) := by
        apply eq_slotElem01_of_peirce
        · rw [← hg1_diag 0, ← g1.preserves_product, ← hw1_diag 0,
            ← W1.preserves_product _ _ _ hermitian3_rel_01_diag0, map_smul, map_smul]
        · rw [← hg1_diag 1, ← g1.preserves_product, ← hw1_diag 1,
            ← W1.preserves_product _ _ _ hermitian3_rel_01_diag1, map_smul, map_smul]
      rw [h0, jordanMul_slotElem01_self] at hsq
      have h0c := congrArg (fun a : Albert => a.1 0) hsq
      simpa [albert_add_fst, albert_smul_fst, diagAtom_fst] using h0c
    rw [hr1_slot, octonionScalar_eq_smul, ← octOne, octNormSq_smul, octNormSq_one, mul_one] at hns
    nlinarith [hr1_nn]
  let W2 := W1.transport g1
  have hw2_diag : ∀ i, W2.embedding (hDiag i) = diagAtom i := fun i => by
    change g1.linearEquiv (W1.embedding (hDiag i)) = diagAtom i
    rw [hw1_diag i, hg1_diag i]
  have hw2_r0 : W2.embedding (hReal 0) = slotElem01 octOne := by
    have hslot : W2.embedding (hReal 0) = slotElem01 ((W2.embedding (hReal 0)).2 0) := by
      apply eq_slotElem01_of_peirce
      · rw [← hw2_diag 0, ← W2.preserves_product _ _ _ hermitian3_rel_01_diag0, map_smul]
      · rw [← hw2_diag 1, ← W2.preserves_product _ _ _ hermitian3_rel_01_diag1, map_smul]
    rw [hslot, show (W2.embedding (hReal 0)).2 0 = octonionScalar r1 from hr1_slot, hr1_eq]
    rfl
  obtain ⟨g2, hg2_diag, hg2_r0, r2, hr2_nn, hr2_slot⟩ :=
    exists_frameAnd01OneStab_slot02_real (W2.embedding (hReal 1))
  let W3 := W2.transport g2
  have hw3_diag : ∀ i, W3.embedding (hDiag i) = diagAtom i := fun i => by
    change g2.linearEquiv (W2.embedding (hDiag i)) = diagAtom i
    rw [hw2_diag i, hg2_diag i]
  have hw3_r0 : W3.embedding (hReal 0) = slotElem01 octOne := by
    change g2.linearEquiv (W2.embedding (hReal 0)) = slotElem01 octOne
    rw [hw2_r0, hg2_r0]
  have hw3_r1_slot : W3.embedding (hReal 1) = slotElem02 ((W3.embedding (hReal 1)).2 1) := by
    apply eq_slotElem02_of_peirce
    · rw [← hw3_diag 0, ← W3.preserves_product _ _ _ hermitian3_rel_02_diag0, map_smul]
    · rw [← hw3_diag 2, ← W3.preserves_product _ _ _ hermitian3_rel_02_diag2, map_smul]
  have hr2_eq : r2 = 1 := by
    have hsq := W3.preserves_product (hReal 1) (hReal 1) (hDiag 0 + hDiag 2) hermitian3_rel_02_sq
    rw [map_add, hw3_diag 0, hw3_diag 2] at hsq
    conv_rhs at hsq =>
      rw [hw3_r1_slot, show (W3.embedding (hReal 1)).2 1 = octonionScalar r2 from hr2_slot,
        jordanMul_slotElem02_self]
    have h0c := congrArg (fun a : Albert => a.1 0) hsq
    simp only [albert_add_fst, diagAtom_fst, albert_smul_fst] at h0c
    rw [octonionScalar_eq_smul, ← octOne, octNormSq_smul, octNormSq_one, mul_one] at h0c
    simp at h0c
    nlinarith [hr2_nn]
  have hw3_r1 : W3.embedding (hReal 1) = slotElem02 octOne := by
    rw [hw3_r1_slot, show (W3.embedding (hReal 1)).2 1 = octonionScalar r2 from hr2_slot, hr2_eq]
    rfl
  have hw3_r2 : W3.embedding (hReal 2) = slotElem12 octOne := by
    have h := W3.preserves_product (hReal 0) (hReal 1) ((1 / 2 : ℝ) • hReal 2) hermitian3_rel_01_02
    rw [map_smul, hw3_r0, hw3_r1, jordanMul_slotElem01_slotElem02, octonionConj_one,
      octonionMul_one_left] at h
    exact half_smul_inj h
  have hw3_i0_slot : W3.embedding (hImag 0) = slotElem01 ((W3.embedding (hImag 0)).2 0) := by
    apply eq_slotElem01_of_peirce
    · rw [← hw3_diag 0, ← W3.preserves_product _ _ _ hermitian3_rel_i0_diag0, map_smul]
    · rw [← hw3_diag 1, ← W3.preserves_product _ _ _ hermitian3_rel_i0_diag1, map_smul]
  let u := (W3.embedding (hImag 0)).2 0
  have hu_re : octonionReal u = 0 := by
    have h := W3.preserves_product (hReal 0) (hImag 0) 0 hermitian3_rel_r0_i0
    rw [map_zero, hw3_r0] at h
    conv_rhs at h => rw [hw3_i0_slot]
    have h0 := congrArg (fun a : Albert => a.1 0) h
    simp only [albert_zero_fst, jordanMul_diag_0, slotElem01_fst, slotElem01_snd_0,
      slotElem01_snd_1, octDot_zero_left, add_zero, zero_mul] at h0
    simpa [octOne, octDot_scalar_left] using h0.symm
  have hu_ns : octNormSq u = 1 := by
    have h := W3.preserves_product (hImag 0) (hImag 0) (hDiag 0 + hDiag 1) hermitian3_rel_i0_sq
    rw [map_add, hw3_diag 0, hw3_diag 1] at h
    conv_rhs at h => rw [hw3_i0_slot, jordanMul_slotElem01_self]
    have h0 := congrArg (fun a : Albert => a.1 0) h
    simpa [albert_add_fst, albert_smul_fst, diagAtom_fst] using h0.symm
  obtain ⟨α, rα, hrα_nn, hαu⟩ := exists_octAuto_imag_to_I u hu_re
  have hrα_eq : rα = 1 := by
    have hns : octNormSq (α.equiv u) = octNormSq u := α.map_normSq u
    rw [hαu, hu_ns, octNormSq_smul, show octNormSq octI = 1 from by rw [octNormSq_eq_coords]; simp [octI],
      mul_one] at hns
    nlinarith
  have hαu_I : α.equiv u = octI := by rw [hαu, hrα_eq, one_smul]
  let g3 := octAutoToAlbertAuto α
  let W4 := W3.transport g3
  have hw4_diag : ∀ i, W4.embedding (hDiag i) = diagAtom i := fun i => by
    change g3.linearEquiv (W3.embedding (hDiag i)) = diagAtom i
    rw [hw3_diag i, octAutoToAlbertAuto_diagAtom]
  have hw4_r0 : W4.embedding (hReal 0) = slotElem01 octOne := by
    change g3.linearEquiv (W3.embedding (hReal 0)) = slotElem01 octOne
    rw [hw3_r0, octAutoToAlbertAuto_slotElem01, α.map_one]
  have hw4_r1 : W4.embedding (hReal 1) = slotElem02 octOne := by
    change g3.linearEquiv (W3.embedding (hReal 1)) = slotElem02 octOne
    rw [hw3_r1, octAutoToAlbertAuto_slotElem02, α.map_one]
  have hw4_r2 : W4.embedding (hReal 2) = slotElem12 octOne := by
    change g3.linearEquiv (W3.embedding (hReal 2)) = slotElem12 octOne
    rw [hw3_r2, octAutoToAlbertAuto_slotElem12, α.map_one]
  have hw4_i0 : W4.embedding (hImag 0) = slotElem01 octI := by
    change g3.linearEquiv (W3.embedding (hImag 0)) = slotElem01 octI
    rw [hw3_i0_slot, octAutoToAlbertAuto_slotElem01, hαu_I]
  have hw4_i1 : W4.embedding (hImag 1) = slotElem02 octI := by
    have h := W4.preserves_product (hImag 0) (hReal 2) ((1 / 2 : ℝ) • hImag 1) hermitian3_rel_i0_r2
    rw [map_smul, hw4_i0, hw4_r2, jordanMul_slotElem01_slotElem12, octonionMul_one_right] at h
    exact half_smul_inj h
  have hw4_i2 : W4.embedding (hImag 2) = slotElem12 octI := by
    have h := W4.preserves_product (hReal 0) (hImag 1) ((1 / 2 : ℝ) • hImag 2) hermitian3_rel_r0_i1
    rw [map_smul, hw4_r0, hw4_i1, jordanMul_slotElem01_slotElem02, octonionConj_one,
      octonionMul_one_left] at h
    exact half_smul_inj h
  refine ⟨g3.comp (g2.comp (g1.comp g0)), fun M => ?_⟩
  conv_lhs => rw [hermitian3_span M]
  conv_rhs => rw [hermitian3_span M]
  simp only [map_add, map_smul]
  change ((M : ComplexMatrix3) 0 0).re • W4.embedding (hDiag 0) +
    ((M : ComplexMatrix3) 1 1).re • W4.embedding (hDiag 1) +
    ((M : ComplexMatrix3) 2 2).re • W4.embedding (hDiag 2) +
    ((M : ComplexMatrix3) 0 1).re • W4.embedding (hReal 0) +
    ((M : ComplexMatrix3) 0 1).im • W4.embedding (hImag 0) +
    ((M : ComplexMatrix3) 0 2).re • W4.embedding (hReal 1) +
    ((M : ComplexMatrix3) 0 2).im • W4.embedding (hImag 1) +
    ((M : ComplexMatrix3) 1 2).re • W4.embedding (hReal 2) +
    ((M : ComplexMatrix3) 1 2).im • W4.embedding (hImag 2) = _
  rw [hw4_diag 0, hw4_diag 1, hw4_diag 2, hw4_r0, hw4_i0, hw4_r1, hw4_i1, hw4_r2, hw4_i2,
    standardComplexWindow_hDiag 0, standardComplexWindow_hDiag 1, standardComplexWindow_hDiag 2,
    standardComplexWindow_hReal0, standardComplexWindow_hImag0,
    standardComplexWindow_hReal1, standardComplexWindow_hImag1,
    standardComplexWindow_hReal2, standardComplexWindow_hImag2]

private def complexHermToQuatHerm : Hermitian3 →ₗ[ℝ] QuatHermitian3 where
  toFun M := ⟨complexHermitianToQuatMatrix M, by
    dsimp only [QuatHermitian3]
    rw [selfAdjoint.mem_iff]
    funext i j
    exact complexHermitianToQuatMatrix_herm M i j⟩
  map_add' M N := by
    apply Subtype.ext; funext i j
    exact complexToQuat.map_add _ _
  map_smul' r M := by
    apply Subtype.ext; funext i j
    exact complexToQuat.map_smul _ _

private def qDiag (k : Fin 3) : QuatHermitian3 := complexHermToQuatHerm (hDiag k)
private def qReal (k : Fin 3) : QuatHermitian3 := complexHermToQuatHerm (hReal k)
private def qI (k : Fin 3) : QuatHermitian3 := complexHermToQuatHerm (hImag k)
private def qJ (k : Fin 3) : QuatHermitian3 :=
  quatHermitian3Equiv.symm (0, fun i => if i = k then ⟨0, 0, 1, 0⟩ else 0)
private def qK (k : Fin 3) : QuatHermitian3 :=
  quatHermitian3Equiv.symm (0, fun i => if i = k then ⟨0, 0, 0, 1⟩ else 0)

private theorem quatHermitian3_span (M : QuatHermitian3) :
    M = ((M : QuatMatrix3) 0 0).re • qDiag 0 +
        ((M : QuatMatrix3) 1 1).re • qDiag 1 +
        ((M : QuatMatrix3) 2 2).re • qDiag 2 +
        ((M : QuatMatrix3) 0 1).re • qReal 0 +
        ((M : QuatMatrix3) 0 1).imI • qI 0 +
        ((M : QuatMatrix3) 0 1).imJ • qJ 0 +
        ((M : QuatMatrix3) 0 1).imK • qK 0 +
        ((M : QuatMatrix3) 0 2).re • qReal 1 +
        ((M : QuatMatrix3) 0 2).imI • qI 1 +
        ((M : QuatMatrix3) 0 2).imJ • qJ 1 +
        ((M : QuatMatrix3) 0 2).imK • qK 1 +
        ((M : QuatMatrix3) 1 2).re • qReal 2 +
        ((M : QuatMatrix3) 1 2).imI • qI 2 +
        ((M : QuatMatrix3) 1 2).imJ • qJ 2 +
        ((M : QuatMatrix3) 1 2).imK • qK 2 := by
  apply quatHermitian3Equiv.injective
  have hqd : ∀ k, quatHermitian3Equiv (qDiag k) = (fun i => if i = k then 1 else 0, 0) := fun k => by
    apply Prod.ext <;> funext i <;> fin_cases k <;> fin_cases i <;> rfl
  have hqr : ∀ k, quatHermitian3Equiv (qReal k) = (0, fun i => if i = k then 1 else 0) := fun k => by
    apply Prod.ext <;> funext i <;> fin_cases k <;> fin_cases i <;> rfl
  have hqi : ∀ k, quatHermitian3Equiv (qI k) = (0, fun i => if i = k then ⟨0, 1, 0, 0⟩ else 0) := fun k => by
    apply Prod.ext <;> funext i <;> fin_cases k <;> fin_cases i <;> rfl
  simp only [map_add, map_smul, hqd, hqr, hqi, qJ, qK, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i; fin_cases i <;> simp [quatHermitian3Equiv]
  · funext k; fin_cases k <;> apply Quaternion.ext <;> simp [quatHermitian3Equiv]

private theorem complexToQuat_inj {z w : ℂ} (h : complexToQuat z = complexToQuat w) : z = w :=
  Complex.ext (congrArg (fun q : Quaternion ℝ => q.re) h) (congrArg (fun q : Quaternion ℝ => q.imI) h)

private def QuaternionicWindow.toComplexWindow (Q : QuaternionicWindow) : ComplexWindow where
  embedding := Q.embedding.comp complexHermToQuatHerm
  injective := fun M N h => by
    have hq := Q.injective h
    apply Subtype.ext
    funext i j
    exact complexToQuat_inj (congrArg (fun A : QuatMatrix3 => A i j) (congrArg Subtype.val hq))
  unit := by
    have h1 : complexHermToQuatHerm 1 = 1 := by
      apply Subtype.ext; funext i j
      fin_cases i <;> fin_cases j <;>
        simp [complexHermToQuatHerm, complexHermitianToQuatMatrix, complexToQuat] <;>
        try apply Quaternion.ext <;> simp
    simp [h1, Q.unit]
  product_closed := standardComplexWindow.product_closed
  preserves_product M N P hP := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    refine Q.preserves_product _ _ _ ?_
    funext i j
    have hPc := congrArg (fun A : ComplexMatrix3 => A i j) hP
    simp only [complexHermToQuatHerm, LinearMap.coe_mk, AddHom.coe_mk, complexHermitianToQuatMatrix,
      Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, hPc, Complex.real_smul,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Fin.sum_univ_three]
    (apply Quaternion.ext <;> simp [complexToQuat]); all_goals ring
  preserves_trace M := by
    simp only [LinearMap.coe_comp, Function.comp_apply, Q.preserves_trace]
    dsimp only [Matrix.trace, Matrix.diag]
    rw [Fin.sum_univ_three]
    simp [complexHermToQuatHerm, complexHermitianToQuatMatrix, complexToQuat]

private def quat3MulEq (A B C : QuatHermitian3) : Prop :=
  (C : QuatMatrix3) = (1 / 2 : ℝ) •
    ((A : QuatMatrix3) * (B : QuatMatrix3) + (B : QuatMatrix3) * (A : QuatMatrix3))

private theorem quat3_rel_j0_d0 : quat3MulEq (qDiag 0) (qJ 0) ((1 / 2 : ℝ) • qJ 0) := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qDiag, qJ, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hDiag, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

private theorem quat3_rel_j0_d1 : quat3MulEq (qDiag 1) (qJ 0) ((1 / 2 : ℝ) • qJ 0) := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qDiag, qJ, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hDiag, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

private theorem quat3_rel_r0_j0 : quat3MulEq (qReal 0) (qJ 0) 0 := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qReal, qJ, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hReal, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

private theorem quat3_rel_i0_j0 : quat3MulEq (qI 0) (qJ 0) 0 := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qI, qJ, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hImag, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

private theorem quat3_rel_j0_sq : quat3MulEq (qJ 0) (qJ 0) (qDiag 0 + qDiag 1) := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qDiag, qJ, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hDiag, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix] <;> norm_num)

private theorem quat3_rel_j0_r2 : quat3MulEq (qJ 0) (qReal 2) ((1 / 2 : ℝ) • qJ 1) := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qReal, qJ, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hReal, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

private theorem quat3_rel_r0_j1 : quat3MulEq (qReal 0) (qJ 1) ((1 / 2 : ℝ) • qJ 2) := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qReal, qJ, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hReal, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

private theorem quat3_rel_i0_j2 : quat3MulEq (qI 0) (qJ 2) ((1 / 2 : ℝ) • qK 1) := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qI, qJ, qK, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hImag, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

private theorem quat3_rel_r0_k1 : quat3MulEq (qReal 0) (qK 1) ((1 / 2 : ℝ) • qK 2) := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qReal, qK, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hReal, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

private theorem quat3_rel_k1_r2 : quat3MulEq (qK 1) (qReal 2) ((1 / 2 : ℝ) • qK 0) := by
  unfold quat3MulEq; funext a b; fin_cases a <;> fin_cases b <;>
    (rw [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_three];
      apply Quaternion.ext <;> simp [qReal, qK, complexHermToQuatHerm, complexHermitianToQuatMatrix,
        complexToQuat, hReal, hermitian3Equiv, mkHerm3Matrix, quatHermitian3Equiv,
        mkQuatHerm3Matrix])

theorem quaternionicWindow_conjugate_standard_embedding (hB : AtomAndRankOneBridge)
    (Q : QuaternionicWindow) :
    ∃ g : NativeAlbertAutomorphism, ∀ M : QuatHermitian3,
      g.linearEquiv (Q.embedding M) = standardQuaternionicWindow.embedding M := by
  obtain ⟨g0, hg0⟩ := complexWindow_conjugate_standard hB Q.toComplexWindow
  let Q1 := Q.transport g0
  have hc : ∀ M : Hermitian3, Q1.embedding (complexHermToQuatHerm M) =
      standardComplexWindow.embedding M := fun M => hg0 M
  have hq_diag : ∀ i, Q1.embedding (qDiag i) = diagAtom i := fun i => by
    rw [qDiag, hc (hDiag i), standardComplexWindow_hDiag]
  have hq_r0 : Q1.embedding (qReal 0) = slotElem01 octOne := by
    rw [qReal, hc (hReal 0), standardComplexWindow_hReal0]
  have hq_r1 : Q1.embedding (qReal 1) = slotElem02 octOne := by
    rw [qReal, hc (hReal 1), standardComplexWindow_hReal1]
  have hq_r2 : Q1.embedding (qReal 2) = slotElem12 octOne := by
    rw [qReal, hc (hReal 2), standardComplexWindow_hReal2]
  have hq_i0 : Q1.embedding (qI 0) = slotElem01 octI := by
    rw [qI, hc (hImag 0), standardComplexWindow_hImag0]
  have hq_i1 : Q1.embedding (qI 1) = slotElem02 octI := by
    rw [qI, hc (hImag 1), standardComplexWindow_hImag1]
  have hq_i2 : Q1.embedding (qI 2) = slotElem12 octI := by
    rw [qI, hc (hImag 2), standardComplexWindow_hImag2]
  have hj0_slot : Q1.embedding (qJ 0) = slotElem01 ((Q1.embedding (qJ 0)).2 0) := by
    apply eq_slotElem01_of_peirce
    · rw [← hq_diag 0, ← Q1.preserves_product _ _ _ quat3_rel_j0_d0, map_smul]
    · rw [← hq_diag 1, ← Q1.preserves_product _ _ _ quat3_rel_j0_d1, map_smul]
  let v := (Q1.embedding (qJ 0)).2 0
  have hv_re : octonionReal v = 0 := by
    have h := Q1.preserves_product (qReal 0) (qJ 0) 0 quat3_rel_r0_j0
    rw [map_zero, hq_r0] at h
    conv_rhs at h => rw [hj0_slot]
    have h0 := congrArg (fun a : Albert => a.1 0) h
    simp only [albert_zero_fst, jordanMul_diag_0, slotElem01_fst, slotElem01_snd_0,
      slotElem01_snd_1, octDot_zero_left, add_zero, zero_mul] at h0
    simpa [octOne, octDot_scalar_left] using h0.symm
  have hv_dotI : octDot octI v = 0 := by
    have h := Q1.preserves_product (qI 0) (qJ 0) 0 quat3_rel_i0_j0
    rw [map_zero, hq_i0] at h
    conv_rhs at h => rw [hj0_slot]
    have h0 := congrArg (fun a : Albert => a.1 0) h
    simp only [albert_zero_fst, jordanMul_diag_0, slotElem01_fst, slotElem01_snd_0,
      slotElem01_snd_1, octDot_zero_left, zero_add, add_zero, zero_mul] at h0
    exact h0.symm
  have hv_ns : octNormSq v = 1 := by
    have h := Q1.preserves_product (qJ 0) (qJ 0) (qDiag 0 + qDiag 1) quat3_rel_j0_sq
    rw [map_add, hq_diag 0, hq_diag 1] at h
    conv_rhs at h => rw [hj0_slot, jordanMul_slotElem01_self]
    have h0 := congrArg (fun a : Albert => a.1 0) h
    simpa [albert_add_fst, albert_smul_fst, diagAtom_fst] using h0.symm
  obtain ⟨β, hβI, c0, c1, c2, hc2_nn, hβv⟩ := exists_octAuto_fix_I_to_IJ v
  have hc0 : c0 = 0 := by
    have hre := congrArg octonionReal hβv
    rw [β.map_real, hv_re, octonionReal_add, octonionReal_add, octonionReal_smul,
      octonionReal_smul, octonionReal_smul] at hre
    simp only [octOne, octI, octJ, octonionReal, octonionScalar] at hre
    linarith
  have hc1 : c1 = 0 := by
    have hdot : octDot octI (β.equiv v) = octDot octI v := by
      conv_lhs => rw [← hβI, β.map_dot]
    rw [hv_dotI, hβv, hc0, zero_smul, zero_add, octDot_add_right, octDot_smul_right,
      octDot_smul_right] at hdot
    have hii : octDot octI octI = 1 := by rw [octDot_eq_coords]; simp [octI]
    have hij : octDot octI octJ = 0 := by rw [octDot_eq_coords]; simp [octI, octJ]
    rw [hii, hij] at hdot
    linarith
  have hc2 : c2 = 1 := by
    have hns : octNormSq (β.equiv v) = octNormSq v := β.map_normSq v
    rw [hv_ns, hβv, hc0, hc1, zero_smul, zero_smul, zero_add, zero_add, octNormSq_smul,
      show octNormSq octJ = 1 from by rw [octNormSq_eq_coords]; simp [octJ], mul_one] at hns
    nlinarith
  have hβv_J : β.equiv v = octJ := by
    rw [hβv, hc0, hc1, hc2, zero_smul, zero_smul, zero_add, zero_add, one_smul]
  let g1 := octAutoToAlbertAuto β
  let Q2 := Q1.transport g1
  have hq2_diag : ∀ i, Q2.embedding (qDiag i) = diagAtom i := fun i => by
    change g1.linearEquiv (Q1.embedding (qDiag i)) = diagAtom i
    rw [hq_diag i, octAutoToAlbertAuto_diagAtom]
  have hq2_r0 : Q2.embedding (qReal 0) = slotElem01 octOne := by
    change g1.linearEquiv (Q1.embedding (qReal 0)) = slotElem01 octOne
    rw [hq_r0, octAutoToAlbertAuto_slotElem01, β.map_one]
  have hq2_r1 : Q2.embedding (qReal 1) = slotElem02 octOne := by
    change g1.linearEquiv (Q1.embedding (qReal 1)) = slotElem02 octOne
    rw [hq_r1, octAutoToAlbertAuto_slotElem02, β.map_one]
  have hq2_r2 : Q2.embedding (qReal 2) = slotElem12 octOne := by
    change g1.linearEquiv (Q1.embedding (qReal 2)) = slotElem12 octOne
    rw [hq_r2, octAutoToAlbertAuto_slotElem12, β.map_one]
  have hq2_i0 : Q2.embedding (qI 0) = slotElem01 octI := by
    change g1.linearEquiv (Q1.embedding (qI 0)) = slotElem01 octI
    rw [hq_i0, octAutoToAlbertAuto_slotElem01, hβI]
  have hq2_i1 : Q2.embedding (qI 1) = slotElem02 octI := by
    change g1.linearEquiv (Q1.embedding (qI 1)) = slotElem02 octI
    rw [hq_i1, octAutoToAlbertAuto_slotElem02, hβI]
  have hq2_i2 : Q2.embedding (qI 2) = slotElem12 octI := by
    change g1.linearEquiv (Q1.embedding (qI 2)) = slotElem12 octI
    rw [hq_i2, octAutoToAlbertAuto_slotElem12, hβI]
  have hq2_j0 : Q2.embedding (qJ 0) = slotElem01 octJ := by
    change g1.linearEquiv (Q1.embedding (qJ 0)) = slotElem01 octJ
    rw [hj0_slot, octAutoToAlbertAuto_slotElem01, hβv_J]
  have hq2_j1 : Q2.embedding (qJ 1) = slotElem02 octJ := by
    have h := Q2.preserves_product (qJ 0) (qReal 2) ((1 / 2 : ℝ) • qJ 1) quat3_rel_j0_r2
    rw [map_smul, hq2_j0, hq2_r2, jordanMul_slotElem01_slotElem12, octonionMul_one_right] at h
    exact half_smul_inj h
  have hq2_j2 : Q2.embedding (qJ 2) = slotElem12 octJ := by
    have h := Q2.preserves_product (qReal 0) (qJ 1) ((1 / 2 : ℝ) • qJ 2) quat3_rel_r0_j1
    rw [map_smul, hq2_r0, hq2_j1, jordanMul_slotElem01_slotElem02, octonionConj_one,
      octonionMul_one_left] at h
    exact half_smul_inj h
  have hq2_k1 : Q2.embedding (qK 1) = slotElem02 octK := by
    have h := Q2.preserves_product (qI 0) (qJ 2) ((1 / 2 : ℝ) • qK 1) quat3_rel_i0_j2
    rw [map_smul, hq2_i0, hq2_j2, jordanMul_slotElem01_slotElem12, octK_eq_mul] at h
    exact half_smul_inj h
  have hq2_k2 : Q2.embedding (qK 2) = slotElem12 octK := by
    have h := Q2.preserves_product (qReal 0) (qK 1) ((1 / 2 : ℝ) • qK 2) quat3_rel_r0_k1
    rw [map_smul, hq2_r0, hq2_k1, jordanMul_slotElem01_slotElem02, octonionConj_one,
      octonionMul_one_left] at h
    exact half_smul_inj h
  have hq2_k0 : Q2.embedding (qK 0) = slotElem01 octK := by
    have h := Q2.preserves_product (qK 1) (qReal 2) ((1 / 2 : ℝ) • qK 0) quat3_rel_k1_r2
    rw [map_smul, hq2_k1, hq2_r2, jordanMul_slotElem02_slotElem12, octonionConj_one,
      octonionMul_one_right] at h
    exact half_smul_inj h
  have hs_diag : ∀ k, standardQuaternionicWindow.embedding (qDiag k) = diagAtom k := fun k => by
    apply albert_ext <;> fin_cases k <;> simp [standardQuaternionicWindow,
      quaternionicWindowOfQuatEmbedding, quatMatrixToAlbert, qDiag, complexHermToQuatHerm,
      hDiag, hermitian3Equiv, diagAtom_fst, diagAtom_snd] <;> rfl
  have hs_r0 : standardQuaternionicWindow.embedding (qReal 0) = slotElem01 octOne := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qReal, complexHermToQuatHerm, hReal, hermitian3Equiv,
      quatEmbed1_apply] <;> rfl
  have hs_r1 : standardQuaternionicWindow.embedding (qReal 1) = slotElem02 octOne := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qReal, complexHermToQuatHerm, hReal, hermitian3Equiv,
      quatEmbed1_apply] <;> rfl
  have hs_r2 : standardQuaternionicWindow.embedding (qReal 2) = slotElem12 octOne := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qReal, complexHermToQuatHerm, hReal, hermitian3Equiv,
      quatEmbed1_apply] <;> rfl
  have hs_i0 : standardQuaternionicWindow.embedding (qI 0) = slotElem01 octI := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qI, complexHermToQuatHerm, hImag, hermitian3Equiv,
      quatEmbed1_apply] <;> rfl
  have hs_i1 : standardQuaternionicWindow.embedding (qI 1) = slotElem02 octI := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qI, complexHermToQuatHerm, hImag, hermitian3Equiv,
      quatEmbed1_apply] <;> rfl
  have hs_i2 : standardQuaternionicWindow.embedding (qI 2) = slotElem12 octI := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qI, complexHermToQuatHerm, hImag, hermitian3Equiv,
      quatEmbed1_apply] <;> rfl
  have hs_j0 : standardQuaternionicWindow.embedding (qJ 0) = slotElem01 octJ := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qJ, quatHermitian3Equiv, quatEmbed1_apply] <;> rfl
  have hs_j1 : standardQuaternionicWindow.embedding (qJ 1) = slotElem02 octJ := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qJ, quatHermitian3Equiv, quatEmbed1_apply] <;> rfl
  have hs_j2 : standardQuaternionicWindow.embedding (qJ 2) = slotElem12 octJ := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qJ, quatHermitian3Equiv, quatEmbed1_apply] <;> rfl
  have hs_k0 : standardQuaternionicWindow.embedding (qK 0) = slotElem01 octK := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qK, quatHermitian3Equiv, quatEmbed1_apply] <;> rfl
  have hs_k1 : standardQuaternionicWindow.embedding (qK 1) = slotElem02 octK := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qK, quatHermitian3Equiv, quatEmbed1_apply] <;> rfl
  have hs_k2 : standardQuaternionicWindow.embedding (qK 2) = slotElem12 octK := by
    apply albert_ext <;> simp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding,
      quatMatrixToAlbert, qK, quatHermitian3Equiv, quatEmbed1_apply] <;> rfl
  refine ⟨g1.comp g0, fun M => ?_⟩
  conv_lhs => rw [quatHermitian3_span M]
  conv_rhs => rw [quatHermitian3_span M]
  simp only [map_add, map_smul]
  change ((M : QuatMatrix3) 0 0).re • Q2.embedding (qDiag 0) +
    ((M : QuatMatrix3) 1 1).re • Q2.embedding (qDiag 1) +
    ((M : QuatMatrix3) 2 2).re • Q2.embedding (qDiag 2) +
    ((M : QuatMatrix3) 0 1).re • Q2.embedding (qReal 0) +
    ((M : QuatMatrix3) 0 1).imI • Q2.embedding (qI 0) +
    ((M : QuatMatrix3) 0 1).imJ • Q2.embedding (qJ 0) +
    ((M : QuatMatrix3) 0 1).imK • Q2.embedding (qK 0) +
    ((M : QuatMatrix3) 0 2).re • Q2.embedding (qReal 1) +
    ((M : QuatMatrix3) 0 2).imI • Q2.embedding (qI 1) +
    ((M : QuatMatrix3) 0 2).imJ • Q2.embedding (qJ 1) +
    ((M : QuatMatrix3) 0 2).imK • Q2.embedding (qK 1) +
    ((M : QuatMatrix3) 1 2).re • Q2.embedding (qReal 2) +
    ((M : QuatMatrix3) 1 2).imI • Q2.embedding (qI 2) +
    ((M : QuatMatrix3) 1 2).imJ • Q2.embedding (qJ 2) +
    ((M : QuatMatrix3) 1 2).imK • Q2.embedding (qK 2) = _
  rw [hq2_diag 0, hq2_diag 1, hq2_diag 2, hq2_r0, hq2_i0, hq2_j0, hq2_k0,
    hq2_r1, hq2_i1, hq2_j1, hq2_k1, hq2_r2, hq2_i2, hq2_j2, hq2_k2,
    hs_diag 0, hs_diag 1, hs_diag 2, hs_r0, hs_i0, hs_j0, hs_k0,
    hs_r1, hs_i1, hs_j1, hs_k1, hs_r2, hs_i2, hs_j2, hs_k2]

end WindowBasis

theorem quaternionicWindow_conjugate_standard (hB : AtomAndRankOneBridge)
    (Q : QuaternionicWindow) :
    ∃ g : NativeAlbertAutomorphism, ∀ x,
      x ∈ Q.subalgebra.carrier ↔ g.linearEquiv x ∈ standardQuaternionicWindow.subalgebra.carrier := by
  obtain ⟨g, hg⟩ := quaternionicWindow_conjugate_standard_embedding hB Q
  refine ⟨g, fun x => ?_⟩
  rw [← Q.range_eq, ← standardQuaternionicWindow.range_eq]
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨M, (hg M).symm⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, g.linearEquiv.injective ?_⟩
    rw [hg M, hM]

theorem support_of_atom_zero_pairing (hB : AtomAndRankOneBridge) {p x : Albert}
    (hp : IsAtom p) (hx : IsPositive x) (hpx : tracePairing p x = 0) :
    jordanMul p x = 0 ∧ quadraticMap p x = 0 ∧ quadraticMap (albertUnit - p) x = x := by
  obtain ⟨g, hg⟩ := hB.atom_to_diagAtom0 p hp
  obtain ⟨y, hy⟩ := hx
  let z := g.linearEquiv y
  have hgx : g.linearEquiv x = jordanMul z z := by
    rw [hy, g.preserves_product]
  have htr : tracePairing (diagAtom 0) (jordanMul z z) = 0 := by
    rw [← hg, ← hgx, g.map_tracePairing, hpx]
  rw [tracePairing_diagAtom, jordanMul_diag_0, octDot_self, octDot_self] at htr
  have hz0 : z.1 0 = 0 := by
    nlinarith [sq_nonneg (z.1 0), octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1)]
  have hz01 : z.2 0 = 0 := (octNormSq_eq_zero _).mp (by
    nlinarith [sq_nonneg (z.1 0), octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1)])
  have hz02 : z.2 1 = 0 := (octNormSq_eq_zero _).mp (by
    nlinarith [sq_nonneg (z.1 0), octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1)])
  have hjz : jordanMul (diagAtom 0) (jordanMul z z) = 0 := by
    rw [jordanMul_diagAtom0]
    apply albert_ext
    · simp [jordanMul_diag_0, hz0, hz01, hz02, octDot_zero_left, albert_zero_fst]
    · simp [albert_zero_fst]
    · simp [albert_zero_fst]
    · simp [jordanMul_off_0, hz0, hz01, hz02, octonionMul_zero_left, albert_zero_snd]
    · simp [jordanMul_off_1, hz0, hz01, hz02, octonionMul_zero_left, albert_zero_snd]
    · simp [albert_zero_snd]
  have hj : jordanMul p x = 0 := by
    apply g.linearEquiv.injective
    rw [g.preserves_product, hg, hgx, hjz, map_zero]
  have hq : quadraticMap p x = 0 := by
    unfold quadraticMap
    rw [hj, jordanMul_zero_right, hp.1, hj, smul_zero, sub_zero]
  have hqc : quadraticMap (albertUnit - p) x = x := by
    unfold quadraticMap
    have hsq : jordanMul (albertUnit - p) (albertUnit - p) = albertUnit - p := by
      simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
        jordanMul_albertUnit_right, hp.1]
      abel
    simp only [hsq, jordanMul_sub_left, jordanMul_albertUnit_left, hj, sub_zero, two_smul]
    abel
  exact ⟨hj, hq, hqc⟩

theorem support_of_corankOne_zero_pairing (hB : AtomAndRankOneBridge) {q x : Albert}
    (hq : IsAtom q) (hx : IsPositive x) (hqx : tracePairing (albertUnit - q) x = 0) :
    jordanMul (albertUnit - q) x = 0 ∧ quadraticMap (albertUnit - q) x = 0 ∧
      quadraticMap q x = x := by
  obtain ⟨g, hg⟩ := hB.atom_to_diagAtom0 q hq
  obtain ⟨y, hy⟩ := hx
  let z := g.linearEquiv y
  have hgx : g.linearEquiv x = jordanMul z z := by rw [hy, g.preserves_product]
  have htr : tracePairing (diagAtom 1 + diagAtom 2) (jordanMul z z) = 0 := by
    have heq : albertUnit - diagAtom 0 = diagAtom 1 + diagAtom 2 := by
      have hds := diagAtom_sum_eq_unit
      rw [Fin.sum_univ_three] at hds
      rw [← hds]
      abel
    rw [← heq, ← hg, ← g.preserves_unit, ← map_sub, ← hgx, g.map_tracePairing, hqx]
  rw [tracePairing_add_left, tracePairing_diagAtom, tracePairing_diagAtom,
    jordanMul_diag_1, jordanMul_diag_2] at htr
  simp only [octDot_self] at htr
  have hnn : 0 ≤ (z.1 1) ^ 2 + octNormSq (z.2 0) + octNormSq (z.2 2) +
      ((z.1 2) ^ 2 + octNormSq (z.2 1) + octNormSq (z.2 2)) := by
    nlinarith [sq_nonneg (z.1 1), sq_nonneg (z.1 2), octNormSq_nonneg (z.2 0),
      octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)]
  have hz1 : z.1 1 = 0 := by nlinarith [sq_nonneg (z.1 1), sq_nonneg (z.1 2), octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)]
  have hz2 : z.1 2 = 0 := by nlinarith [sq_nonneg (z.1 1), sq_nonneg (z.1 2), octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)]
  have hz01 : z.2 0 = 0 := (octNormSq_eq_zero _).mp (by nlinarith [sq_nonneg (z.1 1), sq_nonneg (z.1 2), octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)])
  have hz02 : z.2 1 = 0 := (octNormSq_eq_zero _).mp (by nlinarith [sq_nonneg (z.1 1), sq_nonneg (z.1 2), octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)])
  have hz12 : z.2 2 = 0 := (octNormSq_eq_zero _).mp (by nlinarith [sq_nonneg (z.1 1), sq_nonneg (z.1 2), octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)])
  have hzz : jordanMul z z = (z.1 0) ^ 2 • diagAtom 0 := by
    apply albert_ext
    · simp [jordanMul_diag_0, hz01, hz02, octDot_zero_left, albert_smul_fst, diagAtom_fst]; ring
    · simp [jordanMul_diag_1, hz1, hz01, hz12, octDot_zero_left, albert_smul_fst, diagAtom_fst]
    · simp [jordanMul_diag_2, hz2, hz02, hz12, octDot_zero_left, albert_smul_fst, diagAtom_fst]
    · simp [jordanMul_off_0, hz01, hz02, hz12, octonionMul_zero_left, albert_smul_snd, diagAtom_snd]
    · simp [jordanMul_off_1, hz01, hz02, hz12, octonionMul_zero_left, albert_smul_snd, diagAtom_snd]
    · simp [jordanMul_off_2, hz01, hz02, hz12, octonionConj_zero, octonionMul_zero_left,
        albert_smul_snd, diagAtom_snd]
  have hx_eq : x = (z.1 0) ^ 2 • q := by
    apply g.linearEquiv.injective
    rw [hgx, hzz, map_smul, hg]
  rw [hx_eq]
  have hqmul : jordanMul (albertUnit - q) q = 0 := by
    rw [jordanMul_sub_left, jordanMul_albertUnit_left, hq.1, sub_self]
  refine ⟨?_, ?_, ?_⟩
  · rw [jordanMul_smul_right, hqmul, smul_zero]
  · rw [quadraticMap_smul_right, show quadraticMap (albertUnit - q) q = 0 from by
      unfold quadraticMap
      have hsq : jordanMul (albertUnit - q) (albertUnit - q) = albertUnit - q := by
        simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
          jordanMul_albertUnit_right, hq.1]
        abel
      rw [hsq, hqmul, jordanMul_zero_right, smul_zero, sub_zero], smul_zero]
  · rw [quadraticMap_smul_right, show quadraticMap q q = q from by
      unfold quadraticMap; rw [hq.1, hq.1, two_smul]; abel]

end AlbertSequential

