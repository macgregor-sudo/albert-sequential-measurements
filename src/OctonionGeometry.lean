/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Defs
public import NativeAlbertLaws
public import FixedSBinding
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Octonion Geometry, Harvey–Lawson, `Aut(O)`, and Artin/Subalgebra Classification

Formalizes:
1. Octonion imaginary projection `octIm`, norm squared `octNormSq`, cross product `octCross`,
   and associator `octAssociator`, with trilinearity, alternating laws, and all Moufang identities
   proved conceptually from alternativity and the Teichmüller identity.
2. The Harvey–Lawson identity (`eq:A:HL`) proved via Gram–Schmidt reduction and left Moufang.
3. `OctonionAutomorphism` (`Aut(O)`), automatic preservation of `octonionReal`, `octonionConj`,
   `octDot`, and `octNormSq`, the Basic-Triple theorem `octAutoOfBasicTriple`, and explicit
   orbit normalizers `(i)`–`(iii)` plus `conjIAutomorphism`.
4. Artin's theorem / quaternionic containment (`exists_quatEmbedding_containing_pair`) and the
   complete `{1, 2, 4, 8}` dimension classification of conjugation-closed unital subalgebras `OctSubalgebra`.

No `Mul`, `One`, `Star`, or `Norm` instance is installed on `Octonion` or `Albert`.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

/-! ## Section 1: Octonion Basics, Norms, Imaginary Projection, Cross Product -/

def octOne : Octonion := octonionScalar 1

def octIm (x : Octonion) : Octonion := x - octonionScalar (octonionReal x)

def octNormSq (x : Octonion) : ℝ := octDot x x

def octCross (u v : Octonion) : Octonion :=
  (1 / 2 : ℝ) • (octonionMul u v - octonionMul v u)

def octAssociator (x y z : Octonion) : Octonion :=
  octonionMul (octonionMul x y) z - octonionMul x (octonionMul y z)

private theorem oct_ext {x y : Octonion}
    (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
    (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK)
    (h5 : x.2.re = y.2.re) (h6 : x.2.imI = y.2.imI)
    (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

private theorem q_re_add (p q : Quaternion ℝ) : (p + q).re = p.re + q.re := rfl
private theorem q_imI_add (p q : Quaternion ℝ) : (p + q).imI = p.imI + q.imI := rfl
private theorem q_imJ_add (p q : Quaternion ℝ) : (p + q).imJ = p.imJ + q.imJ := rfl
private theorem q_imK_add (p q : Quaternion ℝ) : (p + q).imK = p.imK + q.imK := rfl
private theorem q_re_neg (p : Quaternion ℝ) : (-p).re = -p.re := rfl
private theorem q_imI_neg (p : Quaternion ℝ) : (-p).imI = -p.imI := rfl
private theorem q_imJ_neg (p : Quaternion ℝ) : (-p).imJ = -p.imJ := rfl
private theorem q_imK_neg (p : Quaternion ℝ) : (-p).imK = -p.imK := rfl
private theorem q_re_sub (p q : Quaternion ℝ) : (p - q).re = p.re - q.re := by
  rw [sub_eq_add_neg]; rfl
private theorem q_imI_sub (p q : Quaternion ℝ) : (p - q).imI = p.imI - q.imI := by
  rw [sub_eq_add_neg]; rfl
private theorem q_imJ_sub (p q : Quaternion ℝ) : (p - q).imJ = p.imJ - q.imJ := by
  rw [sub_eq_add_neg]; rfl
private theorem q_imK_sub (p q : Quaternion ℝ) : (p - q).imK = p.imK - q.imK := by
  rw [sub_eq_add_neg]; rfl
private theorem q_re_smul (r : ℝ) (p : Quaternion ℝ) : (r • p).re = r * p.re := rfl
private theorem q_imI_smul (r : ℝ) (p : Quaternion ℝ) : (r • p).imI = r * p.imI := rfl
private theorem q_imJ_smul (r : ℝ) (p : Quaternion ℝ) : (r • p).imJ = r * p.imJ := rfl
private theorem q_imK_smul (r : ℝ) (p : Quaternion ℝ) : (r • p).imK = r * p.imK := rfl
private theorem q_re_star (p : Quaternion ℝ) : (star p).re = p.re := by simp
private theorem q_imI_star (p : Quaternion ℝ) : (star p).imI = -p.imI := by simp
private theorem q_imJ_star (p : Quaternion ℝ) : (star p).imJ = -p.imJ := by simp
private theorem q_imK_star (p : Quaternion ℝ) : (star p).imK = -p.imK := by simp
private theorem q_re_zero : (0 : Quaternion ℝ).re = 0 := rfl
private theorem q_imI_zero : (0 : Quaternion ℝ).imI = 0 := rfl
private theorem q_imJ_zero : (0 : Quaternion ℝ).imJ = 0 := rfl
private theorem q_imK_zero : (0 : Quaternion ℝ).imK = 0 := rfl

private theorem oct_fst_add (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem oct_snd_add (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem oct_fst_sub (x y : Octonion) : (x - y).1 = x.1 - y.1 := rfl
private theorem oct_snd_sub (x y : Octonion) : (x - y).2 = x.2 - y.2 := rfl
private theorem oct_fst_neg (x : Octonion) : (-x).1 = -x.1 := rfl
private theorem oct_snd_neg (x : Octonion) : (-x).2 = -x.2 := rfl
private theorem oct_fst_smul (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem oct_snd_smul (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl
private theorem oct_fst_zero : (0 : Octonion).1 = 0 := rfl
private theorem oct_snd_zero : (0 : Octonion).2 = 0 := rfl

private theorem octonionScalar_sub (r s : ℝ) :
    octonionScalar (r - s) = octonionScalar r - octonionScalar s := by
  rw [octonionScalar_eq_smul (r - s), octonionScalar_eq_smul r, octonionScalar_eq_smul s, sub_smul]

theorem octonionMul_neg_left (x y : Octonion) :
    octonionMul (-x) y = -octonionMul x y := by
  rw [← neg_one_smul ℝ x, octonionMul_smul_left, neg_one_smul]

theorem octonionMul_neg_right (x y : Octonion) :
    octonionMul x (-y) = -octonionMul x y := by
  rw [← neg_one_smul ℝ y, octonionMul_smul_right, neg_one_smul]

theorem octonionMul_sub_left (x y z : Octonion) :
    octonionMul (x - y) z = octonionMul x z - octonionMul y z := by
  rw [sub_eq_add_neg, octonionMul_add_left, octonionMul_neg_left, ← sub_eq_add_neg]

theorem octonionMul_sub_right (x y z : Octonion) :
    octonionMul x (y - z) = octonionMul x y - octonionMul x z := by
  rw [sub_eq_add_neg, octonionMul_add_right, octonionMul_neg_right, ← sub_eq_add_neg]

theorem octonionReal_sub (x y : Octonion) :
    octonionReal (x - y) = octonionReal x - octonionReal y := rfl

theorem octDot_neg_left (x y : Octonion) : octDot (-x) y = -octDot x y := by
  rw [← neg_one_smul ℝ x, octDot_smul_left]; ring

theorem octDot_neg_right (x y : Octonion) : octDot x (-y) = -octDot x y := by
  rw [octDot_comm, octDot_neg_left, octDot_comm]

theorem octDot_sub_left (x y z : Octonion) :
    octDot (x - y) z = octDot x z - octDot y z := by
  rw [sub_eq_add_neg, octDot_add_left, octDot_neg_left, ← sub_eq_add_neg]

theorem octDot_sub_right (x y z : Octonion) :
    octDot x (y - z) = octDot x y - octDot x z := by
  rw [octDot_comm, octDot_sub_left, octDot_comm x y, octDot_comm x z]

theorem octK_eq_mul : octonionMul octI octJ = octK := by
  apply oct_ext <;> simp [octonionMul, octI, octJ, octK]

theorem octOne_eq_scalar : octOne = octonionScalar 1 := rfl

theorem octonionMul_one_left (x : Octonion) : octonionMul octOne x = x :=
  octonionMul_scalar_one_left x

theorem octonionMul_one_right (x : Octonion) : octonionMul x octOne = x :=
  octonionMul_scalar_one_right x

theorem octonionReal_one : octonionReal octOne = 1 := rfl

theorem octonionConj_one : octonionConj octOne = octOne :=
  octonionConj_scalar 1

theorem octNormSq_eq_coords (x : Octonion) :
    octNormSq x =
      x.1.re ^ 2 + x.1.imI ^ 2 + x.1.imJ ^ 2 + x.1.imK ^ 2 +
      x.2.re ^ 2 + x.2.imI ^ 2 + x.2.imJ ^ 2 + x.2.imK ^ 2 := by
  unfold octNormSq
  rw [octDot_eq_coords]
  ring

theorem octDot_self (x : Octonion) : octDot x x = octNormSq x := rfl

theorem octNormSq_nonneg (x : Octonion) : 0 ≤ octNormSq x := by
  rw [octNormSq_eq_coords]
  positivity

theorem octNormSq_eq_zero (x : Octonion) : octNormSq x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [octNormSq_eq_coords] at h
    rw [show (0 : Octonion) = (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩) from rfl]
    apply oct_ext <;> dsimp <;> nlinarith [sq_nonneg x.1.re, sq_nonneg x.1.imI, sq_nonneg x.1.imJ,
      sq_nonneg x.1.imK, sq_nonneg x.2.re, sq_nonneg x.2.imI, sq_nonneg x.2.imJ, sq_nonneg x.2.imK]
  · rintro rfl
    rw [octNormSq_eq_coords]
    change (0 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = 0
    norm_num

theorem octNormSq_conj (x : Octonion) : octNormSq (octonionConj x) = octNormSq x := by
  rw [octNormSq_eq_coords, octNormSq_eq_coords]
  unfold octonionConj
  dsimp only
  rw [q_re_star, q_imI_star, q_imJ_star, q_imK_star,
    q_re_neg, q_imI_neg, q_imJ_neg, q_imK_neg]
  ring

theorem octNormSq_neg (x : Octonion) : octNormSq (-x) = octNormSq x := by
  rw [octNormSq_eq_coords, octNormSq_eq_coords]
  change (-x.1.re) ^ 2 + (-x.1.imI) ^ 2 + (-x.1.imJ) ^ 2 + (-x.1.imK) ^ 2 +
      (-x.2.re) ^ 2 + (-x.2.imI) ^ 2 + (-x.2.imJ) ^ 2 + (-x.2.imK) ^ 2 =
    x.1.re ^ 2 + x.1.imI ^ 2 + x.1.imJ ^ 2 + x.1.imK ^ 2 +
      x.2.re ^ 2 + x.2.imI ^ 2 + x.2.imJ ^ 2 + x.2.imK ^ 2
  ring

theorem octNormSq_smul (r : ℝ) (x : Octonion) : octNormSq (r • x) = r ^ 2 * octNormSq x := by
  unfold octNormSq
  rw [octDot_smul_left, octDot_smul_right]
  ring

theorem octNormSq_add (x y : Octonion) :
    octNormSq (x + y) = octNormSq x + octNormSq y + 2 * octDot x y := by
  unfold octNormSq
  rw [octDot_add_left, octDot_add_right, octDot_add_right, octDot_comm y x]
  ring

theorem octNormSq_sub (x y : Octonion) :
    octNormSq (x - y) = octNormSq x + octNormSq y - 2 * octDot x y := by
  rw [sub_eq_add_neg, octNormSq_add, octNormSq_neg, octDot_neg_right]
  ring

theorem octNormSq_one : octNormSq octOne = 1 := by
  rw [octNormSq_eq_coords]
  change (1 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
  norm_num

theorem octDot_ext {x y : Octonion} (h : ∀ z, octDot x z = octDot y z) : x = y := by
  have hz : octNormSq (x - y) = 0 := by
    unfold octNormSq
    rw [octDot_sub_left, h (x - y), sub_self]
  exact sub_eq_zero.mp ((octNormSq_eq_zero (x - y)).mp hz)

theorem octNormSq_mul (x y : Octonion) :
    octNormSq (octonionMul x y) = octNormSq x * octNormSq y := by
  rw [octNormSq_eq_coords, octNormSq_eq_coords, octNormSq_eq_coords]
  simp [octonionMul]
  ring

theorem octMul_self_conj (x : Octonion) :
    octonionMul x (octonionConj x) = octonionScalar (octNormSq x) := by
  rw [octNormSq_eq_coords]
  apply oct_ext <;> simp [octonionMul, octonionConj, octonionScalar] <;> ring

theorem octMul_conj_self (x : Octonion) :
    octonionMul (octonionConj x) x = octonionScalar (octNormSq x) := by
  simpa only [octonionConj_conj, octNormSq_conj] using octMul_self_conj (octonionConj x)

theorem octConj_eq_two_real_sub (x : Octonion) :
    octonionConj x = (2 * octonionReal x) • octOne - x := by
  apply oct_ext
  · rw [oct_fst_sub, oct_fst_smul, q_re_sub, q_re_smul]
    change (star x.1).re = (2 * x.1.re) * 1 - x.1.re
    rw [q_re_star]; ring
  · rw [oct_fst_sub, oct_fst_smul, q_imI_sub, q_imI_smul]
    change (star x.1).imI = (2 * x.1.re) * 0 - x.1.imI
    rw [q_imI_star]; ring
  · rw [oct_fst_sub, oct_fst_smul, q_imJ_sub, q_imJ_smul]
    change (star x.1).imJ = (2 * x.1.re) * 0 - x.1.imJ
    rw [q_imJ_star]; ring
  · rw [oct_fst_sub, oct_fst_smul, q_imK_sub, q_imK_smul]
    change (star x.1).imK = (2 * x.1.re) * 0 - x.1.imK
    rw [q_imK_star]; ring
  · rw [oct_snd_sub, oct_snd_smul, q_re_sub, q_re_smul]
    change (-x.2).re = (2 * x.1.re) * 0 - x.2.re
    rw [q_re_neg]; ring
  · rw [oct_snd_sub, oct_snd_smul, q_imI_sub, q_imI_smul]
    change (-x.2).imI = (2 * x.1.re) * 0 - x.2.imI
    rw [q_imI_neg]; ring
  · rw [oct_snd_sub, oct_snd_smul, q_imJ_sub, q_imJ_smul]
    change (-x.2).imJ = (2 * x.1.re) * 0 - x.2.imJ
    rw [q_imJ_neg]; ring
  · rw [oct_snd_sub, oct_snd_smul, q_imK_sub, q_imK_smul]
    change (-x.2).imK = (2 * x.1.re) * 0 - x.2.imK
    rw [q_imK_neg]; ring

theorem octAdd_conj (x : Octonion) :
    x + octonionConj x = (2 : ℝ) • octonionScalar (octonionReal x) := by
  rw [octConj_eq_two_real_sub, octOne_eq_scalar, mul_smul, ← octonionScalar_eq_smul]
  module

theorem octSub_conj (x : Octonion) :
    x - octonionConj x = (2 : ℝ) • octIm x := by
  rw [octConj_eq_two_real_sub, octIm, octOne_eq_scalar, mul_smul, ← octonionScalar_eq_smul]
  module

private theorem quaternion_real_triple_cyclic (a b c : Quaternion ℝ) :
    (a * (b * c)).re = (b * (c * a)).re := by
  have hc : ∀ p q : Quaternion ℝ, (p * q).re = (q * p).re := fun p q => by
    rw [Quaternion.re_mul, Quaternion.re_mul]; ring
  rw [hc a (b * c), mul_assoc]

theorem octonionReal_mul_associative (x y z : Octonion) :
    octonionReal (octonionMul (octonionMul x y) z) =
      octonionReal (octonionMul x (octonionMul y z)) := by
  change ((x.1 * y.1 - star y.2 * x.2) * z.1 -
      star z.2 * (y.2 * x.1 + x.2 * star y.1)).re =
    (x.1 * (y.1 * z.1 - star z.2 * y.2) -
      star (z.2 * y.1 + y.2 * star z.1) * x.2).re
  simp only [sub_mul, mul_sub, mul_add, add_mul, star_add, star_mul, star_star,
    Quaternion.re_add, Quaternion.re_sub, mul_assoc]
  rw [← quaternion_real_triple_cyclic z.1 (star y.2) x.2,
    ← quaternion_real_triple_cyclic x.1 (star z.2) y.2,
    ← quaternion_real_triple_cyclic (star y.1) (star z.2) x.2]
  ring

theorem octDot_mul_left (x y z : Octonion) :
    octDot (octonionMul x y) z = octDot y (octonionMul (octonionConj x) z) := by
  unfold octDot
  calc
    octonionReal (octonionMul (octonionMul x y) (octonionConj z))
        = octonionReal (octonionMul x (octonionMul y (octonionConj z))) :=
          octonionReal_mul_associative x y (octonionConj z)
    _ = octonionReal (octonionMul (octonionMul y (octonionConj z)) x) :=
          octonionReal_mul_comm _ _
    _ = octonionReal (octonionMul y (octonionMul (octonionConj z) x)) :=
          octonionReal_mul_associative y (octonionConj z) x
    _ = octonionReal (octonionMul y (octonionConj (octonionMul (octonionConj x) z))) := by
          rw [octonionConj_mul, octonionConj_conj]

theorem octDot_mul_right (x y z : Octonion) :
    octDot (octonionMul x y) z = octDot x (octonionMul z (octonionConj y)) := by
  unfold octDot
  rw [octonionReal_mul_associative, octonionConj_mul, octonionConj_conj]

theorem octonionReal_octIm (x : Octonion) : octonionReal (octIm x) = 0 := by
  simp [octIm, octonionReal_sub, octonionReal_scalar]

theorem octIm_eq_self_iff (x : Octonion) : octIm x = x ↔ octonionReal x = 0 := by
  constructor
  · intro h
    have hr := congrArg octonionReal h
    simpa [octonionReal_octIm] using hr.symm
  · intro h
    simp [octIm, h, octonionScalar_zero]

theorem octConj_octIm (x : Octonion) : octonionConj (octIm x) = -octIm x := by
  rw [octConj_eq_two_real_sub, octonionReal_octIm, mul_zero, zero_smul, zero_sub]

theorem octonionConj_eq_neg_of_real_zero {u : Octonion} (hu : octonionReal u = 0) :
    octonionConj u = -u := by
  rw [← (octIm_eq_self_iff u).mpr hu, octConj_octIm]

theorem octIm_zero : octIm 0 = 0 := by
  simp [octIm, octonionReal_zero, octonionScalar_zero]

theorem octIm_add (x y : Octonion) : octIm (x + y) = octIm x + octIm y := by
  unfold octIm; rw [octonionReal_add, octonionScalar_add]; abel

theorem octIm_sub (x y : Octonion) : octIm (x - y) = octIm x - octIm y := by
  unfold octIm; rw [octonionReal_sub, octonionScalar_sub]; abel

theorem octIm_neg (x : Octonion) : octIm (-x) = -octIm x := by
  have h := octIm_sub 0 x
  simpa [octIm_zero] using h

theorem octIm_smul (r : ℝ) (x : Octonion) : octIm (r • x) = r • octIm x := by
  simp [octIm, octonionReal_smul, octonionScalar_smul, smul_sub]

theorem octIm_scalar (r : ℝ) : octIm (octonionScalar r) = 0 := by
  simp [octIm, octonionReal_scalar]

theorem oct_eq_scalar_add_octIm (x : Octonion) :
    x = octonionScalar (octonionReal x) + octIm x := by
  simp [octIm]

theorem octDot_scalar_octIm (r : ℝ) (y : Octonion) :
    octDot (octonionScalar r) (octIm y) = 0 := by
  rw [octDot_scalar_left, octonionReal_octIm, mul_zero]

theorem octDot_octIm_left (x y : Octonion) :
    octDot (octIm x) (octIm y) = octDot x (octIm y) := by
  conv_rhs => rw [oct_eq_scalar_add_octIm x]
  rw [octDot_add_left, octDot_scalar_octIm, zero_add]

theorem octDot_octIm_right (x y : Octonion) :
    octDot (octIm x) (octIm y) = octDot (octIm x) y := by
  rw [octDot_comm, octDot_octIm_left, octDot_comm]

theorem octonionReal_mul_imag_eq {u v : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) :
    octonionReal (octonionMul u v) = -octDot u v := by
  have _ := hu
  have hcv : octonionConj v = -v := octonionConj_eq_neg_of_real_zero hv
  calc
    octonionReal (octonionMul u v)
        = octonionReal (octonionMul u (-octonionConj v)) := by rw [hcv, neg_neg]
    _ = -octonionReal (octonionMul u (octonionConj v)) := by
          rw [octonionMul_neg_right, octonionReal_neg]
    _ = -octDot u v := rfl

theorem octonionMul_imag_anticomm {u v : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) :
    octonionMul u v + octonionMul v u = (-2 * octDot u v) • octOne := by
  have hcu : octonionConj u = -u := octonionConj_eq_neg_of_real_zero hu
  have hcv : octonionConj v = -v := octonionConj_eq_neg_of_real_zero hv
  have hconj : octonionConj (octonionMul u v) = octonionMul v u := by
    rw [octonionConj_mul, hcu, hcv, octonionMul_neg_left, octonionMul_neg_right, neg_neg]
  rw [← hconj, octAdd_conj, octonionReal_mul_imag_eq hu hv, octonionScalar_eq_smul,
    smul_smul, ← octOne_eq_scalar]
  congr 1; ring

theorem octonionMul_imag_sq {u : Octonion} (hu : octonionReal u = 0) :
    octonionMul u u = (-octNormSq u) • octOne := by
  have h := octonionMul_imag_anticomm hu hu
  rw [← two_smul ℝ (octonionMul u u), octDot_self] at h
  have h2 := congrArg (fun z : Octonion => (1 / 2 : ℝ) • z) h
  rw [smul_smul, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul,
    show (1 / 2 : ℝ) * (-2 * octNormSq u) = -octNormSq u by ring] at h2
  exact h2

theorem octCross_eq_octIm {u v : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) :
    octCross u v = octIm (octonionMul u v) := by
  unfold octCross octIm
  rw [octonionReal_mul_imag_eq hu hv]
  have ha := octonionMul_imag_anticomm hu hv
  have hvu : octonionMul v u = (-2 * octDot u v) • octOne - octonionMul u v :=
    eq_sub_iff_add_eq'.mpr ha
  rw [hvu, octOne_eq_scalar]
  have hs : octonionScalar (-octDot u v) = (-octDot u v) • octonionScalar 1 := by
    rw [← octonionScalar_smul, mul_one]
  rw [hs]
  module

theorem octonionMul_imag_eq {u v : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) :
    octonionMul u v = (-octDot u v) • octOne + octCross u v := by
  rw [octCross_eq_octIm hu hv, octOne_eq_scalar, ← octonionReal_mul_imag_eq hu hv,
    ← octonionScalar_smul, mul_one, ← oct_eq_scalar_add_octIm]

theorem octCross_anticomm (u v : Octonion) : octCross u v = -octCross v u := by
  unfold octCross
  rw [← neg_sub (octonionMul v u) (octonionMul u v), smul_neg]

theorem octCross_self (u : Octonion) : octCross u u = 0 := by
  unfold octCross
  rw [sub_self, smul_zero]

theorem octCross_add_left (u1 u2 v : Octonion) :
    octCross (u1 + u2) v = octCross u1 v + octCross u2 v := by
  unfold octCross
  rw [octonionMul_add_left, octonionMul_add_right, ← smul_add]
  congr 1; abel

theorem octCross_add_right (u v1 v2 : Octonion) :
    octCross u (v1 + v2) = octCross u v1 + octCross u v2 := by
  unfold octCross
  rw [octonionMul_add_right, octonionMul_add_left, ← smul_add]
  congr 1; abel

theorem octCross_smul_left (r : ℝ) (u v : Octonion) :
    octCross (r • u) v = r • octCross u v := by
  unfold octCross
  rw [octonionMul_smul_left, octonionMul_smul_right, ← smul_sub, smul_comm (1 / 2 : ℝ) r]

theorem octCross_smul_right (r : ℝ) (u v : Octonion) :
    octCross u (r • v) = r • octCross u v := by
  unfold octCross
  rw [octonionMul_smul_right, octonionMul_smul_left, ← smul_sub, smul_comm (1 / 2 : ℝ) r]

theorem octCross_sub_left (u1 u2 v : Octonion) :
    octCross (u1 - u2) v = octCross u1 v - octCross u2 v := by
  rw [sub_eq_add_neg, octCross_add_left, ← neg_one_smul ℝ u2, octCross_smul_left, neg_one_smul,
    ← sub_eq_add_neg]

theorem octCross_sub_right (u v1 v2 : Octonion) :
    octCross u (v1 - v2) = octCross u v1 - octCross u v2 := by
  rw [sub_eq_add_neg, octCross_add_right, ← neg_one_smul ℝ v2, octCross_smul_right, neg_one_smul,
    ← sub_eq_add_neg]

theorem octonionReal_octCross (u v : Octonion) : octonionReal (octCross u v) = 0 := by
  unfold octCross
  rw [octonionReal_smul, octonionReal_sub, octonionReal_mul_comm u v, sub_self, mul_zero]

theorem octDot_octCross_eq {u v w : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) (hw : octonionReal w = 0) :
    octDot (octCross u v) w = octDot (octonionMul u v) w := by
  rw [octCross_eq_octIm hu hv, ← (octIm_eq_self_iff w).mpr hw, octDot_octIm_left]

theorem octDot_octCross_left {u v : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) :
    octDot (octCross u v) u = 0 := by
  rw [octDot_octCross_eq hu hv hu, octDot_mul_left, octMul_conj_self, octDot_comm,
    octDot_scalar_left, hv, mul_zero]

theorem octDot_octCross_right {u v : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) :
    octDot (octCross u v) v = 0 := by
  rw [octCross_anticomm, octDot_neg_left, octDot_octCross_left hv hu, neg_zero]

/-! ## Section 2: Alternativity, Associator Laws, and Moufang Identities -/

theorem octMul_left_alternative (x y : Octonion) :
    octonionMul x (octonionMul x y) = octonionMul (octonionMul x x) y := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [octonionMul] <;> ring

theorem octMul_right_alternative (x y : Octonion) :
    octonionMul (octonionMul x y) y = octonionMul x (octonionMul y y) := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [octonionMul] <;> ring

theorem octAssociator_zero_left (y z : Octonion) : octAssociator 0 y z = 0 := by
  simp [octAssociator, octonionMul_zero_left]

theorem octAssociator_zero_mid (x z : Octonion) : octAssociator x 0 z = 0 := by
  simp [octAssociator, octonionMul_zero_left, octonionMul_zero_right]

theorem octAssociator_zero_right (x y : Octonion) : octAssociator x y 0 = 0 := by
  simp [octAssociator, octonionMul_zero_right]

theorem octAssociator_add_left (x1 x2 y z : Octonion) :
    octAssociator (x1 + x2) y z = octAssociator x1 y z + octAssociator x2 y z := by
  unfold octAssociator
  simp only [octonionMul_add_left]
  abel

theorem octAssociator_add_mid (x y1 y2 z : Octonion) :
    octAssociator x (y1 + y2) z = octAssociator x y1 z + octAssociator x y2 z := by
  unfold octAssociator
  simp only [octonionMul_add_left, octonionMul_add_right]
  abel

theorem octAssociator_add_right (x y z1 z2 : Octonion) :
    octAssociator x y (z1 + z2) = octAssociator x y z1 + octAssociator x y z2 := by
  unfold octAssociator
  simp only [octonionMul_add_right]
  abel

theorem octAssociator_smul_left (r : ℝ) (x y z : Octonion) :
    octAssociator (r • x) y z = r • octAssociator x y z := by
  unfold octAssociator
  simp only [octonionMul_smul_left, smul_sub]

theorem octAssociator_smul_mid (r : ℝ) (x y z : Octonion) :
    octAssociator x (r • y) z = r • octAssociator x y z := by
  unfold octAssociator
  simp only [octonionMul_smul_left, octonionMul_smul_right, smul_sub]

theorem octAssociator_smul_right (r : ℝ) (x y z : Octonion) :
    octAssociator x y (r • z) = r • octAssociator x y z := by
  unfold octAssociator
  simp only [octonionMul_smul_right, smul_sub]

theorem octAssociator_neg_left (x y z : Octonion) :
    octAssociator (-x) y z = -octAssociator x y z := by
  rw [← neg_one_smul ℝ x, octAssociator_smul_left, neg_one_smul]

theorem octAssociator_neg_mid (x y z : Octonion) :
    octAssociator x (-y) z = -octAssociator x y z := by
  rw [← neg_one_smul ℝ y, octAssociator_smul_mid, neg_one_smul]

theorem octAssociator_neg_right (x y z : Octonion) :
    octAssociator x y (-z) = -octAssociator x y z := by
  rw [← neg_one_smul ℝ z, octAssociator_smul_right, neg_one_smul]

theorem octAssociator_sub_left (x1 x2 y z : Octonion) :
    octAssociator (x1 - x2) y z = octAssociator x1 y z - octAssociator x2 y z := by
  rw [sub_eq_add_neg, octAssociator_add_left, octAssociator_neg_left, ← sub_eq_add_neg]

theorem octAssociator_sub_mid (x y1 y2 z : Octonion) :
    octAssociator x (y1 - y2) z = octAssociator x y1 z - octAssociator x y2 z := by
  rw [sub_eq_add_neg, octAssociator_add_mid, octAssociator_neg_mid, ← sub_eq_add_neg]

theorem octAssociator_sub_right (x y z1 z2 : Octonion) :
    octAssociator x y (z1 - z2) = octAssociator x y z1 - octAssociator x y z2 := by
  rw [sub_eq_add_neg, octAssociator_add_right, octAssociator_neg_right, ← sub_eq_add_neg]

theorem octAssociator_scalar_left (r : ℝ) (y z : Octonion) :
    octAssociator (octonionScalar r) y z = 0 := by
  simp [octAssociator, octonionMul_scalar_left, octonionMul_smul_left]

theorem octAssociator_scalar_mid (r : ℝ) (x z : Octonion) :
    octAssociator x (octonionScalar r) z = 0 := by
  simp [octAssociator, octonionMul_scalar_left, octonionMul_scalar_right,
    octonionMul_smul_left, octonionMul_smul_right]

theorem octAssociator_scalar_right (r : ℝ) (x y : Octonion) :
    octAssociator x y (octonionScalar r) = 0 := by
  simp [octAssociator, octonionMul_scalar_right, octonionMul_smul_right]

theorem octAssociator_octIm (x y z : Octonion) :
    octAssociator x y z = octAssociator (octIm x) (octIm y) (octIm z) := by
  conv_lhs =>
    rw [oct_eq_scalar_add_octIm x, oct_eq_scalar_add_octIm y, oct_eq_scalar_add_octIm z]
  simp only [octAssociator_add_left, octAssociator_add_mid, octAssociator_add_right,
    octAssociator_scalar_left, octAssociator_scalar_mid, octAssociator_scalar_right,
    zero_add]

theorem octonionReal_octAssociator (x y z : Octonion) :
    octonionReal (octAssociator x y z) = 0 := by
  unfold octAssociator
  rw [octonionReal_sub, octonionReal_mul_associative, sub_self]

theorem octAssociator_self_left (x y : Octonion) : octAssociator x x y = 0 :=
  sub_eq_zero.mpr (octMul_left_alternative x y).symm

theorem octAssociator_self_right (x y : Octonion) : octAssociator x y y = 0 :=
  sub_eq_zero.mpr (octMul_right_alternative x y)

theorem octAssociator_swap_12 (x y z : Octonion) :
    octAssociator y x z = -octAssociator x y z := by
  have h := octAssociator_self_left (x + y) z
  rw [octAssociator_add_left, octAssociator_add_mid, octAssociator_add_mid,
    octAssociator_self_left, octAssociator_self_left, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem octAssociator_swap_23 (x y z : Octonion) :
    octAssociator x z y = -octAssociator x y z := by
  have h := octAssociator_self_right x (y + z)
  rw [octAssociator_add_mid, octAssociator_add_right, octAssociator_add_right,
    octAssociator_self_right, octAssociator_self_right, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem octAssociator_self_outer (x y : Octonion) : octAssociator x y x = 0 := by
  rw [octAssociator_swap_23, octAssociator_self_left, neg_zero]

theorem octMul_flexible (x y : Octonion) :
    octonionMul (octonionMul x y) x = octonionMul x (octonionMul y x) :=
  sub_eq_zero.mp (octAssociator_self_outer x y)

theorem octAssociator_swap_13 (x y z : Octonion) :
    octAssociator z y x = -octAssociator x y z := by
  calc
    octAssociator z y x = -octAssociator y z x := octAssociator_swap_12 y z x
    _ = -(-octAssociator y x z) := by rw [octAssociator_swap_23 y x z]
    _ = -octAssociator x y z := by rw [octAssociator_swap_12 x y z, neg_neg]

theorem octAssociator_cyclic (x y z : Octonion) :
    octAssociator y z x = octAssociator x y z := by
  calc
    octAssociator y z x = -octAssociator y x z := octAssociator_swap_23 y x z
    _ = -(-octAssociator x y z) := by rw [octAssociator_swap_12 x y z]
    _ = octAssociator x y z := neg_neg _

theorem octMul_conj_left_cancel (a x : Octonion) :
    octonionMul (octonionConj a) (octonionMul a x) = octNormSq a • x := by
  have hc := octConj_eq_two_real_sub a
  have hL : octonionMul (octonionConj a) (octonionMul a x) =
      octonionMul (octonionMul (octonionConj a) a) x := by
    calc
      octonionMul (octonionConj a) (octonionMul a x)
          = octonionMul ((2 * octonionReal a) • octOne - a) (octonionMul a x) := by rw [hc]
      _ = (2 * octonionReal a) • octonionMul a x - octonionMul a (octonionMul a x) := by
            rw [octonionMul_sub_left, octonionMul_smul_left, octonionMul_one_left]
      _ = (2 * octonionReal a) • octonionMul a x - octonionMul (octonionMul a a) x := by
            rw [octMul_left_alternative]
      _ = octonionMul ((2 * octonionReal a) • a - octonionMul a a) x := by
            rw [octonionMul_sub_left, octonionMul_smul_left]
      _ = octonionMul (octonionMul ((2 * octonionReal a) • octOne - a) a) x := by
            have ha : octonionMul ((2 * octonionReal a) • octOne - a) a =
                (2 * octonionReal a) • a - octonionMul a a := by
              rw [octonionMul_sub_left, octonionMul_smul_left, octonionMul_one_left]
            rw [ha]
      _ = octonionMul (octonionMul (octonionConj a) a) x := by rw [← hc]
  rw [hL, octMul_conj_self, octonionMul_scalar_left]

theorem octMul_left_conj_cancel (a x : Octonion) :
    octonionMul a (octonionMul (octonionConj a) x) = octNormSq a • x := by
  simpa only [octonionConj_conj, octNormSq_conj] using
    octMul_conj_left_cancel (octonionConj a) x

theorem octMul_conj_right_cancel (a x : Octonion) :
    octonionMul (octonionMul x a) (octonionConj a) = octNormSq a • x := by
  have hc := octConj_eq_two_real_sub a
  have hR : octonionMul (octonionMul x a) (octonionConj a) =
      octonionMul x (octonionMul a (octonionConj a)) := by
    calc
      octonionMul (octonionMul x a) (octonionConj a)
          = octonionMul (octonionMul x a) ((2 * octonionReal a) • octOne - a) := by rw [hc]
      _ = (2 * octonionReal a) • octonionMul x a - octonionMul (octonionMul x a) a := by
            rw [octonionMul_sub_right, octonionMul_smul_right, octonionMul_one_right]
      _ = (2 * octonionReal a) • octonionMul x a - octonionMul x (octonionMul a a) := by
            rw [octMul_right_alternative]
      _ = octonionMul x ((2 * octonionReal a) • a - octonionMul a a) := by
            rw [octonionMul_sub_right, octonionMul_smul_right]
      _ = octonionMul x (octonionMul a ((2 * octonionReal a) • octOne - a)) := by
            have ha : octonionMul a ((2 * octonionReal a) • octOne - a) =
                (2 * octonionReal a) • a - octonionMul a a := by
              rw [octonionMul_sub_right, octonionMul_smul_right, octonionMul_one_right]
            rw [ha]
      _ = octonionMul x (octonionMul a (octonionConj a)) := by rw [← hc]
  rw [hR, octMul_self_conj, octonionMul_scalar_right]

theorem octMul_right_conj_cancel (a x : Octonion) :
    octonionMul (octonionMul x (octonionConj a)) a = octNormSq a • x := by
  simpa only [octonionConj_conj, octNormSq_conj] using
    octMul_conj_right_cancel (octonionConj a) x

theorem octDot_octAssociator_left (w y z : Octonion) :
    octDot (octAssociator w y z) w = 0 := by
  have hc := octConj_eq_two_real_sub w
  have hw : (2 * octonionReal w) • w - octonionMul w w =
      octonionMul w ((2 * octonionReal w) • octOne - w) := by
    rw [octonionMul_sub_right, octonionMul_smul_right, octonionMul_one_right]
  have hconj : octonionMul (octonionMul (octonionConj y) (octonionConj w)) w =
      octNormSq w • octonionConj y := by
    calc
      octonionMul (octonionMul (octonionConj y) (octonionConj w)) w
          = octonionMul (octonionMul (octonionConj y) ((2 * octonionReal w) • octOne - w)) w := by
            rw [hc]
      _ = octonionMul ((2 * octonionReal w) • octonionConj y - octonionMul (octonionConj y) w) w := by
            rw [octonionMul_sub_right, octonionMul_smul_right, octonionMul_one_right]
      _ = (2 * octonionReal w) • octonionMul (octonionConj y) w -
            octonionMul (octonionMul (octonionConj y) w) w := by
            rw [octonionMul_sub_left, octonionMul_smul_left]
      _ = (2 * octonionReal w) • octonionMul (octonionConj y) w -
            octonionMul (octonionConj y) (octonionMul w w) := by
            rw [octMul_right_alternative]
      _ = octonionMul (octonionConj y) ((2 * octonionReal w) • w - octonionMul w w) := by
            rw [octonionMul_sub_right, octonionMul_smul_right]
      _ = octonionMul (octonionConj y) (octonionMul w ((2 * octonionReal w) • octOne - w)) := by
            rw [hw]
      _ = octonionMul (octonionConj y) (octonionMul w (octonionConj w)) := by rw [← hc]
      _ = octNormSq w • octonionConj y := by
            rw [octMul_self_conj, octonionMul_scalar_right]
  have h1 : octDot (octonionMul (octonionMul w y) z) w =
      octNormSq w * octonionReal (octonionMul y z) := by
    rw [octDot_mul_left, octonionConj_mul, hconj, octDot_smul_right, octDot_comm]
    unfold octDot
    rw [← octonionConj_mul, octonionReal_conj, octonionReal_mul_comm]
  have h2 : octDot (octonionMul w (octonionMul y z)) w =
      octNormSq w * octonionReal (octonionMul y z) := by
    rw [octDot_mul_left, octMul_conj_self, octDot_comm, octDot_scalar_left]
  unfold octAssociator
  rw [octDot_sub_left, h1, h2, sub_self]

theorem octDot_octAssociator_mid (x w z : Octonion) :
    octDot (octAssociator x w z) w = 0 := by
  rw [octAssociator_swap_12, octDot_neg_left, octDot_octAssociator_left, neg_zero]

theorem octDot_octAssociator_right (x y w : Octonion) :
    octDot (octAssociator x y w) w = 0 := by
  rw [octAssociator_swap_13, octDot_neg_left, octDot_octAssociator_left, neg_zero]

private theorem oct_teichmuller (x u y z : Octonion) :
    octonionMul x (octAssociator u y z) + octonionMul (octAssociator x u y) z =
      octAssociator (octonionMul x u) y z - octAssociator x (octonionMul u y) z +
        octAssociator x u (octonionMul y z) := by
  unfold octAssociator
  simp only [octonionMul_sub_left, octonionMul_sub_right]
  abel

private theorem oct_imag_mul_assoc_eq {w a b : Octonion} (hw : octonionReal w = 0) :
    octonionMul w (octAssociator w a b) = -octAssociator (octonionMul w a) b w := by
  have hT := oct_teichmuller w w a b
  have hsq : octonionMul w w = (-octNormSq w) • octOne := octonionMul_imag_sq hw
  rw [octAssociator_self_left, octonionMul_zero_left, add_zero,
    octAssociator_self_left, add_zero, hsq, octOne_eq_scalar, ← octonionScalar_smul,
    mul_one, octAssociator_scalar_left, zero_sub] at hT
  rw [hT, octAssociator_swap_12 (octonionMul w a) w b,
    octAssociator_swap_23 (octonionMul w a) b w, neg_neg]

private theorem octMul_moufang_middle_imag {w a b : Octonion} (hw : octonionReal w = 0) :
    octonionMul (octonionMul w a) (octonionMul b w) =
      octonionMul (octonionMul w (octonionMul a b)) w := by
  have hanti := octonionMul_imag_anticomm hw (octonionReal_octAssociator w a b)
  rw [octDot_comm, octDot_octAssociator_left, mul_zero, zero_smul] at hanti
  have hcomm : octonionMul (octAssociator w a b) w = -octonionMul w (octAssociator w a b) :=
    eq_neg_of_add_eq_zero_right hanti
  rw [oct_imag_mul_assoc_eq hw, neg_neg] at hcomm
  have hdiff : octonionMul (octonionMul w (octonionMul a b)) w -
      octonionMul (octonionMul w a) (octonionMul b w) =
      octAssociator (octonionMul w a) b w - octonionMul (octAssociator w a b) w := by
    unfold octAssociator
    rw [octonionMul_sub_left]
    abel
  rw [hcomm, sub_self] at hdiff
  exact (sub_eq_zero.mp hdiff).symm

theorem octMul_moufang_middle (u a b : Octonion) :
    octonionMul (octonionMul u a) (octonionMul b u) =
      octonionMul (octonionMul u (octonionMul a b)) u := by
  let r := octonionReal u
  let w := octIm u
  have hu : u = octonionScalar r + w := oct_eq_scalar_add_octIm u
  rw [hu]
  simp only [octonionMul_add_left, octonionMul_add_right,
    octonionMul_scalar_left, octonionMul_scalar_right,
    octonionMul_smul_left, octonionMul_smul_right]
  rw [octMul_moufang_middle_imag (octonionReal_octIm u)]
  have hmid :
      r • octonionMul (octonionMul w a) b + r • octonionMul a (octonionMul b w) =
        r • octonionMul w (octonionMul a b) + r • octonionMul (octonionMul a b) w := by
    rw [← smul_add, ← smul_add]
    congr 1
    have h0 : octAssociator w a b - octAssociator a b w = 0 := by
      rw [← octAssociator_cyclic w a b, sub_self]
    unfold octAssociator at h0
    exact sub_eq_zero.mp (by
      calc
        octonionMul (octonionMul w a) b + octonionMul a (octonionMul b w) -
            (octonionMul w (octonionMul a b) + octonionMul (octonionMul a b) w)
            = (octonionMul (octonionMul w a) b - octonionMul w (octonionMul a b)) -
                (octonionMul (octonionMul a b) w - octonionMul a (octonionMul b w)) := by abel
        _ = 0 := h0)
  dsimp only [w]
  simp only [smul_add]
  rw [show (r • (r • octonionMul a b) + r • octonionMul (octonionMul (octIm u) a) b) +
        (r • octonionMul a (octonionMul b (octIm u)) +
          octonionMul (octonionMul (octIm u) (octonionMul a b)) (octIm u)) =
      (r • (r • octonionMul a b) +
        octonionMul (octonionMul (octIm u) (octonionMul a b)) (octIm u)) +
        (r • octonionMul (octonionMul (octIm u) a) b +
          r • octonionMul a (octonionMul b (octIm u))) from by abel]
  rw [hmid]
  abel

theorem octMul_moufang_left (u x y : Octonion) :
    octonionMul u (octonionMul x (octonionMul u y)) =
      octonionMul (octonionMul (octonionMul u x) u) y := by
  let r := octonionReal u
  let w := octIm u
  have hu : u = octonionScalar r + w := oct_eq_scalar_add_octIm u
  have hw_im : octonionReal w = 0 := octonionReal_octIm u
  have hxw_anti : octAssociator w (octonionMul x w) y = octonionMul w (octAssociator w x y) := by
    let s := octonionReal x
    let xm := octIm x
    have hx : x = octonionScalar s + xm := oct_eq_scalar_add_octIm x
    have hxm_im : octonionReal xm = 0 := octonionReal_octIm x
    have hcli := octonionMul_imag_anticomm hxm_im hw_im
    have hxw : octonionMul x w =
        s • w + (-2 * octDot xm w) • octOne - octonionMul w xm := by
      conv_lhs => rw [hx]
      rw [octonionMul_add_left, octonionMul_scalar_left]
      have hsub : octonionMul xm w = (-2 * octDot xm w) • octOne - octonionMul w xm :=
        eq_sub_iff_add_eq.mpr hcli
      rw [hsub]; abel
    have hwx : octonionMul w x = s • w + octonionMul w xm := by
      conv_lhs => rw [hx]
      rw [octonionMul_add_right, octonionMul_scalar_right]
    rw [hxw, octAssociator_sub_mid, octAssociator_add_mid, octAssociator_smul_mid,
      octAssociator_smul_mid, octAssociator_self_left, octOne_eq_scalar,
      octAssociator_scalar_mid 1 w y, smul_zero, smul_zero, zero_add, zero_sub]
    have hT := oct_teichmuller w w x y
    have hsq : octonionMul w w = (-octNormSq w) • octOne := octonionMul_imag_sq hw_im
    rw [octAssociator_self_left, octonionMul_zero_left, add_zero,
      octAssociator_self_left, add_zero, hsq, octOne_eq_scalar, ← octonionScalar_smul,
      mul_one, octAssociator_scalar_left, zero_sub] at hT
    rw [hT, hwx, octAssociator_add_mid, octAssociator_smul_mid,
      octAssociator_self_left, smul_zero, zero_add]
  have hdiff : octonionMul (octonionMul (octonionMul u x) u) y -
      octonionMul u (octonionMul x (octonionMul u y)) =
      octAssociator u (octonionMul x u) y - octonionMul u (octAssociator u x y) := by
    rw [octMul_flexible u x, show octAssociator u x y = -octAssociator x u y from octAssociator_swap_12 x u y,
      octonionMul_neg_right, sub_neg_eq_add]
    unfold octAssociator
    rw [octonionMul_sub_right]
    abel
  have hzero : octAssociator u (octonionMul x u) y - octonionMul u (octAssociator u x y) = 0 := by
    conv_lhs => rw [hu]
    simp only [octAssociator_add_left, octAssociator_scalar_left, zero_add,
      octonionMul_add_right, octonionMul_scalar_right, octAssociator_add_mid,
      octAssociator_smul_mid, octonionMul_add_left, octonionMul_scalar_left]
    rw [hxw_anti]
    abel
  rw [hzero] at hdiff
  exact (sub_eq_zero.mp hdiff).symm

theorem octMul_moufang_right (u x y : Octonion) :
    octonionMul (octonionMul (octonionMul x u) y) u =
      octonionMul x (octonionMul u (octonionMul y u)) := by
  have h := congrArg octonionConj
    (octMul_moufang_left (octonionConj u) (octonionConj y) (octonionConj x))
  simp only [octonionConj_mul, octonionConj_conj] at h
  exact h

theorem octMul_moufang_unit_conj (u x y : Octonion) (hu : octNormSq u = 1) :
    octonionMul (octonionMul (octonionMul u x) u) (octonionMul (octonionConj u) y) =
      octonionMul u (octonionMul x y) := by
  rw [← octMul_moufang_left, octMul_left_conj_cancel, hu, one_smul]

theorem octAssociator_I_J_L : octAssociator octI octJ octL = (2 : ℝ) • octT := by
  have h1 : octonionMul (octonionMul octI octJ) octL = octT := by
    rw [octK_eq_mul]; apply oct_ext <;> simp [octonionMul, octK, octL, octT]
  have h2 : octonionMul octI (octonionMul octJ octL) = -octT := by
    rw [octR_eq_mul]
    rw [show octonionMul octI octR = (0, ({ re := 0, imI := 0, imJ := 0, imK := -1 } : Quaternion ℝ)) from by
      apply oct_ext <;> simp [octonionMul, octI, octR]]
    apply oct_ext
    · change (0 : ℝ) = -0; norm_num
    · change (0 : ℝ) = -0; norm_num
    · change (0 : ℝ) = -0; norm_num
    · change (0 : ℝ) = -0; norm_num
    · change (0 : ℝ) = -0; norm_num
    · change (0 : ℝ) = -0; norm_num
    · change (0 : ℝ) = -0; norm_num
    · change (-1 : ℝ) = -1; norm_num
  rw [octAssociator, h1, h2, sub_neg_eq_add, ← two_smul ℝ]

theorem octNormSq_octAssociator_I_J_L : octNormSq (octAssociator octI octJ octL) = 4 := by
  rw [octAssociator_I_J_L, octNormSq_smul]
  have hT : octNormSq octT = 1 := by
    rw [octNormSq_eq_coords]; simp [octT]
  rw [hT]; norm_num

/-! ## Section 3: The Harvey–Lawson Identity (`eq:A:HL`) -/

private def gramDet3 (u v w : Octonion) : ℝ :=
  (Matrix.of fun k l : Fin 3 => octDot (![u, v, w] k) (![u, v, w] l)).det

private theorem gramDet3_eq (u v w : Octonion) :
    gramDet3 u v w =
      octDot u u * (octDot v v * octDot w w - octDot v w * octDot w v) -
        octDot u v * (octDot v u * octDot w w - octDot v w * octDot w u) +
        octDot u w * (octDot v u * octDot w v - octDot v v * octDot w u) := by
  unfold gramDet3
  have hv0 : ![u, v, w] 0 = u := rfl
  have hv1 : ![u, v, w] 1 = v := rfl
  have hv2 : ![u, v, w] 2 = w := rfl
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, hv0, hv1, hv2]
  ring

private theorem gramDet3_sub_mid (u v w : Octonion) (α : ℝ) :
    gramDet3 u (v - α • u) w = gramDet3 u v w := by
  rw [gramDet3_eq, gramDet3_eq]
  simp only [octDot_sub_left, octDot_sub_right, octDot_smul_left, octDot_smul_right,
    octDot_comm v u, octDot_comm w u, octDot_comm w v]
  ring

private theorem gramDet3_sub_right (u v w : Octonion) (α β : ℝ) :
    gramDet3 u v (w - α • u - β • v) = gramDet3 u v w := by
  rw [gramDet3_eq, gramDet3_eq]
  simp only [octDot_sub_left, octDot_sub_right, octDot_smul_left, octDot_smul_right,
    octDot_comm v u, octDot_comm w u, octDot_comm w v]
  ring

private theorem gramDet3_ortho {u v w : Octonion}
    (huv : octDot u v = 0) (huw : octDot u w = 0) (hvw : octDot v w = 0) :
    gramDet3 u v w = octNormSq u * octNormSq v * octNormSq w := by
  rw [gramDet3_eq]
  unfold octNormSq
  rw [octDot_comm v u, octDot_comm w u, octDot_comm w v, huv, huw, hvw]
  ring

theorem octonionMul_ortho_imag_left_cancel {u v w0 : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) (hw : octonionReal w0 = 0)
    (huv : octDot u v = 0) (huw : octDot u w0 = 0) (hvw : octDot v w0 = 0)
    (huv_w : octDot (octonionMul u v) w0 = 0) :
    octonionMul (octonionMul u v) w0 = -octonionMul u (octonionMul v w0) := by
  by_cases hu0 : u = 0
  · subst hu0; simp [octonionMul_zero_left]
  have hnu : octNormSq u ≠ 0 := fun h => hu0 ((octNormSq_eq_zero u).mp h)
  have huv_im : octonionReal (octonionMul u v) = 0 := by
    rw [octonionReal_mul_imag_eq hu hv, huv, neg_zero]
  have h1 : octonionMul w0 (octonionMul u v) = -octonionMul (octonionMul u v) w0 :=
    eq_neg_of_add_eq_zero_left (by
      rw [octonionMul_imag_anticomm hw huv_im, octDot_comm, huv_w, mul_zero, zero_smul])
  have h2 : octonionMul (octonionMul u w0) u = octNormSq u • w0 := by
    have hwu' : octonionMul u w0 = -octonionMul w0 u :=
      eq_neg_of_add_eq_zero_left (by
        rw [octonionMul_imag_anticomm hu hw, huw, mul_zero, zero_smul])
    rw [hwu', octonionMul_neg_left, octMul_right_alternative, octonionMul_imag_sq hu,
      octonionMul_smul_right, octonionMul_one_right, neg_smul, neg_neg]
  have h3 : octonionMul w0 v = -octonionMul v w0 :=
    eq_neg_of_add_eq_zero_right (by
      rw [octonionMul_imag_anticomm hv hw, hvw, mul_zero, zero_smul])
  have hM := octMul_moufang_left u w0 v
  rw [h1, octonionMul_neg_right, h2, octonionMul_smul_left, h3, smul_neg] at hM
  have hM2 := congrArg (fun z : Octonion => octonionMul u z) hM
  have hsq : octonionMul u (octonionMul u (octonionMul (octonionMul u v) w0)) =
      (-octNormSq u) • octonionMul (octonionMul u v) w0 := by
    rw [octMul_left_alternative, octonionMul_imag_sq hu, octonionMul_smul_left,
      octonionMul_one_left]
  rw [octonionMul_neg_right, hsq, octonionMul_neg_right, octonionMul_smul_right,
    neg_smul, neg_neg, ← smul_neg] at hM2
  exact (smul_right_injective Octonion hnu hM2)

private theorem harvey_lawson_ortho {u v w : Octonion}
    (hu : octonionReal u = 0) (hv : octonionReal v = 0) (hw : octonionReal w = 0)
    (huv : octDot u v = 0) (huw : octDot u w = 0) (hvw : octDot v w = 0) :
    octNormSq u * octNormSq v * octNormSq w - (octDot (octonionMul u v) w) ^ 2 =
      (1 / 4 : ℝ) * octNormSq (octAssociator u v w) := by
  by_cases hu0 : u = 0
  · subst hu0
    simp [(octNormSq_eq_zero 0).mpr rfl, octonionMul_zero_left, octAssociator_zero_left,
      octDot_zero_left]
  by_cases hv0 : v = 0
  · subst hv0
    simp [(octNormSq_eq_zero 0).mpr rfl, octonionMul_zero_right, octAssociator_zero_mid,
      octDot_zero_left]
  have hnu : octNormSq u ≠ 0 := fun h => hu0 ((octNormSq_eq_zero u).mp h)
  have hnv : octNormSq v ≠ 0 := fun h => hv0 ((octNormSq_eq_zero v).mp h)
  have hnuv : octNormSq u * octNormSq v ≠ 0 := mul_ne_zero hnu hnv
  let lam := octDot (octonionMul u v) w / (octNormSq u * octNormSq v)
  let w0 := w - lam • octonionMul u v
  have huv_im : octonionReal (octonionMul u v) = 0 := by
    rw [octonionReal_mul_imag_eq hu hv, huv, neg_zero]
  have hw0_im : octonionReal w0 = 0 := by
    simp [w0, octonionReal_sub, octonionReal_smul, hw, huv_im]
  have hu_uv : octDot u (octonionMul u v) = 0 := by
    rw [octDot_comm, octDot_mul_left, octMul_conj_self, octDot_comm, octDot_scalar_left, hv, mul_zero]
  have hv_uv : octDot v (octonionMul u v) = 0 := by
    rw [octDot_comm, octDot_mul_right, octMul_self_conj, octDot_comm, octDot_scalar_left, hu, mul_zero]
  have huw0 : octDot u w0 = 0 := by
    simp [w0, octDot_sub_right, octDot_smul_right, huw, hu_uv]
  have hvw0 : octDot v w0 = 0 := by
    simp [w0, octDot_sub_right, octDot_smul_right, hvw, hv_uv]
  have huv_w0 : octDot (octonionMul u v) w0 = 0 := by
    simp only [w0, lam, octDot_sub_right, octDot_smul_right, octDot_self, octNormSq_mul]
    field_simp [hnuv]
    ring
  have hassoc_uv : octAssociator u v (octonionMul u v) = 0 := by
    unfold octAssociator
    have hvu : octonionMul v u = -octonionMul u v :=
      eq_neg_of_add_eq_zero_right (by
        rw [octonionMul_imag_anticomm hu hv, huv, mul_zero, zero_smul])
    have hsq_uv : octonionMul (octonionMul u v) (octonionMul u v) =
        (-(octNormSq u * octNormSq v)) • octOne := by
      rw [octonionMul_imag_sq huv_im, octNormSq_mul]
    have hvu2 : octonionMul v (octonionMul u v) = octNormSq v • u := by
      rw [← neg_neg (octonionMul u v), ← hvu, octonionMul_neg_right,
        octMul_left_alternative, octonionMul_imag_sq hv, octonionMul_smul_left,
        octonionMul_one_left, neg_smul, neg_neg]
    rw [hsq_uv, hvu2, octonionMul_smul_right, octonionMul_imag_sq hu, smul_smul, sub_eq_zero]
    congr 1; ring
  have hassoc_eq : octAssociator u v w = (2 : ℝ) • octonionMul (octonionMul u v) w0 := by
    have hw_decomp : w = lam • octonionMul u v + w0 := by simp [w0]
    rw [hw_decomp, octAssociator_add_right, octAssociator_smul_right, hassoc_uv,
      smul_zero, zero_add]
    have hmul : octonionMul u (octonionMul v w0) = -octonionMul (octonionMul u v) w0 := by
      rw [octonionMul_ortho_imag_left_cancel hu hv hw0_im huv huw0 hvw0 huv_w0, neg_neg]
    unfold octAssociator
    rw [hmul, sub_neg_eq_add, ← two_smul ℝ]
  rw [hassoc_eq, octNormSq_smul, octNormSq_mul, octNormSq_mul]
  have hw0_norm : octNormSq w0 = octNormSq w - octDot (octonionMul u v) w ^ 2 / (octNormSq u * octNormSq v) := by
    simp only [w0, octNormSq_sub, octNormSq_smul, octNormSq_mul, octDot_smul_right,
      octDot_comm w (octonionMul u v)]
    dsimp only [lam]
    field_simp [hnuv]
    ring
  rw [hw0_norm]
  field_simp [hnuv]
  ring

theorem harvey_lawson_132 (g1 g2 g3 : Octonion) :
    let u1 := octIm g1
    let u2 := octIm g2
    let u3 := octIm g3
    (Matrix.of fun k l : Fin 3 => octDot (![u1, u2, u3] k) (![u1, u2, u3] l)).det -
      (octDot (octCross u1 u3) u2) ^ 2 =
      (1 / 4 : ℝ) * octNormSq (octAssociator g1 g3 g2) := by
  intro u1 u2 u3
  change gramDet3 u1 u2 u3 - (octDot (octCross u1 u3) u2) ^ 2 =
    (1 / 4 : ℝ) * octNormSq (octAssociator g1 g3 g2)
  rw [octAssociator_octIm g1 g3 g2]
  change _ = (1 / 4 : ℝ) * octNormSq (octAssociator u1 u3 u2)
  have hu1 : octonionReal u1 = 0 := octonionReal_octIm g1
  have hu2 : octonionReal u2 = 0 := octonionReal_octIm g2
  have hu3 : octonionReal u3 = 0 := octonionReal_octIm g3
  have hswap : gramDet3 u1 u2 u3 = gramDet3 u1 u3 u2 := by
    rw [gramDet3_eq, gramDet3_eq]
    simp only [octDot_comm u2 u1, octDot_comm u3 u1, octDot_comm u3 u2]
    ring
  rw [hswap]
  by_cases hu10 : u1 = 0
  · rw [hu10, gramDet3_eq]
    simp only [octDot_zero_left, octDot_zero_right, octCross, octonionMul_zero_left,
      octonionMul_zero_right, sub_self, smul_zero, octAssociator_zero_left,
      (octNormSq_eq_zero 0).mpr rfl]
    ring
  have hn1 : octNormSq u1 ≠ 0 := fun h => hu10 ((octNormSq_eq_zero u1).mp h)
  let α := octDot u1 u3 / octNormSq u1
  let v' := u3 - α • u1
  have hv'_im : octonionReal v' = 0 := by
    simp [v', octonionReal_sub, octonionReal_smul, hu3, hu1]
  have huv' : octDot u1 v' = 0 := by
    simp only [v', α, octDot_sub_right, octDot_smul_right, octDot_self]
    field_simp [hn1]; ring
  rw [← gramDet3_sub_mid u1 u3 u2 α]
  have hcross1 : octCross u1 u3 = octCross u1 v' := by
    simp only [v', octCross_sub_right, octCross_smul_right, octCross_self, smul_zero, sub_zero]
  have hassoc1 : octAssociator u1 u3 u2 = octAssociator u1 v' u2 := by
    simp only [v', octAssociator_sub_mid, octAssociator_smul_mid, octAssociator_self_left,
      smul_zero, sub_zero]
  rw [hcross1, hassoc1]
  by_cases hv'0 : v' = 0
  · rw [show u3 - α • u1 = v' from rfl, hv'0, gramDet3_eq]
    simp only [octDot_zero_left, octDot_zero_right, octCross, octonionMul_zero_left,
      octonionMul_zero_right, sub_self, smul_zero, octAssociator_zero_mid,
      (octNormSq_eq_zero 0).mpr rfl]
    ring
  have hn2 : octNormSq v' ≠ 0 := fun h => hv'0 ((octNormSq_eq_zero v').mp h)
  let β1 := octDot u1 u2 / octNormSq u1
  let β2 := octDot v' u2 / octNormSq v'
  let w' := u2 - β1 • u1 - β2 • v'
  have hw'_im : octonionReal w' = 0 := by
    simp [w', octonionReal_sub, octonionReal_smul, hu2, hu1, hv'_im]
  have huw' : octDot u1 w' = 0 := by
    simp only [w', β1, octDot_sub_right, octDot_smul_right, octDot_self, huv', mul_zero, sub_zero]
    field_simp [hn1]; ring
  have hv'w' : octDot v' w' = 0 := by
    simp only [w', β2, octDot_sub_right, octDot_smul_right, octDot_self, octDot_comm v' u1, huv',
      mul_zero, sub_zero]
    field_simp [hn2]; ring
  rw [← gramDet3_sub_right u1 v' u2 β1 β2,
    show u2 - β1 • u1 - β2 • v' = w' from rfl, gramDet3_ortho huv' huw' hv'w']
  have hdot_w : octDot (octCross u1 v') u2 = octDot (octCross u1 v') w' := by
    simp only [w', octDot_sub_right, octDot_smul_right, octDot_octCross_left hu1 hv'_im,
      octDot_octCross_right hu1 hv'_im, mul_zero, sub_zero]
  have hassoc2 : octAssociator u1 v' u2 = octAssociator u1 v' w' := by
    simp only [w', octAssociator_sub_right, octAssociator_smul_right,
      octAssociator_self_outer, octAssociator_self_right, smul_zero, sub_zero]
  rw [hdot_w, hassoc2, octDot_octCross_eq hu1 hv'_im hw'_im]
  exact harvey_lawson_ortho hu1 hv'_im hw'_im huv' huw' hv'w'

theorem harvey_lawson (g1 g2 g3 : Octonion) :
    let u1 := octIm g1
    let u2 := octIm g2
    let u3 := octIm g3
    (Matrix.of fun k l : Fin 3 => octDot (![u1, u2, u3] k) (![u1, u2, u3] l)).det -
      (octDot (octCross u1 u3) u2) ^ 2 =
      (1 / 4 : ℝ) * octNormSq (octAssociator g1 g2 g3) := by
  dsimp only
  rw [harvey_lawson_132 g1 g2 g3, octAssociator_swap_23 g1 g2 g3, octNormSq_neg]

/-! ## Section 4: `OctonionAutomorphism` and the Basic-Triple Theorem -/

structure OctonionAutomorphism where
  equiv : Octonion ≃ₗ[ℝ] Octonion
  map_one : equiv octOne = octOne
  map_mul : ∀ x y, equiv (octonionMul x y) = octonionMul (equiv x) (equiv y)

namespace OctonionAutomorphism

def refl : OctonionAutomorphism where
  equiv := LinearEquiv.refl ℝ Octonion
  map_one := rfl
  map_mul _ _ := rfl

def comp (α β : OctonionAutomorphism) : OctonionAutomorphism where
  equiv := β.equiv.trans α.equiv
  map_one := by simp [β.map_one, α.map_one]
  map_mul x y := by simp [β.map_mul, α.map_mul]

def symm (α : OctonionAutomorphism) : OctonionAutomorphism where
  equiv := α.equiv.symm
  map_one := by
    apply α.equiv.injective
    simp [α.map_one]
  map_mul x y := by
    apply α.equiv.injective
    simp [α.map_mul]

@[simp] theorem refl_apply (x : Octonion) : refl.equiv x = x := rfl
@[simp] theorem comp_apply (α β : OctonionAutomorphism) (x : Octonion) :
    (α.comp β).equiv x = α.equiv (β.equiv x) := rfl
@[simp] theorem symm_apply (α : OctonionAutomorphism) (x : Octonion) :
    α.symm.equiv x = α.equiv.symm x := rfl

theorem map_scalar (α : OctonionAutomorphism) (r : ℝ) :
    α.equiv (octonionScalar r) = octonionScalar r := by
  rw [octonionScalar_eq_smul, map_smul, ← octOne_eq_scalar, α.map_one, octOne_eq_scalar]

private theorem oct_sq_eq_self_re_normSq (y : Octonion) :
    octonionMul y y = (2 * octonionReal y) • y - octNormSq y • octOne := by
  have h := congrArg (fun z => octonionMul y z) (octAdd_conj y)
  rw [octonionMul_add_right, octMul_self_conj, octonionMul_smul_right,
    octonionMul_scalar_right, octonionScalar_eq_smul, ← octOne_eq_scalar, smul_smul] at h
  exact eq_sub_iff_add_eq.mpr h

theorem map_real_im (α : OctonionAutomorphism) {u : Octonion} (hu : octonionReal u = 0) :
    octonionReal (α.equiv u) = 0 := by
  by_cases hu0 : u = 0
  · subst hu0; simp [octonionReal_zero]
  have hnu : 0 < octNormSq u :=
    lt_of_le_of_ne (octNormSq_nonneg u) (Ne.symm (fun h => hu0 ((octNormSq_eq_zero u).mp h)))
  have husq : octonionMul (α.equiv u) (α.equiv u) = (-octNormSq u) • octOne := by
    rw [← α.map_mul, octonionMul_imag_sq hu, map_smul, α.map_one]
  have hsq := oct_sq_eq_self_re_normSq (α.equiv u)
  rw [husq] at hsq
  by_contra hre
  have hscal : α.equiv u =
      ((octNormSq (α.equiv u) - octNormSq u) / (2 * octonionReal (α.equiv u))) • octOne := by
    have hlin : (2 * octonionReal (α.equiv u)) • α.equiv u =
        (octNormSq (α.equiv u) - octNormSq u) • octOne := by
      calc
        (2 * octonionReal (α.equiv u)) • α.equiv u
            = (-octNormSq u) • octOne + octNormSq (α.equiv u) • octOne :=
              eq_add_of_sub_eq hsq.symm
        _ = (octNormSq (α.equiv u) - octNormSq u) • octOne := by module
    have h2 : (2 * octonionReal (α.equiv u)) ≠ 0 := mul_ne_zero (by norm_num) hre
    apply smul_right_injective Octonion h2
    dsimp only
    rw [hlin, smul_smul]
    congr 1; field_simp [h2]
  have hpos := congrArg octonionReal (congrArg (fun z => octonionMul z z) hscal)
  rw [husq, octonionMul_smul_left, octonionMul_smul_right, octonionMul_one_left,
    octonionReal_smul, octonionReal_smul, octonionReal_smul, octonionReal_one] at hpos
  nlinarith [sq_nonneg ((octNormSq (α.equiv u) - octNormSq u) / (2 * octonionReal (α.equiv u)))]

theorem map_real (α : OctonionAutomorphism) (x : Octonion) :
    octonionReal (α.equiv x) = octonionReal x := by
  conv_lhs => rw [oct_eq_scalar_add_octIm x]
  rw [map_add, α.map_scalar, octonionReal_add, octonionReal_scalar,
    α.map_real_im (octonionReal_octIm x), add_zero]

theorem map_conj (α : OctonionAutomorphism) (x : Octonion) :
    α.equiv (octonionConj x) = octonionConj (α.equiv x) := by
  rw [octConj_eq_two_real_sub x, octConj_eq_two_real_sub (α.equiv x),
    map_sub, map_smul, α.map_one, α.map_real]

theorem map_dot (α : OctonionAutomorphism) (x y : Octonion) :
    octDot (α.equiv x) (α.equiv y) = octDot x y := by
  unfold octDot
  rw [← α.map_conj, ← α.map_mul, α.map_real]

theorem map_normSq (α : OctonionAutomorphism) (x : Octonion) :
    octNormSq (α.equiv x) = octNormSq x :=
  α.map_dot x x

theorem map_im (α : OctonionAutomorphism) (x : Octonion) :
    α.equiv (octIm x) = octIm (α.equiv x) := by
  simp only [octIm, map_sub, α.map_scalar, α.map_real]

theorem map_cross (α : OctonionAutomorphism) (u v : Octonion) :
    α.equiv (octCross u v) = octCross (α.equiv u) (α.equiv v) := by
  simp only [octCross, map_smul, map_sub, α.map_mul]

theorem map_associator (α : OctonionAutomorphism) (x y z : Octonion) :
    α.equiv (octAssociator x y z) = octAssociator (α.equiv x) (α.equiv y) (α.equiv z) := by
  simp only [octAssociator, map_sub, α.map_mul]

end OctonionAutomorphism

/-! ### Basic-Triple Theorem (`octAutoOfBasicTriple`) -/

def octBasisQuat (e1 e2 : Octonion) : Quaternion ℝ →ₗ[ℝ] Octonion where
  toFun q := q.re • octOne + q.imI • e1 + q.imJ • e2 + q.imK • octonionMul e1 e2
  map_add' p q := by
    simp only [q_re_add, q_imI_add, q_imJ_add, q_imK_add, add_smul]
    abel
  map_smul' r q := by
    simp only [q_re_smul, q_imI_smul, q_imJ_smul, q_imK_smul, RingHom.id_apply,
      smul_add, smul_smul]

private theorem octBasisQuat_isQuatEmbedding (e1 e2 : Octonion)
    (h1_im : octonionReal e1 = 0) (h2_im : octonionReal e2 = 0)
    (h1_norm : octNormSq e1 = 1) (h2_norm : octNormSq e2 = 1)
    (h12 : octDot e1 e2 = 0) : IsQuatEmbedding (octBasisQuat e1 e2) := by
  have he12_im : octonionReal (octonionMul e1 e2) = 0 := by
    rw [octonionReal_mul_imag_eq h1_im h2_im, h12, neg_zero]
  have he12_norm : octNormSq (octonionMul e1 e2) = 1 := by
    rw [octNormSq_mul, h1_norm, h2_norm, mul_one]
  have he1_1 : octDot octOne e1 = 0 := by rw [octOne_eq_scalar, octDot_scalar_left, h1_im, mul_zero]
  have he2_1 : octDot octOne e2 = 0 := by rw [octOne_eq_scalar, octDot_scalar_left, h2_im, mul_zero]
  have he3_1 : octDot octOne (octonionMul e1 e2) = 0 := by
    rw [octOne_eq_scalar, octDot_scalar_left, he12_im, mul_zero]
  have he1_3 : octDot e1 (octonionMul e1 e2) = 0 := by
    rw [octDot_comm, octDot_mul_left, octonionConj_eq_neg_of_real_zero h1_im,
      octonionMul_neg_left, octonionMul_imag_sq h1_im, h1_norm, neg_one_smul, neg_neg,
      octDot_comm, he2_1]
  have he2_3 : octDot e2 (octonionMul e1 e2) = 0 := by
    rw [octDot_comm, octDot_mul_right, octonionConj_eq_neg_of_real_zero h2_im,
      octonionMul_neg_right, octonionMul_imag_sq h2_im, h2_norm, neg_one_smul, neg_neg,
      octDot_comm, he1_1]
  have h1sq : octonionMul e1 e1 = -octOne := by
    rw [octonionMul_imag_sq h1_im, h1_norm, neg_one_smul]
  have h2sq : octonionMul e2 e2 = -octOne := by
    rw [octonionMul_imag_sq h2_im, h2_norm, neg_one_smul]
  have h21 : octonionMul e2 e1 = -octonionMul e1 e2 :=
    eq_neg_of_add_eq_zero_right (by
      rw [octonionMul_imag_anticomm h1_im h2_im, h12, mul_zero, zero_smul])
  have h12_neg : octonionMul e1 e2 = -octonionMul e2 e1 := by rw [h21, neg_neg]
  have h1_12 : octonionMul e1 (octonionMul e1 e2) = -e2 := by
    rw [octMul_left_alternative, h1sq, octonionMul_neg_left, octonionMul_one_left]
  have h12_1 : octonionMul (octonionMul e1 e2) e1 = e2 := by
    rw [octMul_flexible, h21, octonionMul_neg_right, h1_12, neg_neg]
  have h2_12 : octonionMul e2 (octonionMul e1 e2) = e1 := by
    rw [h12_neg, octonionMul_neg_right, octMul_left_alternative, h2sq,
      octonionMul_neg_left, octonionMul_one_left, neg_neg]
  have h12_2 : octonionMul (octonionMul e1 e2) e2 = -e1 := by
    rw [octMul_right_alternative, h2sq, octonionMul_neg_right, octonionMul_one_right]
  have h3sq : octonionMul (octonionMul e1 e2) (octonionMul e1 e2) = -octOne := by
    rw [octonionMul_imag_sq he12_im, he12_norm, neg_one_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [octBasisQuat, octOne_eq_scalar]
  · intro p q
    simp only [octBasisQuat, LinearMap.coe_mk, AddHom.coe_mk,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      octonionMul_add_left, octonionMul_add_right, octonionMul_smul_left,
      octonionMul_smul_right, octonionMul_one_left, octonionMul_one_right,
      h1sq, h2sq, h21, h1_12, h12_1, h2_12, h12_2, h3sq]
    module
  · intro q
    have hce1 : octonionConj e1 = -e1 := octonionConj_eq_neg_of_real_zero h1_im
    have hce2 : octonionConj e2 = -e2 := octonionConj_eq_neg_of_real_zero h2_im
    have hce3 : octonionConj (octonionMul e1 e2) = -octonionMul e1 e2 :=
      octonionConj_eq_neg_of_real_zero he12_im
    simp only [octBasisQuat, LinearMap.coe_mk, AddHom.coe_mk,
      q_re_star, q_imI_star, q_imJ_star, q_imK_star,
      octonionConj_add, octonionConj_smul, octonionConj_one, hce1, hce2, hce3, smul_neg]
    module
  · intro q
    simp [octBasisQuat, octonionReal_add, octonionReal_smul, octonionReal_one,
      h1_im, h2_im, he12_im]
  · intro p q h
    have hd := sub_eq_zero.mpr h
    rw [← map_sub] at hd
    let d := p - q
    have hre : octDot (octBasisQuat e1 e2 d) octOne = 0 := by rw [hd, octDot_zero_left]
    have himI : octDot (octBasisQuat e1 e2 d) e1 = 0 := by rw [hd, octDot_zero_left]
    have himJ : octDot (octBasisQuat e1 e2 d) e2 = 0 := by rw [hd, octDot_zero_left]
    have himK : octDot (octBasisQuat e1 e2 d) (octonionMul e1 e2) = 0 := by rw [hd, octDot_zero_left]
    simp only [octBasisQuat, LinearMap.coe_mk, AddHom.coe_mk,
      octDot_add_left, octDot_smul_left, octDot_self, octNormSq_one,
      h1_norm, h2_norm, he12_norm, he1_1, he2_1, he3_1, he1_3, he2_3, h12,
      octDot_comm e1 octOne, octDot_comm e2 octOne, octDot_comm (octonionMul e1 e2) octOne,
      octDot_comm e2 e1, octDot_comm (octonionMul e1 e2) e1,
      octDot_comm (octonionMul e1 e2) e2, mul_one, mul_zero, add_zero, zero_add] at hre himI himJ himK
    apply sub_eq_zero.mp
    apply Quaternion.ext <;> simp [d, hre, himI, himJ, himK]

theorem oct_finrank : Module.finrank ℝ Octonion = 8 := by
  change Module.finrank ℝ (Quaternion ℝ × Quaternion ℝ) = 8
  rw [Module.finrank_prod, Quaternion.finrank_eq_four]

def octExtendQuatLinear (e1 e2 e3 : Octonion) : Octonion →ₗ[ℝ] Octonion where
  toFun x := octBasisQuat e1 e2 x.1 + octonionMul (octBasisQuat e1 e2 x.2) e3
  map_add' x y := by
    rw [oct_fst_add, oct_snd_add, map_add, map_add, octonionMul_add_left]; abel
  map_smul' r x := by
    rw [oct_fst_smul, oct_snd_smul, map_smul, map_smul, octonionMul_smul_left]
    simp only [RingHom.id_apply, smul_add]

theorem octAutoOfBasicTriple_props (e1 e2 e3 : Octonion)
    (h1_im : octonionReal e1 = 0) (h2_im : octonionReal e2 = 0) (h3_im : octonionReal e3 = 0)
    (h1_norm : octNormSq e1 = 1) (h2_norm : octNormSq e2 = 1) (h3_norm : octNormSq e3 = 1)
    (h12 : octDot e1 e2 = 0) (h13 : octDot e1 e3 = 0) (h23 : octDot e2 e3 = 0)
    (h3_12 : octDot e3 (octonionMul e1 e2) = 0) :
    Function.Bijective (octExtendQuatLinear e1 e2 e3) ∧
      octExtendQuatLinear e1 e2 e3 octOne = octOne ∧
      ∀ x y : Octonion, octExtendQuatLinear e1 e2 e3 (octonionMul x y) =
        octonionMul (octExtendQuatLinear e1 e2 e3 x) (octExtendQuatLinear e1 e2 e3 y) := by
  let φ := octBasisQuat e1 e2
  have hφ : IsQuatEmbedding φ :=
    octBasisQuat_isQuatEmbedding e1 e2 h1_im h2_im h1_norm h2_norm h12
  have he3_perp : ∀ q : Quaternion ℝ, octDot (φ q) e3 = 0 := by
    intro q
    simp only [φ, octBasisQuat, LinearMap.coe_mk, AddHom.coe_mk, octDot_add_left, octDot_smul_left,
      show octDot octOne e3 = 0 from by rw [octOne_eq_scalar, octDot_scalar_left, h3_im, mul_zero],
      h13, h23, octDot_comm (octonionMul e1 e2) e3, h3_12, mul_zero, add_zero]
  have hφ_im : ∀ {q : Quaternion ℝ}, q.re = 0 → octonionReal (φ q) = 0 := by
    intro q hq; rw [hφ.map_re, hq]
  have hφ_norm : ∀ q : Quaternion ℝ, octNormSq (φ q) = quatNormSq q := by
    intro q
    unfold octNormSq octDot
    rw [← hφ.map_star, ← hφ.map_mul, hφ.map_re]
    simp [quatNormSq]; ring
  have hce3 : octonionConj e3 = -e3 := octonionConj_eq_neg_of_real_zero h3_im
  have he3sq : octonionMul e3 e3 = -octOne := by
    rw [octonionMul_imag_sq h3_im, h3_norm, neg_one_smul]
  have hrule1_basis : ∀ {u v : Octonion},
      octonionReal u = 0 → octonionReal v = 0 →
      octNormSq u = 1 → octNormSq v = 1 →
      octDot u v = 0 → octDot u e3 = 0 → octDot v e3 = 0 →
      octDot (octonionMul u v) e3 = 0 →
      octonionMul u (octonionMul v e3) = octonionMul (octonionMul v u) e3 := by
    intro u v hu_im hv_im _ _ huv hu3 hv3 huv3
    have hvu : octonionMul v u = -octonionMul u v :=
      eq_neg_of_add_eq_zero_right (by
        rw [octonionMul_imag_anticomm hu_im hv_im, huv, mul_zero, zero_smul])
    rw [hvu, octonionMul_neg_left, ← neg_eq_iff_eq_neg, eq_comm]
    exact octonionMul_ortho_imag_left_cancel hu_im hv_im h3_im huv hu3 hv3 huv3
  have hrule1_imag : ∀ {a b : Quaternion ℝ}, a.re = 0 → b.re = 0 →
      octonionMul (φ a) (octonionMul (φ b) e3) = octonionMul (φ (b * a)) e3 := by
    intro a b ha hb
    let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
    let qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
    let qk : Quaternion ℝ := ⟨0, 0, 0, 1⟩
    have ha_exp : a = a.imI • qi + a.imJ • qj + a.imK • qk := by
      apply Quaternion.ext <;> simp [ha, qi, qj, qk]
    have hb_exp : b = b.imI • qi + b.imJ • qj + b.imK • qk := by
      apply Quaternion.ext <;> simp [hb, qi, qj, qk]
    have hqi : φ qi = e1 := by simp [φ, octBasisQuat, qi]
    have hqj : φ qj = e2 := by simp [φ, octBasisQuat, qj]
    have hqk : φ qk = octonionMul e1 e2 := by simp [φ, octBasisQuat, qk]
    have he12_im : octonionReal (octonionMul e1 e2) = 0 := by
      rw [octonionReal_mul_imag_eq h1_im h2_im, h12, neg_zero]
    have he12_norm : octNormSq (octonionMul e1 e2) = 1 := by
      rw [octNormSq_mul, h1_norm, h2_norm, mul_one]
    have he1_12 : octDot e1 (octonionMul e1 e2) = 0 := by
      rw [octDot_comm, octDot_mul_left, octonionConj_eq_neg_of_real_zero h1_im,
        octonionMul_neg_left, octonionMul_imag_sq h1_im, h1_norm, neg_one_smul, neg_neg,
        octDot_comm, show octDot octOne e2 = 0 from by rw [octOne_eq_scalar, octDot_scalar_left, h2_im, mul_zero]]
    have he2_12 : octDot e2 (octonionMul e1 e2) = 0 := by
      rw [octDot_comm, octDot_mul_right, octonionConj_eq_neg_of_real_zero h2_im,
        octonionMul_neg_right, octonionMul_imag_sq h2_im, h2_norm, neg_one_smul, neg_neg,
        octDot_comm, show octDot octOne e1 = 0 from by rw [octOne_eq_scalar, octDot_scalar_left, h1_im, mul_zero]]
    have he12_e3 : octDot (octonionMul e1 e2) e3 = 0 := by rw [octDot_comm, h3_12]
    have h_ii : octonionMul e1 (octonionMul e1 e3) = octonionMul (octonionMul e1 e1) e3 :=
      octMul_left_alternative e1 e3
    have h_jj : octonionMul e2 (octonionMul e2 e3) = octonionMul (octonionMul e2 e2) e3 :=
      octMul_left_alternative e2 e3
    have h_kk : octonionMul (octonionMul e1 e2) (octonionMul (octonionMul e1 e2) e3) =
        octonionMul (octonionMul (octonionMul e1 e2) (octonionMul e1 e2)) e3 :=
      octMul_left_alternative _ e3
    have h_ij : octonionMul e1 (octonionMul e2 e3) = octonionMul (octonionMul e2 e1) e3 :=
      hrule1_basis h1_im h2_im h1_norm h2_norm h12 h13 h23 he12_e3
    have h_ji : octonionMul e2 (octonionMul e1 e3) = octonionMul (octonionMul e1 e2) e3 :=
      hrule1_basis h2_im h1_im h2_norm h1_norm (octDot_comm e1 e2 ▸ h12) h23 h13 (by
        rw [show octonionMul e2 e1 = -octonionMul e1 e2 from eq_neg_of_add_eq_zero_right (by
          rw [octonionMul_imag_anticomm h1_im h2_im, h12, mul_zero, zero_smul]),
          octDot_neg_left, he12_e3, neg_zero])
    have h_ik : octonionMul e1 (octonionMul (octonionMul e1 e2) e3) =
        octonionMul (octonionMul (octonionMul e1 e2) e1) e3 :=
      hrule1_basis h1_im he12_im h1_norm he12_norm he1_12 h13 he12_e3 (by
        rw [octMul_left_alternative, octonionMul_imag_sq h1_im, h1_norm, neg_one_smul,
          octonionMul_neg_left, octonionMul_one_left, octDot_neg_left, h23, neg_zero])
    have h_ki : octonionMul (octonionMul e1 e2) (octonionMul e1 e3) =
        octonionMul (octonionMul e1 (octonionMul e1 e2)) e3 :=
      hrule1_basis he12_im h1_im he12_norm h1_norm (octDot_comm e1 _ ▸ he1_12) he12_e3 h13 (by
        rw [octMul_flexible,
          show octonionMul e2 e1 = -octonionMul e1 e2 from eq_neg_of_add_eq_zero_right (by
            rw [octonionMul_imag_anticomm h1_im h2_im, h12, mul_zero, zero_smul]),
          octonionMul_neg_right, octMul_left_alternative, octonionMul_imag_sq h1_im,
          h1_norm, neg_one_smul, octonionMul_neg_left, octonionMul_one_left, neg_neg, h23])
    have h_jk : octonionMul e2 (octonionMul (octonionMul e1 e2) e3) =
        octonionMul (octonionMul (octonionMul e1 e2) e2) e3 :=
      hrule1_basis h2_im he12_im h2_norm he12_norm he2_12 h23 he12_e3 (by
        rw [show octonionMul e2 (octonionMul e1 e2) = e1 from by
            have h21 : octonionMul e2 e1 = -octonionMul e1 e2 :=
              eq_neg_of_add_eq_zero_right (by
                rw [octonionMul_imag_anticomm h1_im h2_im, h12, mul_zero, zero_smul])
            rw [show octonionMul e1 e2 = -octonionMul e2 e1 from by rw [h21, neg_neg],
              octonionMul_neg_right, octMul_left_alternative,
              octonionMul_imag_sq h2_im, h2_norm, neg_one_smul, octonionMul_neg_left,
              octonionMul_one_left, neg_neg], h13])
    have h_kj : octonionMul (octonionMul e1 e2) (octonionMul e2 e3) =
        octonionMul (octonionMul e2 (octonionMul e1 e2)) e3 :=
      hrule1_basis he12_im h2_im he12_norm h2_norm (octDot_comm e2 _ ▸ he2_12) he12_e3 h23 (by
        rw [octMul_right_alternative, octonionMul_imag_sq h2_im, h2_norm, neg_one_smul,
          octonionMul_neg_right, octonionMul_one_right, octDot_neg_left, h13, neg_zero])
    rw [ha_exp, hb_exp]
    simp only [map_add, map_smul, hqi, hqj, hqk, mul_add, add_mul, smul_mul_assoc,
      mul_smul_comm, octonionMul_add_left, octonionMul_add_right, octonionMul_smul_left,
      octonionMul_smul_right, hφ.map_mul,
      h_ii, h_jj, h_kk, h_ij, h_ji, h_ik, h_ki, h_jk, h_kj]
    try rw [mul_comm b.imI a.imI]
    try rw [mul_comm b.imI a.imJ]
    try rw [mul_comm b.imI a.imK]
    try rw [mul_comm b.imJ a.imI]
    try rw [mul_comm b.imJ a.imJ]
    try rw [mul_comm b.imJ a.imK]
    try rw [mul_comm b.imK a.imI]
    try rw [mul_comm b.imK a.imJ]
    try rw [mul_comm b.imK a.imK]
    module
  have hrule1 : ∀ a b : Quaternion ℝ,
      octonionMul (φ a) (octonionMul (φ b) e3) = octonionMul (φ (b * a)) e3 := by
    intro a b
    let a0 : Quaternion ℝ := a.re • 1
    let aim : Quaternion ℝ := ⟨0, a.imI, a.imJ, a.imK⟩
    let b0 : Quaternion ℝ := b.re • 1
    let bim : Quaternion ℝ := ⟨0, b.imI, b.imJ, b.imK⟩
    have ha : a = a0 + aim := by apply Quaternion.ext <;> simp [a0, aim]
    have hb : b = b0 + bim := by apply Quaternion.ext <;> simp [b0, bim]
    have h_a0 : φ a0 = octonionScalar a.re := by
      rw [show a0 = a.re • 1 from rfl, map_smul, hφ.map_one, ← octonionScalar_smul, mul_one]
    have h_b0 : φ b0 = octonionScalar b.re := by
      rw [show b0 = b.re • 1 from rfl, map_smul, hφ.map_one, ← octonionScalar_smul, mul_one]
    rw [ha, hb, map_add, map_add, h_a0, h_b0]
    simp only [octonionMul_add_left, octonionMul_add_right, octonionMul_scalar_left,
      octonionMul_smul_right, mul_add, add_mul, map_add]
    have h_b0_aim : φ (b0 * aim) = b.re • φ aim := by
      rw [show b0 * aim = b.re • aim from by simp [b0], map_smul]
    have h_bim_a0 : φ (bim * a0) = a.re • φ bim := by
      rw [show bim * a0 = a.re • bim from by simp [a0], map_smul]
    have h_b0_a0 : φ (b0 * a0) = octonionScalar (b.re * a.re) := by
      rw [show b0 * a0 = (b.re * a.re) • (1 : Quaternion ℝ) from by
        simp [a0, b0, smul_smul, mul_comm],
        map_smul, hφ.map_one, ← octonionScalar_smul, mul_one]
    rw [h_b0_aim, h_bim_a0, h_b0_a0, hrule1_imag (show aim.re = 0 from rfl) (show bim.re = 0 from rfl),
      octonionMul_smul_left, octonionMul_smul_left, octonionMul_scalar_left,
      smul_add, smul_smul]
    abel
  have hrule2_conj : ∀ b : Quaternion ℝ,
      octonionConj (octonionMul (φ b) e3) = -octonionMul (φ b) e3 := by
    intro b
    let b0 : Quaternion ℝ := b.re • 1
    let bim : Quaternion ℝ := ⟨0, b.imI, b.imJ, b.imK⟩
    have hb : b = b0 + bim := by apply Quaternion.ext <;> simp [b0, bim]
    have h_b0 : φ b0 = octonionScalar b.re := by
      rw [show b0 = b.re • 1 from rfl, map_smul, hφ.map_one, ← octonionScalar_smul, mul_one]
    have hbim_im : octonionReal (φ bim) = 0 := hφ_im rfl
    have hcbim : octonionConj (φ bim) = -φ bim := octonionConj_eq_neg_of_real_zero hbim_im
    have hanti : octonionMul e3 (φ bim) = -octonionMul (φ bim) e3 :=
      eq_neg_of_add_eq_zero_right (by
        rw [octonionMul_imag_anticomm hbim_im h3_im, he3_perp bim, mul_zero, zero_smul])
    rw [hb, map_add, h_b0, octonionMul_add_left, octonionMul_scalar_left, octonionConj_add,
      octonionConj_smul, hce3, octonionConj_mul, hce3, hcbim, octonionMul_neg_left,
      octonionMul_neg_right, neg_neg, hanti]
    module
  have hrule3 : ∀ b a : Quaternion ℝ,
      octonionMul (octonionMul (φ b) e3) (φ a) = octonionMul (φ (b * star a)) e3 := by
    intro b a
    have h := congrArg octonionConj (hrule1 (star a) b)
    rw [octonionConj_mul, ← hφ.map_star, star_star, hrule2_conj, hrule2_conj,
      octonionMul_neg_left] at h
    exact neg_inj.mp h
  have hrule4_aux : ∀ x : Quaternion ℝ,
      octonionMul (octonionMul e3 (φ x)) e3 = -φ (star x) := by
    intro x
    let x0 : Quaternion ℝ := x.re • 1
    let xim : Quaternion ℝ := ⟨0, x.imI, x.imJ, x.imK⟩
    have hx : x = x0 + xim := by apply Quaternion.ext <;> simp [x0, xim]
    have h_x0 : φ x0 = octonionScalar x.re := by
      rw [show x0 = x.re • 1 from rfl, map_smul, hφ.map_one, ← octonionScalar_smul, mul_one]
    have hxim_im : octonionReal (φ xim) = 0 := hφ_im rfl
    have hanti : octonionMul e3 (φ xim) = -octonionMul (φ xim) e3 :=
      eq_neg_of_add_eq_zero_right (by
        rw [octonionMul_imag_anticomm hxim_im h3_im, he3_perp xim, mul_zero, zero_smul])
    have hsxim : star xim = -xim := by apply Quaternion.ext <;> simp [xim]
    have hsx0 : star x0 = x0 := by apply Quaternion.ext <;> simp [x0]
    have hx0_term : octonionMul (octonionMul e3 (φ x0)) e3 = -φ (star x0) := by
      rw [hsx0, h_x0, octonionMul_scalar_right, octonionMul_smul_left, he3sq,
        smul_neg, octOne_eq_scalar, ← octonionScalar_eq_smul]
    have hxim_term : octonionMul (octonionMul e3 (φ xim)) e3 = -φ (star xim) := by
      rw [hsxim, map_neg, neg_neg, hanti, octonionMul_neg_left,
        octMul_right_alternative, he3sq, octonionMul_neg_right, octonionMul_one_right, neg_neg]
    rw [hx, star_add, map_add, octonionMul_add_right, octonionMul_add_left,
      hx0_term, hxim_term, map_add, neg_add]
  have hrule4 : ∀ b d : Quaternion ℝ,
      octonionMul (octonionMul (φ b) e3) (octonionMul (φ d) e3) = -φ (star d * b) := by
    intro b d
    let b0 : Quaternion ℝ := b.re • 1
    let bim : Quaternion ℝ := ⟨0, b.imI, b.imJ, b.imK⟩
    have hb : b = b0 + bim := by apply Quaternion.ext <;> simp [b0, bim]
    have h_b0 : φ b0 = octonionScalar b.re := by
      rw [show b0 = b.re • 1 from rfl, map_smul, hφ.map_one, ← octonionScalar_smul, mul_one]
    have hbim_im : octonionReal (φ bim) = 0 := hφ_im rfl
    have hanti_b : octonionMul (φ bim) e3 = octonionMul e3 (φ (star bim)) := by
      have hs : star bim = -bim := by apply Quaternion.ext <;> simp [bim]
      rw [hs, map_neg, octonionMul_neg_right]
      exact eq_neg_of_add_eq_zero_left (by
        rw [octonionMul_imag_anticomm hbim_im h3_im, he3_perp bim, mul_zero, zero_smul])
    have hb0_case : octonionMul (octonionMul (φ b0) e3) (octonionMul (φ d) e3) =
        -φ (star d * b0) := by
      rw [h_b0, octonionMul_scalar_left, octonionMul_smul_left]
      have hed : octonionMul e3 (octonionMul (φ d) e3) = -φ (star d) := by
        rw [← octMul_flexible, hrule4_aux]
      rw [hed, show star d * b0 = b.re • star d from by simp [b0],
        map_smul, smul_neg]
    have hbim_case : octonionMul (octonionMul (φ bim) e3) (octonionMul (φ d) e3) =
        -φ (star d * bim) := by
      rw [hanti_b, octMul_moufang_middle, ← hφ.map_mul, hrule4_aux, star_mul, star_star]
    rw [hb, map_add, octonionMul_add_left, octonionMul_add_left, hb0_case, hbim_case,
      mul_add, map_add, neg_add]
  let Φlin := octExtendQuatLinear e1 e2 e3
  have hΦ_one : Φlin octOne = octOne := by
    change φ (1 : Quaternion ℝ) + octonionMul (φ 0) e3 = octOne
    rw [hφ.map_one, map_zero, octonionMul_zero_left, add_zero]; rfl
  have hΦ_mul : ∀ x y : Octonion, Φlin (octonionMul x y) = octonionMul (Φlin x) (Φlin y) := by
    intro x y
    change φ (x.1 * y.1 - star y.2 * x.2) + octonionMul (φ (y.2 * x.1 + x.2 * star y.1)) e3 =
      octonionMul (φ x.1 + octonionMul (φ x.2) e3) (φ y.1 + octonionMul (φ y.2) e3)
    simp only [map_sub, map_add, hφ.map_mul, octonionMul_add_left, octonionMul_add_right,
      hrule1, hrule3, hrule4]
    abel
  have hΦ_norm : ∀ x : Octonion, octNormSq (Φlin x) = octNormSq x := by
    intro x
    change octNormSq (φ x.1 + octonionMul (φ x.2) e3) = octNormSq x
    have horth : octDot (φ x.1) (octonionMul (φ x.2) e3) = 0 := by
      rw [octDot_comm, octDot_mul_right,
        show octonionConj e3 = -e3 from hce3,
        show octonionMul (φ x.1) (-e3) = -octonionMul (φ x.1) e3 from octonionMul_neg_right _ _,
        octDot_neg_right, octDot_comm,
        show octDot (octonionMul (φ x.1) e3) (φ x.2) =
            octDot e3 (octonionMul (octonionConj (φ x.1)) (φ x.2)) from
          octDot_mul_left (φ x.1) e3 (φ x.2),
        ← hφ.map_star, ← hφ.map_mul, octDot_comm, he3_perp, neg_zero]
    rw [octNormSq_add, horth, mul_zero, add_zero, octNormSq_mul, h3_norm, mul_one,
      hφ_norm, hφ_norm]
    rw [octNormSq_eq_coords]
    simp [quatNormSq]; ring
  have hΦ_inj : Function.Injective Φlin := by
    intro x y hxy
    have hd : Φlin (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hn : octNormSq (x - y) = 0 := by
      rw [← hΦ_norm (x - y), hd, (octNormSq_eq_zero 0).mpr rfl]
    exact sub_eq_zero.mp ((octNormSq_eq_zero (x - y)).mp hn)
  have : FiniteDimensional ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have hΦ_surj : Function.Surjective Φlin := LinearMap.injective_iff_surjective.mp hΦ_inj
  exact ⟨⟨hΦ_inj, hΦ_surj⟩, hΦ_one, hΦ_mul⟩

def octAutoOfBasicTriple (e1 e2 e3 : Octonion)
    (h1_im : octonionReal e1 = 0) (h2_im : octonionReal e2 = 0) (h3_im : octonionReal e3 = 0)
    (h1_norm : octNormSq e1 = 1) (h2_norm : octNormSq e2 = 1) (h3_norm : octNormSq e3 = 1)
    (h12 : octDot e1 e2 = 0) (h13 : octDot e1 e3 = 0) (h23 : octDot e2 e3 = 0)
    (h3_12 : octDot e3 (octonionMul e1 e2) = 0) : OctonionAutomorphism where
  equiv := LinearEquiv.ofBijective (octExtendQuatLinear e1 e2 e3)
    (octAutoOfBasicTriple_props e1 e2 e3 h1_im h2_im h3_im h1_norm h2_norm h3_norm h12 h13 h23 h3_12).1
  map_one :=
    (octAutoOfBasicTriple_props e1 e2 e3 h1_im h2_im h3_im h1_norm h2_norm h3_norm h12 h13 h23 h3_12).2.1
  map_mul :=
    (octAutoOfBasicTriple_props e1 e2 e3 h1_im h2_im h3_im h1_norm h2_norm h3_norm h12 h13 h23 h3_12).2.2

theorem octAutoOfBasicTriple_I (e1 e2 e3 : Octonion)
    (h1_im : octonionReal e1 = 0) (h2_im : octonionReal e2 = 0) (h3_im : octonionReal e3 = 0)
    (h1_norm : octNormSq e1 = 1) (h2_norm : octNormSq e2 = 1) (h3_norm : octNormSq e3 = 1)
    (h12 : octDot e1 e2 = 0) (h13 : octDot e1 e3 = 0) (h23 : octDot e2 e3 = 0)
    (h3_12 : octDot e3 (octonionMul e1 e2) = 0) :
    (octAutoOfBasicTriple e1 e2 e3 h1_im h2_im h3_im h1_norm h2_norm h3_norm h12 h13 h23 h3_12).equiv octI = e1 := by
  change octExtendQuatLinear e1 e2 e3 octI = e1
  simp [octExtendQuatLinear, octBasisQuat, octI, octonionMul_zero_left]

theorem octAutoOfBasicTriple_J (e1 e2 e3 : Octonion)
    (h1_im : octonionReal e1 = 0) (h2_im : octonionReal e2 = 0) (h3_im : octonionReal e3 = 0)
    (h1_norm : octNormSq e1 = 1) (h2_norm : octNormSq e2 = 1) (h3_norm : octNormSq e3 = 1)
    (h12 : octDot e1 e2 = 0) (h13 : octDot e1 e3 = 0) (h23 : octDot e2 e3 = 0)
    (h3_12 : octDot e3 (octonionMul e1 e2) = 0) :
    (octAutoOfBasicTriple e1 e2 e3 h1_im h2_im h3_im h1_norm h2_norm h3_norm h12 h13 h23 h3_12).equiv octJ = e2 := by
  change octExtendQuatLinear e1 e2 e3 octJ = e2
  simp [octExtendQuatLinear, octBasisQuat, octJ, octonionMul_zero_left]

theorem octAutoOfBasicTriple_L (e1 e2 e3 : Octonion)
    (h1_im : octonionReal e1 = 0) (h2_im : octonionReal e2 = 0) (h3_im : octonionReal e3 = 0)
    (h1_norm : octNormSq e1 = 1) (h2_norm : octNormSq e2 = 1) (h3_norm : octNormSq e3 = 1)
    (h12 : octDot e1 e2 = 0) (h13 : octDot e1 e3 = 0) (h23 : octDot e2 e3 = 0)
    (h3_12 : octDot e3 (octonionMul e1 e2) = 0) :
    (octAutoOfBasicTriple e1 e2 e3 h1_im h2_im h3_im h1_norm h2_norm h3_norm h12 h13 h23 h3_12).equiv octL = e3 := by
  change octExtendQuatLinear e1 e2 e3 octL = e3
  simp [octExtendQuatLinear, octBasisQuat, octL, octonionMul_one_left]

private theorem octDot_I_one : octDot octI octOne = 0 := by
  rw [octDot_eq_coords]; simp [octI, octOne, octonionScalar]

private theorem octDot_I_I : octDot octI octI = 1 := by
  rw [octDot_eq_coords]; simp [octI]

private theorem octDot_I_J : octDot octI octJ = 0 := by
  rw [octDot_eq_coords]; simp [octI, octJ]

private theorem octDot_I_K : octDot octI octK = 0 := by
  rw [octDot_eq_coords]; simp [octI, octK]

private theorem octDot_I_L : octDot octI octL = 0 := by
  rw [octDot_eq_coords]; simp [octI, octL]

private theorem octDot_J_one : octDot octJ octOne = 0 := by
  rw [octDot_eq_coords]; simp [octJ, octOne, octonionScalar]

private theorem octDot_J_J : octDot octJ octJ = 1 := by
  rw [octDot_eq_coords]; simp [octJ]

private theorem octDot_J_K : octDot octJ octK = 0 := by
  rw [octDot_eq_coords]; simp [octJ, octK]

private theorem octDot_J_L : octDot octJ octL = 0 := by
  rw [octDot_eq_coords]; simp [octJ, octL]

private theorem octDot_K_one : octDot octK octOne = 0 := by
  rw [octDot_eq_coords]; simp [octK, octOne, octonionScalar]

private theorem octDot_K_K : octDot octK octK = 1 := by
  rw [octDot_eq_coords]; simp [octK]

private theorem octDot_K_L : octDot octK octL = 0 := by
  rw [octDot_eq_coords]; simp [octK, octL]

def conjIAutomorphism : OctonionAutomorphism :=
  octAutoOfBasicTriple (-octI) octJ octL
    (by rw [octonionReal_neg, show octonionReal octI = 0 from rfl, neg_zero])
    rfl rfl
    (by rw [octNormSq_neg, octNormSq_eq_coords]; simp [octI])
    (by rw [octNormSq_eq_coords]; simp [octJ])
    (by rw [octNormSq_eq_coords]; simp [octL])
    (by rw [octDot_neg_left, octDot_I_J, neg_zero])
    (by rw [octDot_neg_left, octDot_I_L, neg_zero])
    (by exact octDot_J_L)
    (by
      rw [octonionMul_neg_left, octK_eq_mul, octDot_neg_right, octDot_comm, octDot_K_L, neg_zero])

theorem conjIAutomorphism_I : conjIAutomorphism.equiv octI = -octI :=
  octAutoOfBasicTriple_I (-octI) octJ octL _ _ _ _ _ _ _ _ _ _

theorem conjIAutomorphism_J : conjIAutomorphism.equiv octJ = octJ :=
  octAutoOfBasicTriple_J (-octI) octJ octL _ _ _ _ _ _ _ _ _ _

theorem conjIAutomorphism_L : conjIAutomorphism.equiv octL = octL :=
  octAutoOfBasicTriple_L (-octI) octJ octL _ _ _ _ _ _ _ _ _ _

theorem conjIAutomorphism_K : conjIAutomorphism.equiv octK = -octK := by
  rw [← octK_eq_mul, conjIAutomorphism.map_mul, conjIAutomorphism_I, conjIAutomorphism_J,
    octonionMul_neg_left, octK_eq_mul]

private theorem octNormSq_sub_proj (x u : Octonion) (hu : octNormSq u = 1) :
    octNormSq (x - octDot x u • u) = octNormSq x - octDot x u ^ 2 := by
  rw [octNormSq_sub, octNormSq_smul, hu, mul_one, octDot_smul_right]
  ring

private theorem exists_ortho_e3 (e1 e2 : Octonion)
    (h1_im : octonionReal e1 = 0) (h2_im : octonionReal e2 = 0)
    (h1_norm : octNormSq e1 = 1) (h2_norm : octNormSq e2 = 1)
    (h12 : octDot e1 e2 = 0) :
    ∃ e3 : Octonion, octonionReal e3 = 0 ∧ octNormSq e3 = 1 ∧
      octDot e1 e3 = 0 ∧ octDot e2 e3 = 0 ∧ octDot e3 (octonionMul e1 e2) = 0 := by
  let e12 := octonionMul e1 e2
  have h12_im : octonionReal e12 = 0 := by
    rw [octonionReal_mul_imag_eq h1_im h2_im, h12, neg_zero]
  have h12_norm : octNormSq e12 = 1 := by rw [octNormSq_mul, h1_norm, h2_norm, mul_one]
  have h1_12 : octDot e1 e12 = 0 := by
    rw [octDot_comm, octDot_mul_left, octonionConj_eq_neg_of_real_zero h1_im,
      octonionMul_neg_left, octonionMul_imag_sq h1_im, h1_norm, neg_one_smul, neg_neg,
      octDot_comm, show octDot octOne e2 = 0 from by rw [octOne_eq_scalar, octDot_scalar_left, h2_im, mul_zero]]
  have h2_12 : octDot e2 e12 = 0 := by
    rw [octDot_comm, octDot_mul_right, octonionConj_eq_neg_of_real_zero h2_im,
      octonionMul_neg_right, octonionMul_imag_sq h2_im, h2_norm, neg_one_smul, neg_neg,
      octDot_comm, show octDot octOne e1 = 0 from by rw [octOne_eq_scalar, octDot_scalar_left, h1_im, mul_zero]]
  let b : Fin 4 → Octonion := ![octI, octJ, octK, octL]
  let w : Fin 4 → Octonion := fun k =>
    b k - octDot (b k) e1 • e1 - octDot (b k) e2 • e2 - octDot (b k) e12 • e12
  have hb_im : ∀ k : Fin 4, octonionReal (b k) = 0 := by
    intro k; fin_cases k <;> rfl
  have hw_im : ∀ k : Fin 4, octonionReal (w k) = 0 := by
    intro k; simp [w, octonionReal_sub, octonionReal_smul, hb_im k, h1_im, h2_im, h12_im]
  have hw_1 : ∀ k : Fin 4, octDot e1 (w k) = 0 := by
    intro k
    simp only [w, octDot_sub_right, octDot_smul_right, octDot_self, h1_norm,
      h12, h1_12, mul_one, mul_zero, octDot_comm e1 (b k), sub_self]
  have hw_2 : ∀ k : Fin 4, octDot e2 (w k) = 0 := by
    intro k
    simp only [w, octDot_sub_right, octDot_smul_right, octDot_self, h2_norm,
      octDot_comm e2 e1, h12, h2_12, mul_one, mul_zero, sub_zero, octDot_comm e2 (b k), sub_self]
  have hw_12 : ∀ k : Fin 4, octDot (w k) e12 = 0 := by
    intro k
    simp only [w, octDot_sub_left, octDot_smul_left, octDot_self, h12_norm,
      h1_12, h2_12, mul_one, mul_zero, sub_zero, sub_self]
  have hbessel : ∀ u : Octonion, octNormSq u = 1 →
      ∑ k : Fin 4, octDot (b k) u ^ 2 ≤ 1 := by
    intro u hu
    have hdotI : octDot octI u = u.1.imI := by
      rw [octDot_eq_coords]
      change 0 * u.1.re + 1 * u.1.imI + 0 * u.1.imJ + 0 * u.1.imK +
        0 * u.2.re + 0 * u.2.imI + 0 * u.2.imJ + 0 * u.2.imK = u.1.imI
      ring
    have hdotJ : octDot octJ u = u.1.imJ := by
      rw [octDot_eq_coords]
      change 0 * u.1.re + 0 * u.1.imI + 1 * u.1.imJ + 0 * u.1.imK +
        0 * u.2.re + 0 * u.2.imI + 0 * u.2.imJ + 0 * u.2.imK = u.1.imJ
      ring
    have hdotK : octDot octK u = u.1.imK := by
      rw [octDot_eq_coords]
      change 0 * u.1.re + 0 * u.1.imI + 0 * u.1.imJ + 1 * u.1.imK +
        0 * u.2.re + 0 * u.2.imI + 0 * u.2.imJ + 0 * u.2.imK = u.1.imK
      ring
    have hdotL : octDot octL u = u.2.re := by
      rw [octDot_eq_coords]
      change 0 * u.1.re + 0 * u.1.imI + 0 * u.1.imJ + 0 * u.1.imK +
        1 * u.2.re + 0 * u.2.imI + 0 * u.2.imJ + 0 * u.2.imK = u.2.re
      ring
    rw [Fin.sum_univ_four]
    have hb0 : b 0 = octI := rfl
    have hb1 : b 1 = octJ := rfl
    have hb2 : b 2 = octK := rfl
    have hb3 : b 3 = octL := rfl
    rw [hb0, hb1, hb2, hb3, hdotI, hdotJ, hdotK, hdotL]
    rw [octNormSq_eq_coords] at hu
    nlinarith [sq_nonneg u.1.re, sq_nonneg u.2.imI, sq_nonneg u.2.imJ, sq_nonneg u.2.imK]
  have hnorm_w : ∀ k : Fin 4, octNormSq (w k) =
      1 - octDot (b k) e1 ^ 2 - octDot (b k) e2 ^ 2 - octDot (b k) e12 ^ 2 := by
    intro k
    have hbk : octNormSq (b k) = 1 := by
      fin_cases k <;> rw [octNormSq_eq_coords] <;> simp [b, octI, octJ, octK, octL]
    let w1 := b k - octDot (b k) e1 • e1
    let w2 := w1 - octDot (b k) e2 • e2
    have hw1_e2 : octDot w1 e2 = octDot (b k) e2 := by
      simp [w1, octDot_sub_left, octDot_smul_left, h12]
    have hw2_e12 : octDot w2 e12 = octDot (b k) e12 := by
      simp [w2, w1, octDot_sub_left, octDot_smul_left, h1_12, h2_12]
    have h1 := octNormSq_sub_proj (b k) e1 h1_norm
    have h2 : octNormSq w2 = octNormSq w1 - octDot (b k) e2 ^ 2 := by
      simpa only [hw1_e2] using octNormSq_sub_proj w1 e2 h2_norm
    have h3 : octNormSq (w k) = octNormSq w2 - octDot (b k) e12 ^ 2 := by
      simpa only [hw2_e12] using octNormSq_sub_proj w2 e12 h12_norm
    linarith [hbk, h1, h2, h3]
  have hsum_pos : 0 < ∑ k : Fin 4, octNormSq (w k) := by
    have hs1 := hbessel e1 h1_norm
    have hs2 := hbessel e2 h2_norm
    have hs3 := hbessel e12 h12_norm
    rw [Fin.sum_univ_four, hnorm_w 0, hnorm_w 1, hnorm_w 2, hnorm_w 3]
    rw [Fin.sum_univ_four] at hs1 hs2 hs3
    linarith
  have hnotall : ∃ k : Fin 4, w k ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑ k : Fin 4, octNormSq (w k) = 0 := by
      simp [h, (octNormSq_eq_zero 0).mpr rfl]
    linarith
  obtain ⟨k, hk⟩ := hnotall
  have hnk : 0 < octNormSq (w k) :=
    lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm (fun h => hk ((octNormSq_eq_zero _).mp h)))
  let r := Real.sqrt (octNormSq (w k))
  have hr : 0 < r := Real.sqrt_pos.mpr hnk
  have hrsq : r ^ 2 = octNormSq (w k) := Real.sq_sqrt hnk.le
  refine ⟨(1 / r) • w k, ?_, ?_, ?_, ?_, ?_⟩
  · simp [octonionReal_smul, hw_im k]
  · rw [octNormSq_smul, div_pow, one_pow, hrsq]
    field_simp [hnk.ne']
  · rw [octDot_smul_right, hw_1 k, mul_zero]
  · rw [octDot_smul_right, hw_2 k, mul_zero]
  · rw [octDot_smul_left, hw_12 k, mul_zero]

theorem exists_octAuto_imag_to_I (w : Octonion) (hw : octonionReal w = 0) :
    ∃ α : OctonionAutomorphism, ∃ r : ℝ, 0 ≤ r ∧ α.equiv w = r • octI := by
  by_cases hw0 : w = 0
  · refine ⟨OctonionAutomorphism.refl, 0, le_rfl, ?_⟩
    simp [hw0]
  have hnw : 0 < octNormSq w :=
    lt_of_le_of_ne (octNormSq_nonneg w) (Ne.symm (fun h => hw0 ((octNormSq_eq_zero w).mp h)))
  let r := Real.sqrt (octNormSq w)
  have hr : 0 < r := Real.sqrt_pos.mpr hnw
  have hrsq : r ^ 2 = octNormSq w := Real.sq_sqrt hnw.le
  let e1 := (1 / r) • w
  have he1_im : octonionReal e1 = 0 := by simp [e1, octonionReal_smul, hw]
  have he1_norm : octNormSq e1 = 1 := by
    rw [octNormSq_smul, div_pow, one_pow, hrsq]; field_simp [hnw.ne']
  let v1 := octI - octDot octI e1 • e1
  let v2 := octJ - octDot octJ e1 • e1
  have hv12 : v1 ≠ 0 ∨ v2 ≠ 0 := by
    by_contra h
    push Not at h
    have hi : octI = octDot octI e1 • e1 := sub_eq_zero.mp h.1
    have hj : octJ = octDot octJ e1 • e1 := sub_eq_zero.mp h.2
    have h0 : octDot octI octJ = 0 := octDot_I_J
    conv_lhs at h0 => rw [hi, hj]
    rw [octDot_smul_left (octDot octI e1) e1, octDot_smul_right (octDot octJ e1) e1 e1,
      octDot_self, he1_norm, mul_one] at h0
    have hi_n : octNormSq octI = 1 := by rw [octNormSq_eq_coords]; simp [octI]
    have hj_n : octNormSq octJ = 1 := by rw [octNormSq_eq_coords]; simp [octJ]
    rw [hi, octNormSq_smul, he1_norm, mul_one] at hi_n
    rw [hj, octNormSq_smul, he1_norm, mul_one] at hj_n
    nlinarith [sq_nonneg (octDot octI e1), sq_nonneg (octDot octJ e1)]
  have hex_e2 : ∃ e2 : Octonion, octonionReal e2 = 0 ∧ octNormSq e2 = 1 ∧ octDot e1 e2 = 0 := by
    rcases hv12 with hv1 | hv2
    · have hnv1 : 0 < octNormSq v1 :=
        lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm (fun h => hv1 ((octNormSq_eq_zero _).mp h)))
      let s := Real.sqrt (octNormSq v1)
      refine ⟨(1 / s) • v1, ?_, ?_, ?_⟩
      · rw [octonionReal_smul, octonionReal_sub, octonionReal_smul, he1_im,
          show octonionReal octI = 0 from rfl]; ring
      · rw [octNormSq_smul, div_pow, one_pow, Real.sq_sqrt hnv1.le]; field_simp [hnv1.ne']
      · rw [octDot_smul_right, octDot_comm]
        have hv1_e1 : octDot v1 e1 = 0 := by
          dsimp only [v1]
          rw [octDot_sub_left, octDot_smul_left, octDot_self, he1_norm, mul_one, sub_self]
        rw [hv1_e1, mul_zero]
    · have hnv2 : 0 < octNormSq v2 :=
        lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm (fun h => hv2 ((octNormSq_eq_zero _).mp h)))
      let s := Real.sqrt (octNormSq v2)
      refine ⟨(1 / s) • v2, ?_, ?_, ?_⟩
      · rw [octonionReal_smul, octonionReal_sub, octonionReal_smul, he1_im,
          show octonionReal octJ = 0 from rfl]; ring
      · rw [octNormSq_smul, div_pow, one_pow, Real.sq_sqrt hnv2.le]; field_simp [hnv2.ne']
      · rw [octDot_smul_right, octDot_comm]
        have hv2_e1 : octDot v2 e1 = 0 := by
          dsimp only [v2]
          rw [octDot_sub_left, octDot_smul_left, octDot_self, he1_norm, mul_one, sub_self]
        rw [hv2_e1, mul_zero]
  obtain ⟨e2, he2_im, he2_norm, h12⟩ := hex_e2
  obtain ⟨e3, he3_im, he3_norm, h13, h23, h3_12⟩ :=
    exists_ortho_e3 e1 e2 he1_im he2_im he1_norm he2_norm h12
  let β := octAutoOfBasicTriple e1 e2 e3 he1_im he2_im he3_im he1_norm he2_norm he3_norm h12 h13 h23 h3_12
  refine ⟨β.symm, r, hr.le, ?_⟩
  apply β.equiv.injective
  dsimp only [β]
  simp only [OctonionAutomorphism.symm_apply, LinearEquiv.apply_symm_apply, map_smul,
    octAutoOfBasicTriple_I]
  change w = r • ((1 / r) • w)
  rw [smul_smul, mul_one_div_cancel hr.ne', one_smul]

theorem exists_octAuto_fix_I_to_IJ (X : Octonion) :
    ∃ α : OctonionAutomorphism, α.equiv octI = octI ∧
      ∃ x0 x1 x2 : ℝ, 0 ≤ x2 ∧ α.equiv X = x0 • octOne + x1 • octI + x2 • octJ := by
  let x0 := octonionReal X
  let x1 := octDot X octI
  let Xperp := X - x0 • octOne - x1 • octI
  have hXp_im : octonionReal Xperp = 0 := by
    simp [Xperp, x0, octonionReal_sub, octonionReal_smul, octonionReal_one,
      show octonionReal octI = 0 from rfl]
  have hXp_I : octDot octI Xperp = 0 := by
    dsimp only [Xperp, x1]
    rw [octDot_sub_right, octDot_sub_right, octDot_smul_right, octDot_smul_right,
      octDot_I_one, octDot_I_I, octDot_comm octI X, mul_zero, mul_one, sub_zero, sub_self]
  by_cases hXp0 : Xperp = 0
  · refine ⟨OctonionAutomorphism.refl, rfl, x0, x1, 0, le_rfl, ?_⟩
    have hX : X = x0 • octOne + x1 • octI := sub_eq_zero.mp (by
      rw [← hXp0]; dsimp only [Xperp]; abel)
    simp [hX]
  have hnXp : 0 < octNormSq Xperp :=
    lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm (fun h => hXp0 ((octNormSq_eq_zero _).mp h)))
  let x2 := Real.sqrt (octNormSq Xperp)
  have hx2 : 0 < x2 := Real.sqrt_pos.mpr hnXp
  let e2 := (1 / x2) • Xperp
  have he1_im : octonionReal octI = 0 := rfl
  have he1_norm : octNormSq octI = 1 := by rw [octNormSq_eq_coords]; simp [octI]
  have he2_im : octonionReal e2 = 0 := by simp [e2, octonionReal_smul, hXp_im]
  have he2_norm : octNormSq e2 = 1 := by
    rw [octNormSq_smul, div_pow, one_pow, Real.sq_sqrt hnXp.le]; field_simp [hnXp.ne']
  have h12 : octDot octI e2 = 0 := by rw [octDot_smul_right, hXp_I, mul_zero]
  obtain ⟨e3, he3_im, he3_norm, h13, h23, h3_12⟩ :=
    exists_ortho_e3 octI e2 he1_im he2_im he1_norm he2_norm h12
  let β := octAutoOfBasicTriple octI e2 e3 he1_im he2_im he3_im he1_norm he2_norm he3_norm h12 h13 h23 h3_12
  refine ⟨β.symm, ?_, x0, x1, x2, hx2.le, ?_⟩
  · apply β.equiv.injective
    dsimp only [β]
    simp only [OctonionAutomorphism.symm_apply, LinearEquiv.apply_symm_apply,
      octAutoOfBasicTriple_I]
  · apply β.equiv.injective
    dsimp only [β]
    simp only [OctonionAutomorphism.symm_apply, LinearEquiv.apply_symm_apply,
      map_add, map_smul, OctonionAutomorphism.map_one, octAutoOfBasicTriple_I,
      octAutoOfBasicTriple_J]
    have he2x : x2 • e2 = Xperp := by
      dsimp [e2]; rw [smul_smul, mul_one_div_cancel hx2.ne', one_smul]
    rw [he2x]
    dsimp [Xperp]
    abel

theorem exists_octAuto_fix_IJ_to_IJL (Y : Octonion) :
    ∃ α : OctonionAutomorphism, α.equiv octI = octI ∧ α.equiv octJ = octJ ∧ α.equiv octK = octK ∧
      ∃ y0 y1 y2 y3 y4 : ℝ, 0 ≤ y4 ∧
        α.equiv Y = y0 • octOne + y1 • octI + y2 • octJ + y3 • octK + y4 • octL := by
  let y0 := octonionReal Y
  let y1 := octDot Y octI
  let y2 := octDot Y octJ
  let y3 := octDot Y octK
  let Yperp := Y - y0 • octOne - y1 • octI - y2 • octJ - y3 • octK
  have hYp_im : octonionReal Yperp = 0 := by
    simp [Yperp, y0, octonionReal_sub, octonionReal_smul, octonionReal_one,
      show octonionReal octI = 0 from rfl, show octonionReal octJ = 0 from rfl,
      show octonionReal octK = 0 from rfl]
  have hYp_I : octDot octI Yperp = 0 := by
    dsimp only [Yperp, y1]
    simp only [octDot_sub_right, octDot_smul_right, octDot_I_one, octDot_I_I,
      octDot_I_J, octDot_I_K, octDot_comm octI Y, mul_zero, mul_one, sub_zero, sub_self]
  have hYp_J : octDot octJ Yperp = 0 := by
    dsimp only [Yperp, y2]
    simp only [octDot_sub_right, octDot_smul_right, octDot_J_one, octDot_comm octJ octI,
      octDot_I_J, octDot_J_J, octDot_J_K, octDot_comm octJ Y, mul_zero, mul_one, sub_zero, sub_self]
  have hYp_K : octDot Yperp (octonionMul octI octJ) = 0 := by
    rw [octK_eq_mul]
    dsimp only [Yperp, y3]
    simp only [octDot_sub_left, octDot_smul_left, octDot_comm octOne octK, octDot_K_one,
      octDot_I_K, octDot_J_K, octDot_K_K, mul_zero, mul_one, sub_zero, sub_self]
  by_cases hYp0 : Yperp = 0
  · refine ⟨OctonionAutomorphism.refl, rfl, rfl, rfl, y0, y1, y2, y3, 0, le_rfl, ?_⟩
    have hY : Y = y0 • octOne + y1 • octI + y2 • octJ + y3 • octK := sub_eq_zero.mp (by
      rw [← hYp0]; dsimp only [Yperp]; abel)
    simp [hY]
  have hnYp : 0 < octNormSq Yperp :=
    lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm (fun h => hYp0 ((octNormSq_eq_zero _).mp h)))
  let y4 := Real.sqrt (octNormSq Yperp)
  have hy4 : 0 < y4 := Real.sqrt_pos.mpr hnYp
  let e3 := (1 / y4) • Yperp
  have he1_im : octonionReal octI = 0 := rfl
  have he2_im : octonionReal octJ = 0 := rfl
  have he3_im : octonionReal e3 = 0 := by simp [e3, octonionReal_smul, hYp_im]
  have he1_norm : octNormSq octI = 1 := by rw [octNormSq_eq_coords]; simp [octI]
  have he2_norm : octNormSq octJ = 1 := by rw [octNormSq_eq_coords]; simp [octJ]
  have he3_norm : octNormSq e3 = 1 := by
    rw [octNormSq_smul, div_pow, one_pow, Real.sq_sqrt hnYp.le]; field_simp [hnYp.ne']
  have h12 : octDot octI octJ = 0 := octDot_I_J
  have h13 : octDot octI e3 = 0 := by rw [octDot_smul_right, hYp_I, mul_zero]
  have h23 : octDot octJ e3 = 0 := by rw [octDot_smul_right, hYp_J, mul_zero]
  have h3_12 : octDot e3 (octonionMul octI octJ) = 0 := by rw [octDot_smul_left, hYp_K, mul_zero]
  let β := octAutoOfBasicTriple octI octJ e3 he1_im he2_im he3_im he1_norm he2_norm he3_norm h12 h13 h23 h3_12
  have hβK : β.equiv octK = octK := by
    rw [← octK_eq_mul, β.map_mul]
    dsimp only [β]
    rw [octAutoOfBasicTriple_I, octAutoOfBasicTriple_J, octK_eq_mul]
  refine ⟨β.symm, ?_, ?_, ?_, y0, y1, y2, y3, y4, hy4.le, ?_⟩
  · apply β.equiv.injective
    dsimp only [β]
    simp only [OctonionAutomorphism.symm_apply, LinearEquiv.apply_symm_apply, octAutoOfBasicTriple_I]
  · apply β.equiv.injective
    dsimp only [β]
    simp only [OctonionAutomorphism.symm_apply, LinearEquiv.apply_symm_apply, octAutoOfBasicTriple_J]
  · apply β.equiv.injective
    simp only [OctonionAutomorphism.symm_apply, LinearEquiv.apply_symm_apply, hβK]
  · apply β.equiv.injective
    dsimp only [β] at hβK ⊢
    simp only [OctonionAutomorphism.symm_apply, LinearEquiv.apply_symm_apply,
      map_add, map_smul, OctonionAutomorphism.map_one, octAutoOfBasicTriple_I,
      octAutoOfBasicTriple_J, octAutoOfBasicTriple_L]
    rw [hβK]
    have he3y : y4 • e3 = Yperp := by
      dsimp [e3]; rw [smul_smul, mul_one_div_cancel hy4.ne', one_smul]
    rw [he3y]
    dsimp [Yperp]
    abel

/-! ## Section 5: Artin / Quaternionic Containment & Subalgebra Classification -/

theorem octonionAutomorphism_comp_isQuatEmbedding (α : OctonionAutomorphism)
    {φ : Quaternion ℝ →ₗ[ℝ] Octonion} (hφ : IsQuatEmbedding φ) :
    IsQuatEmbedding (α.equiv.toLinearMap.comp φ) where
  map_one := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hφ.map_one, ← octOne_eq_scalar, α.map_one, octOne_eq_scalar]
  map_mul p q := by simp [hφ.map_mul, α.map_mul]
  map_star q := by simp [hφ.map_star, α.map_conj]
  map_re q := by simp [α.map_real, hφ.map_re]
  injective := α.equiv.injective.comp hφ.injective

private theorem quatEmbed1_mk_eq (a b c d : ℝ) :
    quatEmbed1 ⟨a, b, c, d⟩ = a • octOne + b • octI + c • octJ + d • octK := by
  have h1 : quatEmbed1 (1 : Quaternion ℝ) = octOne := by
    rw [quatEmbed1_apply]; apply oct_ext <;> simp [octOne, octonionScalar]
  have hi : quatEmbed1 ⟨0, 1, 0, 0⟩ = octI := by
    rw [quatEmbed1_apply]; apply oct_ext <;> simp [octI]
  have hj : quatEmbed1 ⟨0, 0, 1, 0⟩ = octJ := by
    rw [quatEmbed1_apply]; apply oct_ext <;> simp [octJ]
  have hk : quatEmbed1 ⟨0, 0, 0, 1⟩ = octK := by
    rw [quatEmbed1_apply]; apply oct_ext <;> simp [octK]
  have hq : (⟨a, b, c, d⟩ : Quaternion ℝ) =
      a • 1 + b • ⟨0, 1, 0, 0⟩ + c • ⟨0, 0, 1, 0⟩ + d • ⟨0, 0, 0, 1⟩ := by
    apply Quaternion.ext <;> simp
  rw [hq, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, hi, hj, hk]

private theorem oct_basis_expand (z : Octonion) :
    z = z.1.re • octOne + z.1.imI • octI + z.1.imJ • octJ + z.1.imK • octK +
      z.2.re • octL + z.2.imI • octS + z.2.imJ • octR + z.2.imK • octT := by
  have h12 : z = quatEmbed1 z.1 + octonionMul (quatEmbed1 z.2) octL := by
    have hm : octonionMul (quatEmbed1 z.2) octL = ((0, z.2) : Octonion) := by
      apply oct_ext <;> simp [quatEmbed1_apply, octonionMul, octL]
    apply oct_ext
    · rw [oct_fst_add, quatEmbed1_apply, hm]; simp
    · rw [oct_fst_add, quatEmbed1_apply, hm]; simp
    · rw [oct_fst_add, quatEmbed1_apply, hm]; simp
    · rw [oct_fst_add, quatEmbed1_apply, hm]; simp
    · rw [oct_snd_add, quatEmbed1_apply, hm]; simp
    · rw [oct_snd_add, quatEmbed1_apply, hm]; simp
    · rw [oct_snd_add, quatEmbed1_apply, hm]; simp
    · rw [oct_snd_add, quatEmbed1_apply, hm]; simp
  have hIL : octonionMul octI octL = octS := by
    apply oct_ext <;> simp [octonionMul, octI, octL, octS]
  have hJL : octonionMul octJ octL = octR := by
    apply oct_ext <;> simp [octonionMul, octJ, octL, octR]
  have hKL : octonionMul octK octL = octT := by
    apply oct_ext <;> simp [octonionMul, octK, octL, octT]
  have hz1 : z.1 = ⟨z.1.re, z.1.imI, z.1.imJ, z.1.imK⟩ := rfl
  have hz2 : z.2 = ⟨z.2.re, z.2.imI, z.2.imJ, z.2.imK⟩ := rfl
  conv_lhs => rw [h12, hz1, hz2, quatEmbed1_mk_eq, quatEmbed1_mk_eq]
  simp only [octonionMul_add_left, octonionMul_smul_left, octonionMul_one_left, hIL, hJL, hKL]
  abel

theorem exists_quatEmbedding_containing_pair (x y : Octonion) :
    ∃ φ : Quaternion ℝ →ₗ[ℝ] Octonion,
      IsQuatEmbedding φ ∧ x ∈ Set.range φ ∧ y ∈ Set.range φ := by
  obtain ⟨α1, rx, _, hα1x⟩ := exists_octAuto_imag_to_I (octIm x) (octonionReal_octIm x)
  have hx1 : α1.equiv x = octonionReal x • octOne + rx • octI := by
    conv_lhs => rw [oct_eq_scalar_add_octIm x]
    rw [map_add, α1.map_scalar, hα1x, octonionScalar_eq_smul, octOne_eq_scalar]
  obtain ⟨α2, hα2I, y0, y1, y2, _, hα2y⟩ := exists_octAuto_fix_I_to_IJ (α1.equiv y)
  let α := α2.comp α1
  let φ := α.symm.equiv.toLinearMap.comp quatEmbed1
  have hφ : IsQuatEmbedding φ :=
    octonionAutomorphism_comp_isQuatEmbedding α.symm quatEmbed1_isQuatEmbedding
  refine ⟨φ, hφ, ?_, ?_⟩
  · refine ⟨⟨octonionReal x, rx, 0, 0⟩, ?_⟩
    apply α.equiv.injective
    dsimp only [φ, α]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, OctonionAutomorphism.symm_apply,
      LinearEquiv.apply_symm_apply, OctonionAutomorphism.comp_apply, hx1,
      map_add, map_smul, α2.map_one, hα2I]
    rw [quatEmbed1_mk_eq]
    simp only [zero_smul, add_zero]
  · refine ⟨⟨y0, y1, y2, 0⟩, ?_⟩
    apply α.equiv.injective
    dsimp only [φ, α]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, OctonionAutomorphism.symm_apply,
      LinearEquiv.apply_symm_apply, OctonionAutomorphism.comp_apply, hα2y]
    rw [quatEmbed1_mk_eq]
    simp only [zero_smul, add_zero]

theorem octAssociator_eq_zero_of_quatEmbedding (φ : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hφ : IsQuatEmbedding φ) {x y z : Octonion}
    (hx : x ∈ Set.range φ) (hy : y ∈ Set.range φ) (hz : z ∈ Set.range φ) :
    octAssociator x y z = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rcases hz with ⟨c, rfl⟩
  simp only [octAssociator, ← hφ.map_mul, mul_assoc, sub_self]

structure OctSubalgebra where
  carrier : Submodule ℝ Octonion
  one_mem : octOne ∈ carrier
  mul_mem : ∀ x ∈ carrier, ∀ y ∈ carrier, octonionMul x y ∈ carrier
  conj_mem : ∀ x ∈ carrier, octonionConj x ∈ carrier

theorem octSubalgebra_conj_mem_auto (C : Submodule ℝ Octonion) (h1 : octOne ∈ C) :
    ∀ x ∈ C, octonionConj x ∈ C := by
  intro x hx
  rw [octConj_eq_two_real_sub x]
  exact C.sub_mem (C.smul_mem _ h1) hx

def OctSubalgebra.generated (S : Set Octonion) : OctSubalgebra where
  carrier := sInf {C : Submodule ℝ Octonion | S ⊆ C ∧ octOne ∈ C ∧
    (∀ x ∈ C, ∀ y ∈ C, octonionMul x y ∈ C) ∧ (∀ x ∈ C, octonionConj x ∈ C)}
  one_mem := Submodule.mem_sInf.mpr fun _ h => h.2.1
  mul_mem x hx y hy := Submodule.mem_sInf.mpr fun _ h =>
    h.2.2.1 x (Submodule.mem_sInf.mp hx _ h) y (Submodule.mem_sInf.mp hy _ h)
  conj_mem x hx := Submodule.mem_sInf.mpr fun _ h =>
    h.2.2.2 x (Submodule.mem_sInf.mp hx _ h)

theorem OctSubalgebra.subset_generated (S : Set Octonion) :
    S ⊆ (OctSubalgebra.generated S).carrier :=
  fun _ hx => Submodule.mem_sInf.mpr fun _ h => h.1 hx

theorem OctSubalgebra.generated_le (S : Set Octonion) (F : OctSubalgebra)
    (hS : S ⊆ F.carrier) : (OctSubalgebra.generated S).carrier ≤ F.carrier :=
  sInf_le ⟨hS, F.one_mem, F.mul_mem, F.conj_mem⟩

theorem octAssociator_eq_zero_artin (x y z : Octonion)
    (hz : z ∈ (OctSubalgebra.generated {x, y}).carrier) :
    octAssociator x y z = 0 := by
  obtain ⟨φ, hφ, hx, hy⟩ := exists_quatEmbedding_containing_pair x y
  let Fφ : OctSubalgebra :=
    { carrier := LinearMap.range φ
      one_mem := ⟨1, by rw [hφ.map_one]; rfl⟩
      mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, hφ.map_mul a b⟩
      conj_mem := by rintro _ ⟨a, rfl⟩; exact ⟨star a, hφ.map_star a⟩ }
  have hle := OctSubalgebra.generated_le {x, y} Fφ (by
    intro w hw
    rcases hw with rfl | rfl
    · exact hx
    · exact hy)
  exact octAssociator_eq_zero_of_quatEmbedding φ hφ hx hy (hle hz)

private theorem orthonormal_linearIndependent {n : ℕ} (v : Fin n → Octonion)
    (hnorm : ∀ i, octNormSq (v i) = 1)
    (horth : ∀ i j, i ≠ j → octDot (v i) (v j) = 0) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hd := congrArg (fun z => octDot z (v j)) hc
  rw [octDot_zero_left] at hd
  have hsum : octDot (∑ i : Fin n, c i • v i) (v j) = c j := by
    have hlin : ∀ s : Finset (Fin n), octDot (∑ i ∈ s, c i • v i) (v j) =
        ∑ i ∈ s, c i * octDot (v i) (v j) := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => simp [octDot_zero_left]
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, octDot_add_left, octDot_smul_left, ih, Finset.sum_insert ha]
    rw [hlin, Finset.sum_eq_single j]
    · rw [octDot_self, hnorm j, mul_one]
    · intro i _ hij; rw [horth i j hij, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hsum] at hd
  exact hd

private def octSubalgebraIm (F : OctSubalgebra) : Submodule ℝ Octonion where
  carrier := {x ∈ F.carrier | octonionReal x = 0}
  add_mem' {a b} ha hb := ⟨F.carrier.add_mem ha.1 hb.1, by simp [octonionReal_add, ha.2, hb.2]⟩
  zero_mem' := ⟨F.carrier.zero_mem, octonionReal_zero⟩
  smul_mem' r {a} ha := ⟨F.carrier.smul_mem r ha.1, by simp [octonionReal_smul, ha.2]⟩

private def octSubalgebraSplitEquiv (F : OctSubalgebra) :
    F.carrier ≃ₗ[ℝ] ℝ × octSubalgebraIm F where
  toFun x := (octonionReal x.1, ⟨octIm x.1,
    F.carrier.sub_mem x.2 (by
      rw [octonionScalar_eq_smul, ← octOne_eq_scalar]
      exact F.carrier.smul_mem _ F.one_mem),
    octonionReal_octIm x.1⟩)
  invFun p := ⟨p.1 • octOne + p.2.1, F.carrier.add_mem (F.carrier.smul_mem p.1 F.one_mem) p.2.2.1⟩
  left_inv x := by
    ext1
    change octonionReal x.1 • octOne + octIm x.1 = x.1
    rw [octOne_eq_scalar, ← octonionScalar_eq_smul, ← oct_eq_scalar_add_octIm]
  right_inv p := by
    apply Prod.ext
    · simp [octonionReal_add, octonionReal_smul, octonionReal_one, p.2.2.2]
    · ext1
      change octIm (p.1 • octOne + p.2.1) = p.2.1
      rw [octIm_add, octIm_smul, octOne_eq_scalar, octIm_scalar, smul_zero, zero_add,
        (octIm_eq_self_iff p.2.1).mpr p.2.2.2]
  map_add' x y := by
    apply Prod.ext
    · exact octonionReal_add x.1 y.1
    · ext1; exact octIm_add x.1 y.1
  map_smul' r x := by
    apply Prod.ext
    · exact octonionReal_smul r x.1
    · ext1; exact octIm_smul r x.1

private theorem octSubalgebra_finrank_split (F : OctSubalgebra) :
    Module.finrank ℝ F.carrier = 1 + Module.finrank ℝ (octSubalgebraIm F) := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  rw [(octSubalgebraSplitEquiv F).finrank_eq, Module.finrank_prod, Module.finrank_self]

theorem octSubalgebra_le_quatEmbedding_finrank (F : OctSubalgebra)
    (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (hsub : F.carrier ≤ LinearMap.range φ) :
    Module.finrank ℝ F.carrier ∈ ({1, 2, 4} : Set ℕ) := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  let Fφ : OctSubalgebra :=
    { carrier := LinearMap.range φ
      one_mem := ⟨1, by rw [hφ.map_one]; rfl⟩
      mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, hφ.map_mul a b⟩
      conj_mem := by rintro _ ⟨a, rfl⟩; exact ⟨star a, hφ.map_star a⟩ }
  have hfinφ : Module.finrank ℝ Fφ.carrier = 4 := by
    rw [(LinearEquiv.ofInjective φ hφ.injective).symm.finrank_eq, Quaternion.finrank_eq_four]
  have him_le : octSubalgebraIm F ≤ octSubalgebraIm Fφ := fun x hx => ⟨hsub hx.1, hx.2⟩
  have hfin_im_le : Module.finrank ℝ (octSubalgebraIm F) ≤ 3 := by
    have h1 : Module.finrank ℝ (octSubalgebraIm F) ≤ Module.finrank ℝ (octSubalgebraIm Fφ) :=
      Submodule.finrank_mono him_le
    have h2 := octSubalgebra_finrank_split Fφ
    omega
  have hsplit := octSubalgebra_finrank_split F
  let d := Module.finrank ℝ (octSubalgebraIm F)
  have hd_cases : d = 0 ∨ d = 1 ∨ 2 ≤ d := by omega
  rcases hd_cases with hd0 | hd1 | hd2
  · left; omega
  · right; left; omega
  · right; right
    have hne0 : octSubalgebraIm F ≠ ⊥ := by
      intro hbot
      have : d = 0 := by dsimp [d]; rw [hbot, finrank_bot]
      omega
    obtain ⟨x, hx_mem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne0
    have hnx : 0 < octNormSq x :=
      lt_of_le_of_ne (octNormSq_nonneg x) (Ne.symm (fun h => hx0 ((octNormSq_eq_zero x).mp h)))
    let rx := Real.sqrt (octNormSq x)
    let u := (1 / rx) • x
    have hu_mem : u ∈ octSubalgebraIm F := (octSubalgebraIm F).smul_mem _ hx_mem
    have hu_norm : octNormSq u = 1 := by
      rw [octNormSq_smul, div_pow, one_pow, Real.sq_sqrt hnx.le]; field_simp [hnx.ne']
    have hu0 : u ≠ 0 := fun h => by
      have : octNormSq u = 0 := by rw [h, (octNormSq_eq_zero 0).mpr rfl]
      linarith
    have hnotspan : ¬ octSubalgebraIm F ≤ Submodule.span ℝ {u} := by
      intro hle
      have hle_fin : d ≤ Module.finrank ℝ (Submodule.span ℝ {u}) :=
        Submodule.finrank_mono hle
      have hspan_fin : Module.finrank ℝ (Submodule.span ℝ {u}) = 1 :=
        finrank_span_singleton hu0
      omega
    obtain ⟨y, hy_mem, hy_not⟩ := IsConcreteLE.not_le_iff_exists.mp hnotspan
    let v0 := y - octDot y u • u
    have hv0_mem : v0 ∈ octSubalgebraIm F :=
      (octSubalgebraIm F).sub_mem hy_mem ((octSubalgebraIm F).smul_mem _ hu_mem)
    have hv0_ne : v0 ≠ 0 := by
      intro h
      apply hy_not
      rw [show y = octDot y u • u from sub_eq_zero.mp h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have hnv0 : 0 < octNormSq v0 :=
      lt_of_le_of_ne (octNormSq_nonneg v0) (Ne.symm (fun h => hv0_ne ((octNormSq_eq_zero v0).mp h)))
    let rv := Real.sqrt (octNormSq v0)
    let v := (1 / rv) • v0
    have hv_mem : v ∈ octSubalgebraIm F := (octSubalgebraIm F).smul_mem _ hv0_mem
    have hv_norm : octNormSq v = 1 := by
      rw [octNormSq_smul, div_pow, one_pow, Real.sq_sqrt hnv0.le]; field_simp [hnv0.ne']
    have huv : octDot u v = 0 := by
      rw [octDot_smul_right, octDot_comm,
        show octDot v0 u = 0 from by simp [v0, octDot_sub_left, octDot_smul_left, octDot_self, hu_norm],
        mul_zero]
    let w := octonionMul u v
    have hw_mem : w ∈ octSubalgebraIm F :=
      ⟨F.mul_mem u hu_mem.1 v hv_mem.1,
        by rw [octonionReal_mul_imag_eq hu_mem.2 hv_mem.2, huv, neg_zero]⟩
    have hw_norm : octNormSq w = 1 := by rw [octNormSq_mul, hu_norm, hv_norm, mul_one]
    have huw : octDot u w = 0 := by
      rw [octDot_comm, octDot_mul_left, octonionConj_eq_neg_of_real_zero hu_mem.2,
        octonionMul_neg_left, octonionMul_imag_sq hu_mem.2, hu_norm, neg_one_smul, neg_neg,
        octDot_comm, show octDot octOne v = 0 from by rw [octOne_eq_scalar, octDot_scalar_left, hv_mem.2, mul_zero]]
    have hvw : octDot v w = 0 := by
      rw [octDot_comm, octDot_mul_right, octonionConj_eq_neg_of_real_zero hv_mem.2,
        octonionMul_neg_right, octonionMul_imag_sq hv_mem.2, hv_norm, neg_one_smul, neg_neg,
        octDot_comm, show octDot octOne u = 0 from by rw [octOne_eq_scalar, octDot_scalar_left, hu_mem.2, mul_zero]]
    let triple : Fin 3 → octSubalgebraIm F := ![⟨u, hu_mem⟩, ⟨v, hv_mem⟩, ⟨w, hw_mem⟩]
    have hli : LinearIndependent ℝ (fun i => (triple i : Octonion)) :=
      orthonormal_linearIndependent (fun i => (triple i : Octonion))
        (fun i => by fin_cases i <;> dsimp [triple] <;> assumption)
        (fun i j hij => by
          fin_cases i <;> fin_cases j <;> dsimp [triple] <;> try exact absurd rfl hij
          · exact huv
          · exact huw
          · exact octDot_comm u v ▸ huv
          · exact hvw
          · exact octDot_comm u w ▸ huw
          · exact octDot_comm v w ▸ hvw)
    have hli' : LinearIndependent ℝ triple := hli.of_comp (octSubalgebraIm F).subtype
    have hd_ge3 : 3 ≤ d := by simpa [d] using hli'.fintype_card_le_finrank
    dsimp only [d] at hd_ge3
    rw [Set.mem_singleton_iff]
    omega

theorem octSubalgebra_le_quatEmbedding_finrank_one_iff (F : OctSubalgebra)
    (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (hsub : F.carrier ≤ LinearMap.range φ) :
    Module.finrank ℝ F.carrier = 1 ↔ F.carrier = Submodule.span ℝ {octOne} := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have _ := hφ; have _ := hsub
  have h1_le : Submodule.span ℝ {octOne} ≤ F.carrier :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr F.one_mem)
  have h1_fin : Module.finrank ℝ (Submodule.span ℝ {octOne}) = 1 :=
    finrank_span_singleton (fun h => by
      have := congrArg octonionReal h
      simp [octOne, octonionReal_scalar, octonionReal_zero] at this)
  constructor
  · intro hfin
    exact (Submodule.eq_of_le_of_finrank_eq h1_le (by rw [h1_fin, hfin])).symm
  · intro heq
    rw [heq, h1_fin]

theorem octSubalgebra_le_quatEmbedding_finrank_two_iff (F : OctSubalgebra)
    (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (hsub : F.carrier ≤ LinearMap.range φ) :
    Module.finrank ℝ F.carrier = 2 ↔
      ∃ u : Octonion, octonionReal u = 0 ∧ octNormSq u = 1 ∧
        u ∈ LinearMap.range φ ∧ F.carrier = Submodule.span ℝ {octOne, u} := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have _ := hφ
  have hsplit := octSubalgebra_finrank_split F
  constructor
  · intro hfin
    have hdim1 : Module.finrank ℝ (octSubalgebraIm F) = 1 := by omega
    have hne0 : octSubalgebraIm F ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim1
      omega
    obtain ⟨x, hx_mem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne0
    have hnx : 0 < octNormSq x :=
      lt_of_le_of_ne (octNormSq_nonneg x) (Ne.symm (fun h => hx0 ((octNormSq_eq_zero x).mp h)))
    let r := Real.sqrt (octNormSq x)
    let u := (1 / r) • x
    have hu_mem : u ∈ octSubalgebraIm F := (octSubalgebraIm F).smul_mem _ hx_mem
    have hu_norm : octNormSq u = 1 := by
      rw [octNormSq_smul, div_pow, one_pow, Real.sq_sqrt hnx.le]; field_simp [hnx.ne']
    have hu0 : u ≠ 0 := fun h => by
      have : octNormSq u = 0 := by rw [h, (octNormSq_eq_zero 0).mpr rfl]
      linarith
    have hle_span : Submodule.span ℝ {octOne, u} ≤ F.carrier := by
      rw [Submodule.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact F.one_mem
      · exact hu_mem.1
    have hli : LinearIndependent ℝ ![octOne, u] :=
      orthonormal_linearIndependent ![octOne, u]
        (fun i => by fin_cases i <;> dsimp <;> [exact octNormSq_one; exact hu_norm])
        (fun i j hij => by
          fin_cases i <;> fin_cases j <;> dsimp <;> try exact absurd rfl hij
          · rw [octOne_eq_scalar, octDot_scalar_left, hu_mem.2, mul_zero]
          · rw [octDot_comm, octOne_eq_scalar, octDot_scalar_left, hu_mem.2, mul_zero])
    have hspan_fin : Module.finrank ℝ (Submodule.span ℝ {octOne, u}) = 2 := by
      rw [show ({octOne, u} : Set Octonion) = Set.range ![octOne, u] by
        ext z; simp; tauto, finrank_span_eq_card hli, Fintype.card_fin]
    refine ⟨u, hu_mem.2, hu_norm, hsub hu_mem.1, ?_⟩
    exact (Submodule.eq_of_le_of_finrank_eq hle_span (by rw [hspan_fin, hfin])).symm
  · rintro ⟨u, hu_im, hu_norm, _, heq⟩
    have hli : LinearIndependent ℝ ![octOne, u] :=
      orthonormal_linearIndependent ![octOne, u]
        (fun i => by fin_cases i <;> dsimp <;> [exact octNormSq_one; exact hu_norm])
        (fun i j hij => by
          fin_cases i <;> fin_cases j <;> dsimp <;> try exact absurd rfl hij
          · rw [octOne_eq_scalar, octDot_scalar_left, hu_im, mul_zero]
          · rw [octDot_comm, octOne_eq_scalar, octDot_scalar_left, hu_im, mul_zero])
    rw [heq, show ({octOne, u} : Set Octonion) = Set.range ![octOne, u] by
      ext z; simp; tauto, finrank_span_eq_card hli, Fintype.card_fin]

theorem octSubalgebra_le_quatEmbedding_finrank_four_iff (F : OctSubalgebra)
    (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (hsub : F.carrier ≤ LinearMap.range φ) :
    Module.finrank ℝ F.carrier = 4 ↔ F.carrier = LinearMap.range φ := by
  have : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  have hfinφ : Module.finrank ℝ (LinearMap.range φ) = 4 := by
    rw [(LinearEquiv.ofInjective φ hφ.injective).symm.finrank_eq, Quaternion.finrank_eq_four]
  constructor
  · intro hfin
    exact Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfin, hfinφ])
  · intro heq
    rw [heq, hfinφ]

theorem octSubalgebra_strict_gt_quatEmbedding_eq_top (F : OctSubalgebra)
    (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ)
    (hsub : LinearMap.range φ < F.carrier) : F.carrier = ⊤ := by
  have hle : LinearMap.range φ ≤ F.carrier := hsub.le
  have hne : LinearMap.range φ ≠ F.carrier := hsub.ne
  have hex : ∃ y ∈ F.carrier, y ∉ LinearMap.range φ := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hle h)
  obtain ⟨y, hy_mem, hy_not⟩ := hex
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  let qk : Quaternion ℝ := ⟨0, 0, 0, 1⟩
  have hφ_dot : ∀ p q : Quaternion ℝ,
      octDot (φ p) (φ q) = p.re * q.re + p.imI * q.imI + p.imJ * q.imJ + p.imK * q.imK := by
    intro p q
    unfold octDot
    rw [← hφ.map_star, ← hφ.map_mul, hφ.map_re]
    simp
  let qproj : Quaternion ℝ := ⟨octDot y (φ 1), octDot y (φ qi), octDot y (φ qj), octDot y (φ qk)⟩
  let yp := y - φ qproj
  have hyp_mem : yp ∈ F.carrier := F.carrier.sub_mem hy_mem (hle ⟨qproj, rfl⟩)
  have hyp_ne : yp ≠ 0 := by
    intro h
    apply hy_not
    exact ⟨qproj, (sub_eq_zero.mp h).symm⟩
  have hnyp : 0 < octNormSq yp :=
    lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm (fun h => hyp_ne ((octNormSq_eq_zero _).mp h)))
  let r := Real.sqrt (octNormSq yp)
  let e3 := (1 / r) • yp
  have he3_mem : e3 ∈ F.carrier := F.carrier.smul_mem _ hyp_mem
  have he3_dot : ∀ q : Quaternion ℝ, octDot (φ q) e3 = 0 := by
    intro q
    have hq_exp : q = q.re • (1 : Quaternion ℝ) + q.imI • qi + q.imJ • qj + q.imK • qk := by
      apply Quaternion.ext <;> simp [qi, qj, qk]
    have hdot_basis : ∀ b : Quaternion ℝ,
        (b = 1 ∨ b = qi ∨ b = qj ∨ b = qk) → octDot (φ b) yp = 0 := by
      intro b hb
      rcases hb with rfl | rfl | rfl | rfl <;>
        simp [yp, qproj, octDot_sub_right, hφ_dot, qi, qj, qk, octDot_comm y]
    rw [octDot_smul_right, hq_exp]
    simp only [map_add, map_smul, octDot_add_left, octDot_smul_left,
      hdot_basis 1 (Or.inl rfl), hdot_basis qi (Or.inr (Or.inl rfl)),
      hdot_basis qj (Or.inr (Or.inr (Or.inl rfl))),
      hdot_basis qk (Or.inr (Or.inr (Or.inr rfl))), mul_zero, add_zero]
  have he1_im : octonionReal (φ qi) = 0 := by rw [hφ.map_re]
  have he2_im : octonionReal (φ qj) = 0 := by rw [hφ.map_re]
  have he3_im : octonionReal e3 = 0 := by
    have h1 : octDot octOne e3 = 0 := by rw [octOne_eq_scalar, ← hφ.map_one]; exact he3_dot 1
    rw [octOne_eq_scalar, octDot_scalar_left, one_mul] at h1
    exact h1
  have he1_norm : octNormSq (φ qi) = 1 := by
    change octDot (φ qi) (φ qi) = 1; rw [hφ_dot]; simp [qi]
  have he2_norm : octNormSq (φ qj) = 1 := by
    change octDot (φ qj) (φ qj) = 1; rw [hφ_dot]; simp [qj]
  have he3_norm : octNormSq e3 = 1 := by
    rw [octNormSq_smul, div_pow, one_pow, Real.sq_sqrt hnyp.le]; field_simp [hnyp.ne']
  have h12 : octDot (φ qi) (φ qj) = 0 := by rw [hφ_dot]; simp [qi, qj]
  have h13 : octDot (φ qi) e3 = 0 := he3_dot qi
  have h23 : octDot (φ qj) e3 = 0 := he3_dot qj
  have h3_12 : octDot e3 (octonionMul (φ qi) (φ qj)) = 0 := by
    rw [← hφ.map_mul, octDot_comm]; exact he3_dot (qi * qj)
  let α := octAutoOfBasicTriple (φ qi) (φ qj) e3 he1_im he2_im he3_im
    he1_norm he2_norm he3_norm h12 h13 h23 h3_12
  have hrange_eq : ∀ z : Octonion, α.equiv z ∈ F.carrier := by
    intro z
    have hα_I : α.equiv octI = φ qi := by dsimp only [α]; exact octAutoOfBasicTriple_I _ _ _ _ _ _ _ _ _ _ _ _ _
    have hα_J : α.equiv octJ = φ qj := by dsimp only [α]; exact octAutoOfBasicTriple_J _ _ _ _ _ _ _ _ _ _ _ _ _
    have hα_L : α.equiv octL = e3 := by dsimp only [α]; exact octAutoOfBasicTriple_L _ _ _ _ _ _ _ _ _ _ _ _ _
    have hα_K : α.equiv octK = φ qk := by
      rw [← octK_eq_mul, α.map_mul, hα_I, hα_J, ← hφ.map_mul]
      congr 1; apply Quaternion.ext <;> simp [qi, qj, qk]
    have hα_S : α.equiv octS = octonionMul (φ qi) e3 := by
      rw [← octS_eq_mul, α.map_mul, hα_I, hα_L]
    have hα_R : α.equiv octR = octonionMul (φ qj) e3 := by
      rw [← octR_eq_mul, α.map_mul, hα_J, hα_L]
    have hα_T : α.equiv octT = octonionMul (φ qk) e3 := by
      rw [← octT_eq_mul, α.map_mul, hα_K, hα_L]
    rw [oct_basis_expand z]
    simp only [map_add, map_smul, α.map_one, hα_I, hα_J, hα_K, hα_L, hα_S, hα_R, hα_T]
    repeat apply F.carrier.add_mem
    all_goals apply F.carrier.smul_mem
    · exact F.one_mem
    · exact hle ⟨qi, rfl⟩
    · exact hle ⟨qj, rfl⟩
    · exact hle ⟨qk, rfl⟩
    · exact he3_mem
    · exact F.mul_mem _ (hle ⟨qi, rfl⟩) _ he3_mem
    · exact F.mul_mem _ (hle ⟨qj, rfl⟩) _ he3_mem
    · exact F.mul_mem _ (hle ⟨qk, rfl⟩) _ he3_mem
  rw [eq_top_iff]
  intro w _
  rw [← α.equiv.apply_symm_apply w]
  exact hrange_eq (α.equiv.symm w)

theorem octSubalgebra_generated_IJL_eq_top :
    (OctSubalgebra.generated {octOne, octI, octJ, octL}).carrier = ⊤ := by
  let G := OctSubalgebra.generated {octOne, octI, octJ, octL}
  have hsub := OctSubalgebra.subset_generated {octOne, octI, octJ, octL}
  have h1 : octOne ∈ G.carrier := G.one_mem
  have hI : octI ∈ G.carrier := hsub (by simp)
  have hJ : octJ ∈ G.carrier := hsub (by simp)
  have hL : octL ∈ G.carrier := hsub (by simp)
  have hK : octK ∈ G.carrier := by rw [← octK_eq_mul]; exact G.mul_mem _ hI _ hJ
  have hS : octS ∈ G.carrier := by rw [← octS_eq_mul]; exact G.mul_mem _ hI _ hL
  have hR : octR ∈ G.carrier := by rw [← octR_eq_mul]; exact G.mul_mem _ hJ _ hL
  have hT : octT ∈ G.carrier := by rw [← octT_eq_mul]; exact G.mul_mem _ hK _ hL
  rw [eq_top_iff]
  intro z _
  rw [oct_basis_expand z]
  repeat apply G.carrier.add_mem
  all_goals apply G.carrier.smul_mem
  all_goals assumption

end AlbertSequential
