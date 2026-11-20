/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThreeAtomAndFourPoint
public import ComplexPositiveFactor
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complex-Window Determinant, Rank Trichotomy, and Maximality

Formalizes:
1. Complex-window cubic determinant identity `albertCubicNorm (W.embedding M) = det M`,
   `windowProj` automorphism transport, and the triple determinant `tripleDelta` / `windowDelta`.
2. `lem:A:window` (`tripleDelta_nonneg`, `lemma_A_window_generated`) and `prop:windowdet`
   (`prop_windowdet`, `prop_windowdet_zero`).
3. `cor:fp:rank` (`windowProj_atom_isDensity`, `windowProj_atom_det_bounds`,
   `windowProj_atom_det_eq_max_iff`, `windowProj_atom_rankOne_iff_contains`, `cor_fp_rank`).
4. `lem:fp:DeltaWmax`, `prop:max` (single-orbit uniqueness and `maximizerConfig_traces`,
   reusing `ThirteenTracesAndAform.fourPointInvariant_fixedS`), `cor:fp:maxmixed`, and the
   deterministic Laplace integrand / Jordan-determinant kernel of `prop:windowlaw`
   (`complexWindow_laplace_integrand`).
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

open NativeAnalysis

/-! ## Section 1: Local Helpers, Cubic-Norm Determinant, and `windowProj` Transport -/

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

private theorem oct_ext {x y : Octonion}
    (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
    (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK)
    (h5 : x.2.re = y.2.re) (h6 : x.2.imI = y.2.imI)
    (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

private theorem albert_zero_fst (j : Fin 3) : (0 : Albert).1 j = 0 := rfl
private theorem albert_zero_snd (k : Fin 3) : (0 : Albert).2 k = 0 := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem octNormSq_zero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl

private theorem oct_fst_zero : (0 : Octonion).1 = 0 := rfl
private theorem oct_snd_zero : (0 : Octonion).2 = 0 := rfl
private theorem oct_zero_re : (0 : Octonion).1.re = 0 := rfl
private theorem oct_zero_imI : (0 : Octonion).1.imI = 0 := rfl
private theorem oct_zero_imJ : (0 : Octonion).1.imJ = 0 := rfl
private theorem oct_zero_imK : (0 : Octonion).1.imK = 0 := rfl
private theorem oct_zero_s_re : (0 : Octonion).2.re = 0 := rfl
private theorem oct_zero_s_imI : (0 : Octonion).2.imI = 0 := rfl
private theorem oct_zero_s_imJ : (0 : Octonion).2.imJ = 0 := rfl
private theorem oct_zero_s_imK : (0 : Octonion).2.imK = 0 := rfl
private theorem oct_add_re (x y : Octonion) : (x + y).1.re = x.1.re + y.1.re := rfl
private theorem oct_add_imI (x y : Octonion) : (x + y).1.imI = x.1.imI + y.1.imI := rfl
private theorem oct_add_imJ (x y : Octonion) : (x + y).1.imJ = x.1.imJ + y.1.imJ := rfl
private theorem oct_add_imK (x y : Octonion) : (x + y).1.imK = x.1.imK + y.1.imK := rfl
private theorem oct_add_s_re (x y : Octonion) : (x + y).2.re = x.2.re + y.2.re := rfl
private theorem oct_add_s_imI (x y : Octonion) : (x + y).2.imI = x.2.imI + y.2.imI := rfl
private theorem oct_add_s_imJ (x y : Octonion) : (x + y).2.imJ = x.2.imJ + y.2.imJ := rfl
private theorem oct_add_s_imK (x y : Octonion) : (x + y).2.imK = x.2.imK + y.2.imK := rfl
private theorem oct_sub_re (x y : Octonion) : (x - y).1.re = x.1.re - y.1.re := rfl
private theorem oct_sub_imI (x y : Octonion) : (x - y).1.imI = x.1.imI - y.1.imI := rfl
private theorem oct_sub_imJ (x y : Octonion) : (x - y).1.imJ = x.1.imJ - y.1.imJ := rfl
private theorem oct_sub_imK (x y : Octonion) : (x - y).1.imK = x.1.imK - y.1.imK := rfl
private theorem oct_sub_s_re (x y : Octonion) : (x - y).2.re = x.2.re - y.2.re := rfl
private theorem oct_sub_s_imI (x y : Octonion) : (x - y).2.imI = x.2.imI - y.2.imI := rfl
private theorem oct_sub_s_imJ (x y : Octonion) : (x - y).2.imJ = x.2.imJ - y.2.imJ := rfl
private theorem oct_sub_s_imK (x y : Octonion) : (x - y).2.imK = x.2.imK - y.2.imK := rfl
private theorem oct_smul_re (r : ℝ) (x : Octonion) : (r • x).1.re = r * x.1.re := rfl
private theorem oct_smul_imI (r : ℝ) (x : Octonion) : (r • x).1.imI = r * x.1.imI := rfl
private theorem oct_smul_imJ (r : ℝ) (x : Octonion) : (r • x).1.imJ = r * x.1.imJ := rfl
private theorem oct_smul_imK (r : ℝ) (x : Octonion) : (r • x).1.imK = r * x.1.imK := rfl
private theorem oct_smul_s_re (r : ℝ) (x : Octonion) : (r • x).2.re = r * x.2.re := rfl
private theorem oct_smul_s_imI (r : ℝ) (x : Octonion) : (r • x).2.imI = r * x.2.imI := rfl
private theorem oct_smul_s_imJ (r : ℝ) (x : Octonion) : (r • x).2.imJ = r * x.2.imJ := rfl
private theorem oct_smul_s_imK (r : ℝ) (x : Octonion) : (r • x).2.imK = r * x.2.imK := rfl
private theorem oct_neg_re (x : Octonion) : (-x).1.re = -x.1.re := rfl
private theorem oct_neg_imI (x : Octonion) : (-x).1.imI = -x.1.imI := rfl
private theorem oct_neg_imJ (x : Octonion) : (-x).1.imJ = -x.1.imJ := rfl
private theorem oct_neg_imK (x : Octonion) : (-x).1.imK = -x.1.imK := rfl
private theorem oct_neg_s_re (x : Octonion) : (-x).2.re = -x.2.re := rfl
private theorem oct_neg_s_imI (x : Octonion) : (-x).2.imI = -x.2.imI := rfl
private theorem oct_neg_s_imJ (x : Octonion) : (-x).2.imJ = -x.2.imJ := rfl
private theorem oct_neg_s_imK (x : Octonion) : (-x).2.imK = -x.2.imK := rfl

private theorem quat_zero_re : (0 : Quaternion ℝ).re = 0 := rfl
private theorem quat_zero_imI : (0 : Quaternion ℝ).imI = 0 := rfl
private theorem quat_zero_imJ : (0 : Quaternion ℝ).imJ = 0 := rfl
private theorem quat_zero_imK : (0 : Quaternion ℝ).imK = 0 := rfl
private theorem quat_add_re (a b : Quaternion ℝ) : (a + b).re = a.re + b.re := rfl
private theorem quat_add_imI (a b : Quaternion ℝ) : (a + b).imI = a.imI + b.imI := rfl
private theorem quat_add_imJ (a b : Quaternion ℝ) : (a + b).imJ = a.imJ + b.imJ := rfl
private theorem quat_add_imK (a b : Quaternion ℝ) : (a + b).imK = a.imK + b.imK := rfl
private theorem quat_sub_re (a b : Quaternion ℝ) : (a - b).re = a.re - b.re := rfl
private theorem quat_sub_imI (a b : Quaternion ℝ) : (a - b).imI = a.imI - b.imI := rfl
private theorem quat_sub_imJ (a b : Quaternion ℝ) : (a - b).imJ = a.imJ - b.imJ := rfl
private theorem quat_sub_imK (a b : Quaternion ℝ) : (a - b).imK = a.imK - b.imK := rfl
private theorem quat_smul_re (r : ℝ) (a : Quaternion ℝ) : (r • a).re = r * a.re := rfl
private theorem quat_smul_imI (r : ℝ) (a : Quaternion ℝ) : (r • a).imI = r * a.imI := rfl
private theorem quat_smul_imJ (r : ℝ) (a : Quaternion ℝ) : (r • a).imJ = r * a.imJ := rfl
private theorem quat_smul_imK (r : ℝ) (a : Quaternion ℝ) : (r • a).imK = r * a.imK := rfl
private theorem quat_neg_re (a : Quaternion ℝ) : (-a).re = -a.re := rfl
private theorem quat_neg_imI (a : Quaternion ℝ) : (-a).imI = -a.imI := rfl
private theorem quat_neg_imJ (a : Quaternion ℝ) : (-a).imJ = -a.imJ := rfl
private theorem quat_neg_imK (a : Quaternion ℝ) : (-a).imK = -a.imK := rfl
private theorem quat_star_re (a : Quaternion ℝ) : (star a).re = a.re := by simp
private theorem quat_star_imI (a : Quaternion ℝ) : (star a).imI = -a.imI := by simp
private theorem quat_star_imJ (a : Quaternion ℝ) : (star a).imJ = -a.imJ := by simp
private theorem quat_star_imK (a : Quaternion ℝ) : (star a).imK = -a.imK := by simp
private theorem quat_mul_re (a b : Quaternion ℝ) :
    (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK := by
  simp
private theorem quat_mul_imI (a b : Quaternion ℝ) :
    (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ := by
  simp
private theorem quat_mul_imJ (a b : Quaternion ℝ) :
    (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI := by
  simp
private theorem quat_mul_imK (a b : Quaternion ℝ) :
    (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re := by
  simp

private theorem oct_fst_add (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem oct_snd_add (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem oct_fst_sub (x y : Octonion) : (x - y).1 = x.1 - y.1 := rfl
private theorem oct_snd_sub (x y : Octonion) : (x - y).2 = x.2 - y.2 := rfl
private theorem oct_fst_neg (x : Octonion) : (-x).1 = -x.1 := rfl
private theorem oct_snd_neg (x : Octonion) : (-x).2 = -x.2 := rfl
private theorem oct_fst_smul (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem oct_snd_smul (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl
private theorem oct_fst_scalar (r : ℝ) : (octonionScalar r).1 = ⟨r, 0, 0, 0⟩ := rfl
private theorem oct_snd_scalar (r : ℝ) : (octonionScalar r).2 = 0 := rfl
private theorem oct_fst_one : octOne.1 = ⟨1, 0, 0, 0⟩ := rfl
private theorem oct_snd_one : octOne.2 = 0 := rfl
private theorem oct_fst_I : octI.1 = ⟨0, 1, 0, 0⟩ := rfl
private theorem oct_snd_I : octI.2 = 0 := rfl
private theorem oct_fst_J : octJ.1 = ⟨0, 0, 1, 0⟩ := rfl
private theorem oct_snd_J : octJ.2 = 0 := rfl
private theorem oct_fst_K : octK.1 = ⟨0, 0, 0, 1⟩ := rfl
private theorem oct_snd_K : octK.2 = 0 := rfl
private theorem oct_fst_L : octL.1 = 0 := rfl
private theorem oct_snd_L : octL.2 = ⟨1, 0, 0, 0⟩ := rfl
private theorem oct_fst_conj (x : Octonion) : (octonionConj x).1 = star x.1 := rfl
private theorem oct_snd_conj (x : Octonion) : (octonionConj x).2 = -x.2 := rfl
private theorem oct_fst_mul (x y : Octonion) :
    (octonionMul x y).1 = x.1 * y.1 - star y.2 * x.2 := rfl
private theorem oct_snd_mul (x y : Octonion) :
    (octonionMul x y).2 = y.2 * x.1 + x.2 * star y.1 := rfl
private theorem complexToOctonion_fst (z : ℂ) : (complexToOctonion z).1 = ⟨z.re, z.im, 0, 0⟩ := by
  rw [complexToOctonion_apply]
private theorem complexToOctonion_snd (z : ℂ) : (complexToOctonion z).2 = 0 := by
  rw [complexToOctonion_apply]
private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl
private theorem diagAtom_fst (i j : Fin 3) : (diagAtom i).1 j = if j = i then 1 else 0 := rfl
private theorem diagAtom_snd (i k : Fin 3) : (diagAtom i).2 k = 0 := rfl
private theorem slotElem01_fst (a : Octonion) (j : Fin 3) : (slotElem01 a).1 j = 0 := rfl
private theorem slotElem01_snd_0 (a : Octonion) : (slotElem01 a).2 0 = a := rfl
private theorem slotElem01_snd_1 (a : Octonion) : (slotElem01 a).2 1 = 0 := rfl
private theorem slotElem01_snd_2 (a : Octonion) : (slotElem01 a).2 2 = 0 := rfl
private theorem auto_apply_symm (g : NativeAlbertAutomorphism) (x : Albert) :
    g.linearEquiv (g.symm.linearEquiv x) = x :=
  g.symm.linearEquiv.symm_apply_apply x
private theorem auto_symm_apply (g : NativeAlbertAutomorphism) (x : Albert) :
    g.symm.linearEquiv (g.linearEquiv x) = x :=
  g.symm.linearEquiv.apply_symm_apply x

private theorem oct_coords_comb4 (r i j k l : ℝ) :
    let o := octonionScalar r + i • octI + j • octJ + k • octK + l • octL
    o.1.re = r ∧ o.1.imI = i ∧ o.1.imJ = j ∧ o.1.imK = k ∧
      o.2.re = l ∧ o.2.imI = 0 ∧ o.2.imJ = 0 ∧ o.2.imK = 0 := by
  intro o
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [o, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I, oct_fst_J, oct_snd_J,
      oct_fst_K, oct_snd_K, oct_fst_L, oct_snd_L,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]; ring)

private theorem hermE_apply (k i j : Fin 3) :
    (hermE k : ComplexMatrix3) i j = if i = k ∧ j = k then 1 else 0 := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [hermE, hermitian3Equiv, mkHerm3Matrix] <;>
    (apply Complex.ext <;> simp)

private theorem vec3_eq {α : Type*} {a0 a1 a2 b0 b1 b2 : α}
    (h0 : a0 = b0) (h1 : a1 = b1) (h2 : a2 = b2) :
    ![a0, a1, a2] = ![b0, b1, b2] := by
  subst h0 h1 h2; rfl

private theorem octNormSq_scalar (r : ℝ) : octNormSq (octonionScalar r) = r ^ 2 := by
  rw [octNormSq_eq_coords]
  simp [octonionScalar]

private theorem tracePairing_unit_right (x : Albert) :
    tracePairing x albertUnit = albertTrace x := by
  rw [tracePairing_eq_coords]
  have h1 : ∀ k : Fin 3, albertUnit.1 k = 1 := fun _ => rfl
  have h2 : ∀ k : Fin 3, albertUnit.2 k = 0 := fun _ => rfl
  simp [h1, h2, octDot_zero_right, albertTrace, Fin.sum_univ_three]

private theorem tracePairing_self_eq_zero_iff (z : Albert) :
    tracePairing z z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    rw [tracePairing_eq_coords, octDot_self, octDot_self, octDot_self] at hz
    have hd0 : z.1 0 = 0 := sq_eq_zero_iff.mp (by
      nlinarith [sq_nonneg (z.1 0), sq_nonneg (z.1 1), sq_nonneg (z.1 2),
        octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)])
    have hd1 : z.1 1 = 0 := sq_eq_zero_iff.mp (by
      nlinarith [sq_nonneg (z.1 0), sq_nonneg (z.1 1), sq_nonneg (z.1 2),
        octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)])
    have hd2 : z.1 2 = 0 := sq_eq_zero_iff.mp (by
      nlinarith [sq_nonneg (z.1 0), sq_nonneg (z.1 1), sq_nonneg (z.1 2),
        octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)])
    have hn0 : octNormSq (z.2 0) = 0 := by
      nlinarith [octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)]
    have hn1 : octNormSq (z.2 1) = 0 := by
      nlinarith [octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)]
    have hn2 : octNormSq (z.2 2) = 0 := by
      nlinarith [octNormSq_nonneg (z.2 0), octNormSq_nonneg (z.2 1), octNormSq_nonneg (z.2 2)]
    apply albert_ext
    · exact hd0
    · exact hd1
    · exact hd2
    · exact (octNormSq_eq_zero _).mp hn0
    · exact (octNormSq_eq_zero _).mp hn1
    · exact (octNormSq_eq_zero _).mp hn2
  · rintro rfl
    rw [tracePairing_eq_coords]
    simp [albert_zero_fst, albert_zero_snd, octDot_zero_left]

private theorem tracePairing_atom_bounds {a b : Albert} (ha : IsAtom a) (hb : IsAtom b) :
    0 ≤ tracePairing a b ∧ tracePairing a b ≤ 1 := by
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 a ha
  let b' := g.linearEquiv b
  have hb' : IsAtom b' := g.map_isAtom hb
  have htr : tracePairing a b = b'.1 0 := by
    rw [← g.map_tracePairing, hg, tracePairing_diagAtom]
  rw [htr]
  have hn0 := isAtom_diag_nonneg hb' 0
  have hn1 := isAtom_diag_nonneg hb' 1
  have hn2 := isAtom_diag_nonneg hb' 2
  have hsum : b'.1 0 + b'.1 1 + b'.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three] using hb'.2
  exact ⟨hn0, by linarith⟩

private theorem distinct_nonorth_atom_overlap_strict {a b : Albert} (ha : IsAtom a) (hb : IsAtom b)
    (hne : a ≠ b) (hnz : jordanMul a b ≠ 0) :
    0 < tracePairing a b ∧ tracePairing a b < 1 := by
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 a ha
  let b' := g.linearEquiv b
  have hb' : IsAtom b' := g.map_isAtom hb
  have htr : tracePairing a b = b'.1 0 := by
    rw [← g.map_tracePairing, hg, tracePairing_diagAtom]
  rw [htr]
  have hn0 := isAtom_diag_nonneg hb' 0
  have hn1 := isAtom_diag_nonneg hb' 1
  have hn2 := isAtom_diag_nonneg hb' 2
  have hsum : b'.1 0 + b'.1 1 + b'.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three] using hb'.2
  constructor
  · by_contra hle
    have hz0 : b'.1 0 = 0 := le_antisymm (not_lt.mp hle) hn0
    obtain ⟨h01, h02⟩ := isAtom_zero_row0 hb' hz0
    have hj0 : jordanMul (diagAtom 0) b' = 0 := by
      rw [jordanMul_diagAtom0]
      apply albert_ext <;> simp [hz0, h01, h02, albert_zero_fst, albert_zero_snd]
    apply hnz
    apply g.linearEquiv.injective
    rw [g.preserves_product, hg, map_zero]
    exact hj0
  · by_contra hge
    have h1 : b'.1 0 = 1 := le_antisymm (by linarith) (not_lt.mp hge)
    have hz1 : b'.1 1 = 0 := by linarith
    have hz2 : b'.1 2 = 0 := by linarith
    have hns1 : octNormSq (b'.2 0) = 0 := by
      have hf := congrArg (fun x : Albert => x.1 2) (albertSharp_atom_eq_zero b' hb')
      simp [albertSharp, albert_zero_fst, h1, hz1] at hf
      linarith
    have hns2 : octNormSq (b'.2 1) = 0 := by
      have hf := congrArg (fun x : Albert => x.1 1) (albertSharp_atom_eq_zero b' hb')
      simp [albertSharp, albert_zero_fst, h1, hz2] at hf
      linarith
    have hns3 : octNormSq (b'.2 2) = 0 := by
      have hf := congrArg (fun x : Albert => x.1 0) (albertSharp_atom_eq_zero b' hb')
      simp [albertSharp, albert_zero_fst, hz1, hz2] at hf
      linarith
    have hb'_eq : b' = diagAtom 0 := by
      apply albert_ext
      · exact h1
      · exact hz1
      · exact hz2
      · exact (octNormSq_eq_zero _).mp hns1
      · exact (octNormSq_eq_zero _).mp hns2
      · exact (octNormSq_eq_zero _).mp hns3
    apply hne
    apply g.linearEquiv.injective
    exact (hb'_eq.trans hg.symm).symm

private theorem three_nonneg_am_gm {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c ≤ 1) :
    a * b * c ≤ 1 / 27 := by
  let u := a + b
  have hu_nn : 0 ≤ u := by dsimp [u]; linarith
  have hc_le : c ≤ 1 - u := by dsimp [u]; linarith
  have hab : 4 * (a * b) ≤ u ^ 2 := by dsimp [u]; nlinarith [sq_nonneg (a - b)]
  have h4abc : 4 * (a * b * c) ≤ u ^ 2 * (1 - u) := by
    calc
      4 * (a * b * c) = (4 * (a * b)) * c := by ring
      _ ≤ u ^ 2 * c := mul_le_mul_of_nonneg_right hab hc
      _ ≤ u ^ 2 * (1 - u) := mul_le_mul_of_nonneg_left hc_le (sq_nonneg u)
  have hcubic : 27 * (u ^ 2 * (1 - u)) ≤ 4 := by
    have hid : 4 - 27 * (u ^ 2 * (1 - u)) = (3 * u - 2) ^ 2 * (3 * u + 1) := by ring
    have hpos : 0 ≤ (3 * u - 2) ^ 2 * (3 * u + 1) := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  linarith

private theorem three_nonneg_am_gm_eq_iff {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c ≤ 1) :
    a * b * c = 1 / 27 ↔ a = 1 / 3 ∧ b = 1 / 3 ∧ c = 1 / 3 := by
  constructor
  · intro heq
    let u := a + b
    have hu_nn : 0 ≤ u := by dsimp [u]; linarith
    have hc_le : c ≤ 1 - u := by dsimp [u]; linarith
    have hab : 4 * (a * b) ≤ u ^ 2 := by dsimp [u]; nlinarith [sq_nonneg (a - b)]
    have h4abc : 4 * (a * b * c) ≤ u ^ 2 * (1 - u) := by
      calc
        4 * (a * b * c) = (4 * (a * b)) * c := by ring
        _ ≤ u ^ 2 * c := mul_le_mul_of_nonneg_right hab hc
        _ ≤ u ^ 2 * (1 - u) := mul_le_mul_of_nonneg_left hc_le (sq_nonneg u)
    have hcubic : 27 * (u ^ 2 * (1 - u)) ≤ 4 := by
      have hid : 4 - 27 * (u ^ 2 * (1 - u)) = (3 * u - 2) ^ 2 * (3 * u + 1) := by ring
      have hpos : 0 ≤ (3 * u - 2) ^ 2 * (3 * u + 1) := mul_nonneg (sq_nonneg _) (by linarith)
      linarith
    have hcub_eq : 27 * (u ^ 2 * (1 - u)) = 4 := by linarith
    have hfac : (3 * u - 2) ^ 2 * (3 * u + 1) = 0 := by linarith
    have hpos1 : (3 * u + 1) ≠ 0 := by linarith
    have hu_eq : u = 2 / 3 := by
      have hsq : (3 * u - 2) ^ 2 = 0 := (mul_eq_zero.mp hfac).resolve_right hpos1
      linarith [sq_eq_zero_iff.mp hsq]
    have hc_eq : c = 1 / 3 := by
      have h1 : 4 / 27 ≤ u ^ 2 * c := by nlinarith
      have h2 : u ^ 2 * c ≤ 4 / 27 := by
        rw [hu_eq] at hcubic ⊢
        nlinarith [hc_le, hu_eq]
      rw [hu_eq] at h1
      linarith
    have hab_eq : (a - b) ^ 2 = 0 := by nlinarith [heq, hc_eq, hu_eq]
    have ha_eq : a = 1 / 3 := by linarith [sq_eq_zero_iff.mp hab_eq]
    have hb_eq : b = 1 / 3 := by linarith [sq_eq_zero_iff.mp hab_eq]
    exact ⟨ha_eq, hb_eq, hc_eq⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

private theorem unit_prod_sq_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u * (1 - u) ^ 2 ≤ 4 / 27 := by
  have hid : 4 - 27 * (u * (1 - u) ^ 2) = (3 * u - 1) ^ 2 * (4 - 3 * u) := by ring
  have hpos : 0 ≤ (3 * u - 1) ^ 2 * (4 - 3 * u) := mul_nonneg (sq_nonneg _) (by linarith)
  linarith

private theorem unit_prod_sq_eq_iff {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u * (1 - u) ^ 2 = 4 / 27 ↔ u = 1 / 3 := by
  constructor
  · intro heq
    have hid : 4 - 27 * (u * (1 - u) ^ 2) = (3 * u - 1) ^ 2 * (4 - 3 * u) := by ring
    have hfac : (3 * u - 1) ^ 2 * (4 - 3 * u) = 0 := by linarith
    have hpos : 4 - 3 * u ≠ 0 := by linarith
    have hsq : (3 * u - 1) ^ 2 = 0 := (mul_eq_zero.mp hfac).resolve_right hpos
    linarith [sq_eq_zero_iff.mp hsq]
  · rintro rfl; norm_num

/-- Triple determinant invariant `Δ_W(p₁, p₂, p₃) = N(p₁ + p₂ + p₃) (o₁₂ o₂₃ o₃₁ - R₁₂₃²)`. -/
def tripleDelta (p1 p2 p3 : Albert) : ℝ :=
  albertCubicNorm (p1 + p2 + p3) *
    (tracePairing p1 p2 * tracePairing p2 p3 * tracePairing p1 p3 -
      (tracePairing p1 (jordanMul p2 p3)) ^ 2)

/-- Complex-window triangle factor `Δ_W` (`lem:A:window`, `prop:windowdet`). -/
def windowDelta (_W : ComplexWindow) (p1 p2 p3 : Albert) : ℝ :=
  tripleDelta p1 p2 p3

theorem windowDelta_eq_tripleDelta (W : ComplexWindow) (p1 p2 p3 : Albert) :
    windowDelta W p1 p2 p3 = tripleDelta p1 p2 p3 :=
  rfl

theorem tripleDelta_automorphism (g : NativeAlbertAutomorphism) (p1 p2 p3 : Albert) :
    tripleDelta (g.linearEquiv p1) (g.linearEquiv p2) (g.linearEquiv p3) =
      tripleDelta p1 p2 p3 := by
  unfold tripleDelta
  rw [← map_add, ← map_add, g.map_cubicNorm, g.map_tracePairing, g.map_tracePairing,
    g.map_tracePairing, ← g.preserves_product, g.map_tracePairing]

theorem tripleDelta_symm_12 (p1 p2 p3 : Albert) :
    tripleDelta p2 p1 p3 = tripleDelta p1 p2 p3 := by
  unfold tripleDelta
  have hsum : p2 + p1 + p3 = p1 + p2 + p3 := by abel
  have hR : tracePairing p2 (jordanMul p1 p3) = tracePairing p1 (jordanMul p2 p3) := by
    calc
      tracePairing p2 (jordanMul p1 p3)
        = tracePairing (jordanMul p2 p1) p3 := (NativeAnalysis.tracePairing_associative p2 p1 p3).symm
      _ = tracePairing (jordanMul p1 p2) p3 := by rw [jordanMul_comm]
      _ = tracePairing p1 (jordanMul p2 p3) := NativeAnalysis.tracePairing_associative p1 p2 p3
  rw [hsum, tracePairing_comm p2 p1, tracePairing_comm p2 p3, tracePairing_comm p1 p3, hR]
  ring

theorem tripleDelta_symm_23 (p1 p2 p3 : Albert) :
    tripleDelta p1 p3 p2 = tripleDelta p1 p2 p3 := by
  unfold tripleDelta
  have hsum : p1 + p3 + p2 = p1 + p2 + p3 := by abel
  rw [hsum, jordanMul_comm p3 p2, tracePairing_comm p3 p2]
  ring

theorem tripleDelta_symm_13 (p1 p2 p3 : Albert) :
    tripleDelta p3 p2 p1 = tripleDelta p1 p2 p3 := by
  calc
    tripleDelta p3 p2 p1 = tripleDelta p2 p3 p1 := tripleDelta_symm_12 p2 p3 p1
    _ = tripleDelta p2 p1 p3 := tripleDelta_symm_23 p2 p1 p3
    _ = tripleDelta p1 p2 p3 := tripleDelta_symm_12 p1 p2 p3

/-- Every `ComplexWindow` carries a `NativeJordanFrame` whose image is conjugate to `diagAtom`
via `AcceptedRootAtomAdapter.native_frame_to_standardFrame`. -/
theorem complexWindow_frame_conjugate (W : ComplexWindow) :
    let F : NativeJordanFrame :=
      { atom := fun i => W.embedding (hermE i)
        atoms := fun i => by
          have hid : (hermE i : ComplexMatrix3) * (hermE i : ComplexMatrix3) = hermE i := by
            ext a b
            simp only [Matrix.mul_apply, hermE_apply, Fin.sum_univ_three]
            fin_cases i <;> fin_cases a <;> fin_cases b <;> norm_num
          have htr : Matrix.trace (hermE i : ComplexMatrix3) = 1 := by
            simp only [Matrix.trace, Matrix.diag, hermE_apply, Fin.sum_univ_three]
            fin_cases i <;> norm_num
          constructor
          · symm
            apply W.preserves_product
            rw [hid, ← two_smul ℝ, smul_smul]
            norm_num
          · rw [W.preserves_trace, htr, Complex.one_re]
        orthogonal := fun i j hij => by
          have hmul : (hermE i : ComplexMatrix3) * (hermE j : ComplexMatrix3) = 0 := by
            ext a b
            simp only [Matrix.mul_apply, hermE_apply, Fin.sum_univ_three, Matrix.zero_apply]
            fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
              fin_cases a <;> fin_cases b <;> norm_num
          have hmul2 : (hermE j : ComplexMatrix3) * (hermE i : ComplexMatrix3) = 0 := by
            ext a b
            simp only [Matrix.mul_apply, hermE_apply, Fin.sum_univ_three, Matrix.zero_apply]
            fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
              fin_cases a <;> fin_cases b <;> norm_num
          have h0 : jordanMul (W.embedding (hermE i)) (W.embedding (hermE j)) = W.embedding 0 := by
            symm
            apply W.preserves_product
            simp [hmul, hmul2]
          simpa using h0
        sum_unit := by
          have hsum : ∑ i : Fin 3, hermE i = (1 : Hermitian3) := by
            apply Subtype.ext
            rw [Fin.sum_univ_three]
            ext a b
            change ((hermE 0 : ComplexMatrix3) + (hermE 1 : ComplexMatrix3) +
              (hermE 2 : ComplexMatrix3)) a b = (1 : ComplexMatrix3) a b
            simp only [Matrix.add_apply, hermE_apply, Matrix.one_apply]
            fin_cases a <;> fin_cases b <;> norm_num
          rw [← map_sum, hsum, W.unit] }
    ∃ g : NativeAlbertAutomorphism, ∀ i : Fin 3, g.linearEquiv (F.atom i) = diagAtom i := by
  intro F
  exact native_frame_to_standardFrame F

theorem complexWindow_finrank (W : ComplexWindow) :
    Module.finrank ℝ W.toSubalgebra.carrier = 9 := by
  change Module.finrank ℝ (LinearMap.range W.embedding) = 9
  have heq := LinearEquiv.ofInjective W.embedding W.injective
  rw [← LinearEquiv.finrank_eq heq]
  exact hermitian3_finrank

private theorem complexWindow_finite (W : ComplexWindow) :
    FiniteDimensional ℝ W.toSubalgebra.carrier :=
  Module.finite_of_finrank_pos (by rw [complexWindow_finrank W]; norm_num)

theorem standardComplexWindow_albertCubicNorm_eq_det (M : Hermitian3) :
    albertCubicNorm (standardComplexWindow.embedding M) = (M : ComplexMatrix3).det.re ∧
      (M : ComplexMatrix3).det.im = 0 := by
  have hm_herm : (M : ComplexMatrix3).IsHermitian := M.prop
  have hconj : ∀ i j : Fin 3, (M : ComplexMatrix3) j i = star ((M : ComplexMatrix3) i j) := by
    intro i j
    have h := congrFun (congrFun hm_herm.eq j) i
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hd0 : ((M : ComplexMatrix3) 0 0).im = 0 := by
    have h := congrArg Complex.im (hconj 0 0)
    simp at h; linarith
  have hd1 : ((M : ComplexMatrix3) 1 1).im = 0 := by
    have h := congrArg Complex.im (hconj 1 1)
    simp at h; linarith
  have hd2 : ((M : ComplexMatrix3) 2 2).im = 0 := by
    have h := congrArg Complex.im (hconj 2 2)
    simp at h; linarith
  have hdet : (M : ComplexMatrix3).det =
      ((M : ComplexMatrix3) 0 0 * ((M : ComplexMatrix3) 1 1 * (M : ComplexMatrix3) 2 2 -
        (M : ComplexMatrix3) 1 2 * star ((M : ComplexMatrix3) 1 2)) -
      (M : ComplexMatrix3) 0 1 * (star ((M : ComplexMatrix3) 0 1) * (M : ComplexMatrix3) 2 2 -
        (M : ComplexMatrix3) 1 2 * star ((M : ComplexMatrix3) 0 2)) +
      (M : ComplexMatrix3) 0 2 * (star ((M : ComplexMatrix3) 0 1) * star ((M : ComplexMatrix3) 1 2) -
        (M : ComplexMatrix3) 1 1 * star ((M : ComplexMatrix3) 0 2))) := by
    rw [Matrix.det_fin_three, hconj 0 1, hconj 0 2, hconj 1 2]
    ring
  have hemb : standardComplexWindow.embedding M = complexHermToAlbert M := rfl
  have hnorm_c : ∀ z : ℂ, octNormSq (complexToOctonion z) = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [octNormSq_eq_coords, complexToOctonion_apply]
    simp
  have hdot_c : ∀ z1 z2 z3 : ℂ,
      octDot (octonionMul (complexToOctonion z1) (complexToOctonion z3)) (complexToOctonion z2) =
        (z1.re * z3.re - z1.im * z3.im) * z2.re + (z1.re * z3.im + z1.im * z3.re) * z2.im := by
    intro z1 z2 z3
    rw [octDot_eq_coords]
    simp only [oct_fst_mul, oct_snd_mul, complexToOctonion_fst, complexToOctonion_snd,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
      quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
      quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK]
    ring
  have hcub : albertCubicNorm (standardComplexWindow.embedding M) =
      ((M : ComplexMatrix3) 0 0).re * ((M : ComplexMatrix3) 1 1).re * ((M : ComplexMatrix3) 2 2).re -
      ((M : ComplexMatrix3) 0 0).re * (((M : ComplexMatrix3) 1 2).re ^ 2 + ((M : ComplexMatrix3) 1 2).im ^ 2) -
      ((M : ComplexMatrix3) 1 1).re * (((M : ComplexMatrix3) 0 2).re ^ 2 + ((M : ComplexMatrix3) 0 2).im ^ 2) -
      ((M : ComplexMatrix3) 2 2).re * (((M : ComplexMatrix3) 0 1).re ^ 2 + ((M : ComplexMatrix3) 0 1).im ^ 2) +
      2 * ((((M : ComplexMatrix3) 0 1).re * ((M : ComplexMatrix3) 1 2).re -
          ((M : ComplexMatrix3) 0 1).im * ((M : ComplexMatrix3) 1 2).im) * ((M : ComplexMatrix3) 0 2).re +
        (((M : ComplexMatrix3) 0 1).re * ((M : ComplexMatrix3) 1 2).im +
          ((M : ComplexMatrix3) 0 1).im * ((M : ComplexMatrix3) 1 2).re) * ((M : ComplexMatrix3) 0 2).im) := by
    unfold albertCubicNorm
    rw [hemb]
    simp only [complexHermToAlbert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hnorm_c, hdot_c]
  rw [hcub, hdet]
  constructor
  · simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, hd0, hd1, hd2]
    ring
  · simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, hd0, hd1, hd2]
    ring

theorem complexWindow_albertCubicNorm_eq_det (W : ComplexWindow) (M : Hermitian3) :
    albertCubicNorm (W.embedding M) = (M : ComplexMatrix3).det.re ∧
      (M : ComplexMatrix3).det.im = 0 := by
  obtain ⟨g, hg⟩ := native_complexWindow_conjugate_standard W
  rw [← g.map_cubicNorm, hg M]
  exact standardComplexWindow_albertCubicNorm_eq_det M

theorem complexMatrix3_hermitian_det_eq_ofReal (W : ComplexWindow) (M : Hermitian3) :
    (M : ComplexMatrix3).det = ((albertCubicNorm (W.embedding M) : ℝ) : ℂ) := by
  obtain ⟨hre, him⟩ := complexWindow_albertCubicNorm_eq_det W M
  apply Complex.ext
  · simpa using hre.symm
  · simpa using him

theorem windowProj_transport (W : ComplexWindow) (g : NativeAlbertAutomorphism) (y : Albert) :
    windowProj (W.transport g) (g.linearEquiv y) = windowProj W y := by
  dsimp [windowProj]
  have hemb : ∀ x : Hermitian3, (W.transport g).embedding x = g.linearEquiv (W.embedding x) :=
    fun _ => rfl
  simp only [hemb, g.map_tracePairing]

theorem windowProj_eq_of_subalgebra_eq (W₁ W₂ : ComplexWindow)
    (hsub : W₁.toSubalgebra.carrier = W₂.toSubalgebra.carrier) (y : Albert) :
    W₁.embedding (windowProj W₁ y) = W₂.embedding (windowProj W₂ y) := by
  let d := W₁.embedding (windowProj W₁ y) - W₂.embedding (windowProj W₂ y)
  have hd_mem1 : d ∈ W₁.toSubalgebra.carrier := by
    have h1 : W₁.embedding (windowProj W₁ y) ∈ W₁.toSubalgebra.carrier := ⟨windowProj W₁ y, rfl⟩
    have h2 : W₂.embedding (windowProj W₂ y) ∈ W₁.toSubalgebra.carrier := by
      rw [hsub]
      exact ⟨windowProj W₂ y, rfl⟩
    exact W₁.toSubalgebra.carrier.sub_mem h1 h2
  have hd_mem2 : d ∈ W₂.toSubalgebra.carrier := by rwa [← hsub]
  rcases hd_mem1 with ⟨x1, hx1⟩
  rcases hd_mem2 with ⟨x2, hx2⟩
  have horth1 : ∀ z : Hermitian3, tracePairing (W₁.embedding (windowProj W₁ y)) (W₁.embedding z) =
      tracePairing y (W₁.embedding z) := fun z => by
    rw [← windowProj_tracePairing W₁ (W₁.embedding (windowProj W₁ y)) z, windowProj_embedding,
      windowProj_tracePairing]
  have horth2 : ∀ z : Hermitian3, tracePairing (W₂.embedding (windowProj W₂ y)) (W₂.embedding z) =
      tracePairing y (W₂.embedding z) := fun z => by
    rw [← windowProj_tracePairing W₂ (W₂.embedding (windowProj W₂ y)) z, windowProj_embedding,
      windowProj_tracePairing]
  have hdd : tracePairing d d = 0 := by
    calc
      tracePairing d d
        = tracePairing (W₁.embedding (windowProj W₁ y) - W₂.embedding (windowProj W₂ y)) d := rfl
      _ = tracePairing (W₁.embedding (windowProj W₁ y)) d -
            tracePairing (W₂.embedding (windowProj W₂ y)) d := tracePairing_sub_left _ _ _
      _ = tracePairing y d - tracePairing y d := by
            rw [← hx1, horth1 x1, hx1, ← hx2, horth2 x2, hx2]
      _ = 0 := sub_self _
  exact sub_eq_zero.mp ((tracePairing_self_eq_zero_iff d).mp hdd)

theorem windowProj_det_eq_of_subalgebra_eq (W₁ W₂ : ComplexWindow)
    (hsub : W₁.toSubalgebra.carrier = W₂.toSubalgebra.carrier) (y : Albert) :
    (windowProj W₁ y : ComplexMatrix3).det.re = (windowProj W₂ y : ComplexMatrix3).det.re := by
  rw [← (complexWindow_albertCubicNorm_eq_det W₁ (windowProj W₁ y)).1,
    ← (complexWindow_albertCubicNorm_eq_det W₂ (windowProj W₂ y)).1,
    windowProj_eq_of_subalgebra_eq W₁ W₂ hsub y]

private theorem windowProj_eq_of_tracePairing_eq (W : ComplexWindow) (y : Albert) (M : Hermitian3)
    (hpair : ∀ x : Hermitian3, tracePairing (y - W.embedding M) (W.embedding x) = 0) :
    windowProj W y = M := by
  let D : Hermitian3 := windowProj W y - M
  have htr : ((D : ComplexMatrix3) * (D : ComplexMatrix3)).trace.re = 0 := by
    calc
      ((D : ComplexMatrix3) * (D : ComplexMatrix3)).trace.re
        = (((windowProj W y : ComplexMatrix3) - (M : ComplexMatrix3)) * (D : ComplexMatrix3)).trace.re := rfl
      _ = ((windowProj W y : ComplexMatrix3) * (D : ComplexMatrix3) -
            (M : ComplexMatrix3) * (D : ComplexMatrix3)).trace.re := by rw [sub_mul]
      _ = ((windowProj W y : ComplexMatrix3) * (D : ComplexMatrix3)).trace.re -
            ((M : ComplexMatrix3) * (D : ComplexMatrix3)).trace.re := by simp
      _ = tracePairing y (W.embedding D) - tracePairing (W.embedding M) (W.embedding D) := by
            rw [windowProj_tracePairing W y D,
              ← windowProj_tracePairing W (W.embedding M) D, windowProj_embedding]
      _ = tracePairing (y - W.embedding M) (W.embedding D) := (tracePairing_sub_left _ _ _).symm
      _ = 0 := hpair D
  have hD_norm : ∀ i j : Fin 3, ((D : ComplexMatrix3) i j).re ^ 2 + ((D : ComplexMatrix3) i j).im ^ 2 = 0 := by
    have hD_herm : (D : ComplexMatrix3).IsHermitian := D.prop
    have hconj : ∀ i j : Fin 3, (D : ComplexMatrix3) j i = star ((D : ComplexMatrix3) i j) := fun i j => by
      have h := congrFun (congrFun hD_herm.eq j) i
      simpa [Matrix.conjTranspose_apply] using h.symm
    have hnn : ∀ i j : Fin 3,
        0 ≤ (((D : ComplexMatrix3) i j).re ^ 2 + ((D : ComplexMatrix3) i j).im ^ 2) := fun i j => by
      positivity
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
        (((D : ComplexMatrix3) i j).re ^ 2 + ((D : ComplexMatrix3) i j).im ^ 2)) = 0 := by
      have htr_exp : ((D : ComplexMatrix3) * (D : ComplexMatrix3)).trace.re =
          ∑ i : Fin 3, ∑ j : Fin 3,
            (((D : ComplexMatrix3) i j).re ^ 2 + ((D : ComplexMatrix3) i j).im ^ 2) := by
        rw [Matrix.trace]
        simp only [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hconj i j]
        simp [Complex.mul_re]
        ring
      linarith
    intro i j
    have hle1 : (((D : ComplexMatrix3) i j).re ^ 2 + ((D : ComplexMatrix3) i j).im ^ 2) ≤
        ∑ b : Fin 3, (((D : ComplexMatrix3) i b).re ^ 2 + ((D : ComplexMatrix3) i b).im ^ 2) :=
      Finset.single_le_sum (fun b _ => hnn i b) (Finset.mem_univ j)
    have hle2 : (∑ b : Fin 3, (((D : ComplexMatrix3) i b).re ^ 2 + ((D : ComplexMatrix3) i b).im ^ 2)) ≤
        ∑ a : Fin 3, ∑ b : Fin 3, (((D : ComplexMatrix3) a b).re ^ 2 + ((D : ComplexMatrix3) a b).im ^ 2) :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => hnn a b) (Finset.mem_univ i)
    have hnn_ij := hnn i j
    linarith
  have hD0 : D = 0 := by
    apply Subtype.ext
    ext i j
    have hij := hD_norm i j
    have hre : ((D : ComplexMatrix3) i j).re = 0 :=
      sq_eq_zero_iff.mp (by nlinarith [sq_nonneg ((D : ComplexMatrix3) i j).im])
    have him : ((D : ComplexMatrix3) i j).im = 0 :=
      sq_eq_zero_iff.mp (by nlinarith [sq_nonneg ((D : ComplexMatrix3) i j).re])
    apply Complex.ext <;> simp [hre, him]
  exact sub_eq_zero.mp hD0

/-! ## Section 2: `lem:A:window` and `prop:windowdet` -/

theorem sparseFourConfigOct_zero (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : ℝ) (X Y : Octonion) :
    sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y 0 = diagAtom 0 := by
  apply albert_ext <;>
    simp [sparseFourConfigOct, octDyad, diagAtom, octNormSq_scalar, octNormSq_zero,
      octonionConj_zero, octonionMul_zero_right]

theorem tripleDelta_normal_form (B₀ B₁ C₀ C₁ C₂ C₃ : ℝ) :
    tripleDelta
      (diagAtom 0)
      (octDyad ![octonionScalar B₀, octonionScalar B₁, 0])
      (octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃]) =
      B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by
  let q0 := diagAtom 0
  let q1 := octDyad ![octonionScalar B₀, octonionScalar B₁, 0]
  let q2 := octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃]
  let u1 : Fin 3 → ℂ := ![1, 0, 0]
  let u2 : Fin 3 → ℂ := ![B₀, B₁, 0]
  let u3 : Fin 3 → ℂ := ![C₀, ⟨C₁, C₂⟩, C₃]
  let mkDyadMat : (Fin 3 → ℂ) → Hermitian3 := fun u =>
    ⟨Matrix.of (fun i j => u i * star (u j)), by
      ext i j; simp [Matrix.conjTranspose_apply, mul_comm]⟩
  have hq0_emb : standardComplexWindow.embedding (mkDyadMat u1) = q0 := by
    apply albert_ext
    · simp [q0, standardComplexWindow, complexHermToAlbert, mkDyadMat, u1, diagAtom]
    · simp [q0, standardComplexWindow, complexHermToAlbert, mkDyadMat, u1, diagAtom]
    · simp [q0, standardComplexWindow, complexHermToAlbert, mkDyadMat, u1, diagAtom]
    · apply oct_ext <;> simp [q0, standardComplexWindow, complexHermToAlbert, complexToOctonion_apply,
        mkDyadMat, u1, diagAtom, oct_zero_re, oct_zero_imI, oct_zero_imJ, oct_zero_imK,
        oct_zero_s_re, oct_zero_s_imI, oct_zero_s_imJ, oct_zero_s_imK]
    · apply oct_ext <;> simp [q0, standardComplexWindow, complexHermToAlbert, complexToOctonion_apply,
        mkDyadMat, u1, diagAtom, oct_zero_re, oct_zero_imI, oct_zero_imJ, oct_zero_imK,
        oct_zero_s_re, oct_zero_s_imI, oct_zero_s_imJ, oct_zero_s_imK]
    · apply oct_ext <;> simp [q0, standardComplexWindow, complexHermToAlbert, complexToOctonion_apply,
        mkDyadMat, u1, diagAtom, oct_zero_re, oct_zero_imI, oct_zero_imJ, oct_zero_imK,
        oct_zero_s_re, oct_zero_s_imI, oct_zero_s_imJ, oct_zero_s_imK]
  have hq1_emb : standardComplexWindow.embedding (mkDyadMat u2) = q1 := by
    apply albert_ext
    · simp [q1, standardComplexWindow, complexHermToAlbert, mkDyadMat, u2, octDyad,
        octNormSq_scalar, sq]
    · simp [q1, standardComplexWindow, complexHermToAlbert, mkDyadMat, u2, octDyad,
        octNormSq_scalar, sq]
    · simp [q1, standardComplexWindow, complexHermToAlbert, mkDyadMat, u2, octDyad, octNormSq_zero]
    · apply oct_ext <;>
        simp only [q1, standardComplexWindow, complexHermToAlbert, mkDyadMat,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          u2, octDyad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.star_def,
          Complex.zero_re, Complex.zero_im] <;> ring
    · apply oct_ext <;>
        simp only [q1, standardComplexWindow, complexHermToAlbert, mkDyadMat,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          u2, octDyad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.star_def,
          Complex.zero_re, Complex.zero_im] <;> ring
    · apply oct_ext <;>
        simp only [q1, standardComplexWindow, complexHermToAlbert, mkDyadMat,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          u2, octDyad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.star_def,
          Complex.zero_re, Complex.zero_im] <;> ring
  have hq2_emb : standardComplexWindow.embedding (mkDyadMat u3) = q2 := by
    apply albert_ext
    · simp [q2, standardComplexWindow, complexHermToAlbert, mkDyadMat, u3, octDyad,
        octNormSq_scalar, sq]
    · simp only [q2, standardComplexWindow, complexHermToAlbert, mkDyadMat,
        LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply, u3, octDyad,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons,
        octNormSq_eq_coords, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
        oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
        quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
        quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
        quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
        Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.star_def]; ring
    · simp [q2, standardComplexWindow, complexHermToAlbert, mkDyadMat, u3, octDyad,
        octNormSq_scalar, sq]
    · apply oct_ext <;>
        simp only [q2, standardComplexWindow, complexHermToAlbert, mkDyadMat,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          u3, octDyad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
          oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I, oct_fst_zero, oct_snd_zero,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
          Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
    · apply oct_ext <;>
        simp only [q2, standardComplexWindow, complexHermToAlbert, mkDyadMat,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          u3, octDyad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.star_def] <;> ring
    · apply oct_ext <;>
        simp only [q2, standardComplexWindow, complexHermToAlbert, mkDyadMat,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          u3, octDyad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
          oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I, oct_fst_zero, oct_snd_zero,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
          Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
  have hsum_emb : standardComplexWindow.embedding (mkDyadMat u1 + mkDyadMat u2 + mkDyadMat u3) =
      q0 + q1 + q2 := by
    rw [map_add, map_add, hq0_emb, hq1_emb, hq2_emb]
  have hcub : albertCubicNorm (q0 + q1 + q2) = B₁ ^ 2 * C₃ ^ 2 := by
    rw [← hsum_emb, (standardComplexWindow_albertCubicNorm_eq_det _).1]
    rw [Matrix.det_fin_three]
    simp only [AddSubgroup.coe_add, Matrix.add_apply, Matrix.of_apply,
      mkDyadMat, u1, u2, u3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Complex.star_def]
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have htr_all := sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0
  have hp0 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 0 = q0 :=
    sparseFourConfigOct_zero B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0
  have hp1 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 1 = q1 := rfl
  have hp2 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 2 = q2 := rfl
  have ho12 : tracePairing q0 q1 = B₀ ^ 2 := by
    simpa [fpOverlap, hp0, hp1] using htr_all.1
  have ho13 : tracePairing q0 q2 = C₀ ^ 2 := by
    simpa [fpOverlap, hp0, hp2] using htr_all.2.1
  have ho23 : tracePairing q1 q2 = (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 := by
    have h := htr_all.2.2.2.1
    simp only [fpOverlap, hp1, hp2] at h
    rw [h, octNormSq_eq_coords]
    simp only [oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]
    ring
  have hR123 : tracePairing q0 (jordanMul q1 q2) = B₀ * C₀ * (B₀ * C₀ + B₁ * C₁) := by
    rw [← NativeAnalysis.tracePairing_associative q0 q1 q2]
    have h := htr_all.2.2.2.2.2.2.1
    simp only [fpTriangle, hp0, hp1, hp2] at h
    rw [h]
    unfold octonionReal
    simp only [oct_fst_add, oct_fst_smul, oct_fst_scalar, oct_fst_I,
      quat_add_re, quat_smul_re, quat_zero_re]
    ring
  unfold tripleDelta
  rw [hcub, ho12, ho13, ho23, hR123]
  ring

private theorem tripleDelta_atom_normal_exists (p1 p2 p3 : Albert)
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) :
    tripleDelta p1 p2 p3 = 0 ∨
      ∃ (g : NativeAlbertAutomorphism) (B₀ B₁ C₀ C₁ C₂ C₃ : ℝ),
        0 < B₀ ∧ 0 < B₁ ∧ 0 < C₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
        B₀ ^ 2 + B₁ ^ 2 = 1 ∧ C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1 ∧
        g.linearEquiv p1 = diagAtom 0 ∧
        g.linearEquiv p2 = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] ∧
        g.linearEquiv p3 = octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] ∧
        tripleDelta p1 p2 p3 = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by
  by_cases h12_eq : p1 = p2
  · left
    subst h12_eq
    unfold tripleDelta
    have ho : tracePairing p1 p1 = 1 := by unfold tracePairing; rw [hp1.1, hp1.2]
    have hR : tracePairing p1 (jordanMul p1 p3) = tracePairing p1 p3 := by
      rw [← NativeAnalysis.tracePairing_associative, hp1.1]
    rw [ho, hR]; ring
  · by_cases h13_eq : p1 = p3
    · left
      rw [← tripleDelta_symm_23, h13_eq]
      unfold tripleDelta
      have ho : tracePairing p3 p3 = 1 := by unfold tracePairing; rw [hp3.1, hp3.2]
      have hR : tracePairing p3 (jordanMul p3 p2) = tracePairing p3 p2 := by
        rw [← NativeAnalysis.tracePairing_associative, hp3.1]
      rw [ho, hR]; ring
    · by_cases h23_eq : p2 = p3
      · left
        rw [← tripleDelta_symm_13, h23_eq]
        unfold tripleDelta
        have ho : tracePairing p3 p3 = 1 := by unfold tracePairing; rw [hp3.1, hp3.2]
        have hR : tracePairing p3 (jordanMul p3 p1) = tracePairing p3 p1 := by
          rw [← NativeAnalysis.tracePairing_associative, hp3.1]
        rw [ho, hR]; ring
      · by_cases h12_orth : jordanMul p1 p2 = 0
        · left
          unfold tripleDelta
          have ho : tracePairing p1 p2 = 0 := by unfold tracePairing; rw [h12_orth, albertTrace_zero]
          have hR : tracePairing p1 (jordanMul p2 p3) = 0 := by
            rw [← NativeAnalysis.tracePairing_associative, h12_orth, tracePairing_eq_coords]
            simp [albert_zero_fst, albert_zero_snd, octDot_zero_left]
          rw [ho, hR]; ring
        · by_cases h13_orth : jordanMul p1 p3 = 0
          · left
            unfold tripleDelta
            have ho : tracePairing p1 p3 = 0 := by unfold tracePairing; rw [h13_orth, albertTrace_zero]
            have hR : tracePairing p1 (jordanMul p2 p3) = 0 := by
              rw [← NativeAnalysis.tracePairing_associative, jordanMul_comm p1 p2,
                NativeAnalysis.tracePairing_associative, h13_orth, tracePairing_eq_coords]
              simp [albert_zero_fst, albert_zero_snd, octDot_zero_right]
            rw [ho, hR]; ring
          · by_cases h23_orth : jordanMul p2 p3 = 0
            · left
              unfold tripleDelta
              have ho : tracePairing p2 p3 = 0 := by unfold tracePairing; rw [h23_orth, albertTrace_zero]
              have hR : tracePairing p1 (jordanMul p2 p3) = 0 := by
                rw [h23_orth, tracePairing_eq_coords]
                simp [albert_zero_fst, albert_zero_snd, octDot_zero_right]
              rw [ho, hR]; ring
            · right
              have ho12_lt := distinct_nonorth_atom_overlap_strict hp1 hp2 h12_eq h12_orth
              have ho13_lt := distinct_nonorth_atom_overlap_strict hp1 hp3 h13_eq h13_orth
              obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, _D0, _x0, _x1, _x2, _y0, _y1, _y2, _y3, _y4,
                hB0, hB1, hC0, hC2, hC3, _hD0, _hx2, _hy4, hBs, hCs, _hDs, hcfg⟩ :=
                lemma_A_normal ![p1, p2, p3, p1]
                  (fun i => by fin_cases i <;> assumption)
                  ho12_lt.1 ho12_lt.2 ho13_lt.1
                  (by show 0 < tracePairing p1 p1; unfold tracePairing; rw [hp1.1, hp1.2]; norm_num)
              have hg0 : g.linearEquiv p1 = diagAtom 0 :=
                (congrFun hcfg 0).trans (by
                  change sparseFourConfigOct _ _ _ _ _ _ _ _ _ 0 = diagAtom 0
                  exact sparseFourConfigOct_zero _ _ _ _ _ _ _ _ _)
              have hg1 : g.linearEquiv p2 = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] :=
                congrFun hcfg 1
              have hg2 : g.linearEquiv p3 =
                  octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] :=
                congrFun hcfg 2
              have hdel : tripleDelta p1 p2 p3 = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by
                rw [← tripleDelta_automorphism g p1 p2 p3, hg0, hg1, hg2]
                exact tripleDelta_normal_form B₀ B₁ C₀ C₁ C₂ C₃
              exact ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, hB0, hB1, hC0, hC2, hC3, hBs, hCs, hg0, hg1, hg2, hdel⟩

theorem tripleDelta_nonneg {p1 p2 p3 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) :
    0 ≤ tripleDelta p1 p2 p3 := by
  rcases tripleDelta_atom_normal_exists p1 p2 p3 hp1 hp2 hp3 with hz |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdel⟩
  · linarith
  · rw [hdel]; positivity

/-- `lem:A:window(b)`: when `Δ_W(p₁, p₂, p₃) ≠ 0`, pairwise overlaps lie in `(0, 1)`,
and `⟨e, p₁, p₂, p₃⟩` is a `ComplexWindow` characterizing any `ComplexWindow` containing them. -/
theorem lemma_A_window_generated {p1 p2 p3 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3)
    (hne : tripleDelta p1 p2 p3 ≠ 0) :
    0 < tripleDelta p1 p2 p3 ∧
    (0 < tracePairing p1 p2 ∧ tracePairing p1 p2 < 1) ∧
    (0 < tracePairing p1 p3 ∧ tracePairing p1 p3 < 1) ∧
    (0 < tracePairing p2 p3 ∧ tracePairing p2 p3 < 1) ∧
    (∃ W : ComplexWindow, W.Contains p1 ∧ W.Contains p2 ∧ W.Contains p3 ∧
      ∀ x : Albert, W.Contains x ↔ InGeneratedAlgebra ![p1, p2, p3] x) ∧
    (∀ W : ComplexWindow, W.Contains p1 → W.Contains p2 → W.Contains p3 →
      ∀ x : Albert, W.Contains x ↔ InGeneratedAlgebra ![p1, p2, p3] x) := by
  have hpos : 0 < tripleDelta p1 p2 p3 :=
    lt_of_le_of_ne (tripleDelta_nonneg hp1 hp2 hp3) (Ne.symm hne)
  rcases tripleDelta_atom_normal_exists p1 p2 p3 hp1 hp2 hp3 with hz |
    ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, hB0, hB1, hC0, _hC2, _hC3, hBs, hCs, hg0, hg1, hg2, hdel⟩
  · exact absurd hz hne
  have hC2_ne : C₂ ≠ 0 := fun h => by
    rw [h, zero_pow (by norm_num)] at hdel
    ring_nf at hdel; exact hne hdel
  have hC3_ne : C₃ ≠ 0 := fun h => by
    rw [h, zero_pow (by norm_num)] at hdel
    ring_nf at hdel; exact hne hdel
  have ho12 : 0 < tracePairing p1 p2 ∧ tracePairing p1 p2 < 1 := by
    rw [← g.map_tracePairing, hg0, hg1, tracePairing_diagAtom]
    change 0 < octNormSq (octonionScalar B₀) ∧ octNormSq (octonionScalar B₀) < 1
    rw [octNormSq_scalar]
    exact ⟨sq_pos_of_pos hB0, by nlinarith [sq_pos_of_pos hB1]⟩
  have ho13 : 0 < tracePairing p1 p3 ∧ tracePairing p1 p3 < 1 := by
    rw [← g.map_tracePairing, hg0, hg2, tracePairing_diagAtom]
    change 0 < octNormSq (octonionScalar C₀) ∧ octNormSq (octonionScalar C₀) < 1
    rw [octNormSq_scalar]
    exact ⟨sq_pos_of_pos hC0, by
      nlinarith [sq_pos_of_ne_zero hC2_ne, sq_nonneg C₁, sq_nonneg C₃]⟩
  have ho23 : 0 < tracePairing p2 p3 ∧ tracePairing p2 p3 < 1 := by
    have h23_eq : tracePairing p2 p3 = (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 := by
      have htr := (sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0).2.2.2.1
      have hsp1 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 1 = g.linearEquiv p2 := hg1.symm
      have hsp2 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 2 = g.linearEquiv p3 := hg2.symm
      simp only [fpOverlap, hsp1, hsp2, g.map_tracePairing] at htr
      rw [htr, octNormSq_eq_coords]
      simp only [oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
        oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
        quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
        quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
        quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]
      ring
    rw [h23_eq]
    have hBC2_pos : 0 < (B₁ * C₂) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hB1.ne' hC2_ne)
    have hlt : (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 < 1 := by
      have hdiff : (B₀ ^ 2 + B₁ ^ 2) * (C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2) -
          ((B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2) =
          (B₀ * C₁ - B₁ * C₀) ^ 2 + B₀ ^ 2 * C₂ ^ 2 + (B₀ ^ 2 + B₁ ^ 2) * C₃ ^ 2 := by ring
      rw [hBs, hCs, one_mul] at hdiff
      have hpos_diff : 0 < (B₀ * C₁ - B₁ * C₀) ^ 2 + B₀ ^ 2 * C₂ ^ 2 + 1 * C₃ ^ 2 := by
        have hC3p : 0 < C₃ ^ 2 := sq_pos_of_ne_zero hC3_ne
        nlinarith [sq_nonneg (B₀ * C₁ - B₁ * C₀), sq_nonneg (B₀ * C₂)]
      linarith
    exact ⟨by positivity, hlt⟩
  have hgen_std : ∀ x : Albert,
      InGeneratedAlgebra ![g.linearEquiv p1, g.linearEquiv p2, g.linearEquiv p3] x ↔
        standardComplexWindow.Contains x := by
    have hq_eq : ![g.linearEquiv p1, g.linearEquiv p2, g.linearEquiv p3] =
        ![(sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 0 0) 0,
          (sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 0 0) 1,
          (sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 0 0) 2] := by
      funext k
      fin_cases k <;> dsimp
      · exact hg0.trans (by
          change diagAtom 0 = sparseFourConfigOct _ _ _ _ _ _ _ _ _ 0
          exact (sparseFourConfigOct_zero _ _ _ _ _ _ _ _ _).symm)
      · exact hg1
      · exact hg2
    rw [hq_eq]
    exact lemma_A_generate_three B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 0 0 hB0 hB1 hC0 hC2_ne hC3_ne
  let W0 := standardComplexWindow.transport g.symm
  have hW0_char : ∀ x : Albert, W0.Contains x ↔ InGeneratedAlgebra ![p1, p2, p3] x := by
    intro x
    have hc1 : W0.Contains x ↔ standardComplexWindow.Contains (g.linearEquiv x) := by
      constructor
      · rintro ⟨M, rfl⟩
        exact ⟨M, by
          change standardComplexWindow.embedding M =
            g.linearEquiv (g.symm.linearEquiv (standardComplexWindow.embedding M))
          exact (LinearEquiv.apply_symm_apply g.linearEquiv _).symm⟩
      · rintro ⟨M, hM⟩
        exact ⟨M, by
          change g.symm.linearEquiv (standardComplexWindow.embedding M) = x
          rw [hM]
          exact LinearEquiv.symm_apply_apply g.linearEquiv x⟩
    rw [hc1, ← hgen_std (g.linearEquiv x)]
    constructor
    · intro hx B hB
      let Bg : NativeJordanSubalgebra :=
        { carrier := B.carrier.map g.linearEquiv.toLinearMap
          unit_mem := ⟨albertUnit, B.unit_mem, g.preserves_unit⟩
          product_mem := by
            rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
            exact ⟨jordanMul a b, B.product_mem a ha b hb, g.preserves_product a b⟩ }
      have hBg : ∀ i : Fin 3, ![g.linearEquiv p1, g.linearEquiv p2, g.linearEquiv p3] i ∈ Bg.carrier := by
        intro i
        fin_cases i
        · exact ⟨p1, hB 0, rfl⟩
        · exact ⟨p2, hB 1, rfl⟩
        · exact ⟨p3, hB 2, rfl⟩
      rcases hx Bg hBg with ⟨y, hyB, hy_eq⟩
      have hxg : x = y := g.linearEquiv.injective hy_eq.symm
      rwa [hxg]
    · intro hx B hB
      let Bg : NativeJordanSubalgebra :=
        { carrier := B.carrier.map g.symm.linearEquiv.toLinearMap
          unit_mem := ⟨albertUnit, B.unit_mem, g.symm.preserves_unit⟩
          product_mem := by
            rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
            exact ⟨jordanMul a b, B.product_mem a ha b hb, g.symm.preserves_product a b⟩ }
      have hBg : ∀ i : Fin 3, ![p1, p2, p3] i ∈ Bg.carrier := by
        intro i
        fin_cases i
        · exact ⟨g.linearEquiv p1, hB 0, LinearEquiv.symm_apply_apply g.linearEquiv p1⟩
        · exact ⟨g.linearEquiv p2, hB 1, LinearEquiv.symm_apply_apply g.linearEquiv p2⟩
        · exact ⟨g.linearEquiv p3, hB 2, LinearEquiv.symm_apply_apply g.linearEquiv p3⟩
      rcases hx Bg hBg with ⟨y, hyB, hy_eq⟩
      have hgy : g.linearEquiv x = y := by
        rw [← hy_eq]
        exact LinearEquiv.apply_symm_apply g.linearEquiv y
      rwa [hgy]
  have hW0_1 : W0.Contains p1 := (hW0_char p1).mpr (fun _ hB => hB 0)
  have hW0_2 : W0.Contains p2 := (hW0_char p2).mpr (fun _ hB => hB 1)
  have hW0_3 : W0.Contains p3 := (hW0_char p3).mpr (fun _ hB => hB 2)
  have hW_all : ∀ W : ComplexWindow, W.Contains p1 → W.Contains p2 → W.Contains p3 →
      ∀ x : Albert, W.Contains x ↔ InGeneratedAlgebra ![p1, p2, p3] x := by
    intro W h1 h2 h3
    have hle : W0.toSubalgebra.carrier ≤ W.toSubalgebra.carrier := by
      intro x hx
      have hxc : W0.Contains x := hx
      rw [hW0_char] at hxc
      exact hxc W.toSubalgebra (fun i => by fin_cases i <;> assumption)
    have hfin : Module.finrank ℝ W0.toSubalgebra.carrier = Module.finrank ℝ W.toSubalgebra.carrier := by
      rw [complexWindow_finrank W0, complexWindow_finrank W]
    haveI := complexWindow_finite W
    have heq_sub : W0.toSubalgebra.carrier = W.toSubalgebra.carrier :=
      Submodule.eq_of_le_of_finrank_eq hle hfin
    intro x
    have hx_mem : W.Contains x ↔ x ∈ W.toSubalgebra.carrier := Iff.rfl
    have hx0_mem : W0.Contains x ↔ x ∈ W0.toSubalgebra.carrier := Iff.rfl
    rw [hx_mem, ← heq_sub, ← hx0_mem, hW0_char]
  exact ⟨hpos, ho12, ho13, ho23, ⟨W0, hW0_1, hW0_2, hW0_3, hW0_char⟩, hW_all⟩

private theorem windowProj_standardComplexWindow_fourth_det
    (D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄ : ℝ) :
    let X : Octonion := octonionScalar x₀ + x₁ • octI + x₂ • octJ
    let Y : Octonion := y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL
    let q3 := octDyad ![octonionScalar D₀, X, Y]
    (windowProj standardComplexWindow q3 : ComplexMatrix3).det.re = D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 := by
  intro X Y q3
  let m01 : ℂ := ⟨D₀ * x₀, -(D₀ * x₁)⟩
  let m02 : ℂ := ⟨D₀ * y₀, -(D₀ * y₁)⟩
  let m12 : ℂ := ⟨x₀ * y₀ + x₁ * y₁ + x₂ * y₂, x₁ * y₀ - x₀ * y₁ - x₂ * y₃⟩
  let Mmat : ComplexMatrix3 :=
    Matrix.of ![![((D₀ ^ 2 : ℝ) : ℂ), m01, m02],
       ![star m01, ((x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 : ℝ) : ℂ), m12],
       ![star m02, star m12, ((y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 : ℝ) : ℂ)]]
  let M : Hermitian3 :=
    ⟨Mmat, by
      rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
      ext i j
      rw [Matrix.conjTranspose_apply]
      dsimp only [Mmat, Matrix.of_apply]
      fin_cases i <;> fin_cases j <;>
        (apply Complex.ext <;>
          simp [m01, m02, m12, Complex.star_def, sq, Complex.mul_re, Complex.mul_im])⟩
  have hproj : windowProj standardComplexWindow q3 = M := by
    apply windowProj_eq_of_tracePairing_eq
    intro x
    let d := q3 - standardComplexWindow.embedding M
    have hd_012 : d.1 0 = 0 ∧ d.1 1 = 0 ∧ d.1 2 = 0 := by
      refine ⟨?_, ?_, ?_⟩ <;>
        (dsimp only [d]; rw [albert_sub_fst]
         simp only [q3, standardComplexWindow, complexHermToAlbert, M, Mmat, octDyad, X, Y,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, octNormSq_eq_coords,
          oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
          oct_fst_scalar, oct_snd_scalar, oct_fst_one, oct_snd_one,
          oct_fst_I, oct_snd_I, oct_fst_J, oct_snd_J, oct_fst_K, oct_snd_K, oct_fst_L, oct_snd_L,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          Complex.ofReal_re]; ring)
    have hd_diag : ∀ k : Fin 3, d.1 k = 0 := fun k => by
      fin_cases k
      · exact hd_012.1
      · exact hd_012.2.1
      · exact hd_012.2.2
    have hd_01 : (d.2 0).1.re = 0 ∧ (d.2 0).1.imI = 0 := by
      dsimp only [d]; rw [albert_sub_snd]
      constructor <;>
        (simp only [q3, standardComplexWindow, complexHermToAlbert, M, Mmat, m01, octDyad, X, Y,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_add, oct_snd_add, oct_fst_sub, oct_snd_sub,
          oct_fst_smul, oct_snd_smul, oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_scalar, oct_snd_scalar, oct_fst_one, oct_snd_one,
          oct_fst_I, oct_snd_I, oct_fst_J, oct_snd_J, oct_fst_K, oct_snd_K, oct_fst_L, oct_snd_L,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
          Complex.star_def, Complex.mul_re, Complex.mul_im]; ring)
    have hd_02 : (d.2 1).1.re = 0 ∧ (d.2 1).1.imI = 0 := by
      dsimp only [d]; rw [albert_sub_snd]
      constructor <;>
        (simp only [q3, standardComplexWindow, complexHermToAlbert, M, Mmat, m02, octDyad, X, Y,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_add, oct_snd_add, oct_fst_sub, oct_snd_sub,
          oct_fst_smul, oct_snd_smul, oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_scalar, oct_snd_scalar, oct_fst_one, oct_snd_one,
          oct_fst_I, oct_snd_I, oct_fst_J, oct_snd_J, oct_fst_K, oct_snd_K, oct_fst_L, oct_snd_L,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
          Complex.star_def, Complex.mul_re, Complex.mul_im]; ring)
    have hd_12 : (d.2 2).1.re = 0 ∧ (d.2 2).1.imI = 0 := by
      dsimp only [d]; rw [albert_sub_snd]
      constructor <;>
        (simp only [q3, standardComplexWindow, complexHermToAlbert, M, Mmat, m12, octDyad, X, Y,
          LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
          oct_fst_add, oct_snd_add, oct_fst_sub, oct_snd_sub,
          oct_fst_smul, oct_snd_smul, oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
          oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
          oct_fst_scalar, oct_snd_scalar, oct_fst_one, oct_snd_one,
          oct_fst_I, oct_snd_I, oct_fst_J, oct_snd_J, oct_fst_K, oct_snd_K, oct_fst_L, oct_snd_L,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
          quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
          quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
          quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
          Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
          Complex.star_def, Complex.mul_re, Complex.mul_im]; ring)
    have hdot_c : ∀ o : Octonion, o.1.re = 0 → o.1.imI = 0 → ∀ z : ℂ,
        octDot o (complexToOctonion z) = 0 := fun o hr hi z => by
      rw [octDot_eq_coords, complexToOctonion_apply]
      simp [hr, hi]
    have h20 : (standardComplexWindow.embedding x).2 0 = complexToOctonion ((x : ComplexMatrix3) 0 1) := rfl
    have h21 : (standardComplexWindow.embedding x).2 1 = complexToOctonion ((x : ComplexMatrix3) 0 2) := rfl
    have h22 : (standardComplexWindow.embedding x).2 2 = complexToOctonion ((x : ComplexMatrix3) 1 2) := rfl
    rw [tracePairing_eq_coords, hd_diag 0, hd_diag 1, hd_diag 2, h20, h21, h22,
      hdot_c _ hd_01.1 hd_01.2, hdot_c _ hd_02.1 hd_02.2, hdot_c _ hd_12.1 hd_12.2]
    ring
  rw [hproj, Matrix.det_fin_three]
  simp only [M, Mmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Complex.star_def, m01, m02, m12]
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, sq]
  ring

/-- `prop:windowdet` (zero case): if `Δ_W(p₁, p₂, p₃) = 0`, then `𝒜(p₁, p₂, p₃, p₄) = 0`. -/
theorem prop_windowdet_zero {p1 p2 p3 p4 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) (hp4 : IsAtom p4)
    (hz : tripleDelta p1 p2 p3 = 0) :
    fourPointInvariant ![p1, p2, p3, p4] = 0 := by
  have hp_atoms : ∀ i : Fin 4, IsAtom (![p1, p2, p3, p4] i) := fun i => by
    fin_cases i <;> assumption
  by_cases h12_eq : p1 = p2
  · obtain ⟨Q, hQ⟩ := lemma_A_degenerate ![p1, p2, p3, p4] hp_atoms
      ⟨0, 1, by decide, Or.inl h12_eq⟩
    exact lemma_A_zero_of_quat Q ![p1, p2, p3, p4] hp_atoms hQ
  · by_cases h13_eq : p1 = p3
    · obtain ⟨Q, hQ⟩ := lemma_A_degenerate ![p1, p2, p3, p4] hp_atoms
        ⟨0, 2, by decide, Or.inl h13_eq⟩
      exact lemma_A_zero_of_quat Q ![p1, p2, p3, p4] hp_atoms hQ
    · by_cases h23_eq : p2 = p3
      · obtain ⟨Q, hQ⟩ := lemma_A_degenerate ![p1, p2, p3, p4] hp_atoms
          ⟨1, 2, by decide, Or.inl h23_eq⟩
        exact lemma_A_zero_of_quat Q ![p1, p2, p3, p4] hp_atoms hQ
      · by_cases h12_orth : jordanMul p1 p2 = 0
        · obtain ⟨Q, hQ⟩ := lemma_A_degenerate ![p1, p2, p3, p4] hp_atoms
            ⟨0, 1, by decide, Or.inr h12_orth⟩
          exact lemma_A_zero_of_quat Q ![p1, p2, p3, p4] hp_atoms hQ
        · by_cases h13_orth : jordanMul p1 p3 = 0
          · obtain ⟨Q, hQ⟩ := lemma_A_degenerate ![p1, p2, p3, p4] hp_atoms
              ⟨0, 2, by decide, Or.inr h13_orth⟩
            exact lemma_A_zero_of_quat Q ![p1, p2, p3, p4] hp_atoms hQ
          · by_cases h23_orth : jordanMul p2 p3 = 0
            · obtain ⟨Q, hQ⟩ := lemma_A_degenerate ![p1, p2, p3, p4] hp_atoms
                ⟨1, 2, by decide, Or.inr h23_orth⟩
              exact lemma_A_zero_of_quat Q ![p1, p2, p3, p4] hp_atoms hQ
            · by_cases h14_eq : p1 = p4
              · obtain ⟨Q, hQ⟩ := lemma_A_degenerate ![p1, p2, p3, p4] hp_atoms
                  ⟨0, 3, by decide, Or.inl h14_eq⟩
                exact lemma_A_zero_of_quat Q ![p1, p2, p3, p4] hp_atoms hQ
              · by_cases h14_orth : jordanMul p1 p4 = 0
                · obtain ⟨Q, hQ⟩ := lemma_A_degenerate ![p1, p2, p3, p4] hp_atoms
                    ⟨0, 3, by decide, Or.inr h14_orth⟩
                  exact lemma_A_zero_of_quat Q ![p1, p2, p3, p4] hp_atoms hQ
                · have ho12 := distinct_nonorth_atom_overlap_strict hp1 hp2 h12_eq h12_orth
                  have ho13 := distinct_nonorth_atom_overlap_strict hp1 hp3 h13_eq h13_orth
                  have ho14 := distinct_nonorth_atom_overlap_strict hp1 hp4 h14_eq h14_orth
                  obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
                    hB0, hB1, hC0, _hC2, _hC3, _hD0, _hx2, _hy4, _hBs, _hCs, _hDs, hcfg⟩ :=
                    lemma_A_normal ![p1, p2, p3, p4] hp_atoms
                      ho12.1 ho12.2 ho13.1 ho14.1
                  have hg0 : g.linearEquiv p1 = diagAtom 0 :=
                    (congrFun hcfg 0).trans (by
                      change sparseFourConfigOct _ _ _ _ _ _ _ _ _ 0 = diagAtom 0
                      exact sparseFourConfigOct_zero _ _ _ _ _ _ _ _ _)
                  have hg1 : g.linearEquiv p2 = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] :=
                    congrFun hcfg 1
                  have hg2 : g.linearEquiv p3 =
                      octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] :=
                    congrFun hcfg 2
                  have hdel : tripleDelta p1 p2 p3 = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by
                    rw [← tripleDelta_automorphism g p1 p2 p3, hg0, hg1, hg2]
                    exact tripleDelta_normal_form B₀ B₁ C₀ C₁ C₂ C₃
                  rw [hz] at hdel
                  have hC23 : C₂ ^ 2 * C₃ ^ 2 = 0 := by
                    have hpre : B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 ≠ 0 := by positivity
                    have heq : (B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2) * (C₂ ^ 2 * C₃ ^ 2) = 0 := by
                      calc
                        (B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2) * (C₂ ^ 2 * C₃ ^ 2)
                          = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by ring
                        _ = 0 := hdel.symm
                    exact (mul_eq_zero.mp heq).resolve_left hpre
                  have hfp := fourPointInvariant_automorphism_invariant g ![p1, p2, p3, p4]
                  have hcfg' := hcfg
                  rw [octOne_eq_scalar, ← octonionScalar_eq_smul y₀] at hcfg'
                  rw [hcfg', sparseFourConfig_fourPointInvariant] at hfp
                  rw [← hfp]
                  have hfac : B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 =
                      (B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2) * (C₂ ^ 2 * C₃ ^ 2) := by ring
                  rw [hfac, hC23, mul_zero]

/-- A fourth atom overlaps at least one vertex of every nonzero window triangle. -/
theorem tripleDelta_nonzero_some_overlap {p1 p2 p3 p4 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) (hp4 : IsAtom p4)
    (hdel : tripleDelta p1 p2 p3 ≠ 0) :
    0 < tracePairing p1 p4 ∨ 0 < tracePairing p2 p4 ∨ 0 < tracePairing p3 p4 := by
  by_contra hnone
  push Not at hnone
  have hz1 : tracePairing p1 p4 = 0 := le_antisymm hnone.1 (tracePairing_atom_bounds hp1 hp4).1
  have hz2 : tracePairing p2 p4 = 0 := le_antisymm hnone.2.1 (tracePairing_atom_bounds hp2 hp4).1
  have hz3 : tracePairing p3 p4 = 0 := le_antisymm hnone.2.2 (tracePairing_atom_bounds hp3 hp4).1
  rcases tripleDelta_atom_normal_exists p1 p2 p3 hp1 hp2 hp3 with hz |
    ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, _hB0, hB1, _hC0, _hC2, _hC3, _hBs, _hCs, hg0, hg1, hg2, hd⟩
  · exact hdel hz
  have hC3_ne : C₃ ≠ 0 := fun h => by
    rw [h, zero_pow (by norm_num)] at hd; ring_nf at hd; exact hdel hd
  let q4 := g.linearEquiv p4
  have hq4_atom : IsAtom q4 := g.map_isAtom hp4
  have hq4_d0 : q4.1 0 = 0 := by
    rw [← tracePairing_diagAtom 0 q4, ← hg0, g.map_tracePairing]; exact hz1
  obtain ⟨hq4_01, hq4_02⟩ := isAtom_zero_row0 hq4_atom hq4_d0
  have hq4_d1 : q4.1 1 = 0 := by
    have hp24 : tracePairing (g.linearEquiv p2) q4 = 0 := by
      rw [g.map_tracePairing]; exact hz2
    rw [hg1, tracePairing_eq_coords] at hp24
    simp [octDyad, octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right,
      hq4_d0, hq4_01, hq4_02, octDot_zero_left, octDot_zero_right] at hp24
    exact hp24.resolve_left hB1.ne'
  have hq4_d2 : q4.1 2 = 1 := by
    have htr := hq4_atom.2
    rw [albertTrace, Fin.sum_univ_three, hq4_d0, hq4_d1] at htr
    linarith
  have hq4_12 : q4.2 2 = 0 := by
    have hf := congrArg (fun x : Albert => x.1 0) (albertSharp_atom_eq_zero q4 hq4_atom)
    simp only [albertSharp, albert_zero_fst, Matrix.cons_val_zero, hq4_d1, zero_mul,
      zero_sub, neg_eq_zero] at hf
    exact (octNormSq_eq_zero _).mp hf
  have hp34 : tracePairing (g.linearEquiv p3) q4 = 0 := by
    rw [g.map_tracePairing]; exact hz3
  rw [hg2, tracePairing_eq_coords] at hp34
  simp [octDyad, octNormSq_scalar, hq4_d0, hq4_d1, hq4_d2, hq4_01, hq4_02, hq4_12,
    octDot_zero_right] at hp34
  exact hC3_ne hp34

/-- `prop:windowdet`: for ANY `ComplexWindow` `W` containing atoms `p₁, p₂, p₃` and ANY atom `p₄`,
`𝒜(p₁, p₂, p₃, p₄) = Δ_W(p₁, p₂, p₃) * Re(det(P_W p₄))` (including `Δ_W = 0`). -/
theorem prop_windowdet (W : ComplexWindow) {p1 p2 p3 p4 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) (hp4 : IsAtom p4)
    (h1 : W.Contains p1) (h2 : W.Contains p2) (h3 : W.Contains p3) :
    fourPointInvariant ![p1, p2, p3, p4] =
      windowDelta W p1 p2 p3 * (windowProj W p4 : ComplexMatrix3).det.re := by
  rw [windowDelta_eq_tripleDelta]
  by_cases hdel : tripleDelta p1 p2 p3 = 0
  · rw [hdel, zero_mul]
    exact prop_windowdet_zero hp1 hp2 hp3 hp4 hdel
  · obtain ⟨_hpos, _ho12, _ho13, _ho23, _hWex, hW_all⟩ :=
      lemma_A_window_generated hp1 hp2 hp3 hdel
    have hsome := tripleDelta_nonzero_some_overlap hp1 hp2 hp3 hp4 hdel
    have hperm_proof : ∀ (σ : Equiv.Perm (Fin 4)), σ 3 = 3 →
        let a := fun i : Fin 4 => (![p1, p2, p3, p4] : Fin 4 → Albert) (σ i)
        0 < tracePairing (a 0) (a 3) →
        fourPointInvariant ![p1, p2, p3, p4] =
          tripleDelta p1 p2 p3 * (windowProj W p4 : ComplexMatrix3).det.re := by
      intro σ hσ3 a ha03
      have ha_atom : ∀ i, IsAtom (a i) := fun i => by
        dsimp only [a]
        generalize hk : σ i = k
        fin_cases k <;> dsimp <;> first | exact hp1 | exact hp2 | exact hp3 | exact hp4
      have ha3_eq : a 3 = p4 := by dsimp only [a]; rw [hσ3]; rfl
      have ha_del : tripleDelta (a 0) (a 1) (a 2) = tripleDelta p1 p2 p3 := by
        let τ : Equiv.Perm (Fin 3) :=
          { toFun := fun i => ⟨(σ i.castSucc).1, by
              have hne3 : σ i.castSucc ≠ 3 := by
                rw [← hσ3]; exact σ.injective.ne (Fin.castSucc_ne_last i)
              have hlt : (σ i.castSucc).1 < 4 := (σ i.castSucc).isLt
              have hv : (σ i.castSucc).1 ≠ 3 := fun h => hne3 (Fin.ext h)
              omega⟩
            invFun := fun i => ⟨(σ.symm i.castSucc).1, by
              have hne3 : σ.symm i.castSucc ≠ 3 := fun he => by
                have := congrArg σ he
                rw [σ.apply_symm_apply, hσ3] at this
                exact Fin.castSucc_ne_last i this
              have hlt : (σ.symm i.castSucc).1 < 4 := (σ.symm i.castSucc).isLt
              have hv : (σ.symm i.castSucc).1 ≠ 3 := fun h => hne3 (Fin.ext h)
              omega⟩
            left_inv := fun i => by ext; simp [Equiv.apply_symm_apply]
            right_inv := fun i => by ext; simp [Equiv.apply_symm_apply] }
        have ha012 : a 0 = (![p1, p2, p3] : Fin 3 → Albert) (τ 0) ∧
            a 1 = (![p1, p2, p3] : Fin 3 → Albert) (τ 1) ∧
            a 2 = (![p1, p2, p3] : Fin 3 → Albert) (τ 2) := by
          refine ⟨?_, ?_, ?_⟩ <;>
            (dsimp only [a, τ]
             have hk_eq : ∀ (k : Fin 4) (hk : k ≠ 3), (![p1, p2, p3, p4] : Fin 4 → Albert) k =
                 (![p1, p2, p3] : Fin 3 → Albert) ⟨k.1, by
                   have hlt : k.1 < 4 := k.isLt
                   have hv : k.1 ≠ 3 := fun h => hk (Fin.ext h)
                   omega⟩ := fun k hk => by
               fin_cases k <;> [rfl; rfl; rfl; exact absurd rfl hk]
             exact hk_eq _ (by rw [← hσ3]; exact σ.injective.ne (by decide)))
        rw [ha012.1, ha012.2.1, ha012.2.2]
        have hperm3 : ∀ (f : Fin 3 → Albert) (π : Equiv.Perm (Fin 3)),
            tripleDelta (f (π 0)) (f (π 1)) (f (π 2)) = tripleDelta (f 0) (f 1) (f 2) := by
          intro f π
          have hf3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := fun x => by
            have hx := x.isLt
            have hcases : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 := by omega
            rcases hcases with h | h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr (Or.inl (Fin.ext h))
            · exact Or.inr (Or.inr (Fin.ext h))
          have h0 := hf3 (π 0)
          have h1' := hf3 (π 1)
          have h2' := hf3 (π 2)
          have h01 : π 0 ≠ π 1 := π.injective.ne (by decide)
          have h02 : π 0 ≠ π 2 := π.injective.ne (by decide)
          have h12 : π 1 ≠ π 2 := π.injective.ne (by decide)
          rcases h0 with h0 | h0 | h0 <;> rcases h1' with h1' | h1' | h1' <;>
            rcases h2' with h2' | h2' | h2' <;>
            first
            | exact False.elim (h01 (h0.trans h1'.symm))
            | exact False.elim (h02 (h0.trans h2'.symm))
            | exact False.elim (h12 (h1'.trans h2'.symm))
            | (rw [h0, h1', h2']; done)
            | (rw [h0, h1', h2', tripleDelta_symm_23]; done)
            | (rw [h0, h1', h2', tripleDelta_symm_12]; done)
            | (rw [h0, h1', h2', tripleDelta_symm_23, tripleDelta_symm_12]; done)
            | (rw [h0, h1', h2', tripleDelta_symm_12, tripleDelta_symm_23]; done)
            | (rw [h0, h1', h2', tripleDelta_symm_13]; done)
        exact hperm3 ![p1, p2, p3] τ
      have ha_del_ne : tripleDelta (a 0) (a 1) (a 2) ≠ 0 := by rw [ha_del]; exact hdel
      have ha01_eq : a 0 ≠ a 1 := fun heq => ha_del_ne (by
        unfold tripleDelta; rw [heq]
        have ho : tracePairing (a 1) (a 1) = 1 := by unfold tracePairing; rw [(ha_atom 1).1, (ha_atom 1).2]
        have hR : tracePairing (a 1) (jordanMul (a 1) (a 2)) = tracePairing (a 1) (a 2) := by
          rw [← NativeAnalysis.tracePairing_associative, (ha_atom 1).1]
        rw [ho, hR]; ring)
      have ha02_eq : a 0 ≠ a 2 := fun heq => ha_del_ne (by
        rw [← tripleDelta_symm_23, heq]
        unfold tripleDelta
        have ho : tracePairing (a 2) (a 2) = 1 := by unfold tracePairing; rw [(ha_atom 2).1, (ha_atom 2).2]
        have hR : tracePairing (a 2) (jordanMul (a 2) (a 1)) = tracePairing (a 2) (a 1) := by
          rw [← NativeAnalysis.tracePairing_associative, (ha_atom 2).1]
        rw [ho, hR]; ring)
      have ha01_orth : jordanMul (a 0) (a 1) ≠ 0 := fun h0 => ha_del_ne (by
        unfold tripleDelta
        have ho : tracePairing (a 0) (a 1) = 0 := by unfold tracePairing; rw [h0, albertTrace_zero]
        have hR : tracePairing (a 0) (jordanMul (a 1) (a 2)) = 0 := by
          rw [← NativeAnalysis.tracePairing_associative, h0, tracePairing_eq_coords]
          simp [albert_zero_fst, albert_zero_snd, octDot_zero_left]
        rw [ho, hR]; ring)
      have ha02_orth : jordanMul (a 0) (a 2) ≠ 0 := fun h0 => ha_del_ne (by
        unfold tripleDelta
        have ho : tracePairing (a 0) (a 2) = 0 := by unfold tracePairing; rw [h0, albertTrace_zero]
        have hR : tracePairing (a 0) (jordanMul (a 1) (a 2)) = 0 := by
          rw [← NativeAnalysis.tracePairing_associative, jordanMul_comm (a 0) (a 1),
            NativeAnalysis.tracePairing_associative, h0, tracePairing_eq_coords]
          simp [albert_zero_fst, albert_zero_snd, octDot_zero_right]
        rw [ho, hR]; ring)
      have ho01 := distinct_nonorth_atom_overlap_strict (ha_atom 0) (ha_atom 1) ha01_eq ha01_orth
      have ho02 := distinct_nonorth_atom_overlap_strict (ha_atom 0) (ha_atom 2) ha02_eq ha02_orth
      obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
        hB0, hB1, hC0, _hC2, _hC3, hD0, _hx2, _hy4, _hBs, _hCs, _hDs, hcfg⟩ :=
        lemma_A_normal a ha_atom ho01.1 ho01.2 ho02.1 ha03
      have hg0 : g.linearEquiv (a 0) = diagAtom 0 :=
        (congrFun hcfg 0).trans (by
          change sparseFourConfigOct _ _ _ _ _ _ _ _ _ 0 = diagAtom 0
          exact sparseFourConfigOct_zero _ _ _ _ _ _ _ _ _)
      have hg1 : g.linearEquiv (a 1) = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] :=
        congrFun hcfg 1
      have hg2 : g.linearEquiv (a 2) =
          octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] :=
        congrFun hcfg 2
      have hg3 : g.linearEquiv p4 =
          octDyad ![octonionScalar D₀, octonionScalar x₀ + x₁ • octI + x₂ • octJ,
            y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL] := by
        rw [← ha3_eq]; exact congrFun hcfg 3
      have hdel_eq : tripleDelta p1 p2 p3 = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by
        rw [← ha_del, ← tripleDelta_automorphism g (a 0) (a 1) (a 2), hg0, hg1, hg2]
        exact tripleDelta_normal_form B₀ B₁ C₀ C₁ C₂ C₃
      let W0 := standardComplexWindow.transport g.symm
      have hW0_a0 : W0.Contains (a 0) := by
        refine ⟨hermE 0, ?_⟩
        apply g.linearEquiv.injective
        change g.linearEquiv (g.symm.linearEquiv (standardComplexWindow.embedding (hermE 0))) = _
        rw [auto_apply_symm, hg0]
        apply albert_ext
        · simp [standardComplexWindow, complexHermToAlbert, hermE_apply, diagAtom]
        · simp [standardComplexWindow, complexHermToAlbert, hermE_apply, diagAtom]
        · simp [standardComplexWindow, complexHermToAlbert, hermE_apply, diagAtom]
        · apply oct_ext <;> simp [standardComplexWindow, complexHermToAlbert, hermE_apply,
            complexToOctonion_apply, diagAtom, oct_zero_re, oct_zero_imI, oct_zero_imJ,
            oct_zero_imK, oct_zero_s_re, oct_zero_s_imI, oct_zero_s_imJ, oct_zero_s_imK]
        · apply oct_ext <;> simp [standardComplexWindow, complexHermToAlbert, hermE_apply,
            complexToOctonion_apply, diagAtom, oct_zero_re, oct_zero_imI, oct_zero_imJ,
            oct_zero_imK, oct_zero_s_re, oct_zero_s_imI, oct_zero_s_imJ, oct_zero_s_imK]
        · apply oct_ext <;> simp [standardComplexWindow, complexHermToAlbert, hermE_apply,
            complexToOctonion_apply, diagAtom, oct_zero_re, oct_zero_imI, oct_zero_imJ,
            oct_zero_imK, oct_zero_s_re, oct_zero_s_imI, oct_zero_s_imJ, oct_zero_s_imK]
      have hW0_a1 : W0.Contains (a 1) := by
        let u2 : Fin 3 → ℂ := ![B₀, B₁, 0]
        refine ⟨⟨Matrix.of (fun i j => u2 i * star (u2 j)), by
          ext i j; simp [mul_comm]⟩, ?_⟩
        apply g.linearEquiv.injective
        change g.linearEquiv (g.symm.linearEquiv _) = _
        rw [auto_apply_symm, hg1]
        apply albert_ext
        · simp [standardComplexWindow, complexHermToAlbert, u2, octDyad, octNormSq_scalar, sq]
        · simp [standardComplexWindow, complexHermToAlbert, u2, octDyad, octNormSq_scalar, sq]
        · simp [standardComplexWindow, complexHermToAlbert, u2, octDyad, octNormSq_zero]
        · apply oct_ext <;>
            simp only [standardComplexWindow, complexHermToAlbert, u2, octDyad,
              LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
              Complex.conj_re, Complex.conj_im, Complex.star_def,
              Complex.zero_re, Complex.zero_im] <;> ring
        · apply oct_ext <;>
            simp only [standardComplexWindow, complexHermToAlbert, u2, octDyad,
              LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
              Complex.conj_re, Complex.conj_im, Complex.star_def,
              Complex.zero_re, Complex.zero_im] <;> ring
        · apply oct_ext <;>
            simp only [standardComplexWindow, complexHermToAlbert, u2, octDyad,
              LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
              Complex.conj_re, Complex.conj_im, Complex.star_def,
              Complex.zero_re, Complex.zero_im] <;> ring
      have hW0_a2 : W0.Contains (a 2) := by
        let u3 : Fin 3 → ℂ := ![C₀, ⟨C₁, C₂⟩, C₃]
        refine ⟨⟨Matrix.of (fun i j => u3 i * star (u3 j)), by
          ext i j; simp [mul_comm]⟩, ?_⟩
        apply g.linearEquiv.injective
        change g.linearEquiv (g.symm.linearEquiv _) = _
        rw [auto_apply_symm, hg2]
        apply albert_ext
        · simp [standardComplexWindow, complexHermToAlbert, u3, octDyad, octNormSq_scalar, sq]
        · simp only [standardComplexWindow, complexHermToAlbert, u3, octDyad,
            LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons,
            octNormSq_eq_coords, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
            oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
            quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
            quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
            quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
            Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.star_def]; ring
        · simp [standardComplexWindow, complexHermToAlbert, u3, octDyad, octNormSq_scalar, sq]
        · apply oct_ext <;>
            simp only [standardComplexWindow, complexHermToAlbert, u3, octDyad,
              LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
              oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I, oct_fst_zero, oct_snd_zero,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
              Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
              Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
        · apply oct_ext <;>
            simp only [standardComplexWindow, complexHermToAlbert, u3, octDyad,
              LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
              Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring
        · apply oct_ext <;>
            simp only [standardComplexWindow, complexHermToAlbert, u3, octDyad,
              LinearMap.coe_mk, AddHom.coe_mk, Subtype.coe_mk, Matrix.of_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons, complexToOctonion_fst, complexToOctonion_snd,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
              oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I, oct_fst_zero, oct_snd_zero,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK,
              Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
              Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
      have hW0_in : ∀ i : Fin 3, W0.Contains (![p1, p2, p3] i) := by
        have hmem_W0 : ∀ i : Fin 3, a i.castSucc ∈ W0.toSubalgebra.carrier := fun i => by
          fin_cases i <;> dsimp <;> [exact hW0_a0; exact hW0_a1; exact hW0_a2]
        intro i
        let j4 := σ.symm i.castSucc
        have hj_ne3 : j4 ≠ 3 := fun he => by
          have := congrArg σ he
          rw [σ.apply_symm_apply, hσ3] at this
          exact Fin.castSucc_ne_last i this
        have hj_lt : j4.1 < 3 := by
          have hlt : j4.1 < 4 := j4.isLt
          have hv : j4.1 ≠ 3 := fun h => hj_ne3 (Fin.ext h)
          omega
        have hj_eq : (⟨j4.1, hj_lt⟩ : Fin 3).castSucc = j4 := by ext; rfl
        have ha_eq : a (⟨j4.1, hj_lt⟩ : Fin 3).castSucc = ![p1, p2, p3] i := by
          dsimp only [a]
          rw [hj_eq, show σ j4 = i.castSucc from σ.apply_symm_apply i.castSucc]
          fin_cases i <;> dsimp <;> rfl
        rw [← ha_eq]
        exact hmem_W0 ⟨j4.1, hj_lt⟩
      have hsub_le : W0.toSubalgebra.carrier ≤ W.toSubalgebra.carrier := by
        intro x hx
        have hxc : W0.Contains x := hx
        rw [hW_all W0 (hW0_in 0) (hW0_in 1) (hW0_in 2)] at hxc
        exact hxc W.toSubalgebra (fun k => by fin_cases k <;> assumption)
      haveI := complexWindow_finite W
      have hsub_eq : W0.toSubalgebra.carrier = W.toSubalgebra.carrier :=
        Submodule.eq_of_le_of_finrank_eq hsub_le
          (by rw [complexWindow_finrank W0, complexWindow_finrank W])
      have hdet_W : (windowProj W p4 : ComplexMatrix3).det.re = D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 := by
        rw [windowProj_det_eq_of_subalgebra_eq W W0 hsub_eq.symm p4]
        have htrp : windowProj (standardComplexWindow.transport g.symm) p4 =
            windowProj standardComplexWindow (g.linearEquiv p4) := by
          have h := windowProj_transport standardComplexWindow g.symm (g.linearEquiv p4)
          rw [auto_symm_apply] at h
          exact h
        change (windowProj (standardComplexWindow.transport g.symm) p4 : ComplexMatrix3).det.re = _
        rw [htrp, hg3]
        exact windowProj_standardComplexWindow_fourth_det D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄
      have hfp_a : fourPointInvariant a = fourPointInvariant ![p1, p2, p3, p4] :=
        fourPointInvariant_perm_invariant σ ![p1, p2, p3, p4]
      have hfp_g := fourPointInvariant_automorphism_invariant g a
      have hcfg' := hcfg
      rw [octOne_eq_scalar, ← octonionScalar_eq_smul y₀] at hcfg'
      rw [hcfg', sparseFourConfig_fourPointInvariant] at hfp_g
      rw [← hfp_a, ← hfp_g, hdel_eq, hdet_W]
      ring
    rcases hsome with h03 | h13 | h23
    · exact hperm_proof 1 rfl h03
    · exact hperm_proof (Equiv.swap 0 1) (by decide) (by
        change 0 < tracePairing (![p1, p2, p3, p4] ((Equiv.swap (0 : Fin 4) 1) 0))
          (![p1, p2, p3, p4] ((Equiv.swap (0 : Fin 4) 1) 3))
        have hs0 : (Equiv.swap (0 : Fin 4) 1) 0 = 1 := by decide
        have hs3 : (Equiv.swap (0 : Fin 4) 1) 3 = 3 := by decide
        rw [hs0, hs3]; exact h13)
    · exact hperm_proof (Equiv.swap 0 2) (by decide) (by
        change 0 < tracePairing (![p1, p2, p3, p4] ((Equiv.swap (0 : Fin 4) 2) 0))
          (![p1, p2, p3, p4] ((Equiv.swap (0 : Fin 4) 2) 3))
        have hs0 : (Equiv.swap (0 : Fin 4) 2) 0 = 2 := by decide
        have hs3 : (Equiv.swap (0 : Fin 4) 2) 3 = 3 := by decide
        rw [hs0, hs3]; exact h23)

/-! ## Section 3: Rank Trichotomy (`cor:fp:rank`) -/

theorem windowProj_atom_isDensity (W : ComplexWindow) {p : Albert} (hp : IsAtom p) :
    IsComplexDensity3 (windowProj W p : ComplexMatrix3) :=
  windowProj_isComplexDensity3 W p ⟨⟨p, hp.1.symm⟩, hp.2⟩

private theorem complexDensity3_spectral (M : Hermitian3) (hd : IsComplexDensity3 (M : ComplexMatrix3)) :
    ∃ (U : ComplexMatrix3) (μ : Fin 3 → ℝ),
      (U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1) ∧
      ((M : ComplexMatrix3) = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose) ∧
      (∀ i, 0 ≤ μ i) ∧
      (μ 0 + μ 1 + μ 2 = 1) ∧
      ((M : ComplexMatrix3).det = ((μ 0 * μ 1 * μ 2 : ℝ) : ℂ)) ∧
      ((M : ComplexMatrix3).rank = Fintype.card {i : Fin 3 // (μ i : ℂ) ≠ 0}) := by
  have hM : (M : ComplexMatrix3).IsHermitian := M.prop
  let U : ComplexMatrix3 := hM.eigenvectorUnitary
  let μ := hM.eigenvalues
  have hUU : U.conjTranspose * U = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp hM.eigenvectorUnitary.prop
  have hUUt : U * U.conjTranspose = 1 := by
    exact Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.prop
  have hspec : (M : ComplexMatrix3) =
      U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose := by
    simpa [U, μ, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose,
      Matrix.mul_assoc] using hM.spectral_theorem
  have hμ_nn : ∀ i, 0 ≤ μ i := fun i => (hM.posSemidef_iff_eigenvalues_nonneg.mp hd.1) i
  have hμ_sum : μ 0 + μ 1 + μ 2 = 1 := by
    have htr := hd.2
    rw [hspec, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul,
      Matrix.trace_diagonal, Fin.sum_univ_three] at htr
    simpa [Complex.add_re, Complex.ofReal_re] using congrArg Complex.re htr
  have hdet_U : U.det * U.conjTranspose.det = 1 := by
    rw [← Matrix.det_mul, hUUt, Matrix.det_one]
  have hdet : (M : ComplexMatrix3).det = ((μ 0 * μ 1 * μ 2 : ℝ) : ℂ) := by
    rw [hspec, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    calc
      U.det * (∏ i : Fin 3, (μ i : ℂ)) * U.conjTranspose.det
        = (U.det * U.conjTranspose.det) * (∏ i : Fin 3, (μ i : ℂ)) := by ring
      _ = 1 * (∏ i : Fin 3, (μ i : ℂ)) := by rw [hdet_U]
      _ = ((μ 0 * μ 1 * μ 2 : ℝ) : ℂ) := by
            rw [one_mul, Fin.prod_univ_three]; push_cast; ring
  have hU_unit : IsUnit U.det :=
    ⟨⟨U.det, U.conjTranspose.det, hdet_U, by rw [mul_comm, hdet_U]⟩, rfl⟩
  have hUs_unit : IsUnit U.conjTranspose.det :=
    ⟨⟨U.conjTranspose.det, U.det, by rw [mul_comm, hdet_U], hdet_U⟩, rfl⟩
  have hrank : (M : ComplexMatrix3).rank = Fintype.card {i : Fin 3 // (μ i : ℂ) ≠ 0} := by
    rw [hspec, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUs_unit,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU_unit, Matrix.rank_diagonal]
  exact ⟨U, μ, ⟨hUU, hUUt⟩, hspec, hμ_nn, hμ_sum, hdet, hrank⟩

theorem windowProj_atom_det_bounds (W : ComplexWindow) {p : Albert} (hp : IsAtom p) :
    0 ≤ (windowProj W p : ComplexMatrix3).det.re ∧
      (windowProj W p : ComplexMatrix3).det.re ≤ 1 / 27 := by
  have hd := windowProj_atom_isDensity W hp
  obtain ⟨_, μ, _, _, hμ_nn, hμ_sum, hdet, _⟩ := complexDensity3_spectral (windowProj W p) hd
  rw [hdet, Complex.ofReal_re]
  exact ⟨mul_nonneg (mul_nonneg (hμ_nn 0) (hμ_nn 1)) (hμ_nn 2),
    three_nonneg_am_gm (hμ_nn 0) (hμ_nn 1) (hμ_nn 2) (by linarith)⟩

theorem windowProj_atom_det_eq_max_iff (W : ComplexWindow) {p : Albert} (hp : IsAtom p) :
    (windowProj W p : ComplexMatrix3).det.re = 1 / 27 ↔
      (windowProj W p : ComplexMatrix3) = (1 / 3 : ℂ) • (1 : ComplexMatrix3) := by
  have hd := windowProj_atom_isDensity W hp
  obtain ⟨U, μ, ⟨_, hUUt⟩, hspec, hμ_nn, hμ_sum, hdet, _⟩ := complexDensity3_spectral (windowProj W p) hd
  constructor
  · intro heq
    rw [hdet, Complex.ofReal_re] at heq
    obtain ⟨h0, h1, h2⟩ := (three_nonneg_am_gm_eq_iff (hμ_nn 0) (hμ_nn 1) (hμ_nn 2) (by linarith)).mp heq
    have hdiag : Matrix.diagonal (fun i : Fin 3 => (μ i : ℂ)) =
        (1 / 3 : ℂ) • (1 : ComplexMatrix3) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]
    rw [hspec, hdiag, mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hUUt]
  · intro heq
    rw [heq, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
    norm_num

theorem windowProj_atom_rankOne_iff_contains (W : ComplexWindow) {p : Albert} (hp : IsAtom p) :
    IsComplexRankOneProjection (windowProj W p : ComplexMatrix3) ↔ W.Contains p := by
  constructor
  · rintro ⟨v, hv_norm, hv_eq⟩
    let M : Hermitian3 := windowProj W p
    have hM_sq : (M : ComplexMatrix3) * (M : ComplexMatrix3) = (M : ComplexMatrix3) := by
      ext i j
      rw [Matrix.mul_apply, hv_eq i j]
      have hsum : ∑ k : Fin 3, (M : ComplexMatrix3) i k * (M : ComplexMatrix3) k j =
          ∑ k : Fin 3, (v i * star (v k)) * (v k * star (v j)) :=
        Finset.sum_congr rfl fun k _ => by rw [hv_eq i k, hv_eq k j]
      rw [hsum]
      calc
        ∑ k : Fin 3, (v i * star (v k)) * (v k * star (v j))
          = (v i * star (v j)) * ∑ k : Fin 3, star (v k) * v k := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
        _ = v i * star (v j) := by rw [hv_norm, mul_one]
    have hM_tr : Matrix.trace (M : ComplexMatrix3) = 1 := (windowProj_atom_isDensity W hp).2
    let q := W.embedding M
    have hq_atom : IsAtom q := by
      constructor
      · symm; apply W.preserves_product; rw [hM_sq, ← two_smul ℝ, smul_smul]; norm_num
      · rw [W.preserves_trace, hM_tr, Complex.one_re]
    have hpq : tracePairing p q = 1 := by
      rw [← windowProj_tracePairing W p M]
      change ((M : ComplexMatrix3) * (M : ComplexMatrix3)).trace.re = 1
      rw [hM_sq, hM_tr, Complex.one_re]
    have hpp : tracePairing p p = 1 := by unfold tracePairing; rw [hp.1, hp.2]
    have hqq : tracePairing q q = 1 := by unfold tracePairing; rw [hq_atom.1, hq_atom.2]
    have hdiff : tracePairing (p - q) (p - q) = 0 := by
      rw [tracePairing_sub_left, tracePairing_sub_right, tracePairing_sub_right,
        tracePairing_comm q p, hpp, hqq, hpq]
      ring
    have hp_eq : p = q := sub_eq_zero.mp ((tracePairing_self_eq_zero_iff (p - q)).mp hdiff)
    exact ⟨M, hp_eq.symm⟩
  · rintro ⟨M, rfl⟩
    have hproj : windowProj W (W.embedding M) = M := windowProj_embedding W M
    rw [hproj]
    have hd := windowProj_atom_isDensity W hp
    rw [hproj] at hd
    obtain ⟨U, μ, ⟨hUU, _⟩, hspec, hμ_nn, hμ_sum, _, _⟩ := complexDensity3_spectral M hd
    have hM_sq : (M : ComplexMatrix3) * (M : ComplexMatrix3) = (M : ComplexMatrix3) := by
      have hsub_herm : (1 / 2 : ℝ) • ((M : ComplexMatrix3) * (M : ComplexMatrix3) +
          (M : ComplexMatrix3) * (M : ComplexMatrix3)) ∈ Hermitian3 := by
        rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, M.prop, star_trivial, add_comm]
      let M2 : Hermitian3 := ⟨(1 / 2 : ℝ) • ((M : ComplexMatrix3) * (M : ComplexMatrix3) +
        (M : ComplexMatrix3) * (M : ComplexMatrix3)), hsub_herm⟩
      have hprod := W.preserves_product M M M2 rfl
      have hsub : M2 = M := by
        apply W.injective; rw [hprod, hp.1]
      have hval := congrArg Subtype.val hsub
      simpa [M2, ← two_smul ℝ, smul_smul] using hval
    have hdiag_sq : Matrix.diagonal (fun i => (μ i : ℂ)) * Matrix.diagonal (fun i => (μ i : ℂ)) =
        Matrix.diagonal (fun i => (μ i : ℂ)) := by
      calc
        Matrix.diagonal (fun i => (μ i : ℂ)) * Matrix.diagonal (fun i => (μ i : ℂ))
          = (U.conjTranspose * U) * Matrix.diagonal (fun i => (μ i : ℂ)) *
              (U.conjTranspose * U) * Matrix.diagonal (fun i => (μ i : ℂ)) *
              (U.conjTranspose * U) := by
                rw [hUU, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
        _ = U.conjTranspose * ((U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose) *
              (U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose)) * U := by
                simp only [Matrix.mul_assoc]
        _ = U.conjTranspose * ((M : ComplexMatrix3) * (M : ComplexMatrix3)) * U := by
              rw [← hspec]
        _ = U.conjTranspose * (M : ComplexMatrix3) * U := by rw [hM_sq]
        _ = U.conjTranspose * (U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose) * U := by
              rw [hspec]
        _ = (U.conjTranspose * U) * Matrix.diagonal (fun i => (μ i : ℂ)) *
              (U.conjTranspose * U) := by
              simp only [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun i => (μ i : ℂ)) := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
    have hμ_bool : ∀ i : Fin 3, μ i = 0 ∨ μ i = 1 := fun i => by
      have hi := congrArg Complex.re (congrFun (congrFun hdiag_sq i) i)
      simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, ← Complex.ofReal_mul,
        Complex.ofReal_re] at hi
      have hfac : μ i * (μ i - 1) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    have hpick : ∃ k : Fin 3, μ k = 1 ∧ ∀ j : Fin 3, j ≠ k → μ j = 0 := by
      rcases hμ_bool 0 with h0 | h0 <;> rcases hμ_bool 1 with h1 | h1 <;> rcases hμ_bool 2 with h2 | h2
      · exfalso; linarith
      · exact ⟨2, h2, fun j hj => by fin_cases j <;> [exact h0; exact h1; exact absurd rfl hj]⟩
      · exact ⟨1, h1, fun j hj => by fin_cases j <;> [exact h0; exact absurd rfl hj; exact h2]⟩
      · exfalso; linarith
      · exact ⟨0, h0, fun j hj => by fin_cases j <;> [exact absurd rfl hj; exact h1; exact h2]⟩
      · exfalso; linarith
      · exfalso; linarith
      · exfalso; linarith
    rcases hpick with ⟨k, hk1, hk0⟩
    refine ⟨fun i => U i k, ?_, ?_⟩
    · have hnorm : (U.conjTranspose * U) k k = 1 := by
        rw [hUU, Matrix.one_apply_eq]
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, mul_comm] using hnorm
    · intro i j
      rw [hspec]
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Matrix.conjTranspose_apply, RCLike.star_def]
      rw [Fin.sum_univ_three]
      fin_cases k <;> dsimp at hk1 hk0 ⊢
      · rw [hk1, hk0 1 (by decide), hk0 2 (by decide)]; simp
      · rw [hk1, hk0 0 (by decide), hk0 2 (by decide)]; simp
      · rw [hk1, hk0 0 (by decide), hk0 1 (by decide)]; simp

/-- `cor:fp:rank`: complete rank trichotomy and determinant bounds for `M = windowProj W p₄`. -/
theorem cor_fp_rank (W : ComplexWindow) {p1 p2 p3 p4 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) (hp4 : IsAtom p4)
    (h1 : W.Contains p1) (h2 : W.Contains p2) (h3 : W.Contains p3)
    (hΔ : 0 < windowDelta W p1 p2 p3) :
    let M : ComplexMatrix3 := (windowProj W p4 : ComplexMatrix3)
    IsComplexDensity3 M ∧
    (0 ≤ M.det.re ∧ M.det.re ≤ 1 / 27) ∧
    (M.det.re = 1 / 27 ↔ M = (1 / 3 : ℂ) • (1 : ComplexMatrix3)) ∧
    (M.rank = 1 ↔ W.Contains p4) ∧
    (M.rank ≤ 2 ↔ M.det.re = 0) ∧
    (M.rank = 3 ↔ 0 < M.det.re) ∧
    (M.rank ≤ 2 ↔ ∃ Q : QuaternionicWindow,
      (∀ i, ![p1, p2, p3, p4] i ∈ Q.subalgebra.carrier) ∧
      ∀ x, W.Contains x → x ∈ Q.subalgebra.carrier) ∧
    (M.rank = 3 ↔ GeneratesAlbert ![p1, p2, p3, p4]) := by
  intro M
  have hd := windowProj_atom_isDensity W hp4
  obtain ⟨U, μ, ⟨hUU, _⟩, hspec, hμ_nn, hμ_sum, hdet, hrank⟩ :=
    complexDensity3_spectral (windowProj W p4) hd
  have hrank_le3 : M.rank ≤ 3 := by
    change M.rank ≤ 3
    rw [hrank]
    calc Fintype.card {i : Fin 3 // (μ i : ℂ) ≠ 0} ≤ Fintype.card (Fin 3) :=
          Fintype.card_subtype_le _
      _ = 3 := Fintype.card_fin 3
  have hrank_le2_det : M.rank ≤ 2 ↔ M.det.re = 0 := by
    rw [hrank, hdet, Complex.ofReal_re]
    constructor
    · intro hle
      by_contra hnz
      have h0 : μ 0 ≠ 0 := fun h => hnz (by rw [h]; ring)
      have h1' : μ 1 ≠ 0 := fun h => hnz (by rw [h]; ring)
      have h2' : μ 2 ≠ 0 := fun h => hnz (by rw [h]; ring)
      have hcard3 : Fintype.card {i : Fin 3 // (μ i : ℂ) ≠ 0} = 3 := by
        have huniv : ∀ i : Fin 3, (μ i : ℂ) ≠ 0 := fun i => by
          fin_cases i
          · exact Complex.ofReal_ne_zero.mpr h0
          · exact Complex.ofReal_ne_zero.mpr h1'
          · exact Complex.ofReal_ne_zero.mpr h2'
        exact (Fintype.card_congr (Equiv.subtypeUnivEquiv huniv)).trans (Fintype.card_fin 3)
      omega
    · intro h0
      have hkz : ∃ k : Fin 3, (μ k : ℂ) = 0 := by
        rcases mul_eq_zero.mp h0 with h01 | h2
        · rcases mul_eq_zero.mp h01 with h0' | h1'
          · exact ⟨0, Complex.ofReal_eq_zero.mpr h0'⟩
          · exact ⟨1, Complex.ofReal_eq_zero.mpr h1'⟩
        · exact ⟨2, Complex.ofReal_eq_zero.mpr h2⟩
      rcases hkz with ⟨k, hk⟩
      have hcomp_pos : 0 < Fintype.card {i : Fin 3 // (μ i : ℂ) = 0} :=
        Fintype.card_pos_iff.mpr ⟨⟨k, hk⟩⟩
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      omega
  have hrank3_det : M.rank = 3 ↔ 0 < M.det.re := by
    have hbounds := windowProj_atom_det_bounds W hp4
    constructor
    · intro hr3
      have hnot : ¬ M.rank ≤ 2 := by omega
      have hnz : M.det.re ≠ 0 := fun hz => hnot (hrank_le2_det.mpr hz)
      exact lt_of_le_of_ne hbounds.1 (Ne.symm hnz)
    · intro hpos
      have hnot : ¬ M.rank ≤ 2 := fun hle => hpos.ne' (hrank_le2_det.mp hle)
      omega
  have hrank1_rkOne : M.rank = 1 ↔ IsComplexRankOneProjection M := by
    constructor
    · intro hr1
      rw [hrank] at hr1
      obtain ⟨⟨k, hk⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hr1
      have hother : ∀ j : Fin 3, j ≠ k → μ j = 0 := fun j hj => by
        by_contra hj_ne
        have heq := huniq ⟨j, Complex.ofReal_ne_zero.mpr hj_ne⟩
        exact hj (congrArg Subtype.val heq)
      have hk1 : μ k = 1 := by
        fin_cases k <;> dsimp at *
        · have := hother 1 (by decide); have := hother 2 (by decide); linarith
        · have := hother 0 (by decide); have := hother 2 (by decide); linarith
        · have := hother 0 (by decide); have := hother 1 (by decide); linarith
      refine ⟨fun i => U i k, ?_, ?_⟩
      · have hnorm : (U.conjTranspose * U) k k = 1 := by
          rw [hUU, Matrix.one_apply_eq]
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, mul_comm] using hnorm
      · intro i j
        change M i j = _
        rw [show M = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose from hspec]
        simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true, Matrix.conjTranspose_apply, RCLike.star_def]
        rw [Fin.sum_univ_three]
        fin_cases k <;> dsimp at hk1 hother ⊢
        · rw [hk1, hother 1 (by decide), hother 2 (by decide)]; simp
        · rw [hk1, hother 0 (by decide), hother 2 (by decide)]; simp
        · rw [hk1, hother 0 (by decide), hother 1 (by decide)]; simp
    · intro hrk1
      rcases hrk1 with ⟨v, hv_norm, hv_eq⟩
      have hM_sq : M * M = M := by
        ext i j
        rw [Matrix.mul_apply, hv_eq i j]
        have hsum : ∑ k : Fin 3, M i k * M k j =
            ∑ k : Fin 3, (v i * star (v k)) * (v k * star (v j)) :=
          Finset.sum_congr rfl fun k _ => by rw [hv_eq i k, hv_eq k j]
        rw [hsum]
        calc
          ∑ k : Fin 3, (v i * star (v k)) * (v k * star (v j))
            = (v i * star (v j)) * ∑ k : Fin 3, star (v k) * v k := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
          _ = v i * star (v j) := by rw [hv_norm, mul_one]
      have hdiag_sq : Matrix.diagonal (fun i => (μ i : ℂ)) * Matrix.diagonal (fun i => (μ i : ℂ)) =
          Matrix.diagonal (fun i => (μ i : ℂ)) := by
        calc
          _ = (U.conjTranspose * U) * Matrix.diagonal (fun i => (μ i : ℂ)) *
                (U.conjTranspose * U) * Matrix.diagonal (fun i => (μ i : ℂ)) *
                (U.conjTranspose * U) := by
              rw [hUU, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
          _ = U.conjTranspose * (M * M) * U := by
              rw [show M = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose from hspec]
              simp only [Matrix.mul_assoc]
          _ = U.conjTranspose * M * U := by rw [hM_sq]
          _ = Matrix.diagonal (fun i => (μ i : ℂ)) := by
              rw [show M = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose from hspec]
              calc
                U.conjTranspose * (U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose) * U
                  = (U.conjTranspose * U) * Matrix.diagonal (fun i => (μ i : ℂ)) *
                      (U.conjTranspose * U) := by simp only [Matrix.mul_assoc]
                _ = Matrix.diagonal (fun i => (μ i : ℂ)) := by
                      rw [hUU, Matrix.one_mul, Matrix.mul_one]
      have hμ_bool : ∀ i : Fin 3, μ i = 0 ∨ μ i = 1 := fun i => by
        have hi := congrArg Complex.re (congrFun (congrFun hdiag_sq i) i)
        simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, ← Complex.ofReal_mul,
          Complex.ofReal_re] at hi
        have hfac : μ i * (μ i - 1) = 0 := by linarith
        rcases mul_eq_zero.mp hfac with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h)
      have hpick : ∃ k : Fin 3, μ k = 1 ∧ ∀ j : Fin 3, j ≠ k → μ j = 0 := by
        rcases hμ_bool 0 with h0 | h0 <;> rcases hμ_bool 1 with h1 | h1 <;> rcases hμ_bool 2 with h2 | h2
        · exfalso; linarith
        · exact ⟨2, h2, fun j hj => by fin_cases j <;> [exact h0; exact h1; exact absurd rfl hj]⟩
        · exact ⟨1, h1, fun j hj => by fin_cases j <;> [exact h0; exact absurd rfl hj; exact h2]⟩
        · exfalso; linarith
        · exact ⟨0, h0, fun j hj => by fin_cases j <;> [exact absurd rfl hj; exact h1; exact h2]⟩
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
      rcases hpick with ⟨k, hk1, hk0⟩
      rw [hrank, Fintype.card_eq_one_iff]
      refine ⟨⟨k, Complex.ofReal_ne_zero.mpr (by rw [hk1]; norm_num)⟩, fun ⟨j, hj⟩ => ?_⟩
      apply Subtype.ext
      by_contra hne
      exact hj (Complex.ofReal_eq_zero.mpr (hk0 j hne))
  have hrank1_contains : M.rank = 1 ↔ W.Contains p4 :=
    hrank1_rkOne.trans (windowProj_atom_rankOne_iff_contains W hp4)
  have hfp_det := prop_windowdet W hp1 hp2 hp3 hp4 h1 h2 h3
  have hΔ_ne : tripleDelta p1 p2 p3 ≠ 0 := by
    rw [← windowDelta_eq_tripleDelta W p1 p2 p3]; exact hΔ.ne'
  have hW_gen := (lemma_A_window_generated hp1 hp2 hp3 hΔ_ne).2.2.2.2.2 W h1 h2 h3
  have hp_atoms : ∀ i : Fin 4, IsAtom (![p1, p2, p3, p4] i) := fun i => by
    fin_cases i <;> assumption
  have hrank_le2_quat : M.rank ≤ 2 ↔ ∃ Q : QuaternionicWindow,
      (∀ i, ![p1, p2, p3, p4] i ∈ Q.subalgebra.carrier) ∧
      ∀ x, W.Contains x → x ∈ Q.subalgebra.carrier := by
    constructor
    · intro hle
      have hdet0 : M.det.re = 0 := hrank_le2_det.mp hle
      have hfp0 : fourPointInvariant ![p1, p2, p3, p4] = 0 := by
        rw [hfp_det, hdet0, mul_zero]
      obtain ⟨Q, hQ⟩ := (thm_fourpoint ![p1, p2, p3, p4] hp_atoms).2.1.mp hfp0
      refine ⟨Q, hQ, fun x hx => ?_⟩
      rw [hW_gen x] at hx
      exact hx Q.subalgebra (fun i => by fin_cases i <;> [exact hQ 0; exact hQ 1; exact hQ 2])
    · rintro ⟨Q, hQ, _⟩
      have hfp0 : fourPointInvariant ![p1, p2, p3, p4] = 0 :=
        (thm_fourpoint ![p1, p2, p3, p4] hp_atoms).2.1.mpr ⟨Q, hQ⟩
      rw [hfp_det] at hfp0
      have hdet0 : M.det.re = 0 := (mul_eq_zero.mp hfp0).resolve_left hΔ.ne'
      exact hrank_le2_det.mpr hdet0
  have hrank3_gen : M.rank = 3 ↔ GeneratesAlbert ![p1, p2, p3, p4] := by
    rw [hrank3_det]
    constructor
    · intro hpos
      have hfp_pos : 0 < fourPointInvariant ![p1, p2, p3, p4] := by
        rw [hfp_det]; exact mul_pos hΔ hpos
      exact (thm_fourpoint ![p1, p2, p3, p4] hp_atoms).2.2.1.mp hfp_pos
    · intro hgen
      have hfp_pos : 0 < fourPointInvariant ![p1, p2, p3, p4] :=
        (thm_fourpoint ![p1, p2, p3, p4] hp_atoms).2.2.1.mpr hgen
      rw [hfp_det] at hfp_pos
      have hmul := mul_pos_iff.mp hfp_pos
      rcases hmul with ⟨_, hpos⟩ | ⟨hneg, _⟩
      · exact hpos
      · linarith
  exact ⟨hd, windowProj_atom_det_bounds W hp4, windowProj_atom_det_eq_max_iff W hp4,
    hrank1_contains, hrank_le2_det, hrank3_det, hrank_le2_quat, hrank3_gen⟩

/-! ## Section 4: Bounds, `maximizerConfig`, `prop:max`, `cor:fp:maxmixed`, and `prop:windowlaw` -/

theorem lem_fp_DeltaWmax {p1 p2 p3 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) :
    tripleDelta p1 p2 p3 ≤ 4 / 729 ∧
      (∀ W : ComplexWindow, windowDelta W p1 p2 p3 ≤ 4 / 729) ∧
      (tripleDelta p1 p2 p3 = 4 / 729 ↔
        tracePairing p1 p2 = 1 / 3 ∧ tracePairing p1 p3 = 1 / 3 ∧
        tracePairing p2 p3 = 1 / 3 ∧ tracePairing p1 (jordanMul p2 p3) = 1 / 9) := by
  have hbound : tripleDelta p1 p2 p3 ≤ 4 / 729 := by
    rcases tripleDelta_atom_normal_exists p1 p2 p3 hp1 hp2 hp3 with hz |
      ⟨_g, B₀, B₁, C₀, C₁, C₂, C₃, hB0, hB1, hC0, hC2, hC3, hBs, hCs, _hg0, _hg1, _hg2, hdel⟩
    · rw [hz]; norm_num
    · have hB_le : B₀ ^ 2 * B₁ ^ 4 ≤ 4 / 27 := by
        have hB1_sq : B₁ ^ 2 = 1 - B₀ ^ 2 := by linarith
        rw [show B₀ ^ 2 * B₁ ^ 4 = B₀ ^ 2 * (1 - B₀ ^ 2) ^ 2 by rw [← hB1_sq]; ring]
        exact unit_prod_sq_bound (sq_nonneg B₀) (by nlinarith [sq_nonneg B₁])
      have hC_le : C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 ≤ 1 / 27 :=
        three_nonneg_am_gm (sq_nonneg C₀) (sq_nonneg C₂) (sq_nonneg C₃) (by nlinarith [sq_nonneg C₁])
      rw [hdel]
      have h1 : 0 ≤ B₀ ^ 2 * B₁ ^ 4 := by positivity
      have h2 : 0 ≤ C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by positivity
      calc
        B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2
          = (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) := by ring
        _ ≤ (4 / 27) * (1 / 27) := mul_le_mul hB_le hC_le h2 (by norm_num)
        _ = 4 / 729 := by norm_num
  have hiff : tripleDelta p1 p2 p3 = 4 / 729 ↔
      tracePairing p1 p2 = 1 / 3 ∧ tracePairing p1 p3 = 1 / 3 ∧
      tracePairing p2 p3 = 1 / 3 ∧ tracePairing p1 (jordanMul p2 p3) = 1 / 9 := by
    constructor
    · intro heq
      rcases tripleDelta_atom_normal_exists p1 p2 p3 hp1 hp2 hp3 with hz |
        ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, hB0, hB1, hC0, hC2, hC3, hBs, hCs, hg0, hg1, hg2, hdel⟩
      · exfalso; linarith
      have hB_le : B₀ ^ 2 * B₁ ^ 4 ≤ 4 / 27 := by
        have hB1_sq : B₁ ^ 2 = 1 - B₀ ^ 2 := by linarith
        rw [show B₀ ^ 2 * B₁ ^ 4 = B₀ ^ 2 * (1 - B₀ ^ 2) ^ 2 by rw [← hB1_sq]; ring]
        exact unit_prod_sq_bound (sq_nonneg B₀) (by nlinarith [sq_nonneg B₁])
      have hC_le : C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 ≤ 1 / 27 :=
        three_nonneg_am_gm (sq_nonneg C₀) (sq_nonneg C₂) (sq_nonneg C₃) (by nlinarith [sq_nonneg C₁])
      have hB_eq : B₀ ^ 2 * B₁ ^ 4 = 4 / 27 := by
        by_contra hne
        have hlt : B₀ ^ 2 * B₁ ^ 4 < 4 / 27 := lt_of_le_of_ne hB_le hne
        have hC_nn : 0 ≤ C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by positivity
        have hlt_p : (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) < 4 / 729 := by
          by_cases hC0' : C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 = 0
          · rw [hC0', mul_zero]; norm_num
          · have hC_pos : 0 < C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := lt_of_le_of_ne hC_nn (Ne.symm hC0')
            calc (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2)
                < (4 / 27) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) := mul_lt_mul_of_pos_right hlt hC_pos
              _ ≤ (4 / 27) * (1 / 27) := mul_le_mul_of_nonneg_left hC_le (by norm_num)
              _ = 4 / 729 := by norm_num
        have heq' : (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) = 4 / 729 := by
          rw [hdel] at heq; linarith
        linarith
      have hC_eq : C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 = 1 / 27 := by
        rw [hdel] at heq
        have hfac : (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) = 4 / 729 := by linarith
        rw [hB_eq] at hfac
        linarith
      have hB0_sq : B₀ ^ 2 = 1 / 3 := by
        have hB1_sq : B₁ ^ 2 = 1 - B₀ ^ 2 := by linarith
        rw [show B₀ ^ 2 * B₁ ^ 4 = B₀ ^ 2 * (1 - B₀ ^ 2) ^ 2 by rw [← hB1_sq]; ring] at hB_eq
        exact (unit_prod_sq_eq_iff (sq_nonneg B₀) (by nlinarith [sq_nonneg B₁])).mp hB_eq
      have hB1_sq : B₁ ^ 2 = 2 / 3 := by linarith
      obtain ⟨hC0_sq, hC2_sq, hC3_sq⟩ := (three_nonneg_am_gm_eq_iff (sq_nonneg C₀) (sq_nonneg C₂)
        (sq_nonneg C₃) (by nlinarith [sq_nonneg C₁])).mp hC_eq
      have hC1_eq : C₁ = 0 := sq_eq_zero_iff.mp (by linarith)
      have htr_all := sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0
      have hsp0 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 0 = g.linearEquiv p1 := by
        rw [hg0]; exact sparseFourConfigOct_zero B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0
      have hsp1 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 1 = g.linearEquiv p2 := hg1.symm
      have hsp2 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 2 = g.linearEquiv p3 := hg2.symm
      have ho12 : tracePairing p1 p2 = 1 / 3 := by
        have h := htr_all.1
        simp only [fpOverlap, hsp0, hsp1, g.map_tracePairing] at h
        rw [h, hB0_sq]
      have ho13 : tracePairing p1 p3 = 1 / 3 := by
        have h := htr_all.2.1
        simp only [fpOverlap, hsp0, hsp2, g.map_tracePairing] at h
        rw [h, hC0_sq]
      have ho23 : tracePairing p2 p3 = 1 / 3 := by
        have h := htr_all.2.2.2.1
        simp only [fpOverlap, hsp1, hsp2, g.map_tracePairing] at h
        rw [h, octNormSq_eq_coords]
        simp only [hC1_eq, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
          oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]
        have hval : (B₀ * C₀ + B₁ * 0 + (B₁ * 0)) ^ 2 + (0 + B₁ * C₂) ^ 2 +
            (0 + B₁ * 0) ^ 2 + (0 + B₁ * 0) ^ 2 + (0 + B₁ * 0) ^ 2 +
            (0 + B₁ * 0) ^ 2 + (0 + B₁ * 0) ^ 2 + (0 + B₁ * 0) ^ 2 =
            B₀ ^ 2 * C₀ ^ 2 + B₁ ^ 2 * C₂ ^ 2 := by ring
        calc
          _ = B₀ ^ 2 * C₀ ^ 2 + B₁ ^ 2 * C₂ ^ 2 := by ring
          _ = (1 / 3) * (1 / 3) + (2 / 3) * (1 / 3) := by rw [hB0_sq, hB1_sq, hC0_sq, hC2_sq]
          _ = 1 / 3 := by norm_num
      have hR123 : tracePairing p1 (jordanMul p2 p3) = 1 / 9 := by
        have h := htr_all.2.2.2.2.2.2.1
        simp only [fpTriangle, hsp0, hsp1, hsp2, ← g.preserves_product, g.map_tracePairing] at h
        rw [← NativeAnalysis.tracePairing_associative, h]
        unfold octonionReal
        simp only [hC1_eq, oct_fst_add, oct_fst_smul, oct_fst_scalar, oct_fst_I,
          quat_add_re, quat_smul_re, quat_zero_re]
        calc
          B₀ * C₀ * (B₀ * C₀ + B₁ * (0 + C₂ * 0)) = B₀ ^ 2 * C₀ ^ 2 := by ring
          _ = (1 / 3) * (1 / 3) := by rw [hB0_sq, hC0_sq]
          _ = 1 / 9 := by norm_num
      exact ⟨ho12, ho13, ho23, hR123⟩
    · rintro ⟨ho12, ho13, ho23, hR123⟩
      rcases lemma_A_three ![p1, p2, p3] (fun i => by fin_cases i <;> assumption) with
        ⟨g, hg0, ⟨ξ₀, ξ₁, c, hξ₀, hξ₁, hc_nn, hξ_sum, hξ_prod, hg1⟩,
          hg2_in, ⟨s, hs_nn, hg2_02⟩, _hg2_imI, hg2_d0⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hg0 hg1 hg2_in hg2_02 hg2_d0
      let B₀ := Real.sqrt ξ₀
      let B₁ := Real.sqrt ξ₁
      have hB0_sq : B₀ ^ 2 = ξ₀ := Real.sq_sqrt hξ₀
      have hB1_sq : B₁ ^ 2 = ξ₁ := Real.sq_sqrt hξ₁
      have hg1_val : g.linearEquiv p2 = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] := by
        rw [hg1]
        have hB01 : B₀ * B₁ = c := by
          have hsq : (B₀ * B₁) ^ 2 = c ^ 2 := by
            calc (B₀ * B₁) ^ 2 = B₀ ^ 2 * B₁ ^ 2 := by ring
              _ = c ^ 2 := by rw [hB0_sq, hB1_sq, hξ_prod]
          exact (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc_nn).mp hsq
        apply albert_ext
        · change (ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c)).1 0 =
            (octDyad ![octonionScalar B₀, octonionScalar B₁, 0]).1 0
          simp only [octDyad, octNormSq_scalar, hB0_sq, albert_add_fst, albert_smul_fst,
            diagAtom_fst, slotElem01_fst, Matrix.cons_val_zero]
          norm_num
        · change (ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c)).1 1 =
            (octDyad ![octonionScalar B₀, octonionScalar B₁, 0]).1 1
          simp only [octDyad, albert_add_fst, albert_smul_fst,
            diagAtom_fst, slotElem01_fst, Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [octNormSq_scalar, hB1_sq]
          norm_num
        · change (ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c)).1 2 =
            (octDyad ![octonionScalar B₀, octonionScalar B₁, 0]).1 2
          simp only [octDyad, albert_add_fst, albert_smul_fst,
            diagAtom_fst, slotElem01_fst, Matrix.cons_val_two, Matrix.cons_val_one,
            Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons, octNormSq_zero]
          norm_num
        · apply oct_ext <;>
            simp only [octDyad, albert_add_snd, albert_smul_snd, diagAtom_snd,
              slotElem01_snd_0, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hB01,
              oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK] <;> ring
        · apply oct_ext <;>
            simp only [octDyad, albert_add_snd, albert_smul_snd, diagAtom_snd,
              slotElem01_snd_1, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
              oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK] <;> ring
        · apply oct_ext <;>
            simp only [octDyad, albert_add_snd, albert_smul_snd, diagAtom_snd,
              slotElem01_snd_2, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
              oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
              oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
              oct_fst_scalar, oct_snd_scalar, oct_fst_zero, oct_snd_zero,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
              quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
              quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK] <;> ring
      have hξ₀_eq : ξ₀ = 1 / 3 := by
        rw [← g.map_tracePairing, hg0, hg1, tracePairing_diagAtom] at ho12
        simp only [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem01_fst] at ho12
        norm_num at ho12
        exact ho12
      have hξ₁_eq : ξ₁ = 2 / 3 := by linarith only [hξ_sum, hξ₀_eq]
      have hB0_pos : 0 < B₀ := Real.sqrt_pos.mpr (by linarith only [hξ₀_eq])
      have hB1_pos : 0 < B₁ := Real.sqrt_pos.mpr (by linarith only [hξ₁_eq])
      let q2 := g.linearEquiv p3
      have hq2_atom : IsAtom q2 := g.map_isAtom hp3
      have hq2_d0 : q2.1 0 = 1 / 3 := by
        rw [← g.map_tracePairing, hg0, tracePairing_diagAtom] at ho13
        exact ho13
      have hq2_d0_pos : 0 < q2.1 0 := by linarith only [hq2_d0]
      let C₀ := Real.sqrt (q2.1 0)
      have hC0_sq : C₀ ^ 2 = 1 / 3 := by dsimp [C₀]; rw [hq2_d0]; exact Real.sq_sqrt (by norm_num)
      have hC0_pos : 0 < C₀ := Real.sqrt_pos.mpr hq2_d0_pos
      have hq2_in := (standardComplexWindow_contains_iff q2).mp hg2_in
      obtain ⟨hdyad, hnorm⟩ := isAtom_eq_octDyad hq2_atom hq2_d0_pos
      let C₁ := (1 / C₀) * (q2.2 0).1.re
      let C₂ := -(1 / C₀) * (q2.2 0).1.imI
      let C₃ := (1 / C₀) * s
      have hq2_val : q2 = octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] := by
        nth_rw 1 [hdyad]
        refine congrArg octDyad (vec3_eq rfl ?_ ?_)
        · apply oct_ext <;>
            simp only [C₀, C₁, C₂, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
              oct_fst_conj, oct_snd_conj, oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
              hq2_in.1, hq2_in.2.1, hq2_in.2.2.1,
              quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
              quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
              quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
              quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK] <;>
            ring
        · rw [hg2_02, octonionConj_scalar]
          apply oct_ext <;>
            simp only [C₀, C₃, oct_fst_smul, oct_snd_smul, oct_fst_scalar, oct_snd_scalar,
              quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
              quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK] <;> ring
      have hnorm_sum : C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1 := by
        have h1 : octNormSq (octonionScalar C₀) = C₀ ^ 2 := octNormSq_scalar C₀
        have h2 : octNormSq (octonionScalar C₁ + C₂ • octI) = C₁ ^ 2 + C₂ ^ 2 := by
          rw [octNormSq_eq_coords]
          simp only [oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
            oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
            quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
            quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
            quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]
          ring
        have h3 : octNormSq (octonionScalar C₃) = C₃ ^ 2 := octNormSq_scalar C₃
        have hsum_dyad : octNormSq (octonionScalar C₀) + octNormSq (octonionScalar C₁ + C₂ • octI) +
            octNormSq (octonionScalar C₃) = 1 := by
          have htr := hq2_atom.2
          rw [albertTrace, Fin.sum_univ_three, hq2_val] at htr
          simpa [octDyad] using htr
        linarith only [h1, h2, h3, hsum_dyad]
      have htr_all := sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0
      have hsp0 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 0 = g.linearEquiv p1 := by
        rw [hg0]
        exact sparseFourConfigOct_zero B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0
      have hsp1 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 1 = g.linearEquiv p2 := hg1_val.symm
      have hsp2 : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ 1 0 0 2 = g.linearEquiv p3 := hq2_val.symm
      have hR_eq : B₀ * C₀ * (B₀ * C₀ + B₁ * C₁) = 1 / 9 := by
        have h := htr_all.2.2.2.2.2.2.1
        simp only [fpTriangle, hsp0, hsp1, hsp2, ← g.preserves_product, g.map_tracePairing] at h
        rw [NativeAnalysis.tracePairing_associative, hR123] at h
        unfold octonionReal at h
        simp only [oct_fst_add, oct_fst_smul, oct_fst_scalar, oct_fst_I,
          quat_add_re, quat_smul_re, quat_zero_re] at h
        ring_nf at h
        linarith only [h]
      have hC1_eq : C₁ = 0 := by
        have hB0_sq' : B₀ ^ 2 = 1 / 3 := by linarith only [hξ₀_eq, hB0_sq]
        have hBC_sq : (B₀ * C₀) ^ 2 = (1 / 3) ^ 2 := by
          calc (B₀ * C₀) ^ 2 = B₀ ^ 2 * C₀ ^ 2 := by ring
            _ = (1 / 3) ^ 2 := by rw [hB0_sq', hC0_sq]; ring
        have hBC : B₀ * C₀ = 1 / 3 :=
          (sq_eq_sq₀ (mul_pos hB0_pos hC0_pos).le (by norm_num)).mp hBC_sq
        rw [hBC] at hR_eq
        have hB1C1 : B₁ * C₁ = 0 := by linarith only [hR_eq]
        exact (mul_eq_zero.mp hB1C1).resolve_left hB1_pos.ne'
      have ho23_eq : (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 = 1 / 3 := by
        have h := htr_all.2.2.2.1
        simp only [fpOverlap, hsp1, hsp2, g.map_tracePairing] at h
        rw [ho23, octNormSq_eq_coords] at h
        simp only [oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
          oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
          quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
          quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK] at h
        ring_nf at h ⊢
        linarith only [h]
      have hC2_sq : C₂ ^ 2 = 1 / 3 := by
        have hB0_sq' : B₀ ^ 2 = 1 / 3 := by linarith only [hξ₀_eq, hB0_sq]
        have hB1_sq' : B₁ ^ 2 = 2 / 3 := by linarith only [hξ₁_eq, hB1_sq]
        rw [hC1_eq, mul_zero, add_zero] at ho23_eq
        have hB1C2 : B₁ ^ 2 * C₂ ^ 2 = 2 / 9 := by
          calc B₁ ^ 2 * C₂ ^ 2 = (B₁ * C₂) ^ 2 := by ring
            _ = 1 / 3 - (B₀ * C₀) ^ 2 := by linarith only [ho23_eq]
            _ = 1 / 3 - B₀ ^ 2 * C₀ ^ 2 := by ring
            _ = 2 / 9 := by rw [hB0_sq', hC0_sq]; norm_num
        rw [hB1_sq'] at hB1C2
        linarith only [hB1C2]
      have hC3_sq : C₃ ^ 2 = 1 / 3 := by
        rw [hC1_eq] at hnorm_sum
        ring_nf at hnorm_sum
        linarith only [hnorm_sum, hC0_sq, hC2_sq]
      have hq2_val' : g.linearEquiv p3 =
          octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] := hq2_val
      rw [← tripleDelta_automorphism g p1 p2 p3, hg0, hg1_val, hq2_val',
        tripleDelta_normal_form B₀ B₁ C₀ C₁ C₂ C₃,
        show B₀ ^ 2 = 1 / 3 by linarith only [hξ₀_eq, hB0_sq],
        show B₁ ^ 4 = (B₁ ^ 2) ^ 2 by ring,
        show B₁ ^ 2 = 2 / 3 by linarith only [hξ₁_eq, hB1_sq],
        hC0_sq, hC2_sq, hC3_sq]
      norm_num
  exact ⟨hbound, fun W => hbound, hiff⟩

/-- Explicit maximizer quadruple of `prop:max` (`v_A = (1, 0, 0)`, `v_B = (1, √2, 0)/√3`,
`v_C = (1, i, 1)/√3`, `v_D = (1, j, ℓ)/√3`). -/
def maximizerConfig : Fin 4 → Albert :=
  sparseFourConfig (1 / Real.sqrt 3) (Real.sqrt 2 / Real.sqrt 3)
    (1 / Real.sqrt 3) 0 (1 / Real.sqrt 3) (1 / Real.sqrt 3)
    (1 / Real.sqrt 3) 0 0 (1 / Real.sqrt 3) ((1 / Real.sqrt 3) • octL)

theorem maximizerConfig_isAtom (i : Fin 4) : IsAtom (maximizerConfig i) := by
  have hsp : maximizerConfig =
      sparseFourConfigOct (1 / Real.sqrt 3) (Real.sqrt 2 / Real.sqrt 3)
        (1 / Real.sqrt 3) 0 (1 / Real.sqrt 3) (1 / Real.sqrt 3) (1 / Real.sqrt 3)
        ((1 / Real.sqrt 3) • octJ) ((1 / Real.sqrt 3) • octL) := by
    simp [maximizerConfig, sparseFourConfig, octonionScalar_zero]
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnorm1 : (1 / Real.sqrt 3) ^ 2 + octNormSq (octonionScalar (Real.sqrt 2 / Real.sqrt 3)) +
      octNormSq 0 = 1 := by
    rw [octNormSq_scalar, octNormSq_zero, div_pow, div_pow, hs3, hs2]; norm_num
  have hnorm2 : (1 / Real.sqrt 3) ^ 2 +
      octNormSq (octonionScalar 0 + (1 / Real.sqrt 3) • octI) +
      octNormSq (octonionScalar (1 / Real.sqrt 3)) = 1 := by
    rw [octNormSq_scalar, octNormSq_eq_coords]
    simp only [oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]
    ring_nf
    rw [inv_pow, hs3]
    norm_num
  have hnorm3 : (1 / Real.sqrt 3) ^ 2 +
      octNormSq ((1 / Real.sqrt 3) • octJ) +
      octNormSq ((1 / Real.sqrt 3) • octL) = 1 := by
    rw [octNormSq_eq_coords, octNormSq_eq_coords]
    simp only [oct_fst_smul, oct_snd_smul, oct_fst_J, oct_snd_J, oct_fst_L, oct_snd_L,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]
    ring_nf
    rw [inv_pow, hs3]
    norm_num
  rcases (by
    rcases i with ⟨n, hn⟩
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl)) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [hsp, sparseFourConfigOct_zero]
    exact diagAtom_isAtom 0
  · have h1 : maximizerConfig 1 =
        octDyad ![octonionScalar (1 / Real.sqrt 3), octonionScalar (Real.sqrt 2 / Real.sqrt 3), 0] := by
      rw [hsp]; rfl
    rw [h1]
    exact octDyad_real0_isAtom _ _ _ hnorm1
  · have h2 : maximizerConfig 2 =
        octDyad ![octonionScalar (1 / Real.sqrt 3), octonionScalar 0 + (1 / Real.sqrt 3) • octI,
          octonionScalar (1 / Real.sqrt 3)] := by
      rw [hsp]; rfl
    rw [h2]
    exact octDyad_real0_isAtom _ _ _ hnorm2
  · have h3 : maximizerConfig 3 =
        octDyad ![octonionScalar (1 / Real.sqrt 3), (1 / Real.sqrt 3) • octJ,
          (1 / Real.sqrt 3) • octL] := by
      rw [hsp]; rfl
    rw [h3]
    exact octDyad_real0_isAtom _ _ _ hnorm3

theorem fourPointInvariant_maximizerConfig :
    fourPointInvariant maximizerConfig = 4 / 19683 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hmax : maximizerConfig =
      sparseFourConfig (1 / Real.sqrt 3) (Real.sqrt 2 / Real.sqrt 3)
        (1 / Real.sqrt 3) 0 (1 / Real.sqrt 3) (1 / Real.sqrt 3)
        (1 / Real.sqrt 3) 0 0 (1 / Real.sqrt 3)
        (octonionScalar 0 + (0 : ℝ) • octI + (0 : ℝ) • octJ + (0 : ℝ) • octK + (1 / Real.sqrt 3) • octL) := by
    simp [maximizerConfig, octonionScalar_zero]
  rw [hmax, sparseFourConfig_fourPointInvariant]
  have h1 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [div_pow, one_pow, hs3]
  have h2 : (Real.sqrt 2 / Real.sqrt 3) ^ 4 = 4 / 9 := by
    rw [div_pow, show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring,
      show Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 by ring, hs2, hs3]
    norm_num
  rw [h1, h2]
  norm_num

/-- All 13 trace invariants and `fpTetraDtet` at `maximizerConfig` (`prop:max`). -/
theorem maximizerConfig_traces (σ : Equiv.Perm (Fin 4)) :
    (∀ i j : Fin 4, i ≠ j → fpOverlap maximizerConfig i j = 1 / 3) ∧
    (∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → fpTriangle maximizerConfig i j k = 1 / 9) ∧
    fpDoublePair1 maximizerConfig = 1 / 27 ∧
    fpDoublePair2 maximizerConfig = 1 / 27 ∧
    fpDoublePair3 maximizerConfig = 1 / 27 ∧
    fpOmega1 maximizerConfig = 1 / 27 ∧
    fpOmega2 maximizerConfig = 1 / 27 ∧
    fpOmega3 maximizerConfig = 1 / 27 ∧
    fpTetraDtet σ (fpOverlap maximizerConfig) (fpTriangle maximizerConfig)
      ![fpDoublePair1 maximizerConfig, fpDoublePair2 maximizerConfig, fpDoublePair3 maximizerConfig] =
      4 / 27 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3_inv2 : (Real.sqrt 3)⁻¹ ^ 2 = 1 / 3 := by rw [inv_pow, hs3]; norm_num
  have hs3_inv4 : (Real.sqrt 3)⁻¹ ^ 4 = 1 / 9 := by
    rw [show (Real.sqrt 3)⁻¹ ^ 4 = ((Real.sqrt 3)⁻¹ ^ 2) ^ 2 by ring, hs3_inv2]; norm_num
  have hs3_inv6 : (Real.sqrt 3)⁻¹ ^ 6 = 1 / 27 := by
    rw [show (Real.sqrt 3)⁻¹ ^ 6 = ((Real.sqrt 3)⁻¹ ^ 2) ^ 3 by ring, hs3_inv2]; norm_num
  have hsp : maximizerConfig =
      sparseFourConfigOct (1 / Real.sqrt 3) (Real.sqrt 2 / Real.sqrt 3)
        (1 / Real.sqrt 3) 0 (1 / Real.sqrt 3) (1 / Real.sqrt 3) (1 / Real.sqrt 3)
        ((1 / Real.sqrt 3) • octJ) ((1 / Real.sqrt 3) • octL) := by
    simp [maximizerConfig, sparseFourConfig, octonionScalar_zero]
  have htr := sparseFourConfigOct_traces (1 / Real.sqrt 3) (Real.sqrt 2 / Real.sqrt 3)
    (1 / Real.sqrt 3) 0 (1 / Real.sqrt 3) (1 / Real.sqrt 3) (1 / Real.sqrt 3)
    ((1 / Real.sqrt 3) • octJ) ((1 / Real.sqrt 3) • octL)
  rw [← hsp] at htr
  have h1s3 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [div_pow, one_pow, hs3]
  have h2s3 : (Real.sqrt 2 / Real.sqrt 3) ^ 2 = 2 / 3 := by rw [div_pow, hs2, hs3]
  have ho01 : fpOverlap maximizerConfig 0 1 = 1 / 3 := by rw [htr.1, h1s3]
  have ho02 : fpOverlap maximizerConfig 0 2 = 1 / 3 := by rw [htr.2.1, h1s3]
  have ho03 : fpOverlap maximizerConfig 0 3 = 1 / 3 := by rw [htr.2.2.1, h1s3]
  have ho12 : fpOverlap maximizerConfig 1 2 = 1 / 3 := by
    rw [htr.2.2.2.1, octNormSq_eq_coords]
    simp only [one_div, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3]; norm_num
  have ho13 : fpOverlap maximizerConfig 1 3 = 1 / 3 := by
    rw [htr.2.2.2.2.1, octNormSq_eq_coords]
    simp only [one_div, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_scalar, oct_snd_scalar, oct_fst_J, oct_snd_J,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3]; norm_num
  have ho23 : fpOverlap maximizerConfig 2 3 = 1 / 3 := by
    rw [htr.2.2.2.2.2.1, octNormSq_eq_coords]
    simp only [one_div, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
      oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      oct_fst_J, oct_snd_J, oct_fst_L, oct_snd_L,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
      quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
      quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3]; norm_num
  have hcases : ∀ x : Fin 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := fun x => by
    rcases x with ⟨n, hn⟩
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have ho_all : ∀ i j : Fin 4, i ≠ j → fpOverlap maximizerConfig i j = 1 / 3 := by
    have hcomm : ∀ i j, fpOverlap maximizerConfig i j = fpOverlap maximizerConfig j i :=
      fun i j => tracePairing_comm _ _
    intro i j hij
    rcases hcases i with rfl | rfl | rfl | rfl <;> rcases hcases j with rfl | rfl | rfl | rfl
    · exact absurd rfl hij
    · exact ho01
    · exact ho02
    · exact ho03
    · rw [hcomm]; exact ho01
    · exact absurd rfl hij
    · exact ho12
    · exact ho13
    · rw [hcomm]; exact ho02
    · rw [hcomm]; exact ho12
    · exact absurd rfl hij
    · exact ho23
    · rw [hcomm]; exact ho03
    · rw [hcomm]; exact ho13
    · rw [hcomm]; exact ho23
    · exact absurd rfl hij
  have hR012 : fpTriangle maximizerConfig 0 1 2 = 1 / 9 := by
    rw [htr.2.2.2.2.2.2.1]
    unfold octonionReal
    simp only [one_div, oct_fst_add, oct_fst_smul, oct_fst_scalar, oct_fst_I,
      quat_add_re, quat_smul_re, quat_zero_re]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3] <;> norm_num
  have hR013 : fpTriangle maximizerConfig 0 1 3 = 1 / 9 := by
    rw [htr.2.2.2.2.2.2.2.1]
    unfold octonionReal
    simp only [one_div, oct_fst_add, oct_fst_smul, oct_fst_scalar, oct_fst_J,
      quat_add_re, quat_smul_re, quat_zero_re]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3] <;> norm_num
  have hR023 : fpTriangle maximizerConfig 0 2 3 = 1 / 9 := by
    rw [htr.2.2.2.2.2.2.2.2.1]
    unfold octonionReal
    simp only [one_div, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
      oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      oct_fst_J, oct_snd_J, oct_fst_L, oct_snd_L,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
      quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
      quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3] <;> norm_num
  have hR123 : fpTriangle maximizerConfig 1 2 3 = 1 / 9 := by
    rw [htr.2.2.2.2.2.2.2.2.2.1]
    unfold octonionReal
    simp only [one_div, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
      oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      oct_fst_J, oct_snd_J, oct_fst_L, oct_snd_L,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
      quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
      quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3] <;> norm_num
  have hR_all : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → fpTriangle maximizerConfig i j k = 1 / 9 := by
    have hsym12 : ∀ a b c, fpTriangle maximizerConfig a b c = fpTriangle maximizerConfig b a c :=
      fun a b c => by unfold fpTriangle; rw [jordanMul_comm]
    have hsym23 : ∀ a b c, fpTriangle maximizerConfig a b c = fpTriangle maximizerConfig a c b :=
      fun a b c => by
        unfold fpTriangle
        rw [NativeAnalysis.tracePairing_associative, jordanMul_comm (maximizerConfig b),
          ← NativeAnalysis.tracePairing_associative]
    have hR_ord : ∀ a b c : Fin 4, a < b → b < c → fpTriangle maximizerConfig a b c = 1 / 9 := by
      intro a b c hab hbc
      have hb : b.1 = 1 ∨ b.1 = 2 := by have := c.isLt; simp only [Fin.lt_def] at hab hbc; omega
      have hc : c.1 = 2 ∨ c.1 = 3 := by have := c.isLt; simp only [Fin.lt_def] at hab hbc; omega
      rcases (by simp only [Fin.lt_def] at hab hbc; have := c.isLt; omega : a.1 = 0 ∨ a.1 = 1) with ha0 | ha1
      · have ha' : a = 0 := Fin.ext ha0; subst ha'
        rcases hb with hb1 | hb2
        · have hb' : b = 1 := Fin.ext hb1; subst hb'
          rcases hc with hc2 | hc3
          · have hc' : c = 2 := Fin.ext hc2; subst hc'; exact hR012
          · have hc' : c = 3 := Fin.ext hc3; subst hc'; exact hR013
        · have hb' : b = 2 := Fin.ext hb2; subst hb'
          have hc3 : c.1 = 3 := by simp only [Fin.lt_def] at hbc; have := c.isLt; omega
          have hc' : c = 3 := Fin.ext hc3; subst hc'; exact hR023
      · have ha' : a = 1 := Fin.ext ha1; subst ha'
        have hb2 : b.1 = 2 := by simp only [Fin.lt_def] at hab hbc; have := c.isLt; omega
        have hc3 : c.1 = 3 := by simp only [Fin.lt_def] at hab hbc; have := c.isLt; omega
        have hb' : b = 2 := Fin.ext hb2; subst hb'
        have hc' : c = 3 := Fin.ext hc3; subst hc'; exact hR123
    have hstep1 : ∀ a b c : Fin 4, a ≠ b → a < c → b < c →
        fpTriangle maximizerConfig a b c = 1 / 9 := fun a b c hab hac hbc => by
      rcases lt_or_gt_of_ne hab with h | h
      · exact hR_ord a b c h hbc
      · rw [hsym12]; exact hR_ord b a c h hac
    intro i j k hij hik hjk
    rcases lt_or_gt_of_ne hik with hik1 | hik2 <;> rcases lt_or_gt_of_ne hjk with hjk1 | hjk2
    · exact hstep1 i j k hij hik1 hjk1
    · rw [hsym23]; exact hR_ord i k j hik1 hjk2
    · rw [hsym12, hsym23]; exact hR_ord j k i hjk1 hik2
    · rw [hsym23, hsym12]
      rcases lt_or_gt_of_ne hij with hij1 | hij2
      · exact hR_ord k i j hik2 hij1
      · rw [hsym23]; exact hR_ord k j i hjk2 hij2
  have hω1 : fpOmega1 maximizerConfig = 1 / 27 := by
    rw [htr.2.2.2.2.2.2.2.2.2.2.1]
    unfold octonionReal
    simp only [one_div, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
      oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      oct_fst_J, oct_snd_J,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
      quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
      quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3] <;> norm_num
  have hω2 : fpOmega2 maximizerConfig = 1 / 27 := by
    rw [htr.2.2.2.2.2.2.2.2.2.2.2.1]
    unfold octonionReal
    simp only [one_div, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
      oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      oct_fst_J, oct_snd_J, oct_fst_L, oct_snd_L,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
      quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
      quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3] <;> norm_num
  have hω3 : fpOmega3 maximizerConfig = 1 / 27 := by
    rw [htr.2.2.2.2.2.2.2.2.2.2.2.2]
    unfold octonionReal
    simp only [one_div, oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
      oct_fst_neg, oct_snd_neg, oct_fst_zero, oct_snd_zero,
      oct_fst_mul, oct_snd_mul, oct_fst_conj, oct_snd_conj,
      oct_fst_scalar, oct_snd_scalar, oct_fst_I, oct_snd_I,
      oct_fst_J, oct_snd_J, oct_fst_L, oct_snd_L,
      quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
      quat_sub_re, quat_sub_imI, quat_sub_imJ, quat_sub_imK,
      quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK,
      quat_neg_re, quat_neg_imI, quat_neg_imJ, quat_neg_imK,
      quat_zero_re, quat_zero_imI, quat_zero_imJ, quat_zero_imK,
      quat_star_re, quat_star_imI, quat_star_imJ, quat_star_imK,
      quat_mul_re, quat_mul_imI, quat_mul_imJ, quat_mul_imK]
    ring_nf; simp only [hs3_inv2, hs3_inv4, hs3_inv6, hs2, hs3] <;> norm_num
  have ht1 : fpDoublePair1 maximizerConfig = 1 / 27 := by
    have h1 : fpOmega2 maximizerConfig =
        fpDoublePair1 maximizerConfig + fpDoublePair3 maximizerConfig - fpDoublePair2 maximizerConfig := rfl
    have h2 : fpOmega3 maximizerConfig =
        fpDoublePair1 maximizerConfig + fpDoublePair2 maximizerConfig - fpDoublePair3 maximizerConfig := rfl
    linarith [hω2, hω3]
  have ht2 : fpDoublePair2 maximizerConfig = 1 / 27 := by
    have h1 : fpOmega1 maximizerConfig =
        fpDoublePair2 maximizerConfig + fpDoublePair3 maximizerConfig - fpDoublePair1 maximizerConfig := rfl
    have h2 : fpOmega3 maximizerConfig =
        fpDoublePair1 maximizerConfig + fpDoublePair2 maximizerConfig - fpDoublePair3 maximizerConfig := rfl
    linarith [hω1, hω3]
  have ht3 : fpDoublePair3 maximizerConfig = 1 / 27 := by
    have h1 : fpOmega1 maximizerConfig =
        fpDoublePair2 maximizerConfig + fpDoublePair3 maximizerConfig - fpDoublePair1 maximizerConfig := rfl
    have h2 : fpOmega2 maximizerConfig =
        fpDoublePair1 maximizerConfig + fpDoublePair3 maximizerConfig - fpDoublePair2 maximizerConfig := rfl
    linarith [hω1, hω2]
  have hdtet : fpTetraDtet σ (fpOverlap maximizerConfig) (fpTriangle maximizerConfig)
      ![fpDoublePair1 maximizerConfig, fpDoublePair2 maximizerConfig, fpDoublePair3 maximizerConfig] =
      4 / 27 := by
    have hpos : ∀ i j : Fin 4, i ≠ j → 0 < fpOverlap maximizerConfig i j := fun i j hij => by
      rw [ho_all i j hij]; norm_num
    have h := fpTetraDtet_atoms σ maximizerConfig hpos
    rw [ho01, ho02, ho03, ho12, ho13, ho23, fourPointInvariant_maximizerConfig] at h
    linarith
  exact ⟨ho_all, hR_all, ht1, ht2, ht3, hω1, hω2, hω3, hdtet⟩

/-- `prop:max`: `0 ≤ 𝒜(p) ≤ 4 / 19683`, with equality iff `p` is in the single `Aut(𝔍)`-orbit
of `maximizerConfig`; strictly exceeds `fourPointInvariant fixedS = 1 / 5832`. -/
theorem prop_max :
    (∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) →
      0 ≤ fourPointInvariant p ∧ fourPointInvariant p ≤ 4 / 19683) ∧
    (∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) →
      (fourPointInvariant p = 4 / 19683 ↔
        ∃ g : NativeAlbertAutomorphism, ∀ i : Fin 4, g.linearEquiv (p i) = maximizerConfig i)) ∧
    (fourPointInvariant fixedS = 1 / 5832 ∧ fourPointInvariant fixedS < 4 / 19683) := by
  have hbound : ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) →
      0 ≤ fourPointInvariant p ∧ fourPointInvariant p ≤ 4 / 19683 := by
    intro p hp
    refine ⟨(thm_fourpoint p hp).1, ?_⟩
    by_cases hnd : ∀ i j : Fin 4, i ≠ j → p i ≠ p j ∧ jordanMul (p i) (p j) ≠ 0
    · obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
        _hB0, _hB1, _hC0, _hC2, _hC3, _hD0, _hx2, _hy4, hBs, hCs, hDs, hcfg⟩ :=
        lemma_A_normal_nondegenerate p hp hnd
      have hfp := fourPointInvariant_automorphism_invariant g p
      have hcfg' := hcfg
      rw [octOne_eq_scalar, ← octonionScalar_eq_smul y₀] at hcfg'
      rw [hcfg', sparseFourConfig_fourPointInvariant] at hfp
      rw [← hfp]
      have h1 : B₀ ^ 2 * B₁ ^ 4 ≤ 4 / 27 := by
        have hB1_sq : B₁ ^ 2 = 1 - B₀ ^ 2 := by linarith only [hBs]
        rw [show B₀ ^ 2 * B₁ ^ 4 = B₀ ^ 2 * (1 - B₀ ^ 2) ^ 2 by rw [← hB1_sq]; ring]
        exact unit_prod_sq_bound (sq_nonneg B₀) (by linarith only [hBs, sq_nonneg B₁])
      have h2 : C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 ≤ 1 / 27 :=
        three_nonneg_am_gm (sq_nonneg C₀) (sq_nonneg C₂) (sq_nonneg C₃)
          (by linarith only [hCs, sq_nonneg C₁])
      have h3 : D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 ≤ 1 / 27 :=
        three_nonneg_am_gm (sq_nonneg D₀) (sq_nonneg x₂) (sq_nonneg y₄)
          (by linarith only [hDs, sq_nonneg x₀, sq_nonneg x₁,
            sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])
      have hp12 : 0 ≤ (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) := by positivity
      have hp3 : 0 ≤ D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 := by positivity
      have hprod12 : (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) ≤ (4 / 27) * (1 / 27) :=
        mul_le_mul h1 h2 (by positivity) (by norm_num)
      calc
        B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2
          = ((B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2)) * (D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2) := by ring
        _ ≤ ((4 / 27) * (1 / 27)) * (1 / 27) := mul_le_mul hprod12 h3 hp3 (by norm_num)
        _ = 4 / 19683 := by norm_num
    · push Not at hnd
      rcases hnd with ⟨i, j, hij, hdeg_pair⟩
      have hdeg_pair' : p i = p j ∨ jordanMul (p i) (p j) = 0 := by
        by_cases he : p i = p j
        · exact Or.inl he
        · exact Or.inr (hdeg_pair he)
      obtain ⟨Q, hQ⟩ := lemma_A_degenerate p hp ⟨i, j, hij, hdeg_pair'⟩
      have hz := lemma_A_zero_of_quat Q p hp hQ
      rw [hz]; norm_num
  have horbit : ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) →
      (fourPointInvariant p = 4 / 19683 ↔
        ∃ g : NativeAlbertAutomorphism, ∀ i : Fin 4, g.linearEquiv (p i) = maximizerConfig i) := by
    intro p hp
    constructor
    · intro heq
      have hnd : ∀ i j : Fin 4, i ≠ j → p i ≠ p j ∧ jordanMul (p i) (p j) ≠ 0 := by
        intro i j hij
        by_contra hbad
        have hbad' : p i = p j ∨ jordanMul (p i) (p j) = 0 := by
          by_cases he : p i = p j
          · exact Or.inl he
          · exact Or.inr (by by_contra hnz; exact hbad ⟨he, hnz⟩)
        obtain ⟨Q, hQ⟩ := lemma_A_degenerate p hp ⟨i, j, hij, hbad'⟩
        have hz := lemma_A_zero_of_quat Q p hp hQ
        linarith
      obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
        hB0, hB1, hC0, hC2, hC3, hD0, hx2, hy4, hBs, hCs, hDs, hcfg⟩ :=
        lemma_A_normal_nondegenerate p hp hnd
      have hfp := fourPointInvariant_automorphism_invariant g p
      have hcfg' := hcfg
      rw [octOne_eq_scalar, ← octonionScalar_eq_smul y₀] at hcfg'
      rw [hcfg', sparseFourConfig_fourPointInvariant] at hfp
      have hprod : (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) * (D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2) =
          4 / 19683 := by
        calc
          (B₀ ^ 2 * B₁ ^ 4) * (C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2) * (D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2)
            = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 := by ring
          _ = fourPointInvariant p := hfp
          _ = 4 / 19683 := heq
      have h1 : B₀ ^ 2 * B₁ ^ 4 ≤ 4 / 27 := by
        have hB1_sq : B₁ ^ 2 = 1 - B₀ ^ 2 := by linarith only [hBs]
        rw [show B₀ ^ 2 * B₁ ^ 4 = B₀ ^ 2 * (1 - B₀ ^ 2) ^ 2 by rw [← hB1_sq]; ring]
        exact unit_prod_sq_bound (sq_nonneg B₀) (by linarith only [hBs, sq_nonneg B₁])
      have h2 : C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 ≤ 1 / 27 :=
        three_nonneg_am_gm (sq_nonneg C₀) (sq_nonneg C₂) (sq_nonneg C₃)
          (by linarith only [hCs, sq_nonneg C₁])
      have h3 : D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 ≤ 1 / 27 :=
        three_nonneg_am_gm (sq_nonneg D₀) (sq_nonneg x₂) (sq_nonneg y₄)
          (by linarith only [hDs, sq_nonneg x₀, sq_nonneg x₁,
            sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])
      let A := B₀ ^ 2 * B₁ ^ 4
      let B := C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2
      let C := D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2
      have hA_nn : 0 ≤ A := by dsimp [A]; positivity
      have hB_nn : 0 ≤ B := by dsimp [B]; positivity
      have hC_nn : 0 ≤ C := by dsimp [C]; positivity
      have hBC_nn : 0 ≤ B * C := mul_nonneg hB_nn hC_nn
      have hBC_le : B * C ≤ 1 / 729 := by
        calc B * C ≤ (1 / 27) * (1 / 27) := mul_le_mul h2 h3 hC_nn (by norm_num)
          _ = 1 / 729 := by norm_num
      have h1_eq : A = 4 / 27 := by
        by_contra hne
        have hlt : A < 4 / 27 := lt_of_le_of_ne h1 hne
        have hlt_prod : A * (B * C) < (4 / 27) * (1 / 729) := by
          by_cases hBC0 : B * C = 0
          · rw [hBC0, mul_zero]; norm_num
          · have hBC_pos : 0 < B * C := lt_of_le_of_ne hBC_nn (Ne.symm hBC0)
            calc A * (B * C) < (4 / 27) * (B * C) := mul_lt_mul_of_pos_right hlt hBC_pos
              _ ≤ (4 / 27) * (1 / 729) := mul_le_mul_of_nonneg_left hBC_le (by norm_num)
        have h_eq : A * (B * C) = 4 / 19683 := by dsimp [A, B, C]; rw [← mul_assoc]; exact hprod
        linarith only [hlt_prod, h_eq]
      have h2_eq : B = 1 / 27 := by
        by_contra hne
        have hlt : B < 1 / 27 := lt_of_le_of_ne h2 hne
        have hlt_prod : A * (B * C) < (4 / 27) * (1 / 729) := by
          rw [h1_eq]
          have hC_pos : 0 < C := by
            by_contra hle
            have hC0 : C = 0 := le_antisymm (not_lt.mp hle) hC_nn
            have hz_p : A * (B * C) = 0 := by rw [hC0, mul_zero, mul_zero]
            have h_eq : A * (B * C) = 4 / 19683 := by dsimp [A, B, C]; rw [← mul_assoc]; exact hprod
            linarith only [hz_p, h_eq]
          calc (4 / 27) * (B * C) < (4 / 27) * ((1 / 27) * C) :=
                mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hlt hC_pos) (by norm_num)
            _ ≤ (4 / 27) * ((1 / 27) * (1 / 27)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by norm_num)) (by norm_num)
            _ = (4 / 27) * (1 / 729) := by norm_num
        have h_eq : A * (B * C) = 4 / 19683 := by dsimp [A, B, C]; rw [← mul_assoc]; exact hprod
        linarith only [hlt_prod, h_eq]
      have h3_eq : C = 1 / 27 := by
        have h1_eq' : B₀ ^ 2 * B₁ ^ 4 = 4 / 27 := h1_eq
        have h2_eq' : C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 = 1 / 27 := h2_eq
        rw [h1_eq', h2_eq'] at hprod
        dsimp [C]
        linarith only [hprod]
      have hB0_sq : B₀ ^ 2 = 1 / 3 := by
        have hB1_sq : B₁ ^ 2 = 1 - B₀ ^ 2 := by linarith only [hBs]
        have hA_eq : B₀ ^ 2 * (1 - B₀ ^ 2) ^ 2 = 4 / 27 := by
          rw [← hB1_sq]
          calc B₀ ^ 2 * (B₁ ^ 2) ^ 2 = B₀ ^ 2 * B₁ ^ 4 := by ring
            _ = A := rfl
            _ = 4 / 27 := h1_eq
        exact (unit_prod_sq_eq_iff (sq_nonneg B₀) (by linarith only [hBs, sq_nonneg B₁])).mp hA_eq
      have hB1_sq : B₁ ^ 2 = 2 / 3 := by linarith only [hBs, hB0_sq]
      obtain ⟨hC0_sq, hC2_sq, hC3_sq⟩ := (three_nonneg_am_gm_eq_iff (sq_nonneg C₀) (sq_nonneg C₂)
        (sq_nonneg C₃) (by linarith only [hCs, sq_nonneg C₁])).mp h2_eq
      obtain ⟨hD0_sq, hx2_sq, hy4_sq⟩ := (three_nonneg_am_gm_eq_iff (sq_nonneg D₀) (sq_nonneg x₂)
        (sq_nonneg y₄)
        (by linarith only [hDs, sq_nonneg x₀, sq_nonneg x₁,
          sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])).mp h3_eq
      have hC1 : C₁ = 0 := sq_eq_zero_iff.mp (by linarith only [hCs, hC0_sq, hC2_sq, hC3_sq])
      have hx0 : x₀ = 0 := sq_eq_zero_iff.mp (by
        linarith only [hDs, hD0_sq, hx2_sq, hy4_sq, sq_nonneg x₀, sq_nonneg x₁,
          sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])
      have hx1 : x₁ = 0 := sq_eq_zero_iff.mp (by
        linarith only [hDs, hD0_sq, hx2_sq, hy4_sq, sq_nonneg x₀, sq_nonneg x₁,
          sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])
      have hy0 : y₀ = 0 := sq_eq_zero_iff.mp (by
        linarith only [hDs, hD0_sq, hx2_sq, hy4_sq, sq_nonneg x₀, sq_nonneg x₁,
          sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])
      have hy1 : y₁ = 0 := sq_eq_zero_iff.mp (by
        linarith only [hDs, hD0_sq, hx2_sq, hy4_sq, sq_nonneg x₀, sq_nonneg x₁,
          sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])
      have hy2 : y₂ = 0 := sq_eq_zero_iff.mp (by
        linarith only [hDs, hD0_sq, hx2_sq, hy4_sq, sq_nonneg x₀, sq_nonneg x₁,
          sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])
      have hy3 : y₃ = 0 := sq_eq_zero_iff.mp (by
        linarith only [hDs, hD0_sq, hx2_sq, hy4_sq, sq_nonneg x₀, sq_nonneg x₁,
          sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂, sq_nonneg y₃])
      have hsq_eq_one_third : ∀ t : ℝ, 0 ≤ t → t ^ 2 = 1 / 3 → t = 1 / Real.sqrt 3 := fun t ht hsq => by
        have hpos3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
        have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have h13 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [div_pow, one_pow, hs3]
        exact (sq_eq_sq₀ ht (by positivity)).mp (by rw [hsq, h13])
      have hB0_eq := hsq_eq_one_third B₀ hB0.le hB0_sq
      have hB1_eq : B₁ = Real.sqrt 2 / Real.sqrt 3 := by
        have hpos3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
        have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have h23 : (Real.sqrt 2 / Real.sqrt 3) ^ 2 = 2 / 3 := by rw [div_pow, hs2, hs3]
        exact (sq_eq_sq₀ hB1.le (by positivity)).mp (by rw [hB1_sq, h23])
      have hC0_eq := hsq_eq_one_third C₀ hC0.le hC0_sq
      have hC2_eq := hsq_eq_one_third C₂ hC2 hC2_sq
      have hC3_eq := hsq_eq_one_third C₃ hC3 hC3_sq
      have hD0_eq := hsq_eq_one_third D₀ hD0.le hD0_sq
      have hx2_eq := hsq_eq_one_third x₂ hx2 hx2_sq
      have hy4_eq := hsq_eq_one_third y₄ hy4 hy4_sq
      refine ⟨g, fun i => ?_⟩
      rw [congrFun hcfg i, hB0_eq, hB1_eq, hC0_eq, hC1, hC2_eq, hC3_eq, hD0_eq, hx0, hx1, hx2_eq,
        hy0, hy1, hy2, hy3, hy4_eq]
      simp only [maximizerConfig, zero_smul, zero_add]
    · rintro ⟨g, hg⟩
      have hfun : (fun i => g.linearEquiv (p i)) = maximizerConfig := funext hg
      rw [← fourPointInvariant_automorphism_invariant g p, hfun, fourPointInvariant_maximizerConfig]
  exact ⟨hbound, horbit, fourPointInvariant_fixedS, by rw [fourPointInvariant_fixedS]; norm_num⟩

/-- `cor:fp:maxmixed`: at a maximizer (`𝒜 = 4 / 19683`), each triple generates a `ComplexWindow` `W_k`
through which the fourth atom looks maximally mixed (`P_{W_k} p_k = e / 3`), giving identical all-word
probabilities to `(1 / 3) • albertUnit`. -/
theorem cor_fp_maxmixed {p : Fin 4 → Albert} (hp : ∀ i, IsAtom (p i))
    (hmax : fourPointInvariant p = 4 / 19683) (k : Fin 4) :
    let q : Fin 3 → Albert := fun i => p (k.succAbove i)
    0 < tripleDelta (q 0) (q 1) (q 2) ∧
    (∃ W : ComplexWindow, W.Contains (q 0) ∧ W.Contains (q 1) ∧ W.Contains (q 2) ∧
      ∀ x, W.Contains x ↔ InGeneratedAlgebra q x) ∧
    (∀ W : ComplexWindow, W.Contains (q 0) → W.Contains (q 1) → W.Contains (q 2) →
      (windowProj W (p k) : ComplexMatrix3) = (1 / 3 : ℂ) • (1 : ComplexMatrix3) ∧
      W.embedding (windowProj W (p k)) = (1 / 3 : ℝ) • albertUnit ∧
      ∀ w : Word (Fin 3),
        nativeWordProbability q (p k) w = nativeWordProbability q ((1 / 3 : ℝ) • albertUnit) w) := by
  intro q
  let σ : Equiv.Perm (Fin 4) :=
    { toFun := fun i =>
        if h : i = 3 then k else k.succAbove ⟨i.1, by have : i.1 < 4 := i.isLt; omega⟩
      invFun := fun j =>
        if j = k then 3
        else if j.1 < k.1 then ⟨j.1, j.isLt⟩
        else ⟨j.1 - 1, by omega⟩
      left_inv := fun i => by
        fin_cases k <;> fin_cases i <;> dsimp <;> decide
      right_inv := fun j => by
        fin_cases k <;> fin_cases j <;> dsimp <;> decide }
  have hσ3 : σ 3 = k := by simp [σ]
  have hσi : ∀ i : Fin 3, σ i.castSucc = k.succAbove i := fun i => by
    have hne3 : i.castSucc ≠ 3 := Fin.castSucc_ne_last i
    dsimp [σ]
    split_ifs with h
    · exact absurd h hne3
    · rfl
  have hinv_p : fourPointInvariant ![q 0, q 1, q 2, p k] = 4 / 19683 := by
    have hperm := fourPointInvariant_perm_invariant σ p
    have heq : (fun i : Fin 4 => p (σ i)) = ![q 0, q 1, q 2, p k] := by
      funext i
      fin_cases i <;> dsimp
      · exact congrArg p (hσi 0)
      · exact congrArg p (hσi 1)
      · exact congrArg p (hσi 2)
      · exact congrArg p hσ3
    rw [← heq, hperm, hmax]
  have hq0 : IsAtom (q 0) := hp _
  have hq1 : IsAtom (q 1) := hp _
  have hq2 : IsAtom (q 2) := hp _
  have hpk : IsAtom (p k) := hp k
  have hΔ_bound := (lem_fp_DeltaWmax hq0 hq1 hq2).1
  have hΔ_nn := tripleDelta_nonneg hq0 hq1 hq2
  have hΔ_pos : 0 < tripleDelta (q 0) (q 1) (q 2) := by
    by_contra hle
    have hz : tripleDelta (q 0) (q 1) (q 2) = 0 := le_antisymm (not_lt.mp hle) hΔ_nn
    have hfp0 := prop_windowdet_zero hq0 hq1 hq2 hpk hz
    linarith [hinv_p, hfp0]
  obtain ⟨_, _, _, _, hW_ex, _⟩ := lemma_A_window_generated hq0 hq1 hq2 hΔ_pos.ne'
  have hq_vec : ![q 0, q 1, q 2] = q := by
    funext i
    fin_cases i <;> dsimp <;> rfl
  rw [hq_vec] at hW_ex
  refine ⟨hΔ_pos, hW_ex, fun W h0 h1 h2 => ?_⟩
  have hdet_eq : fourPointInvariant ![q 0, q 1, q 2, p k] =
      tripleDelta (q 0) (q 1) (q 2) * (windowProj W (p k) : ComplexMatrix3).det.re := by
    simpa [windowDelta_eq_tripleDelta] using prop_windowdet W hq0 hq1 hq2 hpk h0 h1 h2
  have hM_bound := windowProj_atom_det_bounds W hpk
  have hdet_val : (windowProj W (p k) : ComplexMatrix3).det.re = 1 / 27 := by
    by_contra hne
    have hlt := lt_of_le_of_ne hM_bound.2 hne
    have hprod_lt : tripleDelta (q 0) (q 1) (q 2) * (windowProj W (p k) : ComplexMatrix3).det.re <
        (4 / 729) * (1 / 27) := by
      calc tripleDelta (q 0) (q 1) (q 2) * (windowProj W (p k) : ComplexMatrix3).det.re
          < tripleDelta (q 0) (q 1) (q 2) * (1 / 27 : ℝ) :=
            mul_lt_mul_of_pos_left hlt hΔ_pos
        _ ≤ (4 / 729 : ℝ) * (1 / 27 : ℝ) :=
            mul_le_mul_of_nonneg_right hΔ_bound (by norm_num)
    linarith [hinv_p, hdet_eq, hprod_lt]
  have hM_eq : (windowProj W (p k) : ComplexMatrix3) = (1 / 3 : ℂ) • (1 : ComplexMatrix3) :=
    (windowProj_atom_det_eq_max_iff W hpk).mp hdet_val
  have hproj_eq : windowProj W (p k) = (1 / 3 : ℝ) • (1 : Hermitian3) := by
    apply Subtype.ext
    rw [hM_eq]
    ext i j
    simp [Complex.real_smul]
  have hemb_eq : W.embedding (windowProj W (p k)) = (1 / 3 : ℝ) • albertUnit := by
    rw [hproj_eq, map_smul, W.unit]
  refine ⟨hM_eq, hemb_eq, fun w => ?_⟩
  have heff_mem : ∃ Ew : Hermitian3, W.embedding Ew = nativeWordEffect q w := by
    induction w with
    | nil => exact ⟨1, W.unit⟩
    | cons a ws ih =>
      rcases ih with ⟨Ews, hEws⟩
      have ha_mem : ∃ Qa : Hermitian3, W.embedding Qa = nativeOutcome q a := by
        cases a with
        | mk i b =>
          have hi : ∃ Pi : Hermitian3, W.embedding Pi = q i := by
            fin_cases i <;> dsimp
            · exact h0
            · exact h1
            · exact h2
          rcases hi with ⟨Pi, hPi⟩
          cases b
          · exact ⟨1 - Pi, by rw [map_sub, W.unit, hPi]; rfl⟩
          · exact ⟨Pi, hPi⟩
      rcases ha_mem with ⟨Qa, hQa⟩
      let h1 := W.product_closed Qa Ews
      rcases h1 with ⟨M1, hM1⟩
      let h2 := W.product_closed Qa M1
      rcases h2 with ⟨M2, hM2⟩
      let h3 := W.product_closed Qa Qa
      rcases h3 with ⟨Ma2, hMa2⟩
      let h4 := W.product_closed Ma2 Ews
      rcases h4 with ⟨M3, hM3⟩
      refine ⟨(2 : ℝ) • M2 - M3, ?_⟩
      change W.embedding ((2 : ℝ) • M2 - M3) = quadraticMap (nativeOutcome q a) (nativeWordEffect q ws)
      rw [map_sub, map_smul, W.preserves_product _ _ M2 hM2, W.preserves_product _ _ M1 hM1,
        W.preserves_product _ _ M3 hM3, W.preserves_product _ _ Ma2 hMa2, hQa, hEws]
      unfold quadraticMap
      rw [two_smul ℝ, two_smul ℕ]
  rcases heff_mem with ⟨Ew, hEw⟩
  rw [nativeWordProbability_eq_pairing, nativeWordProbability_eq_pairing, ← hEw]
  rw [← windowProj_tracePairing W (p k) Ew, hM_eq]
  have hmix : ((1 / 3 : ℂ) • (1 : ComplexMatrix3) * (Ew : ComplexMatrix3)).trace.re =
      tracePairing ((1 / 3 : ℝ) • albertUnit) (W.embedding Ew) := by
    have hwm : windowProj W ((1 / 3 : ℝ) • albertUnit) = (1 / 3 : ℝ) • (1 : Hermitian3) := by
      rw [map_smul, ← W.unit, windowProj_embedding]
    rw [← windowProj_tracePairing W ((1 / 3 : ℝ) • albertUnit) Ew, hwm]
    have hcoeff : (((1 / 3 : ℝ) • (1 : Hermitian3) : Hermitian3) : ComplexMatrix3) =
        (1 / 3 : ℂ) • (1 : ComplexMatrix3) := by
      ext i j; simp [Complex.real_smul]
    rw [hcoeff]
  exact hmix

/-- Deterministic `prop:windowlaw` kernel (companion `eq:fp:riesz`):
for every `W : ComplexWindow`, `T : Hermitian3`, and `x : Albert`, the exponent
`Re(Tr(T · P_W x))` equals `⟨x, W.embedding T⟩` and the determinant denominator satisfies
`N(e + W.embedding T) = Re(det(I + T))`. Measure-theoretic Wishart/Riesz law `ν_{3,4}`
remains outside deterministic finite-dimensional algebraic scope (`Interfaces/MeasuresAndRobustness`). -/
theorem complexWindow_laplace_integrand (W : ComplexWindow) (T : Hermitian3) (x : Albert) :
    ((T : ComplexMatrix3) * (windowProj W x : ComplexMatrix3)).trace.re =
      tracePairing x (W.embedding T) ∧
    albertCubicNorm (albertUnit + W.embedding T) =
      ((1 : ComplexMatrix3) + (T : ComplexMatrix3)).det.re ∧
    ((1 : ComplexMatrix3) + (T : ComplexMatrix3)).det.im = 0 := by
  have h1 : ((T : ComplexMatrix3) * (windowProj W x : ComplexMatrix3)).trace.re =
      tracePairing x (W.embedding T) := by
    rw [Matrix.trace_mul_comm, windowProj_tracePairing W x T]
  have h23 : albertCubicNorm (albertUnit + W.embedding T) =
        ((1 : ComplexMatrix3) + (T : ComplexMatrix3)).det.re ∧
      ((1 : ComplexMatrix3) + (T : ComplexMatrix3)).det.im = 0 := by
    have hemb : albertUnit + W.embedding T = W.embedding (1 + T) := by
      rw [map_add, W.unit]
    rw [hemb]
    exact complexWindow_albertCubicNorm_eq_det W (1 + T)
  exact ⟨h1, h23.1, h23.2⟩

end AlbertSequential
