/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.Shestakov
public import AppF.GlennieIngredients
public import ThreeAtomAndFourPoint
public import ComplexWindowDeterminantAndMax
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Associative `M₃(ℂ_i)`-bimodule reduction for `thm:glennie` (Step 1)

Proves:
1. `windowAdI` and `windowDef` using `AppF.octAdI` (`windowAdI z = (0, fun k => octAdI (z.2 k))`).
2. Associative `M₃(ℂ_i)`-bimodule laws on `M₃(𝕆)` (`Fin 3 → Fin 3 → Octonion`) via `matCtoO`:
   for `A B : Hermitian3` and arbitrary `z : Albert`,
   `Dop nativeOps (emb A) (emb B) z = skewComm [A, B] z`,
   `Ubr nativeOps (emb A) (emb A) (emb B) (emb B) z` corresponds to `[A, B] * Z * [A, B]`, and
   `DC nativeOps (emb A) (emb B) z = skewComm ([A, B] ^ 3) z`.
3. Nine-point `(t, u) ∈ {-1, 0, 1}²` polarization extractor `extractT2U2` linking
   `nativeGlennieF (emb A) (emb B) (emb C) z` to `glennieF_of_skew (sixProdComm A B C) z`,
   where `sixProdComm A B C = -([A,B][A,C][B,C] + 5 other permutations)`.
4. Decomposition of skew-Hermitian `Y : ComplexMatrix3` as `(Complex.I * windowMatrixLambda Y) • 1 + Y₀`
   with `Y₀ ∈ su(3)` expressed explicitly as a sum of 5 commutators `[h_r, h'_r]` of Hermitian
   matrices (`hermE`, `hermRe`, `hermIm`); `skewComm Q` is a Jordan derivation of `jordanMul`
   whenever `Q.conjTranspose = -Q` and `Q.trace = 0`, killing `glennieF_of_skew Y₀ z`.
   Hence at any idempotent `pD : Albert` (`jordanMul pD pD = pD`),
   `glennieF_window_eq_four_lambda_def`:
   `nativeGlennieF (emb A) (emb B) (emb C) (symmetryOf pD) = (4 * windowLambda A B C) • windowDef pD`,
   and for symmetries `2 • P_k - 1`, `glennieF_window_symm_eq_four_lambda_def`:
   `nativeGlennieF (symmetryOf (emb P₀)) (symmetryOf (emb P₁)) (symmetryOf (emb P₂)) (symmetryOf pD) =`
   `(4 * windowLambda (2 • P₀ - 1) (2 • P₁ - 1) (2 • P₂ - 1)) • windowDef pD`.
-/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false

noncomputable section

/-! ## Local coordinate helpers -/

private theorem oct_ext_local {x y : Octonion}
    (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
    (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK)
    (h5 : x.2.re = y.2.re) (h6 : x.2.imI = y.2.imI)
    (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y :=
  oct_ext' h1 h2 h3 h4 h5 h6 h7 h8

private theorem albert_ext_local {x y : Albert}
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

private theorem albertCoordinates_add (X Y : Fin 3 → Fin 3 → Octonion) :
    albertCoordinates (X + Y) = albertCoordinates X + albertCoordinates Y := by
  apply albert_ext_local
  · exact octonionReal_add (X 0 0) (Y 0 0)
  · exact octonionReal_add (X 1 1) (Y 1 1)
  · exact octonionReal_add (X 2 2) (Y 2 2)
  · rfl
  · rfl
  · rfl

private theorem albertCoordinates_sub (X Y : Fin 3 → Fin 3 → Octonion) :
    albertCoordinates (X - Y) = albertCoordinates X - albertCoordinates Y := by
  apply albert_ext_local
  · exact octonionReal_sub (X 0 0) (Y 0 0)
  · exact octonionReal_sub (X 1 1) (Y 1 1)
  · exact octonionReal_sub (X 2 2) (Y 2 2)
  · rfl
  · rfl
  · rfl

private theorem albertCoordinates_smul (r : ℝ) (X : Fin 3 → Fin 3 → Octonion) :
    albertCoordinates (r • X) = r • albertCoordinates X := by
  apply albert_ext_local
  · exact octonionReal_smul r (X 0 0)
  · exact octonionReal_smul r (X 1 1)
  · exact octonionReal_smul r (X 2 2)
  · rfl
  · rfl
  · rfl

private theorem albertCoordinates_zero :
    albertCoordinates (0 : Fin 3 → Fin 3 → Octonion) = 0 := by
  apply albert_ext_local
  · exact octonionReal_zero
  · exact octonionReal_zero
  · exact octonionReal_zero
  · rfl
  · rfl
  · rfl

private theorem octonionConj_sub (x y : Octonion) :
    octonionConj (x - y) = octonionConj x - octonionConj y := by
  rw [sub_eq_add_neg, octonionConj_add, octonionConj_neg, ← sub_eq_add_neg]

private theorem q_zero_re : (0 : Quaternion ℝ).re = 0 := rfl
private theorem q_zero_imI : (0 : Quaternion ℝ).imI = 0 := rfl
private theorem q_zero_imJ : (0 : Quaternion ℝ).imJ = 0 := rfl
private theorem q_zero_imK : (0 : Quaternion ℝ).imK = 0 := rfl
private theorem q_add_re (a b : Quaternion ℝ) : (a + b).re = a.re + b.re := rfl
private theorem q_add_imI (a b : Quaternion ℝ) : (a + b).imI = a.imI + b.imI := rfl
private theorem q_add_imJ (a b : Quaternion ℝ) : (a + b).imJ = a.imJ + b.imJ := rfl
private theorem q_add_imK (a b : Quaternion ℝ) : (a + b).imK = a.imK + b.imK := rfl
private theorem q_sub_re (a b : Quaternion ℝ) : (a - b).re = a.re - b.re := rfl
private theorem q_sub_imI (a b : Quaternion ℝ) : (a - b).imI = a.imI - b.imI := rfl
private theorem q_sub_imJ (a b : Quaternion ℝ) : (a - b).imJ = a.imJ - b.imJ := rfl
private theorem q_sub_imK (a b : Quaternion ℝ) : (a - b).imK = a.imK - b.imK := rfl
private theorem q_neg_re (a : Quaternion ℝ) : (-a).re = -a.re := rfl
private theorem q_neg_imI (a : Quaternion ℝ) : (-a).imI = -a.imI := rfl
private theorem q_neg_imJ (a : Quaternion ℝ) : (-a).imJ = -a.imJ := rfl
private theorem q_neg_imK (a : Quaternion ℝ) : (-a).imK = -a.imK := rfl
private theorem q_star_re (a : Quaternion ℝ) : (star a).re = a.re := by simp
private theorem q_star_imI (a : Quaternion ℝ) : (star a).imI = -a.imI := by simp
private theorem q_star_imJ (a : Quaternion ℝ) : (star a).imJ = -a.imJ := by simp
private theorem q_star_imK (a : Quaternion ℝ) : (star a).imK = -a.imK := by simp
private theorem q_mul_re (a b : Quaternion ℝ) :
    (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK := by simp
private theorem q_mul_imI (a b : Quaternion ℝ) :
    (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ := by simp
private theorem q_mul_imJ (a b : Quaternion ℝ) :
    (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI := by simp
private theorem q_mul_imK (a b : Quaternion ℝ) :
    (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re := by simp

/-! ## Section 1: Window `ad_i` and `windowDef` -/

/-- Entrywise `ad_i` on `Albert`: `0` on diagonals and `octAdI` on off-diagonals. -/
def windowAdI (z : Albert) : Albert :=
  (0, fun k => octAdI (z.2 k))

/-- Defect vector `Def(p) = B(p) - 2 p ∘ B(p)` with `B = windowAdI`. -/
def windowDef (z : Albert) : Albert :=
  windowAdI z - (2 : ℝ) • jordanMul z (windowAdI z)

theorem windowAdI_zero : windowAdI 0 = 0 := by
  apply albert_ext_local
  · rfl
  · rfl
  · rfl
  · simp [windowAdI, albert_zero_snd, octAdI, octonionMul_zero_left, octonionMul_zero_right]
  · simp [windowAdI, albert_zero_snd, octAdI, octonionMul_zero_left, octonionMul_zero_right]
  · simp [windowAdI, albert_zero_snd, octAdI, octonionMul_zero_left, octonionMul_zero_right]

theorem windowAdI_albertUnit : windowAdI albertUnit = 0 := by
  apply albert_ext_local
  · rfl
  · rfl
  · rfl
  · simp [windowAdI, albertUnit, albert_zero_snd, octAdI, octonionMul_zero_left, octonionMul_zero_right]
  · simp [windowAdI, albertUnit, albert_zero_snd, octAdI, octonionMul_zero_left, octonionMul_zero_right]
  · simp [windowAdI, albertUnit, albert_zero_snd, octAdI, octonionMul_zero_left, octonionMul_zero_right]

theorem windowAdI_add (x y : Albert) : windowAdI (x + y) = windowAdI x + windowAdI y := by
  apply albert_ext_local
  · exact (add_zero (0 : ℝ)).symm
  · exact (add_zero (0 : ℝ)).symm
  · exact (add_zero (0 : ℝ)).symm
  · change octAdI ((x + y).2 0) = octAdI (x.2 0) + octAdI (y.2 0)
    simp only [albert_add_snd, octAdI, octonionMul_add_left, octonionMul_add_right]; abel
  · change octAdI ((x + y).2 1) = octAdI (x.2 1) + octAdI (y.2 1)
    simp only [albert_add_snd, octAdI, octonionMul_add_left, octonionMul_add_right]; abel
  · change octAdI ((x + y).2 2) = octAdI (x.2 2) + octAdI (y.2 2)
    simp only [albert_add_snd, octAdI, octonionMul_add_left, octonionMul_add_right]; abel

theorem windowAdI_sub (x y : Albert) : windowAdI (x - y) = windowAdI x - windowAdI y := by
  apply albert_ext_local
  · exact (sub_zero (0 : ℝ)).symm
  · exact (sub_zero (0 : ℝ)).symm
  · exact (sub_zero (0 : ℝ)).symm
  · change octAdI ((x - y).2 0) = octAdI (x.2 0) - octAdI (y.2 0)
    simp only [albert_sub_snd, octAdI, octonionMul_sub_left, octonionMul_sub_right]; abel
  · change octAdI ((x - y).2 1) = octAdI (x.2 1) - octAdI (y.2 1)
    simp only [albert_sub_snd, octAdI, octonionMul_sub_left, octonionMul_sub_right]; abel
  · change octAdI ((x - y).2 2) = octAdI (x.2 2) - octAdI (y.2 2)
    simp only [albert_sub_snd, octAdI, octonionMul_sub_left, octonionMul_sub_right]; abel

theorem windowAdI_smul (r : ℝ) (x : Albert) : windowAdI (r • x) = r • windowAdI x := by
  apply albert_ext_local
  · exact (mul_zero r).symm
  · exact (mul_zero r).symm
  · exact (mul_zero r).symm
  · change octAdI ((r • x).2 0) = r • octAdI (x.2 0)
    simp only [albert_smul_snd, octAdI, octonionMul_smul_left, octonionMul_smul_right, smul_sub]
  · change octAdI ((r • x).2 1) = r • octAdI (x.2 1)
    simp only [albert_smul_snd, octAdI, octonionMul_smul_left, octonionMul_smul_right, smul_sub]
  · change octAdI ((r • x).2 2) = r • octAdI (x.2 2)
    simp only [albert_smul_snd, octAdI, octonionMul_smul_left, octonionMul_smul_right, smul_sub]

/-! ## Section 2: `M₃(ℂ_i)`-bimodule laws on `M₃(𝕆)` -/

/-- Lift a `3 × 3` complex matrix to `Fin 3 → Fin 3 → Octonion` via `ℂ_i = span(1, i)`. -/
def matCtoO (M : ComplexMatrix3) : Fin 3 → Fin 3 → Octonion :=
  fun i j => complexToOctonion (M i j)

theorem complexToOctonion_mul (a b : ℂ) :
    complexToOctonion (a * b) = octonionMul (complexToOctonion a) (complexToOctonion b) := by
  apply oct_ext_local <;>
    simp only [complexToOctonion_apply, octonionMul, q_mul_re,
      q_mul_imI, q_mul_imJ, q_mul_imK, Complex.mul_re, Complex.mul_im,
      q_star_re, q_star_imI, q_star_imJ, q_star_imK,
      q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
      q_add_re, q_add_imI, q_add_imJ, q_add_imK,
      q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
    ring

theorem complexToOctonion_star (a : ℂ) :
    complexToOctonion (star a) = octonionConj (complexToOctonion a) := by
  apply oct_ext_local <;>
    simp only [complexToOctonion_apply, octonionConj, Complex.star_def,
      Complex.conj_re, Complex.conj_im, q_star_re, q_star_imI,
      q_star_imJ, q_star_imK, q_zero_re, q_zero_imI,
      q_zero_imJ, q_zero_imK, neg_zero]

theorem complexToOctonion_one : complexToOctonion 1 = octonionScalar 1 := by
  apply oct_ext_local <;> simp [complexToOctonion_apply, octonionScalar]

theorem complexToOctonion_I : complexToOctonion Complex.I = octI := by
  apply oct_ext_local <;> simp [complexToOctonion_apply, octI]

theorem complexToOctonion_assoc_left (a b : ℂ) (u : Octonion) :
    octonionMul (octonionMul (complexToOctonion a) (complexToOctonion b)) u =
      octonionMul (complexToOctonion a) (octonionMul (complexToOctonion b) u) := by
  apply oct_ext_local <;>
    simp only [complexToOctonion_apply, octonionMul,
      q_add_re, q_add_imI, q_add_imJ, q_add_imK,
      q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
      q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
      q_star_re, q_star_imI, q_star_imJ, q_star_imK,
      q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
    ring

theorem complexToOctonion_assoc_mid (a b : ℂ) (u : Octonion) :
    octonionMul (octonionMul (complexToOctonion a) u) (complexToOctonion b) =
      octonionMul (complexToOctonion a) (octonionMul u (complexToOctonion b)) := by
  apply oct_ext_local <;>
    simp only [complexToOctonion_apply, octonionMul,
      q_add_re, q_add_imI, q_add_imJ, q_add_imK,
      q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
      q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
      q_star_re, q_star_imI, q_star_imJ, q_star_imK,
      q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
    ring

theorem complexToOctonion_assoc_right (a b : ℂ) (u : Octonion) :
    octonionMul (octonionMul u (complexToOctonion a)) (complexToOctonion b) =
      octonionMul u (octonionMul (complexToOctonion a) (complexToOctonion b)) := by
  apply oct_ext_local <;>
    simp only [complexToOctonion_apply, octonionMul,
      q_add_re, q_add_imI, q_add_imJ, q_add_imK,
      q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
      q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
      q_star_re, q_star_imI, q_star_imJ, q_star_imK,
      q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
    ring

theorem matCtoO_zero : matCtoO 0 = 0 := by
  funext i j; simp [matCtoO, map_zero]

theorem matCtoO_add (M N : ComplexMatrix3) : matCtoO (M + N) = matCtoO M + matCtoO N := by
  funext i j; simp [matCtoO, map_add]

theorem matCtoO_sub (M N : ComplexMatrix3) : matCtoO (M - N) = matCtoO M - matCtoO N := by
  funext i j; simp [matCtoO, map_sub]

theorem matCtoO_neg (M : ComplexMatrix3) : matCtoO (-M) = -matCtoO M := by
  funext i j; simp [matCtoO, map_neg]

theorem matCtoO_smul (r : ℝ) (M : ComplexMatrix3) : matCtoO (r • M) = r • matCtoO M := by
  funext i j
  change complexToOctonion (r • M i j) = r • complexToOctonion (M i j)
  rw [map_smul]

private theorem octonionMul_sum_left {ι : Type*} (s : Finset ι) (f : ι → Octonion) (y : Octonion) :
    octonionMul (∑ i ∈ s, f i) y = ∑ i ∈ s, octonionMul (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [octonionMul_zero_left]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, octonionMul_add_left, ih]

private theorem octonionMul_sum_right {ι : Type*} (s : Finset ι) (x : Octonion) (f : ι → Octonion) :
    octonionMul x (∑ i ∈ s, f i) = ∑ i ∈ s, octonionMul x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [octonionMul_zero_right]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, octonionMul_add_right, ih]

theorem matCtoO_mul (M N : ComplexMatrix3) :
    matCtoO (M * N) = octonionMatrixMul (matCtoO M) (matCtoO N) := by
  funext i j
  simp only [matCtoO, octonionMatrixMul, Matrix.mul_apply, map_sum, complexToOctonion_mul]

theorem octonionMatrixMul_add_left (X Y Z : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul (X + Y) Z = octonionMatrixMul X Z + octonionMatrixMul Y Z := by
  funext i j
  simp only [octonionMatrixMul, Pi.add_apply, octonionMul_add_left, Finset.sum_add_distrib]

theorem octonionMatrixMul_add_right (X Y Z : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul X (Y + Z) = octonionMatrixMul X Y + octonionMatrixMul X Z := by
  funext i j
  simp only [octonionMatrixMul, Pi.add_apply, octonionMul_add_right, Finset.sum_add_distrib]

theorem octonionMatrixMul_sub_left (X Y Z : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul (X - Y) Z = octonionMatrixMul X Z - octonionMatrixMul Y Z := by
  funext i j
  simp only [octonionMatrixMul, Pi.sub_apply, octonionMul_sub_left, Finset.sum_sub_distrib]

theorem octonionMatrixMul_sub_right (X Y Z : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul X (Y - Z) = octonionMatrixMul X Y - octonionMatrixMul X Z := by
  funext i j
  simp only [octonionMatrixMul, Pi.sub_apply, octonionMul_sub_right, Finset.sum_sub_distrib]

theorem octonionMatrixMul_smul_left (r : ℝ) (X Y : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul (r • X) Y = r • octonionMatrixMul X Y := by
  funext i j
  simp only [octonionMatrixMul, Pi.smul_apply, octonionMul_smul_left, Finset.smul_sum]

theorem octonionMatrixMul_smul_right (r : ℝ) (X Y : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul X (r • Y) = r • octonionMatrixMul X Y := by
  funext i j
  simp only [octonionMatrixMul, Pi.smul_apply, octonionMul_smul_right, Finset.smul_sum]

theorem octonionMatrixMul_zero_left (X : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul 0 X = 0 := by
  funext i j
  simp [octonionMatrixMul, octonionMul_zero_left]

theorem octonionMatrixMul_zero_right (X : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul X 0 = 0 := by
  funext i j
  simp [octonionMatrixMul, octonionMul_zero_right]

theorem octonionMatrixMul_neg_left (X Y : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul (-X) Y = -octonionMatrixMul X Y := by
  rw [← neg_one_smul ℝ X, octonionMatrixMul_smul_left, neg_one_smul]

theorem octonionMatrixMul_neg_right (X Y : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul X (-Y) = -octonionMatrixMul X Y := by
  rw [← neg_one_smul ℝ Y, octonionMatrixMul_smul_right, neg_one_smul]

theorem octonionMatrixMul_C_C_O (M N : ComplexMatrix3) (Z : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul (matCtoO M) (octonionMatrixMul (matCtoO N) Z) =
      octonionMatrixMul (matCtoO (M * N)) Z := by
  funext i j
  simp only [octonionMatrixMul, matCtoO_mul]
  calc
    ∑ k : Fin 3, octonionMul (matCtoO M i k) (∑ l : Fin 3, octonionMul (matCtoO N k l) (Z l j))
      = ∑ k : Fin 3, ∑ l : Fin 3,
          octonionMul (matCtoO M i k) (octonionMul (matCtoO N k l) (Z l j)) := by
            refine Finset.sum_congr rfl fun k _ => octonionMul_sum_right _ _ _
    _ = ∑ l : Fin 3, ∑ k : Fin 3,
          octonionMul (octonionMul (matCtoO M i k) (matCtoO N k l)) (Z l j) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
            exact (complexToOctonion_assoc_left (M i k) (N k l) (Z l j)).symm
    _ = ∑ l : Fin 3,
          octonionMul (∑ k : Fin 3, octonionMul (matCtoO M i k) (matCtoO N k l)) (Z l j) := by
            refine Finset.sum_congr rfl fun l _ => (octonionMul_sum_left _ _ _).symm

theorem octonionMatrixMul_C_O_C (M : ComplexMatrix3) (Z : Fin 3 → Fin 3 → Octonion)
    (N : ComplexMatrix3) :
    octonionMatrixMul (matCtoO M) (octonionMatrixMul Z (matCtoO N)) =
      octonionMatrixMul (octonionMatrixMul (matCtoO M) Z) (matCtoO N) := by
  funext i j
  simp only [octonionMatrixMul]
  calc
    ∑ k : Fin 3, octonionMul (matCtoO M i k) (∑ l : Fin 3, octonionMul (Z k l) (matCtoO N l j))
      = ∑ k : Fin 3, ∑ l : Fin 3,
          octonionMul (matCtoO M i k) (octonionMul (Z k l) (matCtoO N l j)) := by
            refine Finset.sum_congr rfl fun k _ => octonionMul_sum_right _ _ _
    _ = ∑ l : Fin 3, ∑ k : Fin 3,
          octonionMul (octonionMul (matCtoO M i k) (Z k l)) (matCtoO N l j) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
            exact (complexToOctonion_assoc_mid (M i k) (N l j) (Z k l)).symm
    _ = ∑ l : Fin 3,
          octonionMul (∑ k : Fin 3, octonionMul (matCtoO M i k) (Z k l)) (matCtoO N l j) := by
            refine Finset.sum_congr rfl fun l _ => (octonionMul_sum_left _ _ _).symm

theorem octonionMatrixMul_O_C_C (Z : Fin 3 → Fin 3 → Octonion) (M N : ComplexMatrix3) :
    octonionMatrixMul (octonionMatrixMul Z (matCtoO M)) (matCtoO N) =
      octonionMatrixMul Z (matCtoO (M * N)) := by
  funext i j
  simp only [octonionMatrixMul, matCtoO_mul]
  calc
    ∑ l : Fin 3, octonionMul (∑ k : Fin 3, octonionMul (Z i k) (matCtoO M k l)) (matCtoO N l j)
      = ∑ l : Fin 3, ∑ k : Fin 3,
          octonionMul (octonionMul (Z i k) (matCtoO M k l)) (matCtoO N l j) := by
            refine Finset.sum_congr rfl fun l _ => octonionMul_sum_left _ _ _
    _ = ∑ k : Fin 3, ∑ l : Fin 3,
          octonionMul (Z i k) (octonionMul (matCtoO M k l) (matCtoO N l j)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            exact complexToOctonion_assoc_right (M k l) (N l j) (Z i k)
    _ = ∑ k : Fin 3,
          octonionMul (Z i k) (∑ l : Fin 3, octonionMul (matCtoO M k l) (matCtoO N l j)) := by
            refine Finset.sum_congr rfl fun k _ => (octonionMul_sum_right _ _ _).symm

/-- Conjugate transpose of a `3 × 3` octonion matrix. -/
def octMatConjTranspose (Z : Fin 3 → Fin 3 → Octonion) : Fin 3 → Fin 3 → Octonion :=
  fun i j => octonionConj (Z j i)

/-- A `3 × 3` octonion matrix is Hermitian when `octMatConjTranspose Z = Z`. -/
def IsOctHermitian (Z : Fin 3 → Fin 3 → Octonion) : Prop :=
  octMatConjTranspose Z = Z

theorem octMatConjTranspose_albertMatrix (z : Albert) :
    octMatConjTranspose (albertMatrix z) = albertMatrix z := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [octMatConjTranspose, albertMatrix, octonionConj_scalar, octonionConj_conj]

theorem octMatConjTranspose_add (X Y : Fin 3 → Fin 3 → Octonion) :
    octMatConjTranspose (X + Y) = octMatConjTranspose X + octMatConjTranspose Y := by
  funext i j; simp [octMatConjTranspose, octonionConj_add]

theorem octMatConjTranspose_sub (X Y : Fin 3 → Fin 3 → Octonion) :
    octMatConjTranspose (X - Y) = octMatConjTranspose X - octMatConjTranspose Y := by
  funext i j; simp [octMatConjTranspose, octonionConj_sub]

theorem octMatConjTranspose_smul (r : ℝ) (X : Fin 3 → Fin 3 → Octonion) :
    octMatConjTranspose (r • X) = r • octMatConjTranspose X := by
  funext i j; simp [octMatConjTranspose, octonionConj_smul]

theorem octMatConjTranspose_mul (X Y : Fin 3 → Fin 3 → Octonion) :
    octMatConjTranspose (octonionMatrixMul X Y) =
      octonionMatrixMul (octMatConjTranspose Y) (octMatConjTranspose X) := by
  funext i j
  simp only [octMatConjTranspose, octonionMatrixMul]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, octonionConj_add, octonionConj_add,
    octonionConj_mul, octonionConj_mul, octonionConj_mul]

theorem octMatConjTranspose_matCtoO (M : ComplexMatrix3) :
    octMatConjTranspose (matCtoO M) = matCtoO M.conjTranspose := by
  funext i j
  simp only [octMatConjTranspose, matCtoO, Matrix.conjTranspose_apply, complexToOctonion_star]

theorem octMatConjTranspose_matCtoO_skew (M : ComplexMatrix3) (hM : M.conjTranspose = -M) :
    octMatConjTranspose (matCtoO M) = -matCtoO M := by
  rw [octMatConjTranspose_matCtoO, hM, matCtoO_neg]

private theorem octonionScalar_octonionReal_of_conj_eq {u : Octonion} (hu : octonionConj u = u) :
    octonionScalar (octonionReal u) = u := by
  have hi : -u.1.imI = u.1.imI := by
    simpa [octonionConj, oct_conj_fst] using congrArg (fun x : Octonion => x.1.imI) hu
  have hj : -u.1.imJ = u.1.imJ := by
    simpa [octonionConj, oct_conj_fst] using congrArg (fun x : Octonion => x.1.imJ) hu
  have hk : -u.1.imK = u.1.imK := by
    simpa [octonionConj, oct_conj_fst] using congrArg (fun x : Octonion => x.1.imK) hu
  have h2 : -u.2 = u.2 := congrArg (fun x : Octonion => x.2) hu
  have h20 : u.2 = 0 := by
    have h2re : -u.2.re = u.2.re := congrArg (fun q : Quaternion ℝ => q.re) h2
    have h2i : -u.2.imI = u.2.imI := congrArg (fun q : Quaternion ℝ => q.imI) h2
    have h2j : -u.2.imJ = u.2.imJ := congrArg (fun q : Quaternion ℝ => q.imJ) h2
    have h2k : -u.2.imK = u.2.imK := congrArg (fun q : Quaternion ℝ => q.imK) h2
    apply Quaternion.ext <;> simp only [q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;> linarith
  apply oct_ext_local <;>
    simp only [octonionScalar, octonionReal, q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
    try linarith
  · exact (congrArg (fun q : Quaternion ℝ => q.re) h20).symm
  · exact (congrArg (fun q : Quaternion ℝ => q.imI) h20).symm
  · exact (congrArg (fun q : Quaternion ℝ => q.imJ) h20).symm
  · exact (congrArg (fun q : Quaternion ℝ => q.imK) h20).symm

theorem albertMatrix_albertCoordinates_of_isOctHermitian {Z : Fin 3 → Fin 3 → Octonion}
    (hZ : IsOctHermitian Z) : albertMatrix (albertCoordinates Z) = Z := by
  have hdiag : ∀ i : Fin 3, octonionScalar (octonionReal (Z i i)) = Z i i := fun i =>
    octonionScalar_octonionReal_of_conj_eq (congrFun (congrFun hZ i) i)
  have hoff : ∀ i j : Fin 3, octonionConj (Z i j) = Z j i := fun i j =>
    congrFun (congrFun hZ j) i
  funext i j
  fin_cases i <;> fin_cases j <;> simp [albertMatrix, albertCoordinates]
  · exact hdiag 0
  · exact hoff 0 1
  · exact hdiag 1
  · exact hoff 0 2
  · exact hoff 1 2
  · exact hdiag 2

private theorem albertMatrix_smul_aux (r : ℝ) (a : Albert) :
    albertMatrix (r • a) = r • albertMatrix a := by
  funext p q
  fin_cases p <;> fin_cases q <;>
    simp only [albertMatrix, Pi.smul_apply, albert_smul_fst, albert_smul_snd,
      octonionScalar_smul, octonionConj_smul]

theorem albertMatrix_jordanMul (x y : Albert) :
    albertMatrix (jordanMul x y) =
      (1 / 2 : ℝ) •
        (octonionMatrixMul (albertMatrix x) (albertMatrix y) +
          octonionMatrixMul (albertMatrix y) (albertMatrix x)) := by
  let M := octonionMatrixMul (albertMatrix x) (albertMatrix y) +
    octonionMatrixMul (albertMatrix y) (albertMatrix x)
  have hM : IsOctHermitian M := by
    unfold IsOctHermitian M
    rw [octMatConjTranspose_add, octMatConjTranspose_mul, octMatConjTranspose_mul,
      octMatConjTranspose_albertMatrix, octMatConjTranspose_albertMatrix, add_comm]
  have halm : albertMatrix (albertCoordinates M) = M :=
    albertMatrix_albertCoordinates_of_isOctHermitian hM
  change albertMatrix ((1 / 2 : ℝ) • albertCoordinates M) = (1 / 2 : ℝ) • M
  rw [albertMatrix_smul_aux, halm]

theorem albertMatrix_standardComplexWindow (A : Hermitian3) :
    albertMatrix (standardComplexWindow.embedding A) = matCtoO (A : ComplexMatrix3) := by
  have hA := A.prop
  have hdiag : ∀ k : Fin 3, ((A : ComplexMatrix3) k k).im = 0 := fun k => by
    have h := congrArg (fun M : ComplexMatrix3 => (M k k).im) hA
    simp only [Matrix.star_apply, Complex.star_def, Complex.conj_im] at h
    linarith
  have hoff : ∀ i j : Fin 3, star ((A : ComplexMatrix3) i j) = (A : ComplexMatrix3) j i := fun i j =>
    congrArg (fun M : ComplexMatrix3 => M j i) hA
  funext i j
  fin_cases i <;> fin_cases j <;>
    dsimp only [albertMatrix, standardComplexWindow, LinearMap.coe_mk, AddHom.coe_mk,
      complexHermToAlbert, matCtoO]
  · change octonionScalar ((A : ComplexMatrix3) 0 0).re = complexToOctonion ((A : ComplexMatrix3) 0 0)
    rw [complexToOctonion_apply]; apply oct_ext_local <;> simp [octonionScalar, hdiag 0]
  · rfl
  · rfl
  · change octonionConj (complexToOctonion ((A : ComplexMatrix3) 0 1)) =
      complexToOctonion ((A : ComplexMatrix3) 1 0)
    rw [← hoff 0 1, complexToOctonion_star]
  · change octonionScalar ((A : ComplexMatrix3) 1 1).re = complexToOctonion ((A : ComplexMatrix3) 1 1)
    rw [complexToOctonion_apply]; apply oct_ext_local <;> simp [octonionScalar, hdiag 1]
  · rfl
  · change octonionConj (complexToOctonion ((A : ComplexMatrix3) 0 2)) =
      complexToOctonion ((A : ComplexMatrix3) 2 0)
    rw [← hoff 0 2, complexToOctonion_star]
  · change octonionConj (complexToOctonion ((A : ComplexMatrix3) 1 2)) =
      complexToOctonion ((A : ComplexMatrix3) 2 1)
    rw [← hoff 1 2, complexToOctonion_star]
  · change octonionScalar ((A : ComplexMatrix3) 2 2).re = complexToOctonion ((A : ComplexMatrix3) 2 2)
    rw [complexToOctonion_apply]; apply oct_ext_local <;> simp [octonionScalar, hdiag 2]

theorem albertMatrix_injective : Function.Injective albertMatrix := by
  intro x y h
  apply albert_ext_local
  · exact octonionScalar_re_eq (congrFun (congrFun h 0) 0)
  · exact octonionScalar_re_eq (congrFun (congrFun h 1) 1)
  · exact octonionScalar_re_eq (congrFun (congrFun h 2) 2)
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 1) 2
where
  octonionScalar_re_eq {r s : ℝ} (h : octonionScalar r = octonionScalar s) : r = s :=
    congrArg octonionReal h

theorem albertMatrix_add (x y : Albert) :
    albertMatrix (x + y) = albertMatrix x + albertMatrix y := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Pi.add_apply, albertMatrix, albert_add_fst, albert_add_snd,
      octonionScalar_add, octonionConj_add]

theorem albertMatrix_sub (x y : Albert) :
    albertMatrix (x - y) = albertMatrix x - albertMatrix y := by
  have hscal_sub : ∀ r s : ℝ, octonionScalar (r - s) = octonionScalar r - octonionScalar s := fun r s => by
    apply oct_ext_local
    · rfl
    all_goals exact (sub_zero (0 : ℝ)).symm
  funext i j
  fin_cases i <;> fin_cases j <;> dsimp only [albertMatrix, Pi.sub_apply]
  · exact hscal_sub (x.1 0) (y.1 0)
  · rfl
  · rfl
  · exact octonionConj_sub (x.2 0) (y.2 0)
  · exact hscal_sub (x.1 1) (y.1 1)
  · rfl
  · exact octonionConj_sub (x.2 1) (y.2 1)
  · exact octonionConj_sub (x.2 2) (y.2 2)
  · exact hscal_sub (x.1 2) (y.1 2)

theorem albertMatrix_smul (r : ℝ) (x : Albert) :
    albertMatrix (r • x) = r • albertMatrix x :=
  albertMatrix_smul_aux r x

theorem albertMatrix_albertUnit :
    albertMatrix albertUnit = matCtoO (1 : ComplexMatrix3) := by
  have h1 : octonionScalar 1 = complexToOctonion 1 := complexToOctonion_one.symm
  have h0 : (0 : Octonion) = complexToOctonion 0 := (map_zero complexToOctonion).symm
  have hc0 : octonionConj 0 = complexToOctonion 0 := by
    rw [map_zero]
    apply oct_ext_local <;> simp [octonionConj]
  funext i j
  fin_cases i <;> fin_cases j <;>
    dsimp only [albertMatrix, albertUnit, matCtoO]
  · rw [Matrix.one_apply_eq]; exact h1
  · rw [Matrix.one_apply_ne (by decide)]; exact h0
  · rw [Matrix.one_apply_ne (by decide)]; exact h0
  · rw [Matrix.one_apply_ne (by decide)]; exact hc0
  · rw [Matrix.one_apply_eq]; exact h1
  · rw [Matrix.one_apply_ne (by decide)]; exact h0
  · rw [Matrix.one_apply_ne (by decide)]; exact hc0
  · rw [Matrix.one_apply_ne (by decide)]; exact hc0
  · rw [Matrix.one_apply_eq]; exact h1

/-! ## Section 3: Commutator action `skewComm` and `Dop`/`Ubr`/`DC` on the window -/

/-- Matrix commutator action `[Q, Z]` in `Albert` coordinates. -/
def skewComm (Q : ComplexMatrix3) (z : Albert) : Albert :=
  albertCoordinates
    (octonionMatrixMul (matCtoO Q) (albertMatrix z) -
      octonionMatrixMul (albertMatrix z) (matCtoO Q))

theorem isOctHermitian_skewComm (Q : ComplexMatrix3) (hQ : Q.conjTranspose = -Q) (z : Albert) :
    IsOctHermitian
      (octonionMatrixMul (matCtoO Q) (albertMatrix z) -
        octonionMatrixMul (albertMatrix z) (matCtoO Q)) := by
  unfold IsOctHermitian
  rw [octMatConjTranspose_sub, octMatConjTranspose_mul, octMatConjTranspose_mul,
    octMatConjTranspose_matCtoO_skew Q hQ, octMatConjTranspose_albertMatrix,
    octonionMatrixMul_neg_right, octonionMatrixMul_neg_left]
  abel

theorem albertMatrix_skewComm (Q : ComplexMatrix3) (hQ : Q.conjTranspose = -Q) (z : Albert) :
    albertMatrix (skewComm Q z) =
      octonionMatrixMul (matCtoO Q) (albertMatrix z) -
        octonionMatrixMul (albertMatrix z) (matCtoO Q) :=
  albertMatrix_albertCoordinates_of_isOctHermitian (isOctHermitian_skewComm Q hQ z)

theorem skewComm_add_left (Q₁ Q₂ : ComplexMatrix3) (z : Albert) :
    skewComm (Q₁ + Q₂) z = skewComm Q₁ z + skewComm Q₂ z := by
  unfold skewComm
  rw [matCtoO_add, octonionMatrixMul_add_left, octonionMatrixMul_add_right]
  rw [show octonionMatrixMul (matCtoO Q₁) (albertMatrix z) +
        octonionMatrixMul (matCtoO Q₂) (albertMatrix z) -
      (octonionMatrixMul (albertMatrix z) (matCtoO Q₁) +
        octonionMatrixMul (albertMatrix z) (matCtoO Q₂)) =
      (octonionMatrixMul (matCtoO Q₁) (albertMatrix z) -
        octonionMatrixMul (albertMatrix z) (matCtoO Q₁)) +
      (octonionMatrixMul (matCtoO Q₂) (albertMatrix z) -
        octonionMatrixMul (albertMatrix z) (matCtoO Q₂)) by abel]
  exact albertCoordinates_add _ _

theorem skewComm_sub_left (Q₁ Q₂ : ComplexMatrix3) (z : Albert) :
    skewComm (Q₁ - Q₂) z = skewComm Q₁ z - skewComm Q₂ z := by
  unfold skewComm
  rw [matCtoO_sub, octonionMatrixMul_sub_left, octonionMatrixMul_sub_right]
  rw [show (octonionMatrixMul (matCtoO Q₁) (albertMatrix z) -
        octonionMatrixMul (matCtoO Q₂) (albertMatrix z)) -
      (octonionMatrixMul (albertMatrix z) (matCtoO Q₁) -
        octonionMatrixMul (albertMatrix z) (matCtoO Q₂)) =
      (octonionMatrixMul (matCtoO Q₁) (albertMatrix z) -
        octonionMatrixMul (albertMatrix z) (matCtoO Q₁)) -
      (octonionMatrixMul (matCtoO Q₂) (albertMatrix z) -
        octonionMatrixMul (albertMatrix z) (matCtoO Q₂)) by abel]
  exact albertCoordinates_sub _ _

theorem skewComm_neg_left (Q : ComplexMatrix3) (z : Albert) :
    skewComm (-Q) z = -skewComm Q z := by
  have h := skewComm_sub_left 0 Q z
  have hz : skewComm 0 z = 0 := by
    unfold skewComm
    rw [matCtoO_zero, octonionMatrixMul_zero_left, octonionMatrixMul_zero_right, sub_zero]
    exact albertCoordinates_zero
  simpa [hz] using h

theorem skewComm_smul_left (r : ℝ) (Q : ComplexMatrix3) (z : Albert) :
    skewComm (r • Q) z = r • skewComm Q z := by
  unfold skewComm
  rw [matCtoO_smul, octonionMatrixMul_smul_left, octonionMatrixMul_smul_right, ← smul_sub]
  exact albertCoordinates_smul _ _

theorem skewComm_add_right (Q : ComplexMatrix3) (z₁ z₂ : Albert) :
    skewComm Q (z₁ + z₂) = skewComm Q z₁ + skewComm Q z₂ := by
  unfold skewComm
  rw [albertMatrix_add, octonionMatrixMul_add_right, octonionMatrixMul_add_left]
  rw [show (octonionMatrixMul (matCtoO Q) (albertMatrix z₁) +
        octonionMatrixMul (matCtoO Q) (albertMatrix z₂)) -
      (octonionMatrixMul (albertMatrix z₁) (matCtoO Q) +
        octonionMatrixMul (albertMatrix z₂) (matCtoO Q)) =
      (octonionMatrixMul (matCtoO Q) (albertMatrix z₁) -
        octonionMatrixMul (albertMatrix z₁) (matCtoO Q)) +
      (octonionMatrixMul (matCtoO Q) (albertMatrix z₂) -
        octonionMatrixMul (albertMatrix z₂) (matCtoO Q)) by abel]
  exact albertCoordinates_add _ _

theorem skewComm_sub_right (Q : ComplexMatrix3) (z₁ z₂ : Albert) :
    skewComm Q (z₁ - z₂) = skewComm Q z₁ - skewComm Q z₂ := by
  unfold skewComm
  rw [albertMatrix_sub, octonionMatrixMul_sub_right, octonionMatrixMul_sub_left]
  rw [show (octonionMatrixMul (matCtoO Q) (albertMatrix z₁) -
        octonionMatrixMul (matCtoO Q) (albertMatrix z₂)) -
      (octonionMatrixMul (albertMatrix z₁) (matCtoO Q) -
        octonionMatrixMul (albertMatrix z₂) (matCtoO Q)) =
      (octonionMatrixMul (matCtoO Q) (albertMatrix z₁) -
        octonionMatrixMul (albertMatrix z₁) (matCtoO Q)) -
      (octonionMatrixMul (matCtoO Q) (albertMatrix z₂) -
        octonionMatrixMul (albertMatrix z₂) (matCtoO Q)) by abel]
  exact albertCoordinates_sub _ _

theorem skewComm_smul_right (r : ℝ) (Q : ComplexMatrix3) (z : Albert) :
    skewComm Q (r • z) = r • skewComm Q z := by
  unfold skewComm
  rw [albertMatrix_smul, octonionMatrixMul_smul_right, octonionMatrixMul_smul_left, ← smul_sub]
  exact albertCoordinates_smul _ _

theorem skewComm_albertUnit (Q : ComplexMatrix3) : skewComm Q albertUnit = 0 := by
  unfold skewComm
  rw [albertMatrix_albertUnit, ← matCtoO_mul, ← matCtoO_mul, Matrix.mul_one, Matrix.one_mul, sub_self]
  exact albertCoordinates_zero

theorem windowAdI_eq_skewComm (z : Albert) :
    windowAdI z = skewComm (Complex.I • (1 : ComplexMatrix3)) z := by
  have hI : (Complex.I • (1 : ComplexMatrix3)).conjTranspose = -(Complex.I • (1 : ComplexMatrix3)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
  apply albertMatrix_injective
  rw [albertMatrix_skewComm _ hI z]
  funext i j
  have hI0 : complexToOctonion Complex.I = octI := complexToOctonion_I
  have h0 : complexToOctonion (0 : ℂ) = 0 := map_zero complexToOctonion
  have hL : octonionMatrixMul (matCtoO (Complex.I • (1 : ComplexMatrix3))) (albertMatrix z) i j =
      octonionMul octI (albertMatrix z i j) := by
    simp only [octonionMatrixMul, Fin.sum_univ_three, matCtoO, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    fin_cases i <;>
      simp [mul_one, mul_zero, hI0, h0, octonionMul_zero_left]
  have hR : octonionMatrixMul (albertMatrix z) (matCtoO (Complex.I • (1 : ComplexMatrix3))) i j =
      octonionMul (albertMatrix z i j) octI := by
    simp only [octonionMatrixMul, Fin.sum_univ_three, matCtoO, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    fin_cases j <;>
      simp [mul_one, mul_zero, hI0, h0, octonionMul_zero_right]
  change albertMatrix (windowAdI z) i j =
    octonionMatrixMul (matCtoO (Complex.I • (1 : ComplexMatrix3))) (albertMatrix z) i j -
      octonionMatrixMul (albertMatrix z) (matCtoO (Complex.I • (1 : ComplexMatrix3))) i j
  rw [hL, hR]
  have hci : octonionConj octI = -octI := by
    apply oct_ext_local
    · rw [oct_conj_fst, oct_neg_fst, octI_fst, q_star_re, q_neg_re]; exact neg_zero.symm
    · rw [oct_conj_fst, oct_neg_fst, octI_fst, q_star_imI, q_neg_imI]
    · rw [oct_conj_fst, oct_neg_fst, octI_fst, q_star_imJ, q_neg_imJ]
    · rw [oct_conj_fst, oct_neg_fst, octI_fst, q_star_imK, q_neg_imK]
    · rw [oct_conj_snd, oct_neg_snd, octI_snd]
    · rw [oct_conj_snd, oct_neg_snd, octI_snd]
    · rw [oct_conj_snd, oct_neg_snd, octI_snd]
    · rw [oct_conj_snd, oct_neg_snd, octI_snd]
  have hconj_ad : ∀ u : Octonion, octonionConj (octAdI u) = octAdI (octonionConj u) := fun u => by
    simp only [octAdI, octonionConj_sub, octonionConj_mul, hci, octonionMul_neg_left, octonionMul_neg_right]
    abel
  have hscal_ad : ∀ r : ℝ, octAdI (octonionScalar r) = 0 := fun r => by
    simp only [octAdI, octonionMul_scalar_left, octonionMul_scalar_right, sub_self]
  fin_cases i <;> fin_cases j <;>
    dsimp only [albertMatrix, windowAdI]
  · change octonionScalar 0 = _; rw [octonionScalar_zero]; exact (hscal_ad (z.1 0)).symm
  · rfl
  · rfl
  · exact hconj_ad (z.2 0)
  · change octonionScalar 0 = _; rw [octonionScalar_zero]; exact (hscal_ad (z.1 1)).symm
  · rfl
  · exact hconj_ad (z.2 1)
  · exact hconj_ad (z.2 2)
  · change octonionScalar 0 = _; rw [octonionScalar_zero]; exact (hscal_ad (z.1 2)).symm

private theorem commutator_skew (A B : Hermitian3) :
    let q := (A : ComplexMatrix3) * (B : ComplexMatrix3) - (B : ComplexMatrix3) * (A : ComplexMatrix3)
    q.conjTranspose = -q := by
  intro q
  have hA : (A : ComplexMatrix3).conjTranspose = A := A.prop
  have hB : (B : ComplexMatrix3).conjTranspose = B := B.prop
  dsimp only [q]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB]
  abel

private theorem cube_skew {q : ComplexMatrix3} (hq : q.conjTranspose = -q) :
    (q ^ 3).conjTranspose = -(q ^ 3) := by
  rw [pow_three, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hq]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

theorem albertMatrix_jordanMul_window (A : Hermitian3) (z : Albert) :
    albertMatrix (jordanMul (standardComplexWindow.embedding A) z) =
      (1 / 2 : ℝ) •
        (octonionMatrixMul (matCtoO (A : ComplexMatrix3)) (albertMatrix z) +
          octonionMatrixMul (albertMatrix z) (matCtoO (A : ComplexMatrix3))) := by
  rw [albertMatrix_jordanMul, albertMatrix_standardComplexWindow]

theorem Dop_standardComplexWindow (A B : Hermitian3) (z : Albert) :
    Dop nativeOps (standardComplexWindow.embedding A) (standardComplexWindow.embedding B) z =
      skewComm ((A : ComplexMatrix3) * (B : ComplexMatrix3) - (B : ComplexMatrix3) * (A : ComplexMatrix3)) z := by
  let q := (A : ComplexMatrix3) * (B : ComplexMatrix3) - (B : ComplexMatrix3) * (A : ComplexMatrix3)
  have hq := commutator_skew A B
  apply albertMatrix_injective
  rw [nativeD_eq, albertMatrix_smul, albertMatrix_sub,
    albertMatrix_jordanMul_window A (jordanMul (standardComplexWindow.embedding B) z),
    albertMatrix_jordanMul_window B (jordanMul (standardComplexWindow.embedding A) z),
    albertMatrix_jordanMul_window B z, albertMatrix_jordanMul_window A z,
    albertMatrix_skewComm q hq z]
  simp only [octonionMatrixMul_smul_left, octonionMatrixMul_smul_right,
    octonionMatrixMul_add_left, octonionMatrixMul_add_right,
    octonionMatrixMul_C_C_O, octonionMatrixMul_C_O_C, octonionMatrixMul_O_C_C]
  rw [show q = (A : ComplexMatrix3) * B - B * A from rfl, matCtoO_sub,
    octonionMatrixMul_sub_left, octonionMatrixMul_sub_right]
  ext i j
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply]
  module

theorem Upol_standardComplexWindow (A B : Hermitian3) (z : Albert) :
    albertMatrix (Upol nativeOps (standardComplexWindow.embedding A)
      (standardComplexWindow.embedding B) z) =
      (1 / 2 : ℝ) •
        (octonionMatrixMul (octonionMatrixMul (matCtoO (A : ComplexMatrix3)) (albertMatrix z))
          (matCtoO (B : ComplexMatrix3)) +
         octonionMatrixMul (octonionMatrixMul (matCtoO (B : ComplexMatrix3)) (albertMatrix z))
          (matCtoO (A : ComplexMatrix3))) := by
  simp only [Upol, nativeOps]
  rw [albertMatrix_sub, albertMatrix_add,
    albertMatrix_jordanMul_window A (jordanMul (standardComplexWindow.embedding B) z),
    albertMatrix_jordanMul_window B (jordanMul (standardComplexWindow.embedding A) z),
    albertMatrix_jordanMul_window B z, albertMatrix_jordanMul_window A z,
    albertMatrix_jordanMul, albertMatrix_jordanMul,
    albertMatrix_standardComplexWindow, albertMatrix_standardComplexWindow]
  simp only [octonionMatrixMul_smul_left, octonionMatrixMul_smul_right,
    octonionMatrixMul_add_left, octonionMatrixMul_add_right,
    ← matCtoO_mul, octonionMatrixMul_C_C_O, octonionMatrixMul_C_O_C, octonionMatrixMul_O_C_C]
  ext i j
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply]
  module

theorem Ubr_standardComplexWindow (A B : Hermitian3) (z : Albert) :
    let q := (A : ComplexMatrix3) * (B : ComplexMatrix3) - (B : ComplexMatrix3) * (A : ComplexMatrix3)
    albertMatrix (Ubr nativeOps (standardComplexWindow.embedding A) (standardComplexWindow.embedding A)
      (standardComplexWindow.embedding B) (standardComplexWindow.embedding B) z) =
      octonionMatrixMul (octonionMatrixMul (matCtoO q) (albertMatrix z)) (matCtoO q) := by
  intro q
  obtain ⟨AB, hAB⟩ := standardComplexWindow.product_closed A B
  have hAB_emb : jordanMul (standardComplexWindow.embedding A) (standardComplexWindow.embedding B) =
      standardComplexWindow.embedding AB :=
    (standardComplexWindow.preserves_product A B AB hAB).symm
  rw [native_Ubr_diag, hAB_emb, ← native_Upol_self (standardComplexWindow.embedding AB) z,
    ← native_Upol_self (standardComplexWindow.embedding B) z,
    ← native_Upol_self (standardComplexWindow.embedding A) z,
    ← native_Upol_self (standardComplexWindow.embedding A)
      (Upol nativeOps (standardComplexWindow.embedding B) (standardComplexWindow.embedding B) z),
    ← native_Upol_self (standardComplexWindow.embedding B)
      (Upol nativeOps (standardComplexWindow.embedding A) (standardComplexWindow.embedding A) z)]
  rw [albertMatrix_sub, albertMatrix_smul, albertMatrix_smul, albertMatrix_add]
  simp only [Upol_standardComplexWindow]
  have hAB_mat : (AB : ComplexMatrix3) = (1 / 2 : ℝ) • ((A : ComplexMatrix3) * B + B * A) := hAB
  rw [hAB_mat, matCtoO_smul, matCtoO_add]
  simp only [octonionMatrixMul_smul_left, octonionMatrixMul_smul_right,
    octonionMatrixMul_add_left, octonionMatrixMul_add_right,
    octonionMatrixMul_C_C_O, octonionMatrixMul_C_O_C, octonionMatrixMul_O_C_C]
  have hq_def : matCtoO q = matCtoO ((A : ComplexMatrix3) * B) - matCtoO (B * A) := by
    rw [show q = (A : ComplexMatrix3) * B - B * A from rfl, matCtoO_sub]
  rw [hq_def]
  simp only [octonionMatrixMul_sub_left, octonionMatrixMul_sub_right]
  ext i j
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply]
  module

theorem DC_standardComplexWindow (A B : Hermitian3) (z : Albert) :
    let q := (A : ComplexMatrix3) * (B : ComplexMatrix3) - (B : ComplexMatrix3) * (A : ComplexMatrix3)
    DC nativeOps (standardComplexWindow.embedding A) (standardComplexWindow.embedding B) z =
      skewComm (q ^ 3) z := by
  intro q
  have hq := commutator_skew A B
  have hq3 := cube_skew hq
  apply albertMatrix_injective
  rw [native_DC_eq, albertMatrix_add, albertMatrix_smul,
    Dop_standardComplexWindow, Dop_standardComplexWindow, Dop_standardComplexWindow,
    Dop_standardComplexWindow,
    albertMatrix_skewComm q hq, albertMatrix_skewComm q hq, albertMatrix_skewComm q hq,
    albertMatrix_skewComm q hq, albertMatrix_skewComm (q ^ 3) hq3]
  have hUbr := Ubr_standardComplexWindow A B z
  dsimp only at hUbr
  change _ + (3 : ℝ) • (octonionMatrixMul (matCtoO q) (albertMatrix _) -
    octonionMatrixMul (albertMatrix _) (matCtoO q)) = _
  rw [hUbr]
  simp only [octonionMatrixMul_sub_left, octonionMatrixMul_sub_right,
    octonionMatrixMul_C_C_O, octonionMatrixMul_C_O_C, octonionMatrixMul_O_C_C]
  have hq2 : q * (q * q) = q ^ 3 := (pow_three q).symm
  ext i j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Matrix.mul_assoc, hq2]
  module

/-! ## Section 4: Polarization extractor `extractT2U2` and `sixProdComm` -/

/-- Second finite difference `f ↦ ½ (f 1 + f (-1)) - f 0`, extracting `[t²]` of a cubic. -/
def extract2 (f : ℝ → Albert) : Albert :=
  (1 / 2 : ℝ) • (f 1 + f (-1)) - f 0

/-- 9-point `(t, u) ∈ {-1, 0, 1}²` extractor matching `[s² t² u²]`. -/
def extractT2U2 (F : ℝ → ℝ → Albert) : Albert :=
  extract2 (fun t => extract2 (fun u => F t u))

private theorem extract2_cubic (c0 c1 c2 c3 : Albert) :
    extract2 (fun t => c0 + t • c1 + (t ^ 2) • c2 + (t ^ 3) • c3) = c2 := by
  simp only [extract2]
  norm_num
  module

private theorem extract2_add (f g : ℝ → Albert) :
    extract2 (fun t => f t + g t) = extract2 f + extract2 g := by
  simp only [extract2, smul_add]; abel

private theorem extract2_sub (f g : ℝ → Albert) :
    extract2 (fun t => f t - g t) = extract2 f - extract2 g := by
  simp only [extract2, smul_sub, smul_add]; abel

private theorem extract2_smul (r : ℝ) (f : ℝ → Albert) :
    extract2 (fun t => r • f t) = r • extract2 f := by
  simp only [extract2, smul_sub, smul_add, smul_comm r]

private theorem extract2_jordanMul_left (d : Albert) (f : ℝ → Albert) :
    extract2 (fun t => jordanMul d (f t)) = jordanMul d (extract2 f) := by
  simp only [extract2, jordanMul_sub_right, jordanMul_add_right, jordanMul_smul_right]

private theorem extractT2U2_sub (F G : ℝ → ℝ → Albert) :
    extractT2U2 (fun t u => F t u - G t u) = extractT2U2 F - extractT2U2 G := by
  simp only [extractT2U2, extract2_sub]

private theorem extractT2U2_smul (r : ℝ) (F : ℝ → ℝ → Albert) :
    extractT2U2 (fun t u => r • F t u) = r • extractT2U2 F := by
  simp only [extractT2U2, extract2_smul]

private theorem extractT2U2_jordanMul_left (d : Albert) (F : ℝ → ℝ → Albert) :
    extractT2U2 (fun t u => jordanMul d (F t u)) = jordanMul d (extractT2U2 F) := by
  simp only [extractT2U2, extract2_jordanMul_left]

private theorem nativeOps_add (x y : Albert) : nativeOps.add x y = x + y := rfl
private theorem nativeOps_sub (x y : Albert) : nativeOps.sub x y = x - y := rfl
private theorem nativeOps_mul (x y : Albert) : nativeOps.mul x y = jordanMul x y := rfl

-- Multilinearity of `Phi nativeOps` in `(x1, x2, x3, y1, y2, y3)`.
private theorem dop_add_left (x1 x2 y z : Albert) :
    Dop nativeOps (x1 + x2) y z = Dop nativeOps x1 y z + Dop nativeOps x2 y z := by
  simp only [nativeD_eq, jordanMul_add_left, jordanMul_add_right]; module

private theorem dop_add_mid (x y1 y2 z : Albert) :
    Dop nativeOps x (y1 + y2) z = Dop nativeOps x y1 z + Dop nativeOps x y2 z := by
  simp only [nativeD_eq, jordanMul_add_left, jordanMul_add_right]; module

private theorem dop_add_right (x y z1 z2 : Albert) :
    Dop nativeOps x y (z1 + z2) = Dop nativeOps x y z1 + Dop nativeOps x y z2 := by
  simp only [nativeD_eq, jordanMul_add_right]; module

private theorem dop_smul_left (r : ℝ) (x y z : Albert) :
    Dop nativeOps (r • x) y z = r • Dop nativeOps x y z := by
  simp only [nativeD_eq, jordanMul_smul_left, jordanMul_smul_right]; module

private theorem dop_smul_mid (r : ℝ) (x y z : Albert) :
    Dop nativeOps x (r • y) z = r • Dop nativeOps x y z := by
  simp only [nativeD_eq, jordanMul_smul_left, jordanMul_smul_right]; module

private theorem dop_smul_right (r : ℝ) (x y z : Albert) :
    Dop nativeOps x y (r • z) = r • Dop nativeOps x y z := by
  simp only [nativeD_eq, jordanMul_smul_right]; module

private theorem upol_add_left (w1 w2 w' z : Albert) :
    Upol nativeOps (w1 + w2) w' z = Upol nativeOps w1 w' z + Upol nativeOps w2 w' z := by
  simp only [Upol, nativeOps_add, nativeOps_sub, nativeOps_mul, jordanMul_add_left, jordanMul_add_right]
  abel

private theorem upol_add_mid (w w1' w2' z : Albert) :
    Upol nativeOps w (w1' + w2') z = Upol nativeOps w w1' z + Upol nativeOps w w2' z := by
  simp only [Upol, nativeOps_add, nativeOps_sub, nativeOps_mul, jordanMul_add_left, jordanMul_add_right]
  abel

private theorem upol_add_right (w w' z1 z2 : Albert) :
    Upol nativeOps w w' (z1 + z2) = Upol nativeOps w w' z1 + Upol nativeOps w w' z2 := by
  simp only [Upol, nativeOps_add, nativeOps_sub, nativeOps_mul, jordanMul_add_right]
  abel

private theorem upol_smul_left (r : ℝ) (w w' z : Albert) :
    Upol nativeOps (r • w) w' z = r • Upol nativeOps w w' z := by
  simp only [Upol, nativeOps_add, nativeOps_sub, nativeOps_mul, jordanMul_smul_left, jordanMul_smul_right]
  module

private theorem upol_smul_mid (r : ℝ) (w w' z : Albert) :
    Upol nativeOps w (r • w') z = r • Upol nativeOps w w' z := by
  simp only [Upol, nativeOps_add, nativeOps_sub, nativeOps_mul, jordanMul_smul_left, jordanMul_smul_right]
  module

private theorem upol_smul_right (r : ℝ) (w w' z : Albert) :
    Upol nativeOps w w' (r • z) = r • Upol nativeOps w w' z := by
  simp only [Upol, nativeOps_add, nativeOps_sub, nativeOps_mul, jordanMul_smul_right]
  module

private theorem ubr_add_x1 (a1 a2 x2 y1 y2 z : Albert) :
    Ubr nativeOps (a1 + a2) x2 y1 y2 z =
      Ubr nativeOps a1 x2 y1 y2 z + Ubr nativeOps a2 x2 y1 y2 z := by
  simp only [Ubr, four, two, nativeOps_add, nativeOps_sub, nativeOps_mul,
    jordanMul_add_left, upol_add_left, upol_add_right]
  module

private theorem ubr_add_x2 (x1 a1 a2 y1 y2 z : Albert) :
    Ubr nativeOps x1 (a1 + a2) y1 y2 z =
      Ubr nativeOps x1 a1 y1 y2 z + Ubr nativeOps x1 a2 y1 y2 z := by
  simp only [Ubr, four, two, nativeOps_add, nativeOps_sub, nativeOps_mul,
    jordanMul_add_left, upol_add_mid, upol_add_right]
  module

private theorem ubr_add_y1 (x1 x2 b1 b2 y2 z : Albert) :
    Ubr nativeOps x1 x2 (b1 + b2) y2 z =
      Ubr nativeOps x1 x2 b1 y2 z + Ubr nativeOps x1 x2 b2 y2 z := by
  simp only [Ubr, four, two, nativeOps_add, nativeOps_sub, nativeOps_mul,
    jordanMul_add_right, upol_add_left, upol_add_right]
  module

private theorem ubr_add_y2 (x1 x2 y1 b1 b2 z : Albert) :
    Ubr nativeOps x1 x2 y1 (b1 + b2) z =
      Ubr nativeOps x1 x2 y1 b1 z + Ubr nativeOps x1 x2 y1 b2 z := by
  simp only [Ubr, four, two, nativeOps_add, nativeOps_sub, nativeOps_mul,
    jordanMul_add_right, upol_add_mid, upol_add_right]
  module

private theorem ubr_smul_x1 (r : ℝ) (x1 x2 y1 y2 z : Albert) :
    Ubr nativeOps (r • x1) x2 y1 y2 z = r • Ubr nativeOps x1 x2 y1 y2 z := by
  simp only [Ubr, four, two, nativeOps_add, nativeOps_sub, nativeOps_mul,
    jordanMul_smul_left, upol_smul_left, upol_smul_right]
  module

private theorem ubr_smul_x2 (r : ℝ) (x1 x2 y1 y2 z : Albert) :
    Ubr nativeOps x1 (r • x2) y1 y2 z = r • Ubr nativeOps x1 x2 y1 y2 z := by
  simp only [Ubr, four, two, nativeOps_add, nativeOps_sub, nativeOps_mul,
    jordanMul_smul_left, upol_smul_mid, upol_smul_right]
  module

private theorem ubr_smul_y1 (r : ℝ) (x1 x2 y1 y2 z : Albert) :
    Ubr nativeOps x1 x2 (r • y1) y2 z = r • Ubr nativeOps x1 x2 y1 y2 z := by
  simp only [Ubr, four, two, nativeOps_add, nativeOps_sub, nativeOps_mul,
    jordanMul_smul_right, upol_smul_left, upol_smul_right]
  module

private theorem ubr_smul_y2 (r : ℝ) (x1 x2 y1 y2 z : Albert) :
    Ubr nativeOps x1 x2 y1 (r • y2) z = r • Ubr nativeOps x1 x2 y1 y2 z := by
  simp only [Ubr, four, two, nativeOps_add, nativeOps_sub, nativeOps_mul,
    jordanMul_smul_right, upol_smul_mid, upol_smul_right]
  module

private theorem phi_add_x1 (a1 a2 x2 x3 y1 y2 y3 z : Albert) :
    Phi nativeOps (a1 + a2) x2 x3 y1 y2 y3 z =
      Phi nativeOps a1 x2 x3 y1 y2 y3 z + Phi nativeOps a2 x2 x3 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_add_left]; module

private theorem phi_add_x2 (x1 a1 a2 x3 y1 y2 y3 z : Albert) :
    Phi nativeOps x1 (a1 + a2) x3 y1 y2 y3 z =
      Phi nativeOps x1 a1 x3 y1 y2 y3 z + Phi nativeOps x1 a2 x3 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_add_left, dop_add_right, ubr_add_x1]; module

private theorem phi_add_x3 (x1 x2 a1 a2 y1 y2 y3 z : Albert) :
    Phi nativeOps x1 x2 (a1 + a2) y1 y2 y3 z =
      Phi nativeOps x1 x2 a1 y1 y2 y3 z + Phi nativeOps x1 x2 a2 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_add_left, dop_add_right, ubr_add_x2]; module

private theorem phi_add_y1 (x1 x2 x3 b1 b2 y2 y3 z : Albert) :
    Phi nativeOps x1 x2 x3 (b1 + b2) y2 y3 z =
      Phi nativeOps x1 x2 x3 b1 y2 y3 z + Phi nativeOps x1 x2 x3 b2 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_add_mid]; module

private theorem phi_add_y2 (x1 x2 x3 y1 b1 b2 y3 z : Albert) :
    Phi nativeOps x1 x2 x3 y1 (b1 + b2) y3 z =
      Phi nativeOps x1 x2 x3 y1 b1 y3 z + Phi nativeOps x1 x2 x3 y1 b2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_add_mid, dop_add_right, ubr_add_y1]; module

private theorem phi_add_y3 (x1 x2 x3 y1 y2 b1 b2 z : Albert) :
    Phi nativeOps x1 x2 x3 y1 y2 (b1 + b2) z =
      Phi nativeOps x1 x2 x3 y1 y2 b1 z + Phi nativeOps x1 x2 x3 y1 y2 b2 z := by
  simp only [Phi, three, nativeOps_add, dop_add_mid, dop_add_right, ubr_add_y2]; module

private theorem phi_smul_x1 (r : ℝ) (x1 x2 x3 y1 y2 y3 z : Albert) :
    Phi nativeOps (r • x1) x2 x3 y1 y2 y3 z = r • Phi nativeOps x1 x2 x3 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_smul_left]; module

private theorem phi_smul_x2 (r : ℝ) (x1 x2 x3 y1 y2 y3 z : Albert) :
    Phi nativeOps x1 (r • x2) x3 y1 y2 y3 z = r • Phi nativeOps x1 x2 x3 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_smul_left, dop_smul_right, ubr_smul_x1]; module

private theorem phi_smul_x3 (r : ℝ) (x1 x2 x3 y1 y2 y3 z : Albert) :
    Phi nativeOps x1 x2 (r • x3) y1 y2 y3 z = r • Phi nativeOps x1 x2 x3 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_smul_left, dop_smul_right, ubr_smul_x2]; module

private theorem phi_smul_y1 (r : ℝ) (x1 x2 x3 y1 y2 y3 z : Albert) :
    Phi nativeOps x1 x2 x3 (r • y1) y2 y3 z = r • Phi nativeOps x1 x2 x3 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_smul_mid]; module

private theorem phi_smul_y2 (r : ℝ) (x1 x2 x3 y1 y2 y3 z : Albert) :
    Phi nativeOps x1 x2 x3 y1 (r • y2) y3 z = r • Phi nativeOps x1 x2 x3 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_smul_mid, dop_smul_right, ubr_smul_y1]; module

private theorem phi_smul_y3 (r : ℝ) (x1 x2 x3 y1 y2 y3 z : Albert) :
    Phi nativeOps x1 x2 x3 y1 y2 (r • y3) z = r • Phi nativeOps x1 x2 x3 y1 y2 y3 z := by
  simp only [Phi, three, nativeOps_add, dop_smul_mid, dop_smul_right, ubr_smul_y2]; module

private theorem extract2_phi_x (a b y1 y2 y3 z : Albert) :
    extract2 (fun t => Phi nativeOps (a + t • b) (a + t • b) (a + t • b) y1 y2 y3 z) =
      Phi nativeOps a b b y1 y2 y3 z + Phi nativeOps b a b y1 y2 y3 z +
        Phi nativeOps b b a y1 y2 y3 z := by
  have hpoly : ∀ t : ℝ,
      Phi nativeOps (a + t • b) (a + t • b) (a + t • b) y1 y2 y3 z =
        Phi nativeOps a a a y1 y2 y3 z +
        t • (Phi nativeOps a a b y1 y2 y3 z + Phi nativeOps a b a y1 y2 y3 z +
          Phi nativeOps b a a y1 y2 y3 z) +
        (t ^ 2) • (Phi nativeOps a b b y1 y2 y3 z + Phi nativeOps b a b y1 y2 y3 z +
          Phi nativeOps b b a y1 y2 y3 z) +
        (t ^ 3) • Phi nativeOps b b b y1 y2 y3 z := fun t => by
    simp only [phi_add_x1, phi_add_x2, phi_add_x3, phi_smul_x1, phi_smul_x2, phi_smul_x3]
    rw [pow_two, pow_three]
    simp only [mul_smul, smul_add]
    abel
  simp_rw [hpoly]
  exact extract2_cubic _ _ _ _

private theorem extract2_phi_y (x1 x2 x3 a c z : Albert) :
    extract2 (fun u => Phi nativeOps x1 x2 x3 (a + u • c) (a + u • c) (a + u • c) z) =
      Phi nativeOps x1 x2 x3 a c c z + Phi nativeOps x1 x2 x3 c a c z +
        Phi nativeOps x1 x2 x3 c c a z := by
  have hpoly : ∀ u : ℝ,
      Phi nativeOps x1 x2 x3 (a + u • c) (a + u • c) (a + u • c) z =
        Phi nativeOps x1 x2 x3 a a a z +
        u • (Phi nativeOps x1 x2 x3 a a c z + Phi nativeOps x1 x2 x3 a c a z +
          Phi nativeOps x1 x2 x3 c a a z) +
        (u ^ 2) • (Phi nativeOps x1 x2 x3 a c c z + Phi nativeOps x1 x2 x3 c a c z +
          Phi nativeOps x1 x2 x3 c c a z) +
        (u ^ 3) • Phi nativeOps x1 x2 x3 c c c z := fun u => by
    simp only [phi_add_y1, phi_add_y2, phi_add_y3, phi_smul_y1, phi_smul_y2, phi_smul_y3]
    rw [pow_two, pow_three]
    simp only [mul_smul, smul_add]
    abel
  simp_rw [hpoly]
  exact extract2_cubic _ _ _ _

theorem extractT2U2_Phi (a b c z : Albert) :
    extractT2U2 (fun t u =>
        Phi nativeOps (a + t • b) (a + t • b) (a + t • b) (a + u • c) (a + u • c) (a + u • c) z) =
      (Phi nativeOps a b b a c c z + Phi nativeOps a b b c a c z + Phi nativeOps a b b c c a z) +
      (Phi nativeOps b a b a c c z + Phi nativeOps b a b c a c z + Phi nativeOps b a b c c a z) +
      (Phi nativeOps b b a a c c z + Phi nativeOps b b a c a c z + Phi nativeOps b b a c c a z) := by
  unfold extractT2U2
  have hin : ∀ t : ℝ,
      extract2 (fun u => Phi nativeOps (a + t • b) (a + t • b) (a + t • b)
          (a + u • c) (a + u • c) (a + u • c) z) =
        Phi nativeOps (a + t • b) (a + t • b) (a + t • b) a c c z +
        Phi nativeOps (a + t • b) (a + t • b) (a + t • b) c a c z +
        Phi nativeOps (a + t • b) (a + t • b) (a + t • b) c c a z := fun t =>
    extract2_phi_y _ _ _ a c z
  simp_rw [hin, extract2_add, extract2_phi_x]
  abel

theorem extractT2U2_nativePsi (a b c z : Albert) :
    extractT2U2 (fun t u => nativePsi (a + t • b) (a + u • c) z) = nativeGlennieF a b c z := by
  have hpsi : ∀ x y, nativePsi x y z =
      Phi nativeOps x x x y y y (jordanMul z z) -
        (2 : ℝ) • jordanMul z (Phi nativeOps x x x y y y z) := fun x y => by
    rw [native_psi_eq, ← Phi_diag, ← Phi_diag]
  simp_rw [hpsi, extractT2U2_sub, extractT2U2_smul, extractT2U2_jordanMul_left, extractT2U2_Phi]
  simp only [nativeGlennieF, glennieF, glennieTerm, two, nativeOps_add, nativeOps_sub,
    nativeOps_mul, two_smul, jordanMul_add_right]
  abel

/-- Negative of the sum of all six ordered triple products of `[A, B], [A, C], [B, C]`. -/
def sixProdComm (A B C : ComplexMatrix3) : ComplexMatrix3 :=
  let qAB := A * B - B * A
  let qAC := A * C - C * A
  let qBC := B * C - C * B;
  -(qAB * qAC * qBC + qAB * qBC * qAC + qAC * qAB * qBC +
    qAC * qBC * qAB + qBC * qAB * qAC + qBC * qAC * qAB)

theorem sixProdComm_skewHermitian (A B C : Hermitian3) :
    let Y := sixProdComm (A : ComplexMatrix3) (B : ComplexMatrix3) (C : ComplexMatrix3)
    Y.conjTranspose = -Y := by
  intro Y
  have hAB := commutator_skew A B
  have hAC := commutator_skew A C
  have hBC := commutator_skew B C
  dsimp only [Y, sixProdComm]
  simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hAB, hAC, hBC, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  abel

/-- Matrix-level second finite difference extractor. -/
def extract2Mat (f : ℝ → ComplexMatrix3) : ComplexMatrix3 :=
  (1 / 2 : ℝ) • (f 1 + f (-1)) - f 0

/-- Matrix-level 9-point `(t, u) ∈ {-1, 0, 1}²` extractor. -/
def extractT2U2Mat (F : ℝ → ℝ → ComplexMatrix3) : ComplexMatrix3 :=
  extract2Mat (fun t => extract2Mat (fun u => F t u))

theorem skewComm_extract2Mat (f : ℝ → ComplexMatrix3) (z : Albert) :
    skewComm (extract2Mat f) z = extract2 (fun t => skewComm (f t) z) := by
  simp only [extract2Mat, extract2, skewComm_sub_left, skewComm_smul_left, skewComm_add_left]

theorem skewComm_extractT2U2Mat (F : ℝ → ℝ → ComplexMatrix3) (z : Albert) :
    skewComm (extractT2U2Mat F) z = extractT2U2 (fun t u => skewComm (F t u) z) := by
  unfold extractT2U2Mat extractT2U2
  rw [skewComm_extract2Mat]
  congr 1
  funext t
  exact skewComm_extract2Mat (fun u => F t u) z

private theorem matrix_cube_polarize (a b c : ComplexMatrix3) :
    (1 / 4 : ℝ) •
      ((-a + b + c) ^ 3 + (-a - b - c) ^ 3 + (a + b - c) ^ 3 + (a - b + c) ^ 3) =
      -(a * b * c + a * c * b + b * a * c + b * c * a + c * a * b + c * b * a) := by
  simp only [pow_three, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  module

theorem extractT2U2Mat_commCube (A B C : ComplexMatrix3) :
    extractT2U2Mat
        (fun t u => ((A + t • B) * (A + u • C) - (A + u • C) * (A + t • B)) ^ 3) =
      sixProdComm A B C := by
  let qAB := A * B - B * A
  let qAC := A * C - C * A
  let qBC := B * C - C * B
  have hq : ∀ t u : ℝ,
      (A + t • B) * (A + u • C) - (A + u • C) * (A + t • B) =
        (-t) • qAB + u • qAC + (t * u) • qBC := fun t u => by
    simp only [qAB, qAC, qBC, Matrix.add_mul, Matrix.mul_add, smul_mul_assoc,
      mul_smul_comm, smul_sub, smul_add, neg_smul, smul_smul]
    rw [mul_comm u t]
    abel
  have h01 : ((-0 : ℝ) • qAB + (1 : ℝ) • qAC + (0 * 1 : ℝ) • qBC) ^ 3 = qAC ^ 3 := by
    congr 1; module
  have h0m1 : ((-0 : ℝ) • qAB + (-1 : ℝ) • qAC + (0 * -1 : ℝ) • qBC) ^ 3 = (-qAC) ^ 3 := by
    congr 1; module
  have h00 : ((-0 : ℝ) • qAB + (0 : ℝ) • qAC + (0 * 0 : ℝ) • qBC) ^ 3 = 0 := by
    rw [show (-0 : ℝ) • qAB + (0 : ℝ) • qAC + (0 * 0 : ℝ) • qBC = 0 by module]
    simp
  have h10 : ((-1 : ℝ) • qAB + (0 : ℝ) • qAC + (1 * 0 : ℝ) • qBC) ^ 3 = (-qAB) ^ 3 := by
    congr 1; module
  have hm10 : ((- -1 : ℝ) • qAB + (0 : ℝ) • qAC + (-1 * 0 : ℝ) • qBC) ^ 3 = qAB ^ 3 := by
    congr 1; module
  have h11 : ((-1 : ℝ) • qAB + (1 : ℝ) • qAC + (1 * 1 : ℝ) • qBC) ^ 3 = (-qAB + qAC + qBC) ^ 3 := by
    congr 1; module
  have h1m1 : ((-1 : ℝ) • qAB + (-1 : ℝ) • qAC + (1 * -1 : ℝ) • qBC) ^ 3 = (-qAB - qAC - qBC) ^ 3 := by
    congr 1; module
  have hm11 : ((- -1 : ℝ) • qAB + (1 : ℝ) • qAC + (-1 * 1 : ℝ) • qBC) ^ 3 = (qAB + qAC - qBC) ^ 3 := by
    congr 1; module
  have hm1m1 : ((- -1 : ℝ) • qAB + (-1 : ℝ) • qAC + (-1 * -1 : ℝ) • qBC) ^ 3 = (qAB - qAC + qBC) ^ 3 := by
    congr 1; module
  simp_rw [hq]
  simp only [extractT2U2Mat, extract2Mat, h01, h0m1, h00, h10, hm10, h11, h1m1, hm11, hm1m1]
  have hneg_cube : ∀ X : ComplexMatrix3, (-X) ^ 3 = -(X ^ 3) := fun X => by
    simp only [pow_three, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [hneg_cube qAC, hneg_cube qAB]
  calc
    (1 / 2 : ℝ) • ((1 / 2 : ℝ) • ((-qAB + qAC + qBC) ^ 3 + (-qAB - qAC - qBC) ^ 3) - -(qAB ^ 3) +
        ((1 / 2 : ℝ) • ((qAB + qAC - qBC) ^ 3 + (qAB - qAC + qBC) ^ 3) - qAB ^ 3)) -
      ((1 / 2 : ℝ) • (qAC ^ 3 + -(qAC ^ 3)) - 0) =
      (1 / 4 : ℝ) • ((-qAB + qAC + qBC) ^ 3 + (-qAB - qAC - qBC) ^ 3 +
        (qAB + qAC - qBC) ^ 3 + (qAB - qAC + qBC) ^ 3) := by module
    _ = sixProdComm A B C := matrix_cube_polarize qAB qAC qBC

/-- Skew-Hermitian operator action `glennieF_of_skew Y z = [Y, z²] - 2 z ∘ [Y, z]`. -/
def glennieF_of_skew (Y : ComplexMatrix3) (z : Albert) : Albert :=
  skewComm Y (jordanMul z z) - (2 : ℝ) • jordanMul z (skewComm Y z)

theorem glennieF_of_skew_add_left (Y₁ Y₂ : ComplexMatrix3) (z : Albert) :
    glennieF_of_skew (Y₁ + Y₂) z = glennieF_of_skew Y₁ z + glennieF_of_skew Y₂ z := by
  simp only [glennieF_of_skew, skewComm_add_left, jordanMul_add_right, smul_add]
  abel

theorem glennieF_of_skew_smul_left (r : ℝ) (Y : ComplexMatrix3) (z : Albert) :
    glennieF_of_skew (r • Y) z = r • glennieF_of_skew Y z := by
  simp only [glennieF_of_skew, skewComm_smul_left, jordanMul_smul_right, smul_sub, smul_comm r]

theorem nativeGlennieF_standardComplexWindow (A B C : Hermitian3) (z : Albert) :
    nativeGlennieF (standardComplexWindow.embedding A) (standardComplexWindow.embedding B)
        (standardComplexWindow.embedding C) z =
      glennieF_of_skew
        (sixProdComm (A : ComplexMatrix3) (B : ComplexMatrix3) (C : ComplexMatrix3)) z := by
  rw [← extractT2U2_nativePsi]
  have hterm : ∀ t u : ℝ,
      nativePsi (standardComplexWindow.embedding A + t • standardComplexWindow.embedding B)
          (standardComplexWindow.embedding A + u • standardComplexWindow.embedding C) z =
        glennieF_of_skew
          ((((A : ComplexMatrix3) + t • (B : ComplexMatrix3)) *
              ((A : ComplexMatrix3) + u • (C : ComplexMatrix3)) -
            ((A : ComplexMatrix3) + u • (C : ComplexMatrix3)) *
              ((A : ComplexMatrix3) + t • (B : ComplexMatrix3))) ^ 3)
          z := fun t u => by
    rw [← map_smul, ← map_add, ← map_smul, ← map_add]
    rw [native_psi_eq, DC_standardComplexWindow, DC_standardComplexWindow]
    rfl
  simp_rw [hterm]
  unfold glennieF_of_skew
  rw [extractT2U2_sub, extractT2U2_smul, extractT2U2_jordanMul_left,
    ← skewComm_extractT2U2Mat, ← skewComm_extractT2U2Mat, extractT2U2Mat_commCube]

/-! ## Section 5: `su(3)` decomposition, Jordan derivation property, and `4 λ Def` -/

/-- `λ(Y) = (1/3) Re(Tr(Y) / i)` for a skew-Hermitian `3 × 3` complex matrix `Y`. -/
def windowMatrixLambda (Y : ComplexMatrix3) : ℝ :=
  (1 / 3 : ℝ) * (Matrix.trace Y / Complex.I).re

/-- `λ(A, B, C) = windowMatrixLambda (sixProdComm A B C)`. -/
def windowLambda (A B C : ComplexMatrix3) : ℝ :=
  windowMatrixLambda (sixProdComm A B C)

theorem skew_diag_re_eq_zero {Y : ComplexMatrix3} (hY : Y.conjTranspose = -Y) (i : Fin 3) :
    (Y i i).re = 0 := by
  have h := congrArg Complex.re (congrFun (congrFun hY i) i)
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def,
    Complex.conj_re, Complex.neg_re] at h
  linarith

theorem trace_skew_re_eq_zero {Y : ComplexMatrix3} (hY : Y.conjTranspose = -Y) :
    (Matrix.trace Y).re = 0 := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three, Complex.add_re,
    skew_diag_re_eq_zero hY]
  norm_num

theorem trace_skew_eq_three_I_lambda {Y : ComplexMatrix3} (hY : Y.conjTranspose = -Y) :
    Matrix.trace Y = (3 : ℂ) * Complex.I * (windowMatrixLambda Y : ℂ) := by
  have hre := trace_skew_re_eq_zero hY
  unfold windowMatrixLambda
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, hre]
  · simp [Complex.mul_re, Complex.mul_im, Complex.div_I, hre]

theorem skew_split_trace_zero {Y : ComplexMatrix3} (hY : Y.conjTranspose = -Y) :
    let Y₀ := Y - windowMatrixLambda Y • (Complex.I • (1 : ComplexMatrix3))
    Y₀.conjTranspose = -Y₀ ∧ Y₀.trace = 0 := by
  intro Y₀
  have hI : (Complex.I • (1 : ComplexMatrix3)).conjTranspose = -(Complex.I • (1 : ComplexMatrix3)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
  constructor
  · dsimp only [Y₀]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hY, hI, star_trivial]
    simp only [smul_neg, sub_neg_eq_add, neg_sub]
    abel
  · dsimp only [Y₀]
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
    simp only [Complex.real_smul, smul_eq_mul, Fintype.card_fin, Nat.cast_ofNat]
    rw [trace_skew_eq_three_I_lambda hY]
    ring

-- Associator symmetries with one argument in `ℂ_i` (for the derivation law).
private theorem octAssoc_C_left_symm (a : ℂ) (u v : Octonion) :
    octAssociator (complexToOctonion a) u v = -octAssociator (complexToOctonion a) v u := by
  rw [octAssociator, octAssociator]
  apply Prod.ext
  · rw [oct_neg_fst, oct_sub_fst, oct_sub_fst]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring
  · rw [oct_neg_snd, oct_sub_snd, oct_sub_snd]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring

private theorem octAssoc_C_mid (a : ℂ) (u v : Octonion) :
    octAssociator u (complexToOctonion a) v = -octAssociator (complexToOctonion a) u v := by
  rw [octAssociator, octAssociator]
  apply Prod.ext
  · rw [oct_neg_fst, oct_sub_fst, oct_sub_fst]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring
  · rw [oct_neg_snd, oct_sub_snd, oct_sub_snd]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring

private theorem octAssoc_C_right (a : ℂ) (u v : Octonion) :
    octAssociator u v (complexToOctonion a) = octAssociator (complexToOctonion a) u v := by
  rw [octAssociator, octAssociator]
  apply Prod.ext
  · rw [oct_sub_fst, oct_sub_fst]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring
  · rw [oct_sub_snd, oct_sub_snd]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring

private theorem octAssoc_C_conj_mid (a : ℂ) (u v : Octonion) :
    octAssociator (complexToOctonion a) (octonionConj u) v =
      -octAssociator (complexToOctonion a) u v := by
  rw [octAssociator, octAssociator]
  apply Prod.ext
  · rw [oct_neg_fst, oct_sub_fst, oct_sub_fst]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, octonionConj,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring
  · rw [oct_neg_snd, oct_sub_snd, oct_sub_snd]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, octonionConj,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring

private theorem octAssoc_C_conj_right (a : ℂ) (u v : Octonion) :
    octAssociator (complexToOctonion a) u (octonionConj v) =
      -octAssociator (complexToOctonion a) u v := by
  rw [octAssociator, octAssociator]
  apply Prod.ext
  · rw [oct_neg_fst, oct_sub_fst, oct_sub_fst]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, octonionConj,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring
  · rw [oct_neg_snd, oct_sub_snd, oct_sub_snd]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, octonionConj,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring

private theorem octAssoc_C_star (a : ℂ) (u v : Octonion) :
    octAssociator (complexToOctonion (star a)) u v =
      -octAssociator (complexToOctonion a) u v := by
  rw [octAssociator, octAssociator]
  apply Prod.ext
  · rw [oct_neg_fst, oct_sub_fst, oct_sub_fst]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, Complex.star_def,
        Complex.conj_re, Complex.conj_im,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring
  · rw [oct_neg_snd, oct_sub_snd, oct_sub_snd]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, Complex.star_def,
        Complex.conj_re, Complex.conj_im,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_neg_re, q_neg_imI, q_neg_imJ, q_neg_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring

private theorem octAssoc_C_scalar_mid (a : ℂ) (r : ℝ) (v : Octonion) :
    octAssociator (complexToOctonion a) (octonionScalar r) v = 0 := by
  rw [octAssociator]
  apply Prod.ext
  · rw [oct_sub_fst, oct_zero_fst]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, octonionScalar,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring
  · rw [oct_sub_snd, oct_zero_snd]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, octonionScalar,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring

private theorem octAssoc_C_scalar_right (a : ℂ) (u : Octonion) (r : ℝ) :
    octAssociator (complexToOctonion a) u (octonionScalar r) = 0 := by
  rw [octAssociator]
  apply Prod.ext
  · rw [oct_sub_fst, oct_zero_fst]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, octonionScalar,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring
  · rw [oct_sub_snd, oct_zero_snd]
    apply Quaternion.ext <;>
      simp only [complexToOctonion_apply, octonionMul, octonionScalar,
        q_add_re, q_add_imI, q_add_imJ, q_add_imK,
        q_sub_re, q_sub_imI, q_sub_imJ, q_sub_imK,
        q_mul_re, q_mul_imI, q_mul_imJ, q_mul_imK,
        q_star_re, q_star_imI, q_star_imJ, q_star_imK,
        q_zero_re, q_zero_imI, q_zero_imJ, q_zero_imK] <;>
      ring

private theorem octAssoc_C_add_left (a b : ℂ) (u v : Octonion) :
    octAssociator (complexToOctonion (a + b)) u v =
      octAssociator (complexToOctonion a) u v + octAssociator (complexToOctonion b) u v := by
  simp only [octAssociator, map_add, octonionMul_add_left]; abel

private theorem octAssoc_C_zero_left (u v : Octonion) :
    octAssociator (complexToOctonion 0) u v = 0 := by
  simp only [octAssociator, map_zero, octonionMul_zero_left, sub_zero]

private theorem octAssoc_entry_decomp (Q : ComplexMatrix3) (X Y : Fin 3 → Fin 3 → Octonion) (a b : Fin 3) :
    (octonionMatrixMul (matCtoO Q) (octonionMatrixMul X Y) a b -
      octonionMatrixMul (octonionMatrixMul X Y) (matCtoO Q) a b) -
    ((octonionMatrixMul (octonionMatrixMul (matCtoO Q) X - octonionMatrixMul X (matCtoO Q)) Y a b) +
      (octonionMatrixMul X (octonionMatrixMul (matCtoO Q) Y - octonionMatrixMul Y (matCtoO Q)) a b)) =
    ∑ k : Fin 3, ∑ l : Fin 3,
      (-octAssociator (matCtoO Q a k) (X k l) (Y l b) -
        octAssociator (X a k) (Y k l) (matCtoO Q l b) +
        octAssociator (X a k) (matCtoO Q k l) (Y l b)) := by
  simp only [octonionMatrixMul, Pi.sub_apply, octonionMul_sub_left, octonionMul_sub_right,
    octonionMul_sum_left, octonionMul_sum_right, Finset.sum_sub_distrib, octAssociator]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun l k => octonionMul (octonionMul (X a k) (Y k l)) (matCtoO Q l b))]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun l k => octonionMul (octonionMul (matCtoO Q a k) (X k l)) (Y l b))]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun l k => octonionMul (octonionMul (X a k) (matCtoO Q k l)) (Y l b))]
  simp only [Finset.sum_add_distrib, sub_eq_add_neg, neg_add,
    ← Finset.sum_neg_distrib, neg_neg]
  abel

private theorem octAssoc_jordan_off_01 (Q : ComplexMatrix3)
    (hQ : Q.conjTranspose = -Q) (hTr : Q.trace = 0) (z1 z2 : Albert) :
    let Z1 := albertMatrix z1
    let Z2 := albertMatrix z2
    let err := fun X Y : Fin 3 → Fin 3 → Octonion =>
      (octonionMatrixMul (matCtoO Q) (octonionMatrixMul X Y) 0 1 -
        octonionMatrixMul (octonionMatrixMul X Y) (matCtoO Q) 0 1) -
      ((octonionMatrixMul (octonionMatrixMul (matCtoO Q) X - octonionMatrixMul X (matCtoO Q)) Y 0 1) +
        (octonionMatrixMul X (octonionMatrixMul (matCtoO Q) Y - octonionMatrixMul Y (matCtoO Q)) 0 1))
    err Z1 Z2 + err Z2 Z1 = 0 := by
  intro Z1 Z2 err
  have hs10 : Q 1 0 = -star (Q 0 1) := by
    have h := congrFun (congrFun hQ 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hs20 : Q 2 0 = -star (Q 0 2) := by
    have h := congrFun (congrFun hQ 2) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hs21 : Q 2 1 = -star (Q 1 2) := by
    have h := congrFun (congrFun hQ 2) 1
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have htr : Q 0 0 + Q 1 1 + Q 2 2 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_three] using hTr
  have hneg : ∀ a : ℂ, ∀ u v : Octonion,
      octAssociator (complexToOctonion (-a)) u v = -octAssociator (complexToOctonion a) u v := by
    intro a u v
    have h0 := octAssoc_C_add_left a (-a) u v
    rw [add_neg_cancel, octAssoc_C_zero_left] at h0
    exact eq_neg_of_add_eq_zero_right h0.symm
  have hsum : ∀ X Y : Albert,
      err (albertMatrix X) (albertMatrix Y) =
        -octAssociator (complexToOctonion (Q 0 0)) (X.2 1) (octonionConj (Y.2 2))
        -octAssociator (complexToOctonion (Q 0 1)) (octonionConj (X.2 0)) (Y.2 0)
        -octAssociator (complexToOctonion (Q 0 1)) (X.2 2) (octonionConj (Y.2 2))
        -octAssociator (complexToOctonion (Q 0 2)) (octonionConj (X.2 1)) (Y.2 0)
        -octAssociator (X.2 0) (octonionConj (Y.2 0)) (complexToOctonion (Q 0 1))
        -octAssociator (X.2 0) (Y.2 2) (complexToOctonion (Q 2 1))
        -octAssociator (X.2 1) (octonionConj (Y.2 1)) (complexToOctonion (Q 0 1))
        -octAssociator (X.2 1) (octonionConj (Y.2 2)) (complexToOctonion (Q 1 1))
        +octAssociator (X.2 0) (complexToOctonion (Q 1 0)) (Y.2 0)
        +octAssociator (X.2 0) (complexToOctonion (Q 1 2)) (octonionConj (Y.2 2))
        +octAssociator (X.2 1) (complexToOctonion (Q 2 0)) (Y.2 0)
        +octAssociator (X.2 1) (complexToOctonion (Q 2 2)) (octonionConj (Y.2 2)) := by
    intro X Y
    dsimp only [err]
    rw [octAssoc_entry_decomp, Fin.sum_univ_three, Fin.sum_univ_three,
      Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [albertMatrix, matCtoO, Fin.val_zero, Fin.val_one, Fin.val_two,
      octAssoc_C_scalar_mid, octAssoc_C_scalar_right,
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator (octonionScalar r) (complexToOctonion c) u = 0 from
        fun c r u => by rw [octAssoc_C_mid, octAssoc_C_scalar_mid, neg_zero],
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator (octonionScalar r) u (complexToOctonion c) = 0 from
        fun c r u => by rw [octAssoc_C_right, octAssoc_C_scalar_mid],
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator u (octonionScalar r) (complexToOctonion c) = 0 from
        fun c r u => by rw [octAssoc_C_right, octAssoc_C_scalar_right],
      show ∀ u : Octonion, ∀ c : ℂ, ∀ r : ℝ, octAssociator u (complexToOctonion c) (octonionScalar r) = 0 from
        fun u c r => by rw [octAssoc_C_mid, octAssoc_C_scalar_right, neg_zero],
      sub_zero, add_zero, zero_add, neg_zero, zero_sub]
    abel
  have hsimp : ∀ X Y : Albert,
      err (albertMatrix X) (albertMatrix Y) =
        octAssociator (complexToOctonion (Q 0 1)) (X.2 0) (Y.2 0) +
        octAssociator (complexToOctonion (Q 0 1)) (X.2 1) (Y.2 1) +
        octAssociator (complexToOctonion (Q 0 1)) (X.2 2) (Y.2 2) := by
    intro X Y
    rw [hsum X Y]
    simp only [hs10, hs20, hs21, hneg, octAssoc_C_mid, octAssoc_C_right,
      octAssoc_C_conj_mid, octAssoc_C_conj_right, octAssoc_C_star]
    have htr0 : octAssociator (complexToOctonion (Q 0 0)) (X.2 1) (Y.2 2) +
        octAssociator (complexToOctonion (Q 1 1)) (X.2 1) (Y.2 2) +
        octAssociator (complexToOctonion (Q 2 2)) (X.2 1) (Y.2 2) = 0 := by
      rw [← octAssoc_C_add_left, ← octAssoc_C_add_left, htr, octAssoc_C_zero_left]
    calc
      _ = (octAssociator (complexToOctonion (Q 0 0)) (X.2 1) (Y.2 2) +
            octAssociator (complexToOctonion (Q 1 1)) (X.2 1) (Y.2 2) +
            octAssociator (complexToOctonion (Q 2 2)) (X.2 1) (Y.2 2)) +
          (octAssociator (complexToOctonion (Q 0 1)) (X.2 0) (Y.2 0) +
            octAssociator (complexToOctonion (Q 0 1)) (X.2 1) (Y.2 1) +
            octAssociator (complexToOctonion (Q 0 1)) (X.2 2) (Y.2 2)) := by
            abel
      _ = _ := by rw [htr0, zero_add]
  rw [hsimp z1 z2, hsimp z2 z1]
  rw [octAssoc_C_left_symm (Q 0 1) (z2.2 0) (z1.2 0),
    octAssoc_C_left_symm (Q 0 1) (z2.2 1) (z1.2 1),
    octAssoc_C_left_symm (Q 0 1) (z2.2 2) (z1.2 2)]
  abel

private theorem octAssoc_jordan_off_02 (Q : ComplexMatrix3)
    (hQ : Q.conjTranspose = -Q) (hTr : Q.trace = 0) (z1 z2 : Albert) :
    let Z1 := albertMatrix z1
    let Z2 := albertMatrix z2
    let err := fun X Y : Fin 3 → Fin 3 → Octonion =>
      (octonionMatrixMul (matCtoO Q) (octonionMatrixMul X Y) 0 2 -
        octonionMatrixMul (octonionMatrixMul X Y) (matCtoO Q) 0 2) -
      ((octonionMatrixMul (octonionMatrixMul (matCtoO Q) X - octonionMatrixMul X (matCtoO Q)) Y 0 2) +
        (octonionMatrixMul X (octonionMatrixMul (matCtoO Q) Y - octonionMatrixMul Y (matCtoO Q)) 0 2))
    err Z1 Z2 + err Z2 Z1 = 0 := by
  intro Z1 Z2 err
  have hs10 : Q 1 0 = -star (Q 0 1) := by
    have h := congrFun (congrFun hQ 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hs20 : Q 2 0 = -star (Q 0 2) := by
    have h := congrFun (congrFun hQ 2) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hs21 : Q 2 1 = -star (Q 1 2) := by
    have h := congrFun (congrFun hQ 2) 1
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have htr : Q 0 0 + Q 1 1 + Q 2 2 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_three] using hTr
  have hneg : ∀ a : ℂ, ∀ u v : Octonion,
      octAssociator (complexToOctonion (-a)) u v = -octAssociator (complexToOctonion a) u v := by
    intro a u v
    have h0 := octAssoc_C_add_left a (-a) u v
    rw [add_neg_cancel, octAssoc_C_zero_left] at h0
    exact eq_neg_of_add_eq_zero_right h0.symm
  have hsum : ∀ X Y : Albert,
      err (albertMatrix X) (albertMatrix Y) =
        -octAssociator (complexToOctonion (Q 0 0)) (X.2 0) (Y.2 2)
        -octAssociator (complexToOctonion (Q 0 1)) (octonionConj (X.2 0)) (Y.2 1)
        -octAssociator (complexToOctonion (Q 0 2)) (octonionConj (X.2 1)) (Y.2 1)
        -octAssociator (complexToOctonion (Q 0 2)) (octonionConj (X.2 2)) (Y.2 2)
        -octAssociator (X.2 0) (octonionConj (Y.2 0)) (complexToOctonion (Q 0 2))
        -octAssociator (X.2 0) (Y.2 2) (complexToOctonion (Q 2 2))
        -octAssociator (X.2 1) (octonionConj (Y.2 1)) (complexToOctonion (Q 0 2))
        -octAssociator (X.2 1) (octonionConj (Y.2 2)) (complexToOctonion (Q 1 2))
        +octAssociator (X.2 0) (complexToOctonion (Q 1 0)) (Y.2 1)
        +octAssociator (X.2 0) (complexToOctonion (Q 1 1)) (Y.2 2)
        +octAssociator (X.2 1) (complexToOctonion (Q 2 0)) (Y.2 1)
        +octAssociator (X.2 1) (complexToOctonion (Q 2 1)) (Y.2 2) := by
    intro X Y
    dsimp only [err]
    rw [octAssoc_entry_decomp, Fin.sum_univ_three, Fin.sum_univ_three,
      Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [albertMatrix, matCtoO, Fin.val_zero, Fin.val_one, Fin.val_two,
      octAssoc_C_scalar_mid, octAssoc_C_scalar_right,
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator (octonionScalar r) (complexToOctonion c) u = 0 from
        fun c r u => by rw [octAssoc_C_mid, octAssoc_C_scalar_mid, neg_zero],
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator (octonionScalar r) u (complexToOctonion c) = 0 from
        fun c r u => by rw [octAssoc_C_right, octAssoc_C_scalar_mid],
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator u (octonionScalar r) (complexToOctonion c) = 0 from
        fun c r u => by rw [octAssoc_C_right, octAssoc_C_scalar_right],
      show ∀ u : Octonion, ∀ c : ℂ, ∀ r : ℝ, octAssociator u (complexToOctonion c) (octonionScalar r) = 0 from
        fun u c r => by rw [octAssoc_C_mid, octAssoc_C_scalar_right, neg_zero],
      sub_zero, add_zero, zero_add, neg_zero, zero_sub]
    abel
  have hsimp : ∀ X Y : Albert,
      err (albertMatrix X) (albertMatrix Y) =
        octAssociator (complexToOctonion (Q 0 2)) (X.2 0) (Y.2 0) +
        octAssociator (complexToOctonion (Q 0 2)) (X.2 1) (Y.2 1) +
        octAssociator (complexToOctonion (Q 0 2)) (X.2 2) (Y.2 2) := by
    intro X Y
    rw [hsum X Y]
    simp only [hs10, hs20, hs21, hneg, octAssoc_C_mid, octAssoc_C_right,
      octAssoc_C_conj_mid, octAssoc_C_conj_right, octAssoc_C_star]
    have htr0 : octAssociator (complexToOctonion (Q 0 0)) (X.2 0) (Y.2 2) +
        octAssociator (complexToOctonion (Q 1 1)) (X.2 0) (Y.2 2) +
        octAssociator (complexToOctonion (Q 2 2)) (X.2 0) (Y.2 2) = 0 := by
      rw [← octAssoc_C_add_left, ← octAssoc_C_add_left, htr, octAssoc_C_zero_left]
    calc
      _ = -(octAssociator (complexToOctonion (Q 0 0)) (X.2 0) (Y.2 2) +
            octAssociator (complexToOctonion (Q 1 1)) (X.2 0) (Y.2 2) +
            octAssociator (complexToOctonion (Q 2 2)) (X.2 0) (Y.2 2)) +
          (octAssociator (complexToOctonion (Q 0 2)) (X.2 0) (Y.2 0) +
            octAssociator (complexToOctonion (Q 0 2)) (X.2 1) (Y.2 1) +
            octAssociator (complexToOctonion (Q 0 2)) (X.2 2) (Y.2 2)) := by
            abel
      _ = _ := by rw [htr0, neg_zero, zero_add]
  rw [hsimp z1 z2, hsimp z2 z1]
  rw [octAssoc_C_left_symm (Q 0 2) (z2.2 0) (z1.2 0),
    octAssoc_C_left_symm (Q 0 2) (z2.2 1) (z1.2 1),
    octAssoc_C_left_symm (Q 0 2) (z2.2 2) (z1.2 2)]
  abel

private theorem octAssoc_jordan_off_12 (Q : ComplexMatrix3)
    (hQ : Q.conjTranspose = -Q) (hTr : Q.trace = 0) (z1 z2 : Albert) :
    let Z1 := albertMatrix z1
    let Z2 := albertMatrix z2
    let err := fun X Y : Fin 3 → Fin 3 → Octonion =>
      (octonionMatrixMul (matCtoO Q) (octonionMatrixMul X Y) 1 2 -
        octonionMatrixMul (octonionMatrixMul X Y) (matCtoO Q) 1 2) -
      ((octonionMatrixMul (octonionMatrixMul (matCtoO Q) X - octonionMatrixMul X (matCtoO Q)) Y 1 2) +
        (octonionMatrixMul X (octonionMatrixMul (matCtoO Q) Y - octonionMatrixMul Y (matCtoO Q)) 1 2))
    err Z1 Z2 + err Z2 Z1 = 0 := by
  intro Z1 Z2 err
  have hs10 : Q 1 0 = -star (Q 0 1) := by
    have h := congrFun (congrFun hQ 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hs20 : Q 2 0 = -star (Q 0 2) := by
    have h := congrFun (congrFun hQ 2) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hs21 : Q 2 1 = -star (Q 1 2) := by
    have h := congrFun (congrFun hQ 2) 1
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have htr : Q 0 0 + Q 1 1 + Q 2 2 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_three] using hTr
  have hneg : ∀ a : ℂ, ∀ u v : Octonion,
      octAssociator (complexToOctonion (-a)) u v = -octAssociator (complexToOctonion a) u v := by
    intro a u v
    have h0 := octAssoc_C_add_left a (-a) u v
    rw [add_neg_cancel, octAssoc_C_zero_left] at h0
    exact eq_neg_of_add_eq_zero_right h0.symm
  have hsum : ∀ X Y : Albert,
      err (albertMatrix X) (albertMatrix Y) =
        -octAssociator (complexToOctonion (Q 1 0)) (X.2 0) (Y.2 2)
        -octAssociator (complexToOctonion (Q 1 1)) (octonionConj (X.2 0)) (Y.2 1)
        -octAssociator (complexToOctonion (Q 1 2)) (octonionConj (X.2 1)) (Y.2 1)
        -octAssociator (complexToOctonion (Q 1 2)) (octonionConj (X.2 2)) (Y.2 2)
        -octAssociator (octonionConj (X.2 0)) (Y.2 0) (complexToOctonion (Q 1 2))
        -octAssociator (octonionConj (X.2 0)) (Y.2 1) (complexToOctonion (Q 2 2))
        -octAssociator (X.2 2) (octonionConj (Y.2 1)) (complexToOctonion (Q 0 2))
        -octAssociator (X.2 2) (octonionConj (Y.2 2)) (complexToOctonion (Q 1 2))
        +octAssociator (octonionConj (X.2 0)) (complexToOctonion (Q 0 0)) (Y.2 1)
        +octAssociator (octonionConj (X.2 0)) (complexToOctonion (Q 0 1)) (Y.2 2)
        +octAssociator (X.2 2) (complexToOctonion (Q 2 0)) (Y.2 1)
        +octAssociator (X.2 2) (complexToOctonion (Q 2 1)) (Y.2 2) := by
    intro X Y
    dsimp only [err]
    rw [octAssoc_entry_decomp, Fin.sum_univ_three, Fin.sum_univ_three,
      Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [albertMatrix, matCtoO, Fin.val_zero, Fin.val_one, Fin.val_two,
      octAssoc_C_scalar_mid, octAssoc_C_scalar_right,
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator (octonionScalar r) (complexToOctonion c) u = 0 from
        fun c r u => by rw [octAssoc_C_mid, octAssoc_C_scalar_mid, neg_zero],
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator (octonionScalar r) u (complexToOctonion c) = 0 from
        fun c r u => by rw [octAssoc_C_right, octAssoc_C_scalar_mid],
      show ∀ c : ℂ, ∀ r : ℝ, ∀ u : Octonion, octAssociator u (octonionScalar r) (complexToOctonion c) = 0 from
        fun c r u => by rw [octAssoc_C_right, octAssoc_C_scalar_right],
      show ∀ u : Octonion, ∀ c : ℂ, ∀ r : ℝ, octAssociator u (complexToOctonion c) (octonionScalar r) = 0 from
        fun u c r => by rw [octAssoc_C_mid, octAssoc_C_scalar_right, neg_zero],
      sub_zero, add_zero, zero_add, neg_zero, zero_sub]
    abel
  have hsimp : ∀ X Y : Albert,
      err (albertMatrix X) (albertMatrix Y) =
        octAssociator (complexToOctonion (Q 1 2)) (X.2 0) (Y.2 0) +
        octAssociator (complexToOctonion (Q 1 2)) (X.2 1) (Y.2 1) +
        octAssociator (complexToOctonion (Q 1 2)) (X.2 2) (Y.2 2) := by
    intro X Y
    rw [hsum X Y]
    simp only [hs10, hs20, hs21, hneg, octAssoc_C_mid, octAssoc_C_right,
      octAssoc_C_conj_mid, octAssoc_C_conj_right, octAssoc_C_star]
    have htr0 : octAssociator (complexToOctonion (Q 0 0)) (X.2 0) (Y.2 1) +
        octAssociator (complexToOctonion (Q 1 1)) (X.2 0) (Y.2 1) +
        octAssociator (complexToOctonion (Q 2 2)) (X.2 0) (Y.2 1) = 0 := by
      rw [← octAssoc_C_add_left, ← octAssoc_C_add_left, htr, octAssoc_C_zero_left]
    calc
      _ = (octAssociator (complexToOctonion (Q 0 0)) (X.2 0) (Y.2 1) +
            octAssociator (complexToOctonion (Q 1 1)) (X.2 0) (Y.2 1) +
            octAssociator (complexToOctonion (Q 2 2)) (X.2 0) (Y.2 1)) +
          (octAssociator (complexToOctonion (Q 1 2)) (X.2 0) (Y.2 0) +
            octAssociator (complexToOctonion (Q 1 2)) (X.2 1) (Y.2 1) +
            octAssociator (complexToOctonion (Q 1 2)) (X.2 2) (Y.2 2)) := by
            abel
      _ = _ := by rw [htr0, zero_add]
  rw [hsimp z1 z2, hsimp z2 z1]
  rw [octAssoc_C_left_symm (Q 1 2) (z2.2 0) (z1.2 0),
    octAssoc_C_left_symm (Q 1 2) (z2.2 1) (z1.2 1),
    octAssoc_C_left_symm (Q 1 2) (z2.2 2) (z1.2 2)]
  abel

private theorem octonionReal_sum {ι : Type*} (s : Finset ι) (f : ι → Octonion) :
    octonionReal (∑ i ∈ s, f i) = ∑ i ∈ s, octonionReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, octonionReal_add, ih]

/-- Every trace-zero skew-Hermitian `Q ∈ su(3)` acts as a Jordan derivation of `jordanMul`. -/
theorem skewComm_isDerivation (Q : ComplexMatrix3) (hQ : Q.conjTranspose = -Q)
    (hTr : Q.trace = 0) (z1 z2 : Albert) :
    skewComm Q (jordanMul z1 z2) =
      jordanMul (skewComm Q z1) z2 + jordanMul z1 (skewComm Q z2) := by
  apply albertMatrix_injective
  rw [albertMatrix_add, albertMatrix_skewComm Q hQ]
  have hd_eq : ∀ (X Y : Fin 3 → Fin 3 → Octonion), IsOctHermitian X → IsOctHermitian Y →
      (∀ i, octonionReal (X i i) = octonionReal (Y i i)) →
      X 0 1 = Y 0 1 → X 0 2 = Y 0 2 → X 1 2 = Y 1 2 → X = Y := by
    intro X Y hX hY hd h01 h02 h12
    rw [← albertMatrix_albertCoordinates_of_isOctHermitian hX,
      ← albertMatrix_albertCoordinates_of_isOctHermitian hY]
    congr 1
    exact albert_ext_local (hd 0) (hd 1) (hd 2) h01 h02 h12
  refine hd_eq _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← albertMatrix_skewComm Q hQ]
    exact octMatConjTranspose_albertMatrix _
  · rw [← albertMatrix_add]
    exact octMatConjTranspose_albertMatrix _
  · intro i
    have hre_assoc : ∀ A B C : Fin 3 → Fin 3 → Octonion,
        octonionReal (octonionMatrixMul A (octonionMatrixMul B C) i i) =
          octonionReal (octonionMatrixMul (octonionMatrixMul A B) C i i) := fun A B C => by
      simp only [octonionMatrixMul, octonionMul_sum_left, octonionMul_sum_right, octonionReal_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
        (octonionReal_mul_associative _ _ _).symm
    rw [albertMatrix_jordanMul z1 z2, albertMatrix_jordanMul (skewComm Q z1) z2,
      albertMatrix_jordanMul z1 (skewComm Q z2),
      albertMatrix_skewComm Q hQ z1, albertMatrix_skewComm Q hQ z2]
    simp only [octonionMatrixMul_smul_left, octonionMatrixMul_smul_right,
      octonionMatrixMul_add_left, octonionMatrixMul_add_right,
      octonionMatrixMul_sub_left, octonionMatrixMul_sub_right,
      Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
      octonionReal_smul, octonionReal_sub, octonionReal_add]
    rw [hre_assoc (matCtoO Q) (albertMatrix z1) (albertMatrix z2),
      hre_assoc (matCtoO Q) (albertMatrix z2) (albertMatrix z1),
      hre_assoc (albertMatrix z2) (matCtoO Q) (albertMatrix z1),
      hre_assoc (albertMatrix z2) (albertMatrix z1) (matCtoO Q),
      hre_assoc (albertMatrix z1) (matCtoO Q) (albertMatrix z2),
      hre_assoc (albertMatrix z1) (albertMatrix z2) (matCtoO Q)]
    ring
  · have h01 := octAssoc_jordan_off_01 Q hQ hTr z1 z2
    rw [albertMatrix_jordanMul z1 z2, albertMatrix_jordanMul (skewComm Q z1) z2,
      albertMatrix_jordanMul z1 (skewComm Q z2),
      albertMatrix_skewComm Q hQ z1, albertMatrix_skewComm Q hQ z2]
    simp only [octonionMatrixMul_smul_left, octonionMatrixMul_smul_right,
      octonionMatrixMul_add_left, octonionMatrixMul_add_right,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    apply sub_eq_zero.mp
    rw [show (1 / 2 : ℝ) •
          (octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) 0 1 +
            octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) 0 1) -
        (1 / 2 : ℝ) •
          (octonionMatrixMul (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) (matCtoO Q) 0 1 +
            octonionMatrixMul (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) (matCtoO Q) 0 1) -
        ((1 / 2 : ℝ) •
          (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) (albertMatrix z2) 0 1 +
            octonionMatrixMul (albertMatrix z2) (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) 0 1) +
         (1 / 2 : ℝ) •
          (octonionMatrixMul (albertMatrix z1) (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) 0 1 +
            octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) (albertMatrix z1) 0 1)) =
        (1 / 2 : ℝ) •
          (((octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) 0 1 -
              octonionMatrixMul (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) (matCtoO Q) 0 1) -
            (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) (albertMatrix z2) 0 1 +
            octonionMatrixMul (albertMatrix z1) (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) 0 1)) +
          ((octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) 0 1 -
              octonionMatrixMul (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) (matCtoO Q) 0 1) -
            (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) (albertMatrix z1) 0 1 +
            octonionMatrixMul (albertMatrix z2) (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) 0 1))) by module,
      h01, smul_zero]
  · have h02 := octAssoc_jordan_off_02 Q hQ hTr z1 z2
    rw [albertMatrix_jordanMul z1 z2, albertMatrix_jordanMul (skewComm Q z1) z2,
      albertMatrix_jordanMul z1 (skewComm Q z2),
      albertMatrix_skewComm Q hQ z1, albertMatrix_skewComm Q hQ z2]
    simp only [octonionMatrixMul_smul_left, octonionMatrixMul_smul_right,
      octonionMatrixMul_add_left, octonionMatrixMul_add_right,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    apply sub_eq_zero.mp
    rw [show (1 / 2 : ℝ) •
          (octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) 0 2 +
            octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) 0 2) -
        (1 / 2 : ℝ) •
          (octonionMatrixMul (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) (matCtoO Q) 0 2 +
            octonionMatrixMul (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) (matCtoO Q) 0 2) -
        ((1 / 2 : ℝ) •
          (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) (albertMatrix z2) 0 2 +
            octonionMatrixMul (albertMatrix z2) (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) 0 2) +
         (1 / 2 : ℝ) •
          (octonionMatrixMul (albertMatrix z1) (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) 0 2 +
            octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) (albertMatrix z1) 0 2)) =
        (1 / 2 : ℝ) •
          (((octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) 0 2 -
              octonionMatrixMul (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) (matCtoO Q) 0 2) -
            (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) (albertMatrix z2) 0 2 +
            octonionMatrixMul (albertMatrix z1) (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) 0 2)) +
          ((octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) 0 2 -
              octonionMatrixMul (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) (matCtoO Q) 0 2) -
            (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) (albertMatrix z1) 0 2 +
            octonionMatrixMul (albertMatrix z2) (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) 0 2))) by module,
      h02, smul_zero]
  · have h12 := octAssoc_jordan_off_12 Q hQ hTr z1 z2
    rw [albertMatrix_jordanMul z1 z2, albertMatrix_jordanMul (skewComm Q z1) z2,
      albertMatrix_jordanMul z1 (skewComm Q z2),
      albertMatrix_skewComm Q hQ z1, albertMatrix_skewComm Q hQ z2]
    simp only [octonionMatrixMul_smul_left, octonionMatrixMul_smul_right,
      octonionMatrixMul_add_left, octonionMatrixMul_add_right,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    apply sub_eq_zero.mp
    rw [show (1 / 2 : ℝ) •
          (octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) 1 2 +
            octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) 1 2) -
        (1 / 2 : ℝ) •
          (octonionMatrixMul (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) (matCtoO Q) 1 2 +
            octonionMatrixMul (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) (matCtoO Q) 1 2) -
        ((1 / 2 : ℝ) •
          (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) (albertMatrix z2) 1 2 +
            octonionMatrixMul (albertMatrix z2) (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) 1 2) +
         (1 / 2 : ℝ) •
          (octonionMatrixMul (albertMatrix z1) (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) 1 2 +
            octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) (albertMatrix z1) 1 2)) =
        (1 / 2 : ℝ) •
          (((octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) 1 2 -
              octonionMatrixMul (octonionMatrixMul (albertMatrix z1) (albertMatrix z2)) (matCtoO Q) 1 2) -
            (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) (albertMatrix z2) 1 2 +
            octonionMatrixMul (albertMatrix z1) (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) 1 2)) +
          ((octonionMatrixMul (matCtoO Q) (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) 1 2 -
              octonionMatrixMul (octonionMatrixMul (albertMatrix z2) (albertMatrix z1)) (matCtoO Q) 1 2) -
            (octonionMatrixMul (octonionMatrixMul (matCtoO Q) (albertMatrix z2) -
              octonionMatrixMul (albertMatrix z2) (matCtoO Q)) (albertMatrix z1) 1 2 +
            octonionMatrixMul (albertMatrix z2) (octonionMatrixMul (matCtoO Q) (albertMatrix z1) -
              octonionMatrixMul (albertMatrix z1) (matCtoO Q)) 1 2))) by module,
      h12, smul_zero]

theorem dop_standardComplexWindow_isDerivation (h1 h2 : Hermitian3) (z1 z2 : Albert) :
    Dop nativeOps (standardComplexWindow.embedding h1) (standardComplexWindow.embedding h2)
        (jordanMul z1 z2) =
      jordanMul
          (Dop nativeOps (standardComplexWindow.embedding h1) (standardComplexWindow.embedding h2) z1)
          z2 +
        jordanMul z1
          (Dop nativeOps (standardComplexWindow.embedding h1) (standardComplexWindow.embedding h2) z2) := by
  rw [Dop_standardComplexWindow, Dop_standardComplexWindow, Dop_standardComplexWindow]
  apply skewComm_isDerivation
  · exact commutator_skew h1 h2
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- Explicit 5-commutator decomposition of any trace-zero skew-Hermitian `Y₀ ∈ su(3)`. -/
def su3CommPairs (Y₀ : ComplexMatrix3) : Fin 5 → Hermitian3 × Hermitian3
  | 0 => (hermE 0, (Y₀ 0 1).re • hermRe 0 + (Y₀ 0 1).im • hermIm 0)
  | 1 => (hermE 0, (Y₀ 0 2).re • hermRe 1 + (Y₀ 0 2).im • hermIm 1)
  | 2 => (hermE 1, (Y₀ 1 2).re • hermRe 2 + (Y₀ 1 2).im • hermIm 2)
  | 3 => ((-((Y₀ 0 0).im / 2)) • hermRe 0, hermIm 0)
  | 4 => (((Y₀ 2 2).im / 2) • hermRe 2, hermIm 2)

theorem su3CommPairs_sum (Y₀ : ComplexMatrix3) (hSkew : Y₀.conjTranspose = -Y₀)
    (hTr : Y₀.trace = 0) :
    (∑ r : Fin 5,
      (((su3CommPairs Y₀ r).1 : ComplexMatrix3) * ((su3CommPairs Y₀ r).2 : ComplexMatrix3) -
       ((su3CommPairs Y₀ r).2 : ComplexMatrix3) * ((su3CommPairs Y₀ r).1 : ComplexMatrix3))) = Y₀ := by
  have hd_re : ∀ i : Fin 3, (Y₀ i i).re = 0 := skew_diag_re_eq_zero hSkew
  have h10 : Y₀ 1 0 = -star (Y₀ 0 1) := by
    have h := congrFun (congrFun hSkew 1) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have h20 : Y₀ 2 0 = -star (Y₀ 0 2) := by
    have h := congrFun (congrFun hSkew 2) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have h21 : Y₀ 2 1 = -star (Y₀ 1 2) := by
    have h := congrFun (congrFun hSkew 2) 1
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have htr_im : (Y₀ 0 0).im + (Y₀ 1 1).im + (Y₀ 2 2).im = 0 := by
    have h := congrArg Complex.im hTr
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_three] using h
  rw [Fin.sum_univ_five]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [su3CommPairs, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, AddSubgroup.coe_add, selfAdjoint.val_smul, Matrix.smul_apply,
      hermE, hermRe, hermIm, hermitian3Equiv, LinearEquiv.coe_symm_mk, mkHerm3Matrix,
      Complex.real_smul];
     apply Complex.ext <;>
       simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
         Complex.mul_re, Complex.mul_im, hd_re 0, hd_re 1, hd_re 2, h10, h20, h21] <;>
       linarith [htr_im])

theorem glennieF_of_skew_eq_zero_of_trace_zero (Y₀ : ComplexMatrix3) (hSkew : Y₀.conjTranspose = -Y₀)
    (hTr : Y₀.trace = 0) (z : Albert) :
    glennieF_of_skew Y₀ z = 0 := by
  unfold glennieF_of_skew
  rw [skewComm_isDerivation Y₀ hSkew hTr z z, jordanMul_comm (skewComm Y₀ z) z,
    two_smul ℝ, sub_self]

theorem glennieF_of_skew_eq_four_lambda_def (Y : ComplexMatrix3) (hY : Y.conjTranspose = -Y)
    (pD : Albert) (hpD : jordanMul pD pD = pD) :
    glennieF_of_skew Y (symmetryOf pD) = (4 * windowMatrixLambda Y) • windowDef pD := by
  let lam := windowMatrixLambda Y
  let Y₀ := Y - lam • (Complex.I • (1 : ComplexMatrix3))
  have hsplit := skew_split_trace_zero hY
  have hYeq : Y = lam • (Complex.I • (1 : ComplexMatrix3)) + Y₀ := by
    dsimp only [lam, Y₀]; abel
  have hY₀_kill : glennieF_of_skew Y₀ (symmetryOf pD) = 0 :=
    glennieF_of_skew_eq_zero_of_trace_zero Y₀ hsplit.1 hsplit.2 (symmetryOf pD)
  have hI_part :
      glennieF_of_skew (Complex.I • (1 : ComplexMatrix3)) (symmetryOf pD) =
        (4 : ℝ) • windowDef pD := by
    unfold glennieF_of_skew
    rw [← windowAdI_eq_skewComm, ← windowAdI_eq_skewComm]
    have hsym_sq : jordanMul (symmetryOf pD) (symmetryOf pD) = albertUnit := by
      simp only [symmetryOf, jordanMul_sub_left, jordanMul_sub_right,
        jordanMul_smul_left, jordanMul_smul_right, hpD,
        jordanMul_albertUnit_left, jordanMul_albertUnit_right]
      module
    have hsym_ad : windowAdI (symmetryOf pD) = (2 : ℝ) • windowAdI pD := by
      simp only [symmetryOf, windowAdI_sub, windowAdI_smul, windowAdI_albertUnit, sub_zero]
    rw [hsym_sq, windowAdI_albertUnit, zero_sub, hsym_ad]
    simp only [symmetryOf, jordanMul_sub_left, jordanMul_smul_left, jordanMul_smul_right,
      jordanMul_albertUnit_left, windowDef]
    module
  conv_lhs => rw [hYeq]
  rw [glennieF_of_skew_add_left, hY₀_kill, add_zero, glennieF_of_skew_smul_left, hI_part,
    smul_smul]
  congr 1
  ring

/-- `thm:glennie` Step 1 on `standardComplexWindow`:
`F(emb A, emb B, emb C, symmetryOf pD) = (4 * windowLambda A B C) • windowDef pD`. -/
theorem glennieF_window_eq_four_lambda_def (A B C : Hermitian3) (pD : Albert)
    (hpD : jordanMul pD pD = pD) :
    nativeGlennieF (standardComplexWindow.embedding A) (standardComplexWindow.embedding B)
        (standardComplexWindow.embedding C) (symmetryOf pD) =
      (4 * windowLambda (A : ComplexMatrix3) (B : ComplexMatrix3) (C : ComplexMatrix3)) •
        windowDef pD := by
  rw [nativeGlennieF_standardComplexWindow]
  exact glennieF_of_skew_eq_four_lambda_def _ (sixProdComm_skewHermitian A B C) pD hpD

/-- `thm:glennie` Step 1 on symmetries `2 • P_k - 1` of window Hermitian elements `P₀, P₁, P₂`. -/
theorem glennieF_window_symm_eq_four_lambda_def (P₀ P₁ P₂ : Hermitian3) (pD : Albert)
    (hpD : jordanMul pD pD = pD) :
    nativeGlennieF
        (symmetryOf (standardComplexWindow.embedding P₀))
        (symmetryOf (standardComplexWindow.embedding P₁))
        (symmetryOf (standardComplexWindow.embedding P₂))
        (symmetryOf pD) =
      (4 * windowLambda
          (2 • (P₀ : ComplexMatrix3) - 1)
          (2 • (P₁ : ComplexMatrix3) - 1)
          (2 • (P₂ : ComplexMatrix3) - 1)) •
        windowDef pD := by
  let R₀ : Hermitian3 := (2 : ℝ) • P₀ - 1
  let R₁ : Hermitian3 := (2 : ℝ) • P₁ - 1
  let R₂ : Hermitian3 := (2 : ℝ) • P₂ - 1
  have hR : ∀ P : Hermitian3,
      standardComplexWindow.embedding ((2 : ℝ) • P - 1) =
        symmetryOf (standardComplexWindow.embedding P) := fun P => by
    rw [map_sub, map_smul, standardComplexWindow.unit]
    rfl
  have hM : ∀ P : Hermitian3,
      (((2 : ℝ) • P - 1 : Hermitian3) : ComplexMatrix3) = 2 • (P : ComplexMatrix3) - 1 := fun P => by
    simp [two_smul]
  rw [← hR P₀, ← hR P₁, ← hR P₂, glennieF_window_eq_four_lambda_def R₀ R₁ R₂ pD hpD,
    hM P₀, hM P₁, hM P₂]

end

end AlbertSequential.AppF
