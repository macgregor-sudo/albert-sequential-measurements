module

public import Defs
public import DiagPeirceAnchor
public import NativePeircePropagation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Elementary Native Albert Laws, Fixed Real-`B` Compression, and Quaternion Dyad Bridges

Clean-room formalization of:
1. Canonical `Octonion` basis elements (`octI`, `octJ`, `octK`, `octL`, `octS`, `octR`, `octT`)
   and the Euclidean pairing `octDot`.
2. Elementary `ℝ`-bilinearity, commutativity, right-unit, diagonal-entry, trace-pairing,
   and quadratic-map scaling/additivity laws on `AlbertSequential.Albert`.
3. The fixed real-atom compression `quadraticMap atomB y = tracePairing atomB y • atomB`
   for every `y : Albert`, using only real-scalar associativity.
4. Two explicit faithful quaternion subalgebra embeddings `quatEmbed1`, `quatEmbed2`
   and the Hermitian `3 × 3` quaternionic matrix bridge proving `quatDyad_isAtom` and
   `quadraticMap_quatDyad`.

No `Mul`, `One`, `Star`, or `Norm` instance is exported on `Octonion` or `Albert`.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

/-! ## Internal Carrier Projection Helpers -/

private theorem oct_zero_fst : (0 : Octonion).1 = 0 := rfl
private theorem oct_zero_snd : (0 : Octonion).2 = 0 := rfl
private theorem oct_add_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem oct_add_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem oct_smul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem oct_smul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl

private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

private theorem quat_star_smul (r : ℝ) (q : Quaternion ℝ) : star (r • q) = r • star q := by
  apply Quaternion.ext <;> simp

/-! ## Section 1: Octonion Basis, Arithmetic, and Euclidean Pairing `octDot` -/

def octI : Octonion := (⟨0, 1, 0, 0⟩, 0)
def octJ : Octonion := (⟨0, 0, 1, 0⟩, 0)
def octK : Octonion := (⟨0, 0, 0, 1⟩, 0)
def octL : Octonion := (0, ⟨1, 0, 0, 0⟩)
def octS : Octonion := (0, ⟨0, 1, 0, 0⟩)
def octR : Octonion := (0, ⟨0, 0, 1, 0⟩)
def octT : Octonion := (0, ⟨0, 0, 0, 1⟩)

theorem octS_eq_mul : octonionMul octI octL = octS := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octonionMul, octI, octL, octS]

theorem octR_eq_mul : octonionMul octJ octL = octR := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octonionMul, octJ, octL, octR]

theorem octT_eq_mul : octonionMul octK octL = octT := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octonionMul, octK, octL, octT]

theorem octonionMul_zero_left (z : Octonion) : octonionMul 0 z = 0 := by
  apply Prod.ext
  · change (0 : Octonion).1 * z.1 - star z.2 * (0 : Octonion).2 = (0 : Octonion).1
    rw [oct_zero_fst, oct_zero_snd, zero_mul, mul_zero, sub_zero]
  · change z.2 * (0 : Octonion).1 + (0 : Octonion).2 * star z.1 = (0 : Octonion).2
    rw [oct_zero_fst, oct_zero_snd, mul_zero, zero_mul, add_zero]

theorem octonionMul_zero_right (z : Octonion) : octonionMul z 0 = 0 := by
  apply Prod.ext
  · change z.1 * (0 : Octonion).1 - star (0 : Octonion).2 * z.2 = (0 : Octonion).1
    rw [oct_zero_fst, oct_zero_snd, mul_zero, star_zero, zero_mul, sub_zero]
  · change (0 : Octonion).2 * z.1 + z.2 * star (0 : Octonion).1 = (0 : Octonion).2
    rw [oct_zero_fst, oct_zero_snd, zero_mul, star_zero, mul_zero, add_zero]

theorem octonionMul_add_left (x y z : Octonion) :
    octonionMul (x + y) z = octonionMul x z + octonionMul y z := by
  apply Prod.ext
  · change (x.1 + y.1) * z.1 - star z.2 * (x.2 + y.2) =
      (x.1 * z.1 - star z.2 * x.2) + (y.1 * z.1 - star z.2 * y.2)
    rw [add_mul, mul_add]
    abel
  · change z.2 * (x.1 + y.1) + (x.2 + y.2) * star z.1 =
      (z.2 * x.1 + x.2 * star z.1) + (z.2 * y.1 + y.2 * star z.1)
    rw [mul_add, add_mul]
    abel

theorem octonionMul_add_right (x y z : Octonion) :
    octonionMul x (y + z) = octonionMul x y + octonionMul x z := by
  apply Prod.ext
  · change x.1 * (y.1 + z.1) - star (y.2 + z.2) * x.2 =
      (x.1 * y.1 - star y.2 * x.2) + (x.1 * z.1 - star z.2 * x.2)
    rw [mul_add, star_add, add_mul]
    abel
  · change (y.2 + z.2) * x.1 + x.2 * star (y.1 + z.1) =
      (y.2 * x.1 + x.2 * star y.1) + (z.2 * x.1 + x.2 * star z.1)
    rw [add_mul, star_add, mul_add]
    abel

theorem octonionMul_smul_left (r : ℝ) (x y : Octonion) :
    octonionMul (r • x) y = r • octonionMul x y := by
  apply Prod.ext
  · change (r • x.1) * y.1 - star y.2 * (r • x.2) =
      r • (x.1 * y.1 - star y.2 * x.2)
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  · change y.2 * (r • x.1) + (r • x.2) * star y.1 =
      r • (y.2 * x.1 + x.2 * star y.1)
    rw [mul_smul_comm, smul_mul_assoc, smul_add]

theorem octonionMul_smul_right (r : ℝ) (x y : Octonion) :
    octonionMul x (r • y) = r • octonionMul x y := by
  apply Prod.ext
  · change x.1 * (r • y.1) - star (r • y.2) * x.2 =
      r • (x.1 * y.1 - star y.2 * x.2)
    rw [mul_smul_comm, quat_star_smul, smul_mul_assoc, smul_sub]
  · change (r • y.2) * x.1 + x.2 * star (r • y.1) =
      r • (y.2 * x.1 + x.2 * star y.1)
    rw [smul_mul_assoc, quat_star_smul, mul_smul_comm, smul_add]

theorem octonionConj_zero : octonionConj 0 = 0 := by
  apply Prod.ext
  · change star (0 : Octonion).1 = (0 : Octonion).1
    rw [oct_zero_fst, star_zero]
  · change -(0 : Octonion).2 = (0 : Octonion).2
    rw [oct_zero_snd, neg_zero]

theorem octonionConj_add (x y : Octonion) :
    octonionConj (x + y) = octonionConj x + octonionConj y := by
  apply Prod.ext
  · change star (x.1 + y.1) = star x.1 + star y.1
    exact star_add x.1 y.1
  · change -(x.2 + y.2) = -x.2 + -y.2
    exact neg_add x.2 y.2

theorem octonionConj_neg (x : Octonion) :
    octonionConj (-x) = -octonionConj x := by
  apply Prod.ext
  · change star (-x.1) = -star x.1
    exact star_neg x.1
  · change -(-x.2) = -(-x.2)
    rfl

theorem octonionConj_smul (r : ℝ) (x : Octonion) :
    octonionConj (r • x) = r • octonionConj x := by
  apply Prod.ext
  · change star (r • x.1) = r • star x.1
    exact quat_star_smul r x.1
  · change -(r • x.2) = r • (-x.2)
    exact (smul_neg r x.2).symm

theorem octonionConj_conj (x : Octonion) :
    octonionConj (octonionConj x) = x := by
  apply Prod.ext
  · change star (star x.1) = x.1
    exact star_star x.1
  · change -(-x.2) = x.2
    exact neg_neg x.2

theorem octonionConj_mul (x y : Octonion) :
    octonionConj (octonionMul x y) = octonionMul (octonionConj y) (octonionConj x) := by
  apply Prod.ext
  · change star (x.1 * y.1 - star y.2 * x.2) =
      star y.1 * star x.1 - star (-x.2) * (-y.2)
    rw [star_sub, star_mul, star_mul, star_star, star_neg, neg_mul, mul_neg, neg_neg]
  · change -(y.2 * x.1 + x.2 * star y.1) =
      (-x.2) * star y.1 + (-y.2) * star (star x.1)
    rw [star_star, neg_mul, neg_mul, neg_add]
    abel

theorem octonionScalar_zero : octonionScalar 0 = 0 := by
  apply Prod.ext
  · apply Quaternion.ext <;> rfl
  · exact oct_zero_snd.symm

theorem octonionScalar_eq_smul (r : ℝ) :
    octonionScalar r = r • octonionScalar 1 := by
  apply Prod.ext
  · rw [oct_smul_fst]
    apply Quaternion.ext <;> simp [octonionScalar]
  · rw [oct_smul_snd]
    change (0 : Quaternion ℝ) = r • (0 : Quaternion ℝ)
    rw [smul_zero]

theorem octonionScalar_add (r s : ℝ) :
    octonionScalar (r + s) = octonionScalar r + octonionScalar s := by
  apply Prod.ext
  · rw [oct_add_fst]
    apply Quaternion.ext <;> simp [octonionScalar]
  · rw [oct_add_snd]
    change (0 : Quaternion ℝ) = 0 + 0
    rw [add_zero]

theorem octonionScalar_smul (r s : ℝ) :
    octonionScalar (r * s) = r • octonionScalar s := by
  apply Prod.ext
  · rw [oct_smul_fst]
    apply Quaternion.ext <;> simp [octonionScalar]
  · rw [oct_smul_snd]
    change (0 : Quaternion ℝ) = r • (0 : Quaternion ℝ)
    rw [smul_zero]

theorem octonionConj_scalar (r : ℝ) :
    octonionConj (octonionScalar r) = octonionScalar r := by
  apply Prod.ext
  · apply Quaternion.ext <;> simp [octonionConj, octonionScalar]
  · change -(0 : Quaternion ℝ) = 0
    rw [neg_zero]

theorem octonionMul_scalar_one_left (z : Octonion) :
    octonionMul (octonionScalar 1) z = z := by
  have h1 : (octonionScalar 1).1 = (1 : Quaternion ℝ) := by
    apply Quaternion.ext <;> rfl
  have h2 : (octonionScalar 1).2 = (0 : Quaternion ℝ) := rfl
  apply Prod.ext
  · change (octonionScalar 1).1 * z.1 - star z.2 * (octonionScalar 1).2 = z.1
    rw [h1, h2, one_mul, mul_zero, sub_zero]
  · change z.2 * (octonionScalar 1).1 + (octonionScalar 1).2 * star z.1 = z.2
    rw [h1, h2, mul_one, zero_mul, add_zero]

theorem octonionMul_scalar_one_right (z : Octonion) :
    octonionMul z (octonionScalar 1) = z := by
  have h1 : (octonionScalar 1).1 = (1 : Quaternion ℝ) := by
    apply Quaternion.ext <;> rfl
  have h2 : (octonionScalar 1).2 = (0 : Quaternion ℝ) := rfl
  apply Prod.ext
  · change z.1 * (octonionScalar 1).1 - star (octonionScalar 1).2 * z.2 = z.1
    rw [h1, h2, mul_one, star_zero, zero_mul, sub_zero]
  · change (octonionScalar 1).2 * z.1 + z.2 * star (octonionScalar 1).1 = z.2
    rw [h1, h2, zero_mul, star_one, mul_one, zero_add]

theorem octonionMul_scalar_left (r : ℝ) (z : Octonion) :
    octonionMul (octonionScalar r) z = r • z := by
  rw [octonionScalar_eq_smul, octonionMul_smul_left, octonionMul_scalar_one_left]

theorem octonionMul_scalar_right (r : ℝ) (z : Octonion) :
    octonionMul z (octonionScalar r) = r • z := by
  rw [octonionScalar_eq_smul, octonionMul_smul_right, octonionMul_scalar_one_right]

theorem octonionReal_zero : octonionReal 0 = 0 := rfl

theorem octonionReal_add (x y : Octonion) :
    octonionReal (x + y) = octonionReal x + octonionReal y := rfl

theorem octonionReal_neg (x : Octonion) :
    octonionReal (-x) = -octonionReal x := rfl

theorem octonionReal_smul (r : ℝ) (x : Octonion) :
    octonionReal (r • x) = r * octonionReal x := rfl

theorem octonionReal_scalar (r : ℝ) :
    octonionReal (octonionScalar r) = r := rfl

theorem octonionReal_conj (x : Octonion) :
    octonionReal (octonionConj x) = octonionReal x := by
  simp [octonionReal, octonionConj]

theorem octonionReal_mul_comm (x y : Octonion) :
    octonionReal (octonionMul x y) = octonionReal (octonionMul y x) := by
  simp [octonionReal, octonionMul]
  ring

def octDot (x y : Octonion) : ℝ := octonionReal (octonionMul x (octonionConj y))

theorem octDot_eq_coords (x y : Octonion) :
    octDot x y =
      x.1.re * y.1.re + x.1.imI * y.1.imI + x.1.imJ * y.1.imJ + x.1.imK * y.1.imK +
      x.2.re * y.2.re + x.2.imI * y.2.imI + x.2.imJ * y.2.imJ + x.2.imK * y.2.imK := by
  simp [octDot, octonionReal, octonionMul, octonionConj]
  ring

theorem octDot_comm (x y : Octonion) : octDot x y = octDot y x := by
  rw [octDot_eq_coords, octDot_eq_coords]
  ring

theorem octDot_zero_left (y : Octonion) : octDot 0 y = 0 := by
  simp [octDot, octonionMul_zero_left, octonionReal_zero]

theorem octDot_zero_right (x : Octonion) : octDot x 0 = 0 := by
  rw [octDot_comm, octDot_zero_left]

theorem octDot_add_left (x y z : Octonion) :
    octDot (x + y) z = octDot x z + octDot y z := by
  simp [octDot, octonionMul_add_left, octonionReal_add]

theorem octDot_add_right (x y z : Octonion) :
    octDot x (y + z) = octDot x y + octDot x z := by
  rw [octDot_comm, octDot_add_left, octDot_comm x y, octDot_comm x z]

theorem octDot_smul_left (r : ℝ) (x y : Octonion) :
    octDot (r • x) y = r * octDot x y := by
  simp [octDot, octonionMul_smul_left, octonionReal_smul]

theorem octDot_smul_right (r : ℝ) (x y : Octonion) :
    octDot x (r • y) = r * octDot x y := by
  rw [octDot_comm, octDot_smul_left, octDot_comm]

theorem octDot_scalar_left (r : ℝ) (y : Octonion) :
    octDot (octonionScalar r) y = r * octonionReal y := by
  simp [octDot, octonionMul_scalar_left, octonionReal_smul, octonionReal_conj]

private theorem octonionReal_mul_conj_left (a b : Octonion) :
    octonionReal (octonionMul (octonionConj a) b) = octDot a b := by
  rw [octonionReal_mul_comm]
  exact octDot_comm b a

/-! ## Section 2: Elementary Native Albert Laws -/

private theorem albertMatrix_00 (x : Albert) : albertMatrix x 0 0 = octonionScalar (x.1 0) := rfl
private theorem albertMatrix_01 (x : Albert) : albertMatrix x 0 1 = x.2 0 := rfl
private theorem albertMatrix_02 (x : Albert) : albertMatrix x 0 2 = x.2 1 := rfl
private theorem albertMatrix_10 (x : Albert) : albertMatrix x 1 0 = octonionConj (x.2 0) := rfl
private theorem albertMatrix_11 (x : Albert) : albertMatrix x 1 1 = octonionScalar (x.1 1) := rfl
private theorem albertMatrix_12 (x : Albert) : albertMatrix x 1 2 = x.2 2 := rfl
private theorem albertMatrix_20 (x : Albert) : albertMatrix x 2 0 = octonionConj (x.2 1) := rfl
private theorem albertMatrix_21 (x : Albert) : albertMatrix x 2 1 = octonionConj (x.2 2) := rfl
private theorem albertMatrix_22 (x : Albert) : albertMatrix x 2 2 = octonionScalar (x.1 2) := rfl

private theorem albertMatrix_add (x y : Albert) :
    albertMatrix (x + y) = albertMatrix x + albertMatrix y := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact octonionScalar_add (x.1 0) (y.1 0)
  · rfl
  · rfl
  · exact octonionConj_add (x.2 0) (y.2 0)
  · exact octonionScalar_add (x.1 1) (y.1 1)
  · rfl
  · exact octonionConj_add (x.2 1) (y.2 1)
  · exact octonionConj_add (x.2 2) (y.2 2)
  · exact octonionScalar_add (x.1 2) (y.1 2)

private theorem albertMatrix_smul (r : ℝ) (x : Albert) :
    albertMatrix (r • x) = r • albertMatrix x := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact octonionScalar_smul r (x.1 0)
  · rfl
  · rfl
  · exact octonionConj_smul r (x.2 0)
  · exact octonionScalar_smul r (x.1 1)
  · rfl
  · exact octonionConj_smul r (x.2 1)
  · exact octonionConj_smul r (x.2 2)
  · exact octonionScalar_smul r (x.1 2)

private theorem octonionMatrixMul_add_left (X Y Z : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul (X + Y) Z = octonionMatrixMul X Z + octonionMatrixMul Y Z := by
  funext i j
  simp [octonionMatrixMul, octonionMul_add_left, Finset.sum_add_distrib]

private theorem octonionMatrixMul_add_right (X Y Z : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul X (Y + Z) = octonionMatrixMul X Y + octonionMatrixMul X Z := by
  funext i j
  simp [octonionMatrixMul, octonionMul_add_right, Finset.sum_add_distrib]

private theorem octonionMatrixMul_smul_left (r : ℝ) (X Y : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul (r • X) Y = r • octonionMatrixMul X Y := by
  funext i j
  simp [octonionMatrixMul, octonionMul_smul_left, Finset.smul_sum]

private theorem octonionMatrixMul_smul_right (r : ℝ) (X Y : Fin 3 → Fin 3 → Octonion) :
    octonionMatrixMul X (r • Y) = r • octonionMatrixMul X Y := by
  funext i j
  simp [octonionMatrixMul, octonionMul_smul_right, Finset.smul_sum]

private theorem albertCoordinates_add (M N : Fin 3 → Fin 3 → Octonion) :
    albertCoordinates (M + N) = albertCoordinates M + albertCoordinates N := by
  apply Prod.ext <;> funext i
  · rw [albert_add_fst]
    exact octonionReal_add (M i i) (N i i)
  · rw [albert_add_snd]
    fin_cases i <;> rfl

private theorem albertCoordinates_smul (r : ℝ) (M : Fin 3 → Fin 3 → Octonion) :
    albertCoordinates (r • M) = r • albertCoordinates M := by
  apply Prod.ext <;> funext i
  · rw [albert_smul_fst]
    exact octonionReal_smul r (M i i)
  · rw [albert_smul_snd]
    fin_cases i <;> rfl

theorem jordanMul_comm (x y : Albert) : jordanMul x y = jordanMul y x := by
  unfold jordanMul
  rw [add_comm]

theorem jordanMul_albertUnit_right (x : Albert) : jordanMul x albertUnit = x := by
  rw [jordanMul_comm, jordanMul_albertUnit_left]

theorem jordanMul_add_left (x y z : Albert) :
    jordanMul (x + y) z = jordanMul x z + jordanMul y z := by
  unfold jordanMul
  rw [albertMatrix_add, octonionMatrixMul_add_left, octonionMatrixMul_add_right]
  have h :
      (octonionMatrixMul (albertMatrix x) (albertMatrix z) +
          octonionMatrixMul (albertMatrix y) (albertMatrix z)) +
        (octonionMatrixMul (albertMatrix z) (albertMatrix x) +
          octonionMatrixMul (albertMatrix z) (albertMatrix y)) =
      (octonionMatrixMul (albertMatrix x) (albertMatrix z) +
          octonionMatrixMul (albertMatrix z) (albertMatrix x)) +
        (octonionMatrixMul (albertMatrix y) (albertMatrix z) +
          octonionMatrixMul (albertMatrix z) (albertMatrix y)) := by
    abel
  rw [h, albertCoordinates_add, smul_add]

theorem jordanMul_add_right (x y z : Albert) :
    jordanMul x (y + z) = jordanMul x y + jordanMul x z := by
  rw [jordanMul_comm, jordanMul_add_left, jordanMul_comm x y, jordanMul_comm x z]

theorem jordanMul_smul_left (r : ℝ) (x y : Albert) :
    jordanMul (r • x) y = r • jordanMul x y := by
  unfold jordanMul
  rw [albertMatrix_smul, octonionMatrixMul_smul_left, octonionMatrixMul_smul_right,
    ← smul_add, albertCoordinates_smul, smul_comm]

theorem jordanMul_smul_right (r : ℝ) (x y : Albert) :
    jordanMul x (r • y) = r • jordanMul x y := by
  rw [jordanMul_comm, jordanMul_smul_left, jordanMul_comm]

theorem jordanMul_zero_left (x : Albert) : jordanMul 0 x = 0 := by
  calc
    jordanMul 0 x = jordanMul ((0 : ℝ) • (0 : Albert)) x := by rw [zero_smul]
    _ = (0 : ℝ) • jordanMul 0 x := jordanMul_smul_left 0 0 x
    _ = 0 := zero_smul ℝ _

theorem jordanMul_zero_right (x : Albert) : jordanMul x 0 = 0 := by
  rw [jordanMul_comm, jordanMul_zero_left]

theorem jordanMul_neg_left (x y : Albert) : jordanMul (-x) y = -jordanMul x y := by
  calc
    jordanMul (-x) y = jordanMul ((-1 : ℝ) • x) y := by rw [neg_one_smul]
    _ = (-1 : ℝ) • jordanMul x y := jordanMul_smul_left (-1) x y
    _ = -jordanMul x y := neg_one_smul ℝ _

theorem jordanMul_neg_right (x y : Albert) : jordanMul x (-y) = -jordanMul x y := by
  rw [jordanMul_comm, jordanMul_neg_left, jordanMul_comm]

theorem jordanMul_sub_left (x y z : Albert) :
    jordanMul (x - y) z = jordanMul x z - jordanMul y z := by
  rw [sub_eq_add_neg, jordanMul_add_left, jordanMul_neg_left, ← sub_eq_add_neg]

theorem jordanMul_sub_right (x y z : Albert) :
    jordanMul x (y - z) = jordanMul x y - jordanMul x z := by
  rw [sub_eq_add_neg, jordanMul_add_right, jordanMul_neg_right, ← sub_eq_add_neg]

theorem albertTrace_add (x y : Albert) :
    albertTrace (x + y) = albertTrace x + albertTrace y := by
  unfold albertTrace
  simp only [albert_add_fst, Finset.sum_add_distrib]

theorem albertTrace_sub (x y : Albert) :
    albertTrace (x - y) = albertTrace x - albertTrace y := by
  unfold albertTrace
  simp only [albert_sub_fst, Finset.sum_sub_distrib]

theorem albertTrace_smul (r : ℝ) (x : Albert) :
    albertTrace (r • x) = r * albertTrace x := by
  unfold albertTrace
  simp only [albert_smul_fst, Finset.mul_sum]

private theorem octonionReal_mul_conj_right (a b : Octonion) :
    octonionReal (octonionMul a (octonionConj b)) = octDot a b := rfl

theorem jordanMul_diag_0 (x y : Albert) :
    (jordanMul x y).1 0 = x.1 0 * y.1 0 + octDot (x.2 0) (y.2 0) + octDot (x.2 1) (y.2 1) := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) * octonionReal
      (octonionMatrixMul (albertMatrix x) (albertMatrix y) 0 0 +
        octonionMatrixMul (albertMatrix y) (albertMatrix x) 0 0) =
    x.1 0 * y.1 0 + octDot (x.2 0) (y.2 0) + octDot (x.2 1) (y.2 1)
  unfold octonionMatrixMul
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [albertMatrix_00, albertMatrix_01, albertMatrix_02,
    albertMatrix_10, albertMatrix_20,
    octonionReal_add, octonionMul_scalar_left, octonionReal_smul, octonionReal_scalar,
    octonionReal_mul_conj_right]
  rw [octDot_comm (y.2 0) (x.2 0), octDot_comm (y.2 1) (x.2 1)]
  ring

theorem jordanMul_diag_1 (x y : Albert) :
    (jordanMul x y).1 1 = x.1 1 * y.1 1 + octDot (x.2 0) (y.2 0) + octDot (x.2 2) (y.2 2) := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) * octonionReal
      (octonionMatrixMul (albertMatrix x) (albertMatrix y) 1 1 +
        octonionMatrixMul (albertMatrix y) (albertMatrix x) 1 1) =
    x.1 1 * y.1 1 + octDot (x.2 0) (y.2 0) + octDot (x.2 2) (y.2 2)
  unfold octonionMatrixMul
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [albertMatrix_10, albertMatrix_11, albertMatrix_12,
    albertMatrix_01, albertMatrix_21,
    octonionReal_add, octonionMul_scalar_left, octonionReal_smul, octonionReal_scalar,
    octonionReal_mul_conj_left, octonionReal_mul_conj_right]
  rw [octDot_comm (y.2 0) (x.2 0), octDot_comm (y.2 2) (x.2 2)]
  ring

theorem jordanMul_diag_2 (x y : Albert) :
    (jordanMul x y).1 2 = x.1 2 * y.1 2 + octDot (x.2 1) (y.2 1) + octDot (x.2 2) (y.2 2) := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) * octonionReal
      (octonionMatrixMul (albertMatrix x) (albertMatrix y) 2 2 +
        octonionMatrixMul (albertMatrix y) (albertMatrix x) 2 2) =
    x.1 2 * y.1 2 + octDot (x.2 1) (y.2 1) + octDot (x.2 2) (y.2 2)
  unfold octonionMatrixMul
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [albertMatrix_20, albertMatrix_21, albertMatrix_22,
    albertMatrix_02, albertMatrix_12,
    octonionReal_add, octonionMul_scalar_left, octonionReal_smul, octonionReal_scalar,
    octonionReal_mul_conj_left]
  rw [octDot_comm (y.2 1) (x.2 1), octDot_comm (y.2 2) (x.2 2)]
  ring

theorem tracePairing_eq_coords (x y : Albert) :
    tracePairing x y =
      (x.1 0 * y.1 0 + x.1 1 * y.1 1 + x.1 2 * y.1 2) +
      2 * (octDot (x.2 0) (y.2 0) + octDot (x.2 1) (y.2 1) + octDot (x.2 2) (y.2 2)) := by
  unfold tracePairing albertTrace
  rw [Fin.sum_univ_three, jordanMul_diag_0, jordanMul_diag_1, jordanMul_diag_2]
  ring

theorem tracePairing_comm (x y : Albert) : tracePairing x y = tracePairing y x := by
  unfold tracePairing
  rw [jordanMul_comm]

theorem tracePairing_add_right (x y z : Albert) :
    tracePairing x (y + z) = tracePairing x y + tracePairing x z := by
  unfold tracePairing
  rw [jordanMul_add_right, albertTrace_add]

theorem tracePairing_sub_right (x y z : Albert) :
    tracePairing x (y - z) = tracePairing x y - tracePairing x z := by
  unfold tracePairing
  rw [jordanMul_sub_right, albertTrace_sub]

theorem tracePairing_smul_right (r : ℝ) (x y : Albert) :
    tracePairing x (r • y) = r * tracePairing x y := by
  unfold tracePairing
  rw [jordanMul_smul_right, albertTrace_smul]

theorem tracePairing_add_left (x y z : Albert) :
    tracePairing (x + y) z = tracePairing x z + tracePairing y z := by
  rw [tracePairing_comm, tracePairing_add_right, tracePairing_comm z x, tracePairing_comm z y]

theorem tracePairing_sub_left (x y z : Albert) :
    tracePairing (x - y) z = tracePairing x z - tracePairing y z := by
  rw [tracePairing_comm, tracePairing_sub_right, tracePairing_comm z x, tracePairing_comm z y]

theorem tracePairing_smul_left (r : ℝ) (x y : Albert) :
    tracePairing (r • x) y = r * tracePairing x y := by
  rw [tracePairing_comm, tracePairing_smul_right, tracePairing_comm]

theorem quadraticMap_smul_left (r : ℝ) (x y : Albert) :
    quadraticMap (r • x) y = (r ^ 2) • quadraticMap x y := by
  unfold quadraticMap
  simp only [jordanMul_smul_left, jordanMul_smul_right, smul_smul, two_smul]
  have hsq : r * r = r ^ 2 := by ring
  rw [hsq]
  module

theorem quadraticMap_smul_right (r : ℝ) (x y : Albert) :
    quadraticMap x (r • y) = r • quadraticMap x y := by
  unfold quadraticMap
  rw [jordanMul_smul_right, jordanMul_smul_right, jordanMul_smul_right, two_smul, two_smul]
  module

theorem quadraticMap_add_right (x y z : Albert) :
    quadraticMap x (y + z) = quadraticMap x y + quadraticMap x z := by
  unfold quadraticMap
  rw [jordanMul_add_right, jordanMul_add_right, jordanMul_add_right, smul_add]
  abel

theorem quadraticMap_zero_right (x : Albert) :
    quadraticMap x 0 = 0 := by
  unfold quadraticMap
  simp [jordanMul_zero_right]

/-! ## Section 3: Fixed Real `atomB` All-Input Compression -/

def atomB : Albert := (1 / 2 : ℝ) • (![1, 1, 0], ![octonionScalar 1, 0, 0])

private theorem atomB_fst_0 : atomB.1 0 = 1 / 2 := by
  change (1 / 2 : ℝ) * (1 : ℝ) = 1 / 2
  ring

private theorem atomB_fst_1 : atomB.1 1 = 1 / 2 := by
  change (1 / 2 : ℝ) * (1 : ℝ) = 1 / 2
  ring

private theorem atomB_fst_2 : atomB.1 2 = 0 := by
  change (1 / 2 : ℝ) * (0 : ℝ) = 0
  ring

private theorem atomB_snd_0 : atomB.2 0 = (1 / 2 : ℝ) • octonionScalar 1 := rfl

private theorem atomB_snd_1 : atomB.2 1 = 0 := by
  change (1 / 2 : ℝ) • (0 : Octonion) = 0
  exact smul_zero _

private theorem atomB_snd_2 : atomB.2 2 = 0 := by
  change (1 / 2 : ℝ) • (0 : Octonion) = 0
  exact smul_zero _

theorem tracePairing_atomB (y : Albert) :
    tracePairing atomB y = (y.1 0 + y.1 1) / 2 + octonionReal (y.2 0) := by
  rw [tracePairing_eq_coords, atomB_fst_0, atomB_fst_1, atomB_fst_2,
    atomB_snd_0, atomB_snd_1, atomB_snd_2,
    octDot_smul_left, octDot_scalar_left, octDot_zero_left, octDot_zero_left]
  ring

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (hu0 : x.2 0 = y.2 0) (hu1 : x.2 1 = y.2 1) (hu2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext i <;> fin_cases i
  · exact hd0
  · exact hd1
  · exact hd2
  · exact hu0
  · exact hu1
  · exact hu2

private theorem albertMatrix_atomB (r s : Fin 3) :
    albertMatrix atomB r s =
      if r.val < 2 ∧ s.val < 2 then octonionScalar (1 / 2) else 0 := by
  have h12 : (1 / 2 : ℝ) • octonionScalar 1 = octonionScalar (1 / 2) := by
    rw [← octonionScalar_smul, mul_one]
  simp only [one_div] at h12
  fin_cases r <;> fin_cases s <;>
    simp [albertMatrix, atomB_fst_0, atomB_fst_1, atomB_fst_2,
      atomB_snd_0, atomB_snd_1, atomB_snd_2,
      h12, octonionConj_scalar, octonionScalar_zero, octonionConj_zero]

private theorem octonionMatrixMul_atomB_left (M : Fin 3 → Fin 3 → Octonion) (r s : Fin 3) :
    octonionMatrixMul (albertMatrix atomB) M r s =
      if r.val < 2 then (1 / 2 : ℝ) • (M 0 s + M 1 s) else 0 := by
  unfold octonionMatrixMul
  rw [Fin.sum_univ_three]
  fin_cases r <;>
    simp [albertMatrix_atomB, octonionMul_scalar_left, octonionMul_zero_left, smul_add]

private theorem octonionMatrixMul_atomB_right (M : Fin 3 → Fin 3 → Octonion) (r s : Fin 3) :
    octonionMatrixMul M (albertMatrix atomB) r s =
      if s.val < 2 then (1 / 2 : ℝ) • (M r 0 + M r 1) else 0 := by
  unfold octonionMatrixMul
  rw [Fin.sum_univ_three]
  fin_cases s <;>
    simp [albertMatrix_atomB, octonionMul_scalar_right, octonionMul_zero_right, smul_add]

private theorem jordanMul_atomB_fst_0 (y : Albert) :
    (jordanMul atomB y).1 0 = (y.1 0 + octonionReal (y.2 0)) / 2 := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) * octonionReal
      (octonionMatrixMul (albertMatrix atomB) (albertMatrix y) 0 0 +
        octonionMatrixMul (albertMatrix y) (albertMatrix atomB) 0 0) =
    (y.1 0 + octonionReal (y.2 0)) / 2
  rw [octonionMatrixMul_atomB_left, octonionMatrixMul_atomB_right]
  have h0 : (0 : Fin 3).val < 2 := by decide
  simp only [h0, ↓reduceIte, albertMatrix_00, albertMatrix_10,
    albertMatrix_01, octonionReal_add, octonionReal_smul, octonionReal_scalar, octonionReal_conj]
  ring

private theorem jordanMul_atomB_fst_1 (y : Albert) :
    (jordanMul atomB y).1 1 = (y.1 1 + octonionReal (y.2 0)) / 2 := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) * octonionReal
      (octonionMatrixMul (albertMatrix atomB) (albertMatrix y) 1 1 +
        octonionMatrixMul (albertMatrix y) (albertMatrix atomB) 1 1) =
    (y.1 1 + octonionReal (y.2 0)) / 2
  rw [octonionMatrixMul_atomB_left, octonionMatrixMul_atomB_right]
  have h1 : (1 : Fin 3).val < 2 := by decide
  simp only [h1, ↓reduceIte, albertMatrix_01, albertMatrix_11,
    albertMatrix_10, octonionReal_add, octonionReal_smul, octonionReal_scalar, octonionReal_conj]
  ring

private theorem jordanMul_atomB_fst_2 (y : Albert) :
    (jordanMul atomB y).1 2 = 0 := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) * octonionReal
      (octonionMatrixMul (albertMatrix atomB) (albertMatrix y) 2 2 +
        octonionMatrixMul (albertMatrix y) (albertMatrix atomB) 2 2) = 0
  rw [octonionMatrixMul_atomB_left, octonionMatrixMul_atomB_right]
  simp [octonionReal_zero]

private theorem jordanMul_atomB_snd_0 (y : Albert) :
    (jordanMul atomB y).2 0 =
      (1 / 4 : ℝ) • octonionScalar (y.1 0 + y.1 1) + (1 / 2 : ℝ) • y.2 0 := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) •
      (octonionMatrixMul (albertMatrix atomB) (albertMatrix y) 0 1 +
        octonionMatrixMul (albertMatrix y) (albertMatrix atomB) 0 1) =
    (1 / 4 : ℝ) • octonionScalar (y.1 0 + y.1 1) + (1 / 2 : ℝ) • y.2 0
  rw [octonionMatrixMul_atomB_left, octonionMatrixMul_atomB_right]
  have h0 : (0 : Fin 3).val < 2 := by decide
  have h1 : (1 : Fin 3).val < 2 := by decide
  simp only [h0, h1, ↓reduceIte, albertMatrix_01, albertMatrix_11, albertMatrix_00, octonionScalar_add]
  module

private theorem jordanMul_atomB_snd_1 (y : Albert) :
    (jordanMul atomB y).2 1 = (1 / 4 : ℝ) • (y.2 1 + y.2 2) := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) •
      (octonionMatrixMul (albertMatrix atomB) (albertMatrix y) 0 2 +
        octonionMatrixMul (albertMatrix y) (albertMatrix atomB) 0 2) =
    (1 / 4 : ℝ) • (y.2 1 + y.2 2)
  rw [octonionMatrixMul_atomB_left, octonionMatrixMul_atomB_right]
  have h0 : (0 : Fin 3).val < 2 := by decide
  have h2 : ¬ ((2 : Fin 3).val < 2) := by decide
  simp only [h0, h2, ↓reduceIte, albertMatrix_02, albertMatrix_12, add_zero]
  module

private theorem jordanMul_atomB_snd_2 (y : Albert) :
    (jordanMul atomB y).2 2 = (1 / 4 : ℝ) • (y.2 1 + y.2 2) := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) •
      (octonionMatrixMul (albertMatrix atomB) (albertMatrix y) 1 2 +
        octonionMatrixMul (albertMatrix y) (albertMatrix atomB) 1 2) =
    (1 / 4 : ℝ) • (y.2 1 + y.2 2)
  rw [octonionMatrixMul_atomB_left, octonionMatrixMul_atomB_right]
  have h1 : (1 : Fin 3).val < 2 := by decide
  have h2 : ¬ ((2 : Fin 3).val < 2) := by decide
  simp only [h1, h2, ↓reduceIte, albertMatrix_02, albertMatrix_12, add_zero]
  module

private theorem jordanMul_atomB_self : jordanMul atomB atomB = atomB := by
  apply albert_ext
  · rw [jordanMul_atomB_fst_0, atomB_fst_0, atomB_snd_0, octonionReal_smul, octonionReal_scalar]
    ring
  · rw [jordanMul_atomB_fst_1, atomB_fst_1, atomB_snd_0, octonionReal_smul, octonionReal_scalar]
    ring
  · rw [jordanMul_atomB_fst_2, atomB_fst_2]
  · rw [jordanMul_atomB_snd_0, atomB_fst_0, atomB_fst_1, atomB_snd_0,
      octonionScalar_eq_smul (1 / 2 + 1 / 2)]
    module
  · rw [jordanMul_atomB_snd_1, atomB_snd_1, atomB_snd_2, add_zero, smul_zero]
  · rw [jordanMul_atomB_snd_2, atomB_snd_1, atomB_snd_2, add_zero, smul_zero]

theorem quadraticMap_atomB (y : Albert) :
    quadraticMap atomB y = tracePairing atomB y • atomB := by
  unfold quadraticMap
  rw [jordanMul_atomB_self, tracePairing_atomB]
  apply albert_ext
  · rw [albert_sub_fst, two_smul, albert_add_fst, albert_smul_fst,
      jordanMul_atomB_fst_0, jordanMul_atomB_fst_0, jordanMul_atomB_snd_0,
      octonionReal_add, octonionReal_smul, octonionReal_smul, octonionReal_scalar, atomB_fst_0]
    ring
  · rw [albert_sub_fst, two_smul, albert_add_fst, albert_smul_fst,
      jordanMul_atomB_fst_1, jordanMul_atomB_fst_1, jordanMul_atomB_snd_0,
      octonionReal_add, octonionReal_smul, octonionReal_smul, octonionReal_scalar, atomB_fst_1]
    ring
  · rw [albert_sub_fst, two_smul, albert_add_fst, albert_smul_fst,
      jordanMul_atomB_fst_2, jordanMul_atomB_fst_2, atomB_fst_2]
    ring
  · rw [albert_sub_snd, two_smul, albert_add_snd, albert_smul_snd,
      jordanMul_atomB_snd_0, jordanMul_atomB_fst_0, jordanMul_atomB_fst_1,
      jordanMul_atomB_snd_0, atomB_snd_0,
      octonionScalar_eq_smul ((y.1 0 + octonionReal (y.2 0)) / 2 + (y.1 1 + octonionReal (y.2 0)) / 2),
      octonionScalar_eq_smul (y.1 0 + y.1 1)]
    module
  · rw [albert_sub_snd, two_smul, albert_add_snd, albert_smul_snd,
      jordanMul_atomB_snd_1, jordanMul_atomB_snd_1, jordanMul_atomB_snd_2,
      atomB_snd_1, smul_zero]
    module
  · rw [albert_sub_snd, two_smul, albert_add_snd, albert_smul_snd,
      jordanMul_atomB_snd_2, jordanMul_atomB_snd_1, jordanMul_atomB_snd_2,
      atomB_snd_2, smul_zero]
    module

/-! ## Section 4: Explicit Faithful Quaternion Embeddings and Rank-One Dyad Bridge -/

structure IsQuatEmbedding (ι : Quaternion ℝ →ₗ[ℝ] Octonion) : Prop where
  map_one : ι 1 = octonionScalar 1
  map_mul : ∀ p q, ι (p * q) = octonionMul (ι p) (ι q)
  map_star : ∀ q, ι (star q) = octonionConj (ι q)
  map_re : ∀ q, octonionReal (ι q) = q.re
  injective : Function.Injective ι

def quatEmbed1 : Quaternion ℝ →ₗ[ℝ] Octonion where
  toFun q := (q, 0)
  map_add' p q := by
    apply Prod.ext
    · rfl
    · exact (add_zero (0 : Quaternion ℝ)).symm
  map_smul' r q := by
    apply Prod.ext
    · rfl
    · exact (smul_zero r).symm

theorem quatEmbed1_apply (q : Quaternion ℝ) : quatEmbed1 q = (q, 0) := rfl

theorem quatEmbed1_isQuatEmbedding : IsQuatEmbedding quatEmbed1 where
  map_one := by
    apply Prod.ext
    · apply Quaternion.ext <;> rfl
    · rfl
  map_mul p q := by
    rw [quatEmbed1_apply, quatEmbed1_apply, quatEmbed1_apply]
    apply Prod.ext
    · change p * q = p * q - star (0 : Quaternion ℝ) * 0
      simp
    · change (0 : Quaternion ℝ) = 0 * p + 0 * star q
      simp
  map_star q := by
    rw [quatEmbed1_apply, quatEmbed1_apply]
    apply Prod.ext
    · rfl
    · change (0 : Quaternion ℝ) = -0
      simp
  map_re q := rfl
  injective p q h := (Prod.ext_iff.mp h).1

def quatEmbed2 : Quaternion ℝ →ₗ[ℝ] Octonion where
  toFun q := (⟨q.re, 0, q.imI, 0⟩, ⟨q.imJ, 0, q.imK, 0⟩)
  map_add' p q := by
    apply Prod.ext
    · change (⟨(p + q).re, 0, (p + q).imI, 0⟩ : Quaternion ℝ) =
        ⟨p.re, 0, p.imI, 0⟩ + ⟨q.re, 0, q.imI, 0⟩
      apply Quaternion.ext <;> simp
    · change (⟨(p + q).imJ, 0, (p + q).imK, 0⟩ : Quaternion ℝ) =
        ⟨p.imJ, 0, p.imK, 0⟩ + ⟨q.imJ, 0, q.imK, 0⟩
      apply Quaternion.ext <;> simp
  map_smul' r q := by
    apply Prod.ext
    · change (⟨(r • q).re, 0, (r • q).imI, 0⟩ : Quaternion ℝ) =
        r • ⟨q.re, 0, q.imI, 0⟩
      apply Quaternion.ext <;> simp
    · change (⟨(r • q).imJ, 0, (r • q).imK, 0⟩ : Quaternion ℝ) =
        r • ⟨q.imJ, 0, q.imK, 0⟩
      apply Quaternion.ext <;> simp

theorem quatEmbed2_apply (q : Quaternion ℝ) :
    quatEmbed2 q = (⟨q.re, 0, q.imI, 0⟩, ⟨q.imJ, 0, q.imK, 0⟩) := rfl

theorem quatEmbed2_isQuatEmbedding : IsQuatEmbedding quatEmbed2 where
  map_one := by
    rw [quatEmbed2_apply]
    apply Prod.ext <;> apply Quaternion.ext <;> simp [octonionScalar]
  map_mul p q := by
    rw [quatEmbed2_apply, quatEmbed2_apply, quatEmbed2_apply]
    apply Prod.ext <;> apply Quaternion.ext <;> simp [octonionMul] <;> ring
  map_star q := by
    rw [quatEmbed2_apply, quatEmbed2_apply]
    apply Prod.ext <;> apply Quaternion.ext <;> simp [octonionConj]
  map_re q := rfl
  injective p q h := by
    rw [quatEmbed2_apply, quatEmbed2_apply] at h
    have hre : p.re = q.re := congrArg (fun z : Octonion => z.1.re) h
    have himI : p.imI = q.imI := congrArg (fun z : Octonion => z.1.imJ) h
    have himJ : p.imJ = q.imJ := congrArg (fun z : Octonion => z.2.re) h
    have himK : p.imK = q.imK := congrArg (fun z : Octonion => z.2.imJ) h
    apply Quaternion.ext
    · exact hre
    · exact himI
    · exact himJ
    · exact himK

def quatNormSq (q : Quaternion ℝ) : ℝ :=
  q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

private theorem quat_star_mul_self (q : Quaternion ℝ) :
    star q * q = quatNormSq q • (1 : Quaternion ℝ) := by
  apply Quaternion.ext <;> simp [quatNormSq] <;> ring

private theorem quat_mul_star_self (q : Quaternion ℝ) :
    q * star q = quatNormSq q • (1 : Quaternion ℝ) := by
  apply Quaternion.ext <;> simp [quatNormSq] <;> ring

private theorem quat_mul_star_re (q : Quaternion ℝ) :
    (q * star q).re = quatNormSq q := by
  simp [quatNormSq]
  ring

private theorem quat_eq_re_smul_one_of_star_eq {q : Quaternion ℝ} (hq : star q = q) :
    q = q.re • (1 : Quaternion ℝ) := by
  have hi : -q.imI = q.imI := congrArg (fun z : Quaternion ℝ => z.imI) hq
  have hj : -q.imJ = q.imJ := congrArg (fun z : Quaternion ℝ => z.imJ) hq
  have hk : -q.imK = q.imK := congrArg (fun z : Quaternion ℝ => z.imK) hq
  apply Quaternion.ext
  · simp
  · simp; linarith
  · simp; linarith
  · simp; linarith

private def IsQuatHermitian (M : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) : Prop :=
  ∀ i j, star (M j i) = M i j

private def quatToAlbert (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (M : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) : Albert :=
  (fun i => (M i i).re, ![ι (M 0 1), ι (M 0 2), ι (M 1 2)])

private def quatSymMul (M N : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) :
    Matrix (Fin 3) (Fin 3) (Quaternion ℝ) :=
  (1 / 2 : ℝ) • (M * N + N * M)

private theorem isQuatHermitian_symMul {M N : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)}
    (hM : IsQuatHermitian M) (hN : IsQuatHermitian N) :
    IsQuatHermitian (quatSymMul M N) := by
  intro i j
  change star ((1 / 2 : ℝ) • ((M * N) j i + (N * M) j i)) =
    (1 / 2 : ℝ) • ((M * N) i j + (N * M) i j)
  rw [quat_star_smul, star_add]
  have hMN : star ((M * N) j i) = (N * M) i j := by
    simp only [Matrix.mul_apply, Fin.sum_univ_three, star_add, star_mul, hM _ _, hN _ _]
  have hNM : star ((N * M) j i) = (M * N) i j := by
    simp only [Matrix.mul_apply, Fin.sum_univ_three, star_add, star_mul, hM _ _, hN _ _]
  rw [hMN, hNM, add_comm]

private theorem isQuatHermitian_mul_self {M : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)}
    (hM : IsQuatHermitian M) : IsQuatHermitian (M * M) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, star_add, star_mul, hM _ _]

private theorem albertMatrix_quatToAlbert (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hι : IsQuatEmbedding ι) {M : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)}
    (hM : IsQuatHermitian M) (i j : Fin 3) :
    albertMatrix (quatToAlbert ι M) i j = ι (M i j) := by
  have hdiag : ∀ k : Fin 3, octonionScalar (M k k).re = ι (M k k) := by
    intro k
    have hk : M k k = (M k k).re • (1 : Quaternion ℝ) :=
      quat_eq_re_smul_one_of_star_eq (hM k k)
    calc
      octonionScalar (M k k).re = (M k k).re • octonionScalar 1 := octonionScalar_eq_smul _
      _ = (M k k).re • ι 1 := by rw [hι.map_one]
      _ = ι ((M k k).re • (1 : Quaternion ℝ)) := (ι.map_smul _ _).symm
      _ = ι (M k k) := by rw [← hk]
  fin_cases i <;> fin_cases j
  · exact hdiag 0
  · rfl
  · rfl
  · change octonionConj (ι (M 0 1)) = ι (M 1 0)
    rw [← hι.map_star, hM]
  · exact hdiag 1
  · rfl
  · change octonionConj (ι (M 0 2)) = ι (M 2 0)
    rw [← hι.map_star, hM]
  · change octonionConj (ι (M 1 2)) = ι (M 2 1)
    rw [← hι.map_star, hM]
  · exact hdiag 2

private theorem jordanMul_quatToAlbert (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hι : IsQuatEmbedding ι) {M N : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)}
    (hM : IsQuatHermitian M) (hN : IsQuatHermitian N) :
    jordanMul (quatToAlbert ι M) (quatToAlbert ι N) =
      quatToAlbert ι (quatSymMul M N) := by
  have hmul :
      ∀ (A B : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)),
        IsQuatHermitian A → IsQuatHermitian B → ∀ i j : Fin 3,
          octonionMatrixMul (albertMatrix (quatToAlbert ι A))
            (albertMatrix (quatToAlbert ι B)) i j = ι ((A * B) i j) := by
    intro A B hA hB i j
    unfold octonionMatrixMul
    simp only [albertMatrix_quatToAlbert ι hι hA, albertMatrix_quatToAlbert ι hι hB,
      ← hι.map_mul, ← map_sum, Matrix.mul_apply]
  unfold jordanMul albertCoordinates
  apply albert_ext
  · change (1 / 2 : ℝ) * octonionReal
        (octonionMatrixMul (albertMatrix (quatToAlbert ι M))
            (albertMatrix (quatToAlbert ι N)) 0 0 +
          octonionMatrixMul (albertMatrix (quatToAlbert ι N))
            (albertMatrix (quatToAlbert ι M)) 0 0) = (quatSymMul M N 0 0).re
    rw [hmul M N hM hN 0 0, hmul N M hN hM 0 0, ← map_add, hι.map_re]
    rfl
  · change (1 / 2 : ℝ) * octonionReal
        (octonionMatrixMul (albertMatrix (quatToAlbert ι M))
            (albertMatrix (quatToAlbert ι N)) 1 1 +
          octonionMatrixMul (albertMatrix (quatToAlbert ι N))
            (albertMatrix (quatToAlbert ι M)) 1 1) = (quatSymMul M N 1 1).re
    rw [hmul M N hM hN 1 1, hmul N M hN hM 1 1, ← map_add, hι.map_re]
    rfl
  · change (1 / 2 : ℝ) * octonionReal
        (octonionMatrixMul (albertMatrix (quatToAlbert ι M))
            (albertMatrix (quatToAlbert ι N)) 2 2 +
          octonionMatrixMul (albertMatrix (quatToAlbert ι N))
            (albertMatrix (quatToAlbert ι M)) 2 2) = (quatSymMul M N 2 2).re
    rw [hmul M N hM hN 2 2, hmul N M hN hM 2 2, ← map_add, hι.map_re]
    rfl
  · change (1 / 2 : ℝ) •
        (octonionMatrixMul (albertMatrix (quatToAlbert ι M))
            (albertMatrix (quatToAlbert ι N)) 0 1 +
          octonionMatrixMul (albertMatrix (quatToAlbert ι N))
            (albertMatrix (quatToAlbert ι M)) 0 1) = ι (quatSymMul M N 0 1)
    rw [hmul M N hM hN 0 1, hmul N M hN hM 0 1, ← map_add, ← ι.map_smul]
    rfl
  · change (1 / 2 : ℝ) •
        (octonionMatrixMul (albertMatrix (quatToAlbert ι M))
            (albertMatrix (quatToAlbert ι N)) 0 2 +
          octonionMatrixMul (albertMatrix (quatToAlbert ι N))
            (albertMatrix (quatToAlbert ι M)) 0 2) = ι (quatSymMul M N 0 2)
    rw [hmul M N hM hN 0 2, hmul N M hN hM 0 2, ← map_add, ← ι.map_smul]
    rfl
  · change (1 / 2 : ℝ) •
        (octonionMatrixMul (albertMatrix (quatToAlbert ι M))
            (albertMatrix (quatToAlbert ι N)) 1 2 +
          octonionMatrixMul (albertMatrix (quatToAlbert ι N))
            (albertMatrix (quatToAlbert ι M)) 1 2) = ι (quatSymMul M N 1 2)
    rw [hmul M N hM hN 1 2, hmul N M hN hM 1 2, ← map_add, ← ι.map_smul]
    rfl

private theorem quatSymMul_self (M : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) :
    quatSymMul M M = M * M := by
  unfold quatSymMul
  apply Matrix.ext
  intro i j
  change (1 / 2 : ℝ) • ((M * M) i j + (M * M) i j) = (M * M) i j
  rw [← two_smul ℝ ((M * M) i j), smul_smul]
  norm_num

private theorem quadraticMap_quatToAlbert (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (hι : IsQuatEmbedding ι) {M N : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)}
    (hM : IsQuatHermitian M) (hN : IsQuatHermitian N) :
    quadraticMap (quatToAlbert ι M) (quatToAlbert ι N) =
      quatToAlbert ι (M * N * M) := by
  unfold quadraticMap
  rw [jordanMul_quatToAlbert ι hι hM hN,
    jordanMul_quatToAlbert ι hι hM (isQuatHermitian_symMul hM hN),
    jordanMul_quatToAlbert ι hι hM hM,
    quatSymMul_self M,
    jordanMul_quatToAlbert ι hι (isQuatHermitian_mul_self hM) hN]
  have hlin :
      2 • quatToAlbert ι (quatSymMul M (quatSymMul M N)) -
        quatToAlbert ι (quatSymMul (M * M) N) =
      quatToAlbert ι ((2 : ℝ) • quatSymMul M (quatSymMul M N) - quatSymMul (M * M) N) := by
    apply Prod.ext <;> funext idx
    · rw [albert_sub_fst, two_smul, albert_add_fst]
      change (quatSymMul M (quatSymMul M N) idx idx).re +
          (quatSymMul M (quatSymMul M N) idx idx).re - (quatSymMul (M * M) N idx idx).re =
        ((2 : ℝ) • (quatSymMul M (quatSymMul M N) idx idx) - quatSymMul (M * M) N idx idx).re
      simp
      ring
    · rw [albert_sub_snd, two_smul, albert_add_snd]
      fin_cases idx <;> simp [quatToAlbert, two_smul, ι.map_sub]
  rw [hlin]
  congr 1
  unfold quatSymMul
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul, smul_smul, ← mul_assoc]
  have hhalf : (2 : ℝ) * (1 / 2 : ℝ) * (1 / 2 : ℝ) = (1 / 2 : ℝ) := by norm_num
  rw [hhalf, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← smul_sub]
  have hcancel :
      (M * (M * N) + M * (N * M) + (M * (N * M) + N * (M * M))) -
          (M * (M * N) + N * (M * M)) =
        (2 : ℝ) • (M * (N * M)) := by
    rw [two_smul ℝ (M * (N * M))]
    abel
  rw [Matrix.mul_assoc M M N, hcancel, smul_smul]
  norm_num

private def quatDyadMat (u : Fin 3 → Quaternion ℝ) :
    Matrix (Fin 3) (Fin 3) (Quaternion ℝ) :=
  Matrix.of (fun i j => u i * star (u j))

private theorem isQuatHermitian_quatDyadMat (u : Fin 3 → Quaternion ℝ) :
    IsQuatHermitian (quatDyadMat u) := by
  intro i j
  simp [quatDyadMat, star_mul, star_star]

private theorem quatDyadMat_mul_self (u : Fin 3 → Quaternion ℝ) :
    quatDyadMat u * quatDyadMat u = (∑ k : Fin 3, quatNormSq (u k)) • quatDyadMat u := by
  apply Matrix.ext
  intro i j
  simp only [quatDyadMat, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply]
  have hsum :
      ∑ k : Fin 3, (u i * star (u k)) * (u k * star (u j)) =
        u i * (∑ k : Fin 3, star (u k) * u k) * star (u j) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [mul_assoc]
  rw [hsum]
  have hnorm :
      ∑ k : Fin 3, star (u k) * u k = (∑ k : Fin 3, quatNormSq (u k)) • (1 : Quaternion ℝ) := by
    simp only [quat_star_mul_self, ← Finset.sum_smul]
  rw [hnorm, mul_smul_comm, mul_one, smul_mul_assoc]

private theorem quatDyadMat_triple (u v : Fin 3 → Quaternion ℝ) :
    quatDyadMat u * quatDyadMat v * quatDyadMat u =
      quatNormSq (∑ k : Fin 3, star (u k) * v k) • quatDyadMat u := by
  let c : Quaternion ℝ := ∑ k : Fin 3, star (u k) * v k
  have hc_star : ∑ l : Fin 3, star (v l) * u l = star c := by
    dsimp only [c]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, star_add, star_add,
      star_mul, star_mul, star_mul, star_star, star_star, star_star]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, quatDyadMat, Matrix.of_apply, Matrix.smul_apply]
  have hleft : ∀ l : Fin 3,
      ∑ k : Fin 3, (u i * star (u k)) * (v k * star (v l)) = u i * c * star (v l) := by
    intro l
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [mul_assoc]
  simp_rw [hleft]
  have hright :
      ∑ l : Fin 3, (u i * c * star (v l)) * (u l * star (u j)) =
        u i * (c * (∑ l : Fin 3, star (v l) * u l)) * star (u j) := by
    symm
    calc
      u i * (c * (∑ l : Fin 3, star (v l) * u l)) * star (u j)
          = u i * (∑ l : Fin 3, c * (star (v l) * u l)) * star (u j) := by rw [Finset.mul_sum]
      _ = (∑ l : Fin 3, u i * (c * (star (v l) * u l))) * star (u j) := by rw [Finset.mul_sum]
      _ = ∑ l : Fin 3, (u i * (c * (star (v l) * u l))) * star (u j) := by rw [Finset.sum_mul]
      _ = ∑ l : Fin 3, (u i * c * star (v l)) * (u l * star (u j)) := by
        refine Finset.sum_congr rfl ?_
        intro l _
        simp only [mul_assoc]
  rw [hright, hc_star, quat_mul_star_self c, mul_smul_comm, mul_one, smul_mul_assoc]

private theorem quatToAlbert_smul (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (r : ℝ) (M : Matrix (Fin 3) (Fin 3) (Quaternion ℝ)) :
    quatToAlbert ι (r • M) = r • quatToAlbert ι M := by
  apply Prod.ext <;> funext idx
  · rw [albert_smul_fst]
    rfl
  · rw [albert_smul_snd]
    fin_cases idx <;> simp [quatToAlbert, ι.map_smul]

def quatDyad (ι : Quaternion ℝ →ₗ[ℝ] Octonion) (u : Fin 3 → Quaternion ℝ) (n : ℝ) : Albert :=
  (1 / n : ℝ) •
    ((fun i => (u i * star (u i)).re),
      ![ι (u 0 * star (u 1)), ι (u 0 * star (u 2)), ι (u 1 * star (u 2))])

private theorem quatDyad_eq_smul_quatToAlbert (ι : Quaternion ℝ →ₗ[ℝ] Octonion)
    (u : Fin 3 → Quaternion ℝ) (n : ℝ) :
    quatDyad ι u n = (1 / n : ℝ) • quatToAlbert ι (quatDyadMat u) := rfl

theorem quatDyad_isAtom (ι : Quaternion ℝ →ₗ[ℝ] Octonion) (hι : IsQuatEmbedding ι)
    (u : Fin 3 → Quaternion ℝ) (n : ℝ) (hn : n ≠ 0)
    (hu : ∑ i : Fin 3, quatNormSq (u i) = n) : IsAtom (quatDyad ι u n) := by
  constructor
  · rw [quatDyad_eq_smul_quatToAlbert, jordanMul_smul_left, jordanMul_smul_right,
      jordanMul_quatToAlbert ι hι (isQuatHermitian_quatDyadMat u) (isQuatHermitian_quatDyadMat u),
      quatSymMul_self, quatDyadMat_mul_self, hu, quatToAlbert_smul, smul_smul, smul_smul]
    congr 1
    rw [one_div, mul_assoc, inv_mul_cancel₀ hn, mul_one]
  · unfold albertTrace
    rw [quatDyad_eq_smul_quatToAlbert, Fin.sum_univ_three,
      albert_smul_fst, albert_smul_fst, albert_smul_fst]
    change (1 / n : ℝ) * (u 0 * star (u 0)).re + (1 / n : ℝ) * (u 1 * star (u 1)).re +
        (1 / n : ℝ) * (u 2 * star (u 2)).re = 1
    simp only [quat_mul_star_re]
    have hsum : quatNormSq (u 0) + quatNormSq (u 1) + quatNormSq (u 2) = n := by
      rw [← hu, Fin.sum_univ_three]
    rw [← mul_add, ← mul_add, hsum, one_div, inv_mul_cancel₀ hn]

theorem quadraticMap_quatDyad (ι : Quaternion ℝ →ₗ[ℝ] Octonion) (hι : IsQuatEmbedding ι)
    (u v : Fin 3 → Quaternion ℝ) (nu nv : ℝ) (hnu : nu ≠ 0)
    (hu : ∑ i : Fin 3, quatNormSq (u i) = nu) :
    quadraticMap (quatDyad ι u nu) (quatDyad ι v nv) =
      (quatNormSq (∑ i : Fin 3, star (u i) * v i) / (nu * nv)) • quatDyad ι u nu := by
  let _ := hnu
  let _ := hu
  rw [quatDyad_eq_smul_quatToAlbert ι u nu, quatDyad_eq_smul_quatToAlbert ι v nv,
    quadraticMap_smul_left, quadraticMap_smul_right,
    quadraticMap_quatToAlbert ι hι (isQuatHermitian_quatDyadMat u) (isQuatHermitian_quatDyadMat v),
    quatDyadMat_triple, quatToAlbert_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end AlbertSequential
