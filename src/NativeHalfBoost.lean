/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCornerLorentz
public import TaggedDilationDefect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-! A positive boost and an orthogonal factor of the actual native Kraus lift. -/
@[expose] public section
noncomputable section

open Matrix
open scoped Matrix

namespace AlbertSequential.NativeAnalysis

abbrev NativeSpinorMatrix := Matrix SpinorCoordinate SpinorCoordinate ℝ

theorem nativeHalfMatrix_injective (p : Albert) (hp : IsAtom p) :
    Function.Injective (nativeHalfMatrix p hp) := by
  intro x y h
  apply sub_eq_zero.mp
  let d := x - y
  have hd : nativeHalfMatrix p hp d = 0 := by rw [show d = x - y from rfl, map_sub, h, sub_self]
  have ht := nativeHalfMatrix_trace_product p hp d d
  rw [hd, Matrix.zero_mul, Matrix.trace_zero] at ht
  have hz : tracePairing (d : Albert) d = 0 := by linarith
  exact Subtype.ext ((tracePairing_self_eq_zero _).mp hz)

/-- The corner element whose matrix is the positive polar factor of the native lift. -/
def nativeCornerBoostRoot (p q : Albert) (hq : IsAtom q) : nativePeirceZero q :=
  nativeCornerUnit q hq.1 -
    (1 + Real.sqrt (tracePairing p q))⁻¹ • nativeCornerProjection q hq p

private theorem nativeCornerNoUpdate_unit_eq_sub (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    nativeCornerNoUpdate p q hq (nativeCornerUnit p hp.1) =
      nativeCornerUnit q hq.1 - nativeCornerProjection q hq p := by
  change nativeCornerProjection q hq (albertUnit - p) = _
  rw [map_sub, nativeCornerProjection_unit]

theorem nativeCornerBoostRoot_positive (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    IsPositive (nativeCornerBoostRoot p q hq) := by
  let r := Real.sqrt (tracePairing p q)
  let a := (1 + r)⁻¹
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have ha : 0 < a := inv_pos.mpr (by positivity)
  have hcoef : 1 - a = r * a := by
    change 1 - (1 + r)⁻¹ = r * (1 + r)⁻¹
    field_simp [show (1 + r : ℝ) ≠ 0 by positivity]
    ring
  have hu : IsPositive (nativeCornerUnit q hq.1 : Albert) :=
    isPositive_idempotent _ (complementary_idempotent q hq.1)
  have hu' : IsPositive (nativeCornerUnit p hp.1 : Albert) :=
    isPositive_idempotent _ (complementary_idempotent p hp.1)
  have hy := nativeCornerNoUpdate_preserves_positive p q hq (nativeCornerUnit p hp.1) hu'
  rw [nativeCornerNoUpdate_unit_eq_sub p q hp hq] at hy
  have he : nativeCornerBoostRoot p q hq =
      (1 - a) • nativeCornerUnit q hq.1 +
        a • (nativeCornerUnit q hq.1 - nativeCornerProjection q hq p) := by
    change nativeCornerUnit q hq.1 - a • nativeCornerProjection q hq p = _
    module
  rw [he]
  exact isPositive_add _ _ (isPositive_smul _ _ (by rw [hcoef]; positivity) hu)
    (isPositive_smul _ _ ha.le hy)

theorem nativeHalfMatrix_boostRoot (p q : Albert) (hq : IsAtom q) :
    nativeHalfMatrix q hq (nativeCornerBoostRoot p q hq) =
      1 - (1 + Real.sqrt (tracePairing p q))⁻¹ • nativeCornerYesEffect q hq p := by
  simp only [nativeCornerBoostRoot, map_sub, map_smul, nativeHalfMatrix_unit, nativeCornerYesEffect]

private theorem boost_scalar_coefficients (r : ℝ) (hr : 0 < r) :
    let a := (1 + r)⁻¹
    let b := a / r
    a + a - a * a * (1 - r^2) = 1 ∧ b - a - b * a * (1 - r^2) = 0 := by
  have h₁ : (1 + r : ℝ) ≠ 0 := by positivity
  constructor
  · field_simp [h₁]
    ring
  · field_simp [h₁, hr.ne']
    ring

private theorem boost_matrices (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : 0 < tracePairing p q) :
    let o := tracePairing p q
    let r := Real.sqrt o
    let a := (1 + r)⁻¹
    let b := a / r
    let C := nativeCornerYesEffect q hq p
    let B := 1 - a • C
    let N := 1 + b • C
    B * B = 1 - C ∧ N * B = 1 ∧ N.transpose = N := by
  intro o r a b C B N
  have hr : r ^ 2 = o := Real.sq_sqrt ho.le
  have hcoef := boost_scalar_coefficients r (Real.sqrt_pos.mpr ho)
  change a + a - a * a * (1 - r^2) = 1 ∧ b - a - b * a * (1 - r^2) = 0 at hcoef
  rw [hr] at hcoef
  have hca : -(a + a) + a * a * (1 - o) = -1 := by linarith [hcoef.1]
  have hC : C * C = (1 - o) • C := by
    change nativeCornerYesEffect q hq p * nativeCornerYesEffect q hq p =
      (1 - tracePairing p q) • nativeCornerYesEffect q hq p
    rw [tracePairing_comm p q]
    exact (nativeCornerYesEffect_square_trace q p hq hp).1
  have hCs : C.transpose = C := nativeHalfMatrix_symmetric q hq _
  refine ⟨?_, ?_, ?_⟩
  · calc
      B * B = 1 + (-(a + a) + a * a * (1-o)) • C := by
        dsimp only [B]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
          smul_mul_assoc, mul_smul_comm, hC, smul_smul]
        module
      _ = 1 - C := by rw [hca, neg_one_smul, sub_eq_add_neg]
  · calc
      N * B = 1 + (b - a - b * a * (1-o)) • C := by
        dsimp only [N, B]
        simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
          smul_mul_assoc, mul_smul_comm, hC, smul_smul]
        module
      _ = 1 := by rw [hcoef.2, zero_smul, add_zero]
  · change (1 + b • C).transpose = 1 + b • C
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hCs]

theorem nativeHalfBoostRoot_square (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : 0 < tracePairing p q) :
    nativeCornerProduct q hq.1 (nativeCornerBoostRoot p q hq) (nativeCornerBoostRoot p q hq) =
      nativeCornerNoUpdate p q hq (nativeCornerUnit p hp.1) := by
  apply nativeHalfMatrix_injective q hq
  rw [nativeHalfMatrix_square, nativeHalfMatrix_boostRoot, (boost_matrices p q hp hq ho).1,
    nativeCornerNoUpdate_unit_eq_sub p q hp hq, map_sub, nativeHalfMatrix_unit]
  rfl

/-- The actual native lift factors as the positive boost of the printed construction
and an orthogonal matrix. Its two Gram formulas use the same native corner units. -/
theorem nativePositiveOverlapKraus_boost_factorization (p q : Albert) (hp : IsAtom p)
    (hq : IsAtom q) (ho : 0 < tracePairing p q) :
    let A := nativePositiveOverlapKraus p hp q hq
    let c := nativeCornerBoostRoot p q hq
    let B := nativeHalfMatrix q hq c
    let F := nativeHalfMatrix q hq (nativeCornerNoUpdate p q hq (nativeCornerUnit p hp.1))
    ∃ S : NativeSpinorMatrix, S.transpose * S = 1 ∧ S * S.transpose = 1 ∧
      A = B * S ∧ A * A.transpose = F ∧ A.transpose * A = S.transpose * F * S := by
  intro A c B F
  let o := tracePairing p q
  let r := Real.sqrt o
  let a := (1 + r)⁻¹
  let N := (1 : NativeSpinorMatrix) + (a / r) • nativeCornerYesEffect q hq p
  let S := N * A
  have hBs : B.transpose = B := nativeHalfMatrix_symmetric q hq c
  have hNB : N * B = 1 := by
    change N * nativeHalfMatrix q hq (nativeCornerBoostRoot p q hq) = 1
    rw [nativeHalfMatrix_boostRoot]
    exact (boost_matrices p q hp hq ho).2.1
  have hNs : N.transpose = N := (boost_matrices p q hp hq ho).2.2
  have hBN : B * N = 1 := mul_eq_one_comm.mp hNB
  have hBB : B * B = F := by
    change nativeHalfMatrix q hq c * nativeHalfMatrix q hq c =
      nativeHalfMatrix q hq (nativeCornerNoUpdate p q hq (nativeCornerUnit p hp.1))
    rw [← nativeHalfMatrix_square, nativeHalfBoostRoot_square p q hp hq ho]
  have hAA : A * A.transpose = F := by
    have h := nativePositiveOverlapKraus_intertwining p hp q hq ho (nativeCornerUnit p hp.1)
    rw [nativeHalfMatrix_unit, Matrix.mul_one] at h
    exact h
  have hSS : S * S.transpose = 1 := by
    calc
      _ = N * (A * A.transpose) * N := by
        simp only [S, Matrix.transpose_mul, hNs, Matrix.mul_assoc]
      _ = N * (B * B) * N := by rw [hAA, ← hBB]
      _ = (N * B) * (B * N) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hNB, hBN, Matrix.one_mul]
  have hA : A = B * S := by
    change A = B * (N * A)
    rw [← Matrix.mul_assoc, hBN, Matrix.one_mul]
  refine ⟨S, mul_eq_one_comm.mp hSS, hSS, hA, hAA, ?_⟩
  calc
    A.transpose * A = (B*S).transpose * (B*S) := by rw [← hA]
    _ = S.transpose * (B*B) * S := by simp only [Matrix.transpose_mul, hBs, Matrix.mul_assoc]
    _ = S.transpose * F * S := by rw [hBB]

/-- The inverse boost remains in the image of the same native corner representation. -/
def nativeCornerBoostReciprocal (p q : Albert) (hq : IsAtom q) : nativePeirceZero q :=
  nativeCornerUnit q hq.1 +
    ((1 + Real.sqrt (tracePairing p q))⁻¹ / Real.sqrt (tracePairing p q)) • nativeCornerProjection q hq p

theorem nativeHalfMatrix_boostReciprocal (p q : Albert) (hq : IsAtom q) :
    nativeHalfMatrix q hq (nativeCornerBoostReciprocal p q hq) =
      1 + ((1 + Real.sqrt (tracePairing p q))⁻¹ / Real.sqrt (tracePairing p q)) • nativeCornerYesEffect q hq p := by
  simp only [nativeCornerBoostReciprocal, map_add, map_smul, nativeHalfMatrix_unit, nativeCornerYesEffect]

/-- The ordinary quadratic representation restricted to the actual native corner. -/
def nativeCornerQuadraticMapLinear (p : Albert) (hp : IsAtom p) (c : nativePeirceZero p) :
    nativePeirceZero p →ₗ[ℝ] nativePeirceZero p :=
  let L := nativeCornerProduct p hp.1
  (2 : ℕ) • ((L c).comp (L c)) - L (L c c)

theorem nativeCornerQuadraticMapLinear_val (p : Albert) (hp : IsAtom p) (c x : nativePeirceZero p) :
    (nativeCornerQuadraticMapLinear p hp c x : Albert) = quadraticMap (c : Albert) x := rfl

theorem nativeHalfMatrix_cornerQuadraticMap (p : Albert) (hp : IsAtom p)
    (c x : nativePeirceZero p) :
    nativeHalfMatrix p hp (nativeCornerQuadraticMapLinear p hp c x) =
      nativeHalfMatrix p hp c * nativeHalfMatrix p hp x * nativeHalfMatrix p hp c := by
  let m := nativeCornerProduct p hp.1
  change nativeHalfMatrix p hp ((2 : ℕ) • m c (m c x) - m (m c c) x) = _
  simp only [m, map_sub, map_nsmul, nativeHalfMatrix_jordan, Matrix.mul_add, Matrix.add_mul,
    smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc]
  module

/-- The normalized rest of the actual transfer, the printed `U_c⁻¹ g`. -/
def nativeCornerBoostRest (p q : Albert) (hq : IsAtom q) :
    nativePeirceZero p →ₗ[ℝ] nativePeirceZero q :=
  (nativeCornerQuadraticMapLinear q hq (nativeCornerBoostReciprocal p q hq)).comp
    (nativeCornerNoUpdate p q hq)

theorem nativePositiveOverlapKraus_boost_rest (p q : Albert) (hp : IsAtom p)
    (hq : IsAtom q) (ho : 0 < tracePairing p q) :
    let A := nativePositiveOverlapKraus p hp q hq
    let c := nativeCornerBoostRoot p q hq
    let B := nativeHalfMatrix q hq c
    let k := nativeCornerBoostRest p q hq
    ∃ S : NativeSpinorMatrix, S.transpose * S = 1 ∧ S * S.transpose = 1 ∧ A = B * S ∧
      (∀ x, S * nativeHalfMatrix p hp x * S.transpose = nativeHalfMatrix q hq (k x)) ∧
      (∀ x, nativeCornerQuadraticMapLinear q hq c (k x) = nativeCornerNoUpdate p q hq x) := by
  intro A c B k
  obtain ⟨S, hs₁, hs₂, hA, _, _⟩ := nativePositiveOverlapKraus_boost_factorization p q hp hq ho
  change A = B * S at hA
  let N := nativeHalfMatrix q hq (nativeCornerBoostReciprocal p q hq)
  have hNB : N * B = 1 := by
    change nativeHalfMatrix q hq (nativeCornerBoostReciprocal p q hq) *
      nativeHalfMatrix q hq (nativeCornerBoostRoot p q hq) = 1
    rw [nativeHalfMatrix_boostReciprocal, nativeHalfMatrix_boostRoot]
    exact (boost_matrices p q hp hq ho).2.1
  have hNs : N.transpose = N := nativeHalfMatrix_symmetric q hq _
  have hBs : B.transpose = B := nativeHalfMatrix_symmetric q hq _
  have hS : N * A = S := by rw [hA, ← Matrix.mul_assoc, hNB, Matrix.one_mul]
  have hk (x : nativePeirceZero p) :
      S * nativeHalfMatrix p hp x * S.transpose = nativeHalfMatrix q hq (k x) := by
    change _ = nativeHalfMatrix q hq
      (nativeCornerQuadraticMapLinear q hq (nativeCornerBoostReciprocal p q hq) (nativeCornerNoUpdate p q hq x))
    rw [nativeHalfMatrix_cornerQuadraticMap, ← nativePositiveOverlapKraus_intertwining p hp q hq ho x]
    simp only [← hS, Matrix.transpose_mul, hNs, Matrix.mul_assoc]
    rfl
  refine ⟨S, hs₁, hs₂, hA, hk, fun x => ?_⟩
  apply nativeHalfMatrix_injective q hq
  rw [nativeHalfMatrix_cornerQuadraticMap, ← hk x, ← nativePositiveOverlapKraus_intertwining p hp q hq ho x]
  change B * (S * nativeHalfMatrix p hp x * S.transpose) * B =
    A * nativeHalfMatrix p hp x * A.transpose
  rw [hA, Matrix.transpose_mul, hBs]
  simp only [Matrix.mul_assoc]

/-- The rest fixes the spin unit and preserves the spin Jordan product. -/
theorem nativeCornerBoostRest_unital_jordan (p q : Albert) (hp : IsAtom p)
    (hq : IsAtom q) (ho : 0 < tracePairing p q) :
    let k := nativeCornerBoostRest p q hq
    k (nativeCornerUnit p hp.1) = nativeCornerUnit q hq.1 ∧
      ∀ x y, k (nativeCornerProduct p hp.1 x y) =
        nativeCornerProduct q hq.1 (k x) (k y) := by
  intro k
  obtain ⟨S, hs, hs', _, hk, _⟩ := nativePositiveOverlapKraus_boost_rest p q hp hq ho
  change ∀ x, S * nativeHalfMatrix p hp x * S.transpose = nativeHalfMatrix q hq (k x) at hk
  constructor
  · apply nativeHalfMatrix_injective q hq
    rw [← hk, nativeHalfMatrix_unit, nativeHalfMatrix_unit, Matrix.mul_one, hs']
  · intro x y
    apply nativeHalfMatrix_injective q hq
    rw [← hk, nativeHalfMatrix_jordan, nativeHalfMatrix_jordan, ← hk x, ← hk y]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, mul_smul_comm, smul_mul_assoc]
    have hg (u : NativeSpinorMatrix) : S.transpose * (S * u) = u := by
      rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
    simp only [hg]

/-- The normalized rest preserves the trace and the Lorentz form. -/
theorem nativeCornerBoostRest_trace_lorentz (p q : Albert) (hp : IsAtom p)
    (hq : IsAtom q) (ho : 0 < tracePairing p q) :
    let k := nativeCornerBoostRest p q hq
    (∀ x, albertTrace (k x) = albertTrace x) ∧
      (∀ x y, nativeCornerLorentzForm (k x) (k y) = nativeCornerLorentzForm x y) := by
  intro k
  obtain ⟨S, hs, _, _, hk, _⟩ := nativePositiveOverlapKraus_boost_rest p q hp hq ho
  change ∀ x, S * nativeHalfMatrix p hp x * S.transpose = nativeHalfMatrix q hq (k x) at hk
  have ht (x : nativePeirceZero p) : albertTrace (k x) = albertTrace x := by
    have h := congrArg Matrix.trace (hk x)
    rw [Matrix.trace_mul_comm (S * nativeHalfMatrix p hp x) S.transpose,
      ← Matrix.mul_assoc, hs, Matrix.one_mul, nativeHalfMatrix_trace, nativeHalfMatrix_trace] at h
    linarith
  refine ⟨ht, fun x y => ?_⟩
  obtain ⟨_, hj⟩ := nativeCornerBoostRest_unital_jordan p q hp hq ho
  change ∀ x y, k (nativeCornerProduct p hp.1 x y) =
    nativeCornerProduct q hq.1 (k x) (k y) at hj
  have htxy := ht (nativeCornerProduct p hp.1 x y)
  rw [hj] at htxy
  change tracePairing (k x : Albert) (k y : Albert) = tracePairing (x : Albert) y at htxy
  unfold nativeCornerLorentzForm
  rw [ht x, ht y, htxy]

end AlbertSequential.NativeAnalysis
