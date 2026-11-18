/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.SecondOrderQuotient

/-! # Second-order neighbourhood, part (a) (`prop:so:kernel`(a)): `E₁ = W ⊕ tJ` is special

`D₁ = ℂ_i ⊕ t𝕆` (`t² = 0`), modelled as `D1` with `(c₀, o₁)(d₀, p₁) = (c₀d₀, c₀p₁ + o₁d₀)`; it is an
associative unital real algebra (`D1.instRing`).  `E₁ = {(x₀, x₁) ∈ J × J | x₀ ∈ W}` with the product
`(x₀∘y₀, x₀∘y₁ + x₁∘y₀)`; the entrywise map `red1 : E₁ → M₃(D₁)` is an injective Jordan homomorphism
(`red1_jordan`, `red1_injective`). -/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

noncomputable section

@[simp] theorem octonionScalar_inj'' (a b : ℝ) : octonionScalar a = octonionScalar b ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun o : Octonion => o.1.re) h
    simpa using this
  · rintro rfl; rfl

@[ext] structure D1 where
  c0 : ℂ
  o1 : Octonion

namespace D1

instance : Zero D1 := ⟨⟨0, 0⟩⟩
instance : One D1 := ⟨⟨1, 0⟩⟩
instance : Add D1 := ⟨fun x y => ⟨x.c0 + y.c0, x.o1 + y.o1⟩⟩
instance : Neg D1 := ⟨fun x => ⟨-x.c0, -x.o1⟩⟩
instance : Sub D1 := ⟨fun x y => ⟨x.c0 - y.c0, x.o1 - y.o1⟩⟩
instance : SMul ℕ D1 := ⟨fun n x => ⟨n • x.c0, n • x.o1⟩⟩
instance : SMul ℤ D1 := ⟨fun n x => ⟨n • x.c0, n • x.o1⟩⟩
instance : SMul ℝ D1 := ⟨fun r x => ⟨r • x.c0, r • x.o1⟩⟩
instance : Mul D1 := ⟨fun x y => ⟨x.c0 * y.c0, octonionMul (cO x.c0) y.o1 + octonionMul x.o1 (cO y.c0)⟩⟩

@[simp] theorem zero_c0 : (0 : D1).c0 = 0 := rfl
@[simp] theorem zero_o1 : (0 : D1).o1 = 0 := rfl
@[simp] theorem one_c0 : (1 : D1).c0 = 1 := rfl
@[simp] theorem one_o1 : (1 : D1).o1 = 0 := rfl
@[simp] theorem add_c0 (x y : D1) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_o1 (x y : D1) : (x + y).o1 = x.o1 + y.o1 := rfl
@[simp] theorem smul_c0 (r : ℝ) (x : D1) : (r • x).c0 = r • x.c0 := rfl
@[simp] theorem smul_o1 (r : ℝ) (x : D1) : (r • x).o1 = r • x.o1 := rfl
@[simp] theorem mul_c0 (x y : D1) : (x * y).c0 = x.c0 * y.c0 := rfl
@[simp] theorem mul_o1 (x y : D1) :
    (x * y).o1 = octonionMul (cO x.c0) y.o1 + octonionMul x.o1 (cO y.c0) := rfl

def toPair (x : D1) : ℂ × Octonion := (x.c0, x.o1)

theorem toPair_injective : Function.Injective toPair := by
  intro x y h
  simp only [toPair, Prod.mk.injEq] at h
  ext1 <;> simp [h]

instance instAddCommGroup : AddCommGroup D1 :=
  Function.Injective.addCommGroup toPair toPair_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

def toPairHom : D1 →+ ℂ × Octonion := ⟨⟨toPair, rfl⟩, fun _ _ => rfl⟩

instance instModule : Module ℝ D1 :=
  Function.Injective.module ℝ toPairHom toPair_injective (fun _ _ => rfl)

theorem ext_coords {x y : D1} (h1 : x.c0.re = y.c0.re) (h2 : x.c0.im = y.c0.im)
    (h3 : x.o1 = y.o1) : x = y := by
  ext1
  · exact Complex.ext h1 h2
  · exact h3

macro "d1_tac" : tactic => `(tactic| (
  apply ext_coords <;> (try apply oct_ext') <;>
    (try simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im]) <;> (try ring)))

theorem mul_assoc' (x y z : D1) : x * y * z = x * (y * z) := by d1_tac
theorem left_distrib' (x y z : D1) : x * (y + z) = x * y + x * z := by d1_tac
theorem right_distrib' (x y z : D1) : (x + y) * z = x * z + y * z := by d1_tac
theorem zero_mul' (x : D1) : 0 * x = 0 := by d1_tac
theorem mul_zero' (x : D1) : x * 0 = 0 := by d1_tac
theorem one_mul' (x : D1) : 1 * x = x := by d1_tac
theorem mul_one' (x : D1) : x * 1 = x := by d1_tac

instance instRing : Ring D1 where
  __ := instAddCommGroup
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul := zero_mul'
  mul_zero := mul_zero'

end D1

/-- `E₁ = W ⊕ tJ` inside `J × J`. -/
def E1 : Submodule ℝ (Albert × Albert) := Submodule.comap (LinearMap.fst ℝ Albert Albert) Wso

/-- The Jordan product of `J[t]/(t²)`. -/
def j2mul (x y : Albert × Albert) : Albert × Albert :=
  (jordanMul x.1 y.1, jordanMul x.1 y.2 + jordanMul x.2 y.1)

/-- Entrywise map `E₁ → M₃(D₁)`. -/
def red1 (x : Albert × Albert) : Matrix (Fin 3) (Fin 3) D1 :=
  fun i j => ⟨oC (albertMatrix x.1 i j), albertMatrix x.2 i j⟩

set_option maxHeartbeats 100000000 in
theorem red1_jordan_00 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 0 0 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 0 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem red1_jordan_01 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 0 1 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 0 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem red1_jordan_02 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 0 2 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 0 2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem red1_jordan_10 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 1 0 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 1 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem red1_jordan_11 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 1 1 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 1 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem red1_jordan_12 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 1 2 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 1 2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem red1_jordan_20 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 2 0 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 2 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem red1_jordan_21 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 2 1 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 2 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem red1_jordan_22 (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) 2 2 = ((1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x)) 2 2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply D1.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [red1, j2mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

/-- `prop:so:kernel`(a): `red1` is a Jordan homomorphism on `E₁` into `M₃(D₁)⁺`. -/
theorem red1_jordan (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1) :
    red1 (j2mul x y) = (1 / 2 : ℝ) • (red1 x * red1 y + red1 y * red1 x) := by
  ext1 i j
  fin_cases i <;> fin_cases j
  · exact red1_jordan_00 x y hx hy
  · exact red1_jordan_01 x y hx hy
  · exact red1_jordan_02 x y hx hy
  · exact red1_jordan_10 x y hx hy
  · exact red1_jordan_11 x y hx hy
  · exact red1_jordan_12 x y hx hy
  · exact red1_jordan_20 x y hx hy
  · exact red1_jordan_21 x y hx hy
  · exact red1_jordan_22 x y hx hy

/-- `red1` is injective on `E₁`. -/
theorem red1_injective (x y : Albert × Albert) (hx : x ∈ E1) (hy : y ∈ E1)
    (h : red1 x = red1 y) : x = y := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  have e : ∀ i j, red1 x i j = red1 y i j := fun i j => by rw [h]
  have e00 := e 0 0; have e11 := e 1 1; have e22 := e 2 2
  have e01 := e 0 1; have e02 := e 0 2; have e12 := e 1 2
  simp only [red1, albertMatrix, D1.mk.injEq] at e00 e11 e22 e01 e02 e12
  simp [oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, Complex.ext_iff, Prod.ext_iff, Quaternion.ext_iff] at e00 e11 e22 e01 e02 e12
  apply Prod.ext
  · apply albert_ext' <;> (try apply oct_ext') <;> simp_all [Quaternion.ext_iff]
  · apply albert_ext' <;> (try apply oct_ext') <;> simp_all [Quaternion.ext_iff]

end

end AlbertSequential.AppF
