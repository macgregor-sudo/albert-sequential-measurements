/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.SecondOrderKernel
public import AppF.GlennieIngredients
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Matrix.Basic

/-! # Second-order neighbourhood, part (c) (`prop:so:kernel`(c)) and the corollary's core

`D₂/I = ℂ_i ⊕ t𝕆 ⊕ t²ℂ_i` (`I = t²ℂ_i^⊥`), modelled as `Dq` with the product
`(c₀, o₁, c₂)(d₀, p₁, d₂) = (c₀d₀, c₀p₁ + o₁d₀, c₀d₂ + c₂d₀ + π_ℂ(o₁p₁))` (complex numbers act
on octonions through `ℂ ≅ ℂ_i ⊂ 𝕆`).  `Dq` is an associative unital real algebra
(`Dq.instRing`, `Dq.instAlgebra`; associativity is `Dq.mul_assoc'`).  The entrywise
reduction `redq : J₃ → M₃(Dq)` (`x ↦ (π_ℂ x₀, x₁, π_ℂ x₂)` entrywise on the Hermitian
matrices) is a unital Jordan homomorphism on `E₂` (`redq_jordan`, `redq_unit`) whose kernel on
`E₂` is exactly `K = t²W^⊥` (`redq_eq_zero_iff`).

Corollary core (`cor:so:residual`, formal-jet version): every Jordan-polynomial term that
vanishes at all idempotent tuples of every special unital real algebra takes values in `K` at
every tuple of idempotents of `E₂` (`term_value_mem_K`).  The analytic `C³` statement and the
passage `E(c) = 0 ⇒ (vanishing in special algebras)` (paper: factorisation through `σ`) are
not formalised here. -/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

noncomputable section

/-! ## The algebra `Dq = D₂/I` -/

@[ext] structure Dq where
  c0 : ℂ
  o1 : Octonion
  c2 : ℂ

/-- `ℂ ≅ ℂ_i ⊂ 𝕆`. -/
def cO (c : ℂ) : Octonion := (⟨c.re, c.im, 0, 0⟩, 0)
@[simp] theorem cO_fst (c : ℂ) : (cO c).1 = ⟨c.re, c.im, 0, 0⟩ := rfl
@[simp] theorem cO_snd (c : ℂ) : (cO c).2 = 0 := rfl

/-- `π_ℂ : 𝕆 → ℂ`. -/
def oC (o : Octonion) : ℂ := ⟨o.1.re, o.1.imI⟩
@[simp] theorem oC_re (o : Octonion) : (oC o).re = o.1.re := rfl
@[simp] theorem oC_im (o : Octonion) : (oC o).im = o.1.imI := rfl
@[simp] theorem octonionScalar_eq_zero'' (r : ℝ) : octonionScalar r = 0 ↔ r = 0 := by
  constructor
  · intro h
    have := congrArg (fun o : Octonion => o.1.re) h
    simpa using this
  · rintro rfl
    apply oct_ext' <;> simp

@[simp] theorem albert_zero_fst'' (i : Fin 3) : (0 : Albert).1 i = 0 := rfl
@[simp] theorem albert_zero_snd'' (k : Fin 3) : (0 : Albert).2 k = 0 := rfl
@[simp] theorem albertUnit_fst'' (i : Fin 3) : albertUnit.1 i = 1 := rfl
@[simp] theorem albertUnit_snd'' (k : Fin 3) : albertUnit.2 k = 0 := rfl
@[simp] theorem octonionConj_zero'' : octonionConj 0 = 0 := by
  apply oct_ext' <;> simp
attribute [simp] albert_add_fst' albert_add_snd' albert_smul_fst' albert_smul_snd'

namespace Dq

instance : Zero Dq := ⟨⟨0, 0, 0⟩⟩
instance : One Dq := ⟨⟨1, 0, 0⟩⟩
instance : Add Dq := ⟨fun x y => ⟨x.c0 + y.c0, x.o1 + y.o1, x.c2 + y.c2⟩⟩
instance : Neg Dq := ⟨fun x => ⟨-x.c0, -x.o1, -x.c2⟩⟩
instance : Sub Dq := ⟨fun x y => ⟨x.c0 - y.c0, x.o1 - y.o1, x.c2 - y.c2⟩⟩
instance : SMul ℕ Dq := ⟨fun n x => ⟨n • x.c0, n • x.o1, n • x.c2⟩⟩
instance : SMul ℤ Dq := ⟨fun n x => ⟨n • x.c0, n • x.o1, n • x.c2⟩⟩
instance : SMul ℝ Dq := ⟨fun r x => ⟨r • x.c0, r • x.o1, r • x.c2⟩⟩
instance : Mul Dq := ⟨fun x y => ⟨x.c0 * y.c0, octonionMul (cO x.c0) y.o1 + octonionMul x.o1 (cO y.c0),
  x.c0 * y.c2 + x.c2 * y.c0 + oC (octonionMul x.o1 y.o1)⟩⟩

@[simp] theorem zero_c0 : (0 : Dq).c0 = 0 := rfl
@[simp] theorem zero_o1 : (0 : Dq).o1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Dq).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : Dq).c0 = 1 := rfl
@[simp] theorem one_o1 : (1 : Dq).o1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Dq).c2 = 0 := rfl
@[simp] theorem add_c0 (x y : Dq) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_o1 (x y : Dq) : (x + y).o1 = x.o1 + y.o1 := rfl
@[simp] theorem add_c2 (x y : Dq) : (x + y).c2 = x.c2 + y.c2 := rfl
@[simp] theorem neg_c0 (x : Dq) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_o1 (x : Dq) : (-x).o1 = -x.o1 := rfl
@[simp] theorem neg_c2 (x : Dq) : (-x).c2 = -x.c2 := rfl
@[simp] theorem sub_c0 (x y : Dq) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_o1 (x y : Dq) : (x - y).o1 = x.o1 - y.o1 := rfl
@[simp] theorem sub_c2 (x y : Dq) : (x - y).c2 = x.c2 - y.c2 := rfl
@[simp] theorem smul_c0 (r : ℝ) (x : Dq) : (r • x).c0 = r • x.c0 := rfl
@[simp] theorem smul_o1 (r : ℝ) (x : Dq) : (r • x).o1 = r • x.o1 := rfl
@[simp] theorem smul_c2 (r : ℝ) (x : Dq) : (r • x).c2 = r • x.c2 := rfl
@[simp] theorem mul_c0 (x y : Dq) : (x * y).c0 = x.c0 * y.c0 := rfl
@[simp] theorem mul_o1 (x y : Dq) :
    (x * y).o1 = octonionMul (cO x.c0) y.o1 + octonionMul x.o1 (cO y.c0) := rfl
@[simp] theorem mul_c2 (x y : Dq) :
    (x * y).c2 = x.c0 * y.c2 + x.c2 * y.c0 + oC (octonionMul x.o1 y.o1) := rfl

def toTriple (x : Dq) : ℂ × Octonion × ℂ := (x.c0, x.o1, x.c2)

theorem toTriple_injective : Function.Injective toTriple := by
  intro x y h
  simp only [toTriple, Prod.mk.injEq] at h
  ext1 <;> simp [h]

instance instAddCommGroup : AddCommGroup Dq :=
  Function.Injective.addCommGroup toTriple toTriple_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

def toTripleHom : Dq →+ ℂ × Octonion × ℂ := ⟨⟨toTriple, rfl⟩, fun _ _ => rfl⟩

instance instModule : Module ℝ Dq :=
  Function.Injective.module ℝ toTripleHom toTriple_injective (fun _ _ => rfl)

/-- Componentwise extensionality down to real coordinates. -/
theorem ext_coords {x y : Dq} (h1 : x.c0.re = y.c0.re) (h2 : x.c0.im = y.c0.im)
    (h3 : x.o1 = y.o1) (h4 : x.c2.re = y.c2.re) (h5 : x.c2.im = y.c2.im) : x = y := by
  ext1
  · exact Complex.ext h1 h2
  · exact h3
  · exact Complex.ext h4 h5

/-- The octonion-coordinate expansion used by every ring law below. -/
theorem mul_assoc' (x y z : Dq) : x * y * z = x * (y * z) := by
  apply ext_coords
  · simp only [mul_c0, Complex.mul_re, Complex.mul_im]; ring
  · simp only [mul_c0, Complex.mul_re, Complex.mul_im]; ring
  · simp only [mul_o1, mul_c0]
    apply oct_ext' <;>
      simp [oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im] <;> ring
  · simp [oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oC, oct_add_fst, oct_add_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im]; ring
  · simp [oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oC, oct_add_fst, oct_add_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im]; ring

macro "dq_tac" : tactic => `(tactic| (
  apply ext_coords <;> (try apply oct_ext') <;>
    (try simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im]) <;> (try ring)))

theorem left_distrib' (x y z : Dq) : x * (y + z) = x * y + x * z := by dq_tac
theorem right_distrib' (x y z : Dq) : (x + y) * z = x * z + y * z := by dq_tac
theorem zero_mul' (x : Dq) : 0 * x = 0 := by dq_tac
theorem mul_zero' (x : Dq) : x * 0 = 0 := by dq_tac
theorem one_mul' (x : Dq) : 1 * x = x := by dq_tac
theorem mul_one' (x : Dq) : x * 1 = x := by dq_tac
theorem smul_mul_assoc' (r : ℝ) (x y : Dq) : (r • x) * y = r • (x * y) := by dq_tac
theorem mul_smul_comm' (r : ℝ) (x y : Dq) : x * (r • y) = r • (x * y) := by dq_tac

instance instRing : Ring Dq where
  __ := instAddCommGroup
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul := zero_mul'
  mul_zero := mul_zero'

instance instAlgebra : Algebra ℝ Dq := Algebra.ofModule smul_mul_assoc' mul_smul_comm'

end Dq

/-! ## The reduction `E₂ → M₃(Dq)` -/

/-- Entrywise reduction modulo `I = t²ℂ_i^⊥` of the Hermitian matrix of `x ∈ J₃`. -/
def redq (x : J3) : Matrix (Fin 3) (Fin 3) Dq :=
  fun i j => ⟨oC (albertMatrix x.1 i j), albertMatrix x.2.1 i j, oC (albertMatrix x.2.2 i j)⟩

theorem redq_unit : redq (albertUnit, 0, 0) = 1 := by
  ext i j
  · fin_cases i <;> fin_cases j <;>
      simp [redq, oC, albertMatrix, albertUnit, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, Matrix.one_apply] <;> rfl
  · fin_cases i <;> fin_cases j <;>
      simp [redq, albertMatrix, Matrix.one_apply, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq] <;> rfl
  · fin_cases i <;> fin_cases j <;>
      simp [redq, oC, albertMatrix, Matrix.one_apply, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq] <;> rfl

theorem albertMatrix_add' (x y : Albert) (i j : Fin 3) :
    albertMatrix (x + y) i j = albertMatrix x i j + albertMatrix y i j := by
  fin_cases i <;> fin_cases j <;>
    simp [albertMatrix, albert_add_fst', albert_add_snd', oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq] <;>
    (try apply oct_ext') <;> simp [oct_add_fst, oct_add_snd] <;> (try ring) <;> rfl

theorem albertMatrix_smul' (r : ℝ) (x : Albert) (i j : Fin 3) :
    albertMatrix (r • x) i j = r • albertMatrix x i j := by
  fin_cases i <;> fin_cases j <;>
    simp [albertMatrix, albert_smul_fst', albert_smul_snd', oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq] <;>
    (try apply oct_ext') <;> simp [oct_smul_fst, oct_smul_snd] <;> (try ring) <;> rfl

theorem oC_add (a b : Octonion) : oC (a + b) = oC a + oC b := by
  apply Complex.ext <;> simp [oC, oct_add_fst]
theorem oC_smul (r : ℝ) (a : Octonion) : oC (r • a) = r • oC a := by
  apply Complex.ext <;> simp [oC, oct_smul_fst]

theorem redq_add (x y : J3) : redq (x + y) = redq x + redq y := by
  ext i j <;> simp [redq, albertMatrix_add', oC_add]

theorem redq_smul (r : ℝ) (x : J3) : redq (r • x) = r • redq x := by
  ext i j <;> simp [redq, albertMatrix_smul', oC_smul]

theorem W_coords {x : Albert} (hx : x ∈ Wso) :
    (x.2 0).1.imJ = 0 ∧ (x.2 0).1.imK = 0 ∧ (x.2 0).2 = 0 ∧
      (x.2 1).1.imJ = 0 ∧ (x.2 1).1.imK = 0 ∧ (x.2 1).2 = 0 ∧
      (x.2 2).1.imJ = 0 ∧ (x.2 2).1.imK = 0 ∧ (x.2 2).2 = 0 :=
  (standardComplexWindow_contains_iff x).1 hx

set_option maxHeartbeats 100000000 in
theorem redq_jordan_00 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 0 0 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 0 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem redq_jordan_01 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 0 1 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 0 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem redq_jordan_02 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 0 2 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 0 2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem redq_jordan_10 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 1 0 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 1 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem redq_jordan_11 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 1 1 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 1 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem redq_jordan_12 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 1 2 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 1 2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem redq_jordan_20 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 2 0 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 2 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem redq_jordan_21 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 2 1 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 2 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

set_option maxHeartbeats 100000000 in
theorem redq_jordan_22 (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) 2 2 = ((1 / 2 : ℝ) • (redq x * redq y + redq y * redq x)) 2 2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := W_coords (x := y.1) hy
  apply Dq.ext
  all_goals (first | apply Complex.ext | apply oct_ext')
  all_goals
    simp [redq, j3mul, Matrix.mul_apply, Fin.sum_univ_three, albertMatrix, jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2', octonionMatrixMul, albert_add_fst', albert_add_snd', oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, cO_fst, cO_snd, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  all_goals ring

/-- `prop:so:kernel`(c): the reduction is a Jordan homomorphism on `E₂` into `M₃(D₂/I)⁺`. -/
theorem redq_jordan (x y : J3) (hx : x ∈ E2) (hy : y ∈ E2) :
    redq (j3mul x y) = (1 / 2 : ℝ) • (redq x * redq y + redq y * redq x) := by
  ext1 i j
  fin_cases i <;> fin_cases j
  · exact redq_jordan_00 x y hx hy
  · exact redq_jordan_01 x y hx hy
  · exact redq_jordan_02 x y hx hy
  · exact redq_jordan_10 x y hx hy
  · exact redq_jordan_11 x y hx hy
  · exact redq_jordan_12 x y hx hy
  · exact redq_jordan_20 x y hx hy
  · exact redq_jordan_21 x y hx hy
  · exact redq_jordan_22 x y hx hy

/-- `prop:so:kernel`(c): on `E₂` the reduction vanishes exactly on `K = t²W^⊥`. -/
theorem redq_eq_zero_iff (x : J3) (hx : x ∈ E2) : redq x = 0 ↔ x ∈ Kso := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := W_coords (x := x.1) hx
  constructor
  · intro h
    have e : ∀ i j, redq x i j = 0 := fun i j => by rw [h]; rfl
    have e00 := e 0 0; have e11 := e 1 1; have e22 := e 2 2
    have e01 := e 0 1; have e02 := e 0 2; have e12 := e 1 2
    simp only [redq, albertMatrix, Dq.ext_iff, Dq.zero_c0, Dq.zero_o1, Dq.zero_c2] at e00 e11 e22 e01 e02 e12
    simp [oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, Complex.ext_iff, Prod.ext_iff] at e00 e11 e22 e01 e02 e12
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply albert_ext' <;> (try apply oct_ext') <;> simp_all
    · apply albert_ext' <;> (try apply oct_ext') <;> simp_all [Quaternion.ext_iff]
    · intro i; fin_cases i <;> simp_all
    · intro k; fin_cases k <;> simp_all
  · rintro ⟨h0, h1, hd, ho⟩
    ext i j
    all_goals (fin_cases i <;> fin_cases j)
    all_goals simp [redq, albertMatrix, h0, h1, hd, (ho 0).1, (ho 0).2, (ho 1).1, (ho 1).2, (ho 2).1, (ho 2).2, oC, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq] <;> rfl

/-! ## Corollary core: Jordan-polynomial values at idempotents of `E₂` -/

/-- Jordan-polynomial terms in `n` variables (unit, sums, real multiples, Jordan products). -/
inductive JTerm (n : ℕ) where
  | var : Fin n → JTerm n
  | one : JTerm n
  | add : JTerm n → JTerm n → JTerm n
  | smul : ℝ → JTerm n → JTerm n
  | mul : JTerm n → JTerm n → JTerm n

namespace JTerm

variable {n : ℕ}

/-- Evaluation in `A⁺`, `A` a unital associative real algebra. -/
def evalS {A : Type} [Ring A] [Algebra ℝ A] (P : Fin n → A) : JTerm n → A
  | var k => P k
  | one => 1
  | add s t => evalS P s + evalS P t
  | smul r t => r • evalS P t
  | mul s t => (1 / 2 : ℝ) • (evalS P s * evalS P t + evalS P t * evalS P s)

/-- Evaluation in the jet algebra `J₃ = J[t]/(t³)`. -/
def evalE (p : Fin n → J3) : JTerm n → J3
  | var k => p k
  | one => (albertUnit, 0, 0)
  | add s t => evalE p s + evalE p t
  | smul r t => r • evalE p t
  | mul s t => j3mul (evalE p s) (evalE p t)

/-- `T` vanishes at every tuple of idempotents of every special unital real algebra. -/
def VanishesOnSpecialIdempotents (T : JTerm n) : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℝ A] (P : Fin n → A), (∀ k, P k * P k = P k) → evalS P T = 0

theorem evalE_mem (p : Fin n → J3) (hp : ∀ k, p k ∈ E2) (T : JTerm n) : evalE p T ∈ E2 := by
  induction T with
  | var k => exact hp k
  | one => exact standardComplexWindow.toSubalgebra.unit_mem
  | add s t hs ht => exact E2.add_mem hs ht
  | smul r t ht => exact E2.smul_mem r ht
  | mul s t hs ht => exact E2_mul_mem hs ht

theorem redq_evalE (p : Fin n → J3) (hp : ∀ k, p k ∈ E2) (T : JTerm n) :
    redq (evalE p T) = evalS (fun k => redq (p k)) T := by
  induction T with
  | var k => rfl
  | one => exact redq_unit
  | add s t hs ht => simp only [evalE, evalS, redq_add, hs, ht]
  | smul r t ht => simp only [evalE, evalS, redq_smul, ht]
  | mul s t hs ht =>
    simp only [evalE, evalS]
    rw [redq_jordan _ _ (evalE_mem p hp s) (evalE_mem p hp t), hs, ht]

end JTerm

/-- `cor:so:residual`, formal-jet core: if `T` vanishes at all idempotent tuples of every special
unital real algebra, then at idempotents `p̃_k` of `E₂` (e.g. 2-jets of idempotent curves based
in `W`) its value lies in `K = t²W^⊥`: the coefficients of `1` and `t` vanish and the coefficient
of `t²` lies in `W^⊥`. -/
theorem term_value_mem_K {n : ℕ} (T : JTerm n) (hT : T.VanishesOnSpecialIdempotents)
    (p : Fin n → J3) (hp : ∀ k, p k ∈ E2) (hidem : ∀ k, j3mul (p k) (p k) = p k) :
    T.evalE p ∈ Kso := by
  rw [← redq_eq_zero_iff _ (JTerm.evalE_mem p hp T), JTerm.redq_evalE p hp T]
  apply hT
  intro k
  have h := redq_jordan (p k) (p k) (hp k) (hp k)
  rw [hidem k] at h
  have e : (1 / 2 : ℝ) • (redq (p k) * redq (p k) + redq (p k) * redq (p k)) =
      redq (p k) * redq (p k) := by
    rw [← two_smul ℝ (redq (p k) * redq (p k)), smul_smul]
    norm_num
  exact e.symm.trans h.symm

end

end AlbertSequential.AppF
