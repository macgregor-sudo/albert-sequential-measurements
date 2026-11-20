/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.AssociatorTriangleBinding
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic.Module

/-! Hermitian matrices over real-linear unital coefficients, with the binary Jordan product. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

open scoped BigOperators

variable {C : Type*} [AddCommGroup C] [Module ℝ C]

abbrev CoefficientMatrix (C : Type*) := Matrix (Fin 3) (Fin 3) C

def coefficientHermitian (s : C →ₗ[ℝ] C) : Submodule ℝ (CoefficientMatrix C) where
  carrier := {M | ∀ i j, s (M j i) = M i j}
  zero_mem' := fun _ _ => map_zero s
  add_mem' {M N} hM hN i j := by
    change s (M j i + N j i) = M i j + N i j
    rw [map_add, hM i j, hN i j]
  smul_mem' r M hM i j := by
    change s (r • M j i) = r • M i j
    rw [map_smul, hM i j]

def coefficientMatrixProduct (μ : C →ₗ[ℝ] C →ₗ[ℝ] C) (M N : CoefficientMatrix C) :
    CoefficientMatrix C := fun i j => ∑ k, μ (M i k) (N k j)

theorem coefficientMatrixProduct_add_left (μ : C →ₗ[ℝ] C →ₗ[ℝ] C)
    (M N P : CoefficientMatrix C) :
    coefficientMatrixProduct μ (M + N) P =
      coefficientMatrixProduct μ M P + coefficientMatrixProduct μ N P := by
  ext i j
  simp [coefficientMatrixProduct, Finset.sum_add_distrib]

theorem coefficientMatrixProduct_add_right (μ : C →ₗ[ℝ] C →ₗ[ℝ] C)
    (M N P : CoefficientMatrix C) :
    coefficientMatrixProduct μ M (N + P) =
      coefficientMatrixProduct μ M N + coefficientMatrixProduct μ M P := by
  ext i j
  simp [coefficientMatrixProduct, Finset.sum_add_distrib]

variable (s : C →ₗ[ℝ] C) (μ : C →ₗ[ℝ] C →ₗ[ℝ] C)

def coefficientHermitianProduct
    (hanti : ∀ x y, s (μ x y) = μ (s y) (s x))
    (M N : coefficientHermitian s) : coefficientHermitian s :=
  ⟨(1 / 2 : ℝ) • (coefficientMatrixProduct μ M.val N.val + coefficientMatrixProduct μ N.val M.val),
    fun i j => by
      change s ((1 / 2 : ℝ) • ((∑ k, μ (M.val j k) (N.val k i)) +
        (∑ k, μ (N.val j k) (M.val k i)))) =
        (1 / 2 : ℝ) • ((∑ k, μ (M.val i k) (N.val k j)) +
          (∑ k, μ (N.val i k) (M.val k j)))
      have hM (a b : Fin 3) : s (M.val b a) = M.val a b := M.property a b
      have hN (a b : Fin 3) : s (N.val b a) = N.val a b := N.property a b
      simp only [map_smul, map_add, map_sum, hanti, hM, hN]
      rw [add_comm]⟩

def coefficientMatrixUnit (i j : Fin 3) (x : C) : CoefficientMatrix C :=
  fun u v => if u = i ∧ v = j then x else 0

theorem coefficientMatrixUnit_product (i j k l : Fin 3) (x y : C) :
    coefficientMatrixProduct μ (coefficientMatrixUnit i j x) (coefficientMatrixUnit k l y) =
      if j = k then coefficientMatrixUnit i l (μ x y) else 0 := by
  ext u v
  by_cases hu : u = i <;> by_cases hv : v = l
  · subst u; subst v
    change (∑ w : Fin 3, μ (if i = i ∧ w = j then x else 0)
      (if w = k ∧ l = l then y else 0)) = (if j = k then coefficientMatrixUnit i l (μ x y) else 0) i l
    rw [Finset.sum_eq_single j]
    · by_cases hj : j = k <;> simp [hj, coefficientMatrixUnit]
    · intro w _ hw
      simp [hw]
    · simp
  · by_cases hj : j = k <;> simp [coefficientMatrixProduct, coefficientMatrixUnit, hv, hj]
  · by_cases hj : j = k <;> simp [coefficientMatrixProduct, coefficientMatrixUnit, hu, hj]
  · by_cases hj : j = k <;> simp [coefficientMatrixProduct, coefficientMatrixUnit, hu, hj]

def coefficientDiagonal (u : C) (hs : s u = u) (i : Fin 3) : coefficientHermitian s :=
  ⟨coefficientMatrixUnit i i u, fun a b => by
    by_cases ha : a = i <;> by_cases hb : b = i <;> simp [coefficientMatrixUnit, ha, hb, hs]⟩

def coefficientEdge (hstar : Function.Involutive s) (i j : Fin 3) (x : C) :
    coefficientHermitian s :=
  ⟨coefficientMatrixUnit i j x + coefficientMatrixUnit j i (s x), fun a b => by
    have hs (i j : Fin 3) (x : C) : s (coefficientMatrixUnit i j x b a) =
        coefficientMatrixUnit j i (s x) a b := by
      by_cases hi : b = i <;> by_cases hj : a = j <;> simp [coefficientMatrixUnit, hi, hj]
    change s (coefficientMatrixUnit i j x b a + coefficientMatrixUnit j i (s x) b a) =
      coefficientMatrixUnit i j x a b + coefficientMatrixUnit j i (s x) a b
    rw [map_add, hs, hs, hstar, add_comm]⟩

theorem coefficientEdge_flip (hstar : Function.Involutive s) (i j : Fin 3) (x : C) :
    coefficientEdge s hstar j i (s x) = coefficientEdge s hstar i j x := by
  apply Subtype.ext
  exact congrArg (fun y => coefficientMatrixUnit j i (s x) + coefficientMatrixUnit i j y) (hstar x) |>.trans
    (add_comm _ _)

theorem coefficientEdge_linear (hstar : Function.Involutive s) (i j : Fin 3) :
    ∃ f : C →ₗ[ℝ] coefficientHermitian s, ∀ x, f x = coefficientEdge s hstar i j x := by
  refine ⟨{ toFun := coefficientEdge s hstar i j, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · intro x y
    apply Subtype.ext
    ext a b
    change coefficientMatrixUnit i j (x + y) a b + coefficientMatrixUnit j i (s (x + y)) a b =
      (coefficientMatrixUnit i j x a b + coefficientMatrixUnit j i (s x) a b) +
        (coefficientMatrixUnit i j y a b + coefficientMatrixUnit j i (s y) a b)
    simp only [coefficientMatrixUnit, map_add]
    split_ifs <;> simp [add_add_add_comm]
  · intro r x
    apply Subtype.ext
    ext a b
    change coefficientMatrixUnit i j (r • x) a b + coefficientMatrixUnit j i (s (r • x)) a b =
      r • (coefficientMatrixUnit i j x a b + coefficientMatrixUnit j i (s x) a b)
    by_cases h : a = i ∧ b = j <;> by_cases h' : a = j ∧ b = i <;>
      simp [coefficientMatrixUnit, h, h', smul_add]

section ProductLaws

variable (hanti : ∀ x y, s (μ x y) = μ (s y) (s x))
variable (u : C) (hu : s u = u)
variable (hL : ∀ x, μ u x = x) (hR : ∀ x, μ x u = x)

include hL in
theorem coefficientDiagonal_square (i : Fin 3) :
    coefficientHermitianProduct s μ hanti (coefficientDiagonal s u hu i) (coefficientDiagonal s u hu i) =
      coefficientDiagonal s u hu i := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (coefficientMatrixProduct μ (coefficientMatrixUnit i i u) (coefficientMatrixUnit i i u) +
    coefficientMatrixProduct μ (coefficientMatrixUnit i i u) (coefficientMatrixUnit i i u)) =
    coefficientMatrixUnit i i u
  rw [coefficientMatrixUnit_product]
  simp only [ite_true, hL]
  module

theorem coefficientDiagonal_orthogonal (i j : Fin 3) (hij : i ≠ j) :
    coefficientHermitianProduct s μ hanti (coefficientDiagonal s u hu i) (coefficientDiagonal s u hu j) = 0 := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (coefficientMatrixProduct μ (coefficientMatrixUnit i i u) (coefficientMatrixUnit j j u) +
    coefficientMatrixProduct μ (coefficientMatrixUnit j j u) (coefficientMatrixUnit i i u)) = 0
  simp [coefficientMatrixUnit_product, hij, hij.symm]

include hL hR in
theorem coefficientDiagonal_edge_left (hstar : Function.Involutive s) (i j : Fin 3) (hij : i ≠ j) (x : C) :
    coefficientHermitianProduct s μ hanti (coefficientDiagonal s u hu i) (coefficientEdge s hstar i j x) =
      (1 / 2 : ℝ) • coefficientEdge s hstar i j x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) •
      (coefficientMatrixProduct μ (coefficientMatrixUnit i i u)
        (coefficientMatrixUnit i j x + coefficientMatrixUnit j i (s x)) +
      coefficientMatrixProduct μ (coefficientMatrixUnit i j x + coefficientMatrixUnit j i (s x))
        (coefficientMatrixUnit i i u)) =
    (1 / 2 : ℝ) • (coefficientMatrixUnit i j x + coefficientMatrixUnit j i (s x))
  simp [coefficientMatrixProduct_add_left, coefficientMatrixProduct_add_right,
    coefficientMatrixUnit_product, hL, hR, hij, hij.symm]

include hL hR in
theorem coefficientDiagonal_edge_right (hstar : Function.Involutive s)
    (i j : Fin 3) (hij : i ≠ j) (x : C) :
    coefficientHermitianProduct s μ hanti (coefficientDiagonal s u hu j) (coefficientEdge s hstar i j x) =
      (1 / 2 : ℝ) • coefficientEdge s hstar i j x := by
  rw [← coefficientEdge_flip s hstar i j x]
  exact coefficientDiagonal_edge_left s μ hanti u hu hL hR hstar j i hij.symm (s x)

theorem coefficientEdge_triangle (hstar : Function.Involutive s)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x y : C) :
    coefficientHermitianProduct s μ hanti (coefficientEdge s hstar i j x) (coefficientEdge s hstar j k y) =
      (1 / 2 : ℝ) • coefficientEdge s hstar i k (μ x y) := by
  apply Subtype.ext
  change (1 / 2 : ℝ) •
      (coefficientMatrixProduct μ (coefficientMatrixUnit i j x + coefficientMatrixUnit j i (s x))
        (coefficientMatrixUnit j k y + coefficientMatrixUnit k j (s y)) +
      coefficientMatrixProduct μ (coefficientMatrixUnit j k y + coefficientMatrixUnit k j (s y))
        (coefficientMatrixUnit i j x + coefficientMatrixUnit j i (s x))) =
    (1 / 2 : ℝ) • (coefficientMatrixUnit i k (μ x y) + coefficientMatrixUnit k i (s (μ x y)))
  simp [coefficientMatrixProduct_add_left, coefficientMatrixProduct_add_right,
    coefficientMatrixUnit_product, hanti, hij, hij.symm, hik, hik.symm, hjk, hjk.symm]

end ProductLaws

end AlbertSequential.AppF
