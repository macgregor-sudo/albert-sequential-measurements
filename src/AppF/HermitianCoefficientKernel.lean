/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.CoefficientHermitianMatrices
import Mathlib.Tactic.Module

/-! The universal ideal of the Hermitian Jordan algebra detected by associative targets. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

variable {C A : Type*} [AddCommGroup C] [Module ℝ C]
variable (s : C →ₗ[ℝ] C) (μ : C →ₗ[ℝ] C →ₗ[ℝ] C)
variable (hanti : ∀ x y, s (μ x y) = μ (s y) (s x))

section AssociativeTarget
variable [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

def IsCoefficientJordanMap (f : coefficientHermitian s →ₗ[ℝ] A) : Prop :=
  ∀ M N, f (coefficientHermitianProduct s μ hanti M N) =
    (1 / 2 : ℝ) • (f M * f N + f N * f M)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
private theorem half_smul_cancel {x y : A} (h : (1 / 2 : ℝ) • x = (1 / 2 : ℝ) • y) : x = y := by
  have h' := congrArg (fun z : A => (2 : ℝ) • z) h
  change (2 : ℝ) • ((1 / 2 : ℝ) • x) = (2 : ℝ) • ((1 / 2 : ℝ) • y) at h'
  norm_num [smul_smul] at h'
  exact h'

/-- The intersection of all associative-target kernels contains the Hermitian
matrices supported in the coefficient associator span, when its fixed part is zero. -/
theorem coefficientJordanMap_kills_associatorIdeal
    (u : C) (hu : s u = u) (hstar : Function.Involutive s)
    (hL : ∀ x, μ u x = x) (hR : ∀ x, μ x u = x)
    (I : Submodule ℝ C)
    (hI : Submodule.span ℝ (Set.range (fun t : C × C × C =>
      μ (μ t.1 t.2.1) t.2.2 - μ t.1 (μ t.2.1 t.2.2))) = I)
    (hstarI : ∀ x, x ∈ I → s x ∈ I)
    (hfixedI : ∀ x, x ∈ I → s x = x → x = 0)
    (f : coefficientHermitian s →ₗ[ℝ] A) (hf : IsCoefficientJordanMap s μ hanti f)
    (M : coefficientHermitian s) (hM : ∀ i j, M.val i j ∈ I) :
    f M = 0 := by
  let P (i : Fin 3) := f (coefficientDiagonal s u hu i)
  let E (i j : Fin 3) (x : C) := f (coefficientEdge s hstar i j x)
  have hP (i : Fin 3) : P i * P i = P i := by
    have h := hf (coefficientDiagonal s u hu i) (coefficientDiagonal s u hu i)
    rw [coefficientDiagonal_square s μ hanti u hu hL] at h
    change P i = (1 / 2 : ℝ) • (P i * P i + P i * P i) at h
    rw [← two_smul ℝ (P i * P i), smul_smul] at h
    norm_num at h
    exact h.symm
  have hzero ⦃i j : Fin 3⦄ (hij : i ≠ j) : P i * P j = 0 := by
    have h := hf (coefficientDiagonal s u hu i) (coefficientDiagonal s u hu j)
    rw [coefficientDiagonal_orthogonal s μ hanti u hu i j hij, map_zero, ← smul_zero (1 / 2 : ℝ)] at h
    exact mul_eq_zero_of_idempotent_anticommutator (hP i) (half_smul_cancel h.symm)
  have hleft ⦃i j : Fin 3⦄ (hij : i ≠ j) (x : C) : P i * E i j x + E i j x * P i = E i j x := by
    have h := hf (coefficientDiagonal s u hu i) (coefficientEdge s hstar i j x)
    rw [coefficientDiagonal_edge_left s μ hanti u hu hL hR hstar i j hij, map_smul] at h
    exact half_smul_cancel h.symm
  have hright ⦃i j : Fin 3⦄ (hij : i ≠ j) (x : C) : P j * E i j x + E i j x * P j = E i j x := by
    have h := hf (coefficientDiagonal s u hu j) (coefficientEdge s hstar i j x)
    rw [coefficientDiagonal_edge_right s μ hanti u hu hL hR hstar i j hij, map_smul] at h
    exact half_smul_cancel h.symm
  have htri ⦃i j k : Fin 3⦄ (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x y : C) :
      E i j x * E j k y + E j k y * E i j x = E i k (μ x y) := by
    have h := hf (coefficientEdge s hstar i j x) (coefficientEdge s hstar j k y)
    rw [coefficientEdge_triangle s μ hanti hstar i j k hij hik hjk, map_smul] at h
    exact half_smul_cancel h.symm
  have hcorner (i k : Fin 3) (hik : i ≠ k) (x : C) (hx : x ∈ I) :
      P i * E i k x * P k = 0 := by
    have hex : ∃ j : Fin 3, i ≠ j ∧ j ≠ k := by
      fin_cases i <;> fin_cases k <;> decide
    obtain ⟨j, hij, hjk⟩ := hex
    obtain ⟨edge, hedge⟩ := coefficientEdge_linear s hstar i k
    let corner : C →ₗ[ℝ] A :=
      { toFun := fun y => P i * f (edge y) * P k
        map_add' := fun x y => by simp [mul_add, add_mul]
        map_smul' := fun r x => by simp [mul_smul_comm, smul_mul_assoc] }
    have hkill : I ≤ LinearMap.ker corner := by
      rw [← hI]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, b, c⟩, rfl⟩
      have h := directedCorner_associator P E (fun x y => μ x y) u hL hR
        hP hzero hleft hright htri hij hik hjk a b c
      change P i * f (edge (μ (μ a b) c - μ a (μ b c))) * P k = 0
      rw [map_sub, map_sub, mul_sub, sub_mul, hedge, hedge]
      exact sub_eq_zero.mpr h
    have hc : corner x = 0 := hkill hx
    simpa only [corner, LinearMap.coe_mk, AddHom.coe_mk, hedge] using hc
  have hedge0 (i j : Fin 3) (hij : i ≠ j) (x : C) (hx : x ∈ I) : E i j x = 0 := by
    have h₁ := hcorner i j hij x hx
    have h₂ := hcorner j i hij.symm (s x) (hstarI x hx)
    change P j * f (coefficientEdge s hstar j i (s x)) * P i = 0 at h₂
    rw [coefficientEdge_flip s hstar i j x] at h₂
    have hl : P i * E i j x = P i * E i j x * P j := by
      conv_lhs => rw [← hright hij x]
      simp [mul_add, ← mul_assoc, hzero hij]
    have hr : E i j x * P i = P j * E i j x * P i := by
      conv_lhs => rw [← hright hij x]
      simp [add_mul, mul_assoc, hzero hij.symm]
    rw [← hleft hij x, hl, hr, h₁]
    exact zero_add _ |>.trans h₂
  have hdiag (i : Fin 3) : M.val i i = 0 := hfixedI _ (hM i i) (M.property i i)
  have hsym (i j : Fin 3) : s (M.val j i) = M.val i j := M.property i j
  have hsplit : M = coefficientEdge s hstar 0 1 (M.val 0 1) +
      coefficientEdge s hstar 0 2 (M.val 0 2) + coefficientEdge s hstar 1 2 (M.val 1 2) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coefficientEdge, coefficientMatrixUnit, hdiag, hsym]
  rw [hsplit, map_add, map_add]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (hedge0 0 1 (by decide) _ (hM 0 1)) (hedge0 0 2 (by decide) _ (hM 0 2)))
    (hedge0 1 2 (by decide) _ (hM 1 2)) |>.trans (by simp)

end AssociativeTarget

section Entrywise
variable [Ring A] [Module ℝ A]

def coefficientEntrywiseMap (f : C →ₗ[ℝ] A) : coefficientHermitian s →ₗ[ℝ] CoefficientMatrix A where
  toFun M := fun i j => f (M.val i j)
  map_add' M N := by ext i j; exact map_add f (M.val i j) (N.val i j)
  map_smul' r M := by ext i j; exact map_smul f r (M.val i j)

theorem coefficientEntrywiseMap_jordan (f : C →ₗ[ℝ] A)
    (hf : ∀ x y, f (μ x y) = f x * f y) :
    IsCoefficientJordanMap s μ hanti (coefficientEntrywiseMap s f) := by
  intro M N
  ext i j
  change f ((1 / 2 : ℝ) • ((∑ k, μ (M.val i k) (N.val k j)) +
    (∑ k, μ (N.val i k) (M.val k j)))) =
    (1 / 2 : ℝ) • ((∑ k, f (M.val i k) * f (N.val k j)) +
      (∑ k, f (N.val i k) * f (M.val k j)))
  simp [map_sum, hf]

theorem coefficientEntrywiseMap_eq_zero (f : C →ₗ[ℝ] A) (M : coefficientHermitian s) :
    coefficientEntrywiseMap s f M = 0 ↔ ∀ i j, M.val i j ∈ LinearMap.ker f := by
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    ext i j
    exact h i j

theorem coefficientEntrywiseMap_injective (f : C →ₗ[ℝ] A) (hf : Function.Injective f) :
    Function.Injective (coefficientEntrywiseMap s f) := by
  intro M N h
  apply Subtype.ext
  ext i j
  exact hf (congrFun (congrFun h i) j)

end Entrywise

end AlbertSequential.AppF
