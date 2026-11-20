/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel

/-!
An associative representation of Hermitian matrices respects the directed corner product
on any triple of distinct diagonal indices. The resulting scalar corner kills every
coefficient associator, including when the representation is nonunital.
-/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

section AssociativeTarget

variable {A : Type*} [NonUnitalRing A]

theorem mul_eq_zero_of_idempotent_anticommutator [Module ℝ A] {p q : A}
    (hp : p * p = p) (h : p * q + q * p = 0) : p * q = 0 := by
  have hcomm : p * q = q * p := by
    apply sub_eq_zero.mp
    calc
      p * q - q * p = p * (p * q + q * p) - (p * q + q * p) * p := by
        simp only [mul_add, add_mul, ← mul_assoc p p q, mul_assoc q p p, hp, mul_assoc p q p]
        abel
      _ = 0 := by rw [h, mul_zero, zero_mul, sub_zero]
  have htwo : (2 : ℝ) • (p * q) = 0 := by rw [two_smul, hcomm]; rw [hcomm] at h; exact h
  have hv := congrArg (fun v : A => (2 : ℝ)⁻¹ • v) htwo
  rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul, smul_zero] at hv

variable {C : Type*} {S : Type*}
variable (p : S → A) (s : S → S → C → A)

private def corner (i j : S) (a : C) : A := p i * s i j a * p j

private theorem edgeLeft {i j : S} {a : C} (h : p i * p j = 0)
    (hs : p j * s i j a + s i j a * p j = s i j a) :
    p i * s i j a = corner p s i j a := by
  calc
    p i * s i j a = p i * (p j * s i j a + s i j a * p j) := by rw [hs]
    _ = corner p s i j a := by simp [corner, mul_add, ← mul_assoc, h]

private theorem edgeOff {i j k : S} {a : C}
    (hij : p i * p j = 0) (hik : p i * p k = 0) (hjk : p j * p k = 0)
    (hj : p j * s j k a + s j k a * p j = s j k a)
    (hk : p k * s j k a + s j k a * p k = s j k a) :
    p i * s j k a = 0 := by
  have h₁ : p i * s j k a = p i * s j k a * p j := by
    conv_lhs => rw [← hj]
    simp [mul_add, ← mul_assoc, hij]
  have h₂ : p i * s j k a = p i * s j k a * p k := by
    conv_lhs => rw [← hk]
    simp [mul_add, ← mul_assoc, hik]
  calc
    p i * s j k a = p i * s j k a * p k := h₂
    _ = (p i * s j k a * p j) * p k := congrArg (· * p k) h₁
    _ = 0 := by rw [mul_assoc _ (p j), hjk, mul_zero]

variable (prod : C → C → C)

private theorem cornerTriangle
    (hidem : ∀ i, p i * p i = p i)
    (hortho : ∀ ⦃i j : S⦄, i ≠ j → p i * p j = 0)
    (hleft : ∀ ⦃i j : S⦄, i ≠ j → ∀ a, p i * s i j a + s i j a * p i = s i j a)
    (hright : ∀ ⦃i j : S⦄, i ≠ j → ∀ a, p j * s i j a + s i j a * p j = s i j a)
    (htriangle : ∀ ⦃i j k : S⦄, i ≠ j → i ≠ k → j ≠ k → ∀ a b,
      s i j a * s j k b + s j k b * s i j a = s i k (prod a b))
    {i j k : S} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : C) :
    corner p s i k (prod a b) = corner p s i j a * corner p s j k b := by
  calc
    corner p s i k (prod a b) =
        p i * (s i j a * s j k b + s j k b * s i j a) * p k := by
      simp only [corner, htriangle hij hik hjk]
    _ = p i * s i j a * s j k b * p k := by
      rw [mul_add, ← mul_assoc (p i) (s j k b), edgeOff p s (hortho hij)
        (hortho hik) (hortho hjk) (hleft hjk b) (hright hjk b), zero_mul, add_zero, ← mul_assoc]
    _ = corner p s i j a * corner p s j k b := by
      rw [edgeLeft p s (hortho hij) (hright hij a)]
      have hc : corner p s i j a * p j = corner p s i j a := by
        unfold corner
        rw [mul_assoc _ (p j), hidem j]
      calc
        corner p s i j a * s j k b * p k = (corner p s i j a * p j) * s j k b * p k := by rw [hc]
        _ = corner p s i j a * corner p s j k b := by simp only [corner, mul_assoc]

/-- Directed corner associativity follows from the triangular edge laws and their unit edges. -/
theorem directedCorner_associator
    (u : C) (hunitLeft : ∀ a, prod u a = a) (hunitRight : ∀ a, prod a u = a)
    (hidem : ∀ i, p i * p i = p i)
    (hortho : ∀ ⦃i j : S⦄, i ≠ j → p i * p j = 0)
    (hleft : ∀ ⦃i j : S⦄, i ≠ j → ∀ a, p i * s i j a + s i j a * p i = s i j a)
    (hright : ∀ ⦃i j : S⦄, i ≠ j → ∀ a, p j * s i j a + s i j a * p j = s i j a)
    (htriangle : ∀ ⦃i j k : S⦄, i ≠ j → i ≠ k → j ≠ k → ∀ a b,
      s i j a * s j k b + s j k b * s i j a = s i k (prod a b))
    {i j k : S} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b c : C) :
    p i * s i k (prod (prod a b) c) * p k = p i * s i k (prod a (prod b c)) * p k := by
  let ρ := corner p s
  have hprod {i j k : S} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : C) :
      ρ i k (prod a b) = ρ i j a * ρ j k b :=
    cornerTriangle p s prod hidem hortho hleft hright htriangle hij hik hjk a b
  have hright' (x : C) : ρ i j x = ρ i k x * ρ k j u := by
    simpa only [hunitRight] using hprod hik hij hjk.symm x u
  have hleft' (x : C) : ρ j k x = ρ j i u * ρ i k x := by
    simpa only [hunitLeft] using hprod hij.symm hjk hik u x
  have hmiddle : ρ j k b * ρ k j u = ρ j i u * ρ i j b := by
    rw [hleft' b, mul_assoc, ← hright']
  change ρ i k (prod (prod a b) c) = ρ i k (prod a (prod b c))
  calc
    ρ i k (prod (prod a b) c) = (ρ i k (prod a b) * ρ k j u) * ρ j k c := by
      rw [hprod hij hik hjk (prod a b) c, hright']
    _ = ρ i j a * ((ρ j k b * ρ k j u) * ρ j k c) := by
      rw [hprod hij hik hjk]
      simp only [mul_assoc]
    _ = ρ i j a * (ρ j i u * (ρ i j b * ρ j k c)) := by
      rw [hmiddle, mul_assoc (ρ j i u)]
    _ = ρ i j a * ρ j k (prod b c) := by rw [← hprod hij hik hjk b c, ← hleft']
    _ = ρ i k (prod a (prod b c)) := (hprod hij hik hjk a (prod b c)).symm

end AssociativeTarget
end AlbertSequential.AppF
