/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE (the Apache-2.0 text, identical to Physlib's LICENSE).
Authors: Tom Ole Diem

Adapted from Physlib, https://github.com/leanprover-community/physlib, commit
08a6c1b5b8e6db340547142c3f7047635128c786, file
PhyslibAlpha/ProbabilisticTheory/JordanOrderUnit/Power/Associative.lean.
Adapted declarations: commute_mulLeft_sq, commute_mulLeft_apply, linearized_mul_sq,
square_mul_jpow, mulLeft_jpow_add_two, fundamental_mulLeft_commute_pow, commute_mulLeft_pow,
pow_add.
Modifications: stated for the element wrapper of a concrete Jordan product structure instead of an
abstract unital ring; explicit powers `elementPower` use that structure's unit, with no ambient
multiplication or unit instance on the carrier (upstream `jpow_*` lemmas become `elementPower_*`,
`Module.End.mul_apply` becomes `mul_apply_eq_comp`); upstream docstrings and `omit` lines are
dropped; the proof bodies are otherwise unchanged. No Physlib import remains. Licence: Apache-2.0.
See THIRD_PARTY_NOTICES.
Thanks to Tom Ole Diem and the Physlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to
Robert Hooke, 1676.
-/
module

public import UnitalJordanProduct

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

-- These instances affect only the faithful wrapper, never the carrier E.
instance (P : UnitalJordanProduct E) : One P.Element := ⟨⟨P.unit⟩⟩
instance (P : UnitalJordanProduct E) : MulOneClass P.Element :=
  { (inferInstance : Mul P.Element), (inferInstance : One P.Element) with
    mul_one x := by
      apply P.elementEquiv.injective
      change P.product x.value P.unit=x.value
      rw [P.commutative,P.unit_left]
    one_mul x := by
      apply P.elementEquiv.injective
      exact P.unit_left x.value }

namespace Power
open RealJordan
variable {P : UnitalJordanProduct E}

def elementPower (a : P.Element) : ℕ → P.Element
  | 0 => 1
  | n+1 => a*elementPower a n

@[simp] theorem elementPower_zero (a : P.Element) : elementPower a 0=1 := rfl
@[simp] theorem elementPower_one (a : P.Element) : elementPower a 1=a := by
  simp only [elementPower,mul_one]
@[simp] theorem elementPower_two (a : P.Element) : elementPower a 2=a*a := by
  simp only [elementPower,mul_one]
theorem elementPower_succ (a : P.Element) (n : ℕ) :
    elementPower a (n+1)=a*elementPower a n := rfl

local notation "L" => RealJordan.leftMultiplication
local notation a " ^[" n "]" => elementPower a n

lemma commute_mulLeft_sq (a : P.Element) : Commute (L a) (L (a ^[2])) := by
  rw [elementPower_two]
  ext b
  simp only [mul_apply_eq_comp, mulLeft_apply]
  have h := IsCommJordan.lmul_comm_rmul_rmul a b
  rw [mul_comm (a * b) (a * a), mul_comm b (a * a)] at h
  exact h.symm

lemma commute_mulLeft_apply {a x : P.Element} (h : Commute (L a) (L x)) (y : P.Element) :
    a * (x * y) = x * (a * y) := by
  have hpt := LinearMap.congr_fun h.eq y
  simpa only [mul_apply_eq_comp, mulLeft_apply] using hpt

lemma linearized_mul_sq (a y z : P.Element) :
    (a * a * y) * z =
      -(2 : ℝ) • (a * (y * (a * z))) + (a * a) * (y * z) +
        (2 : ℝ) • ((a * y) * (a * z)) := by
  have hp := IsCommJordan.lmul_comm_rmul_rmul (a + z) y
  have hm := IsCommJordan.lmul_comm_rmul_rmul (a - z) y
  have hz := IsCommJordan.lmul_comm_rmul_rmul z y
  simp only [add_mul, mul_add, sub_mul, mul_sub] at hp hm
  have h := congrArg₂ (fun u v : P.Element => u - v) hp hm
  abel_nf at h
  rw [mul_comm z a, mul_comm (z * y) (a * a), mul_comm z (y * (a * a)),
    mul_comm y (a * a)] at h
  rw [hz] at h
  abel_nf at h
  have hclean :
      (2 : ℤ) • (z * (y * (z * z))) +
          ((2 : ℤ) • (a * a * (z * y)) + (4 : ℤ) • (a * y * (a * z))) =
        (2 : ℤ) • (z * (y * (z * z))) +
          ((2 : ℤ) • (a * a * y * z) + (4 : ℤ) • (a * (y * (a * z)))) := by
    calc
      _ = (2 : ℤ) • (a * a * (z * y)) +
          ((4 : ℤ) • (a * y * (a * z)) + (2 : ℤ) • (z * (y * (z * z)))) := by abel
      _ = _ := h
      _ = _ := by abel
  have hc := add_left_cancel hclean
  have h' : (2 : ℤ) • (a * a * y * z) =
      (2 : ℤ) • (-(2 : ℝ) • (a * (y * (a * z))) +
        (a * a) * (y * z) + (2 : ℝ) • ((a * y) * (a * z))) := by
    calc
      _ = (2 : ℤ) • (a * a * (z * y)) + (4 : ℤ) • (a * y * (a * z)) -
          (4 : ℤ) • (a * (y * (a * z))) := by rw [hc]; module
      _ = _ := by rw [mul_comm z y]; module
  calc
    _ = (1 / 2 : ℝ) • ((2 : ℤ) • (a * a * y * z)) := by module
    _ = (1 / 2 : ℝ) • ((2 : ℤ) • (-(2 : ℝ) • (a * (y * (a * z))) +
        (a * a) * (y * z) + (2 : ℝ) • ((a * y) * (a * z)))) :=
      congrArg (fun w : P.Element => (1 / 2 : ℝ) • w) h'
    _ = _ := by module

lemma square_mul_jpow (a : P.Element) (n : ℕ) : (a * a) * a ^[n] = a ^[n + 2] := by
  induction n with
  | zero => simp [elementPower_two]
  | succ n ih =>
      rw [elementPower_succ, ← elementPower_two]
      rw [← commute_mulLeft_apply (commute_mulLeft_sq a) (a ^[n])]
      rw [elementPower_two, ih, ← elementPower_succ]

lemma mulLeft_jpow_add_two (a : P.Element) (n : ℕ) :
    L (a ^[n + 2]) =
      -(2 : ℝ) • ((L a) * ((L (a ^[n])) * (L a))) +
        ((L (a * a)) * (L (a ^[n])) +
          (2 : ℝ) • ((L (a ^[n + 1])) * (L a))) := by
  ext z
  simp only [LinearMap.add_apply, LinearMap.smul_apply, mul_apply_eq_comp, mulLeft_apply]
  rw [← square_mul_jpow a n]
  simpa only [← elementPower_succ, add_assoc] using linearized_mul_sq a (a ^[n]) z

lemma fundamental_mulLeft_commute_pow (a : P.Element) (n : ℕ) :
    Commute (L a) (L (a ^[n])) ∧ Commute (L (a * a)) (L (a ^[n])) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      constructor <;> ext z <;>
        simp only [elementPower_zero, mul_apply_eq_comp, mulLeft_apply, one_mul]
  | one =>
      constructor
      · simpa only [elementPower_one] using Commute.refl (L a)
      · simpa only [elementPower_one, elementPower_two] using (commute_mulLeft_sq a).symm
  | more n hn hn1 =>
      rw [mulLeft_jpow_add_two]
      let X := L a
      let Y := L (a * a)
      let N := L (a ^[n])
      let M := L (a ^[n + 1])
      have hXY : Commute X Y := by simpa [X, Y, elementPower_two] using commute_mulLeft_sq a
      have hXN : Commute X N := by simpa [X, N] using hn.1
      have hYN : Commute Y N := by simpa [Y, N] using hn.2
      have hXM : Commute X M := by simpa [X, M] using hn1.1
      have hYM : Commute Y M := by simpa [Y, M] using hn1.2
      constructor
      · simpa [X, Y, N, M] using
          (Commute.smul_right
            ((Commute.refl X).mul_right (hXN.mul_right (Commute.refl X))) (-2 : ℝ)).add_right
            ((hXY.mul_right hXN).add_right
              ((hXM.mul_right (Commute.refl X)).smul_right (2 : ℝ)))
      · simpa [X, Y, N, M] using
          ((((hXY.symm.mul_right (hYN.mul_right hXY.symm))).smul_right (-2 : ℝ)).add_right
            (((Commute.refl Y).mul_right hYN).add_right
              ((hYM.mul_right hXY.symm).smul_right (2 : ℝ))))

lemma commute_mulLeft_pow (a : P.Element) (n : ℕ) : Commute (L a) (L (a ^[n])) :=
  (fundamental_mulLeft_commute_pow a n).1

lemma pow_add (a : P.Element) (m n : ℕ) : a ^[m] * a ^[n] = a ^[m + n] := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpt := commute_mulLeft_apply (commute_mulLeft_pow a m) (a ^[n])
      calc a ^[m] * a ^[n + 1] = a ^[m] * (a * a ^[n]) := by rw [elementPower_succ]
        _ = a * (a ^[m] * a ^[n]) := hpt.symm
        _ = a * a ^[m + n] := by rw [ih]
        _ = a ^[m + n + 1] := (elementPower_succ a (m + n)).symm

end Power
variable (P : UnitalJordanProduct E)

/-- Powers of the actual explicit product and explicit unit. -/
def jordanPower (a : E) (n : ℕ) : E :=
  (Power.elementPower (Element.mk a : P.Element) n).value

@[simp] theorem jordanPower_zero (a : E) : P.jordanPower a 0=P.unit := rfl
@[simp] theorem jordanPower_one (a : E) : P.jordanPower a 1=a := by
  exact congrArg Element.value (Power.elementPower_one (Element.mk a : P.Element))
theorem jordanPower_succ (a : E) (n : ℕ) :
    P.jordanPower a (n+1)=P.product a (P.jordanPower a n) := rfl

/-- Power associativity for the actual Jordan product, not an imported field. -/
theorem jordanPower_mul (a : E) (m n : ℕ) :
    P.product (P.jordanPower a m) (P.jordanPower a n)=P.jordanPower a (m+n) := by
  exact congrArg Element.value (Power.pow_add (Element.mk a : P.Element) m n)

end AlbertSequential.UnitalJordanProduct
