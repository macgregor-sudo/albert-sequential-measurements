/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OctonionGeometry
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The leading associator coefficients of the real and quaternionic jet algebras. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

@[local simp] theorem oct_fst_add (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
@[local simp] theorem oct_snd_add (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
@[local simp] theorem oct_fst_smul (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
@[local simp] theorem oct_snd_smul (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl

private theorem octAssociator_pair (x y z : Octonion) :
    octAssociator x y z =
      ((octonionMul (octonionMul x y) z).1 - (octonionMul x (octonionMul y z)).1,
       (octonionMul (octonionMul x y) z).2 - (octonionMul x (octonionMul y z)).2) := rfl

/-- The complement of the real scalar line in the given octonion coordinates. -/
def realAssociatorSpace : Submodule ℝ Octonion where
  carrier := {x | octonionReal x = 0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    change octonionReal x + octonionReal y = 0
    rw [hx, hy, zero_add]
  smul_mem' r x hx := by
    change r * octonionReal x = 0
    rw [hx, mul_zero]

/-- The complement of the standard quaternionic half in the Cayley–Dickson splitting. -/
def quaternionicAssociatorSpace : Submodule ℝ Octonion where
  carrier := {x | x.1 = 0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by change x.1 + y.1 = 0; rw [hx, hy, zero_add]
  smul_mem' r x hx := by change r • x.1 = 0; rw [hx, smul_zero]

@[simp] theorem mem_realAssociatorSpace (x : Octonion) :
    x ∈ realAssociatorSpace ↔ octonionReal x = 0 := Iff.rfl

@[simp] theorem mem_quaternionicAssociatorSpace (x : Octonion) :
    x ∈ quaternionicAssociatorSpace ↔ x.1 = 0 := Iff.rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] Octonion

private theorem octAssociator_quat_quat_fst (a b : Quaternion ℝ) (x : Octonion) :
    (octAssociator (a, 0) (b, 0) x).1 = 0 := by
  change (a * b - star (0 : Quaternion ℝ) * 0) * x.1 - star x.2 * (0 * a + 0 * star b) -
    (a * (b * x.1 - star x.2 * 0) - star (x.2 * b + 0 * star x.1) * 0) = 0
  simp [mul_assoc]

theorem octAssociator_of_two_quaternionic (a b : Quaternion ℝ) (x : Octonion) :
    octAssociator (a, 0) (b, 0) x ∈ quaternionicAssociatorSpace ∧
    octAssociator (a, 0) x (b, 0) ∈ quaternionicAssociatorSpace ∧
    octAssociator x (a, 0) (b, 0) ∈ quaternionicAssociatorSpace := by
  have h : octAssociator (a, 0) (b, 0) x ∈ quaternionicAssociatorSpace :=
    octAssociator_quat_quat_fst a b x
  refine ⟨h, ?_, ?_⟩
  · rw [octAssociator_swap_23]
    exact Submodule.neg_mem _ h
  · rw [← octAssociator_cyclic x (a, 0) (b, 0)]
    exact h

theorem octAssociator_standard_quaternionic (a b c : Quaternion ℝ) :
    octAssociator (a, 0) (b, 0) (c, 0) = 0 := by
  apply Prod.ext
  · exact octAssociator_quat_quat_fst a b (c, 0)
  · change (0 : Quaternion ℝ) * (a * b - star (0 : Quaternion ℝ) * 0) +
      (0 * a + 0 * star b) * star c -
      ((0 * b + 0 * star c) * a + 0 * star (b * c - star (0 : Quaternion ℝ) * 0)) = 0
    simp

theorem octAssociator_twoQuats_oneOutside (q : Quaternion ℝ) :
    octAssociator octI octJ (0, q) = (0, (2 : ℝ) • (q * (octK.1))) := by
  apply Prod.ext
  · exact octAssociator_quat_quat_fst _ _ _
  · change q * ((⟨0, 1, 0, 0⟩ : Quaternion ℝ) * ⟨0, 0, 1, 0⟩ -
        star (0 : Quaternion ℝ) * 0) + (0 * ⟨0, 1, 0, 0⟩ + 0 * star ⟨0, 0, 1, 0⟩) * star 0 -
      ((q * ⟨0, 0, 1, 0⟩ + 0 * star 0) * ⟨0, 1, 0, 0⟩ +
        0 * star ((⟨0, 0, 1, 0⟩ : Quaternion ℝ) * 0 - star q * 0)) =
      (2 : ℝ) • (q * (⟨0, 0, 0, 1⟩ : Quaternion ℝ))
    have h₁ : (⟨0, 1, 0, 0⟩ : Quaternion ℝ) * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 0, 1⟩ := by
      apply Quaternion.ext <;> norm_num [Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul]
    have h₂ : (⟨0, 0, 1, 0⟩ : Quaternion ℝ) * ⟨0, 1, 0, 0⟩ = -⟨0, 0, 0, 1⟩ := by
      apply Quaternion.ext <;> norm_num [Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul]
    simp only [star_zero, mul_zero, zero_mul, add_zero, sub_zero, h₁, mul_assoc,
      h₂, mul_neg, sub_neg_eq_add, two_smul]

theorem octAssociator_real_extra_direction :
    octAssociator octJ octL (octonionMul octK octL) = (-2 : ℝ) • octI := by
  rw [octAssociator_pair]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [octonionMul, octJ, octK, octL, octI, Quaternion.re_smul]

theorem octAssociator_real_twoDirections (j k : ℝ) :
    octAssociator octI octL (0, (⟨0, 0, -(k / 2), j / 2⟩ : Quaternion ℝ)) =
      (⟨0, 0, j, k⟩, 0) := by
  rw [octAssociator_pair]
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octonionMul, octI, octL]

theorem quaternionicLeadingAssociator_representative (q : Quaternion ℝ) :
    ∃ u : Quaternion ℝ, octAssociator octI octJ (0, u) = (0, q) := by
  let u : Quaternion ℝ := ⟨q.imK / 2, -q.imJ / 2, q.imI / 2, -q.re / 2⟩
  refine ⟨u, ?_⟩
  rw [octAssociator_twoQuats_oneOutside]
  refine Prod.ext rfl ?_
  change (2 : ℝ) • (u * (⟨0, 0, 0, 1⟩ : Quaternion ℝ)) = q
  apply Quaternion.ext <;> simp [u] <;> ring

theorem span_quaternionic_leadingAssociators :
    Submodule.span ℝ (Set.range (fun t : Quaternion ℝ × Quaternion ℝ × Octonion =>
      octAssociator (t.1, 0) (t.2.1, 0) t.2.2)) = quaternionicAssociatorSpace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, b, x⟩, rfl⟩
    exact (octAssociator_of_two_quaternionic a b x).1
  · rintro ⟨p, q⟩ h
    change p = 0 at h
    subst p
    obtain ⟨u, hu⟩ := quaternionicLeadingAssociator_representative q
    rw [← hu]
    exact Submodule.subset_span ⟨(octI.1, octJ.1, (0, u)), rfl⟩

theorem realLeadingAssociator_decomposition (p q : Quaternion ℝ) (hp : p.re = 0) :
    ∃ u : Quaternion ℝ, ((p, q) : Octonion) =
      (-(p.imI / 2) : ℝ) • octAssociator octJ octL (octonionMul octK octL) +
      octAssociator octI octL (0, (⟨0, 0, -(p.imK / 2), p.imJ / 2⟩ : Quaternion ℝ)) +
      octAssociator octI octJ (0, u) := by
  obtain ⟨u, hu⟩ := quaternionicLeadingAssociator_representative q
  refine ⟨u, ?_⟩
  rw [hu, octAssociator_real_extra_direction, octAssociator_real_twoDirections]
  apply Prod.ext
  · apply Quaternion.ext <;> simp [octI, hp]
  · simp [octI]

theorem span_real_leadingAssociators :
    Submodule.span ℝ (Set.range (fun t : Octonion × Octonion × Octonion =>
      octAssociator t.1 t.2.1 t.2.2)) = realAssociatorSpace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y, z⟩, rfl⟩
    exact octonionReal_octAssociator x y z
  · rintro ⟨p, q⟩ h
    change p.re = 0 at h
    let S := Submodule.span ℝ (Set.range (fun t : Octonion × Octonion × Octonion =>
      octAssociator t.1 t.2.1 t.2.2))
    have hgen (x y z : Octonion) : octAssociator x y z ∈ S :=
      Submodule.subset_span ⟨(x, y, z), rfl⟩
    obtain ⟨u, hu⟩ := realLeadingAssociator_decomposition p q h
    rw [hu]
    exact S.add_mem (S.add_mem (S.smul_mem _ (hgen octJ octL (octonionMul octK octL)))
      (hgen octI octL (0, ⟨0, 0, -(p.imK / 2), p.imJ / 2⟩))) (hgen octI octJ (0, u))

end AlbertSequential.AppF
