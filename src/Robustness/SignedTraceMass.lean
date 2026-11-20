/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.TraceBaseNorm

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential

/-- Cone and trace data with an attained minimum positive-decomposition mass. -/
structure SignedTraceMassData (E : Type*) [AddCommGroup E] [Module ℝ E] where
  positive : Set E
  trace : E →ₗ[ℝ] ℝ
  zero_positive : (0 : E) ∈ positive
  add_positive : ∀ x ∈ positive, ∀ y ∈ positive, x + y ∈ positive
  smul_positive : ∀ (r : ℝ), 0 ≤ r → ∀ x ∈ positive, r • x ∈ positive
  positive_trace : ∀ x ∈ positive, x ≠ 0 → 0 < trace x
  exists_minimum : ∀ x : E, ∃ p n : E,
    p ∈ positive ∧ n ∈ positive ∧ x = p - n ∧
      ∀ u ∈ positive, ∀ v ∈ positive, x = u - v → trace p + trace n ≤ trace u + trace v

namespace SignedTraceMassData

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (T : SignedTraceMassData E)

def mass (x : E) : ℝ :=
  T.trace (T.exists_minimum x).choose + T.trace (T.exists_minimum x).choose_spec.choose

theorem minimum (x : E) : ∃ p n : E,
    p ∈ T.positive ∧ n ∈ T.positive ∧ x = p - n ∧ T.mass x = T.trace p + T.trace n := by
  let h := (T.exists_minimum x).choose_spec.choose_spec
  exact ⟨_, _, h.1, h.2.1, h.2.2.1, rfl⟩

theorem mass_le {x p n : E} (hp : p ∈ T.positive) (hn : n ∈ T.positive)
    (hx : x = p - n) : T.mass x ≤ T.trace p + T.trace n :=
  (T.exists_minimum x).choose_spec.choose_spec.2.2.2 p hp n hn hx

theorem trace_nonneg {x : E} (hx : x ∈ T.positive) : 0 ≤ T.trace x := by
  by_cases h : x = 0
  · simp [h]
  · exact (T.positive_trace x hx h).le

theorem trace_eq_zero_iff {x : E} (hx : x ∈ T.positive) : T.trace x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hn
    exact (T.positive_trace x hx hn).ne' h
  · rintro rfl
    exact map_zero _

theorem mass_nonneg (x : E) : 0 ≤ T.mass x := by
  obtain ⟨p, n, hp, hn, _, hmass⟩ := T.minimum x
  rw [hmass]
  exact add_nonneg (T.trace_nonneg hp) (T.trace_nonneg hn)

theorem mass_eq_trace_of_positive {x : E} (hx : x ∈ T.positive) : T.mass x = T.trace x := by
  apply le_antisymm
  · simpa only [map_zero, add_zero] using T.mass_le hx T.zero_positive (sub_zero x).symm
  · obtain ⟨p, n, hp, hn, heq, hmass⟩ := T.minimum x
    rw [hmass, heq, map_sub]
    linarith [T.trace_nonneg hn]

@[simp] theorem mass_zero : T.mass 0 = 0 := by
  rw [T.mass_eq_trace_of_positive T.zero_positive, map_zero]

theorem mass_eq_zero_iff (x : E) : T.mass x = 0 ↔ x = 0 := by
  constructor
  · intro h
    obtain ⟨p, n, hp, hn, heq, hmass⟩ := T.minimum x
    have hp0 : T.trace p = 0 := by linarith [T.trace_nonneg hp, T.trace_nonneg hn]
    have hn0 : T.trace n = 0 := by linarith [T.trace_nonneg hp, T.trace_nonneg hn]
    rw [heq, (T.trace_eq_zero_iff hp).mp hp0, (T.trace_eq_zero_iff hn).mp hn0, sub_self]
  · rintro rfl
    exact T.mass_zero

theorem mass_add_le (x y : E) : T.mass (x + y) ≤ T.mass x + T.mass y := by
  obtain ⟨p, n, hp, hn, hx, hmass⟩ := T.minimum x
  obtain ⟨q, m, hq, hm, hy, hmass'⟩ := T.minimum y
  have h := T.mass_le (T.add_positive p hp q hq) (T.add_positive n hn m hm)
    (show x + y = (p + q) - (n + m) by rw [hx, hy]; abel)
  rw [map_add, map_add] at h
  linarith

theorem mass_neg_le (x : E) : T.mass (-x) ≤ T.mass x := by
  obtain ⟨p, n, hp, hn, heq, hmass⟩ := T.minimum x
  rw [hmass, add_comm]
  exact T.mass_le hn hp (by rw [heq, neg_sub])

@[simp] theorem mass_neg (x : E) : T.mass (-x) = T.mass x :=
  le_antisymm (T.mass_neg_le x) (by simpa only [neg_neg] using T.mass_neg_le (-x))

theorem mass_smul_le_of_nonneg {r : ℝ} (hr : 0 ≤ r) (x : E) :
    T.mass (r • x) ≤ r * T.mass x := by
  obtain ⟨p, n, hp, hn, hx, hmass⟩ := T.minimum x
  have h := T.mass_le (T.smul_positive r hr p hp) (T.smul_positive r hr n hn)
    (show r • x = r • p - r • n by rw [← smul_sub, ← hx])
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_add, ← hmass] at h
  exact h

theorem mass_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (x : E) :
    T.mass (r • x) = r * T.mass x := by
  rcases hr.eq_or_lt with h | h
  · rw [← h, zero_smul, T.mass_zero, zero_mul]
  apply le_antisymm (T.mass_smul_le_of_nonneg hr x)
  have hi := T.mass_smul_le_of_nonneg (inv_nonneg.mpr hr) (r • x)
  rw [smul_smul, inv_mul_cancel₀ h.ne', one_smul] at hi
  have h' := mul_le_mul_of_nonneg_left hi hr
  rwa [← mul_assoc, mul_inv_cancel₀ h.ne', one_mul] at h'

theorem mass_smul (r : ℝ) (x : E) : T.mass (r • x) = ‖r‖ * T.mass x := by
  rw [Real.norm_eq_abs]
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h, T.mass_smul_of_nonneg h]
  · rw [abs_of_nonpos h, ← T.mass_smul_of_nonneg (neg_nonneg.mpr h), neg_smul, T.mass_neg]

/-- The same additive/module carrier with its trace norm. -/
def WithNorm (_T : SignedTraceMassData E) := E

instance : AddCommGroup T.WithNorm := inferInstanceAs (AddCommGroup E)
instance : Module ℝ T.WithNorm := inferInstanceAs (Module ℝ E)
instance : Norm T.WithNorm := ⟨T.mass⟩

theorem normedCore : NormedSpace.Core ℝ T.WithNorm where
  norm_nonneg := T.mass_nonneg
  norm_triangle := T.mass_add_le
  norm_smul := T.mass_smul
  norm_eq_zero_iff := T.mass_eq_zero_iff

instance : NormedAddCommGroup T.WithNorm := NormedAddCommGroup.ofCore T.normedCore
instance : NormedSpace ℝ T.WithNorm := NormedSpace.ofCore T.normedCore

theorem norm_eq_mass (x : T.WithNorm) : ‖x‖ = T.mass x := rfl

def toTraceBaseNormData : TraceBaseNormData T.WithNorm where
  positive := T.positive
  trace := T.trace
  zero_positive := T.zero_positive
  add_positive := T.add_positive
  smul_positive := T.smul_positive
  trace_eq_norm := fun _ hx => (T.mass_eq_trace_of_positive hx).symm
  decompose := T.minimum

end SignedTraceMassData
end AlbertSequential
