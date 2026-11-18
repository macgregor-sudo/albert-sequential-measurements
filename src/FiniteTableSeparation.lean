/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteTableCompactness
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Algebra.BigOperators.Pi

/-! Generic finite-coordinate separation. Native no-match, an appropriate common
finite list, and compact/convex native table sets are inputs to later assembly.
A homogeneous inequality is obtained only under explicit normalization. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped BigOperators

def tableLinearForm {I : Type*} [Fintype I] (c x : I → ℝ) : ℝ :=
  ∑ i, c i * x i

theorem exists_tableLinearForm_coefficients {I : Type*} [Fintype I]
    (f : (I → ℝ) →L[ℝ] ℝ) :
    ∃ c : I → ℝ, ∀ x, f x = tableLinearForm c x := by
  classical
  refine ⟨fun i => f (Pi.single i 1), fun x => ?_⟩
  calc
    f x = f (∑ i, x i • Pi.single i (1 : ℝ)) := congrArg f (pi_eq_sum_univ' x)
    _ = ∑ i, x i * f (Pi.single i 1) := by simp
    _ = tableLinearForm (fun i => f (Pi.single i 1)) x := by
      simp only [tableLinearForm, mul_comm]

/-- S is on the low side and T on the high side. Empty sets and an empty
coordinate type are allowed; no nonzero functional is claimed in those cases. -/
theorem finiteCompactConvex_strictSeparation {I : Type*} [Fintype I]
    {S T : Set (I → ℝ)} (hSc : IsCompact S) (hSv : Convex ℝ S)
    (hTc : IsCompact T) (hTv : Convex ℝ T) (hdisj : Disjoint S T) :
    ∃ (c : I → ℝ) (r γ : ℝ), 0 < γ ∧
      (∀ x ∈ S, tableLinearForm c x ≤ r - γ) ∧
      (∀ y ∈ T, r + γ ≤ tableLinearForm c y) := by
  obtain ⟨f, u, v, hS, huv, hT⟩ :=
    geometric_hahn_banach_compact_closed hSv hSc hTv hTc.isClosed hdisj
  obtain ⟨c, hc⟩ := exists_tableLinearForm_coefficients f
  refine ⟨c, (u + v) / 2, (v - u) / 2, by linarith, ?_, ?_⟩
  · intro x hx
    have h := hS x hx
    rw [hc x] at h
    linarith
  · intro y hy
    have h := hT y hy
    rw [hc y] at h
    linarith

theorem tableLinearForm_sub_single {I : Type*} [Fintype I] [DecidableEq I]
    (c x : I → ℝ) (r : ℝ) (e : I) :
    tableLinearForm (c - r • Pi.single e 1) x = tableLinearForm c x - r * x e := by
  classical
  simp only [tableLinearForm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  simp

/-- Threshold absorption uses the supplied common normalization coordinate.
It does not follow for unnormalized data or from per-point nonexistence alone. -/
theorem finiteCompactConvex_normalizedSeparation {I : Type*} [Fintype I]
    {S T : Set (I → ℝ)} (hSc : IsCompact S) (hSv : Convex ℝ S)
    (hTc : IsCompact T) (hTv : Convex ℝ T) (hdisj : Disjoint S T)
    (e : I) (hSe : ∀ x ∈ S, x e = 1) (hTe : ∀ y ∈ T, y e = 1) :
    ∃ (c : I → ℝ) (γ : ℝ), 0 < γ ∧
      (∀ x ∈ S, tableLinearForm c x ≤ -γ) ∧
      (∀ y ∈ T, γ ≤ tableLinearForm c y) := by
  classical
  obtain ⟨c, r, γ, hγ, hS, hT⟩ :=
    finiteCompactConvex_strictSeparation hSc hSv hTc hTv hdisj
  refine ⟨c - r • Pi.single e 1, γ, hγ, ?_, ?_⟩
  · intro x hx
    rw [tableLinearForm_sub_single, hSe x hx]
    have h := hS x hx
    linarith
  · intro y hy
    rw [tableLinearForm_sub_single, hTe y hy]
    have h := hT y hy
    linarith

theorem finiteCompactConvex_pointSeparation {I : Type*} [Fintype I]
    {T : Set (I → ℝ)} (hTc : IsCompact T) (hTv : Convex ℝ T)
    (x : I → ℝ) (hx : x ∉ T) :
    ∃ (c : I → ℝ) (r γ : ℝ), 0 < γ ∧
      tableLinearForm c x ≤ r - γ ∧
      (∀ y ∈ T, r + γ ≤ tableLinearForm c y) := by
  obtain ⟨c, r, γ, hγ, hS, hT⟩ := finiteCompactConvex_strictSeparation
    (S := {x}) isCompact_singleton (convex_singleton x)
    hTc hTv (Set.disjoint_singleton_left.mpr hx)
  exact ⟨c, r, γ, hγ, hS x (Set.mem_singleton x), hT⟩

end AlbertSequential
