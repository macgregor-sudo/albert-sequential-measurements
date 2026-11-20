/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityTransport
public import NativeCubicLowerBounds

/-! The actual open positive cone of the native Albert algebra. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.WindowProbability

open NativeAnalysis Set Filter
open scoped Topology

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

/-- The interior of the native Jordan square cone. -/
def albertOpenPositiveCone : Set Albert := interior {X | IsPositive X}

/-- Strict positivity is a positive lower bound in the Jordan square order. -/
def AlbertStrictPositive (Y : Albert) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ IsPositive (Y - ε • albertUnit)

theorem albertStrictPositive_iff_atoms (Y : Albert) :
    AlbertStrictPositive Y ↔ ∀ p : Albert, IsAtom p → 0 < tracePairing Y p := by
  constructor
  · rintro ⟨ε, hε, hY⟩ p hp
    have h := tracePairing_positive_nonnegative _ p hY (isPositive_idempotent p hp.1)
    rw [tracePairing_sub_left, tracePairing_smul_left, tracePairing_comm albertUnit,
      tracePairing_unit_right, hp.2, mul_one] at h
    linarith
  · intro hY
    obtain ⟨g, d, hd⟩ := nativeDiagonalization Y
    have hpos (i : Fin 3) : 0 < d i := by
      let p := g.linearEquiv.symm (diagAtom i)
      have hp : IsAtom p := g.symm.map_isAtom (diagAtom_isAtom i)
      have h := hY p hp
      rw [← nativeAutomorphism_pairing g Y p, hd, tracePairing_comm] at h
      change 0 < tracePairing (g.linearEquiv (g.linearEquiv.symm (diagAtom i))) (diagonalElement d) at h
      rwa [LinearEquiv.apply_symm_apply, tracePairing_diagAtom] at h
    let ε := min (d 0) (min (d 1) (d 2))
    have hε : 0 < ε := lt_min (hpos 0) (lt_min (hpos 1) (hpos 2))
    have hle (i : Fin 3) : ε ≤ d i := by
      fin_cases i
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    have hg : g.linearEquiv (Y - ε • albertUnit) = diagonalElement (fun i => d i - ε) := by
      rw [map_sub, map_smul, g.preserves_unit, hd, diagonal_sub_scalar_unit]
    have hdiag := diagonal_positive_of_entries _ (fun i => sub_nonneg.mpr (hle i))
    rw [← hg] at hdiag
    have hback := nativeAutomorphism_positive (nativeAutomorphismInverse g) _ hdiag
    exact ⟨ε, hε, by simpa only [nativeAutomorphismInverse_apply, LinearEquiv.symm_apply_apply] using hback⟩

private theorem isOpen_albertPositiveTracePair : IsOpen {xy : Albert × Albert | 0 < tracePairing xy.1 xy.2} :=
  (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))).preimage continuous_tracePairing

theorem isOpen_albertStrictPositive : IsOpen {Y : Albert | AlbertStrictPositive Y} := by
  rw [isOpen_iff_mem_nhds]
  intro Y hY
  change ∀ᶠ X in 𝓝 Y, AlbertStrictPositive X
  have hpos (p : Albert) (hp : p ∈ {p : Albert | IsAtom p}) :
      ∀ᶠ z : Albert × Albert in 𝓝 (Y,p), 0 < tracePairing z.1 z.2 := by
    have h : (Y,p) ∈ {xy : Albert × Albert | 0 < tracePairing xy.1 xy.2} :=
      (albertStrictPositive_iff_atoms Y).mp hY p hp
    exact isOpen_albertPositiveTracePair.mem_nhds h
  have h := isCompact_atomSet.eventually_forall_of_forall_eventually
    (P := fun X p : Albert => 0 < tracePairing X p) hpos
  exact h.mono (fun X hx => (albertStrictPositive_iff_atoms X).mpr hx)

theorem albertStrictPositive_mem_openCone (Y : Albert) :
    AlbertStrictPositive Y ↔ Y ∈ albertOpenPositiveCone := by
  constructor
  · intro hY
    apply interior_maximal _ isOpen_albertStrictPositive hY
    intro x hx
    change IsPositive x
    obtain ⟨ε, hε, hx'⟩ := hx
    have he : IsPositive albertUnit := isPositive_idempotent _ (jordanMul_albertUnit_left _)
    have hs := isPositive_smul ε albertUnit hε.le he
    simpa only [sub_add_cancel] using isPositive_add _ _ hx' hs
  · intro hY
    let f (ε : ℝ) := Y - ε • albertUnit
    have hf : Continuous f :=
      (continuous_const : Continuous (fun _ : ℝ => Y)).sub (continuous_id.smul continuous_const)
    have hf0 : f 0 = Y := by simp [f]
    have hpre : 0 ∈ f ⁻¹' albertOpenPositiveCone := by
      change f 0 ∈ albertOpenPositiveCone
      rwa [hf0]
    have hopen : IsOpen (f ⁻¹' albertOpenPositiveCone) := isOpen_interior.preimage hf
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hpre)
    refine ⟨r / 2, half_pos hr, ?_⟩
    have hmem : r / 2 ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
      linarith
    exact interior_subset (hball hmem)

theorem albertStrictPositive_diagonalization {Y : Albert} (hY : AlbertStrictPositive Y) :
    ∃ g : NativeAlbertAutomorphism, ∃ d : Fin 3 → ℝ,
      (∀ i, 0 < d i) ∧ g.linearEquiv Y = diagonalElement d := by
  obtain ⟨g, d, hd⟩ := nativeDiagonalization Y
  refine ⟨g, d, fun i => ?_, hd⟩
  let p := g.linearEquiv.symm (diagAtom i)
  have hp : IsAtom p := g.symm.map_isAtom (diagAtom_isAtom i)
  have h := (albertStrictPositive_iff_atoms Y).mp hY p hp
  rw [← nativeAutomorphism_pairing g Y p, hd, tracePairing_comm] at h
  change 0 < tracePairing (g.linearEquiv (g.linearEquiv.symm (diagAtom i))) (diagonalElement d) at h
  rwa [LinearEquiv.apply_symm_apply, tracePairing_diagAtom] at h

end AlbertSequential.WindowProbability
