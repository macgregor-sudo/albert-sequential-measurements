/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeWordPositivity
public import NativeDiagonalProduct
public import NativeCubicLowerBounds
public import NativeAtomSpanning
public import NativeSupport
public import ThreeAtomAndFourPoint
public import Mathlib.Analysis.Convex.Extreme

/-! Pure states as extreme points of the native normalized square cone, core §3. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

theorem nativeDensity_eq_convexHull_atoms :
    {ρ : Albert | IsDensity ρ} = convexHull ℝ {p | IsAtom p} := by
  apply Set.Subset.antisymm _ (convexHull_min (s := {p : Albert | IsAtom p}) (t := {ρ : Albert | IsDensity ρ}) (fun _ hp => ⟨isPositive_idempotent _ hp.1,hp.2⟩) convex_density_set)
  intro ρ hρ
  obtain ⟨g,d,hg⟩ := nativeDiagonalization ρ
  have hd (i : Fin 3) : 0 ≤ d i := by
    have h := tracePairing_positive_nonnegative (diagAtom i) (g.linearEquiv ρ)
      (isPositive_idempotent _ (diagAtom_isAtom i).1) (nativeAutomorphism_positive g ρ hρ.1)
    rwa [tracePairing_diagAtom,hg] at h
  have hsum : ∑ i, d i = 1 := by
    change albertTrace (diagonalElement d) = 1
    rw [← hg, g.preserves_trace, hρ.2]
  have hrep : ρ = ∑ i, d i • g.symm.linearEquiv (diagAtom i) := by
    apply g.linearEquiv.injective
    rw [hg,diagonalElement_eq_sum_atoms,map_sum]
    simp only [map_smul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x : Albert => d i • x) (g.linearEquiv.apply_symm_apply _).symm)
  rw [hrep]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hd i) hsum
    (fun i _ => subset_convexHull ℝ _ (g.symm.map_isAtom (diagAtom_isAtom i)))

theorem nativePureState_iff_atom (p : Albert) :
    p ∈ Set.extremePoints ℝ {ρ : Albert | IsDensity ρ} ↔ IsAtom p := by
  constructor
  · rw [nativeDensity_eq_convexHull_atoms]
    exact fun hp => extremePoints_convexHull_subset hp
  · intro hp
    refine mem_extremePoints_iff_left.mpr ⟨⟨isPositive_idempotent _ hp.1,hp.2⟩,?_⟩
    rintro x hx y hy ⟨a,b,ha,hb,hab,hp'⟩
    have hbound (z : Albert) (hz : IsDensity z) : tracePairing z p ≤ 1 := by
      have h := (quadraticMap_trace_bounds p z hp.1 hz.1).2
      rwa [albertTrace_quadraticMap,hp.1,tracePairing_comm,hz.2] at h
    have hpair := congrArg (fun z => tracePairing z p) hp'
    change tracePairing (a • x + b • y) p = tracePairing p p at hpair
    rw [tracePairing_add_left,tracePairing_smul_left,tracePairing_smul_left] at hpair
    have hpp : tracePairing p p = 1 := by rw [tracePairing,hp.1,hp.2]
    have hx1 : tracePairing x p = 1 := by
      rw [hpp] at hpair
      by_contra hne
      have hlt := lt_of_le_of_ne (hbound x hx) hne
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr (hbound y hy)), mul_pos ha (sub_pos.mpr hlt)]
    have hh := native_idempotent_certainty_ideality p x hp.1 hx hx1
    rw [quadraticMap_atom _ _ hp,tracePairing_comm,hx1,one_smul] at hh
    exact hh.symm
end AlbertSequential
