/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Defs
public import NativeAlbertLaws
public import DiagPeirceAnchor
public import NativePeircePropagation
public import NativeDiagonalProduct
public import NativeAutomorphisms
public import NativeCubicLowerBounds
public import NativeAtomSpanning
public import NativeSquareCone
public import NativeDensityCompactness
public import NativeWordDuality
public import NativeWordPositivity
public import NativeSupport
public import NativeReachableDensity
public import AcceptedRootAtomAdapter
public import SubalgebraCoordsAndLine
public import ThirteenTracesAndAform
public import ThreeAtomAndFourPoint
public import Mathlib.Topology.Order.Compact
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # All-State Positive Support and Permutation Symmetry for Four Generating Atoms

For any four Albert atoms `p : Fin 4 → Albert` with `0 < fourPointInvariant p`:
- `atomSum_pairing_pos`: every density `ρ : Albert` (`IsDensity ρ`) has strictly positive
  pairing with `p 0 + p 1 + p 2 + p 3` (matching the support argument in `thm:eleven(b)`).
- `exists_atom_pairing_pos`: every density `ρ` has `0 < tracePairing ρ (p j)` for some `j : Fin 4`.
- `exists_uniform_atomSum_lower_bound`: by compactness of `{ρ | IsDensity ρ}`, there is a
  uniform `c > 0` with `c ≤ tracePairing ρ (p 0 + p 1 + p 2 + p 3)` for every density `ρ`
  (and `exists_uniform_single_atom_lower_bound` gives a uniform `c > 0` with
  `∃ j, c ≤ tracePairing ρ (p j)`).
- `fourPointInvariant_comp_equiv` and `fourPointInvariant_swap_pos`: permutation symmetry of
  `fourPointInvariant` and preservation under `Equiv.swap 0 j`.
- Conditioning/prefix identities `nativeWordProbability_cons_yes`,
  `nativeWordProbability_singleton_yes`, `nativeWordProbability_cons_yes_e3`, and
  `nativeWordProbability_cons_yes_eq_e3_mul`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.BlockB

open AlbertSequential AlbertSequential.NativeAnalysis
open scoped BigOperators

/- Lean 4.36 / Mathlib v4.36.0: `Real.lt` is no longer an `irreducible_def`; in this non-module file
defeq checks of `0 < fourPointInvariant p` would evaluate the invariant. No proof here needs its body. -/
attribute [local irreducible] fourPointInvariant

/-! ## Permutation symmetry of `fourPointInvariant` -/

theorem fourPointInvariant_comp_equiv (σ : Equiv.Perm (Fin 4)) (p : Fin 4 → Albert) :
    fourPointInvariant (p ∘ σ) = fourPointInvariant p :=
  fourPointInvariant_perm_invariant σ p

theorem fourPointInvariant_swap_pos (p : Fin 4 → Albert)
    (hA : 0 < fourPointInvariant p) (j : Fin 4) :
    0 < fourPointInvariant (p ∘ Equiv.swap 0 j) := by
  rwa [fourPointInvariant_comp_equiv (Equiv.swap 0 j) p]

/-! ## Basic positivity and pairing bounds for atoms and densities -/

theorem tracePairing_atom_density_bounds (q : Albert) (hq : IsAtom q)
    (ρ : Albert) (hρ : IsDensity ρ) :
    0 ≤ tracePairing ρ q ∧ tracePairing ρ q ≤ 1 := by
  have hpos_q : IsPositive q := isPositive_idempotent q hq.1
  have hpos_cq : IsPositive (albertUnit - q) :=
    isPositive_idempotent (albertUnit - q) (complementary_idempotent q hq.1)
  have h0 : 0 ≤ tracePairing ρ q := tracePairing_positive_nonnegative ρ q hρ.1 hpos_q
  have h1 : 0 ≤ tracePairing ρ (albertUnit - q) :=
    tracePairing_positive_nonnegative ρ (albertUnit - q) hρ.1 hpos_cq
  have hsum : tracePairing ρ q + tracePairing ρ (albertUnit - q) = 1 := by
    rw [← tracePairing_add_right, add_sub_cancel, tracePairing_unit_right, hρ.2]
  exact ⟨h0, by linarith⟩

/-! ## Native yes-prefix conditioning identities -/

theorem nativeWordProbability_cons_yes {ι : Type*} (p : ι → Albert) (ρ : Albert)
    (j : ι) (hj : IsAtom (p j)) (v : Word ι) :
    nativeWordProbability p ρ ((j, true) :: v) =
      tracePairing ρ (p j) * nativeWordProbability p (p j) v := by
  unfold nativeWordProbability
  rw [nativeBranchState_cons, nativeOutcome]
  simp only [↓reduceIte, AlbertSequential.quadraticMap_atom (p j) ρ hj]
  rw [tracePairing_comm (p j) ρ]
  exact nativeWordProbability_smul p (tracePairing ρ (p j)) (p j) v

theorem nativeWordProbability_singleton_yes {ι : Type*} (p : ι → Albert) (ρ : Albert)
    (j : ι) (hj : IsAtom (p j)) :
    nativeWordProbability p ρ [(j, true)] = tracePairing ρ (p j) := by
  rw [nativeWordProbability_cons_yes p ρ j hj []]
  change tracePairing ρ (p j) * albertTrace (p j) = tracePairing ρ (p j)
  rw [hj.2, mul_one]

theorem nativeWordProbability_cons_yes_e3 {ι : Type*} (p : ι → Albert)
    (j : ι) (hj : IsAtom (p j)) (v : Word ι) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) ((j, true) :: v) =
      (1 / 3 : ℝ) * nativeWordProbability p (p j) v := by
  rw [nativeWordProbability_cons_yes p _ j hj v, tracePairing_smul_left,
    tracePairing_comm, tracePairing_unit_right, hj.2, mul_one]

theorem nativeWordProbability_cons_yes_eq_e3_mul {ι : Type*} (p : ι → Albert) (ρ : Albert)
    (j : ι) (hj : IsAtom (p j)) (v : Word ι) :
    nativeWordProbability p ρ ((j, true) :: v) =
      (3 * tracePairing ρ (p j)) *
        nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) ((j, true) :: v) := by
  rw [nativeWordProbability_cons_yes p ρ j hj v, nativeWordProbability_cons_yes_e3 p j hj v]
  ring

/-! ## Diagonal decomposition of a density and atom-sum support -/

private theorem tracePairing_diagAtom_sum (k : Fin 3) (d : Fin 3 → ℝ) :
    tracePairing (diagAtom k) (∑ j : Fin 3, d j • diagAtom j) = d k := by
  have hdiag : tracePairing (diagAtom k) (diagAtom k) = 1 := by
    unfold tracePairing
    rw [(diagAtom_isAtom k).1, (diagAtom_isAtom k).2]
  have hortho : ∀ j : Fin 3, j ≠ k → tracePairing (diagAtom k) (diagAtom j) = 0 := fun j hjk => by
    unfold tracePairing
    rw [diagAtom_orthogonal hjk.symm, albertTrace_zero]
  have hsum : ∀ s : Finset (Fin 3),
      tracePairing (diagAtom k) (∑ j ∈ s, d j • diagAtom j) =
        ∑ j ∈ s, d j * tracePairing (diagAtom k) (diagAtom j) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, tracePairing]
      rw [jordanMul_zero_right, albertTrace_zero]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, tracePairing_add_right,
        tracePairing_smul_right, ih]
  rw [hsum, Finset.sum_eq_single k (fun j _ hjk => by rw [hortho j hjk, mul_zero])
    (fun hk => absurd (Finset.mem_univ k) hk), hdiag, mul_one]

private theorem realConnector01_ne_zero : realConnector01 ≠ 0 := by
  intro h0
  have h := congrArg (fun x => albertTrace (jordanMul x x)) h0
  rw [jordanMul_realConnector01_self, jordanMul_zero_left, albertTrace_zero,
    albertTrace_add, (diagAtom_isAtom 0).2, (diagAtom_isAtom 1).2] at h
  norm_num at h

private theorem not_all_mem_lineSubalgebra (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (r : Albert) (hr : IsAtom r) :
    ¬ (∀ i : Fin 4, p i ∈ (lineSubalgebra r hr).carrier) := by
  intro hmem
  have hgen : GeneratesAlbert p := (fourPointInvariant_pos_iff p hp).mp hA
  obtain ⟨g, hg⟩ := atom_to_diagAtom0 r hr
  let x : Albert := g.linearEquiv.symm realConnector01
  have hx_mem : x ∈ (lineSubalgebra r hr).carrier := hgen x (lineSubalgebra r hr) hmem
  have hx_idem : jordanMul r (jordanMul r x) = jordanMul r x :=
    (mem_lineSubalgebra_iff_idem r hr x).mp hx_mem
  have hmap := congrArg g.linearEquiv hx_idem
  simp only [g.preserves_product, hg] at hmap
  have hgx : g.linearEquiv x = realConnector01 := g.linearEquiv.apply_symm_apply realConnector01
  rw [hgx, jordanMul_diagAtom0_realConnector01, jordanMul_smul_right,
    jordanMul_diagAtom0_realConnector01, smul_smul] at hmap
  have hdiff : ((1 / 2 * (1 / 2) : ℝ) • realConnector01 - (1 / 2 : ℝ) • realConnector01) = 0 :=
    sub_eq_zero.mpr hmap
  have hscale : (-(1 / 4 : ℝ)) • realConnector01 = 0 := by
    rw [← hdiff]
    module
  exact realConnector01_ne_zero ((smul_eq_zero.mp hscale).resolve_left (by norm_num))

private theorem exists_atom_orthogonal_of_sum_zero (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (ρ : Albert) (hρ : IsDensity ρ) (hzero : tracePairing ρ (p 0 + p 1 + p 2 + p 3) = 0) :
    ∃ r : Albert, IsAtom r ∧ tracePairing r (p 0 + p 1 + p 2 + p 3) = 0 := by
  let y : Albert := p 0 + p 1 + p 2 + p 3
  have hy_pos : IsPositive y :=
    isPositive_add _ _ (isPositive_add _ _ (isPositive_add _ _
      (isPositive_idempotent _ (hp 0).1) (isPositive_idempotent _ (hp 1).1))
      (isPositive_idempotent _ (hp 2).1)) (isPositive_idempotent _ (hp 3).1)
  obtain ⟨g, d, hg⟩ := nativeDiagonalization ρ
  have hgρ : g.linearEquiv ρ = ∑ k : Fin 3, d k • diagAtom k :=
    hg.trans (diagonalElement_eq_sum_atoms d)
  have hd_nonneg : ∀ k : Fin 3, 0 ≤ d k := fun k => by
    have hpos_g : IsPositive (g.linearEquiv ρ) := nativeAutomorphism_positive g ρ hρ.1
    have hpos_k : IsPositive (diagAtom k) := isPositive_idempotent _ (diagAtom_isAtom k).1
    have hp_nn := tracePairing_positive_nonnegative (diagAtom k) (g.linearEquiv ρ) hpos_k hpos_g
    rwa [hgρ, tracePairing_diagAtom_sum] at hp_nn
  have hd_sum : ∑ k : Fin 3, d k = 1 := by
    have htr : albertTrace (∑ k : Fin 3, d k • diagAtom k) = 1 := by
      rw [← hgρ, g.preserves_trace, hρ.2]
    rw [Fin.sum_univ_three] at htr ⊢
    simp only [albertTrace_add, albertTrace_smul, (diagAtom_isAtom _).2, mul_one] at htr
    exact htr
  have hk_exists : ∃ k : Fin 3, 0 < d k := by
    by_contra hnone
    push Not at hnone
    have hall0 : ∀ k : Fin 3, d k = 0 := fun k => le_antisymm (hnone k) (hd_nonneg k)
    have hsum0 : ∑ k : Fin 3, d k = 0 := Finset.sum_eq_zero fun k _ => hall0 k
    linarith
  obtain ⟨k, hdk⟩ := hk_exists
  let r : Fin 3 → Albert := fun j => (nativeAutomorphismInverse g).linearEquiv (diagAtom j)
  have hr_atom : ∀ j : Fin 3, IsAtom (r j) := fun j =>
    nativeAutomorphism_isAtom (nativeAutomorphismInverse g) (diagAtom j) (diagAtom_isAtom j)
  have hρ_decomp : ρ = ∑ j : Fin 3, d j • r j := by
    apply g.linearEquiv.injective
    rw [hgρ, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    congr 1
    exact (g.linearEquiv.apply_symm_apply (diagAtom j)).symm
  have hterm_nn : ∀ j : Fin 3, 0 ≤ d j * tracePairing (r j) y := fun j =>
    mul_nonneg (hd_nonneg j)
      (tracePairing_positive_nonnegative (r j) y (isPositive_idempotent _ (hr_atom j).1) hy_pos)
  have hsum_zero : ∑ j : Fin 3, d j * tracePairing (r j) y = 0 := by
    have h : tracePairing ρ y = 0 := hzero
    rw [hρ_decomp, Fin.sum_univ_three] at h
    simp only [tracePairing_add_left, tracePairing_smul_left] at h
    rw [Fin.sum_univ_three]
    exact h
  have hk_term : d k * tracePairing (r k) y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm_nn j).mp hsum_zero k (Finset.mem_univ k)
  exact ⟨r k, hr_atom k, (mul_eq_zero.mp hk_term).resolve_left hdk.ne'⟩

theorem atomSum_pairing_pos (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (ρ : Albert) (hρ : IsDensity ρ) :
    0 < tracePairing ρ (p 0 + p 1 + p 2 + p 3) := by
  let y : Albert := p 0 + p 1 + p 2 + p 3
  have hy_pos : IsPositive y :=
    isPositive_add _ _ (isPositive_add _ _ (isPositive_add _ _
      (isPositive_idempotent _ (hp 0).1) (isPositive_idempotent _ (hp 1).1))
      (isPositive_idempotent _ (hp 2).1)) (isPositive_idempotent _ (hp 3).1)
  have hnn : 0 ≤ tracePairing ρ y := tracePairing_positive_nonnegative ρ y hρ.1 hy_pos
  rcases hnn.lt_or_eq with hpos | heq
  · exact hpos
  · exfalso
    obtain ⟨r, hr, hry⟩ := exists_atom_orthogonal_of_sum_zero p hp ρ hρ heq.symm
    have hr_nn : ∀ i : Fin 4, 0 ≤ tracePairing r (p i) := fun i =>
      tracePairing_positive_nonnegative r (p i) (isPositive_idempotent r hr.1)
        (isPositive_idempotent (p i) (hp i).1)
    have hsum_r : tracePairing r (p 0) + tracePairing r (p 1) +
        tracePairing r (p 2) + tracePairing r (p 3) = 0 := by
      simpa only [y, tracePairing_add_right] using hry
    have hz0 : tracePairing r (p 0) = 0 := by linarith [hr_nn 0, hr_nn 1, hr_nn 2, hr_nn 3]
    have hz1 : tracePairing r (p 1) = 0 := by linarith [hr_nn 0, hr_nn 1, hr_nn 2, hr_nn 3]
    have hz2 : tracePairing r (p 2) = 0 := by linarith [hr_nn 0, hr_nn 1, hr_nn 2, hr_nn 3]
    have hz3 : tracePairing r (p 3) = 0 := by linarith [hr_nn 0, hr_nn 1, hr_nn 2, hr_nn 3]
    have hr_zero : ∀ i : Fin 4, tracePairing r (p i) = 0 := fun i => by
      match i with
      | 0 => exact hz0
      | 1 => exact hz1
      | 2 => exact hz2
      | 3 => exact hz3
    have hline : ∀ i : Fin 4, p i ∈ (lineSubalgebra r hr).carrier := fun i => by
      rw [mem_lineSubalgebra_iff]
      have hsup := (native_positive_zero_pairing_support r (p i) hr.1
        (isPositive_idempotent (p i) (hp i).1) (by rw [tracePairing_comm]; exact hr_zero i)).1
      rw [hsup, hr_zero i, zero_smul]
    exact not_all_mem_lineSubalgebra p hp hA r hr hline

theorem exists_atom_pairing_pos (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ j : Fin 4, 0 < tracePairing ρ (p j) := by
  have hsum := atomSum_pairing_pos p hp hA ρ hρ
  rw [tracePairing_add_right, tracePairing_add_right, tracePairing_add_right] at hsum
  by_contra hnone
  push Not at hnone
  linarith [hnone 0, hnone 1, hnone 2, hnone 3]

/-! ## Uniform positive lower bound over all densities -/

theorem exists_uniform_atomSum_lower_bound (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : Albert, IsDensity ρ →
      c ≤ tracePairing ρ (p 0 + p 1 + p 2 + p 3) := by
  have heq : (fun ρ : Albert => tracePairing ρ (p 0 + p 1 + p 2 + p 3)) =
      fun ρ : Albert =>
        nativeWordProbability p ρ [(0, true)] + nativeWordProbability p ρ [(1, true)] +
        nativeWordProbability p ρ [(2, true)] + nativeWordProbability p ρ [(3, true)] := by
    funext ρ
    simp only [tracePairing_add_right,
      nativeWordProbability_singleton_yes p ρ 0 (hp 0),
      nativeWordProbability_singleton_yes p ρ 1 (hp 1),
      nativeWordProbability_singleton_yes p ρ 2 (hp 2),
      nativeWordProbability_singleton_yes p ρ 3 (hp 3)]
  have hcont : Continuous (fun ρ : Albert => tracePairing ρ (p 0 + p 1 + p 2 + p 3)) := by
    rw [heq]
    exact (((continuous_nativeWordProbability p [(0, true)]).add
      (continuous_nativeWordProbability p [(1, true)])).add
      (continuous_nativeWordProbability p [(2, true)])).add
      (continuous_nativeWordProbability p [(3, true)])
  exact isCompact_density_set.exists_forall_le' hcont.continuousOn
    (fun ρ hρ => atomSum_pairing_pos p hp hA ρ hρ)

theorem exists_uniform_single_atom_lower_bound (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : Albert, IsDensity ρ →
      ∃ j : Fin 4, c ≤ tracePairing ρ (p j) := by
  obtain ⟨c0, hc0, hbound⟩ := exists_uniform_atomSum_lower_bound p hp hA
  refine ⟨c0 / 4, by linarith, fun ρ hρ => ?_⟩
  have hsum := hbound ρ hρ
  rw [tracePairing_add_right, tracePairing_add_right, tracePairing_add_right] at hsum
  by_contra hnone
  push Not at hnone
  linarith [hnone 0, hnone 1, hnone 2, hnone 3]

end AlbertSequential.BlockB

#print axioms AlbertSequential.BlockB.fourPointInvariant_comp_equiv
#print axioms AlbertSequential.BlockB.fourPointInvariant_swap_pos
#print axioms AlbertSequential.BlockB.tracePairing_atom_density_bounds
#print axioms AlbertSequential.BlockB.atomSum_pairing_pos
#print axioms AlbertSequential.BlockB.exists_atom_pairing_pos
#print axioms AlbertSequential.BlockB.exists_uniform_atomSum_lower_bound
#print axioms AlbertSequential.BlockB.exists_uniform_single_atom_lower_bound
#print axioms AlbertSequential.BlockB.nativeWordProbability_cons_yes
#print axioms AlbertSequential.BlockB.nativeWordProbability_singleton_yes
#print axioms AlbertSequential.BlockB.nativeWordProbability_cons_yes_e3
#print axioms AlbertSequential.BlockB.nativeWordProbability_cons_yes_eq_e3_mul
