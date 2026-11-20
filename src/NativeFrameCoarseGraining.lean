/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AcceptedRootAtomAdapter
public import NativeAutomorphisms
public import NativeWordPositivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

/-! A complete native frame's coarse no-branch and the binary complement differ. -/

@[expose] public section
noncomputable section

namespace AlbertSequential

open NativeAnalysis

/-- The no-branch obtained by grouping the other outcomes of a complete frame. -/
def frameCoarseNoUpdate (F : NativeJordanFrame) (k : Fin 3) : Albert →ₗ[ℝ] Albert :=
  ∑ i ∈ Finset.univ.erase k, quadraticMapLinear (F.atom i)

private def standardComplementSlot : Albert := (0, ![0, 0, octOne])

private theorem standardComplementSlot_ne_zero : standardComplementSlot ≠ 0 := by
  intro h
  have hr := congrArg (fun x : Albert => (x.2 2).1.re) h
  change (1 : ℝ) = 0 at hr
  norm_num at hr

private theorem diagAtom0_mul_slot :
    jordanMul (diagAtom 0) standardComplementSlot = 0 := by
  rw [jordanMul_diagAtom0]
  change ((![0, 0, 0], ![(1 / 2 : ℝ) • (0 : Octonion), (1 / 2 : ℝ) • (0 : Octonion), 0]) :
    Albert) = 0
  simp only [smul_zero]
  apply Prod.ext <;> funext j <;> fin_cases j <;> rfl

private theorem diagAtom1_mul_slot :
    jordanMul (diagAtom 1) standardComplementSlot = (1 / 2 : ℝ) • standardComplementSlot := by
  rw [jordanMul_diagAtom1]
  change ((![0, 0, 0], ![(1 / 2 : ℝ) • (0 : Octonion), 0, (1 / 2 : ℝ) • octOne]) : Albert) =
    (1 / 2 : ℝ) • standardComplementSlot
  apply Prod.ext <;> funext j <;> fin_cases j
  all_goals
    first
    | rfl
    | (change (0 : ℝ) = (1 / 2 : ℝ) * 0; norm_num)
    | (change (0 : Octonion) = (1 / 2 : ℝ) • (0 : Octonion); rw [smul_zero])

private theorem diagAtom2_mul_slot :
    jordanMul (diagAtom 2) standardComplementSlot = (1 / 2 : ℝ) • standardComplementSlot := by
  rw [jordanMul_diagAtom2]
  change ((![0, 0, 0], ![0, (1 / 2 : ℝ) • (0 : Octonion), (1 / 2 : ℝ) • octOne]) : Albert) =
    (1 / 2 : ℝ) • standardComplementSlot
  apply Prod.ext <;> funext j <;> fin_cases j
  all_goals
    first
    | rfl
    | (change (0 : ℝ) = (1 / 2 : ℝ) * 0; norm_num)
    | (change (0 : Octonion) = (1 / 2 : ℝ) • (0 : Octonion); rw [smul_zero])

private theorem diagAtom_quad_standardComplementSlot {i : Fin 3} (h : i ≠ 0) :
    quadraticMap (diagAtom i) standardComplementSlot = 0 := by
  have he : jordanMul (diagAtom i) standardComplementSlot = (1 / 2 : ℝ) • standardComplementSlot := by
    fin_cases i
    · exact False.elim (h rfl)
    · exact diagAtom1_mul_slot
    · exact diagAtom2_mul_slot
  unfold quadraticMap
  rw [(diagAtom_isAtom i).1, he, jordanMul_smul_right, he, two_nsmul]
  module

private theorem standardComplement_quad_slot :
    quadraticMap (albertUnit - diagAtom 0) standardComplementSlot = standardComplementSlot := by
  have hu : jordanMul (albertUnit - diagAtom 0) standardComplementSlot =
      standardComplementSlot := by
    rw [jordanMul_sub_left, jordanMul_albertUnit_left, diagAtom0_mul_slot, sub_zero]
  unfold quadraticMap
  simp only [NativeAnalysis.complementary_idempotent _ (diagAtom_isAtom 0).1, hu, two_nsmul]
  abel

/-- A nonzero coherence in the complementary corner is killed by the fine readout
and fixed by the binary no-branch. The witness exists for every frame and label. -/
theorem frameCoarseNo_separatingVector (F : NativeJordanFrame) (k : Fin 3) :
    ∃ x : Albert, x ≠ 0 ∧ frameCoarseNoUpdate F k x = 0 ∧
      quadraticMap (albertUnit - F.atom k) x = x := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 k
  let F' : NativeJordanFrame :=
    { atom := F.atom ∘ σ
      atoms := fun i => F.atoms (σ i)
      orthogonal := fun i j hij => F.orthogonal (σ i) (σ j) (fun h => hij (σ.injective h))
      sum_unit := (Equiv.sum_comp σ F.atom).trans F.sum_unit }
  obtain ⟨g, hstd⟩ := native_frame_to_standardFrame F'
  have hg (i : Fin 3) : g.linearEquiv (F.atom i) = diagAtom (σ.symm i) := by
    have h := hstd (σ.symm i)
    change g.linearEquiv (F.atom (σ (σ.symm i))) = _ at h
    rwa [σ.apply_symm_apply i] at h
  have hzero : σ.symm k = 0 := by
    apply σ.injective
    rw [σ.apply_symm_apply k]
    exact (Equiv.swap_apply_left 0 k).symm
  let x := g.linearEquiv.symm standardComplementSlot
  have hx : g.linearEquiv x = standardComplementSlot :=
    g.linearEquiv.apply_symm_apply standardComplementSlot
  have hx0 : x ≠ 0 := by
    intro h0
    apply standardComplementSlot_ne_zero
    rw [← hx, h0, map_zero]
  refine ⟨x, hx0, ?_, ?_⟩
  · apply g.linearEquiv.injective
    simp only [frameCoarseNoUpdate, LinearMap.sum_apply, quadraticMapLinear_apply, map_sum,
      map_zero, g.map_quadraticMap, hx, hg]
    apply Finset.sum_eq_zero
    intro i hi
    apply diagAtom_quad_standardComplementSlot
    rw [← hzero]
    exact fun he => (Finset.ne_of_mem_erase hi) (σ.symm.injective he)
  · apply g.linearEquiv.injective
    rw [g.map_quadraticMap, map_sub, g.preserves_unit, hg, hzero, hx]
    exact standardComplement_quad_slot

theorem frameCoarseNoUpdate_ne_binaryComplement (F : NativeJordanFrame) (k : Fin 3) :
    frameCoarseNoUpdate F k ≠ quadraticMapLinear (albertUnit - F.atom k) := by
  obtain ⟨x, hx, hcoarse, hbinary⟩ := frameCoarseNo_separatingVector F k
  intro he
  have hv := LinearMap.congr_fun he x
  rw [hcoarse, quadraticMapLinear_apply, hbinary] at hv
  exact hx hv.symm

end AlbertSequential
