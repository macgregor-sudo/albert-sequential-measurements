/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.TableValues
public import FrameSlotNormalizers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! # ω index control at an asymmetric rational configuration

`S` and `M` have three equal ω, so they cannot detect a rotated ω index.  Here is a
rational configuration of four atoms of `J` whose three ω are pairwise different:
the real rank-one projections onto

`v_A = (1,0,0)`, `v_B = (3,4,0)/5`, `v_C = (3,0,4)/5`, `v_D = (2,1,2)/3`,

placed in `J` through the quaternionic embedding `quatMatrixToAlbert
quatEmbed1` (real symmetric matrices; `jordanMul_quatMatrixToAlbert`).  For real
atoms `ω_B = g_AC g_AD g_BC g_BD`, `ω_C = g_AB g_AD g_BC g_CD`,
`ω_D = g_AB g_AC g_BD g_CD` with `g` the Gram matrix of the vectors, here
`ω_B = 12/125`, `ω_C = 84/625`, `ω_D = 28/125` (computed below in Lean from the native
double pairings; the closed forms are only a comment).  The control:

* `omegaControl_om`: the three values of `nativeTraceData` at this configuration;
* `omegaAsymmetricControl`: the interface contract `OmegaAsymmetricControl`
  (three distinct values, each `= ⟨p_A, {p_x p_y p_z}⟩` with `y` the middle letter);
* `omegaControl_rotation_detected`: binding `om` through the indices of
  `nativeCornerQ` (which is rotated, index 0 ↦ ω_C) gives different values here;
* `nativeCornerQ_eq_om`: `nativeCornerQ p = ![ω_C, ω_D, ω_B]` for every `p`, derived from
  the general identity `nativeTraceData_om_eq_triple`, independently of
  `nativeCornerQ_eq_fpOmega`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

open AlbertSequential

/-! ## Real symmetric matrices inside `J` -/

/-- A real `3 × 3` matrix placed in `J` through the first quaternion embedding. -/
def realSymAlbert (M : Matrix (Fin 3) (Fin 3) ℝ) : Albert :=
  quatMatrixToAlbert quatEmbed1 (M.map (algebraMap ℝ (Quaternion ℝ)))

theorem quat_algebraMap_re (r : ℝ) : (algebraMap ℝ (Quaternion ℝ) r).re = r := by
  rw [Algebra.algebraMap_eq_smul_one, Quaternion.re_smul]
  simp

private theorem herm_map (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : ∀ i j, M j i = M i j) :
    ∀ i j, star ((M.map (algebraMap ℝ (Quaternion ℝ))) j i) =
      (M.map (algebraMap ℝ (Quaternion ℝ))) i j := by
  intro i j
  rw [Matrix.map_apply, Matrix.map_apply, ← algebraMap_star_comm, star_trivial, hM]

theorem jordanMul_realSymAlbert (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : ∀ i j, M j i = M i j) (hN : ∀ i j, N j i = N i j) :
    jordanMul (realSymAlbert M) (realSymAlbert N) =
      realSymAlbert ((1 / 2 : ℝ) • (M * N + N * M)) := by
  refine (jordanMul_quatMatrixToAlbert quatEmbed1 quatEmbed1_isQuatEmbedding
    (herm_map M hM) (herm_map N hN) ?_).symm
  ext i j : 1
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
    smul_eq_mul]
  simp only [map_mul, map_add, map_sum, Algebra.smul_def]

theorem albertTrace_realSymAlbert (M : Matrix (Fin 3) (Fin 3) ℝ) :
    albertTrace (realSymAlbert M) = M 0 0 + M 1 1 + M 2 2 := by
  simp [albertTrace, realSymAlbert, quatMatrixToAlbert, Fin.sum_univ_three]

theorem symm_jordanHalf (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : ∀ i j, M j i = M i j) (hN : ∀ i j, N j i = N i j) :
    ∀ i j, ((1 / 2 : ℝ) • (M * N + N * M)) j i = ((1 / 2 : ℝ) • (M * N + N * M)) i j := by
  intro i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, smul_eq_mul]
  congr 1
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> rw [hM, hN, mul_comm]

/-- The double pairing of four real symmetric matrices, as a real matrix trace. -/
theorem doublePair_realSymAlbert (A B C D : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i j, A j i = A i j) (hB : ∀ i j, B j i = B i j)
    (hC : ∀ i j, C j i = C i j) (hD : ∀ i j, D j i = D i j) :
    tracePairing (jordanMul (realSymAlbert A) (realSymAlbert B))
        (jordanMul (realSymAlbert C) (realSymAlbert D)) =
      ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • (A * B + B * A) * ((1 / 2 : ℝ) • (C * D + D * C)) +
        (1 / 2 : ℝ) • (C * D + D * C) * ((1 / 2 : ℝ) • (A * B + B * A)))) 0 0 +
      ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • (A * B + B * A) * ((1 / 2 : ℝ) • (C * D + D * C)) +
        (1 / 2 : ℝ) • (C * D + D * C) * ((1 / 2 : ℝ) • (A * B + B * A)))) 1 1 +
      ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • (A * B + B * A) * ((1 / 2 : ℝ) • (C * D + D * C)) +
        (1 / 2 : ℝ) • (C * D + D * C) * ((1 / 2 : ℝ) • (A * B + B * A)))) 2 2 := by
  rw [jordanMul_realSymAlbert A B hA hB, jordanMul_realSymAlbert C D hC hD, tracePairing,
    jordanMul_realSymAlbert _ _ (symm_jordanHalf A B hA hB) (symm_jordanHalf C D hC hD),
    albertTrace_realSymAlbert]

/-! ## Real rank-one atoms -/

/-- The real rank-one matrix `v vᵀ`. -/
def dyadR (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => v i * v j

theorem dyadR_symm (v : Fin 3 → ℝ) : ∀ i j, dyadR v j i = dyadR v i j := by
  intro i j; simp [dyadR, mul_comm]

theorem isAtom_dyadR (v : Fin 3 → ℝ) (h : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    IsAtom (realSymAlbert (dyadR v)) := by
  constructor
  · rw [jordanMul_realSymAlbert _ _ (dyadR_symm v) (dyadR_symm v)]
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_three,
      dyadR, Matrix.of_apply, smul_eq_mul]
    linear_combination (v i * v j) * h
  · rw [albertTrace_realSymAlbert]
    simp only [dyadR, Matrix.of_apply]
    linear_combination h

/-! ## The configuration -/

def ctrlVec : Fin 4 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![3 / 5, 4 / 5, 0], ![3 / 5, 0, 4 / 5], ![2 / 3, 1 / 3, 2 / 3]]

/-- Four real atoms with three distinct ω. -/
def omegaControlConfig : Fin 4 → Albert := fun i => realSymAlbert (dyadR (ctrlVec i))

theorem omegaControlConfig_isAtom (i : Fin 4) : IsAtom (omegaControlConfig i) := by
  apply isAtom_dyadR
  fin_cases i <;> simp [ctrlVec] <;> norm_num

private theorem ctrl_dp (a b c d : Fin 4) :
    tracePairing (jordanMul (omegaControlConfig a) (omegaControlConfig b))
        (jordanMul (omegaControlConfig c) (omegaControlConfig d)) =
      ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • (dyadR (ctrlVec a) * dyadR (ctrlVec b) +
          dyadR (ctrlVec b) * dyadR (ctrlVec a)) *
        ((1 / 2 : ℝ) • (dyadR (ctrlVec c) * dyadR (ctrlVec d) +
          dyadR (ctrlVec d) * dyadR (ctrlVec c))) +
        (1 / 2 : ℝ) • (dyadR (ctrlVec c) * dyadR (ctrlVec d) +
          dyadR (ctrlVec d) * dyadR (ctrlVec c)) *
        ((1 / 2 : ℝ) • (dyadR (ctrlVec a) * dyadR (ctrlVec b) +
          dyadR (ctrlVec b) * dyadR (ctrlVec a))))) 0 0 +
      ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • (dyadR (ctrlVec a) * dyadR (ctrlVec b) +
          dyadR (ctrlVec b) * dyadR (ctrlVec a)) *
        ((1 / 2 : ℝ) • (dyadR (ctrlVec c) * dyadR (ctrlVec d) +
          dyadR (ctrlVec d) * dyadR (ctrlVec c))) +
        (1 / 2 : ℝ) • (dyadR (ctrlVec c) * dyadR (ctrlVec d) +
          dyadR (ctrlVec d) * dyadR (ctrlVec c)) *
        ((1 / 2 : ℝ) • (dyadR (ctrlVec a) * dyadR (ctrlVec b) +
          dyadR (ctrlVec b) * dyadR (ctrlVec a))))) 1 1 +
      ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • (dyadR (ctrlVec a) * dyadR (ctrlVec b) +
          dyadR (ctrlVec b) * dyadR (ctrlVec a)) *
        ((1 / 2 : ℝ) • (dyadR (ctrlVec c) * dyadR (ctrlVec d) +
          dyadR (ctrlVec d) * dyadR (ctrlVec c))) +
        (1 / 2 : ℝ) • (dyadR (ctrlVec c) * dyadR (ctrlVec d) +
          dyadR (ctrlVec d) * dyadR (ctrlVec c)) *
        ((1 / 2 : ℝ) • (dyadR (ctrlVec a) * dyadR (ctrlVec b) +
          dyadR (ctrlVec b) * dyadR (ctrlVec a))))) 2 2 :=
  doublePair_realSymAlbert _ _ _ _ (dyadR_symm _) (dyadR_symm _) (dyadR_symm _) (dyadR_symm _)

theorem omegaControl_t1 : fpDoublePair1 omegaControlConfig = 112 / 625 := by
  rw [fpDoublePair1, ctrl_dp]
  simp [Matrix.mul_apply, Fin.sum_univ_three, dyadR, ctrlVec]
  norm_num

theorem omegaControl_t2 : fpDoublePair2 omegaControlConfig = 4 / 25 := by
  rw [fpDoublePair2, ctrl_dp]
  simp [Matrix.mul_apply, Fin.sum_univ_three, dyadR, ctrlVec]
  norm_num

theorem omegaControl_t3 : fpDoublePair3 omegaControlConfig = 72 / 625 := by
  rw [fpDoublePair3, ctrl_dp]
  simp [Matrix.mul_apply, Fin.sum_univ_three, dyadR, ctrlVec]
  norm_num

/-- The three ω of the control configuration, by middle letter. -/
theorem omegaControl_om :
    (nativeTraceData omegaControlConfig).om 1 = 12 / 125 ∧
      (nativeTraceData omegaControlConfig).om 2 = 84 / 625 ∧
      (nativeTraceData omegaControlConfig).om 3 = 28 / 125 := by
  obtain ⟨h1, h2, h3⟩ := nativeTraceData_om omegaControlConfig
  rw [h1, h2, h3, fpOmega1, fpOmega2, fpOmega3, omegaControl_t1, omegaControl_t2,
    omegaControl_t3]
  norm_num

/-- For every four elements, `nativeCornerQ` is the ω vector rotated:
`![ω_C, ω_D, ω_B]`, derived from the middle-letter identity. -/
theorem nativeCornerQ_eq_om (p : Fin 4 → Albert) :
    nativeCornerQ p =
      ![(nativeTraceData p).om 2, (nativeTraceData p).om 3, (nativeTraceData p).om 1] := by
  funext k
  fin_cases k
  · exact (nativeTraceData_om_eq_triple p 1 2 3 (by decide)).symm
  · exact (nativeTraceData_om_eq_triple p 2 3 1 (by decide)).symm
  · exact (nativeTraceData_om_eq_triple p 3 1 2 (by decide)).symm

/-- The interface contract `Pending.OmegaAsymmetricControl` (stated verbatim). -/
theorem omegaAsymmetricControl :
    ∃ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) ∧
      (nativeTraceData p).om 1 ≠ (nativeTraceData p).om 2 ∧
      (nativeTraceData p).om 2 ≠ (nativeTraceData p).om 3 ∧
      (nativeTraceData p).om 1 ≠ (nativeTraceData p).om 3 ∧
      ∀ x y z : Letter, IsOrderingBCD x y z →
        (nativeTraceData p).om y = tracePairing (p 0) (jordanTriple (p x) (p y) (p z)) := by
  obtain ⟨h1, h2, h3⟩ := omegaControl_om
  refine ⟨omegaControlConfig, omegaControlConfig_isAtom, ?_, ?_, ?_,
    fun x y z h => nativeTraceData_om_eq_triple _ x y z h⟩ <;>
  · norm_num [h1, h2, h3]

/-- Negative control: binding `om y` through `nativeCornerQ` at index `y - 1`
(the rotation trap) gives wrong values at this configuration, for every letter. -/
theorem omegaControl_rotation_detected :
    (nativeTraceData omegaControlConfig).om 1 ≠ nativeCornerQ omegaControlConfig 0 ∧
      (nativeTraceData omegaControlConfig).om 2 ≠ nativeCornerQ omegaControlConfig 1 ∧
      (nativeTraceData omegaControlConfig).om 3 ≠ nativeCornerQ omegaControlConfig 2 := by
  obtain ⟨h1, h2, h3⟩ := omegaControl_om
  rw [nativeCornerQ_eq_om]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [h1, h2, h3]
  norm_num

end AlbertSequential.LengthSeven
