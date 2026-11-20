/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCornerLorentz
import Mathlib.Tactic.Module

/-! The exact basis change between the printed Clifford action and the native spinor action. -/
@[expose] public section
noncomputable section

open Matrix
open scoped Matrix

namespace AlbertSequential.NativeAnalysis

/-- Componentwise octonion conjugation changes the native right-multiplication
action to the paper's left-multiplication action. -/
def spinorOctonionConjugation (w : Octonion × Octonion) : Octonion × Octonion :=
  (octonionConj w.1, octonionConj w.2)

theorem spinorOctonionConjugation_involutive : Function.Involutive spinorOctonionConjugation :=
  fun w => Prod.ext (octonionConj_conj w.1) (octonionConj_conj w.2)

private theorem octDot_conjugation (u v : Octonion) :
    octDot (octonionConj u) (octonionConj v) = octDot u v := by
  change octonionReal (octonionMul (octonionConj u) (octonionConj (octonionConj v))) = _
  rw [octonionConj_conj, octonionReal_mul_comm]
  exact octDot_comm _ _

theorem spinorOctonionConjugation_orthogonal (u v : Octonion × Octonion) :
    octDot (spinorOctonionConjugation u).1 (spinorOctonionConjugation v).1 +
      octDot (spinorOctonionConjugation u).2 (spinorOctonionConjugation v).2 =
    octDot u.1 v.1 + octDot u.2 v.2 :=
  congrArg₂ (· + ·) (octDot_conjugation u.1 v.1) (octDot_conjugation u.2 v.2)

private theorem firstHalf_left_action (x : nativePeirceZero (diagAtom 0)) (w : Octonion × Octonion) :
    spinorOctonionConjugation
        (firstHalfReadout ((2 : ℝ) • jordanMul (x : Albert)
          (firstHalfInclusion (spinorOctonionConjugation w)))) =
      (x.val.1 1 • w.1 + octonionMul (x.val.2 2) w.2,
       x.val.1 2 • w.2 + octonionMul (octonionConj (x.val.2 2)) w.1) := by
  have hz := congrArg (fun y : Albert => y.1 0) ((mem_nativePeirceZero _ x).mp x.property)
  rw [first_atom_mul] at hz
  change x.val.1 0 = 0 at hz
  let u := octonionConj w.1
  let v := octonionConj w.2
  apply Prod.ext
  · change octonionConj ((2 : ℝ) • (jordanMul (x : Albert) (firstHalfInclusion (u,v))).2 0) =
        x.val.1 1 • w.1 + octonionMul (x.val.2 2) w.2
    rw [jordanMul_upper01]
    change octonionConj ((2 : ℝ) • ((1 / 2 : ℝ) •
        ((x.val.1 0 + x.val.1 1) • u + (0 + 0 : ℝ) • x.val.2 0 +
          octonionMul (x.val.2 1) (octonionConj 0) +
          octonionMul v (octonionConj (x.val.2 2))))) = _
    simp only [hz, u, v, zero_add, zero_smul, add_zero, octonionConj_zero,
      octonionMul_zero_right, smul_smul, octonionConj_smul, octonionConj_add,
      octonionConj_mul, octonionConj_conj]
    module
  · change octonionConj ((2 : ℝ) • (jordanMul (x : Albert) (firstHalfInclusion (u,v))).2 1) =
        x.val.1 2 • w.2 + octonionMul (octonionConj (x.val.2 2)) w.1
    rw [jordanMul_upper02]
    change octonionConj ((2 : ℝ) • ((1 / 2 : ℝ) •
        ((x.val.1 0 + x.val.1 2) • v + (0 + 0 : ℝ) • x.val.2 1 +
          octonionMul (x.val.2 0) 0 + octonionMul u (x.val.2 2)))) = _
    simp only [hz, u, v, zero_add, zero_smul, add_zero, octonionMul_zero_right,
      smul_smul, octonionConj_smul, octonionConj_add, octonionConj_mul, octonionConj_conj]
    module

/-- In the printed spinor basis the actual native representation has diagonal blocks
`a I`, `b I` and off-diagonal blocks `L_z`, `L_(conj z)`. -/
theorem nativeHalfMatrix_printedClifford_action (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) (w : Octonion × Octonion) :
    let z := (chosenAtomNormalizer p hp).linearEquiv (x : Albert)
    spinorOctonionConjugation (octonionPairCoordinates.symm
      (nativeHalfMatrix p hp x *ᵥ octonionPairCoordinates (spinorOctonionConjugation w))) =
    (z.1 1 • w.1 + octonionMul (z.2 2) w.2,
      z.1 2 • w.2 + octonionMul (octonionConj (z.2 2)) w.1) := by
  intro z
  have hz : z ∈ nativePeirceZero (diagAtom 0) := by
    let g := chosenAtomNormalizer p hp
    change jordanMul (diagAtom 0) (g.linearEquiv x) = 0
    rw [← atomNormalizer_first p hp, ← g.preserves_product,
      (mem_nativePeirceZero p x).mp x.property, map_zero]
  rw [nativeHalfMatrix_eq_first]
  change spinorOctonionConjugation (octonionPairCoordinates.symm
    (firstHalfMatrix z *ᵥ octonionPairCoordinates (spinorOctonionConjugation w))) = _
  unfold firstHalfMatrix
  rw [LinearMap.toMatrix'_mulVec]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.smul_apply]
  exact firstHalf_left_action ⟨z,hz⟩ w

/-- The printed lower block is the transpose of the printed upper block. -/
theorem printedSpinor_octonionLeft_adjoint (z u v : Octonion) :
    octDot (octonionMul z u) v = octDot u (octonionMul (octonionConj z) v) :=
  octDot_mul_left z u v

end AlbertSequential.NativeAnalysis
