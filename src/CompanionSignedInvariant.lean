/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeAtomCompression
public import NativeMatrixTrace

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def signedThreeInvariant (x y z : Albert) : ℝ :=
  tracePairing (quadraticMap x (quadraticMap y z) - quadraticMap y (quadraticMap x z))
    (quadraticMap z (jordanMul x y))

theorem signedThreeInvariant_swap (x y z : Albert) :
    signedThreeInvariant y x z = - signedThreeInvariant x y z := by
  unfold signedThreeInvariant
  rw [jordanMul_comm y x,tracePairing_sub_left,tracePairing_sub_left]
  ring

theorem signedThreeInvariant_scale (a b c : ℝ) (x y z : Albert) :
    signedThreeInvariant (a • x) (b • y) (c • z) = a^3 * b^3 * c^3 * signedThreeInvariant x y z := by
  simp only [signedThreeInvariant,tracePairing_sub_left,quadraticMap_smul_left,quadraticMap_smul_right,
    jordanMul_smul_left,jordanMul_smul_right,tracePairing_smul_left,tracePairing_smul_right]
  ring

/-- The third argument being an atom suffices even for unrestricted x and y. -/
theorem signedThreeInvariant_zero_of_atom (x y z : Albert) (hz : IsAtom z) :
    signedThreeInvariant x y z = 0 := by
  unfold signedThreeInvariant
  rw [quadraticMap_atom z _ hz,tracePairing_smul_right,tracePairing_sub_left,
    quadraticMap_self_adjoint,quadraticMap_self_adjoint,tracePairing_comm z (quadraticMap y (quadraticMap x z))]
  ring

end AlbertSequential.NativeAnalysis
