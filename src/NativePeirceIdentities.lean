module

public import NativeAutomorphisms

/-! Universal complement/quadratic/Peirce identities from bilinearity and the
unit. These equations do not assert that an arbitrary parameter defines a
Jordan automorphism. The atom hypothesis appears in the reflection module. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem quadraticMap_complement (p x : Albert) :
    quadraticMap (albertUnit - p) x =
      x - (2 : ℝ) • jordanMul p x + quadraticMap p x := by
  unfold quadraticMap
  simp only [jordanMul_sub_left, jordanMul_sub_right,
    jordanMul_albertUnit_left, jordanMul_albertUnit_right]
  module

theorem quadraticMap_symmetry (p x : Albert) :
    quadraticMap ((2 : ℝ) • p - albertUnit) x =
      (2 : ℝ) • (quadraticMap p x + quadraticMap (albertUnit - p) x) - x := by
  rw [quadraticMap_complement]
  unfold quadraticMap
  simp only [jordanMul_sub_left, jordanMul_sub_right,
    jordanMul_smul_left, jordanMul_smul_right,
    jordanMul_albertUnit_left, jordanMul_albertUnit_right]
  module

theorem peirce_identity (p x : Albert) :
    jordanMul p x = quadraticMap p x + (1 / 4 : ℝ) •
      (x - quadraticMap ((2 : ℝ) • p - albertUnit) x) := by
  rw [quadraticMap_symmetry, quadraticMap_complement]
  module

theorem idempotent_symmetry_unit (p : Albert) (hp : jordanMul p p = p) :
    quadraticMap ((2 : ℝ) • p - albertUnit) albertUnit = albertUnit := by
  unfold quadraticMap
  simp only [jordanMul_sub_left, jordanMul_sub_right,
    jordanMul_smul_left, jordanMul_smul_right,
    jordanMul_albertUnit_left, jordanMul_albertUnit_right, hp]
  module

end AlbertSequential.NativeAnalysis
