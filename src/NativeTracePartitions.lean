/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FixedSBinding
public import NativeMatrixTrace

/-! The three four-linear pair partitions determine all local Q values.
No new octonion coordinate contraction, geometric invariant or array is used. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential
open NativeAnalysis

def nativePairPartition (x y z w : Albert) : ℝ :=
  tracePairing (jordanMul x y) (jordanMul z w)

theorem nativePairPartition_swap_left (x y z w : Albert) :
    nativePairPartition x y z w = nativePairPartition y x z w := by
  rw [nativePairPartition, jordanMul_comm x y]
  rfl

theorem nativePairPartition_swap_right (x y z w : Albert) :
    nativePairPartition x y z w = nativePairPartition x y w z := by
  rw [nativePairPartition, jordanMul_comm z w]
  rfl

theorem nativePairPartition_exchange (x y z w : Albert) :
    nativePairPartition x y z w = nativePairPartition z w x y := tracePairing_comm _ _

theorem tracePairing_nested_partition (x y z w : Albert) :
    tracePairing x (jordanMul (jordanMul y z) w) = nativePairPartition x w y z := by
  rw [jordanMul_comm (jordanMul y z) w, ← tracePairing_associative x w (jordanMul y z)]
  rfl

theorem tracePairing_jordanTriple_partitions (x y z w : Albert) :
    tracePairing x (jordanTriple y z w) =
      nativePairPartition x y z w + nativePairPartition x w y z - nativePairPartition x z y w := by
  simp only [jordanTriple, tracePairing_sub_right, tracePairing_add_right, tracePairing_nested_partition]
  rw [nativePairPartition_swap_right x y w z]
  ring

theorem native_quartic_cyclic (x y z w : Albert) :
    tracePairing x (jordanTriple y z w) = tracePairing y (jordanTriple z w x) := by
  rw [tracePairing_jordanTriple_partitions, tracePairing_jordanTriple_partitions,
    nativePairPartition_exchange y z w x, nativePairPartition_swap_left w x y z,
    nativePairPartition_swap_left y x z w, nativePairPartition_exchange y w z x,
    nativePairPartition_swap_left z x y w]
  ring

theorem native_quartic_reverse (x y z w : Albert) :
    tracePairing x (jordanTriple y z w) = tracePairing x (jordanTriple w z y) := by
  rw [tracePairing_jordanTriple_partitions, tracePairing_jordanTriple_partitions,
    nativePairPartition_swap_right x w z y, nativePairPartition_swap_right x y w z,
    nativePairPartition_swap_right x z w y]
  ring

theorem native_quartic_cyclic_twice (x y z w : Albert) :
    tracePairing x (jordanTriple y z w) = tracePairing z (jordanTriple w x y) :=
  (native_quartic_cyclic x y z w).trans (native_quartic_cyclic y z w x)

theorem native_quartic_cyclic_thrice (x y z w : Albert) :
    tracePairing x (jordanTriple y z w) = tracePairing w (jordanTriple x y z) :=
  (native_quartic_cyclic_twice x y z w).trans (native_quartic_cyclic z w x y)

theorem fixedS_pair_partitions :
    nativePairPartition (fixedS 0) (fixedS 1) (fixedS 2) (fixedS 3) = 1 / 18 ∧
    nativePairPartition (fixedS 0) (fixedS 2) (fixedS 1) (fixedS 3) = 1 / 18 ∧
    nativePairPartition (fixedS 0) (fixedS 3) (fixedS 1) (fixedS 2) = 1 / 18 := by
  have h0 := congrFun nativeCornerQ_fixedS 0
  have h1 := congrFun nativeCornerQ_fixedS 1
  have h2 := congrFun nativeCornerQ_fixedS 2
  change tracePairing (fixedS 0) (jordanTriple (fixedS 1) (fixedS 2) (fixedS 3)) = 1 / 18 at h0
  change tracePairing (fixedS 0) (jordanTriple (fixedS 2) (fixedS 3) (fixedS 1)) = 1 / 18 at h1
  change tracePairing (fixedS 0) (jordanTriple (fixedS 3) (fixedS 1) (fixedS 2)) = 1 / 18 at h2
  rw [tracePairing_jordanTriple_partitions] at h0 h1 h2
  rw [nativePairPartition_swap_right (fixedS 0) (fixedS 2) (fixedS 3) (fixedS 1),
    nativePairPartition_swap_right (fixedS 0) (fixedS 3) (fixedS 2) (fixedS 1)] at h1
  rw [nativePairPartition_swap_right (fixedS 0) (fixedS 2) (fixedS 3) (fixedS 1),
    nativePairPartition_swap_right (fixedS 0) (fixedS 1) (fixedS 3) (fixedS 2)] at h2
  exact ⟨by linarith, by linarith, by linarith⟩

end AlbertSequential
