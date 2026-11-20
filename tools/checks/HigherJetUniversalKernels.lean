module

import AppF.HigherJetUniversalKernels
import AppF.HigherJetNativeOrthogonality
import AppF.SecondOrderDimensions
import OctonionGeometry

open AlbertSequential AlbertSequential.AppF HigherJetCoefficients

universe u

example (b : HigherJetBase) (M : HigherJetHermitian b b.threshold) :
    ((∀ n, n ≠ b.threshold → higherJetAlbertCoefficient M n = 0) ∧
      ∀ w : Albert, w ∈ (H3Subalgebra b.nativeLevel).carrier →
        tracePairing w (higherJetAlbertCoefficient M b.threshold) = 0) ↔
      ∀ (T : Type u) [NonUnitalRing T] [Module ℝ T] [IsScalarTower ℝ T T] [SMulCommClass ℝ T T]
        (f : HigherJetHermitian b b.threshold →ₗ[ℝ] T),
          IsCoefficientJordanMap (conjugate b b.threshold) bilinear (conjugate_product b b.threshold) f →
            f M = 0 :=
  (higherJetHermitianKernel_iff_top_orthogonal b M).symm.trans
    (higherJetHermitian_universal_kernel_all_universes b M)

example : octAssociator octJ octL (octonionMul (octonionMul octI octJ) octL) =
    (-2 : ℝ) • octI := by
  rw [octK_eq_mul]
  exact octAssociator_real_extra_direction

example (q : Quaternion ℝ) : ∃ p : Quaternion ℝ,
    octAssociator octI octJ (octonionMul (p, 0) octL) = octonionMul (q, 0) octL := by
  have mulL (x : Quaternion ℝ) : octonionMul (x, 0) octL = (0, x) := by
    change (x * 0 - star (1 : Quaternion ℝ) * 0, (1 : Quaternion ℝ) * x + 0 * star 0) = (0, x)
    simp
  obtain ⟨p, hp⟩ := quaternionicLeadingAssociator_representative q
  exact ⟨p, by simpa only [mulL] using hp⟩

example (x : E2) :
    x.val ∈ Kso ↔ ∀ (T : Type u) [NonUnitalRing T] [Module ℝ T] [IsScalarTower ℝ T T]
      [SMulCommClass ℝ T T] (f : E2 →ₗ[ℝ] T), IsE2JordanHom f → f x = 0 :=
  secondOrder_universal_kernel_all_universes x

example : Module.finrank ℝ (higherJetHermitianKernel .real) = 21 :=
  higherJetHermitianKernel_finrank .real

example : Module.finrank ℝ Kso = 18 := secondOrderKernel_finrank

example : Module.finrank ℝ (higherJetHermitianKernel .quaternionic) = 12 :=
  higherJetHermitianKernel_finrank .quaternionic

#print axioms higherJetHermitian_universal_kernel_all_universes
#print axioms secondOrder_universal_kernel_all_universes
#print axioms octAssociator_real_extra_direction
#print axioms quaternionicLeadingAssociator_representative
#print axioms higherJetHermitianKernel_finrank
#print axioms secondOrderKernel_finrank
