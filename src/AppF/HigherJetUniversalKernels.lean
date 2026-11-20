/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.HigherJetHermitianDimensions
public import AppF.SecondOrderCoefficientIdeal
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.ULift

/-! The common Hermitian jet kernels tested against targets in any universe. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF
open HigherJetCoefficients

universe u

variable {A : Type} [NonUnitalRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

local instance : IsScalarTower ℝ (ULift.{u} A) (ULift.{u} A) where
  smul_assoc r x y := ULift.ext (smul_assoc r x.down y.down)

local instance : SMulCommClass ℝ (ULift.{u} A) (ULift.{u} A) where
  smul_comm r x y := ULift.ext (smul_comm r x.down y.down)

private def liftTarget {E : Type} [AddCommMonoid E] [Module ℝ E] (f : E →ₗ[ℝ] A) :
    E →ₗ[ℝ] ULift.{u} A :=
  (ULift.moduleEquiv (R := ℝ)).symm.toLinearMap.comp f


/-- The threshold kernel for the real and quaternionic jets, in every associative target universe. -/
theorem higherJetHermitian_universal_kernel_all_universes (b : HigherJetBase)
    (M : HigherJetHermitian b b.threshold) :
    M ∈ higherJetHermitianKernel b ↔
      ∀ (T : Type u) [NonUnitalRing T] [Module ℝ T] [IsScalarTower ℝ T T] [SMulCommClass ℝ T T]
        (f : HigherJetHermitian b b.threshold →ₗ[ℝ] T),
          IsCoefficientJordanMap (conjugate b b.threshold) bilinear (conjugate_product b b.threshold) f →
            f M = 0 := by
  constructor
  · intro hM T _ _ _ _ f hf
    exact coefficientJordanMap_kills_associatorIdeal
      (conjugate b b.threshold) bilinear (conjugate_product b b.threshold) (unit b b.threshold)
      (conjugate_unit b b.threshold) (conjugate_involutive b b.threshold)
      (fun x => product_unit_left x) (fun x => product_unit_right x)
      (leadingIdeal b) (span_associators_eq_leadingIdeal b) (leadingIdeal_conj b)
      (leadingIdeal_fixed_eq_zero b) f hf M hM
  · intro hall
    apply (higherJetHermitian_universal_kernel b M).mpr
    intro T _ _ _ _ f hf
    let F : HigherJetHermitian b b.threshold →ₗ[ℝ] ULift.{u} T := liftTarget f
    have hflift : IsCoefficientJordanMap (conjugate b b.threshold) bilinear
        (conjugate_product b b.threshold) F := by
      intro X Y
      exact ULift.ext (hf X Y)
    exact congrArg ULift.down (hall (ULift.{u} T) F hflift)

/-- The threshold kernel for the complex jet, in every associative target universe. -/
theorem secondOrder_universal_kernel_all_universes (x : E2) :
    x.val ∈ Kso ↔ ∀ (T : Type u) [NonUnitalRing T] [Module ℝ T] [IsScalarTower ℝ T T]
      [SMulCommClass ℝ T T] (f : E2 →ₗ[ℝ] T), IsE2JordanHom f → f x = 0 := by
  constructor
  · intro hx T _ _ _ _ f hf
    exact E2_jordanHom_kills_K f hf x hx
  · intro hall
    apply (secondOrder_universal_kernel x).mpr
    intro T _ _ _ _ f hf
    have hflift : IsE2JordanHom (liftTarget.{u} f) := by
      intro X Y
      exact ULift.ext (hf X Y)
    exact congrArg ULift.down (hall (ULift.{u} T) (liftTarget f) hflift)

end AlbertSequential.AppF
