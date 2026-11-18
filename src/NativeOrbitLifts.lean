/- SPDX-License-Identifier: Apache-2.0 -/
module
public import NativeReflectionOrbit
public import OrbitExpectation
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis

def nativeJordanProductLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert where
  toFun x :=
    { toFun := jordanMul x
      map_add' := jordanMul_add_right x
      map_smul' := fun r y => jordanMul_smul_right r x y }
  map_add' x y := by ext z; exact jordanMul_add_left x y z
  map_smul' r x := by ext z; exact jordanMul_smul_left r x z

def nativePairingFunctional (ρ : Albert) : Albert →ₗ[ℝ] ℝ where
  toFun := tracePairing ρ
  map_add' := tracePairing_add_right ρ
  map_smul' r x := tracePairing_smul_right r ρ x

section Reconstruction
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

def cyclicOrbitProjection (M : AlgebraicProjectiveData ι A) (α : ReflectionOrbitLabel ι) :
    wordSubalgebra M.projection :=
  ⟨orbitProjection M.projection α.1 α.2,
    orbitProjection_mem_wordVectorSpan M.projection M.selfAdjoint α.1 α.2⟩

theorem nativeAtom_quadratic_unit (p : Albert) (hp : IsAtom p) : quadraticMap p albertUnit = p := by
  unfold quadraticMap
  simp only [jordanMul_albertUnit_right, hp.1, two_smul]
  module

theorem nativeOrbitProjection_has_lift (M : AlgebraicProjectiveData ι A)
    (p : ι → Albert) (hp : ∀ i, IsAtom (p i)) (α : ReflectionOrbitLabel ι) :
    HasSequentialEffectLift M.projection (nativeWordEffect p)
      (cyclicOrbitProjection M α : A) (nativeOrbitPoint p hp α) := by
  have hi := hasSequentialEffectLift_word M.projection (nativeWordEffect p) [(α.2, true)]
  have h := hasSequentialEffectLift_reflection_word M.projection (nativeWordEffect p)
    (nativeOutcomeUpdate p) M.selfAdjoint (fun _ _ => rfl) α.1 hi
  simpa only [wordOperator_singleton M.projection M.idempotent M.selfAdjoint,
    algebraicOutcome, nativeWordEffect, nativeOutcome, ↓reduceIte,
    nativeAtom_quadratic_unit _ (hp α.2), reflectionWordUpdate_native p hp,
    nativeOrbitPoint, orbitProjection, cyclicOrbitProjection] using h


end Reconstruction
end AlbertSequential
