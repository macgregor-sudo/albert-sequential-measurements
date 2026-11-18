/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OrbitJordanDescent

/-!
The Peirce cross-term lift used to kill every finite orbit linear relation.
The two lift-preserving operations are exact corners and reflections, already
constructed for transported orbit labels in SequentialEffectLifts. Their
native identification and the native Peirce identity remain explicit inputs.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section PeirceLifts
variable {ι κ A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

theorem hasSequentialEffectLift_peirce_product
    (P : ι → A) (θ : Word ι → J) (Q : A) (q : J)
    (K R : Module.End ℝ J) (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hpeirce : ∀ x, jmul q x = K x + (1 / 4 : ℝ) • (x - R x))
    (hcorner : ∀ {Z x}, HasSequentialEffectLift P θ Z x →
      HasSequentialEffectLift P θ (Q * Z * Q) (K x))
    (hreflect : ∀ {Z x}, HasSequentialEffectLift P θ Z x →
      HasSequentialEffectLift P θ
        (((2 : ℝ) • Q - 1) * Z * ((2 : ℝ) • Q - 1)) (R x))
    {Y : A} {y : J} (hY : HasSequentialEffectLift P θ Y y) :
    HasSequentialEffectLift P θ (associativeJordanProduct Q Y) (jmul q y) := by
  have h := hasSequentialEffectLift_add P θ (hcorner hY)
    (hasSequentialEffectLift_smul P θ (1 / 4 : ℝ)
      (hasSequentialEffectLift_sub P θ hY (hreflect hY)))
  rw [← associativeJordanProduct_peirce, ← hpeirce] at h
  exact h

theorem orbitGenerator_cross_lifts
    (P : ι → A) (θ : Word ι → J) (e : J) (q : κ → J) (Q : κ → A)
    (K R : κ → Module.End ℝ J) (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hunit : ∀ x, jmul e x = x)
    (he : HasSequentialEffectLift P θ 1 e)
    (hq : ∀ i, HasSequentialEffectLift P θ (Q i) (q i))
    (hpeirce : ∀ i x, jmul (q i) x = K i x + (1 / 4 : ℝ) • (x - R i x))
    (hcorner : ∀ i {Z x}, HasSequentialEffectLift P θ Z x →
      HasSequentialEffectLift P θ (Q i * Z * Q i) (K i x))
    (hreflect : ∀ i {Z x}, HasSequentialEffectLift P θ Z x →
      HasSequentialEffectLift P θ
        (((2 : ℝ) • Q i - 1) * Z * ((2 : ℝ) • Q i - 1)) (R i x)) :
    ∀ i j : Option κ, HasSequentialEffectLift P θ
      (associativeJordanProduct (unitAndAtomLabels 1 Q i) (unitAndAtomLabels 1 Q j))
      (jmul (unitAndAtomLabels e q i) (unitAndAtomLabels e q j)) := by
  intro i j
  have hj : HasSequentialEffectLift P θ (unitAndAtomLabels 1 Q j) (unitAndAtomLabels e q j) := by
    cases j with
    | none => exact he
    | some j => exact hq j
  cases i with
  | none => simpa only [unitAndAtomLabels, hunit, associativeJordanProduct_unit_left] using hj
  | some i =>
      exact hasSequentialEffectLift_peirce_product P θ (Q i) (q i)
        (K i) (R i) jmul (hpeirce i) (hcorner i) (hreflect i) hj

end PeirceLifts
end AlbertSequential
