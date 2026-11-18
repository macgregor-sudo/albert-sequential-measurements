/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OrbitPairPurity
public import OrbitPeirceLifts
public import OrbitExpectation

/-!
Complete abstract assembly of all-history cyclic reconstruction. Every
native atom/reflection/Peirce input is explicit. The target pair relations,
linear well-definedness, Jordan preservation and expectation are conclusions,
not fields of an assumed reconstruction contract.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section Assembly
variable {ι κ A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

def rankOneLinearUpdate (weight : J →ₗ[ℝ] ℝ) (q : J) : Module.End ℝ J where
  toFun x := weight x • q
  map_add' x y := by rw [map_add, add_smul]
  map_smul' r x := by simp only [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply]

theorem exists_cyclicOrbitJordanMap
    (M : AlgebraicProjectiveData ι A)
    (θ : Word ι → J) (U : Outcome ι → Module.End ℝ J)
    (hθ : ∀ a w, θ (a :: w) = U a (θ w)) (ω : J →ₗ[ℝ] ℝ)
    (hmatch : ∀ w, M.probability w = ω (θ w))
    (e : J) (q : κ → J) (Q : κ → wordSubalgebra M.projection)
    (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J) (hunit : ∀ x, jmul e x = x)
    (hspan : Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) = ⊤)
    (weight : κ → J →ₗ[ℝ] ℝ) (R : κ → Module.End ℝ J)
    (hweightunit : ∀ i, weight i e = 1)
    (hweightsym : ∀ i j, weight i (q j) = weight j (q i))
    (hpeirce : ∀ i x, jmul (q i) x = weight i x • q i + (1 / 4 : ℝ) • (x - R i x))
    (reflectLabel : κ → κ → κ)
    (hRunit : ∀ i, R i e = e) (hRlabel : ∀ i j, R i (q j) = q (reflectLabel i j))
    (he : HasSequentialEffectLift M.projection θ 1 e)
    (hq : ∀ i, HasSequentialEffectLift M.projection θ (Q i : A) (q i))
    (hQ : ∀ i, (Q i : A) * Q i = Q i) (hQstar : ∀ i, star (Q i : A) = Q i)
    (hQlabel : ∀ i j, Q (reflectLabel i j) =
      ((2 : ℝ) • Q i - 1) * Q j * ((2 : ℝ) • Q i - 1))
    (hcorner : ∀ i {Z x}, HasSequentialEffectLift M.projection θ Z x →
      HasSequentialEffectLift M.projection θ ((Q i : A) * Z * Q i) (weight i x • q i))
    (hreflect : ∀ i {Z x}, HasSequentialEffectLift M.projection θ Z x →
      HasSequentialEffectLift M.projection θ
        (((2 : ℝ) • (Q i : A) - 1) * Z * ((2 : ℝ) • (Q i : A) - 1)) (R i x)) :
    ∃ η : J →ₗ[ℝ] Module.End ℝ (CyclicWordSpace M),
      (∀ x y, η (jmul x y) = associativeJordanProduct (η x) (η y)) ∧ η e = 1 ∧
      (∀ i, η (q i) = cyclicRepresentation M (Q i)) ∧
      ∀ x, cyclicExpectation M (η x (cyclicVector M)) = ω x := by
  let K := fun i => rankOneLinearUpdate (weight i) (q i)
  have hcross := orbitGenerator_cross_lifts M.projection θ e q (fun i => (Q i : A))
    K R jmul hunit he hq hpeirce hcorner hreflect
  obtain ⟨η, hηunit, hηq, hgraph⟩ := exists_cyclicOrbitLinearMap M θ U hθ ω hmatch e q Q
    jmul hspan hQstar hcross
  have hprojection : ∀ i, η (q i) * η (q i) = η (q i) := by
    intro i
    rw [hηq, ← map_mul]
    congr 1
    exact Subtype.ext (hQ i)
  have hpair : ∀ i j, η (q i) * η (q j) * η (q i) = weight i (q j) • η (q i) := by
    intro i j
    let c := weight i (q j)
    let T : wordSubalgebra M.projection := Q i * Q j * Q i - c • Q i
    have hsq := orbitPairPurity_square_lift M.projection θ q (fun i => (Q i : A))
      hQ hQstar weight hweightsym hq hcorner i j
    have hTsq : HasSequentialEffectLift M.projection θ ((T : A) * T) 0 := by
      simpa only [T, c, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_smul,
        outcomePurityElement, wordOperator_singleton (fun i => (Q i : A)) hQ hQstar,
        algebraicOutcome, ↓reduceIte] using hsq
    have hTstar : star (T : A) = T := by
      dsimp only [T]
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_smul,
        star_sub, star_mul, star_smul, star_trivial, hQstar, mul_assoc]
    have hT := cyclicRepresentation_eq_zero_of_square_lift M θ U hθ ω hmatch T hTstar hTsq
    rw [hηq, hηq]
    apply sub_eq_zero.mp
    dsimp only [T, c] at hT
    simpa only [map_sub, map_mul, map_smul] using hT
  have hreflection : ∀ i j, η (q (reflectLabel i j)) =
      ((2 : ℝ) • η (q i) - 1) * η (q j) * ((2 : ℝ) • η (q i) - 1) := by
    intro i j
    rw [hηq, hηq, hηq, hQlabel, map_mul, map_mul, map_sub, map_smul, map_one]
  have hjordan := jordan_preserving_of_orbit_relations e q jmul hunit hspan R weight
    hweightunit hpeirce reflectLabel hRunit hRlabel η hηunit hprojection hpair hreflection
  refine ⟨η, hjordan, hηunit, hηq, ?_⟩
  exact cyclicOrbitLinearMap_expectation M θ ω hmatch e q Q he hq η hgraph

end Assembly
end AlbertSequential
