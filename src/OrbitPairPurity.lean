/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SequentialEffectLifts
public import PurityResiduals

/-!
Transported pair-purity square lifts for an arbitrary spanning atom family.
The operator identity is the short-mirror purity identity, applied
to the literal family of orbit projections. No fundamental formula is assumed
in this atom-pair step: two rank-one corners and symmetric weights suffice.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section PairPurity
variable {ι κ A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

theorem orbitPairPurity_square_lift
    (P : ι → A) (θ : Word ι → J) (q : κ → J) (Q : κ → A)
    (hQ : ∀ i, Q i * Q i = Q i) (hQstar : ∀ i, star (Q i) = Q i)
    (weight : κ → J →ₗ[ℝ] ℝ)
    (hsym : ∀ i j, weight i (q j) = weight j (q i))
    (hq : ∀ i, HasSequentialEffectLift P θ (Q i) (q i))
    (hcorner : ∀ i {Z x}, HasSequentialEffectLift P θ Z x →
      HasSequentialEffectLift P θ (Q i * Z * Q i) (weight i x • q i))
    (i j : κ) :
    HasSequentialEffectLift P θ
      (outcomePurityElement Q (i, true) [(j, true)] (weight i (q j)) *
        outcomePurityElement Q (i, true) [(j, true)] (weight i (q j))) 0 := by
  let c := weight i (q j)
  have hshort : HasSequentialEffectLift P θ (wordOperator Q [(i, true)]) (q i) := by
    simpa only [wordOperator_singleton Q hQ hQstar, algebraicOutcome, ↓reduceIte] using hq i
  have hmiddle : HasSequentialEffectLift P θ (wordOperator Q [(i, true), (j, true)])
      (weight i (q j) • q i) := by
    simpa only [wordOperator_cons Q hQstar, wordOperator_singleton Q hQ hQstar,
      algebraicOutcome, ↓reduceIte, wordOperator_nil, mul_one, hQ] using hcorner i (hq j)
  have hlong : HasSequentialEffectLift P θ
      (wordOperator Q [(i, true), (j, true), (i, true)])
      (weight i (weight j (q i) • q j) • q i) := by
    simpa only [wordOperator_cons Q hQstar, wordOperator_singleton Q hQ hQstar,
      algebraicOutcome, ↓reduceIte, wordOperator_nil, mul_one, hQ] using hcorner i (hcorner j (hq i))
  have h := hasSequentialEffectLift_add P θ
    (hasSequentialEffectLift_sub P θ hlong (hasSequentialEffectLift_smul P θ (2 * c) hmiddle))
    (hasSequentialEffectLift_smul P θ (c ^ 2) hshort)
  have heffect : weight i (weight j (q i) • q j) • q i -
      (2 * c) • (weight i (q j) • q i) + (c ^ 2) • q i = 0 := by
    dsimp only [c]
    rw [map_smul, hsym j i]
    simp only [smul_eq_mul]
    module
  rw [heffect] at h
  have hsquare := purityResidual_operator Q hQ hQstar (i, true) [(j, true)] [] c
  simp only [wordAmplitude_nil, mul_one, outcomePurityElement_star Q hQstar,
    purityMirror, List.dropLast_singleton, List.reverse_nil, List.nil_append,
    List.append_nil, List.singleton_append, List.cons_append] at hsquare
  rw [← hsquare] at h
  exact h

end PairPurity
end AlbertSequential
