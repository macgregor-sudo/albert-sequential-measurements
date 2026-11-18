/- SPDX-License-Identifier: Apache-2.0 -/
module

public import SequentialEffectLifts
public import LinearRelationDescent

/-!
The ordered-double-sum step of the printed reconstruction is expressed by
bilinear span induction. A lift for each pair of generators gives a lift for
the square of every finite linear relation. Native generator cross-lifts are
explicit hypotheses, to be supplied by the Peirce/reflection construction.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section Squares
variable {ι κ A J : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  [AddCommGroup J] [Module ℝ J]

def associativeJordanProduct (x y : A) : A := (1 / 2 : ℝ) • (x * y + y * x)

omit [StarRing A] [StarModule ℝ A] in
theorem associativeJordanProduct_add_left (x y z : A) :
    associativeJordanProduct (x + y) z = associativeJordanProduct x z + associativeJordanProduct y z := by
  unfold associativeJordanProduct
  simp only [add_mul, mul_add, smul_add]
  abel

omit [StarRing A] [StarModule ℝ A] in
theorem associativeJordanProduct_add_right (x y z : A) :
    associativeJordanProduct x (y + z) = associativeJordanProduct x y + associativeJordanProduct x z := by
  unfold associativeJordanProduct
  simp only [add_mul, mul_add, smul_add]
  abel

omit [StarRing A] [StarModule ℝ A] in
theorem associativeJordanProduct_smul_left (r : ℝ) (x y : A) :
    associativeJordanProduct (r • x) y = r • associativeJordanProduct x y := by
  unfold associativeJordanProduct
  simp only [smul_mul_assoc, mul_smul_comm, smul_add]
  module

omit [StarRing A] [StarModule ℝ A] in
theorem associativeJordanProduct_smul_right (r : ℝ) (x y : A) :
    associativeJordanProduct x (r • y) = r • associativeJordanProduct x y := by
  unfold associativeJordanProduct
  simp only [smul_mul_assoc, mul_smul_comm, smul_add]
  module

omit [StarRing A] [StarModule ℝ A] in
theorem associativeJordanProduct_self (x : A) : associativeJordanProduct x x = x * x := by
  unfold associativeJordanProduct
  module

theorem unitAndAtomRelation_lift (P : ι → A) (θ : Word ι → J)
    (e : J) (q : κ → J) (Q : κ → A)
    (he : HasSequentialEffectLift P θ 1 e)
    (hq : ∀ i, HasSequentialEffectLift P θ (Q i) (q i))
    {x : J} {Z : A} (h : (x, Z) ∈ unitAndAtomRelation e q 1 Q) :
    HasSequentialEffectLift P θ Z x := by
  have hall : ∀ z ∈ unitAndAtomRelation e q 1 Q, HasSequentialEffectLift P θ z.2 z.1 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨i, rfl⟩
        cases i with
        | none => exact he
        | some i => exact hq i
    | zero => exact hasSequentialEffectLift_zero P θ
    | add z w hz hw ihz ihw => exact hasSequentialEffectLift_add P θ ihz ihw
    | smul r z hz ih => exact hasSequentialEffectLift_smul P θ r ih
  exact hall (x, Z) h

theorem unitAndAtomRelation_selfAdjoint (e : J) (q : κ → J) (Q : κ → A)
    (hstar : ∀ i, star (Q i) = Q i)
    {x : J} {Z : A} (h : (x, Z) ∈ unitAndAtomRelation e q 1 Q) : star Z = Z := by
  have hall : ∀ z ∈ unitAndAtomRelation e q 1 Q, star z.2 = z.2 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨i, rfl⟩
        cases i with
        | none => exact star_one _
        | some i => exact hstar i
    | zero => exact star_zero _
    | add z w hz hw ihz ihw => simp only [Prod.snd_add, star_add, ihz, ihw]
    | smul r z hz ih => simp only [Prod.smul_snd, star_smul, star_trivial, ih]
  exact hall (x, Z) h

/-- The finite cross-term proof extends over BOTH finite spans. This is the
printed ordered double sum, without a fixed finite generator count. -/
theorem unitAndAtomRelation_product_lift (P : ι → A) (θ : Word ι → J)
    (e : J) (q : κ → J) (Q : κ → A) (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hcross : ∀ i j : Option κ, HasSequentialEffectLift P θ
      (associativeJordanProduct (unitAndAtomLabels 1 Q i) (unitAndAtomLabels 1 Q j))
      (jmul (unitAndAtomLabels e q i) (unitAndAtomLabels e q j)))
    {x y : J} {Z Y : A}
    (hZ : (x, Z) ∈ unitAndAtomRelation e q 1 Q)
    (hY : (y, Y) ∈ unitAndAtomRelation e q 1 Q) :
    HasSequentialEffectLift P θ (associativeJordanProduct Z Y) (jmul x y) := by
  have hall : ∀ z ∈ unitAndAtomRelation e q 1 Q, ∀ w ∈ unitAndAtomRelation e q 1 Q,
      HasSequentialEffectLift P θ (associativeJordanProduct z.2 w.2) (jmul z.1 w.1) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨i, rfl⟩
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
            rcases hw with ⟨j, rfl⟩
            exact hcross i j
        | zero =>
            simpa only [Prod.snd_zero, Prod.fst_zero, associativeJordanProduct, mul_zero,
              zero_mul, add_zero, smul_zero, map_zero] using hasSequentialEffectLift_zero P θ
        | add w v hw hv ihw ihv =>
            simpa only [Prod.snd_add, Prod.fst_add, associativeJordanProduct_add_right, map_add] using
              hasSequentialEffectLift_add P θ ihw ihv
        | smul r w hw ih =>
            simpa only [Prod.smul_snd, Prod.smul_fst, associativeJordanProduct_smul_right, map_smul] using
              hasSequentialEffectLift_smul P θ r ih
    | zero =>
        intro w hw
        simpa only [Prod.snd_zero, Prod.fst_zero, associativeJordanProduct, mul_zero,
          zero_mul, add_zero, smul_zero, map_zero, LinearMap.zero_apply] using
          hasSequentialEffectLift_zero P θ
    | add z v hz hv ihz ihv =>
        intro w hw
        simpa only [Prod.snd_add, Prod.fst_add, associativeJordanProduct_add_left,
          map_add, LinearMap.add_apply] using hasSequentialEffectLift_add P θ (ihz w hw) (ihv w hw)
    | smul r z hz ih =>
        intro w hw
        simpa only [Prod.smul_snd, Prod.smul_fst, associativeJordanProduct_smul_left,
          map_smul, LinearMap.smul_apply] using hasSequentialEffectLift_smul P θ r (ih w hw)
  exact hall (x, Z) hZ (y, Y) hY

theorem unitAndAtomRelation_square_lift (P : ι → A) (θ : Word ι → J)
    (e : J) (q : κ → J) (Q : κ → A) (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hcross : ∀ i j : Option κ, HasSequentialEffectLift P θ
      (associativeJordanProduct (unitAndAtomLabels 1 Q i) (unitAndAtomLabels 1 Q j))
      (jmul (unitAndAtomLabels e q i) (unitAndAtomLabels e q j)))
    {Z : A} (hZ : (0, Z) ∈ unitAndAtomRelation e q 1 Q) :
    HasSequentialEffectLift P θ (Z * Z) 0 := by
  have h := unitAndAtomRelation_product_lift P θ e q Q jmul hcross hZ hZ
  simpa only [associativeJordanProduct_self, map_zero, LinearMap.zero_apply] using h

end Squares
end AlbertSequential
