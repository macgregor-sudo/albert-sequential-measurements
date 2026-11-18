/- SPDX-License-Identifier: Apache-2.0 -/
module

public import JordanSquareLifts

/-!
The final Peirce step of the printed reconstruction, proved for an arbitrary
spanning orbit family. Pair-purity and reflected-label relations are explicit
inputs and must be supplied by the square-lift/null argument. A merely linear
map or an assumed reconstruction bundle is not used as the endpoint.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section JordanDescent
variable {κ E J : Type*} [Ring E] [Module ℝ E]
  [IsScalarTower ℝ E E] [SMulCommClass ℝ E E]
  [AddCommGroup J] [Module ℝ J]

theorem associativeJordanProduct_unit_left (x : E) : associativeJordanProduct 1 x = x := by
  unfold associativeJordanProduct
  simp only [one_mul, mul_one]
  module

theorem associativeJordanProduct_peirce (P Y : E) :
    associativeJordanProduct P Y = P * Y * P + (1 / 4 : ℝ) •
      (Y - ((2 : ℝ) • P - 1) * Y * ((2 : ℝ) • P - 1)) := by
  unfold associativeJordanProduct
  simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, one_mul, mul_one, mul_assoc]
  module

theorem jordan_preserving_of_orbit_relations
    (e : J) (q : κ → J) (jmul : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hunit : ∀ x, jmul e x = x)
    (hspan : Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) = ⊤)
    (R : κ → Module.End ℝ J) (weight : κ → J →ₗ[ℝ] ℝ)
    (hweightunit : ∀ i, weight i e = 1)
    (hpeirce : ∀ i x, jmul (q i) x = weight i x • q i + (1 / 4 : ℝ) • (x - R i x))
    (reflectLabel : κ → κ → κ)
    (hRunit : ∀ i, R i e = e)
    (hRlabel : ∀ i j, R i (q j) = q (reflectLabel i j))
    (η : J →ₗ[ℝ] E) (hηunit : η e = 1)
    (hprojection : ∀ i, η (q i) * η (q i) = η (q i))
    (hpair : ∀ i j, η (q i) * η (q j) * η (q i) = weight i (q j) • η (q i))
    (hreflection : ∀ i j, η (q (reflectLabel i j)) =
      ((2 : ℝ) • η (q i) - 1) * η (q j) * ((2 : ℝ) • η (q i) - 1)) :
    ∀ x y, η (jmul x y) = associativeJordanProduct (η x) (η y) := by
  have hcorner : ∀ i x, η (q i) * η x * η (q i) = weight i x • η (q i) := by
    intro i x
    have hx : x ∈ Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨j, rfl⟩
        cases j with
        | none => simp only [unitAndAtomLabels, hηunit, mul_one, hprojection, hweightunit, one_smul]
        | some j => exact hpair i j
    | zero => simp only [map_zero, mul_zero, zero_mul, zero_smul]
    | add x y hx hy ihx ihy =>
        simp only [map_add, mul_add, add_mul, ihx, ihy, add_smul]
    | smul r x hx ih =>
        simp only [map_smul, mul_smul_comm, smul_mul_assoc, ih, smul_eq_mul, mul_smul]
  have hreflect : ∀ i x, η (R i x) =
      ((2 : ℝ) • η (q i) - 1) * η x * ((2 : ℝ) • η (q i) - 1) := by
    intro i x
    have hx : x ∈ Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨j, rfl⟩
        cases j with
        | none =>
            simp only [unitAndAtomLabels, hRunit, hηunit, mul_one, two_smul]
            noncomm_ring [hprojection i]
        | some j => simp only [unitAndAtomLabels, hRlabel]; exact hreflection i j
    | zero => simp only [map_zero, mul_zero, zero_mul]
    | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, mul_add, add_mul]
    | smul r x hx ih => simp only [map_smul, ih, mul_smul_comm, smul_mul_assoc]
  have hproduct : ∀ i x, η (jmul (q i) x) = associativeJordanProduct (η (q i)) (η x) := by
    intro i x
    rw [hpeirce, map_add, map_smul, map_smul, map_sub, hreflect,
      associativeJordanProduct_peirce, hcorner]
  intro x y
  have hx : x ∈ Submodule.span ℝ (Set.range (unitAndAtomLabels e q)) := by rw [hspan]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      cases i with
      | none => rw [unitAndAtomLabels, hunit, hηunit, associativeJordanProduct_unit_left]
      | some i => exact hproduct i y
  | zero => simp only [map_zero, LinearMap.zero_apply, associativeJordanProduct, zero_mul,
      mul_zero, add_zero, smul_zero]
  | add x z hx hz ihx ihz =>
      simp only [map_add, LinearMap.add_apply, ihx, ihz, associativeJordanProduct_add_left]
  | smul r x hx ih =>
      simp only [map_smul, LinearMap.smul_apply, ih, associativeJordanProduct_smul_left]

end JordanDescent
end AlbertSequential
