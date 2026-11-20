/- SPDX-License-Identifier: Apache-2.0 -/
module
public import TwoAlbertTableMixture

@[expose] public section
noncomputable section
namespace AlbertSequential.TwoAlbert
open scoped TwoAlbert

theorem pair_compression_not_scalar {I : Type*} (p q : I → Albert) (i : I)
    (hp : IsAtom (p i)) (hq : IsAtom (q i)) :
    ∀ c : ℝ, product.quadraticRepresentation (pair p q i) (left (p i)) ≠ c • pair p q i := by
  have fix : product.product (pair p q i) (left (p i)) = left (p i) := by
    rw [pair_eq_left_add_right,map_add,LinearMap.add_apply,product.commutative (right _) (left _),
      left_right_orthogonal,left_idempotent _ hp.1,add_zero]
  have idem : product.product (pair p q i) (pair p q i) = pair p q i := by
    apply coordinates.injective
    funext j
    rw [product_coordinates,coordinates_pair]
    fin_cases j <;> first | exact hp.1 | exact hq.1
  intro c h
  rw [product.quadraticRepresentation_apply,idem,fix,fix,two_smul,add_sub_cancel_right] at h
  have hc := congrArg coordinates h
  rw [left_coordinates,map_smul,coordinates_pair] at hc
  have r := congrArg albertTrace (congrFun hc 1)
  change albertTrace 0 = albertTrace (c • q i) at r
  rw [NativeAnalysis.albertTrace_zero,albertTrace_smul,hq.2,mul_one] at r
  subst c
  have l := congrArg albertTrace (congrFun hc 0)
  change albertTrace (p i) = albertTrace ((0:ℝ) • p i) at l
  rw [zero_smul,NativeAnalysis.albertTrace_zero,hp.2] at l
  norm_num at l

end AlbertSequential.TwoAlbert
