/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanIdealOrthogonal

/-! Actual central component projections preserve product/unit and quadratic
updates. The ambient inclusion of a proper ideal remains generally nonunital. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem idealProjection_product
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (x y : E) :
    I.starProjection (P.product x y)=P.product (I.starProjection x) (I.starProjection y) := by
  have hm : P.product (I.starProjection x) y∈I := by
    rw [P.commutative]
    exact hI _ (I.starProjection_apply_mem x) y
  have hres : P.product x y-P.product (I.starProjection x) y∈Iᗮ := by
    have h := P.isJordanIdeal_orthogonal hinner I hI (x-I.starProjection x)
      (I.sub_starProjection_mem_orthogonal x) y
    simpa only [map_sub,P.commutative y x,P.commutative y (I.starProjection x)] using h
  have hp : I.starProjection (P.product x y-P.product (I.starProjection x) y)=0 :=
    I.eq_starProjection_of_mem_orthogonal I.zero_mem (by simpa only [sub_zero] using hres)
  rw [map_sub,I.starProjection_eq_self_iff.mpr hm] at hp
  have hcross := P.ideal_orthogonal_product_zero hinner I hI (I.starProjection x)
    (y-I.starProjection y) (I.starProjection_apply_mem x) (I.sub_starProjection_mem_orthogonal y)
  rw [map_sub] at hcross
  exact (sub_eq_zero.mp hp).trans (sub_eq_zero.mp hcross)

theorem idealProjection_product_subtype
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (x y : E) :
    I.orthogonalProjectionOnto (P.product x y)=
      (P.orthogonalIdealProduct hinner I hI).product
        (I.orthogonalProjectionOnto x) (I.orthogonalProjectionOnto y) :=
  Subtype.ext (P.idealProjection_product hinner I hI x y)

theorem idealProjection_unit_subtype
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) :
    I.orthogonalProjectionOnto P.unit=(P.orthogonalIdealProduct hinner I hI).unit := rfl

theorem idealProjection_quadraticRepresentation
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (a x : E) :
    I.orthogonalProjectionOnto (P.quadraticRepresentation a x)=
      (P.orthogonalIdealProduct hinner I hI).quadraticRepresentation
        (I.orthogonalProjectionOnto a) (I.orthogonalProjectionOnto x) := by
  simp only [quadraticRepresentation_apply,map_sub,map_smul,
    P.idealProjection_product_subtype hinner I hI]

theorem idealUnit_quadraticRepresentation
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (x : E) :
    P.quadraticRepresentation (P.idealUnit I) x=I.starProjection x := by
  rw [P.quadraticRepresentation_apply,P.idealUnit_idempotent hinner I hI,
    P.idealUnit_product_eq_projection hinner I hI x,
    P.idealUnit_left hinner I hI _ (I.starProjection_apply_mem x)]
  module

end AlbertSequential.UnitalJordanProduct
