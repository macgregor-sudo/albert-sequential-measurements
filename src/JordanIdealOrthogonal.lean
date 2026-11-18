/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanIdeals
public import EuclideanJordanForm
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Orthogonal ideal complements and actual local units from the actual
positive associative form. Ambient inclusion is generally nonunital. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem isJordanIdeal_orthogonal
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) : P.IsJordanIdeal Iᗮ := by
  intro x hx y
  apply (I.mem_orthogonal _).mpr
  intro z hz
  rw [← P.product_inner hinner y z x]
  exact (I.mem_orthogonal x).mp hx _ (hI z hz y)

theorem ideal_orthogonal_product_zero
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I)
    (x y : E) (hx : x∈I) (hy : y∈Iᗮ) : P.product x y=0 := by
  have hmI : P.product x y∈I := by rw [P.commutative]; exact hI x hx y
  have hmPerp : P.product x y∈Iᗮ := P.isJordanIdeal_orthogonal hinner I hI y hy x
  exact inner_self_eq_zero.mp ((I.mem_orthogonal _).mp hmPerp _ hmI)

def idealUnit (I : Submodule ℝ E) : E := I.starProjection P.unit

theorem idealUnit_mem (I : Submodule ℝ E) : P.idealUnit I∈I := I.starProjection_apply_mem _

theorem idealUnit_left
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (x : E) (hx : x∈I) :
    P.product (P.idealUnit I) x=x := by
  have hzero := P.ideal_orthogonal_product_zero hinner I hI x
    (P.unit-P.idealUnit I) hx (I.sub_starProjection_mem_orthogonal P.unit)
  rw [P.commutative x (P.unit-P.idealUnit I),map_sub,LinearMap.sub_apply,P.unit_left] at hzero
  exact (sub_eq_zero.mp hzero).symm

theorem idealUnit_idempotent
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) :
    P.product (P.idealUnit I) (P.idealUnit I)=P.idealUnit I :=
  P.idealUnit_left hinner I hI _ (P.idealUnit_mem I)

theorem idealUnit_product_eq_projection
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (x : E) :
    P.product (P.idealUnit I) x=I.starProjection x := by
  have hzero := P.ideal_orthogonal_product_zero hinner I hI (P.idealUnit I)
    (x-I.starProjection x) (P.idealUnit_mem I) (I.sub_starProjection_mem_orthogonal x)
  rw [map_sub,P.idealUnit_left hinner I hI _ (I.starProjection_apply_mem x)] at hzero
  exact sub_eq_zero.mp hzero

def orthogonalIdealProduct
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) : UnitalJordanProduct I :=
  P.idealProduct I hI ⟨P.idealUnit I,P.idealUnit_mem I⟩
    (fun x => P.idealUnit_left hinner I hI x.val x.property)

theorem orthogonalIdealProduct_inner
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (x y z : I) :
    inner ℝ ((P.orthogonalIdealProduct hinner I hI).product x y) z=
      inner ℝ x ((P.orthogonalIdealProduct hinner I hI).product y z) :=
  hinner x.val y.val z.val

end AlbertSequential.UnitalJordanProduct
