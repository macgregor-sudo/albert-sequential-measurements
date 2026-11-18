/- SPDX-License-Identifier: Apache-2.0 -/
module
public import EuclideanJordanForm

/-! A self-adjoint idempotent's multiplication is positive semidefinite.
The ordinary Jordan cubic produces actual Peirce projections; no positivity,
spectral, finite-dimensional or trace-normalization premise is inserted. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

theorem idempotent_leftMultiplication_cubic (q z : E) (hq : P.product q q=q) :
    (2 : ℝ) • P.product q (P.product q (P.product q z))-
      (3 : ℝ) • P.product q (P.product q z)+P.product q z=0 := by
  have hq' : (Element.mk q : P.Element)*(Element.mk q)=Element.mk q := by
    exact congrArg Element.mk hq
  have h := congrArg Element.value (RealJordan.idempotent_multiplication_cubic
    (Element.mk q : P.Element) (Element.mk z) hq')
  exact h

/-- The literal half-eigenspace projection polynomial. -/
def peirceHalfProjection (q : E) : E →ₗ[ℝ] E :=
  (4 : ℝ) • (P.product q-(P.product q).comp (P.product q))

@[simp] theorem peirceHalfProjection_apply (q z : E) :
    P.peirceHalfProjection q z=(4 : ℝ) •
      (P.product q z-P.product q (P.product q z)) := rfl

theorem peirceHalfProjection_half_eigenvalue (q z : E) (hq : P.product q q=q) :
    P.product q (P.peirceHalfProjection q z)=
      (1/2 : ℝ) • P.peirceHalfProjection q z := by
  have h := congrArg (fun v : E => (-2 : ℝ) • v)
    (P.idempotent_leftMultiplication_cubic q z hq)
  simp only [smul_add,smul_sub,smul_smul,smul_zero] at h
  simp only [P.peirceHalfProjection_apply,map_smul,map_sub]
  linear_combination (norm := module) h

theorem peirceHalfProjection_idempotent (q z : E) (hq : P.product q q=q) :
    P.peirceHalfProjection q (P.peirceHalfProjection q z)=P.peirceHalfProjection q z := by
  rw [P.peirceHalfProjection_apply,P.peirceHalfProjection_half_eigenvalue q z hq,
    map_smul,P.peirceHalfProjection_half_eigenvalue q z hq]
  module

theorem quadraticRepresentation_idempotent_apply (q z : E) (hq : P.product q q=q) :
    P.quadraticRepresentation q (P.quadraticRepresentation q z)=P.quadraticRepresentation q z := by
  have hf := (P.mem_peirceOne q _).mp (P.quadraticRepresentation_mem_peirceOne q z hq)
  change (2 : ℝ) • P.product q (P.product q (P.quadraticRepresentation q z))-
    P.product (P.product q q) (P.quadraticRepresentation q z)=P.quadraticRepresentation q z
  rw [hq,hf,hf]
  module

theorem leftMultiplication_projection_decomposition (q z : E) (hq : P.product q q=q) :
    P.product q z=P.quadraticRepresentation q z+
      (1/2 : ℝ) • P.peirceHalfProjection q z := by
  simp only [P.quadraticRepresentation_apply,hq,P.peirceHalfProjection_apply]
  module

end AlbertSequential.UnitalJordanProduct

namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : UnitalJordanProduct E)

theorem peirceHalfProjection_inner
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q x y : E) : inner ℝ (P.peirceHalfProjection q x) y=
      inner ℝ x (P.peirceHalfProjection q y) := by
  simp only [P.peirceHalfProjection_apply,real_inner_smul_left,inner_smul_right,
    inner_sub_left,inner_sub_right]
  rw [P.product_inner hinner q x y,P.product_inner hinner q (P.product q x) y,
    P.product_inner hinner q x (P.product q y)]

theorem idempotent_leftMultiplication_inner_decomposition
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q z : E) (hq : P.product q q=q) :
    inner ℝ (P.product q z) z=
      inner ℝ (P.quadraticRepresentation q z) (P.quadraticRepresentation q z)+
        (1/2 : ℝ)*inner ℝ (P.peirceHalfProjection q z) (P.peirceHalfProjection q z) := by
  have hQ := P.quadraticRepresentation_inner hinner q (P.quadraticRepresentation q z) z
  rw [P.quadraticRepresentation_idempotent_apply q z hq] at hQ
  have hH := P.peirceHalfProjection_inner hinner q (P.peirceHalfProjection q z) z
  rw [P.peirceHalfProjection_idempotent q z hq] at hH
  rw [P.leftMultiplication_projection_decomposition q z hq,inner_add_left,
    real_inner_smul_left,hQ,hH]

theorem idempotent_leftMultiplication_nonneg
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q z : E) (hq : P.product q q=q) : 0 ≤ inner ℝ (P.product q z) z := by
  rw [P.idempotent_leftMultiplication_inner_decomposition hinner q z hq]
  exact add_nonneg real_inner_self_nonneg (mul_nonneg (by norm_num) real_inner_self_nonneg)

theorem idempotent_inner_square_nonneg
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (q z : E) (hq : P.product q q=q) : 0 ≤ inner ℝ q (P.product z z) := by
  rw [← hinner q z z]
  exact P.idempotent_leftMultiplication_nonneg hinner q z hq

end AlbertSequential.UnitalJordanProduct
