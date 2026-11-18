/- SPDX-License-Identifier: Apache-2.0
Conventions follow Physlib; see THIRD_PARTY_NOTICES. -/
module

public import JordanProductQuadratic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! Elementary consequences of an actual associative positive inner product.
This proves the positive-form => formal-reality direction only. It does not
assume or prove the reverse direction or canonical Jordan trace normalization. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : UnitalJordanProduct E)

theorem product_inner
    (hassoc : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a x y : E) : inner ℝ (P.product a x) y=inner ℝ x (P.product a y) := by
  rw [P.commutative a x,hassoc]

theorem square_inner_unit
    (hassoc : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x : E) : inner ℝ (P.product x x) P.unit=inner ℝ x x := by
  rw [hassoc,P.commutative x P.unit,P.unit_left]

/-- Formal reality follows from the actual inner form and unit, without a
finite-dimensional or spectral assumption. -/
theorem formallyReal_of_associative_inner
    (hassoc : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    P.FormallyReal := by
  intro n x hsum i
  have h := congrArg (fun z => inner ℝ z P.unit) hsum
  simp only [sum_inner,P.square_inner_unit hassoc,inner_zero_left] at h
  have hi : inner ℝ (x i) (x i)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => real_inner_self_nonneg)).mp h i
      (Finset.mem_univ i)
  exact inner_self_eq_zero.mp hi

theorem quadraticRepresentation_inner
    (hassoc : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a x y : E) : inner ℝ (P.quadraticRepresentation a x) y=
      inner ℝ x (P.quadraticRepresentation a y) := by
  simp only [P.quadraticRepresentation_apply,inner_sub_left,inner_sub_right,
    real_inner_smul_left,inner_smul_right]
  rw [P.product_inner hassoc a (P.product a x) y,
    P.product_inner hassoc a x (P.product a y),
    P.product_inner hassoc (P.product a a) x y]

end AlbertSequential.UnitalJordanProduct
