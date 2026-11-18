/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicHilbertRepresentation

/-! Every actual word-algebra multiplier extends to the actual real Hilbert
completion. Density preserves its full algebra and adjoint identities. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
section
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

def cyclicPreContinuousAction (M : AlgebraicProjectiveData ι A) (z : CyclicWordAlgebra M) :
    CyclicPreHilbert M →L[ℝ] CyclicPreHilbert M :=
  (cyclicPreRepresentation M z).mkContinuous
    (Classical.choose (cyclicPreRepresentation_bounded M z))
    (Classical.choose_spec (cyclicPreRepresentation_bounded M z)).2

def cyclicHilbertAction (M : AlgebraicProjectiveData ι A) (z : CyclicWordAlgebra M) :
    CyclicHilbert M →L[ℝ] CyclicHilbert M := (cyclicPreContinuousAction M z).completion

@[simp] theorem cyclicHilbertAction_coe (M : AlgebraicProjectiveData ι A)
    (z : CyclicWordAlgebra M) (q : CyclicPreHilbert M) :
    cyclicHilbertAction M z (q : CyclicHilbert M) =
      (cyclicPreRepresentation M z q : CyclicPreHilbert M) :=
  ContinuousLinearMap.completion_apply_coe _ q

theorem cyclicHilbertOperator_ext (M : AlgebraicProjectiveData ι A)
    {S T : CyclicHilbert M →L[ℝ] CyclicHilbert M}
    (h : ∀ q : CyclicPreHilbert M, S (q : CyclicHilbert M)=T (q : CyclicHilbert M)) : S=T := by
  apply ContinuousLinearMap.ext
  intro x
  exact UniformSpace.Completion.induction_on x (isClosed_eq S.continuous T.continuous) h

theorem cyclicHilbertAction_zero (M : AlgebraicProjectiveData ι A) : cyclicHilbertAction M 0=0 := by
  apply cyclicHilbertOperator_ext M
  intro q
  rw [cyclicHilbertAction_coe]
  change ((cyclicPreRepresentation M) 0 q : CyclicHilbert M)=0
  simp only [map_zero,LinearMap.zero_apply,UniformSpace.Completion.coe_zero]

theorem cyclicHilbertAction_one (M : AlgebraicProjectiveData ι A) : cyclicHilbertAction M 1=1 := by
  apply cyclicHilbertOperator_ext M
  intro q
  rw [cyclicHilbertAction_coe]
  change ((cyclicPreRepresentation M) 1 q : CyclicHilbert M)=(q : CyclicHilbert M)
  simp only [map_one,one_apply_eq_self]

theorem cyclicHilbertAction_add (M : AlgebraicProjectiveData ι A) (z w : CyclicWordAlgebra M) :
    cyclicHilbertAction M (z+w)=cyclicHilbertAction M z+cyclicHilbertAction M w := by
  apply cyclicHilbertOperator_ext M
  intro q
  change cyclicHilbertAction M (z+w) (q : CyclicHilbert M)=
    cyclicHilbertAction M z (q : CyclicHilbert M)+cyclicHilbertAction M w (q : CyclicHilbert M)
  rw [cyclicHilbertAction_coe,cyclicHilbertAction_coe,cyclicHilbertAction_coe,
    ←UniformSpace.Completion.coe_add]
  congr 1
  change ((cyclicPreRepresentation M).toLinearMap (z+w)) q = _
  rw [map_add,LinearMap.add_apply,AlgHom.toLinearMap_apply,AlgHom.toLinearMap_apply]

theorem cyclicHilbertAction_smul (M : AlgebraicProjectiveData ι A) (r : ℝ)
    (z : CyclicWordAlgebra M) : cyclicHilbertAction M (r • z)=r • cyclicHilbertAction M z := by
  apply cyclicHilbertOperator_ext M
  intro q
  change cyclicHilbertAction M (r • z) (q : CyclicHilbert M)=
    r • cyclicHilbertAction M z (q : CyclicHilbert M)
  rw [cyclicHilbertAction_coe,cyclicHilbertAction_coe,←UniformSpace.Completion.coe_smul]
  congr 1
  change ((cyclicPreRepresentation M).toLinearMap (r • z)) q = _
  rw [map_smul,LinearMap.smul_apply,AlgHom.toLinearMap_apply]

theorem cyclicHilbertAction_mul (M : AlgebraicProjectiveData ι A) (z w : CyclicWordAlgebra M) :
    cyclicHilbertAction M (z*w)=cyclicHilbertAction M z*cyclicHilbertAction M w := by
  apply cyclicHilbertOperator_ext M
  intro q
  change cyclicHilbertAction M (z*w) (q : CyclicHilbert M)=
    cyclicHilbertAction M z (cyclicHilbertAction M w (q : CyclicHilbert M))
  rw [cyclicHilbertAction_coe,cyclicHilbertAction_coe,cyclicHilbertAction_coe]
  congr 1
  change ((cyclicPreRepresentation M).toRingHom (z*w)) q = _
  rw [map_mul]
  rfl

def cyclicHilbertAlgRepresentation (M : AlgebraicProjectiveData ι A) :
    CyclicWordAlgebra M →ₐ[ℝ] (CyclicHilbert M →L[ℝ] CyclicHilbert M) where
  toFun := cyclicHilbertAction M
  map_zero' := cyclicHilbertAction_zero M
  map_one' := cyclicHilbertAction_one M
  map_add' := cyclicHilbertAction_add M
  map_mul' := cyclicHilbertAction_mul M
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one,cyclicHilbertAction_smul,cyclicHilbertAction_one]

theorem cyclicPreRepresentation_inner_adjoint (M : AlgebraicProjectiveData ι A)
    (z : CyclicWordAlgebra M) (x y : CyclicPreHilbert M) :
    inner ℝ (cyclicPreRepresentation M (star z) x) y =
      inner ℝ x (cyclicPreRepresentation M z y) := by
  obtain ⟨x,rfl⟩ := cyclicPreHilbertMk_surjective M x
  obtain ⟨y,rfl⟩ := cyclicPreHilbertMk_surjective M y
  rw [cyclicPreRepresentation_mk,cyclicPreRepresentation_mk,
    cyclicPreHilbert_inner_mk,cyclicPreHilbert_inner_mk]
  change M.state (star (star (z : A)*(x : A))*(y : A)) =
    M.state (star (x : A)*((z : A)*(y : A)))
  rw [star_mul,star_star,mul_assoc]

theorem cyclicHilbertAction_star (M : AlgebraicProjectiveData ι A) (z : CyclicWordAlgebra M) :
    cyclicHilbertAction M (star z)=star (cyclicHilbertAction M z) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  exact UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) (fun q r => by
      simpa only [cyclicHilbertAction_coe,UniformSpace.Completion.inner_coe] using
        cyclicPreRepresentation_inner_adjoint M z q r)

def cyclicHilbertRepresentation (M : AlgebraicProjectiveData ι A) :
    CyclicWordAlgebra M →⋆ₐ[ℝ] (CyclicHilbert M →L[ℝ] CyclicHilbert M) where
  toAlgHom := cyclicHilbertAlgRepresentation M
  map_star' := cyclicHilbertAction_star M

end
end AlbertSequential
