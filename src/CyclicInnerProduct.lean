/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SequentialEffectLifts
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Algebra.Module.TransferInstance

/-! The SAME algebraic null quotient receives its positive-definite real inner
product. A fresh wrapper carries the norm, leaving the algebraic carriers
and actual operator norms unchanged. No quotient multiplication is defined. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
section
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

def cyclicRawInner (M : AlgebraicProjectiveData ι A) :
    wordSubalgebra M.projection →ₗ[ℝ] wordSubalgebra M.projection →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => M.state (star (x : A) * (y : A))
      map_add' y z := by simp only [AddMemClass.coe_add,mul_add,map_add]
      map_smul' r y := by simp only [SetLike.val_smul,mul_smul_comm,map_smul,smul_eq_mul,RingHom.id_apply] }
  map_add' x y := by
    ext z
    change M.state (star ((x+y : wordSubalgebra M.projection) : A) * (z : A)) =
      M.state (star (x : A) * (z : A)) + M.state (star (y : A) * (z : A))
    simp only [AddMemClass.coe_add,star_add,add_mul,map_add]
  map_smul' r x := by
    ext y
    change M.state (star (r • (x : A)) * (y : A)) = r * M.state (star (x : A) * (y : A))
    simp only [star_smul,star_trivial,smul_mul_assoc,map_smul,smul_eq_mul]

theorem cyclicRawInner_left_null (M : AlgebraicProjectiveData ι A) :
    cyclicNullSubmodule M ≤ (cyclicRawInner M).ker := by
  intro x hx
  apply LinearMap.ext
  intro y
  exact nullFor_pair_zero M.state M.state_star M.state_positive x hx y

theorem cyclicRawInner_right_null (M : AlgebraicProjectiveData ι A) :
    cyclicNullSubmodule M ≤ (cyclicRawInner M).flip.ker := by
  intro x hx
  apply LinearMap.ext
  intro y
  change M.state (star (y : A) * (x : A))=0
  rw [positiveForm_symmetric M.state M.state_star]
  exact nullFor_pair_zero M.state M.state_star M.state_positive x hx y

def cyclicQuotientInner (M : AlgebraicProjectiveData ι A) :
    CyclicWordSpace M →ₗ[ℝ] CyclicWordSpace M →ₗ[ℝ] ℝ :=
  (cyclicRawInner M).liftQ₂ (cyclicNullSubmodule M) (cyclicNullSubmodule M)
    (cyclicRawInner_left_null M) (cyclicRawInner_right_null M)

@[simp] theorem cyclicQuotientInner_mk (M : AlgebraicProjectiveData ι A)
    (x y : wordSubalgebra M.projection) :
    cyclicQuotientInner M (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      M.state (star (x : A) * (y : A)) := rfl

theorem cyclicQuotientInner_symmetric (M : AlgebraicProjectiveData ι A)
    (x y : CyclicWordSpace M) : cyclicQuotientInner M y x=cyclicQuotientInner M x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y => exact positiveForm_symmetric M.state M.state_star y x

theorem cyclicQuotientInner_nonnegative (M : AlgebraicProjectiveData ι A)
    (x : CyclicWordSpace M) : 0 ≤ cyclicQuotientInner M x x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact M.state_positive x

theorem cyclicQuotientInner_definite (M : AlgebraicProjectiveData ι A)
    (x : CyclicWordSpace M) (hx : cyclicQuotientInner M x x=0) : x=0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact (Submodule.Quotient.mk_eq_zero (cyclicNullSubmodule M)).mpr hx

/-- A fresh norm-bearing type, with no target conclusions stored as fields. -/
structure CyclicPreHilbert (M : AlgebraicProjectiveData ι A) where
  toQuotient : CyclicWordSpace M

def cyclicPreHilbertEquiv (M : AlgebraicProjectiveData ι A) :
    CyclicPreHilbert M ≃ CyclicWordSpace M where
  toFun := CyclicPreHilbert.toQuotient
  invFun := fun q => ⟨q⟩
  left_inv := fun q => by cases q; rfl
  right_inv := fun _ => rfl

instance cyclicPreHilbertAddCommGroup (M : AlgebraicProjectiveData ι A) :
    AddCommGroup (CyclicPreHilbert M) := (cyclicPreHilbertEquiv M).addCommGroup

def cyclicPreHilbertAddEquiv (M : AlgebraicProjectiveData ι A) :
    CyclicPreHilbert M ≃+ CyclicWordSpace M where
  toEquiv := cyclicPreHilbertEquiv M
  map_add' := fun _ _ => rfl

instance cyclicPreHilbertModule (M : AlgebraicProjectiveData ι A) :
    Module ℝ (CyclicPreHilbert M) := (cyclicPreHilbertAddEquiv M).module ℝ

def cyclicPreHilbertLinearEquiv (M : AlgebraicProjectiveData ι A) :
    CyclicPreHilbert M ≃ₗ[ℝ] CyclicWordSpace M := (cyclicPreHilbertAddEquiv M).linearEquiv ℝ

instance cyclicPreHilbertCore (M : AlgebraicProjectiveData ι A) :
    InnerProductSpace.Core ℝ (CyclicPreHilbert M) where
  inner x y := cyclicQuotientInner M x.toQuotient y.toQuotient
  conj_inner_symm x y := cyclicQuotientInner_symmetric M x.toQuotient y.toQuotient
  re_inner_nonneg x := cyclicQuotientInner_nonnegative M x.toQuotient
  add_left x y z := (cyclicQuotientInner M).map_add x.toQuotient y.toQuotient
    |> congrArg (fun f => f z.toQuotient)
  smul_left x y r := by
    exact congrArg (fun f => f y.toQuotient)
      ((cyclicQuotientInner M).map_smul r x.toQuotient)
  definite x hx := by
    apply (cyclicPreHilbertEquiv M).injective
    exact cyclicQuotientInner_definite M x.toQuotient hx

instance cyclicPreHilbertNormedAddCommGroup (M : AlgebraicProjectiveData ι A) :
    NormedAddCommGroup (CyclicPreHilbert M) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (CyclicPreHilbert M) _ _ _ (cyclicPreHilbertCore M)

instance cyclicPreHilbertInnerProductSpace (M : AlgebraicProjectiveData ι A) :
    InnerProductSpace ℝ (CyclicPreHilbert M) :=
  @InnerProductSpace.ofCore ℝ (CyclicPreHilbert M) _ _ _ inferInstance

def cyclicPreHilbertMk (M : AlgebraicProjectiveData ι A)
    (x : wordSubalgebra M.projection) : CyclicPreHilbert M := ⟨Submodule.Quotient.mk x⟩

@[simp] theorem cyclicPreHilbert_inner_mk (M : AlgebraicProjectiveData ι A)
    (x y : wordSubalgebra M.projection) :
    inner ℝ (cyclicPreHilbertMk M x) (cyclicPreHilbertMk M y) =
      M.state (star (x : A) * (y : A)) := rfl

theorem cyclicPreHilbert_norm_sq (M : AlgebraicProjectiveData ι A)
    (x : wordSubalgebra M.projection) :
    ‖cyclicPreHilbertMk M x‖^2=M.state (star (x : A) * (x : A)) := by
  rw [← real_inner_self_eq_norm_sq,cyclicPreHilbert_inner_mk]

abbrev CyclicHilbert (M : AlgebraicProjectiveData ι A) :=
  UniformSpace.Completion (CyclicPreHilbert M)

def cyclicHilbertVector (M : AlgebraicProjectiveData ι A) : CyclicHilbert M :=
  (cyclicPreHilbertMk M 1 : CyclicPreHilbert M)

theorem cyclicHilbertVector_norm (M : AlgebraicProjectiveData ι A) :
    ‖cyclicHilbertVector M‖=1 := by
  have h := cyclicPreHilbert_norm_sq M 1
  simp only [OneMemClass.coe_one,star_one,mul_one,M.state_unit] at h
  rw [cyclicHilbertVector,UniformSpace.Completion.norm_coe]
  nlinarith [norm_nonneg (cyclicPreHilbertMk M 1)]

end
end AlbertSequential
