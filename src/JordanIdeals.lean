/- SPDX-License-Identifier: Apache-2.0 -/
module
public import UnitalJordanProduct

/-! Actual real Jordan ideals as absorbing real submodules. These are distinct
from the instrument-ideality predicate. Restricted units are explicit data,
proved to exist later from the positive associative form. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

def IsJordanIdeal (I : Submodule ℝ E) : Prop :=
  ∀ x∈I,∀ y,P.product y x∈I

theorem isJordanIdeal_bot : P.IsJordanIdeal (⊥ : Submodule ℝ E) := by
  intro x hx y
  have hx0 : x=0 := hx
  simp [hx0]

theorem isJordanIdeal_top : P.IsJordanIdeal (⊤ : Submodule ℝ E) := by
  intro _ _ _
  trivial

theorem isJordanIdeal_inf (I J : Submodule ℝ E)
    (hI : P.IsJordanIdeal I) (hJ : P.IsJordanIdeal J) : P.IsJordanIdeal (I⊓J) := by
  intro x hx y
  exact ⟨hI x hx.1 y,hJ x hx.2 y⟩

def IsSimpleJordan : Prop := P.unit≠0 ∧
  ∀ I : Submodule ℝ E,P.IsJordanIdeal I → I=⊥ ∨ I=⊤

def IsSimpleJordanIdeal (I : Submodule ℝ E) : Prop :=
  P.IsJordanIdeal I ∧ I≠⊥ ∧
    ∀ K : Submodule ℝ E,P.IsJordanIdeal K → K≤I → K=⊥ ∨ K=I

/-- Literal restricted product with its explicitly verified local unit. -/
def idealProduct (I : Submodule ℝ E) (hI : P.IsJordanIdeal I)
    (u : I) (hu : ∀ x : I,P.product u.val x.val=x.val) : UnitalJordanProduct I where
  product :=
    { toFun := fun x =>
        { toFun := fun y => ⟨P.product x.val y.val,hI y.val y.property x.val⟩
          map_add' := fun y z => Subtype.ext ((P.product x.val).map_add y.val z.val)
          map_smul' := fun r y => Subtype.ext ((P.product x.val).map_smul r y.val) }
      map_add' := fun x y => LinearMap.ext fun z =>
        Subtype.ext (LinearMap.congr_fun (P.product.map_add x.val y.val) z.val)
      map_smul' := fun r x => LinearMap.ext fun y =>
        Subtype.ext (LinearMap.congr_fun (P.product.map_smul r x.val) y.val) }
  unit := u
  commutative x y := Subtype.ext (P.commutative x.val y.val)
  unit_left x := Subtype.ext (hu x)
  jordan_identity x y := Subtype.ext (P.jordan_identity x.val y.val)

@[simp] theorem idealProduct_apply (I : Submodule ℝ E) (hI : P.IsJordanIdeal I)
    (u : I) (hu : ∀ x : I,P.product u.val x.val=x.val) (x y : I) :
    ((P.idealProduct I hI u hu).product x y).val=P.product x.val y.val := rfl

@[simp] theorem idealProduct_unit (I : Submodule ℝ E) (hI : P.IsJordanIdeal I)
    (u : I) (hu : ∀ x : I,P.product u.val x.val=x.val) :
    (P.idealProduct I hI u hu).unit=u := rfl

end AlbertSequential.UnitalJordanProduct
