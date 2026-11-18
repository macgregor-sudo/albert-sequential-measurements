/- SPDX-License-Identifier: Apache-2.0 -/
module

public import EuclideanJordanSquareCone
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Ordinary matrix trace supplies a positive associative form on a supplied
faithful Hermitian Jordan image. Only the separate Element wrapper receives
the induced norm; no norm or algebra instance is put on the source carrier. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential

structure FaithfulHermitianJordanEmbedding {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) (d : ℕ) where
  map : E →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ
  injective : Function.Injective map
  hermitian : ∀ x, (map x).IsHermitian
  unit : map P.unit = 1
  jordan : ∀ x y, map (P.product x y) =
    (1 / 2 : ℝ) • (map x * map y + map y * map x)

namespace FaithfulHermitianJordanEmbedding
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {P : UnitalJordanProduct E} {d : ℕ} (ι : FaithfulHermitianJordanEmbedding P d)

def traceForm (x y : E) : ℝ := (Matrix.trace (ι.map x * ι.map y)).re

theorem traceForm_symm (x y : E) : ι.traceForm x y = ι.traceForm y x := by
  unfold traceForm
  rw [Matrix.trace_mul_comm]

theorem traceForm_add_left (x y z : E) :
    ι.traceForm (x+y) z = ι.traceForm x z + ι.traceForm y z := by
  simp [traceForm, add_mul, Matrix.trace_add]

theorem traceForm_smul_left (r : ℝ) (x y : E) :
    ι.traceForm (r • x) y = r * ι.traceForm x y := by
  simp [traceForm, Matrix.trace_smul]

theorem traceForm_self_nonnegative (x : E) : 0 ≤ ι.traceForm x x := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self (ι.map x)
  rw [ι.hermitian x] at hp
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

theorem traceForm_self_eq_zero (x : E) : ι.traceForm x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hp := Matrix.posSemidef_conjTranspose_mul_self (ι.map x)
    have hr : (Matrix.trace ((ι.map x).conjTranspose * ι.map x)).re = 0 := by
      rw [ι.hermitian x]
      exact h
    have hz : Matrix.trace ((ι.map x).conjTranspose * ι.map x) = 0 :=
      Complex.ext hr (Complex.nonneg_iff.mp hp.trace_nonneg).2.symm
    have hm := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz
    apply ι.injective
    simpa only [map_zero] using hm
  · intro h
    simp [h, traceForm]

theorem map_square (x : E) : ι.map (P.product x x) = ι.map x * ι.map x := by
  rw [ι.jordan]
  module

theorem map_quadratic (a x : E) :
    ι.map (P.quadraticRepresentation a x) = ι.map a * ι.map x * ι.map a := by
  simp only [P.quadraticRepresentation_apply, map_sub, map_smul, ι.jordan,
    Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, smul_add, smul_smul,
    Matrix.mul_assoc]
  module

theorem traceForm_associative (x y z : E) :
    ι.traceForm (P.product x y) z = ι.traceForm x (P.product y z) := by
  unfold traceForm
  rw [ι.jordan, ι.jordan]
  simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
    Matrix.trace_smul, Matrix.trace_add, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Matrix.mul_assoc, Matrix.trace_mul_cycle (ι.map y) (ι.map x) (ι.map z),
    Matrix.trace_mul_cycle (ι.map z) (ι.map y) (ι.map x)]
  rw [Matrix.mul_assoc]

structure Element (ι : FaithfulHermitianJordanEmbedding P d) where
  value : E

def elementEquiv : ι.Element ≃ E where
  toFun := Element.value
  invFun := Element.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup ι.Element := ι.elementEquiv.addCommGroup
def elementAddEquiv : ι.Element ≃+ E := ι.elementEquiv.addEquiv
instance : Module ℝ ι.Element := ι.elementAddEquiv.module ℝ

def elementLinearEquiv : ι.Element ≃ₗ[ℝ] E where
  toEquiv := ι.elementEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : FiniteDimensional ℝ ι.Element :=
  FiniteDimensional.of_injective (ι.map.comp ι.elementLinearEquiv.toLinearMap)
    (ι.injective.comp ι.elementEquiv.injective)

@[instance_reducible] def innerCore : InnerProductSpace.Core ℝ ι.Element where
  inner x y := ι.traceForm x.value y.value
  conj_inner_symm x y := ι.traceForm_symm y.value x.value
  re_inner_nonneg x := ι.traceForm_self_nonnegative x.value
  add_left x y z := ι.traceForm_add_left x.value y.value z.value
  smul_left x y r := ι.traceForm_smul_left r x.value y.value
  definite x hx := ι.elementEquiv.injective ((ι.traceForm_self_eq_zero x.value).mp hx)

instance : NormedAddCommGroup ι.Element := ι.innerCore.toNormedAddCommGroup
instance : InnerProductSpace ℝ ι.Element :=
  InnerProductSpace.ofCore { ι.innerCore with }

@[simp] theorem element_inner (x y : ι.Element) :
    inner ℝ x y = ι.traceForm x.value y.value := rfl

def elementProduct : UnitalJordanProduct ι.Element where
  product :=
    { toFun x :=
        { toFun y := ⟨P.product x.value y.value⟩
          map_add' y z := ι.elementEquiv.injective ((P.product x.value).map_add y.value z.value)
          map_smul' r y := ι.elementEquiv.injective ((P.product x.value).map_smul r y.value) }
      map_add' x y := by
        ext z
        apply ι.elementEquiv.injective
        exact LinearMap.congr_fun (P.product.map_add x.value y.value) z.value
      map_smul' r x := by
        ext z
        apply ι.elementEquiv.injective
        exact LinearMap.congr_fun (P.product.map_smul r x.value) z.value }
  unit := ⟨P.unit⟩
  commutative x y := ι.elementEquiv.injective (P.commutative x.value y.value)
  unit_left x := ι.elementEquiv.injective (P.unit_left x.value)
  jordan_identity x y := ι.elementEquiv.injective (P.jordan_identity x.value y.value)

theorem elementProduct_associative (x y z : ι.Element) :
    inner ℝ (ι.elementProduct.product x y) z =
      inner ℝ x (ι.elementProduct.product y z) :=
  ι.traceForm_associative x.value y.value z.value

end FaithfulHermitianJordanEmbedding
end AlbertSequential
