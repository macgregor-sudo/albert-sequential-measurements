/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameMatrixRealization
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
    {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "A" => P.frameOffDiagonalSpace c r t
local notation "B" => P.frameOffDiagonalTraceForm hfr c r t
local notation "bar" => P.peirceCoefficientConjugate hfr c C

/-- A faithful real matrix representation of the coefficient product,
with conjugation represented by transpose. -/
structure PeirceCoefficientRegularRepresentation (d : ℕ) where
  map : A →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ
  injective : Function.Injective map
  unit : map C.unit = 1
  mul : ∀ a b, map (C.product a b) = map a * map b
  conj : ∀ a, (map a).transpose = map (bar a)

theorem exists_peirceCoefficientRegularRepresentation
    (hAssoc : ∀ x y z, C.product (C.product x y) z = C.product x (C.product y z)) :
    ∃ d, Nonempty (P.PeirceCoefficientRegularRepresentation hfr c C d) := by
  let V := AlbertSequential.PositiveFormModel.Model A
  let core : InnerProductSpace.Core ℝ V := AlbertSequential.PositiveFormModel.innerCore A B
    C.form_symmetric C.form_positive
  let _ : InnerProductSpace.Core ℝ V := core
  let _ : NormedAddCommGroup V := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e := AlbertSequential.PositiveFormModel.linearEquiv A
  let b₀ := stdOrthonormalBasis ℝ V
  let b := b₀.toBasis.map e
  have hb (a : A) (i : Fin (finrank ℝ V)) : b.repr a i = B (b i) a := by
    change b₀.toBasis.repr (e.symm a) i = B (e (b₀ i)) a
    rw [b₀.coe_toBasis_repr_apply, b₀.repr_apply_apply]
    change B (e (b₀ i)) (e (e.symm a)) = B (e (b₀ i)) a
    rw [e.apply_symm_apply]
  let f : A →ₗ[ℝ] Matrix (Fin (finrank ℝ V)) (Fin (finrank ℝ V)) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap.comp C.product
  refine ⟨finrank ℝ V, ⟨{ map := f, injective := ?_, unit := ?_, mul := ?_, conj := ?_ }⟩⟩
  · intro a a' h
    have he : C.product a = C.product a' := (LinearMap.toMatrix b b).injective h
    have hx := LinearMap.congr_fun he C.unit
    rwa [C.unit_right a, C.unit_right a'] at hx
  · change LinearMap.toMatrix b b (C.product C.unit) = 1
    have h : C.product C.unit = LinearMap.id := LinearMap.ext C.unit_left
    rw [h, LinearMap.toMatrix_id]
  · intro a a'
    have h : C.product (C.product a a') = (C.product a).comp (C.product a') :=
      LinearMap.ext (hAssoc a a')
    change LinearMap.toMatrix b b (C.product (C.product a a')) =
      LinearMap.toMatrix b b (C.product a) * LinearMap.toMatrix b b (C.product a')
    rw [h, LinearMap.toMatrix_comp b b b]
  · intro a
    apply Matrix.ext
    intro i j
    change LinearMap.toMatrix b b (C.product a) j i = LinearMap.toMatrix b b (C.product (bar a)) i j
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb, hb, C.form_symmetric (b j)]
    exact P.peirceCoefficient_left_adjoint hfr c C a (b i) (b j)

end AlbertSequential.UnitalJordanProduct
