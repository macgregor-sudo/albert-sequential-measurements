/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameMatrixSurjective
public import Defs
public import CompositionAlgebras.Composition.Classification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open scoped Quaternion

private def cdNativeOctonionEquiv :
    CompositionAlgebra.CD (Quaternion ℝ) ≃ₗ[ℝ] AlbertSequential.Octonion where
  toFun x := (x.fst, x.snd)
  invFun x := CompositionAlgebra.CD.mk x.1 x.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem quaternion_cstar_eq_star (a : Quaternion ℝ) :
    CompositionAlgebra.cstar a = star a := by
  apply Quaternion.ext <;> simp [Quaternion.cstar_eq]

private theorem cdNativeOctonionEquiv_mul (a b : CompositionAlgebra.CD (Quaternion ℝ)) :
    cdNativeOctonionEquiv (a * b) =
      AlbertSequential.octonionMul (cdNativeOctonionEquiv a) (cdNativeOctonionEquiv b) := by
  apply Prod.ext
  · change a.fst * b.fst - CompositionAlgebra.cstar b.snd * a.snd =
      a.fst * b.fst - star b.snd * a.snd
    rw [quaternion_cstar_eq_star]
  · change b.snd * a.fst + a.snd * CompositionAlgebra.cstar b.fst =
      b.snd * a.fst + a.snd * star b.fst
    rw [quaternion_cstar_eq_star]

private theorem cdNativeOctonionEquiv_conj (a : CompositionAlgebra.CD (Quaternion ℝ)) :
    cdNativeOctonionEquiv (CompositionAlgebra.cstar a) =
      AlbertSequential.octonionConj (cdNativeOctonionEquiv a) := by
  rw [CompositionAlgebra.CD.cstar_eq, quaternion_cstar_eq_star]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
    {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "A" => P.frameOffDiagonalSpace c r t
local notation "B" => P.frameOffDiagonalTraceForm hfr c r t
local notation "bar" => P.peirceCoefficientConjugate hfr c C

@[instance_reducible]
private def peirceCoefficientUnitalRing : NonAssocRing A :=
  { (inferInstance : AddCommGroup A) with
    one := C.unit
    mul a b := C.product a b
    one_mul := C.unit_left
    mul_one := C.unit_right
    left_distrib x y z := (C.product x).map_add y z
    right_distrib x y z := LinearMap.congr_fun (C.product.map_add x y) z
    zero_mul x := LinearMap.congr_fun C.product.map_zero x
    mul_zero x := (C.product x).map_zero }

/-- The native chart coefficient algebra identified with the actual compact
octonions, including the unit, product, and conjugation conventions. -/
structure PeirceCoefficientNativeOctonionIso where
  map : A ≃ₗ[ℝ] AlbertSequential.Octonion
  unit : map C.unit = AlbertSequential.octonionScalar 1
  mul : ∀ a b, map (C.product a b) = AlbertSequential.octonionMul (map a) (map b)
  conj : ∀ a, map (bar a) = AlbertSequential.octonionConj (map a)

private theorem coefficient_associative_of_map {D : Type*} [Semigroup D]
    (f : A → D) (hf : Function.Injective f) (h : ∀ a b, f (C.product a b) = f a * f b) :
    ∀ x y z, C.product (C.product x y) z = C.product x (C.product y z) := by
  intro x y z
  apply hf
  simp only [h, mul_assoc]

theorem peirceCoefficient_associative_or_nativeOctonion :
    (∀ x y z, C.product (C.product x y) z = C.product x (C.product y z)) ∨
      Nonempty (P.PeirceCoefficientNativeOctonionIso hfr c C) := by
  let _ : NonAssocRing A := P.peirceCoefficientUnitalRing hfr c C
  let _ : IsScalarTower ℝ A A := ⟨fun q x y => LinearMap.congr_fun (C.product.map_smul q x) y⟩
  let _ : SMulCommClass ℝ A A := ⟨fun q x y => ((C.product x).map_smul q y).symm⟩
  let _ : CompositionAlgebra A := ⟨B, C.form_symmetric, C.form_positive, C.form_composition⟩
  let _ : Nontrivial A := nontrivial_of_ne C.unit 0 (P.peirceTriangle_unit_ne_zero hfr c C)
  rcases CompositionAlgebra.hurwitz_classification (C := A) with ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl (P.coefficient_associative_of_map hfr c C f f.injective hf.map_mul)
  · exact Or.inl (P.coefficient_associative_of_map hfr c C f f.injective hf.map_mul)
  · exact Or.inl (P.coefficient_associative_of_map hfr c C f f.injective hf.map_mul)
  · right
    let g := CompositionAlgebra.cdQuaternionEquiv.symm
    have hg := CompositionAlgebra.cdQuaternionEquiv_isCompIso.symm
    let F : CompositionAlgebra.CompEmb A _root_.Octonion :=
      ⟨f.toLinearMap, hf.map_one, hf.map_mul, hf.map_nf⟩
    let G : CompositionAlgebra.CompEmb _root_.Octonion (CompositionAlgebra.CD (Quaternion ℝ)) :=
      ⟨g.toLinearMap, hg.map_one, hg.map_mul, hg.map_nf⟩
    have hbar (a : A) : bar a = CompositionAlgebra.cstar a :=
      P.peirceCoefficientConjugate_apply hfr c C a
    refine ⟨{ map := (f.trans g).trans cdNativeOctonionEquiv, unit := ?_, mul := ?_, conj := ?_ }⟩
    · change cdNativeOctonionEquiv (g (f 1)) = _
      calc
        _ = cdNativeOctonionEquiv (1 : CompositionAlgebra.CD (Quaternion ℝ)) := by
          rw [hf.map_one, hg.map_one]
        _ = _ := rfl
    · intro a b
      change cdNativeOctonionEquiv (g (f (a * b))) =
        AlbertSequential.octonionMul (cdNativeOctonionEquiv (g (f a))) (cdNativeOctonionEquiv (g (f b)))
      rw [hf.map_mul, hg.map_mul, cdNativeOctonionEquiv_mul]
    · intro a
      change cdNativeOctonionEquiv (g (f (bar a))) =
        AlbertSequential.octonionConj (cdNativeOctonionEquiv (g (f a)))
      have hF (x : A) : f (CompositionAlgebra.cstar x) = CompositionAlgebra.cstar (f x) := F.map_cstar x
      have hG (x : _root_.Octonion) : g (CompositionAlgebra.cstar x) = CompositionAlgebra.cstar (g x) :=
        G.map_cstar x
      rw [hbar, hF, hG, cdNativeOctonionEquiv_conj]

end AlbertSequential.UnitalJordanProduct
