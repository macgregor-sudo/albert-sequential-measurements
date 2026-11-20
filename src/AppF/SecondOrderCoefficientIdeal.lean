/- SPDX-License-Identifier: Apache-2.0 -/
module
public import AppF.SecondOrderQuotientImage
public import AppF.SecondOrderSpecial

/-! The truncated coefficient product, its associator ideal, and the universal kernel of E₂. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.AppF

abbrev SecondOrderCoefficients := ℂ × Octonion × Octonion

def coefficientProduct (x y : SecondOrderCoefficients) : SecondOrderCoefficients :=
  (x.1 * y.1, octonionMul (cO x.1) y.2.1 + octonionMul x.2.1 (cO y.1),
    octonionMul (cO x.1) y.2.2 + octonionMul x.2.1 y.2.1 + octonionMul x.2.2 (cO y.1))

def coefficientReduction : SecondOrderCoefficients →ₗ[ℝ] Dq where
  toFun x := ⟨x.1,x.2.1,oC x.2.2⟩
  map_add' _ _ := Dq.ext rfl rfl (oC_add _ _)
  map_smul' _ _ := Dq.ext rfl rfl (oC_smul _ _)

theorem coefficientReduction_product (x y : SecondOrderCoefficients) :
    coefficientReduction (coefficientProduct x y) = coefficientReduction x * coefficientReduction y := by
  refine Dq.ext ?_ ?_ ?_
  · rfl
  · rfl
  change oC (octonionMul (cO x.1) y.2.2 + octonionMul x.2.1 y.2.1 +
    octonionMul x.2.2 (cO y.1)) = x.1 * oC y.2.2 + oC x.2.2 * y.1 + oC (octonionMul x.2.1 y.2.1)
  have hl (c : ℂ) (v : Octonion) : oC (octonionMul (cO c) v) = c * oC v := by
    apply Complex.ext <;> simp [oC,cO,octonionMul,Complex.mul_re,Complex.mul_im]
  have hr (c : ℂ) (v : Octonion) : oC (octonionMul v (cO c)) = oC v * c := by
    apply Complex.ext <;> simp [oC,cO,octonionMul,Complex.mul_re,Complex.mul_im]
  rw [oC_add,oC_add,hl,hr]
  abel

def secondOrderCoefficientIdeal := LinearMap.ker coefficientReduction

theorem mem_secondOrderCoefficientIdeal (x : SecondOrderCoefficients) :
    x ∈ secondOrderCoefficientIdeal ↔ x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1.re = 0 ∧ x.2.2.1.imI = 0 := by
  change Dq.mk x.1 x.2.1 (oC x.2.2) = 0 ↔ _
  rw [Dq.ext_iff]
  simp [oC,Complex.ext_iff]

theorem secondOrderCoefficientIdeal_twoSided (x y : SecondOrderCoefficients)
    (hy : y ∈ secondOrderCoefficientIdeal) :
    coefficientProduct x y ∈ secondOrderCoefficientIdeal ∧
    coefficientProduct y x ∈ secondOrderCoefficientIdeal := by
  change coefficientReduction y = 0 at hy
  change coefficientReduction _ = 0 ∧ coefficientReduction _ = 0
  simp only [coefficientReduction_product, hy, mul_zero, zero_mul, and_self]

theorem coefficientReduction_surjective : Function.Surjective coefficientReduction := by
  intro z
  exact ⟨(z.c0,z.o1,cO z.c2), Dq.ext rfl rfl (Complex.ext rfl rfl)⟩

def coefficientQuotientEquiv : (SecondOrderCoefficients ⧸ secondOrderCoefficientIdeal) ≃ₗ[ℝ] Dq :=
  coefficientReduction.quotKerEquivOfSurjective coefficientReduction_surjective

theorem coefficientQuotient_product (x y : SecondOrderCoefficients) :
    coefficientQuotientEquiv (Submodule.Quotient.mk (coefficientProduct x y)) =
      coefficientQuotientEquiv (Submodule.Quotient.mk x) *
      coefficientQuotientEquiv (Submodule.Quotient.mk y) := by
  exact coefficientReduction_product x y

def coefficientAssociator (x y z : SecondOrderCoefficients) :=
  coefficientProduct (coefficientProduct x y) z - coefficientProduct x (coefficientProduct y z)

theorem coefficientAssociator_mem (x y z : SecondOrderCoefficients) :
    coefficientAssociator x y z ∈ secondOrderCoefficientIdeal := by
  change coefficientReduction (_ - _) = 0
  rw [map_sub, coefficientReduction_product, coefficientReduction_product,
    coefficientReduction_product, coefficientReduction_product, mul_assoc, sub_self]

private def degreeOne (u : Octonion) : SecondOrderCoefficients := (0,u,0)
private def degreeZeroI : SecondOrderCoefficients := (Complex.I,0,0)

private theorem degreeTwoAssociator (u v : Octonion) :
    coefficientAssociator degreeZeroI (degreeOne u) (degreeOne v) =
      (0, 0, octonionMul (octonionMul octI u) v - octonionMul octI (octonionMul u v)) := by
  simp [coefficientAssociator,coefficientProduct,degreeOne,degreeZeroI,show cO 0 = 0 from rfl,
    show cO Complex.I = octI from rfl,octonionMul_zero_left,octonionMul_zero_right]

private def pairOct (a b : Quaternion ℝ) : Octonion := (a,b)
private theorem pairOct_mul (a b c d : Quaternion ℝ) :
    octonionMul (pairOct a b) (pairOct c d) = pairOct (a*c-star d*b) (d*a+b*star c) := rfl
private theorem pairOct_add (a b c d : Quaternion ℝ) :
    pairOct a b + pairOct c d = pairOct (a+c) (b+d) := rfl
private theorem pairOct_sub (a b c d : Quaternion ℝ) :
    pairOct a b - pairOct c d = pairOct (a-c) (b-d) := rfl

/-- The paper's six-dimensional coefficient ideal is exactly the span of the actual associators. -/
theorem span_coefficientAssociators :
    Submodule.span ℝ (Set.range (fun t : SecondOrderCoefficients × SecondOrderCoefficients ×
      SecondOrderCoefficients => coefficientAssociator t.1 t.2.1 t.2.2)) = secondOrderCoefficientIdeal := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact coefficientAssociator_mem _ _ _
  · intro x hx
    rcases x with ⟨c,u,⟨v,w⟩⟩
    obtain ⟨hc,hu,hre,him⟩ := (mem_secondOrderCoefficientIdeal _).mp hx
    dsimp only at hc hu hre him
    subst c
    subst u
    let h : Quaternion ℝ := ⟨0,0,-v.imK/2,v.imJ/2⟩
    let r : Quaternion ℝ := ⟨w.imK/2,-w.imJ/2,w.imI/2,-w.re/2⟩
    let S := Submodule.span ℝ (Set.range (fun t : SecondOrderCoefficients × SecondOrderCoefficients ×
      SecondOrderCoefficients => coefficientAssociator t.1 t.2.1 t.2.2))
    have hm (a b : Octonion) : coefficientAssociator degreeZeroI (degreeOne a) (degreeOne b) ∈ S :=
      Submodule.subset_span ⟨(degreeZeroI,degreeOne a,degreeOne b),rfl⟩
    have he : ((0,0,(v,w)) : SecondOrderCoefficients) =
        coefficientAssociator degreeZeroI (degreeOne octL) (degreeOne (0,h)) +
        coefficientAssociator degreeZeroI (degreeOne octJ) (degreeOne (0,r)) := by
      erw [degreeTwoAssociator octL (0,h), degreeTwoAssociator octJ (0,r)]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp
      · simp
      let i : Quaternion ℝ := ⟨0,1,0,0⟩
      let j : Quaternion ℝ := ⟨0,0,1,0⟩
      let A := pairOct i 0
      let B := pairOct 0 1
      let C := pairOct j 0
      let assoc (x y z : Octonion) := octonionMul (octonionMul x y) z - octonionMul x (octonionMul y z)
      change pairOct v w = assoc A B (pairOct 0 h) + assoc A C (pairOct 0 r)
      simp only [assoc,A,B,C,pairOct_mul,pairOct_sub,pairOct_add]
      congr 1 <;> apply Quaternion.ext <;> simp [h,r,i,j,hre,him] <;> ring
    exact he.symm ▸ S.add_mem (hm _ _) (hm _ _)

/-- The reduction both detects the common kernel and attains it. -/
theorem secondOrder_universal_kernel (x : E2) :
    x.val ∈ Kso ↔ ∀ (A : Type) [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A]
      [SMulCommClass ℝ A A] (f : E2 →ₗ[ℝ] A), IsE2JordanHom f → f x = 0 := by
  constructor
  · intro hx A _ _ _ _ f hf
    exact E2_jordanHom_kills_K f hf x hx
  · intro hall
    apply (redq_eq_zero_iff _ x.property).mp
    exact hall _ secondOrderReduction (fun a b => redq_jordan _ _ a.property b.property)

end AlbertSequential.AppF
