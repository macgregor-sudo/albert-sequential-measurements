/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAFrameMatrix

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
    {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "A" => P.frameOffDiagonalSpace c r t
local notation "Mat" => Matrix (Fin n) (Fin n) A
local notation "B" => P.frameOffDiagonalTraceForm hfr c r t
local notation "bar" => P.peirceCoefficientConjugate hfr c C

theorem peirceCoefficientConjugate_product (a b : A) :
    bar (C.product a b) = C.product (bar b) (bar a) := by
  let trace (x : A) := 2 * B x C.unit
  have hval (x : A) : bar x = trace x • C.unit - x := P.peirceCoefficientConjugate_apply hfr c C x
  have htrace : trace (C.product a b) = trace a * trace b - 2 * B a b := by
    dsimp only [trace]
    rw [P.peirceCoefficient_left_adjoint hfr c C a b C.unit, C.unit_right, hval,
      (B b).map_sub, (B b).map_smul, smul_eq_mul, C.form_symmetric b a]
    ring
  have hp := P.peirceCoefficient_product_conjugate_polarized hfr c C a b
  simp only [hval, map_sub, map_smul, C.unit_right] at hp
  rw [hval (C.product a b), htrace, hval a, hval b]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, C.unit_left, C.unit_right]
  linear_combination (norm := module) hp

@[instance_reducible] private def peirceCoefficientRing : NonUnitalNonAssocRing A :=
  { (inferInstance : AddCommGroup A) with
    mul x y := C.product x y
    left_distrib x y z := (C.product x).map_add y z
    right_distrib x y z := LinearMap.congr_fun (C.product.map_add x y) z
    zero_mul x := LinearMap.congr_fun C.product.map_zero x
    mul_zero x := (C.product x).map_zero }

def peirceCoefficientMatrixMul : Mat →ₗ[ℝ] Mat →ₗ[ℝ] Mat := by
  let mul (U V : Mat) : Mat := Matrix.of fun i k => ∑ j, C.product (U i j) (V j k)
  refine LinearMap.mk₂ ℝ mul ?_ ?_ ?_ ?_
  · intro U V X
    apply Matrix.ext
    intro i k
    simp [mul, Matrix.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  · intro a U V
    apply Matrix.ext
    intro i k
    simp [mul, Matrix.smul_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum]
  · intro U V X
    apply Matrix.ext
    intro i k
    simp [mul, Matrix.add_apply, map_add, Finset.sum_add_distrib]
  · intro a U V
    apply Matrix.ext
    intro i k
    simp [mul, Matrix.smul_apply, map_smul, Finset.smul_sum]

local notation "Mmul" => P.peirceCoefficientMatrixMul hfr c C

theorem peirceCoefficientMatrixMul_apply (U V : Mat) (i k : Fin n) :
    Mmul U V i k = ∑ j, C.product (U i j) (V j k) := rfl

theorem peirceCoefficientMatrixMul_single (i j k l : Fin n) (a b : A) :
    Mmul (Matrix.single i j a) (Matrix.single k l b) =
      if j = k then Matrix.single i l (C.product a b) else 0 := by
  let _ : NonUnitalNonAssocRing A := P.peirceCoefficientRing hfr c C
  by_cases h : j = k
  · subst k
    rw [ite_eq_left rfl]
    change Matrix.single i j a * Matrix.single j l b = Matrix.single i l (a * b)
    exact Matrix.single_mul_single_same a i j l b
  · rw [ite_eq_right h]
    change Matrix.single i j a * Matrix.single k l b = 0
    exact Matrix.single_mul_single_of_ne a i j k h b

def peirceCoefficientMatrixJordan : Mat →ₗ[ℝ] Mat →ₗ[ℝ] Mat :=
  (1 / 2 : ℝ) • (Mmul + (Mmul).flip)

local notation "MJ" => P.peirceCoefficientMatrixJordan hfr c C

theorem peirceCoefficientMatrixJordan_apply (U V : Mat) :
    MJ U V = (1 / 2 : ℝ) • (Mmul U V + Mmul V U) := rfl

theorem peirceCoefficientMatrixJordan_comm (U V : Mat) : MJ U V = MJ V U := by
  rw [P.peirceCoefficientMatrixJordan_apply, P.peirceCoefficientMatrixJordan_apply, add_comm]

end AlbertSequential.UnitalJordanProduct
