/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HermitianDefectTelescope

/-! Exact action-side binder to the already proved scalar Clifford telescope.
Local-unit-to-vector substitution always exposes J*xi=xi. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerHolonomy
section Binding
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

omit [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem squareDefect_action (J h : A) (c : ℝ) (ξ : A) (hξ : J * ξ = ξ) :
    squareCliffordDefect J h c * ξ =
      skewHermitianPart h * (skewHermitianPart h * ξ) + (1 - c ^ 2) • ξ := by
  simp only [squareCliffordDefect, add_mul, smul_mul_assoc, hξ, mul_assoc]

omit [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem pairDefect_action (J h k : A) (c d K : ℝ) (ξ : A) (hξ : J * ξ = ξ) :
    pairCliffordDefect J h k c d K * ξ =
      skewHermitianPart h * (skewHermitianPart k * ξ) +
        skewHermitianPart k * (skewHermitianPart h * ξ) + (2 * (c * d - K)) • ξ := by
  simp only [pairCliffordDefect, add_mul, smul_mul_assoc, hξ, mul_assoc]

omit [SMulCommClass ℝ A A] [StarModule ℝ A] in
theorem cornerSquareDefect_binding (J : A) (h : Fin 3 → A) (c : Fin 3 → ℝ)
    (K12 K13 K23 c4 : ℝ) (ξ : A) (hξ : J * ξ = ξ) (i : Fin 3) :
    squareCliffordDefect J (h i) (c i) * ξ =
      cliffordSquareDefect (fun j => skewHermitianPart (h j))
        (cornerCliffordParameters c K12 K13 K23 c4) i ξ := by
  have hd : (cornerCliffordParameters c K12 K13 K23 c4).diagonal i = 1 - c i ^ 2 := by
    fin_cases i <;> rfl
  rw [cliffordSquareDefect, hd]
  exact squareDefect_action J (h i) (c i) ξ hξ

omit [StarModule ℝ A] in
theorem cornerSquareError_reduction (J : A) (hJJ : J * J = J) (hJ : star J = J)
    (h : Fin 3 → A) (hsupport : ∀ i, CornerSupported J (h i))
    (c : Fin 3 → ℝ) (K12 K13 K23 c4 : ℝ) (ξ : A) (hξ : J * ξ = ξ) (i : Fin 3) :
    cliffordSquareDefect (fun j => skewHermitianPart (h j))
        (cornerCliffordParameters c K12 K13 K23 c4) i ξ =
      ((hermitianPart (h i) + c i • J) * hermitianDefect J (h i) (c i) -
        (1 / 2 : ℝ) • (rightUnitarityDefect J (h i) + leftUnitarityDefect J (h i))) * ξ := by
  rw [← cornerSquareDefect_binding J h c K12 K13 K23 c4 ξ hξ i,
    squareDefect_reduction J (h i) hJJ hJ (hsupport i) (c i)]

theorem cornerDataError_expansion (J : A) (hJJ : J * J = J) (hJ : star J = J)
    (h : Fin 3 → A) (hsupport : ∀ i, CornerSupported J (h i))
    (c : Fin 3 → ℝ) (K12 K13 K23 c4 : ℝ) (ξ : A) (hξ : J * ξ = ξ) :
    let N := fun i => skewHermitianPart (h i)
    let s := cornerCliffordParameters c K12 K13 K23 c4
    cliffordDataError N ξ s =
      (cornerCubicDefect J h c4 - hermitianProductTelescope J h c) * ξ -
        (1 / 2 : ℝ) • (c 0 • cliffordPairDefect N s 1 2 ξ +
          c 1 • cliffordPairDefect N s 0 2 ξ + c 2 • cliffordPairDefect N s 0 1 ξ) := by
  have he := congrArg (fun x : A => x * ξ)
    (cornerDataError_element J hJJ hJ h hsupport c K12 K13 K23 c4)
  dsimp only
  simp only [cliffordDataError, cliffordPairDefect, cornerCliffordParameters,
    CliffordScalarParameters.gramMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    pairCliffordDefect, sub_mul, add_mul, smul_mul_assoc, hξ, mul_assoc] at he ⊢
  exact he

end Binding
end CornerHolonomy
end AlbertSequential
