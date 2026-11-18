/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FixedSCornerConditions

/-! Normalized Clifford discriminants for the two actual fixed-S shapes.
The normalized value 1/12 is explicitly distinct from the denominator-free
base-A value 1/104976 (`fixedS_discriminant`). No state mass enters these normalizers. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential

private theorem sqrt18_square : Real.sqrt (1 / 18 : ℝ) ^ 2 = 1 / 18 := Real.sq_sqrt (by norm_num)
private theorem sqrt27_square : Real.sqrt (1 / 27 : ℝ) ^ 2 = 1 / 27 := Real.sq_sqrt (by norm_num)

private theorem fixedSAB_parameter_values :
    fixedSABCornerData.scalarParameters.m1 = 1 / 2 ∧
    fixedSABCornerData.scalarParameters.m2 = 2 / 3 ∧
    fixedSABCornerData.scalarParameters.m3 = 1 / 2 ∧
    fixedSABCornerData.scalarParameters.u = 0 ∧
    fixedSABCornerData.scalarParameters.v = 0 ∧
    fixedSABCornerData.scalarParameters.w = 0 ∧
    fixedSABCornerData.scalarParameters.d0 ^ 2 = 1 / 12 := by
  dsimp [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
    CornerNumericalData.hermitianConstants, CornerNumericalData.mixed12,
    CornerNumericalData.mixed13, CornerNumericalData.mixed23,
    CornerNumericalData.cubicConstant, fixedSABCornerData]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_pow, sqrt18_square]; norm_num
  · rw [div_pow, sqrt27_square]; norm_num
  · rw [div_pow, sqrt18_square]; norm_num
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring
  · have hd : CornerHolonomy.cornerScalarPart
        ![(1 / 6 : ℝ) / Real.sqrt (1 / 18), (1 / 9) / Real.sqrt (1 / 27), (1 / 6) / Real.sqrt (1 / 18)]
        ((1 / 3) * (1 / 18) / (Real.sqrt (1 / 18) * Real.sqrt (1 / 27)))
        ((1 / 2) * (1 / 18) / (Real.sqrt (1 / 18) * Real.sqrt (1 / 18)))
        ((1 / 3) * (1 / 18) / (Real.sqrt (1 / 27) * Real.sqrt (1 / 18))) =
        (1 / 324) / (Real.sqrt (1 / 18) * Real.sqrt (1 / 27) * Real.sqrt (1 / 18)) := by
      dsimp [CornerHolonomy.cornerScalarPart]
      field_simp
      ring
    rw [hd]
    have he : (1 / 2 : ℝ) * (1 / 3) * (1 / 3) * (1 / 9) = 1 / 162 := by norm_num
    rw [he, ← sub_div]
    norm_num only [show (1 / 162 : ℝ) - 1 / 324 = 1 / 324 by norm_num]
    rw [div_pow, mul_pow, mul_pow, sqrt18_square, sqrt27_square]
    norm_num

private theorem fixedSCD_parameter_values :
    fixedSCDCornerData.scalarParameters.m1 = 1 / 2 ∧
    fixedSCDCornerData.scalarParameters.m2 = 2 / 3 ∧
    fixedSCDCornerData.scalarParameters.m3 = 2 / 3 ∧
    fixedSCDCornerData.scalarParameters.u = 0 ∧
    fixedSCDCornerData.scalarParameters.v = 0 ∧
    fixedSCDCornerData.scalarParameters.w = -1 / 6 ∧
    fixedSCDCornerData.scalarParameters.d0 ^ 2 = 1 / 8 := by
  dsimp [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
    CornerNumericalData.hermitianConstants, CornerNumericalData.mixed12,
    CornerNumericalData.mixed13, CornerNumericalData.mixed23,
    CornerNumericalData.cubicConstant, fixedSCDCornerData]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_pow, sqrt18_square]; norm_num
  · rw [div_pow, sqrt27_square]; norm_num
  · rw [div_pow, sqrt27_square]; norm_num
  · field_simp; ring
  · field_simp; ring
  · field_simp
    nlinarith [sqrt27_square]
  · have hd : CornerHolonomy.cornerScalarPart
        ![(1 / 6 : ℝ) / Real.sqrt (1 / 18), (1 / 9) / Real.sqrt (1 / 27), (1 / 9) / Real.sqrt (1 / 27)]
        ((1 / 3) * (1 / 18) / (Real.sqrt (1 / 18) * Real.sqrt (1 / 27)))
        ((1 / 3) * (1 / 18) / (Real.sqrt (1 / 18) * Real.sqrt (1 / 27)))
        ((1 / 3) * (1 / 18) / (Real.sqrt (1 / 27) * Real.sqrt (1 / 27))) =
        (1 / 324) / (Real.sqrt (1 / 18) * Real.sqrt (1 / 27) * Real.sqrt (1 / 27)) := by
      dsimp [CornerHolonomy.cornerScalarPart]
      field_simp
      ring
    rw [hd]
    have he : (1 / 3 : ℝ) * (1 / 3) * (1 / 3) * (1 / 6) = 1 / 162 := by norm_num
    rw [he, ← sub_div]
    norm_num only [show (1 / 162 : ℝ) - 1 / 324 = 1 / 324 by norm_num]
    rw [div_pow, mul_pow, mul_pow, sqrt18_square, sqrt27_square]
    norm_num

theorem fixedSCorner_discriminant (j : Fin 4) :
    (fixedSCornerData j).scalarParameters.discriminant = 1 / 12 := by
  have ha := fixedSAB_parameter_values
  have hc := fixedSCD_parameter_values
  unfold fixedSCornerData
  split
  · rw [CliffordScalarParameters.discriminant, ha.1, ha.2.1, ha.2.2.1,
      ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2.1, ha.2.2.2.2.2.2]
    norm_num
  · rw [CliffordScalarParameters.discriminant, hc.1, hc.2.1, hc.2.2.1,
      hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2]
    norm_num

/-- Scaling the normalized discriminant back by the three squared normalizers
recovers the two denominator-free base shapes. -/
theorem fixedSCorner_denominator_free (j : Fin 4) :
    (fixedSCornerData j).scalarParameters.discriminant *
      ((fixedSCornerData j).ν0 ^ 2 * (fixedSCornerData j).ν1 ^ 2 * (fixedSCornerData j).ν2 ^ 2) =
      if j.val < 2 then 1 / 104976 else 1 / 157464 := by
  rw [fixedSCorner_discriminant]
  fin_cases j <;> norm_num [fixedSCornerData, fixedSABCornerData, fixedSCDCornerData,
    sqrt18_square, sqrt27_square]

end AlbertSequential
