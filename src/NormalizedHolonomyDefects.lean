/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CornerContractionDefects
public import HolonomyCliffordBinding
public import CornerAlgebra
public import Mathlib.Tactic.FieldSimp

/-! Literal normalized projection-word bindings for H/T/F defects.
All divisions expose nonzero real normalizers; no probability is divided by.
The raw contractions retain all errors and need only the base idempotence. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerHolonomy
section Normalized
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

def normalizedCornerWord (J K L : A) (ν : ℝ) : A := ν⁻¹ • (J * K * L * J)

def normalizedCyclicHolonomies (J K L M : A) (ν1 ν2 ν3 : ℝ) : Fin 3 → A :=
  ![normalizedCornerWord J K L ν1, normalizedCornerWord J L M ν2, normalizedCornerWord J M K ν3]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem normalizedCornerWord_star (J K L : A)
    (hJ : star J = J) (hK : star K = K) (hL : star L = L) (ν : ℝ) :
    star (normalizedCornerWord J K L ν) = normalizedCornerWord J L K ν := by
  simp only [normalizedCornerWord, star_smul, star_trivial, star_mul, hJ, hK, hL, mul_assoc]

omit [StarRing A] [StarModule ℝ A] in
theorem normalizedCornerWord_supported (J K L : A) (hJJ : J * J = J) (ν : ℝ) :
    CornerSupported J (normalizedCornerWord J K L ν) := by
  exact supported_smul J _ ⟨cornerWord_left J K L hJJ, cornerWord_right J K L hJJ⟩ _

omit [StarRing A] [StarModule ℝ A] in
theorem normalizedCyclicHolonomies_supported (J K L M : A) (hJJ : J * J = J)
    (ν1 ν2 ν3 : ℝ) : ∀ i, CornerSupported J (normalizedCyclicHolonomies J K L M ν1 ν2 ν3 i) := by
  intro i
  fin_cases i <;> apply normalizedCornerWord_supported <;> exact hJJ

theorem normalizedLeftUnitarity_defect_expansion (J K L : A)
    (hJJ : J * J = J) (hJ : star J = J) (hK : star K = K) (hL : star L = L)
    (a t b ν : ℝ) (hν : ν ≠ 0) (hνsq : ν ^ 2 = a * t * b) :
    (ν ^ 2) • leftUnitarityDefect J (normalizedCornerWord J K L ν) =
      J * L * pairDefectElement K J a * L * J +
        a • (J * pairDefectElement L K t * J) + (a * t) • pairDefectElement J L b := by
  have hs : ν ^ 2 * (ν⁻¹ * ν⁻¹) = 1 := by field_simp [hν]
  calc
    _ = (J * L * K * J) * (J * K * L * J) - (ν ^ 2) • J := by
      rw [leftUnitarityDefect, normalizedCornerWord_star J K L hJ hK hL]
      simp only [normalizedCornerWord, smul_sub, smul_mul_assoc, mul_smul_comm,
        smul_smul, mul_assoc, hs, one_smul]
    _ = _ := by rw [hνsq]; exact reverseProduct_defect_expansion J K L hJJ a t b

theorem normalizedRightUnitarity_defect_expansion (J K L : A)
    (hJJ : J * J = J) (hJ : star J = J) (hK : star K = K) (hL : star L = L)
    (a t b ν : ℝ) (hν : ν ≠ 0) (hνsq : ν ^ 2 = a * t * b) :
    (ν ^ 2) • rightUnitarityDefect J (normalizedCornerWord J K L ν) =
      J * K * pairDefectElement L J b * K * J +
        b • (J * pairDefectElement K L t * J) + (b * t) • pairDefectElement J K a := by
  have hs : ν ^ 2 = b * t * a := hνsq.trans (by ring)
  have hh := normalizedLeftUnitarity_defect_expansion J L K hJJ hJ hL hK b t a ν hν hs
  simpa only [leftUnitarityDefect, rightUnitarityDefect,
    normalizedCornerWord_star J L K hJ hL hK, normalizedCornerWord_star J K L hJ hK hL] using hh

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem normalizedHermitian_defect_expansion (J K L : A)
    (hJ : star J = J) (hK : star K = K) (hL : star L = L)
    (r ν : ℝ) (hν : ν ≠ 0) :
    (2 * ν) • hermitianDefect J (normalizedCornerWord J K L ν) (r / ν) =
      triangleDefectElement J K L r := by
  have hs : (2 * ν) * ((1 / 2) * ν⁻¹) = 1 := by field_simp [hν]
  have hc : (2 * ν) * (r / ν) = 2 * r := by field_simp [hν]
  rw [hermitianDefect, hermitianPart, normalizedCornerWord_star J K L hJ hK hL]
  simp only [normalizedCornerWord, triangleDefectElement, smul_sub, smul_add,
    smul_smul, mul_assoc, hs, hc, one_smul, mul_add, add_mul]

theorem normalizedPairProduct_defect_expansion (J K L M : A)
    (hJJ : J * J = J) (hJ : star J = J) (hK : star K = K)
    (hL : star L = L) (hM : star M = M)
    (b q ν1 ν2 : ℝ) (hν1 : ν1 ≠ 0) (hν2 : ν2 ≠ 0) :
    (2 * ν1 * ν2) • pairProductDefect J
        (normalizedCornerWord J K L ν1) (normalizedCornerWord J L M ν2)
        (b * q / (ν1 * ν2)) =
      J * K * pairDefectElement L J b * M * J +
        J * M * pairDefectElement L J b * K * J + b • tripleDefectElement J K L M q := by
  have hs : (2 * ν1 * ν2) * ((1 / 2) * (ν1⁻¹ * ν2⁻¹)) = 1 := by
    field_simp [hν1, hν2]
  have hr : (2 * ν1 * ν2) * ((1 / 2) * (ν2⁻¹ * ν1⁻¹)) = 1 := by
    field_simp [hν1, hν2]
  have hc : (2 * ν1 * ν2) * (b * q / (ν1 * ν2)) = 2 * b * q := by
    field_simp [hν1, hν2]
  simp only [mul_assoc] at hs hr hc
  calc
    _ = (J * K * L * J) * (J * L * M * J) +
        (J * M * L * J) * (J * L * K * J) - (2 * b * q) • J := by
      rw [pairProductDefect, normalizedCornerWord_star J L M hJ hL hM,
        normalizedCornerWord_star J K L hJ hK hL]
      simp only [normalizedCornerWord, smul_sub, smul_add, smul_mul_assoc,
        mul_smul_comm, smul_smul, mul_assoc, hs, hr, hc, one_smul]
    _ = _ := mixedProduct_defect_expansion J K L M hJJ b q

theorem normalizedCubic_defect_expansion (J K L M : A)
    (hJJ : J * J = J) (hJ : star J = J) (hK : star K = K)
    (hL : star L = L) (hM : star M = M)
    (a b c r ν1 ν2 ν3 : ℝ) (hν1 : ν1 ≠ 0) (hν2 : ν2 ≠ 0) (hν3 : ν3 ≠ 0) :
    (2 * (ν1 * ν2 * ν3)) • cornerCubicDefect J
        (normalizedCyclicHolonomies J K L M ν1 ν2 ν3) (a * b * c * r / (ν1 * ν2 * ν3)) =
      J * K * L * J * L * pairDefectElement M J c * K * J +
        c • (J * K * pairDefectElement L J b * M * K * J) +
        J * K * M * J * M * pairDefectElement L J b * K * J +
        b • (J * K * pairDefectElement M J c * L * K * J) +
        (b * c) • (J * triangleDefectElement K L M r * J) +
        (2 * b * c * r) • pairDefectElement J K a := by
  have hr : (2 * (ν1 * ν2 * ν3)) * ((1 / 2) * (ν3⁻¹ * ν2⁻¹ * ν1⁻¹)) = 1 := by
    field_simp [hν1, hν2, hν3]
  have hc : (2 * (ν1 * ν2 * ν3)) * (a * b * c * r / (ν1 * ν2 * ν3)) =
      2 * a * b * c * r := by field_simp [hν1, hν2, hν3]
  simp only [mul_assoc] at hr hc
  calc
    _ = (J * K * L * J) * (J * L * M * J) * (J * M * K * J) +
        (J * K * M * J) * (J * M * L * J) * (J * L * K * J) - (2 * a * b * c * r) • J := by
      simp only [cornerCubicDefect, normalizedCyclicHolonomies,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, star_smul, star_trivial, star_mul, hJ, hK, hL, hM,
        normalizedCornerWord, smul_sub, smul_add, smul_mul_assoc,
        mul_smul_comm, smul_smul, mul_assoc, hr, hc, one_smul]
    _ = _ := farFace_defect_expansion J K L M hJJ a b c r

end Normalized
end CornerHolonomy
end AlbertSequential
