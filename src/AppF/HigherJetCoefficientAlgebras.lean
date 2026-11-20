/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.HigherJetCoefficientProduct
import Mathlib.Tactic.Abel

/-! Real and quaternionic truncated octonion coefficient algebras. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

inductive HigherJetBase where
  | real
  | quaternionic
  deriving DecidableEq

/-- The chosen base is the image of its coordinate projection. -/
def HigherJetBase.project : HigherJetBase → Octonion →ₗ[ℝ] Octonion
  | .real => {
      toFun x := octonionScalar (octonionReal x)
      map_add' x y := by
        apply Prod.ext
        · change (⟨x.1.re + y.1.re, 0, 0, 0⟩ : Quaternion ℝ) =
            ⟨x.1.re, 0, 0, 0⟩ + ⟨y.1.re, 0, 0, 0⟩
          apply Quaternion.ext <;> simp
        · exact (zero_add (0 : Quaternion ℝ)).symm
      map_smul' r x := by
        apply Prod.ext
        · change (⟨r * x.1.re, 0, 0, 0⟩ : Quaternion ℝ) = r • ⟨x.1.re, 0, 0, 0⟩
          apply Quaternion.ext <;> simp
        · exact (smul_zero r).symm }
  | .quaternionic => {
      toFun x := (x.1, 0)
      map_add' _ _ := Prod.ext rfl (zero_add (0 : Quaternion ℝ)).symm
      map_smul' r x := Prod.ext rfl (smul_zero r).symm }

abbrev HigherJetBase.threshold : HigherJetBase → Fin 4
  | .real => 3
  | .quaternionic => 1

def HigherJetBase.leadingSpace : HigherJetBase → Submodule ℝ Octonion
  | .real => realAssociatorSpace
  | .quaternionic => quaternionicAssociatorSpace

@[simp] theorem HigherJetBase.project_idem (b : HigherJetBase) (x : Octonion) :
    b.project (b.project x) = b.project x := by cases b <;> rfl

private theorem project_mul_fixed (b : HigherJetBase) (x y : Octonion)
    (hx : b.project x = x) (hy : b.project y = y) :
    b.project (octonionMul x y) = octonionMul x y := by
  have hxy : octonionMul x y = octonionMul (b.project x) (b.project y) :=
    congrArg₂ octonionMul hx.symm hy.symm
  have hh : b.project (octonionMul (b.project x) (b.project y)) =
      octonionMul (b.project x) (b.project y) := by
    cases b
    · change HigherJetBase.real.project
        (octonionMul (octonionScalar (octonionReal x)) (octonionScalar (octonionReal y))) =
        octonionMul (octonionScalar (octonionReal x)) (octonionScalar (octonionReal y))
      have hs (r : ℝ) : HigherJetBase.real.project (octonionScalar r) = octonionScalar r := rfl
      rw [octonionMul_scalar_left, map_smul, hs]
    · change ((x.1 * y.1 - star (0 : Quaternion ℝ) * 0), (0 : Quaternion ℝ)) =
        (x.1 * y.1 - star (0 : Quaternion ℝ) * 0, 0 * x.1 + 0 * star y.1)
      simp
  exact (congrArg b.project hxy).trans (hh.trans hxy.symm)

def truncateOctonionJet (m : Fin 4) (x : OctonionJetCoefficients) : OctonionJetCoefficients :=
  fun i => if i ≤ m then x i else 0

@[simp] theorem truncateOctonionJet_apply (m : Fin 4) (x : OctonionJetCoefficients) (i : Fin 4) :
    truncateOctonionJet m x i = if i ≤ m then x i else 0 := rfl

private theorem octonionJetProduct_truncate_left (m j : Fin 4) (hj : j ≤ m)
    (x y : OctonionJetCoefficients) :
    octonionJetProduct (truncateOctonionJet m x) y j = octonionJetProduct x y j := by
  fin_cases m <;> fin_cases j <;>
    simp_all [octonionJetProduct, truncateOctonionJet, Fin.le_iff_val_le_val]

private theorem octonionJetProduct_truncate_right (m j : Fin 4) (hj : j ≤ m)
    (x y : OctonionJetCoefficients) :
    octonionJetProduct x (truncateOctonionJet m y) j = octonionJetProduct x y j := by
  fin_cases m <;> fin_cases j <;>
    simp_all [octonionJetProduct, truncateOctonionJet, Fin.le_iff_val_le_val]

/-- Native octonion jets with constant coefficient in the chosen base and all coefficients
above `m` zero. The product below is actual truncated convolution. -/
def HigherJetCoefficients (b : HigherJetBase) (m : Fin 4) : Submodule ℝ OctonionJetCoefficients where
  carrier := {x | b.project (x 0) = x 0 ∧ ∀ i, m < i → x i = 0}
  zero_mem' := ⟨map_zero _, fun _ _ => rfl⟩
  add_mem' {x y} hx hy := by
    exact ⟨by change b.project (x 0 + y 0) = x 0 + y 0; rw [map_add, hx.1, hy.1],
      fun i hi => by change x i + y i = 0; rw [hx.2 i hi, hy.2 i hi, zero_add]⟩
  smul_mem' r x hx := by
    exact ⟨by change b.project (r • x 0) = r • x 0; rw [map_smul, hx.1],
      fun i hi => by change r • x i = 0; rw [hx.2 i hi, smul_zero]⟩

namespace HigherJetCoefficients

variable {b : HigherJetBase} {m : Fin 4}

@[simp] theorem base (x : HigherJetCoefficients b m) : b.project (x.val 0) = x.val 0 :=
  x.property.1

theorem support (x : HigherJetCoefficients b m) (i : Fin 4) (hi : m < i) : x.val i = 0 :=
  x.property.2 i hi

def product (x y : HigherJetCoefficients b m) : HigherJetCoefficients b m :=
  ⟨truncateOctonionJet m (octonionJetProduct x.val y.val),
    ⟨by simpa [octonionJetProduct, truncateOctonionJet] using
          project_mul_fixed b (x.val 0) (y.val 0) x.property.1 y.property.1,
      fun i hi => by simp [truncateOctonionJet, not_le_of_gt hi]⟩⟩

def unit (b : HigherJetBase) (m : Fin 4) : HigherJetCoefficients b m :=
  ⟨![octonionScalar 1, 0, 0, 0],
    ⟨by cases b <;> rfl, fun i hi => by
      fin_cases i <;> simp_all [Fin.lt_def]⟩⟩

theorem product_unit_left (x : HigherJetCoefficients b m) : product (unit b m) x = x := by
  apply Subtype.ext
  funext i
  change (if i ≤ m then octonionJetProduct (unit b m).val x.val i else 0) = x.val i
  split
  · rename_i hi
    fin_cases i <;> simp [unit, octonionJetProduct, octonionMul_scalar_left, octonionMul_zero_left]
  · exact (support x i (lt_of_not_ge ‹_›)).symm

theorem product_unit_right (x : HigherJetCoefficients b m) : product x (unit b m) = x := by
  apply Subtype.ext
  funext i
  change (if i ≤ m then octonionJetProduct x.val (unit b m).val i else 0) = x.val i
  split
  · rename_i hi
    fin_cases i <;> simp [unit, octonionJetProduct, octonionMul_scalar_right, octonionMul_zero_right]
  · exact (support x i (lt_of_not_ge ‹_›)).symm

theorem product_add_left (x y z : HigherJetCoefficients b m) :
    product (x + y) z = product x z + product y z := by
  apply Subtype.ext
  funext i
  by_cases hi : i ≤ m
  · fin_cases i <;> simp_all [product, octonionJetProduct, octonionMul_add_left] <;> abel
  · simp [product, hi]

theorem product_add_right (x y z : HigherJetCoefficients b m) :
    product x (y + z) = product x y + product x z := by
  apply Subtype.ext
  funext i
  by_cases hi : i ≤ m
  · fin_cases i <;> simp_all [product, octonionJetProduct, octonionMul_add_right] <;> abel
  · simp [product, hi]

theorem product_smul_left (r : ℝ) (x y : HigherJetCoefficients b m) :
    product (r • x) y = r • product x y := by
  apply Subtype.ext
  funext i
  by_cases hi : i ≤ m
  · fin_cases i <;> simp_all [product, octonionJetProduct, octonionMul_smul_left, smul_add]
  · simp [product, hi]

theorem product_smul_right (r : ℝ) (x y : HigherJetCoefficients b m) :
    product x (r • y) = r • product x y := by
  apply Subtype.ext
  funext i
  by_cases hi : i ≤ m
  · fin_cases i <;> simp_all [product, octonionJetProduct, octonionMul_smul_right, smul_add]
  · simp [product, hi]

def bilinear : HigherJetCoefficients b m →ₗ[ℝ]
    HigherJetCoefficients b m →ₗ[ℝ] HigherJetCoefficients b m :=
  LinearMap.mk₂ ℝ product product_add_left product_smul_left product_add_right product_smul_right

def associator (x y z : HigherJetCoefficients b m) :=
  product (product x y) z - product x (product y z)

theorem associator_apply (x y z : HigherJetCoefficients b m) (i : Fin 4) (hi : i ≤ m) :
    (associator x y z).val i = octonionJetAssociator x.val y.val z.val i := by
  change truncateOctonionJet m (octonionJetProduct (truncateOctonionJet m
    (octonionJetProduct x.val y.val)) z.val) i -
    truncateOctonionJet m (octonionJetProduct x.val (truncateOctonionJet m
      (octonionJetProduct y.val z.val))) i = _
  simp only [truncateOctonionJet_apply, ite_eq_left hi]
  rw [octonionJetProduct_truncate_left m i hi, octonionJetProduct_truncate_right m i hi]
  rfl

theorem associator_eq_zero_below (b : HigherJetBase) (m : Fin 4) (hm : m < b.threshold)
    (x y z : HigherJetCoefficients b m) : associator x y z = 0 := by
  apply Subtype.ext
  funext i
  by_cases hi : i ≤ m
  · rw [associator_apply x y z i hi]
    cases b
    · have h := octonionJetAssociator_realBase x.val y.val z.val _ _ _
          (base x).symm (base y).symm (base z).symm
      fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · change m < (3 : Fin 4) at hm
        exact False.elim ((not_le_of_gt hm) hi)
    · have h := octonionJetAssociator_quaternionicBase x.val y.val z.val _ _ _
          (base x).symm (base y).symm (base z).symm
      change m < (1 : Fin 4) at hm
      have h₀ : i = 0 := by apply Fin.ext; change i.val = 0; omega
      rw [h₀]
      exact h.1
  · exact support _ i (lt_of_not_ge hi)

/-- At the threshold, every associator is supported in the top degree with value
in the specified real or quaternionic orthogonal coefficient space. -/
theorem associator_at_threshold (b : HigherJetBase) (x y z : HigherJetCoefficients b b.threshold) :
    (∀ i, i ≠ b.threshold → (associator x y z).val i = 0) ∧
    (associator x y z).val b.threshold ∈ b.leadingSpace := by
  cases b
  · have h := octonionJetAssociator_realBase x.val y.val z.val _ _ _
        (base x).symm (base y).symm (base z).symm
    constructor
    · intro i hi
      rw [associator_apply x y z i (by change i ≤ (3 : Fin 4); omega)]
      fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact False.elim (hi rfl)
    · change (associator x y z).val 3 ∈ realAssociatorSpace
      rw [associator_apply x y z (3 : Fin 4) le_rfl, h.2.2.2]
      exact octonionReal_octAssociator _ _ _
  · have h := octonionJetAssociator_quaternionicBase x.val y.val z.val _ _ _
        (base x).symm (base y).symm (base z).symm
    constructor
    · intro i hi
      change i ≠ (1 : Fin 4) at hi
      by_cases hle : i ≤ (1 : Fin 4)
      · have h₀ : i = 0 := by apply Fin.ext; change i.val = 0; omega
        rw [associator_apply x y z i hle, h₀]
        exact h.1
      · exact support _ i (lt_of_not_ge hle)
    · change (associator x y z).val 1 ∈ quaternionicAssociatorSpace
      rw [associator_apply x y z (1 : Fin 4) le_rfl]
      exact h.2

end HigherJetCoefficients
end AlbertSequential.AppF
