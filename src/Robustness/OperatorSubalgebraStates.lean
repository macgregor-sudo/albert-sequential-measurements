module
public import Mathlib.Algebra.Star.Subalgebra
public import Robustness.BoundedOperatorOrderUnit
public import Robustness.EffectPerturbation

/-! Actual positive states stay on a real operator star-subalgebra, including
the quaternionic commutant. No extension to all real bounded operators. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (B : StarSubalgebra ℝ (H →L[ℝ] H))

theorem operatorSubalgebra_order_units_positive (T : selfAdjoint B) :
    ((((‖(T.val : H →L[ℝ] H)‖ • 1 + T : selfAdjoint B).val : B) :
      H →L[ℝ] H)).IsPositive ∧
    ((((‖(T.val : H →L[ℝ] H)‖ • 1 - T : selfAdjoint B).val : B) :
      H →L[ℝ] H)).IsPositive := by
  have hv : IsSelfAdjoint (T.val : H →L[ℝ] H) := T.property.map B.subtype
  constructor
  · change (‖(T.val : H →L[ℝ] H)‖ • (1 : H →L[ℝ] H) + (T.val : H →L[ℝ] H)).IsPositive
    exact isPositive_norm_identity_add _ hv
  · change (‖(T.val : H →L[ℝ] H)‖ • (1 : H →L[ℝ] H) - (T.val : H →L[ℝ] H)).IsPositive
    exact isPositive_norm_identity_sub _ hv

theorem operatorSubalgebra_state_abs_le_norm
    (psi : selfAdjoint B →ₗ[ℝ] ℝ) (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint B, (T.val : H →L[ℝ] H).IsPositive → 0 ≤ psi T)
    (T : selfAdjoint B) : |psi T| ≤ ‖(T.val : H →L[ℝ] H)‖ := by
  have hp := hpositive (‖(T.val : H →L[ℝ] H)‖ • 1 + T)
    (operatorSubalgebra_order_units_positive B T).1
  have hm := hpositive (‖(T.val : H →L[ℝ] H)‖ • 1 - T)
    (operatorSubalgebra_order_units_positive B T).2
  simp only [map_add, map_sub, map_smul, hnormalized, smul_eq_mul, mul_one] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem operatorSubalgebra_state_error_le_norm
    (psi : selfAdjoint B →ₗ[ℝ] ℝ) (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint B, (T.val : H →L[ℝ] H).IsPositive → 0 ≤ psi T)
    (X Y : selfAdjoint B) :
    |psi X - psi Y| ≤ ‖((X - Y).val : H →L[ℝ] H)‖ := by
  simpa only [map_sub] using operatorSubalgebra_state_abs_le_norm B psi hnormalized hpositive (X - Y)

def operatorSubalgebraAmplitudeEffect (a : B) : selfAdjoint B :=
  ⟨star a * a, IsSelfAdjoint.star_mul_self a⟩

theorem operatorSubalgebraAmplitudeEffect_value (a : B) :
    ((operatorSubalgebraAmplitudeEffect B a).val : H →L[ℝ] H) =
      star (a : H →L[ℝ] H) * (a : H →L[ℝ] H) := rfl

theorem operatorSubalgebra_amplitude_probability_mem_Icc
    (psi : selfAdjoint B →ₗ[ℝ] ℝ) (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint B, (T.val : H →L[ℝ] H).IsPositive → 0 ≤ psi T)
    (a : B) (ha : ‖(a : H →L[ℝ] H)‖ ≤ 1) :
    psi (operatorSubalgebraAmplitudeEffect B a) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply hpositive
    rw [operatorSubalgebraAmplitudeEffect_value]
    exact ContinuousLinearMap.isPositive_adjoint_comp_self (a : H →L[ℝ] H)
  · calc
      _ ≤ |psi (operatorSubalgebraAmplitudeEffect B a)| := le_abs_self _
      _ ≤ ‖((operatorSubalgebraAmplitudeEffect B a).val : H →L[ℝ] H)‖ :=
        operatorSubalgebra_state_abs_le_norm B psi hnormalized hpositive _
      _ = ‖star (a : H →L[ℝ] H) * (a : H →L[ℝ] H)‖ := rfl
      _ ≤ ‖star (a : H →L[ℝ] H)‖ * ‖(a : H →L[ℝ] H)‖ := norm_mul_le _ _
      _ = ‖(a : H →L[ℝ] H)‖ * ‖(a : H →L[ℝ] H)‖ :=
        congrArg (fun t : ℝ => t * ‖(a : H →L[ℝ] H)‖) (norm_star (a : H →L[ℝ] H))
      _ ≤ 1 * 1 := mul_le_mul ha ha (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem operatorSubalgebra_state_amplitude_error
    (psi : selfAdjoint B →ₗ[ℝ] ℝ) (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint B, (T.val : H →L[ℝ] H).IsPositive → 0 ≤ psi T)
    {a b : B} (ha : ‖(a : H →L[ℝ] H)‖ ≤ 1) (hb : ‖(b : H →L[ℝ] H)‖ ≤ 1) :
    |psi (operatorSubalgebraAmplitudeEffect B a) - psi (operatorSubalgebraAmplitudeEffect B b)| ≤
      2 * ‖(a : H →L[ℝ] H) - (b : H →L[ℝ] H)‖ := by
  calc
    _ ≤ ‖((operatorSubalgebraAmplitudeEffect B a - operatorSubalgebraAmplitudeEffect B b).val :
      H →L[ℝ] H)‖ := operatorSubalgebra_state_error_le_norm B psi hnormalized hpositive _ _
    _ = ‖star (a : H →L[ℝ] H) * (a : H →L[ℝ] H) -
        star (b : H →L[ℝ] H) * (b : H →L[ℝ] H)‖ := rfl
    _ ≤ 2 * ‖(a : H →L[ℝ] H) - (b : H →L[ℝ] H)‖ := norm_star_mul_self_sub_le ha hb

theorem operatorSubalgebra_chronologicalProduct_value (a : I → B) (w : List I) :
    ((chronologicalProduct a w : B) : H →L[ℝ] H) =
      chronologicalProduct (fun i => (a i : H →L[ℝ] H)) w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w i ih =>
      rw [chronologicalProduct_append_singleton, chronologicalProduct_append_singleton]
      change (a i : H →L[ℝ] H) * ((chronologicalProduct a w : B) : H →L[ℝ] H) = _
      rw [ih]

theorem operatorSubalgebra_state_word_error
    (psi : selfAdjoint B →ₗ[ℝ] ℝ) (hnormalized : psi 1 = 1)
    (hpositive : ∀ T : selfAdjoint B, (T.val : H →L[ℝ] H).IsPositive → 0 ≤ psi T)
    (a b : I → B) (ha : ∀ i, ‖(a i : H →L[ℝ] H)‖ ≤ 1)
    (hb : ∀ i, ‖(b i : H →L[ℝ] H)‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hab : ∀ i, ‖(a i : H →L[ℝ] H) - (b i : H →L[ℝ] H)‖ ≤ epsilon) (w : List I) :
    |psi (operatorSubalgebraAmplitudeEffect B (chronologicalProduct a w)) -
      psi (operatorSubalgebraAmplitudeEffect B (chronologicalProduct b w))| ≤
      2 * (w.length : ℝ) * epsilon := by
  have hunit : ‖(1 : H →L[ℝ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hA : ‖((chronologicalProduct a w : B) : H →L[ℝ] H)‖ ≤ 1 := by
    rw [operatorSubalgebra_chronologicalProduct_value]
    exact norm_chronologicalProduct_le_one hunit _ ha w
  have hB : ‖((chronologicalProduct b w : B) : H →L[ℝ] H)‖ ≤ 1 := by
    rw [operatorSubalgebra_chronologicalProduct_value]
    exact norm_chronologicalProduct_le_one hunit _ hb w
  calc
    _ ≤ 2 * ‖((chronologicalProduct a w : B) : H →L[ℝ] H) -
        ((chronologicalProduct b w : B) : H →L[ℝ] H)‖ :=
      operatorSubalgebra_state_amplitude_error B psi hnormalized hpositive hA hB
    _ = 2 * ‖chronologicalProduct (fun i => (a i : H →L[ℝ] H)) w -
        chronologicalProduct (fun i => (b i : H →L[ℝ] H)) w‖ := by
      rw [operatorSubalgebra_chronologicalProduct_value, operatorSubalgebra_chronologicalProduct_value]
    _ ≤ 2 * ((w.length : ℝ) * epsilon) := mul_le_mul_of_nonneg_left
      (norm_chronologicalProduct_sub_le hunit _ _ ha hb hepsilon hab w) (by norm_num)
    _ = 2 * (w.length : ℝ) * epsilon := by ring

end AlbertSequential
