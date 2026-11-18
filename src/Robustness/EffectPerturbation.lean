module

public import Robustness.WordContractions
public import Mathlib.Analysis.CStarAlgebra.Basic

/-! The factor-two transition from amplitude error to measured-effect error.
No finite matrix or scalar-field representation is selected here.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

theorem norm_star_mul_self_sub_le {A : Type*} [NormedRing A] [StarRing A]
    [NormedStarGroup A] {a b : A} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖star a * a - star b * b‖ ≤ 2 * ‖a - b‖ := by
  have hid : star a * a - star b * b = star a * (a - b) + (star a - star b) * b := by
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖star a * (a - b)‖ + ‖(star a - star b) * b‖ := norm_add_le _ _
    _ ≤ ‖star a‖ * ‖a - b‖ + ‖star a - star b‖ * ‖b‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = ‖a‖ * ‖a - b‖ + ‖a - b‖ * ‖b‖ := by rw [← star_sub, norm_star, norm_star]
    _ ≤ 1 * ‖a - b‖ + ‖a - b‖ * 1 := by
      exact add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    _ = 2 * ‖a - b‖ := by ring

theorem norm_word_effect_sub_le {A I : Type*} [NormedRing A] [StarRing A]
    [NormedStarGroup A] (hunit : ‖(1 : A)‖ ≤ 1) (a b : I → A)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hab : ∀ i, ‖a i - b i‖ ≤ epsilon)
    (w : List I) :
    ‖star (chronologicalProduct a w) * chronologicalProduct a w -
        star (chronologicalProduct b w) * chronologicalProduct b w‖ ≤
      2 * (w.length : ℝ) * epsilon := by
  apply (norm_star_mul_self_sub_le
    (norm_chronologicalProduct_le_one hunit a ha w)
    (norm_chronologicalProduct_le_one hunit b hb w)).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (norm_chronologicalProduct_sub_le hunit a b ha hb hepsilon hab w) (by norm_num : (0 : ℝ) ≤ 2)

end AlbertSequential
