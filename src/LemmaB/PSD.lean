module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# A positive semidefinite real 3×3 matrix has nonnegative determinant

`Matrix.PosSemidef.det_nonneg` is not used; this is proved directly: a 2×2 lemma,
then a Schur-complement argument without division (`G₀₀ · det G = det S'` with
`S' = G₀₀ H - g gᵀ`), and the case `G₀₀ = 0` separately. Then the version for the Gram matrix
of three vectors under a symmetric positive semidefinite bilinear form on any real module.
-/

@[expose] public section

namespace LemmaB

theorem psd2 {a b c : ℝ} (h : ∀ x y : ℝ, 0 ≤ a * x * x + 2 * b * x * y + c * y * y) :
    b ^ 2 ≤ a * c := by
  have ha : 0 ≤ a := by simpa using h 1 0
  rcases ha.lt_or_eq with ha | ha
  · have := h (-b) a
    nlinarith [this, ha]
  · subst ha
    by_cases hb : b = 0
    · subst hb; simp
    · exfalso
      have h1 := h (-(c + 1) / (2 * b)) 1
      have h2 : 2 * b * (-(c + 1) / (2 * b)) = -(c + 1) := by field_simp
      nlinarith [h1, h2]

theorem psd3_det_nonneg (G : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, G i j = G j i)
    (hq : ∀ v : Fin 3 → ℝ, 0 ≤ ∑ i, ∑ j, v i * G i j * v j) : 0 ≤ G.det := by
  have q : ∀ x y z : ℝ, 0 ≤ G 0 0 * x * x + G 1 1 * y * y + G 2 2 * z * z
      + 2 * G 0 1 * x * y + 2 * G 0 2 * x * z + 2 * G 1 2 * y * z := by
    intro x y z
    have := hq ![x, y, z]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
    rw [hs 1 0, hs 2 0, hs 2 1] at this
    linarith
  rw [Matrix.det_fin_three]
  rw [hs 1 0, hs 2 0, hs 2 1]
  have ha : 0 ≤ G 0 0 := by simpa using q 1 0 0
  rcases ha.lt_or_eq with ha | ha
  · -- Schur complement, multiplied through by `G 0 0`
    have hS : ∀ y z : ℝ, 0 ≤ (G 0 0 * G 1 1 - G 0 1 ^ 2) * y * y
        + 2 * (G 0 0 * G 1 2 - G 0 1 * G 0 2) * y * z + (G 0 0 * G 2 2 - G 0 2 ^ 2) * z * z := by
      intro y z
      have h := q (-(G 0 1 * y + G 0 2 * z)) (G 0 0 * y) (G 0 0 * z)
      by_contra hneg
      push Not at hneg
      nlinarith [mul_neg_of_pos_of_neg ha hneg]
    have h2 := psd2 hS
    nlinarith [h2, ha]
  · have hb : G 0 1 = 0 := by
      have := psd2 (a := G 0 0) (b := G 0 1) (c := G 1 1) (fun x y => by
        have := q x y 0; linarith)
      rw [← ha] at this; nlinarith [sq_nonneg (G 0 1)]
    have hc : G 0 2 = 0 := by
      have := psd2 (a := G 0 0) (b := G 0 2) (c := G 2 2) (fun x z => by
        have := q x 0 z; linarith)
      rw [← ha] at this; nlinarith [sq_nonneg (G 0 2)]
    rw [← ha, hb, hc]; simp

/-- The Gram matrix of three vectors under a symmetric positive semidefinite real bilinear form
has nonnegative determinant. -/
theorem gram_det_nonneg {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u) (hpos : ∀ u, 0 ≤ B u u)
    (e : Fin 3 → E) : 0 ≤ (Matrix.of fun i j => B (e i) (e j)).det := by
  apply psd3_det_nonneg
  · intro i j; simp [hsymm]
  · intro v
    have := hpos (∑ i, v i • e i)
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum] at this
    simp only [Matrix.of_apply]
    rw [Finset.sum_comm] at this
    exact this.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

end LemmaB
