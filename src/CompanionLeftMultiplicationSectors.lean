/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionOctonionLeftMultiplication
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The two quaternionic sectors in companion Proposition 2.7. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

def leftModelSpan (a b u x y z : ℝ) : Octonion :=
  (⟨u, x, y, a * z⟩, ⟨b * z, 0, 0, 0⟩)

def leftModelQuaternion (sign u x y z : ℝ) : Quaternion ℝ :=
  ⟨u, x, y, sign * z⟩

/-- The column (c,d) in the multiplicity space of (x,k·star y). -/
def octonionLeftSector (c d : ℝ) (q : Quaternion ℝ) : Octonion :=
  (⟨c * q.re, c * q.imI, c * q.imJ, c * q.imK⟩,
    ⟨d * q.imK, -d * q.imJ, d * q.imI, d * q.re⟩)

theorem octonionLeftSector_pairing (c d e f : ℝ) (p q : Quaternion ℝ) :
    octDot (octonionLeftSector c d p) (octonionLeftSector e f q) =
      (c * e + d * f) * octDot (p, 0) (q, 0) := by
  rw [octDot_eq_coords (p, 0) (q, 0)]
  conv_lhs => rw [octDot_eq_coords]
  simp only [octonionLeftSector, Quaternion.re_zero, Quaternion.imI_zero,
    Quaternion.imJ_zero, Quaternion.imK_zero, mul_zero, add_zero]
  ring

theorem octonionLeftSector_intertwines (a b sign c d : ℝ)
    (hc : a * c + b * d = sign * c) (hd : b * c - a * d = sign * d)
    (u x y z : ℝ) (q : Quaternion ℝ) :
    octonionMul (leftModelSpan a b u x y z) (octonionLeftSector c d q) =
      octonionLeftSector c d (leftModelQuaternion sign u x y z * q) := by
  apply Prod.ext <;> ext <;>
    simp only [octonionMul, leftModelSpan, octonionLeftSector, leftModelQuaternion,
      Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] <;>
    first
    | linear_combination -z * q.imK * hc
    | linear_combination -z * q.imJ * hc
    | linear_combination z * q.imI * hc
    | linear_combination z * q.re * hc
    | linear_combination z * q.re * hd
    | linear_combination -(z * q.imI) * hd
    | linear_combination -(z * q.imJ) * hd
    | linear_combination -(z * q.imK) * hd

theorem leftModelSectorParameters (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) (hb : b ≠ 0) :
    ∃ c d : ℝ, c ^ 2 + d ^ 2 = 1 ∧
      a * c + b * d = c ∧ b * c - a * d = d ∧
      a * (-d) + b * c = -(-d) ∧ b * (-d) - a * c = -c := by
  have hs : 0 < (1 + a) ^ 2 + b ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb)
  let s := Real.sqrt ((1 + a) ^ 2 + b ^ 2)
  have hs' : s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hsq : s ^ 2 = (1 + a) ^ 2 + b ^ 2 := Real.sq_sqrt hs.le
  refine ⟨(1 + a) / s, b / s, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp [hs']
    exact hsq.symm
  all_goals (field_simp [hs']; nlinarith only [h])

private theorem octonionSum_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl

private theorem octonionSum_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl

/-- Recombination of the two signed sectors spans the entire octonion column. -/
theorem octonionLeftSector_spans (c d : ℝ) (h : c ^ 2 + d ^ 2 = 1) (v : Octonion) :
    ∃ p q : Quaternion ℝ,
      octonionLeftSector c d p + octonionLeftSector (-d) c q = v := by
  let x := v.1
  let y := v.2
  let kY : Quaternion ℝ := ⟨y.imK, y.imJ, -y.imI, y.re⟩
  refine ⟨c • x + d • kY, (-d) • x + c • kY, ?_⟩
  apply Prod.ext <;> first | rw [octonionSum_fst] | rw [octonionSum_snd]
  all_goals ext <;>
    simp only [octonionLeftSector, x, y, kY,
      Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      smul_eq_mul] <;>
    first
    | linear_combination v.1.re * h
    | linear_combination v.1.imI * h
    | linear_combination v.1.imJ * h
    | linear_combination v.1.imK * h
    | linear_combination v.2.re * h
    | linear_combination v.2.imI * h
    | linear_combination v.2.imJ * h
    | linear_combination v.2.imK * h

end AlbertSequential.NativeAnalysis
