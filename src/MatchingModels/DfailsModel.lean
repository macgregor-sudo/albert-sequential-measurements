/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.MatrixClassIBridge
public import FixedSBinding
public import ThirteenTracesAndAform
public import NativeAtomCompression
public import NativeWordDuality
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Calculation `prop:Dfails`: Explicit `ℂ^12` Model with `D_tet = 1/12 > 0`

Formalizes Calculation `prop:Dfails` and Appendix `app:cert:models`:
1. Explicit `4 × 4` skew-Hermitian anticommuting matrices `dfailsC1, dfailsC2, dfailsC3`
   with `C_k^2 = -1`, `J = C_1 C_2 C_3 = 1_2 ⊗ σ_x`, and `Tr = 0` on `C_k`, `C_i C_j` (`i ≠ j`),
   `J`, `J C_k`.
2. Four column isometries `dfailsIsometry : Fin 4 → Matrix (Fin 12) (Fin 4) ℂ`, rank-4
   Hermitian projections `dfailsProj`, and `dfailsModel : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12))`
   with state `Tr/12`.
3. `dfails_length_le_two`: exact agreement with `nativeWordProbability fixedS ((1/3 : ℝ) • albertUnit)`
   for all words of length `≤ 2`.
4. Exact extraction of all 13 traces of `dfailsModel` from length `≤ 4` word probabilities
   (`sec:fp:traces`), matching those of `fixedS` (`o_AB = 1/2`, others `1/3`, `R_ABC = R_ABD = 1/6`,
   `R_ACD = R_BCD = 1/9`, `t_1 = t_2 = t_3 = 1/18`), hence `fpTetraDtet = 1/12 > 0`.
5. `dfails_purity_defect`: for `T = P_C P_D P_C - (1/3) P_C`, `(1/12) * (Tr(T^2)).re = 4 / 243`.
6. `dfails_length_three_deviations`: full characterization of all words of length 3:
   - for `w.map Prod.fst = [2, 3, 2]` or `[3, 2, 3]` (`C,D,C` or `D,C,D`), the deviation is
     `± 4 / 243` with exact sign `(if b₀ == b₂ then 1 else -1) * (4 / 243)` (so `|Δ| = 4 / 243`);
   - for all other words of length 3, `dfailsModel.probability w = nativeWordProbability fixedS ((1/3 : ℝ) • albertUnit) w`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.MatchingModels

open scoped Matrix
open AlbertSequential.NativeAnalysis

/-! ## Section 1: Explicit `4 × 4` Matrices `C₁, C₂, C₃` and `J` -/

section Clifford4

def dfailsC1 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![0, 0, Complex.I, 0], ![0, 0, 0, Complex.I],
    ![Complex.I, 0, 0, 0], ![0, Complex.I, 0, 0]]

def dfailsC2 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![0, 0, 1, 0], ![0, 0, 0, 1], ![(-1 : ℂ), 0, 0, 0], ![0, (-1 : ℂ), 0, 0]]

def dfailsC3 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![0, Complex.I, 0, 0], ![Complex.I, 0, 0, 0],
    ![0, 0, 0, -Complex.I], ![0, 0, -Complex.I, 0]]

def dfailsJ : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]]

theorem dfailsC1_conjTranspose : dfailsC1.conjTranspose = -dfailsC1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dfailsC1]

theorem dfailsC2_conjTranspose : dfailsC2.conjTranspose = -dfailsC2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dfailsC2]

theorem dfailsC3_conjTranspose : dfailsC3.conjTranspose = -dfailsC3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dfailsC3]

theorem dfailsJ_conjTranspose : dfailsJ.conjTranspose = dfailsJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dfailsJ]

theorem dfailsC1_sq : dfailsC1 * dfailsC1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dfailsC1, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem dfailsC2_sq : dfailsC2 * dfailsC2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dfailsC2, Matrix.mul_apply, Fin.sum_univ_four]

theorem dfailsC3_sq : dfailsC3 * dfailsC3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dfailsC3, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem dfailsJ_sq : dfailsJ * dfailsJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dfailsJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem dfailsC1_C2_anticomm : dfailsC2 * dfailsC1 = -(dfailsC1 * dfailsC2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dfailsC1, dfailsC2, Matrix.mul_apply, Fin.sum_univ_four]

theorem dfailsC1_C3_anticomm : dfailsC3 * dfailsC1 = -(dfailsC1 * dfailsC3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dfailsC1, dfailsC3, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem dfailsC2_C3_anticomm : dfailsC3 * dfailsC2 = -(dfailsC2 * dfailsC3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dfailsC2, dfailsC3, Matrix.mul_apply, Fin.sum_univ_four]

theorem dfailsC1_C2_C3 : dfailsC1 * dfailsC2 * dfailsC3 = dfailsJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dfailsC1, dfailsC2, dfailsC3, dfailsJ, Matrix.mul_apply, Fin.sum_univ_four,
      Complex.I_mul_I]

theorem dfailsC1_trace : Matrix.trace dfailsC1 = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsC1]

theorem dfailsC2_trace : Matrix.trace dfailsC2 = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsC2]

theorem dfailsC3_trace : Matrix.trace dfailsC3 = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsC3]

theorem dfailsJ_trace : Matrix.trace dfailsJ = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsJ]

theorem dfailsC1C2_trace : Matrix.trace (dfailsC1 * dfailsC2) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsC1, dfailsC2]

theorem dfailsC1C3_trace : Matrix.trace (dfailsC1 * dfailsC3) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsC1, dfailsC3]

theorem dfailsC2C3_trace : Matrix.trace (dfailsC2 * dfailsC3) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsC2, dfailsC3]

theorem dfailsJC1_trace : Matrix.trace (dfailsJ * dfailsC1) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsJ, dfailsC1]

theorem dfailsJC2_trace : Matrix.trace (dfailsJ * dfailsC2) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsJ, dfailsC2]

theorem dfailsJC3_trace : Matrix.trace (dfailsJ * dfailsC3) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, dfailsJ, dfailsC3]

end Clifford4

/-! ## Section 2: Isometries `V_A, V_B, V_C, V_D` and Projections `P_dfails` on `ℂ^12` -/

section IsometriesAndProjections

def fin3ProdFin4Equiv12 : Fin 3 × Fin 4 ≃ Fin 12 where
  toFun p := ⟨4 * p.1.1 + p.2.1, by omega⟩
  invFun k := (⟨k.1 / 4, by omega⟩, ⟨k.1 % 4, by omega⟩)
  left_inv p := by rcases p with ⟨i, j⟩; fin_cases i <;> fin_cases j <;> decide
  right_inv k := by fin_cases k <;> decide

def blockCol12 (X₀ X₁ X₂ : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 12) (Fin 4) ℂ :=
  Matrix.of fun r c =>
    let rp := fin3ProdFin4Equiv12.symm r
    match rp.1 with
    | 0 => X₀ rp.2 c
    | 1 => X₁ rp.2 c
    | 2 => X₂ rp.2 c

theorem blockCol12_conjTranspose_mul (X₀ X₁ X₂ Y₀ Y₁ Y₂ : Matrix (Fin 4) (Fin 4) ℂ) :
    (blockCol12 X₀ X₁ X₂).conjTranspose * blockCol12 Y₀ Y₁ Y₂ =
      X₀.conjTranspose * Y₀ + X₁.conjTranspose * Y₁ + X₂.conjTranspose * Y₂ := by
  ext i j
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp fin3ProdFin4Equiv12, Fintype.sum_prod_type]
  rw [Fin.sum_univ_three]
  simp [blockCol12, Matrix.mul_apply, Matrix.conjTranspose_apply, add_assoc]

def invSqrt2C : ℂ := ((Real.sqrt 2 : ℝ)⁻¹ : ℝ)
def invSqrt3C : ℂ := ((Real.sqrt 3 : ℝ)⁻¹ : ℝ)

theorem invSqrt2C_mul_self : invSqrt2C * invSqrt2C = (1 / 2 : ℂ) := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simpa [invSqrt2C] using congrArg ((↑) : ℝ → ℂ) h

theorem invSqrt3C_mul_self : invSqrt3C * invSqrt3C = (1 / 3 : ℂ) := by
  have h : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = (1 / 3 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simpa [invSqrt3C] using congrArg ((↑) : ℝ → ℂ) h

theorem star_invSqrt2C : star invSqrt2C = invSqrt2C := by
  simp [invSqrt2C, Complex.conj_ofReal]

theorem star_invSqrt3C : star invSqrt3C = invSqrt3C := by
  simp [invSqrt3C, Complex.conj_ofReal]

def dfailsIsometry : Fin 4 → Matrix (Fin 12) (Fin 4) ℂ
  | 0 => blockCol12 1 0 0
  | 1 => invSqrt2C • blockCol12 1 1 0
  | 2 => invSqrt3C • blockCol12 1 (-dfailsC1) 1
  | 3 => invSqrt3C • blockCol12 1 (-dfailsC2) (-dfailsC3)

theorem dfailsIsometry_isometry (i : Fin 4) :
    (dfailsIsometry i).conjTranspose * dfailsIsometry i = 1 := by
  fin_cases i
  · simp [dfailsIsometry, blockCol12_conjTranspose_mul]
  · simp only [dfailsIsometry, Matrix.conjTranspose_smul, star_invSqrt2C,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, blockCol12_conjTranspose_mul,
      Matrix.conjTranspose_one, Matrix.mul_one, Matrix.conjTranspose_zero,
      invSqrt2C_mul_self]
    ext a b; simp; ring
  · simp only [dfailsIsometry, Matrix.conjTranspose_smul, star_invSqrt3C,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, blockCol12_conjTranspose_mul,
      Matrix.conjTranspose_one, Matrix.mul_one, Matrix.conjTranspose_neg,
      dfailsC1_conjTranspose, neg_neg, Matrix.mul_neg, dfailsC1_sq, invSqrt3C_mul_self]
    ext a b; simp; ring
  · simp only [dfailsIsometry, Matrix.conjTranspose_smul, star_invSqrt3C,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, blockCol12_conjTranspose_mul,
      Matrix.conjTranspose_one, Matrix.mul_one, Matrix.conjTranspose_neg,
      dfailsC2_conjTranspose, dfailsC3_conjTranspose, neg_neg,
      Matrix.mul_neg, dfailsC2_sq, dfailsC3_sq, invSqrt3C_mul_self]
    ext a b; simp; ring

def dfailsProj (i : Fin 4) : Matrix (Fin 12) (Fin 12) ℂ :=
  dfailsIsometry i * (dfailsIsometry i).conjTranspose

theorem dfailsProj_hermitian (i : Fin 4) : (dfailsProj i).IsHermitian := by
  rw [Matrix.IsHermitian, dfailsProj, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem dfailsProj_idempotent (i : Fin 4) : dfailsProj i * dfailsProj i = dfailsProj i := by
  unfold dfailsProj
  calc
    dfailsIsometry i * (dfailsIsometry i).conjTranspose *
        (dfailsIsometry i * (dfailsIsometry i).conjTranspose) =
        dfailsIsometry i * ((dfailsIsometry i).conjTranspose * dfailsIsometry i) *
          (dfailsIsometry i).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = dfailsIsometry i * (dfailsIsometry i).conjTranspose := by
      rw [dfailsIsometry_isometry i, Matrix.mul_one]

theorem dfailsProj_trace (i : Fin 4) : Matrix.trace (dfailsProj i) = 4 := by
  unfold dfailsProj
  rw [Matrix.trace_mul_comm, dfailsIsometry_isometry i]
  simp

def dfailsModel : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)) :=
  c12TraceModel dfailsProj dfailsProj_hermitian dfailsProj_idempotent

theorem dfailsModel_probability (w : Word (Fin 4)) :
    dfailsModel.probability w =
      (1 / 12 : ℝ) * (Matrix.trace (wordOperator dfailsProj w)).re :=
  c12TraceModel_probability dfailsProj dfailsProj_hermitian dfailsProj_idempotent w

end IsometriesAndProjections

/-! ## Section 3: Overlap Matrices `K_{ij} = V_i† V_j` and `X_{ij} = K_{ij} K_{ji}` -/

section OverlapsAndK

def dfailsK (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (dfailsIsometry i).conjTranspose * dfailsIsometry j

theorem dfailsK_conjTranspose (i j : Fin 4) : (dfailsK i j).conjTranspose = dfailsK j i := by
  unfold dfailsK
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem dfailsK_01 : dfailsK 0 1 = invSqrt2C • 1 := by
  simp [dfailsK, dfailsIsometry, blockCol12_conjTranspose_mul]

theorem dfailsK_02 : dfailsK 0 2 = invSqrt3C • 1 := by
  simp [dfailsK, dfailsIsometry, blockCol12_conjTranspose_mul]

theorem dfailsK_03 : dfailsK 0 3 = invSqrt3C • 1 := by
  simp [dfailsK, dfailsIsometry, blockCol12_conjTranspose_mul]

theorem dfailsK_12 : dfailsK 1 2 = (invSqrt2C * invSqrt3C) • (1 - dfailsC1) := by
  simp only [dfailsK, dfailsIsometry, Matrix.conjTranspose_smul, star_invSqrt2C,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, blockCol12_conjTranspose_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_neg, Matrix.conjTranspose_zero]
  ext a b; simp; ring

theorem dfailsK_13 : dfailsK 1 3 = (invSqrt2C * invSqrt3C) • (1 - dfailsC2) := by
  simp only [dfailsK, dfailsIsometry, Matrix.conjTranspose_smul, star_invSqrt2C,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, blockCol12_conjTranspose_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_neg, Matrix.conjTranspose_zero,
    Matrix.zero_mul]
  ext a b; simp; ring

theorem dfailsK_23 :
    dfailsK 2 3 = (1 / 3 : ℂ) • (1 - dfailsC1 * dfailsC2 - dfailsC3) := by
  simp only [dfailsK, dfailsIsometry, Matrix.conjTranspose_smul, star_invSqrt3C,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, blockCol12_conjTranspose_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.conjTranspose_neg,
    dfailsC1_conjTranspose, neg_neg, Matrix.mul_neg, invSqrt3C_mul_self]
  congr 1

theorem dfailsK_10 : dfailsK 1 0 = invSqrt2C • 1 := by
  rw [← dfailsK_conjTranspose, dfailsK_01, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_invSqrt2C]

theorem dfailsK_20 : dfailsK 2 0 = invSqrt3C • 1 := by
  rw [← dfailsK_conjTranspose, dfailsK_02, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_invSqrt3C]

theorem dfailsK_30 : dfailsK 3 0 = invSqrt3C • 1 := by
  rw [← dfailsK_conjTranspose, dfailsK_03, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_invSqrt3C]

theorem dfailsK_21 : dfailsK 2 1 = (invSqrt2C * invSqrt3C) • (1 + dfailsC1) := by
  rw [← dfailsK_conjTranspose, dfailsK_12, Matrix.conjTranspose_smul, star_mul,
    star_invSqrt2C, star_invSqrt3C, mul_comm invSqrt3C invSqrt2C,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, dfailsC1_conjTranspose, sub_neg_eq_add]

theorem dfailsK_31 : dfailsK 3 1 = (invSqrt2C * invSqrt3C) • (1 + dfailsC2) := by
  rw [← dfailsK_conjTranspose, dfailsK_13, Matrix.conjTranspose_smul, star_mul,
    star_invSqrt2C, star_invSqrt3C, mul_comm invSqrt3C invSqrt2C,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, dfailsC2_conjTranspose, sub_neg_eq_add]

theorem dfailsK_32 :
    dfailsK 3 2 = (1 / 3 : ℂ) • (1 + dfailsC1 * dfailsC2 + dfailsC3) := by
  rw [← dfailsK_conjTranspose, dfailsK_23, Matrix.conjTranspose_smul,
    show star (1 / 3 : ℂ) = (1 / 3 : ℂ) by norm_num,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_mul, dfailsC1_conjTranspose, dfailsC2_conjTranspose,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, dfailsC1_C2_anticomm,
    dfailsC3_conjTranspose, sub_neg_eq_add, sub_neg_eq_add]

theorem dfailsK_diag (i : Fin 4) : dfailsK i i = 1 :=
  dfailsIsometry_isometry i

def dfailsX (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  dfailsK i j * dfailsK j i

theorem dfailsX_23 : dfailsX 2 3 = (1 / 9 : ℂ) • ((3 : ℂ) • 1 - (2 : ℂ) • dfailsJ) := by
  unfold dfailsX
  rw [dfailsK_23, dfailsK_32, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hc : (1 / 3 : ℂ) * (1 / 3 : ℂ) = 1 / 9 := by norm_num
  rw [hc]
  congr 1
  have hC12sq : dfailsC1 * dfailsC2 * (dfailsC1 * dfailsC2) = -1 := by
    calc
      dfailsC1 * dfailsC2 * (dfailsC1 * dfailsC2) =
          dfailsC1 * (dfailsC2 * dfailsC1) * dfailsC2 := by simp only [Matrix.mul_assoc]
      _ = -(dfailsC1 * dfailsC1 * (dfailsC2 * dfailsC2)) := by
        rw [dfailsC1_C2_anticomm]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -1 := by rw [dfailsC1_sq, dfailsC2_sq, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
        Matrix.mul_one]
  have h123 : dfailsC1 * dfailsC2 * dfailsC3 = dfailsJ := dfailsC1_C2_C3
  have h312 : dfailsC3 * (dfailsC1 * dfailsC2) = dfailsJ := by
    calc
      dfailsC3 * (dfailsC1 * dfailsC2) = (dfailsC3 * dfailsC1) * dfailsC2 := by
        simp only [Matrix.mul_assoc]
      _ = -(dfailsC1 * (dfailsC3 * dfailsC2)) := by
        rw [dfailsC1_C3_anticomm]; simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = dfailsC1 * dfailsC2 * dfailsC3 := by
        rw [dfailsC2_C3_anticomm, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
      _ = dfailsJ := dfailsC1_C2_C3
  calc
    (1 - dfailsC1 * dfailsC2 - dfailsC3) * (1 + dfailsC1 * dfailsC2 + dfailsC3)
        = 1 - (dfailsC1 * dfailsC2 * (dfailsC1 * dfailsC2) +
            dfailsC1 * dfailsC2 * dfailsC3 + dfailsC3 * (dfailsC1 * dfailsC2) +
            dfailsC3 * dfailsC3) := by noncomm_ring
    _ = 1 - (-1 + dfailsJ + dfailsJ + -1) := by rw [hC12sq, h123, h312, dfailsC3_sq]
    _ = (3 : ℂ) • 1 - (2 : ℂ) • dfailsJ := by
      ext a b; simp; ring

theorem dfailsX_32 : dfailsX 3 2 = (1 / 9 : ℂ) • ((3 : ℂ) • 1 - (2 : ℂ) • dfailsJ) := by
  unfold dfailsX
  rw [dfailsK_32, dfailsK_23, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hc : (1 / 3 : ℂ) * (1 / 3 : ℂ) = 1 / 9 := by norm_num
  rw [hc]
  congr 1
  have hC12sq : dfailsC1 * dfailsC2 * (dfailsC1 * dfailsC2) = -1 := by
    calc
      dfailsC1 * dfailsC2 * (dfailsC1 * dfailsC2) =
          dfailsC1 * (dfailsC2 * dfailsC1) * dfailsC2 := by simp only [Matrix.mul_assoc]
      _ = -(dfailsC1 * dfailsC1 * (dfailsC2 * dfailsC2)) := by
        rw [dfailsC1_C2_anticomm]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -1 := by rw [dfailsC1_sq, dfailsC2_sq, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
        Matrix.mul_one]
  have h312 : dfailsC3 * (dfailsC1 * dfailsC2) = dfailsJ := by
    calc
      dfailsC3 * (dfailsC1 * dfailsC2) = (dfailsC3 * dfailsC1) * dfailsC2 := by
        simp only [Matrix.mul_assoc]
      _ = -(dfailsC1 * (dfailsC3 * dfailsC2)) := by
        rw [dfailsC1_C3_anticomm]; simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = dfailsC1 * dfailsC2 * dfailsC3 := by
        rw [dfailsC2_C3_anticomm, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
      _ = dfailsJ := dfailsC1_C2_C3
  calc
    (1 + dfailsC1 * dfailsC2 + dfailsC3) * (1 - dfailsC1 * dfailsC2 - dfailsC3)
        = 1 - (dfailsC1 * dfailsC2 * (dfailsC1 * dfailsC2) +
            dfailsC1 * dfailsC2 * dfailsC3 + dfailsC3 * (dfailsC1 * dfailsC2) +
            dfailsC3 * dfailsC3) := by noncomm_ring
    _ = 1 - (-1 + dfailsJ + dfailsJ + -1) := by rw [hC12sq, dfailsC1_C2_C3, h312, dfailsC3_sq]
    _ = (3 : ℂ) • 1 - (2 : ℂ) • dfailsJ := by
      ext a b; simp; ring

theorem dfailsX_other (i j : Fin 4)
    (h : ¬ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2))) :
    dfailsX i j = (nativeOverlaps fixedS i j : ℂ) • 1 := by
  have hs23 : (invSqrt2C * invSqrt3C) * (invSqrt2C * invSqrt3C) = (1 / 6 : ℂ) := by
    calc
      (invSqrt2C * invSqrt3C) * (invSqrt2C * invSqrt3C) =
          (invSqrt2C * invSqrt2C) * (invSqrt3C * invSqrt3C) := by ring
      _ = (1 / 2 : ℂ) * (1 / 3 : ℂ) := by
        rw [invSqrt2C_mul_self, invSqrt3C_mul_self]
      _ = 1 / 6 := by norm_num
  rw [nativeOverlaps_fixedS_eq]
  fin_cases i <;> fin_cases j <;> dsimp <;> simp only [dfailsX]
  · simp [dfailsK_diag]
  · rw [dfailsK_01, dfailsK_10, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      invSqrt2C_mul_self, Matrix.one_mul]
    congr 1; push_cast; norm_num
  · rw [dfailsK_02, dfailsK_20, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      invSqrt3C_mul_self, Matrix.one_mul]
    congr 1; push_cast; norm_num
  · rw [dfailsK_03, dfailsK_30, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      invSqrt3C_mul_self, Matrix.one_mul]
    congr 1; push_cast; norm_num
  · rw [dfailsK_10, dfailsK_01, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      invSqrt2C_mul_self, Matrix.one_mul]
    congr 1; push_cast; norm_num
  · simp [dfailsK_diag]
  · rw [dfailsK_12, dfailsK_21, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs23]
    have hm : (1 - dfailsC1) * (1 + dfailsC1) = (2 : ℂ) • 1 := by
      calc
        (1 - dfailsC1) * (1 + dfailsC1) = 1 - dfailsC1 * dfailsC1 := by noncomm_ring
        _ = (2 : ℂ) • 1 := by rw [dfailsC1_sq]; ext a b; simp; ring
    rw [hm, smul_smul]
    congr 1; push_cast; norm_num
  · rw [dfailsK_13, dfailsK_31, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs23]
    have hm : (1 - dfailsC2) * (1 + dfailsC2) = (2 : ℂ) • 1 := by
      calc
        (1 - dfailsC2) * (1 + dfailsC2) = 1 - dfailsC2 * dfailsC2 := by noncomm_ring
        _ = (2 : ℂ) • 1 := by rw [dfailsC2_sq]; ext a b; simp; ring
    rw [hm, smul_smul]
    congr 1; push_cast; norm_num
  · rw [dfailsK_20, dfailsK_02, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      invSqrt3C_mul_self, Matrix.one_mul]
    congr 1; push_cast; norm_num
  · rw [dfailsK_21, dfailsK_12, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs23]
    have hm : (1 + dfailsC1) * (1 - dfailsC1) = (2 : ℂ) • 1 := by
      calc
        (1 + dfailsC1) * (1 - dfailsC1) = 1 - dfailsC1 * dfailsC1 := by noncomm_ring
        _ = (2 : ℂ) • 1 := by rw [dfailsC1_sq]; ext a b; simp; ring
    rw [hm, smul_smul]
    congr 1; push_cast; norm_num
  · simp [dfailsK_diag]
  · exact absurd (Or.inl ⟨rfl, rfl⟩) h
  · rw [dfailsK_30, dfailsK_03, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      invSqrt3C_mul_self, Matrix.one_mul]
    congr 1; push_cast; norm_num
  · rw [dfailsK_31, dfailsK_13, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs23]
    have hm : (1 + dfailsC2) * (1 - dfailsC2) = (2 : ℂ) • 1 := by
      calc
        (1 + dfailsC2) * (1 - dfailsC2) = 1 - dfailsC2 * dfailsC2 := by noncomm_ring
        _ = (2 : ℂ) • 1 := by rw [dfailsC2_sq]; ext a b; simp; ring
    rw [hm, smul_smul]
    congr 1; push_cast; norm_num
  · exact absurd (Or.inr ⟨rfl, rfl⟩) h
  · simp [dfailsK_diag]

theorem dfailsX_trace (i j : Fin 4) :
    Matrix.trace (dfailsX i j) = (4 : ℂ) * (nativeOverlaps fixedS i j : ℂ) := by
  by_cases h : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [dfailsX_23, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_smul, dfailsJ_trace, smul_zero, sub_zero, Matrix.trace_one,
        Fintype.card_fin]
      rw [nativeOverlaps_fixedS_eq]
      simp only [Fin.reduceEq, ↓reduceIte, Fin.isValue, and_self, or_self]
      push_cast; ring
    · rw [dfailsX_32, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_smul, dfailsJ_trace, smul_zero, sub_zero, Matrix.trace_one,
        Fintype.card_fin]
      rw [nativeOverlaps_fixedS_eq]
      simp only [Fin.reduceEq, ↓reduceIte, Fin.isValue, and_self, or_self]
      push_cast; ring
  · rw [dfailsX_other i j h, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul, mul_comm]
    norm_cast

theorem dfailsX_mul_trace_cd :
    Matrix.trace (dfailsX 3 2 * dfailsX 3 2) = (52 / 81 : ℂ) ∧
    Matrix.trace (dfailsX 2 3 * dfailsX 2 3) = (52 / 81 : ℂ) := by
  have hsq : ((3 : ℂ) • 1 - (2 : ℂ) • dfailsJ) * ((3 : ℂ) • 1 - (2 : ℂ) • dfailsJ) =
      (13 : ℂ) • 1 - (12 : ℂ) • dfailsJ := by
    calc
      ((3 : ℂ) • 1 - (2 : ℂ) • dfailsJ) * ((3 : ℂ) • 1 - (2 : ℂ) • dfailsJ) =
          (9 : ℂ) • 1 - (12 : ℂ) • dfailsJ + (4 : ℂ) • (dfailsJ * dfailsJ) := by
        ext a b; simp [Matrix.sub_mul, Matrix.mul_sub]; ring
      _ = (13 : ℂ) • 1 - (12 : ℂ) • dfailsJ := by
        rw [dfailsJ_sq]; ext a b; simp; ring
  have htr : Matrix.trace ((1 / 9 : ℂ) • ((3 : ℂ) • 1 - (2 : ℂ) • dfailsJ) *
      ((1 / 9 : ℂ) • ((3 : ℂ) • 1 - (2 : ℂ) • dfailsJ))) = (52 / 81 : ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, Matrix.trace_smul,
      Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, dfailsJ_trace,
      smul_zero, sub_zero, Matrix.trace_one, Fintype.card_fin]
    norm_num
  exact ⟨by rw [dfailsX_32]; exact htr, by rw [dfailsX_23]; exact htr⟩

theorem dfailsX_mul_trace_re (i j k : Fin 4) :
    (1 / 4 : ℝ) * (Matrix.trace (dfailsX j i * dfailsX j k)).re =
      if (i = 2 ∧ j = 3 ∧ k = 2) ∨ (i = 3 ∧ j = 2 ∧ k = 3) then (13 / 81 : ℝ)
      else nativeOverlaps fixedS i j * nativeOverlaps fixedS j k := by
  by_cases hcdc : (i = 2 ∧ j = 3 ∧ k = 2) ∨ (i = 3 ∧ j = 2 ∧ k = 3)
  · simp only [hcdc, ↓reduceIte]
    rcases hcdc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [dfailsX_mul_trace_cd.1]; norm_num
    · rw [dfailsX_mul_trace_cd.2]; norm_num
  · simp only [hcdc, ↓reduceIte]
    by_cases hij : (j = 2 ∧ i = 3) ∨ (j = 3 ∧ i = 2)
    · have hjk : ¬ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2)) := by
        intro hk
        apply hcdc
        rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
        · exact Or.inr ⟨rfl, rfl, rfl⟩
        · simp at h1
        · simp at h1
        · exact Or.inl ⟨rfl, rfl, rfl⟩
      rw [dfailsX_other j k hjk, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
        dfailsX_trace j i, smul_eq_mul]
      have ho_symm : nativeOverlaps fixedS j i = nativeOverlaps fixedS i j :=
        fixedS_overlap_symmetric j i
      rw [ho_symm]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, mul_zero]
      ring
    · rw [dfailsX_other j i hij, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
        dfailsX_trace j k, smul_eq_mul]
      have ho_symm : nativeOverlaps fixedS j i = nativeOverlaps fixedS i j :=
        fixedS_overlap_symmetric j i
      rw [ho_symm]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, mul_zero]
      ring

end OverlapsAndK

/-! ## Section 4: Endpoint Complementation and Length `≤ 2` Agreement -/

section LengthTwo

theorem dfails_prob_append_false (w : Word (Fin 4)) (i : Fin 4) :
    dfailsModel.probability (w ++ [(i, false)]) =
      dfailsModel.probability w - dfailsModel.probability (w ++ [(i, true)]) := by
  rw [dfailsModel_probability, dfailsModel_probability, dfailsModel_probability]
  have hsplit := wordOperator_terminal_split dfailsProj dfailsProj_idempotent
    (fun j => (dfailsProj_hermitian j).eq) w i
  have htr : Matrix.trace (wordOperator dfailsProj (w ++ [(i, false)])) =
      Matrix.trace (wordOperator dfailsProj w) -
        Matrix.trace (wordOperator dfailsProj (w ++ [(i, true)])) := by
    rw [← hsplit, Matrix.trace_add]
    ring
  rw [htr, Complex.sub_re]
  ring

theorem dfails_prob_cons_false (i : Fin 4) (w : Word (Fin 4)) :
    dfailsModel.probability ((i, false) :: w) =
      dfailsModel.probability w - dfailsModel.probability ((i, true) :: w) := by
  rw [dfailsModel_probability, dfailsModel_probability, dfailsModel_probability]
  have htr_split : Matrix.trace (wordOperator dfailsProj ((i, true) :: w)) +
      Matrix.trace (wordOperator dfailsProj ((i, false) :: w)) =
      Matrix.trace (wordOperator dfailsProj w) := by
    have hstar : ∀ j, star (dfailsProj j) = dfailsProj j := fun j => (dfailsProj_hermitian j).eq
    rw [wordOperator_cons dfailsProj hstar (i, true) w,
      wordOperator_cons dfailsProj hstar (i, false) w]
    simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte]
    have h1 : Matrix.trace (dfailsProj i * wordOperator dfailsProj w * dfailsProj i) =
        Matrix.trace (dfailsProj i * wordOperator dfailsProj w) := by
      rw [Matrix.trace_mul_cycle, dfailsProj_idempotent]
    have h0 : Matrix.trace ((1 - dfailsProj i) * wordOperator dfailsProj w * (1 - dfailsProj i)) =
        Matrix.trace ((1 - dfailsProj i) * wordOperator dfailsProj w) := by
      have hid : (1 - dfailsProj i) * (1 - dfailsProj i) = 1 - dfailsProj i := by
        noncomm_ring [dfailsProj_idempotent i]
      rw [Matrix.trace_mul_cycle, hid]
    rw [h1, h0, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
    ring
  have htr : Matrix.trace (wordOperator dfailsProj ((i, false) :: w)) =
      Matrix.trace (wordOperator dfailsProj w) -
        Matrix.trace (wordOperator dfailsProj ((i, true) :: w)) := by
    rw [← htr_split]
    ring
  rw [htr, Complex.sub_re]
  ring

private theorem nativeBranchState_linear_add {ι : Type*} (p : ι → Albert)
    (ρ₁ ρ₂ : Albert) (w : Word ι) :
    nativeBranchState p (ρ₁ + ρ₂) w =
      nativeBranchState p ρ₁ w + nativeBranchState p ρ₂ w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [nativeBranchState_append, nativeBranchState_append, nativeBranchState_append]
    change quadraticMap (nativeOutcome p a) (nativeBranchState p (ρ₁ + ρ₂) w) =
      quadraticMap (nativeOutcome p a) (nativeBranchState p ρ₁ w) +
        quadraticMap (nativeOutcome p a) (nativeBranchState p ρ₂ w)
    rw [ih, quadraticMap_add_right]

private theorem tracePairing_albertUnit_left (x : Albert) :
    tracePairing albertUnit x = albertTrace x := by
  unfold tracePairing
  rw [jordanMul_albertUnit_left]

private theorem tracePairing_albertUnit_right (x : Albert) :
    tracePairing x albertUnit = albertTrace x := by
  unfold tracePairing
  rw [jordanMul_albertUnit_right]

private theorem fixedS_quadratic_e3 (i : Fin 4) :
    quadraticMap (fixedS i) ((1 / 3 : ℝ) • albertUnit) = (1 / 3 : ℝ) • fixedS i := by
  rw [quadraticMap_smul_right, quadraticMap_atom _ _ (fixedS_isAtom i),
    tracePairing_albertUnit_right, (fixedS_isAtom i).2, one_smul]

private theorem fixedS_quadratic_comp_e3 (i : Fin 4) :
    quadraticMap (albertUnit - fixedS i) ((1 / 3 : ℝ) • albertUnit) =
      (1 / 3 : ℝ) • (albertUnit - fixedS i) := by
  rw [quadraticMap_smul_right]
  congr 1
  unfold quadraticMap
  simp only [jordanMul_sub_left, jordanMul_sub_right,
    jordanMul_albertUnit_left, jordanMul_albertUnit_right, (fixedS_isAtom i).1]
  simp only [two_smul]
  abel

private theorem fixedS_quadratic_atom (i j : Fin 4) :
    quadraticMap (fixedS j) (fixedS i) = nativeOverlaps fixedS i j • fixedS j := by
  rw [quadraticMap_atom _ _ (fixedS_isAtom j)]
  congr 1
  exact fixedS_overlap_symmetric j i

theorem fixedS_prob_append_false (w : Word (Fin 4)) (i : Fin 4) :
    nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) (w ++ [(i, false)]) =
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w -
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) (w ++ [(i, true)]) := by
  have hsum : nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) (w ++ [(i, true)]) +
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) (w ++ [(i, false)]) =
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w := by
    unfold nativeWordProbability
    rw [nativeBranchState_append, nativeBranchState_append]
    unfold nativeBranchState
    simp only [List.foldl_cons, List.foldl_nil, nativeOutcome, Bool.false_eq_true, ↓reduceIte]
    let x := nativeBranchState fixedS ((1 / 3 : ℝ) • albertUnit) w
    change albertTrace (quadraticMap (fixedS i) x) +
        albertTrace (quadraticMap (albertUnit - fixedS i) x) = albertTrace x
    have htr1 : albertTrace (quadraticMap (fixedS i) x) = tracePairing (fixedS i) x := by
      rw [NativeAnalysis.albertTrace_quadraticMap, (fixedS_isAtom i).1]
    have htr0 : albertTrace (quadraticMap (albertUnit - fixedS i) x) =
        tracePairing (albertUnit - fixedS i) x := by
      have hid : jordanMul (albertUnit - fixedS i) (albertUnit - fixedS i) =
          albertUnit - fixedS i := by
        simp only [jordanMul_sub_left, jordanMul_sub_right,
          jordanMul_albertUnit_left, jordanMul_albertUnit_right, (fixedS_isAtom i).1]
        abel
      rw [NativeAnalysis.albertTrace_quadraticMap, hid]
    rw [htr1, htr0, tracePairing_sub_left, tracePairing_albertUnit_left]
    ring
  linarith

theorem fixedS_prob_cons_false (i : Fin 4) (w : Word (Fin 4)) :
    nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) ((i, false) :: w) =
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w -
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) ((i, true) :: w) := by
  have hsum : nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) ((i, true) :: w) +
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) ((i, false) :: w) =
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w := by
    unfold nativeWordProbability
    change albertTrace (nativeBranchState fixedS
        (quadraticMap (fixedS i) ((1 / 3 : ℝ) • albertUnit)) w) +
      albertTrace (nativeBranchState fixedS
        (quadraticMap (albertUnit - fixedS i) ((1 / 3 : ℝ) • albertUnit)) w) =
      albertTrace (nativeBranchState fixedS ((1 / 3 : ℝ) • albertUnit) w)
    rw [fixedS_quadratic_e3, fixedS_quadratic_comp_e3, ← albertTrace_add,
      ← nativeBranchState_linear_add, ← smul_add, add_sub_cancel]
  linarith

theorem dfailsModel_prob_nil : dfailsModel.probability [] = 1 := by
  rw [dfailsModel_probability, wordOperator_nil, Matrix.trace_one, Fintype.card_fin]
  norm_num

theorem fixedS_prob_nil :
    nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [] = 1 := by
  unfold nativeWordProbability nativeBranchState
  rw [List.foldl_nil, albertTrace_smul, native_trace_unit]
  norm_num

theorem dfailsModel_prob_single_true (i : Fin 4) :
    dfailsModel.probability [(i, true)] = 1 / 3 := by
  rw [dfailsModel_probability, wordOperator_singleton dfailsProj dfailsProj_idempotent
    (fun j => (dfailsProj_hermitian j).eq)]
  simp only [algebraicOutcome, ↓reduceIte, dfailsProj_trace]
  norm_num

theorem fixedS_prob_single_true (i : Fin 4) :
    nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true)] = 1 / 3 := by
  unfold nativeWordProbability nativeBranchState
  simp only [List.foldl_cons, List.foldl_nil, nativeOutcome, ↓reduceIte]
  rw [fixedS_quadratic_e3, albertTrace_smul, (fixedS_isAtom i).2]
  norm_num

theorem dfailsModel_prob_two_true (i j : Fin 4) :
    dfailsModel.probability [(i, true), (j, true)] = (1 / 3 : ℝ) * nativeOverlaps fixedS i j := by
  rw [dfailsModel_probability, wordOperator_cons dfailsProj (fun k => (dfailsProj_hermitian k).eq),
    wordOperator_singleton dfailsProj dfailsProj_idempotent (fun k => (dfailsProj_hermitian k).eq)]
  simp only [algebraicOutcome, ↓reduceIte]
  have htr : Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj i) =
      Matrix.trace (dfailsX i j) := by
    unfold dfailsProj dfailsX dfailsK
    calc
      Matrix.trace ((dfailsIsometry i * (dfailsIsometry i).conjTranspose) *
          (dfailsIsometry j * (dfailsIsometry j).conjTranspose) *
          (dfailsIsometry i * (dfailsIsometry i).conjTranspose))
          = Matrix.trace ((dfailsIsometry i *
              ((dfailsIsometry i).conjTranspose * dfailsIsometry j *
                ((dfailsIsometry j).conjTranspose * dfailsIsometry i))) *
              (dfailsIsometry i).conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((dfailsIsometry i).conjTranspose *
            (dfailsIsometry i *
              ((dfailsIsometry i).conjTranspose * dfailsIsometry j *
                ((dfailsIsometry j).conjTranspose * dfailsIsometry i)))) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (((dfailsIsometry i).conjTranspose * dfailsIsometry i) *
            ((dfailsIsometry i).conjTranspose * dfailsIsometry j *
              ((dfailsIsometry j).conjTranspose * dfailsIsometry i))) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((dfailsIsometry i).conjTranspose * dfailsIsometry j *
            ((dfailsIsometry j).conjTranspose * dfailsIsometry i)) := by
        rw [dfailsIsometry_isometry i, Matrix.one_mul]
  rw [htr, dfailsX_trace]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, sub_zero, mul_zero]
  ring

theorem fixedS_prob_two_true (i j : Fin 4) :
    nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, true)] =
      (1 / 3 : ℝ) * nativeOverlaps fixedS i j := by
  unfold nativeWordProbability nativeBranchState
  simp only [List.foldl_cons, List.foldl_nil, nativeOutcome, ↓reduceIte]
  rw [fixedS_quadratic_e3, quadraticMap_smul_right, fixedS_quadratic_atom,
    smul_smul, albertTrace_smul, (fixedS_isAtom j).2, mul_one]

theorem dfails_length_le_two (w : Word (Fin 4)) (hw : w.length ≤ 2) :
    dfailsModel.probability w = nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w := by
  rcases w with _ | ⟨⟨i, b₀⟩, w₁⟩
  · rw [dfailsModel_prob_nil, fixedS_prob_nil]
  · rcases w₁ with _ | ⟨⟨j, b₁⟩, w₂⟩
    · cases b₀
      · rw [dfails_prob_cons_false, fixedS_prob_cons_false, dfailsModel_prob_nil, fixedS_prob_nil,
          dfailsModel_prob_single_true, fixedS_prob_single_true]
      · exact (dfailsModel_prob_single_true i).trans (fixedS_prob_single_true i).symm
    · have hw2 : w₂ = [] := by
        simp only [List.length_cons] at hw
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hw2
      cases b₀ <;> cases b₁
      · change dfailsModel.probability ((i, false) :: [(j, false)]) = _
        rw [dfails_prob_cons_false, fixedS_prob_cons_false]
        have h1 : dfailsModel.probability [(j, false)] =
            nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(j, false)] := by
          rw [dfails_prob_cons_false, fixedS_prob_cons_false, dfailsModel_prob_nil,
            fixedS_prob_nil, dfailsModel_prob_single_true, fixedS_prob_single_true]
        have h2 : dfailsModel.probability [(i, true), (j, false)] =
            nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, false)] := by
          change dfailsModel.probability ([(i, true)] ++ [(j, false)]) =
            nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) ([(i, true)] ++ [(j, false)])
          rw [dfails_prob_append_false, fixedS_prob_append_false, dfailsModel_prob_single_true,
            fixedS_prob_single_true]
          simp only [List.singleton_append]
          rw [dfailsModel_prob_two_true, fixedS_prob_two_true]
        rw [h1, h2]
      · change dfailsModel.probability ((i, false) :: [(j, true)]) = _
        rw [dfails_prob_cons_false, fixedS_prob_cons_false, dfailsModel_prob_single_true,
          fixedS_prob_single_true, dfailsModel_prob_two_true, fixedS_prob_two_true]
      · change dfailsModel.probability ([(i, true)] ++ [(j, false)]) =
          nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) ([(i, true)] ++ [(j, false)])
        rw [dfails_prob_append_false, fixedS_prob_append_false, dfailsModel_prob_single_true,
          fixedS_prob_single_true]
        simp only [List.singleton_append]
        rw [dfailsModel_prob_two_true, fixedS_prob_two_true]
      · exact (dfailsModel_prob_two_true i j).trans (fixedS_prob_two_true i j).symm

end LengthTwo

/-! ## Section 5: Thirteen Traces Extracted from Words of Length `≤ 4` and `D_tet = 1/12` -/

section ThirteenTraces

def wordExtractOverlap (prob : Word (Fin 4) → ℝ) (i j : Fin 4) : ℝ :=
  3 * prob [(i, true), (j, true)]

def wordExtractTriangle (prob : Word (Fin 4) → ℝ) (i j k : Fin 4) : ℝ :=
  (3 / 2 : ℝ) * (prob [(i, true), (k, true)] +
    prob [(i, true), (j, true), (k, true)] -
    prob [(i, true), (j, false), (k, true)])

def wordExtractDoublePair (prob : Word (Fin 4) → ℝ) (a b c d : Fin 4) : ℝ :=
  let mid (x : Fin 4) : List (ℝ × Word (Fin 4)) :=
    [(1, []), (1, [(x, true)]), (-1, [(x, false)])]
  (3 / 4 : ℝ) *
    ((mid b).map (fun sb =>
      ((mid c).map (fun tc =>
        sb.1 * tc.1 * prob ([(a, true)] ++ sb.2 ++ tc.2 ++ [(d, true)]))).sum)).sum

theorem trace_dfailsProj_two_re (i j : Fin 4) :
    (Matrix.trace (dfailsProj i * dfailsProj j)).re = 4 * nativeOverlaps fixedS i j := by
  have htr : Matrix.trace (dfailsProj i * dfailsProj j) = Matrix.trace (dfailsX i j) := by
    unfold dfailsProj dfailsX dfailsK
    calc
      Matrix.trace ((dfailsIsometry i * (dfailsIsometry i).conjTranspose) *
          (dfailsIsometry j * (dfailsIsometry j).conjTranspose))
          = Matrix.trace ((dfailsIsometry i *
              ((dfailsIsometry i).conjTranspose * dfailsIsometry j *
                (dfailsIsometry j).conjTranspose))) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((dfailsIsometry i).conjTranspose * dfailsIsometry j *
              (dfailsIsometry j).conjTranspose) * dfailsIsometry i) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((dfailsIsometry i).conjTranspose * dfailsIsometry j *
            ((dfailsIsometry j).conjTranspose * dfailsIsometry i)) := by
        simp only [Matrix.mul_assoc]
  rw [htr, dfailsX_trace]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, sub_zero, mul_zero]

theorem trace_dfailsProj_three_eq_K (i j k : Fin 4) :
    Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj k) =
      Matrix.trace (dfailsK i j * dfailsK j k * dfailsK k i) := by
  unfold dfailsProj dfailsK
  calc
    Matrix.trace ((dfailsIsometry i * (dfailsIsometry i).conjTranspose) *
        (dfailsIsometry j * (dfailsIsometry j).conjTranspose) *
        (dfailsIsometry k * (dfailsIsometry k).conjTranspose))
        = Matrix.trace (dfailsIsometry i *
            ((dfailsIsometry i).conjTranspose * dfailsIsometry j *
              ((dfailsIsometry j).conjTranspose * dfailsIsometry k) *
              (dfailsIsometry k).conjTranspose)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((dfailsIsometry i).conjTranspose * dfailsIsometry j *
            ((dfailsIsometry j).conjTranspose * dfailsIsometry k) *
            (dfailsIsometry k).conjTranspose) * dfailsIsometry i) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((dfailsIsometry i).conjTranspose * dfailsIsometry j) *
          ((dfailsIsometry j).conjTranspose * dfailsIsometry k) *
          ((dfailsIsometry k).conjTranspose * dfailsIsometry i)) := by
      simp only [Matrix.mul_assoc]

theorem trace_dfailsProj_three_re_swap12 (i j k : Fin 4) :
    (Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj k)).re =
      (Matrix.trace (dfailsProj j * dfailsProj i * dfailsProj k)).re := by
  have hconj : (dfailsProj i * dfailsProj j * dfailsProj k).conjTranspose =
      dfailsProj k * dfailsProj j * dfailsProj i := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      (dfailsProj_hermitian i).eq, (dfailsProj_hermitian j).eq, (dfailsProj_hermitian k).eq,
      Matrix.mul_assoc]
  have htr : Matrix.trace (dfailsProj k * dfailsProj j * dfailsProj i) =
      star (Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj k)) := by
    rw [← hconj, Matrix.trace_conjTranspose]
  rw [Matrix.trace_mul_cycle (dfailsProj j) (dfailsProj i) (dfailsProj k)]
  have hre := congrArg Complex.re htr
  simpa [Complex.star_def, Complex.conj_re] using hre.symm

theorem trace_dfailsProj_three_re_cycle (i j k : Fin 4) :
    (Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj k)).re =
      (Matrix.trace (dfailsProj j * dfailsProj k * dfailsProj i)).re := by
  rw [Matrix.mul_assoc (dfailsProj i), Matrix.trace_mul_comm]

theorem trace_dfailsProj_three_re_012 :
    (Matrix.trace (dfailsProj 0 * dfailsProj 1 * dfailsProj 2)).re = 2 / 3 := by
  rw [trace_dfailsProj_three_eq_K, dfailsK_01, dfailsK_12, dfailsK_20]
  have hs : invSqrt3C * (invSqrt2C * invSqrt3C * invSqrt2C) = (1 / 6 : ℂ) := by
    calc
      invSqrt3C * (invSqrt2C * invSqrt3C * invSqrt2C) =
          (invSqrt2C * invSqrt2C) * (invSqrt3C * invSqrt3C) := by ring
      _ = (1 / 2 : ℂ) * (1 / 3 : ℂ) := by rw [invSqrt2C_mul_self, invSqrt3C_mul_self]
      _ = 1 / 6 := by norm_num
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [hs, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin,
    dfailsC1_trace, sub_zero]
  norm_num

theorem trace_dfailsProj_three_re_013 :
    (Matrix.trace (dfailsProj 0 * dfailsProj 1 * dfailsProj 3)).re = 2 / 3 := by
  rw [trace_dfailsProj_three_eq_K, dfailsK_01, dfailsK_13, dfailsK_30]
  have hs : invSqrt3C * (invSqrt2C * invSqrt3C * invSqrt2C) = (1 / 6 : ℂ) := by
    calc
      invSqrt3C * (invSqrt2C * invSqrt3C * invSqrt2C) =
          (invSqrt2C * invSqrt2C) * (invSqrt3C * invSqrt3C) := by ring
      _ = (1 / 2 : ℂ) * (1 / 3 : ℂ) := by rw [invSqrt2C_mul_self, invSqrt3C_mul_self]
      _ = 1 / 6 := by norm_num
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [hs, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin,
    dfailsC2_trace, sub_zero]
  norm_num

theorem trace_dfailsProj_three_re_023 :
    (Matrix.trace (dfailsProj 0 * dfailsProj 2 * dfailsProj 3)).re = 4 / 9 := by
  rw [trace_dfailsProj_three_eq_K, dfailsK_02, dfailsK_23, dfailsK_30]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [show invSqrt3C * ((1 / 3 : ℂ) * invSqrt3C) = (1 / 9 : ℂ) by
    rw [mul_left_comm, invSqrt3C_mul_self]; norm_num,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin,
    dfailsC1C2_trace, dfailsC3_trace, sub_zero, sub_zero]
  norm_num

theorem trace_dfailsProj_three_re_123 :
    (Matrix.trace (dfailsProj 1 * dfailsProj 2 * dfailsProj 3)).re = 4 / 9 := by
  rw [trace_dfailsProj_three_eq_K, dfailsK_12, dfailsK_23, dfailsK_31]
  have hs : (invSqrt2C * invSqrt3C) * ((1 / 3 : ℂ) * (invSqrt2C * invSqrt3C)) = (1 / 18 : ℂ) := by
    calc
      (invSqrt2C * invSqrt3C) * ((1 / 3 : ℂ) * (invSqrt2C * invSqrt3C)) =
          (1 / 3 : ℂ) * ((invSqrt2C * invSqrt2C) * (invSqrt3C * invSqrt3C)) := by ring
      _ = (1 / 3 : ℂ) * ((1 / 2 : ℂ) * (1 / 3 : ℂ)) := by
        rw [invSqrt2C_mul_self, invSqrt3C_mul_self]
      _ = 1 / 18 := by norm_num
  have hnum : (1 - dfailsC1) * (1 - dfailsC1 * dfailsC2 - dfailsC3) * (1 + dfailsC2) =
      (2 : ℂ) • 1 - dfailsJ - (2 : ℂ) • (dfailsC1 * dfailsC2) - dfailsC3 +
        dfailsC1 * dfailsC3 + dfailsC2 * dfailsC3 := by
    have hstep1 : (1 - dfailsC1) * (1 - dfailsC1 * dfailsC2 - dfailsC3) =
        1 - dfailsC1 - dfailsC1 * dfailsC2 - dfailsC2 - dfailsC3 + dfailsC1 * dfailsC3 := by
      have h1 : (1 - dfailsC1) * (1 - dfailsC1 * dfailsC2 - dfailsC3) =
          1 - dfailsC1 - dfailsC1 * dfailsC2 + dfailsC1 * dfailsC1 * dfailsC2 -
            dfailsC3 + dfailsC1 * dfailsC3 := by noncomm_ring
      rw [h1, dfailsC1_sq]
      noncomm_ring
    rw [hstep1]
    have h2 : (1 - dfailsC1 - dfailsC1 * dfailsC2 - dfailsC2 - dfailsC3 + dfailsC1 * dfailsC3) *
          (1 + dfailsC2) =
        1 - dfailsC1 - dfailsC1 * dfailsC2 - dfailsC2 - dfailsC3 + dfailsC1 * dfailsC3 +
          dfailsC2 - dfailsC1 * dfailsC2 - dfailsC1 * (dfailsC2 * dfailsC2) -
          dfailsC2 * dfailsC2 - dfailsC3 * dfailsC2 + dfailsC1 * (dfailsC3 * dfailsC2) := by
      noncomm_ring
    rw [h2, dfailsC2_sq, dfailsC2_C3_anticomm]
    simp only [Matrix.mul_neg, Matrix.mul_one]
    rw [← Matrix.mul_assoc, dfailsC1_C2_C3]
    ext a b; simp; ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hs, hnum, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, dfailsJ_trace, dfailsC1C2_trace, dfailsC3_trace,
    dfailsC1C3_trace, dfailsC2C3_trace]
  norm_num

private theorem fixedSTriangleVal_distinct (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    fixedSTriangleVal i j k = if i.val + j.val + k.val ≤ 4 then 1 / 6 else 1 / 9 := by
  simp [fixedSTriangleVal, hij, hik, hjk]

theorem trace_dfailsProj_three_re (i j k : Fin 4) :
    (Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj k)).re = 4 * fpTriangle fixedS i j k := by
  rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]
  by_cases hij : i = j
  · subst hij
    rw [dfailsProj_idempotent, trace_dfailsProj_two_re, fixedSTriangleVal]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, and_self, nativeOverlaps_fixedS_eq]
    · simp only [hik, ↓reduceIte, and_false]
  · by_cases hik : i = k
    · subst hik
      rw [Matrix.trace_mul_cycle, dfailsProj_idempotent,
        trace_dfailsProj_two_re, fixedSTriangleVal]
      simp only [hij, ↓reduceIte, false_and]
    · by_cases hjk : j = k
      · subst hjk
        rw [Matrix.mul_assoc, dfailsProj_idempotent, trace_dfailsProj_two_re,
          fixedSTriangleVal]
        simp only [hij, ↓reduceIte, false_and, fixedS_overlap_symmetric]
      · rw [fixedSTriangleVal_distinct i j k hij hik hjk]
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          (try exact absurd rfl hij) <;>
          (try exact absurd rfl hik) <;>
          (try exact absurd rfl hjk) <;>
          dsimp
        · rw [trace_dfailsProj_three_re_012]; norm_num
        · rw [trace_dfailsProj_three_re_013]; norm_num
        · rw [trace_dfailsProj_three_re_swap12,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_012]; norm_num
        · rw [trace_dfailsProj_three_re_023]; norm_num
        · rw [trace_dfailsProj_three_re_swap12,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_013]; norm_num
        · rw [trace_dfailsProj_three_re_swap12,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_023]; norm_num
        · rw [trace_dfailsProj_three_re_swap12,
            trace_dfailsProj_three_re_012]; norm_num
        · rw [trace_dfailsProj_three_re_swap12,
            trace_dfailsProj_three_re_013]; norm_num
        · rw [trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_012]; norm_num
        · rw [trace_dfailsProj_three_re_123]; norm_num
        · rw [trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_013]; norm_num
        · rw [trace_dfailsProj_three_re_swap12,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_123]; norm_num
        · rw [trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_012]; norm_num
        · rw [trace_dfailsProj_three_re_swap12,
            trace_dfailsProj_three_re_023]; norm_num
        · rw [trace_dfailsProj_three_re_swap12, trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_012]; norm_num
        · rw [trace_dfailsProj_three_re_swap12,
            trace_dfailsProj_three_re_123]; norm_num
        · rw [trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_023]; norm_num
        · rw [trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_123]; norm_num
        · rw [trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_013]; norm_num
        · rw [trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_023]; norm_num
        · rw [trace_dfailsProj_three_re_swap12, trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_013]; norm_num
        · rw [trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_123]; norm_num
        · rw [trace_dfailsProj_three_re_swap12, trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_023]; norm_num
        · rw [trace_dfailsProj_three_re_swap12, trace_dfailsProj_three_re_cycle,
            trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_123]; norm_num

theorem trace_dfailsProj_four_eq_K (a b c d : Fin 4) :
    Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj c * dfailsProj d) =
      Matrix.trace (dfailsK a b * dfailsK b c * dfailsK c d * dfailsK d a) := by
  unfold dfailsProj dfailsK
  calc
    Matrix.trace ((dfailsIsometry a * (dfailsIsometry a).conjTranspose) *
        (dfailsIsometry b * (dfailsIsometry b).conjTranspose) *
        (dfailsIsometry c * (dfailsIsometry c).conjTranspose) *
        (dfailsIsometry d * (dfailsIsometry d).conjTranspose))
        = Matrix.trace (dfailsIsometry a *
            ((dfailsIsometry a).conjTranspose * dfailsIsometry b *
              ((dfailsIsometry b).conjTranspose * dfailsIsometry c) *
              ((dfailsIsometry c).conjTranspose * dfailsIsometry d) *
              (dfailsIsometry d).conjTranspose)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((dfailsIsometry a).conjTranspose * dfailsIsometry b *
            ((dfailsIsometry b).conjTranspose * dfailsIsometry c) *
            ((dfailsIsometry c).conjTranspose * dfailsIsometry d) *
            (dfailsIsometry d).conjTranspose) * dfailsIsometry a) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((dfailsIsometry a).conjTranspose * dfailsIsometry b) *
          ((dfailsIsometry b).conjTranspose * dfailsIsometry c) *
          ((dfailsIsometry c).conjTranspose * dfailsIsometry d) *
          ((dfailsIsometry d).conjTranspose * dfailsIsometry a)) := by
      simp only [Matrix.mul_assoc]

theorem trace_dfailsProj_four_re_0123 :
    (Matrix.trace (dfailsProj 0 * dfailsProj 1 * dfailsProj 2 * dfailsProj 3)).re = 2 / 9 := by
  rw [trace_dfailsProj_four_eq_K, dfailsK_01, dfailsK_12, dfailsK_23, dfailsK_30]
  have hs : invSqrt3C * ((1 / 3 : ℂ) * (invSqrt2C * invSqrt3C * invSqrt2C)) = (1 / 18 : ℂ) := by
    calc
      invSqrt3C * ((1 / 3 : ℂ) * (invSqrt2C * invSqrt3C * invSqrt2C)) =
          (1 / 3 : ℂ) * ((invSqrt2C * invSqrt2C) * (invSqrt3C * invSqrt3C)) := by ring
      _ = (1 / 3 : ℂ) * ((1 / 2 : ℂ) * (1 / 3 : ℂ)) := by
        rw [invSqrt2C_mul_self, invSqrt3C_mul_self]
      _ = 1 / 18 := by norm_num
  have hnum : (1 - dfailsC1) * (1 - dfailsC1 * dfailsC2 - dfailsC3) =
      1 - dfailsC1 * dfailsC2 - dfailsC3 - dfailsC1 - dfailsC2 + dfailsC1 * dfailsC3 := by
    have h1 : (1 - dfailsC1) * (1 - dfailsC1 * dfailsC2 - dfailsC3) =
        1 - dfailsC1 * dfailsC2 - dfailsC3 - dfailsC1 + dfailsC1 * dfailsC1 * dfailsC2 +
          dfailsC1 * dfailsC3 := by noncomm_ring
    rw [h1, dfailsC1_sq]
    noncomm_ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [hs, hnum, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_one, Fintype.card_fin, dfailsC1C2_trace, dfailsC3_trace, dfailsC1_trace,
    dfailsC2_trace, dfailsC1C3_trace]
  norm_num

theorem trace_dfailsProj_four_re_0213 :
    (Matrix.trace (dfailsProj 0 * dfailsProj 2 * dfailsProj 1 * dfailsProj 3)).re = 2 / 9 := by
  rw [trace_dfailsProj_four_eq_K, dfailsK_02, dfailsK_21, dfailsK_13, dfailsK_30]
  have hs : invSqrt3C * (invSqrt2C * invSqrt3C * (invSqrt2C * invSqrt3C * invSqrt3C)) =
      (1 / 18 : ℂ) := by
    calc
      invSqrt3C * (invSqrt2C * invSqrt3C * (invSqrt2C * invSqrt3C * invSqrt3C)) =
          (invSqrt2C * invSqrt2C) * ((invSqrt3C * invSqrt3C) * (invSqrt3C * invSqrt3C)) := by ring
      _ = (1 / 2 : ℂ) * ((1 / 3 : ℂ) * (1 / 3 : ℂ)) := by
        rw [invSqrt2C_mul_self, invSqrt3C_mul_self]
      _ = 1 / 18 := by norm_num
  have hnum : (1 + dfailsC1) * (1 - dfailsC2) = 1 - dfailsC2 + dfailsC1 - dfailsC1 * dfailsC2 := by
    noncomm_ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [hs, hnum, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, dfailsC2_trace, dfailsC1_trace,
    dfailsC1C2_trace]
  norm_num

theorem trace_dfailsProj_four_re_0231 :
    (Matrix.trace (dfailsProj 0 * dfailsProj 2 * dfailsProj 3 * dfailsProj 1)).re = 2 / 9 := by
  rw [trace_dfailsProj_four_eq_K, dfailsK_02, dfailsK_23, dfailsK_31, dfailsK_10]
  have hs : invSqrt2C * (invSqrt2C * invSqrt3C * ((1 / 3 : ℂ) * invSqrt3C)) = (1 / 18 : ℂ) := by
    calc
      invSqrt2C * (invSqrt2C * invSqrt3C * ((1 / 3 : ℂ) * invSqrt3C)) =
          (1 / 3 : ℂ) * ((invSqrt2C * invSqrt2C) * (invSqrt3C * invSqrt3C)) := by ring
      _ = (1 / 3 : ℂ) * ((1 / 2 : ℂ) * (1 / 3 : ℂ)) := by
        rw [invSqrt2C_mul_self, invSqrt3C_mul_self]
      _ = 1 / 18 := by norm_num
  have hnum : (1 - dfailsC1 * dfailsC2 - dfailsC3) * (1 + dfailsC2) =
      1 + dfailsC2 - dfailsC1 * dfailsC2 + dfailsC1 - dfailsC3 - dfailsC3 * dfailsC2 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [dfailsC1, dfailsC2, dfailsC3, Matrix.mul_apply, Fin.sum_univ_four] <;>
      ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [hs, hnum, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin,
    dfailsC2_trace, dfailsC1C2_trace, dfailsC1_trace, dfailsC3_trace, dfailsC2_C3_anticomm,
    Matrix.trace_neg, dfailsC2C3_trace]
  norm_num

private theorem trace_dfailsProj_four_re_rev (a b c d : Fin 4) :
    (Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj c * dfailsProj d)).re =
      (Matrix.trace (dfailsProj a * dfailsProj d * dfailsProj c * dfailsProj b)).re := by
  have hconj : (dfailsProj a * dfailsProj b * dfailsProj c * dfailsProj d).conjTranspose =
      dfailsProj d * dfailsProj c * dfailsProj b * dfailsProj a := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      (dfailsProj_hermitian a).eq, (dfailsProj_hermitian b).eq,
      (dfailsProj_hermitian c).eq, (dfailsProj_hermitian d).eq]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (dfailsProj d * dfailsProj c * dfailsProj b * dfailsProj a) =
      star (Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj c * dfailsProj d)) := by
    rw [← hconj, Matrix.trace_conjTranspose]
  have hcyc : Matrix.trace (dfailsProj d * dfailsProj c * dfailsProj b * dfailsProj a) =
      Matrix.trace (dfailsProj a * dfailsProj d * dfailsProj c * dfailsProj b) := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hcyc] at htr
  have hre := congrArg Complex.re htr
  simpa [Complex.star_def, Complex.conj_re] using hre.symm

theorem wordExtractOverlap_dfails (i j : Fin 4) :
    wordExtractOverlap dfailsModel.probability i j = fpOverlap fixedS i j := by
  unfold wordExtractOverlap
  rw [dfailsModel_prob_two_true]
  change 3 * (1 / 3 * fpOverlap fixedS i j) = fpOverlap fixedS i j
  ring

theorem wordExtractOverlap_fixedS (i j : Fin 4) :
    wordExtractOverlap (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) i j =
      fpOverlap fixedS i j := by
  unfold wordExtractOverlap
  rw [fixedS_prob_two_true]
  change 3 * (1 / 3 * fpOverlap fixedS i j) = fpOverlap fixedS i j
  ring

theorem wordExtractTriangle_dfails (i j k : Fin 4) :
    wordExtractTriangle dfailsModel.probability i j k = fpTriangle fixedS i j k := by
  unfold wordExtractTriangle
  rw [dfailsModel_probability, dfailsModel_probability, dfailsModel_probability]
  have hstar : ∀ l, star (dfailsProj l) = dfailsProj l := fun l => (dfailsProj_hermitian l).eq
  have hw2 : wordOperator dfailsProj [(i, true), (k, true)] =
      dfailsProj i * dfailsProj k * dfailsProj i := by
    rw [wordOperator_cons dfailsProj hstar, wordOperator_singleton dfailsProj dfailsProj_idempotent hstar]
    rfl
  have hw3t : wordOperator dfailsProj [(i, true), (j, true), (k, true)] =
      dfailsProj i * (dfailsProj j * dfailsProj k * dfailsProj j) * dfailsProj i := by
    rw [wordOperator_cons dfailsProj hstar, wordOperator_cons dfailsProj hstar,
      wordOperator_singleton dfailsProj dfailsProj_idempotent hstar]
    rfl
  have hw3f : wordOperator dfailsProj [(i, true), (j, false), (k, true)] =
      dfailsProj i * ((1 - dfailsProj j) * dfailsProj k * (1 - dfailsProj j)) * dfailsProj i := by
    rw [wordOperator_cons dfailsProj hstar, wordOperator_cons dfailsProj hstar,
      wordOperator_singleton dfailsProj dfailsProj_idempotent hstar]
    rfl
  have halg : dfailsProj i * dfailsProj k * dfailsProj i +
      dfailsProj i * (dfailsProj j * dfailsProj k * dfailsProj j) * dfailsProj i -
      dfailsProj i * ((1 - dfailsProj j) * dfailsProj k * (1 - dfailsProj j)) * dfailsProj i =
      dfailsProj i * (dfailsProj j * dfailsProj k + dfailsProj k * dfailsProj j) * dfailsProj i := by
    noncomm_ring
  have htr : Matrix.trace (dfailsProj i * dfailsProj k * dfailsProj i) +
      Matrix.trace (dfailsProj i * (dfailsProj j * dfailsProj k * dfailsProj j) * dfailsProj i) -
      Matrix.trace (dfailsProj i * ((1 - dfailsProj j) * dfailsProj k * (1 - dfailsProj j)) * dfailsProj i) =
      Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj k) +
        Matrix.trace (dfailsProj i * dfailsProj k * dfailsProj j) := by
    rw [← Matrix.trace_add, ← Matrix.trace_sub, halg, Matrix.mul_add, Matrix.add_mul,
      Matrix.trace_add]
    have hc1 : Matrix.trace (dfailsProj i * (dfailsProj j * dfailsProj k) * dfailsProj i) =
        Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj k) := by
      rw [Matrix.trace_mul_cycle, dfailsProj_idempotent]
      simp only [Matrix.mul_assoc]
    have hc2 : Matrix.trace (dfailsProj i * (dfailsProj k * dfailsProj j) * dfailsProj i) =
        Matrix.trace (dfailsProj i * dfailsProj k * dfailsProj j) := by
      rw [Matrix.trace_mul_cycle, dfailsProj_idempotent]
      simp only [Matrix.mul_assoc]
    rw [hc1, hc2]
  rw [hw2, hw3t, hw3f]
  have hsum_re : (Matrix.trace (dfailsProj i * dfailsProj k * dfailsProj i)).re +
      (Matrix.trace (dfailsProj i * (dfailsProj j * dfailsProj k * dfailsProj j) * dfailsProj i)).re -
      (Matrix.trace (dfailsProj i * ((1 - dfailsProj j) * dfailsProj k * (1 - dfailsProj j)) * dfailsProj i)).re =
      8 * fpTriangle fixedS i j k := by
    rw [← Complex.add_re, ← Complex.sub_re, htr, Complex.add_re,
      trace_dfailsProj_three_re,
      show (Matrix.trace (dfailsProj i * dfailsProj k * dfailsProj j)).re =
        (Matrix.trace (dfailsProj i * dfailsProj j * dfailsProj k)).re by
        rw [trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_swap12,
          trace_dfailsProj_three_re_cycle, trace_dfailsProj_three_re_cycle],
      trace_dfailsProj_three_re]
    ring
  linarith

theorem wordExtractTriangle_fixedS (i j k : Fin 4) :
    wordExtractTriangle (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) i j k =
      fpTriangle fixedS i j k := by
  unfold wordExtractTriangle
  have h1 : nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (k, true)] +
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, true), (k, true)] -
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, false), (k, true)] =
      (2 / 3 : ℝ) * fpTriangle fixedS i j k := by
    unfold nativeWordProbability nativeBranchState
    simp only [List.foldl_cons, List.foldl_nil, nativeOutcome, Bool.false_eq_true, ↓reduceIte]
    rw [fixedS_quadratic_e3]
    have hdiff : fixedS i + quadraticMap (fixedS j) (fixedS i) -
        quadraticMap (albertUnit - fixedS j) (fixedS i) =
        (2 : ℝ) • jordanMul (fixedS j) (fixedS i) := by
      unfold quadraticMap
      simp only [jordanMul_sub_left, jordanMul_sub_right,
        jordanMul_albertUnit_left, jordanMul_albertUnit_right, (fixedS_isAtom j).1]
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
      abel
    simp only [quadraticMap_smul_right, quadraticMap_atom _ _ (fixedS_isAtom k),
      albertTrace_smul, (fixedS_isAtom k).2, mul_one, tracePairing_smul_right]
    rw [show (1 / 3 : ℝ) * tracePairing (fixedS k) (fixedS i) +
        (1 / 3 : ℝ) * tracePairing (fixedS k) (quadraticMap (fixedS j) (fixedS i)) -
        (1 / 3 : ℝ) * tracePairing (fixedS k) (quadraticMap (albertUnit - fixedS j) (fixedS i)) =
        (1 / 3 : ℝ) * tracePairing (fixedS k)
          (fixedS i + quadraticMap (fixedS j) (fixedS i) -
            quadraticMap (albertUnit - fixedS j) (fixedS i)) by
      rw [tracePairing_sub_right, tracePairing_add_right]; ring]
    rw [hdiff, tracePairing_smul_right]
    unfold fpTriangle
    rw [tracePairing_comm (fixedS k), jordanMul_comm (fixedS j) (fixedS i)]
    ring
  rw [h1]
  ring

private theorem dfails_mid_sum (x : Fin 4) (X : Matrix (Fin 12) (Fin 12) ℂ) :
    X + dfailsProj x * X * dfailsProj x -
      (1 - dfailsProj x) * X * (1 - dfailsProj x) =
      dfailsProj x * X + X * dfailsProj x := by
  noncomm_ring

private theorem trace_re_conj_swap_ab (a b c d : Fin 4) :
    (Matrix.trace (dfailsProj b * dfailsProj a * dfailsProj c * dfailsProj d)).re =
      (Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj d * dfailsProj c)).re := by
  have hconj : (dfailsProj b * dfailsProj a * dfailsProj c * dfailsProj d).conjTranspose =
      dfailsProj d * dfailsProj c * dfailsProj a * dfailsProj b := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      (dfailsProj_hermitian a).eq, (dfailsProj_hermitian b).eq,
      (dfailsProj_hermitian c).eq, (dfailsProj_hermitian d).eq]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (dfailsProj d * dfailsProj c * dfailsProj a * dfailsProj b) =
      star (Matrix.trace (dfailsProj b * dfailsProj a * dfailsProj c * dfailsProj d)) := by
    rw [← hconj, Matrix.trace_conjTranspose]
  have hcyc : Matrix.trace (dfailsProj d * dfailsProj c * dfailsProj a * dfailsProj b) =
      Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj d * dfailsProj c) := by
    calc
      Matrix.trace (dfailsProj d * dfailsProj c * dfailsProj a * dfailsProj b)
          = Matrix.trace ((dfailsProj d * dfailsProj c) * (dfailsProj a * dfailsProj b)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((dfailsProj a * dfailsProj b) * (dfailsProj d * dfailsProj c)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj d * dfailsProj c) := by
        simp only [Matrix.mul_assoc]
  rw [hcyc] at htr
  have hre := congrArg Complex.re htr
  simpa [Complex.star_def, Complex.conj_re] using hre.symm

theorem wordExtractDoublePair_dfails_eq (a b c d : Fin 4) :
    wordExtractDoublePair dfailsModel.probability a b c d =
      (1 / 8 : ℝ) * (Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj c * dfailsProj d)).re +
      (1 / 8 : ℝ) * (Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj d * dfailsProj c)).re := by
  unfold wordExtractDoublePair
  have hstar : ∀ l, star (dfailsProj l) = dfailsProj l := fun l => (dfailsProj_hermitian l).eq
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.append_nil, List.nil_append, List.cons_append, dfailsModel_probability]
  let W0 := wordOperator dfailsProj [(d, true)]
  let W1 := wordOperator dfailsProj [(c, true), (d, true)]
  let W2 := wordOperator dfailsProj [(c, false), (d, true)]
  have hW0 : W0 = dfailsProj d := by
    simp only [W0, wordOperator_singleton dfailsProj dfailsProj_idempotent hstar, algebraicOutcome]
    rfl
  have hW1 : W1 = dfailsProj c * dfailsProj d * dfailsProj c := by
    rw [show W1 = dfailsProj c * W0 * dfailsProj c by
      simp only [W1, W0, wordOperator_cons dfailsProj hstar, algebraicOutcome]; rfl, hW0]
  have hW2 : W2 = (1 - dfailsProj c) * dfailsProj d * (1 - dfailsProj c) := by
    rw [show W2 = (1 - dfailsProj c) * W0 * (1 - dfailsProj c) by
      simp only [W2, W0, wordOperator_cons dfailsProj hstar, algebraicOutcome]; rfl, hW0]
  have hY : W0 + W1 - W2 = dfailsProj c * dfailsProj d + dfailsProj d * dfailsProj c := by
    rw [hW0, hW1, hW2, dfails_mid_sum]
  have hw_cons : ∀ (w : Word (Fin 4)),
      wordOperator dfailsProj ((a, true) :: w) =
        dfailsProj a * wordOperator dfailsProj w * dfailsProj a := fun w => by
    rw [wordOperator_cons dfailsProj hstar]
    rfl
  have hw_cons2 : ∀ (x : Fin 4) (s : Bool) (w : Word (Fin 4)),
      wordOperator dfailsProj ((a, true) :: (x, s) :: w) =
        dfailsProj a * (algebraicOutcome dfailsProj (x, s) * wordOperator dfailsProj w *
          algebraicOutcome dfailsProj (x, s)) * dfailsProj a := fun x s w => by
    rw [hw_cons, wordOperator_cons dfailsProj hstar]
  have hsum_op :
      (wordOperator dfailsProj [(a, true), (d, true)] +
        wordOperator dfailsProj [(a, true), (c, true), (d, true)] -
        wordOperator dfailsProj [(a, true), (c, false), (d, true)]) +
      (wordOperator dfailsProj [(a, true), (b, true), (d, true)] +
        wordOperator dfailsProj [(a, true), (b, true), (c, true), (d, true)] -
        wordOperator dfailsProj [(a, true), (b, true), (c, false), (d, true)]) -
      (wordOperator dfailsProj [(a, true), (b, false), (d, true)] +
        wordOperator dfailsProj [(a, true), (b, false), (c, true), (d, true)] -
        wordOperator dfailsProj [(a, true), (b, false), (c, false), (d, true)]) =
      dfailsProj a * (dfailsProj b * (W0 + W1 - W2) + (W0 + W1 - W2) * dfailsProj b) *
        dfailsProj a := by
    rw [hw_cons [(d, true)], hw_cons [(c, true), (d, true)], hw_cons [(c, false), (d, true)],
      hw_cons2 b true [(d, true)], hw_cons2 b true [(c, true), (d, true)],
      hw_cons2 b true [(c, false), (d, true)],
      hw_cons2 b false [(d, true)], hw_cons2 b false [(c, true), (d, true)],
      hw_cons2 b false [(c, false), (d, true)]]
    simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte]
    change (dfailsProj a * W0 * dfailsProj a + dfailsProj a * W1 * dfailsProj a -
        dfailsProj a * W2 * dfailsProj a) +
      (dfailsProj a * (dfailsProj b * W0 * dfailsProj b) * dfailsProj a +
        dfailsProj a * (dfailsProj b * W1 * dfailsProj b) * dfailsProj a -
        dfailsProj a * (dfailsProj b * W2 * dfailsProj b) * dfailsProj a) -
      (dfailsProj a * ((1 - dfailsProj b) * W0 * (1 - dfailsProj b)) * dfailsProj a +
        dfailsProj a * ((1 - dfailsProj b) * W1 * (1 - dfailsProj b)) * dfailsProj a -
        dfailsProj a * ((1 - dfailsProj b) * W2 * (1 - dfailsProj b)) * dfailsProj a) = _
    noncomm_ring
  rw [hY] at hsum_op
  have htr_op : Matrix.trace (dfailsProj a *
      (dfailsProj b * (dfailsProj c * dfailsProj d + dfailsProj d * dfailsProj c) +
        (dfailsProj c * dfailsProj d + dfailsProj d * dfailsProj c) * dfailsProj b) *
      dfailsProj a) =
      Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj c * dfailsProj d) +
      Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj d * dfailsProj c) +
      Matrix.trace (dfailsProj b * dfailsProj a * dfailsProj c * dfailsProj d) +
      Matrix.trace (dfailsProj b * dfailsProj a * dfailsProj d * dfailsProj c) := by
    have h1 : Matrix.trace (dfailsProj a * (dfailsProj b * dfailsProj c * dfailsProj d) * dfailsProj a) =
        Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj c * dfailsProj d) := by
      rw [Matrix.trace_mul_cycle, dfailsProj_idempotent]
      simp only [Matrix.mul_assoc]
    have h2 : Matrix.trace (dfailsProj a * (dfailsProj b * dfailsProj d * dfailsProj c) * dfailsProj a) =
        Matrix.trace (dfailsProj a * dfailsProj b * dfailsProj d * dfailsProj c) := by
      rw [Matrix.trace_mul_cycle, dfailsProj_idempotent]
      simp only [Matrix.mul_assoc]
    have h3 : Matrix.trace (dfailsProj a * (dfailsProj c * dfailsProj d * dfailsProj b) * dfailsProj a) =
        Matrix.trace (dfailsProj b * dfailsProj a * dfailsProj c * dfailsProj d) := by
      calc
        Matrix.trace (dfailsProj a * (dfailsProj c * dfailsProj d * dfailsProj b) * dfailsProj a)
            = Matrix.trace (dfailsProj a * dfailsProj a * (dfailsProj c * dfailsProj d * dfailsProj b)) :=
          Matrix.trace_mul_cycle _ _ _
        _ = Matrix.trace ((dfailsProj a * (dfailsProj c * dfailsProj d)) * dfailsProj b) := by
          rw [dfailsProj_idempotent]; simp only [Matrix.mul_assoc]
        _ = Matrix.trace (dfailsProj b * (dfailsProj a * (dfailsProj c * dfailsProj d))) :=
          Matrix.trace_mul_comm _ _
        _ = Matrix.trace (dfailsProj b * dfailsProj a * dfailsProj c * dfailsProj d) := by
          simp only [Matrix.mul_assoc]
    have h4 : Matrix.trace (dfailsProj a * (dfailsProj d * dfailsProj c * dfailsProj b) * dfailsProj a) =
        Matrix.trace (dfailsProj b * dfailsProj a * dfailsProj d * dfailsProj c) := by
      calc
        Matrix.trace (dfailsProj a * (dfailsProj d * dfailsProj c * dfailsProj b) * dfailsProj a)
            = Matrix.trace (dfailsProj a * dfailsProj a * (dfailsProj d * dfailsProj c * dfailsProj b)) :=
          Matrix.trace_mul_cycle _ _ _
        _ = Matrix.trace ((dfailsProj a * (dfailsProj d * dfailsProj c)) * dfailsProj b) := by
          rw [dfailsProj_idempotent]; simp only [Matrix.mul_assoc]
        _ = Matrix.trace (dfailsProj b * (dfailsProj a * (dfailsProj d * dfailsProj c))) :=
          Matrix.trace_mul_comm _ _
        _ = Matrix.trace (dfailsProj b * dfailsProj a * dfailsProj d * dfailsProj c) := by
          simp only [Matrix.mul_assoc]
    have hexp : dfailsProj a *
        (dfailsProj b * (dfailsProj c * dfailsProj d + dfailsProj d * dfailsProj c) +
          (dfailsProj c * dfailsProj d + dfailsProj d * dfailsProj c) * dfailsProj b) *
        dfailsProj a =
        dfailsProj a * (dfailsProj b * dfailsProj c * dfailsProj d) * dfailsProj a +
        dfailsProj a * (dfailsProj b * dfailsProj d * dfailsProj c) * dfailsProj a +
        dfailsProj a * (dfailsProj c * dfailsProj d * dfailsProj b) * dfailsProj a +
        dfailsProj a * (dfailsProj d * dfailsProj c * dfailsProj b) * dfailsProj a := by
      noncomm_ring
    rw [hexp, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, h1, h2, h3, h4]
  have htr_re :
      ((1 * 1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (d, true)])).re) +
          (1 * 1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (c, true), (d, true)])).re) +
          1 * -1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (c, false), (d, true)])).re))) +
        ((1 * 1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (b, true), (d, true)])).re) +
          (1 * 1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (b, true), (c, true), (d, true)])).re) +
          1 * -1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (b, true), (c, false), (d, true)])).re))) +
        (-1 * 1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (b, false), (d, true)])).re) +
          (-1 * 1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (b, false), (c, true), (d, true)])).re) +
          -1 * -1 * (1 / 12 * (Matrix.trace (wordOperator dfailsProj [(a, true), (b, false), (c, false), (d, true)])).re))))) =
      (1 / 12 : ℝ) * (Matrix.trace (
        (wordOperator dfailsProj [(a, true), (d, true)] +
          wordOperator dfailsProj [(a, true), (c, true), (d, true)] -
          wordOperator dfailsProj [(a, true), (c, false), (d, true)]) +
        (wordOperator dfailsProj [(a, true), (b, true), (d, true)] +
          wordOperator dfailsProj [(a, true), (b, true), (c, true), (d, true)] -
          wordOperator dfailsProj [(a, true), (b, true), (c, false), (d, true)]) -
        (wordOperator dfailsProj [(a, true), (b, false), (d, true)] +
          wordOperator dfailsProj [(a, true), (b, false), (c, true), (d, true)] -
          wordOperator dfailsProj [(a, true), (b, false), (c, false), (d, true)]))).re := by
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
    ring
  rw [htr_re, hsum_op, htr_op]
  simp only [Complex.add_re, trace_re_conj_swap_ab a b c d, trace_re_conj_swap_ab a b d c]
  ring

theorem wordExtractDoublePair_dfails_1 :
    wordExtractDoublePair dfailsModel.probability 0 1 2 3 = 1 / 18 := by
  rw [wordExtractDoublePair_dfails_eq, trace_dfailsProj_four_re_0123,
    trace_dfailsProj_four_re_rev 0 1 3 2, trace_dfailsProj_four_re_0231]
  norm_num

theorem wordExtractDoublePair_dfails_2 :
    wordExtractDoublePair dfailsModel.probability 0 2 1 3 = 1 / 18 := by
  rw [wordExtractDoublePair_dfails_eq, trace_dfailsProj_four_re_0213,
    trace_dfailsProj_four_re_rev 0 2 3 1]
  have h132 : (Matrix.trace (dfailsProj 0 * dfailsProj 1 * dfailsProj 3 * dfailsProj 2)).re =
      2 / 9 := by
    rw [trace_dfailsProj_four_re_rev 0 1 3 2]
    exact trace_dfailsProj_four_re_0231
  rw [h132]
  norm_num

theorem wordExtractDoublePair_dfails_3 :
    wordExtractDoublePair dfailsModel.probability 0 3 1 2 = 1 / 18 := by
  rw [wordExtractDoublePair_dfails_eq]
  have h0312 : (Matrix.trace (dfailsProj 0 * dfailsProj 3 * dfailsProj 1 * dfailsProj 2)).re =
      2 / 9 := by
    rw [trace_dfailsProj_four_re_rev 0 3 1 2]
    exact trace_dfailsProj_four_re_0213
  have h0321 : (Matrix.trace (dfailsProj 0 * dfailsProj 3 * dfailsProj 2 * dfailsProj 1)).re =
      2 / 9 := by
    rw [trace_dfailsProj_four_re_rev 0 3 2 1]
    exact trace_dfailsProj_four_re_0123
  rw [h0312, h0321]
  norm_num

private theorem quadraticMap_mid_diff (q x : Albert) (hq : jordanMul q q = q) :
    x + quadraticMap q x - quadraticMap (albertUnit - q) x = (2 : ℝ) • jordanMul q x := by
  unfold quadraticMap
  simp only [jordanMul_sub_left, jordanMul_sub_right,
    jordanMul_albertUnit_left, jordanMul_albertUnit_right, hq]
  simp only [two_smul]
  abel

theorem wordExtractDoublePair_fixedS_eq (a b c d : Fin 4) :
    wordExtractDoublePair (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) a b c d =
      tracePairing (jordanMul (fixedS a) (fixedS b)) (jordanMul (fixedS c) (fixedS d)) := by
  unfold wordExtractDoublePair
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.append_nil, List.nil_append, List.cons_append]
  let ρ0 : Albert := (1 / 3 : ℝ) • fixedS a
  have hstep_mid : ∀ (x : Fin 4) (y : Albert) (w : Word (Fin 4)),
      nativeWordProbability fixedS y w +
        nativeWordProbability fixedS y ((x, true) :: w) -
        nativeWordProbability fixedS y ((x, false) :: w) =
      nativeWordProbability fixedS ((2 : ℝ) • jordanMul (fixedS x) y) w := by
    intro x y w
    unfold nativeWordProbability
    change albertTrace (nativeBranchState fixedS y w) +
        albertTrace (nativeBranchState fixedS (quadraticMap (fixedS x) y) w) -
        albertTrace (nativeBranchState fixedS (quadraticMap (albertUnit - fixedS x) y) w) = _
    have hsub : ∀ ρ₁ ρ₂ : Albert,
        nativeBranchState fixedS (ρ₁ - ρ₂) w =
          nativeBranchState fixedS ρ₁ w - nativeBranchState fixedS ρ₂ w := by
      intro ρ₁ ρ₂
      have h := nativeBranchState_linear_add fixedS (ρ₁ - ρ₂) ρ₂ w
      rw [sub_add_cancel] at h
      exact eq_sub_of_add_eq h.symm
    rw [← albertTrace_add, ← nativeBranchState_linear_add, ← albertTrace_sub, ← hsub,
      quadraticMap_mid_diff (fixedS x) y (fixedS_isAtom x).1]
  have hstep_first : ∀ (w : Word (Fin 4)),
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) ((a, true) :: w) =
        nativeWordProbability fixedS ρ0 w := fun w => by
    unfold nativeWordProbability
    change albertTrace (nativeBranchState fixedS
        (quadraticMap (fixedS a) ((1 / 3 : ℝ) • albertUnit)) w) = _
    rw [fixedS_quadratic_e3]
  have hb0 := hstep_mid c ρ0 [(d, true)]
  have hb1 := hstep_mid c (quadraticMap (fixedS b) ρ0) [(d, true)]
  have hb2 := hstep_mid c (quadraticMap (albertUnit - fixedS b) ρ0) [(d, true)]
  have hcombine :
      (nativeWordProbability fixedS ρ0 [(d, true)] +
          nativeWordProbability fixedS ρ0 [(c, true), (d, true)] -
          nativeWordProbability fixedS ρ0 [(c, false), (d, true)]) +
        (nativeWordProbability fixedS ρ0 [(b, true), (d, true)] +
          nativeWordProbability fixedS ρ0 [(b, true), (c, true), (d, true)] -
          nativeWordProbability fixedS ρ0 [(b, true), (c, false), (d, true)]) -
        (nativeWordProbability fixedS ρ0 [(b, false), (d, true)] +
          nativeWordProbability fixedS ρ0 [(b, false), (c, true), (d, true)] -
          nativeWordProbability fixedS ρ0 [(b, false), (c, false), (d, true)]) =
      nativeWordProbability fixedS
        ((2 : ℝ) • jordanMul (fixedS c) ((2 : ℝ) • jordanMul (fixedS b) ρ0)) [(d, true)] := by
    have hqb : ∀ (s : Word (Fin 4)),
        nativeWordProbability fixedS ρ0 ((b, true) :: s) =
          nativeWordProbability fixedS (quadraticMap (fixedS b) ρ0) s := fun _ => rfl
    have hqnb : ∀ (s : Word (Fin 4)),
        nativeWordProbability fixedS ρ0 ((b, false) :: s) =
          nativeWordProbability fixedS (quadraticMap (albertUnit - fixedS b) ρ0) s := fun _ => rfl
    rw [hqb [(d, true)], hqb [(c, true), (d, true)], hqb [(c, false), (d, true)],
      hqnb [(d, true)], hqnb [(c, true), (d, true)], hqnb [(c, false), (d, true)],
      hb0, hb1, hb2]
    have hfin : ∀ y : Albert,
        nativeWordProbability fixedS ((2 : ℝ) • jordanMul (fixedS c) y) [(d, true)] =
          2 * tracePairing (jordanMul (fixedS c) (fixedS d)) y := fun y => by
      unfold nativeWordProbability nativeBranchState
      simp only [List.foldl_cons, List.foldl_nil, nativeOutcome, ↓reduceIte,
        quadraticMap_atom _ _ (fixedS_isAtom d), albertTrace_smul, (fixedS_isAtom d).2,
        mul_one, tracePairing_smul_right]
      rw [tracePairing_comm (fixedS d), jordanMul_comm (fixedS c) y,
        NativeAnalysis.tracePairing_associative, tracePairing_comm y]
    rw [hfin ρ0, hfin (quadraticMap (fixedS b) ρ0), hfin (quadraticMap (albertUnit - fixedS b) ρ0),
      hfin ((2 : ℝ) • jordanMul (fixedS b) ρ0)]
    rw [← mul_add, ← mul_sub, ← tracePairing_add_right, ← tracePairing_sub_right,
      quadraticMap_mid_diff (fixedS b) ρ0 (fixedS_isAtom b).1]
  have hLHS :
      ((1 * 1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(a, true), (d, true)] +
          (1 * 1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            [(a, true), (c, true), (d, true)] +
          1 * -1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            [(a, true), (c, false), (d, true)])) +
        ((1 * 1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            [(a, true), (b, true), (d, true)] +
          (1 * 1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            [(a, true), (b, true), (c, true), (d, true)] +
          1 * -1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            [(a, true), (b, true), (c, false), (d, true)])) +
        (-1 * 1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            [(a, true), (b, false), (d, true)] +
          (-1 * 1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            [(a, true), (b, false), (c, true), (d, true)] +
          -1 * -1 * nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            [(a, true), (b, false), (c, false), (d, true)])))) =
      nativeWordProbability fixedS
        ((2 : ℝ) • jordanMul (fixedS c) ((2 : ℝ) • jordanMul (fixedS b) ρ0)) [(d, true)] := by
    rw [hstep_first [(d, true)], hstep_first [(c, true), (d, true)],
      hstep_first [(c, false), (d, true)], hstep_first [(b, true), (d, true)],
      hstep_first [(b, true), (c, true), (d, true)],
      hstep_first [(b, true), (c, false), (d, true)],
      hstep_first [(b, false), (d, true)],
      hstep_first [(b, false), (c, true), (d, true)],
      hstep_first [(b, false), (c, false), (d, true)]]
    linarith [hcombine]
  rw [hLHS]
  unfold nativeWordProbability nativeBranchState
  simp only [List.foldl_cons, List.foldl_nil, nativeOutcome, ↓reduceIte,
    quadraticMap_atom _ _ (fixedS_isAtom d),
    albertTrace_smul, (fixedS_isAtom d).2, mul_one]
  dsimp only [ρ0]
  rw [jordanMul_smul_right, jordanMul_smul_right, jordanMul_smul_right,
    tracePairing_smul_right, tracePairing_smul_right, tracePairing_smul_right,
    tracePairing_comm (fixedS d),
    jordanMul_comm (fixedS c) (jordanMul (fixedS b) (fixedS a)),
    NativeAnalysis.tracePairing_associative, jordanMul_comm (fixedS b) (fixedS a)]
  ring

theorem dfails_thirteen_traces :
    (∀ i j, wordExtractOverlap dfailsModel.probability i j = fpOverlap fixedS i j) ∧
    (∀ i j k, wordExtractTriangle dfailsModel.probability i j k = fpTriangle fixedS i j k) ∧
    wordExtractDoublePair dfailsModel.probability 0 1 2 3 = fpDoublePair1 fixedS ∧
    wordExtractDoublePair dfailsModel.probability 0 2 1 3 = fpDoublePair2 fixedS ∧
    wordExtractDoublePair dfailsModel.probability 0 3 1 2 = fpDoublePair3 fixedS := by
  have hQ := nativeCornerQ_eq_fpOmega fixedS
  rw [nativeCornerQ_fixedS] at hQ
  have hω2 : fpOmega2 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 0) hQ.symm
  have hω3 : fpOmega3 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 1) hQ.symm
  have hω1 : fpOmega1 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 2) hQ.symm
  unfold fpOmega1 at hω1
  unfold fpOmega2 at hω2
  unfold fpOmega3 at hω3
  have ht1 : fpDoublePair1 fixedS = 1 / 18 := by linarith
  have ht2 : fpDoublePair2 fixedS = 1 / 18 := by linarith
  have ht3 : fpDoublePair3 fixedS = 1 / 18 := by linarith
  refine ⟨wordExtractOverlap_dfails, wordExtractTriangle_dfails, ?_, ?_, ?_⟩
  · rw [wordExtractDoublePair_dfails_1, ht1]
  · rw [wordExtractDoublePair_dfails_2, ht2]
  · rw [wordExtractDoublePair_dfails_3, ht3]

theorem dfails_thirteen_traces_match_fixedS :
    (∀ i j, wordExtractOverlap dfailsModel.probability i j =
      wordExtractOverlap (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) i j) ∧
    (∀ i j k, wordExtractTriangle dfailsModel.probability i j k =
      wordExtractTriangle (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) i j k) ∧
    wordExtractDoublePair dfailsModel.probability 0 1 2 3 =
      wordExtractDoublePair (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) 0 1 2 3 ∧
    wordExtractDoublePair dfailsModel.probability 0 2 1 3 =
      wordExtractDoublePair (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) 0 2 1 3 ∧
    wordExtractDoublePair dfailsModel.probability 0 3 1 2 =
      wordExtractDoublePair (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) 0 3 1 2 := by
  obtain ⟨ho, hR, ht1, ht2, ht3⟩ := dfails_thirteen_traces
  refine ⟨fun i j => (ho i j).trans (wordExtractOverlap_fixedS i j).symm,
    fun i j k => (hR i j k).trans (wordExtractTriangle_fixedS i j k).symm,
    ht1.trans (wordExtractDoublePair_fixedS_eq 0 1 2 3).symm,
    ht2.trans (wordExtractDoublePair_fixedS_eq 0 2 1 3).symm,
    ht3.trans (wordExtractDoublePair_fixedS_eq 0 3 1 2).symm⟩

theorem dfails_tetra_dtet :
    fpTetraDtet 1 (wordExtractOverlap dfailsModel.probability)
      (wordExtractTriangle dfailsModel.probability)
      ![wordExtractDoublePair dfailsModel.probability 0 1 2 3,
        wordExtractDoublePair dfailsModel.probability 0 2 1 3,
        wordExtractDoublePair dfailsModel.probability 0 3 1 2] = 1 / 12 := by
  obtain ⟨ho, hR, ht1, ht2, ht3⟩ := dfails_thirteen_traces
  have ho_fun : wordExtractOverlap dfailsModel.probability = fpOverlap fixedS := by
    funext i j; exact ho i j
  have hR_fun : wordExtractTriangle dfailsModel.probability = fpTriangle fixedS := by
    funext i j k; exact hR i j k
  rw [ho_fun, hR_fun, ht1, ht2, ht3]
  have hpos : ∀ i j : Fin 4, i ≠ j → 0 < fpOverlap fixedS i j := by
    intro i j hij
    change 0 < nativeOverlaps fixedS i j
    rw [nativeOverlaps_fixedS_eq, ite_eq_right hij]
    split_ifs <;> norm_num
  have hdt := fpTetraDtet_atoms 1 fixedS hpos
  have ho01 : fpOverlap fixedS 0 1 = 1 / 2 := by
    change nativeOverlaps fixedS 0 1 = 1 / 2
    rw [nativeOverlaps_fixedS_eq]; norm_num
  have ho02 : fpOverlap fixedS 0 2 = 1 / 3 := by
    change nativeOverlaps fixedS 0 2 = 1 / 3
    rw [nativeOverlaps_fixedS_eq]; norm_num
  have ho03 : fpOverlap fixedS 0 3 = 1 / 3 := by
    change nativeOverlaps fixedS 0 3 = 1 / 3
    rw [nativeOverlaps_fixedS_eq]; norm_num
  have ho12 : fpOverlap fixedS 1 2 = 1 / 3 := by
    change nativeOverlaps fixedS 1 2 = 1 / 3
    rw [nativeOverlaps_fixedS_eq]; norm_num
  have ho13 : fpOverlap fixedS 1 3 = 1 / 3 := by
    change nativeOverlaps fixedS 1 3 = 1 / 3
    rw [nativeOverlaps_fixedS_eq]; norm_num
  have ho23 : fpOverlap fixedS 2 3 = 1 / 3 := by
    change nativeOverlaps fixedS 2 3 = 1 / 3
    rw [nativeOverlaps_fixedS_eq]; norm_num
  rw [ho01, ho02, ho03, ho12, ho13, ho23, fourPointInvariant_fixedS] at hdt
  linarith

end ThirteenTraces

/-! ## Section 6: Purity Defect `φ(T^2) = 4 / 243` -/

section PurityDefect

def dfailsPurityOp : Matrix (Fin 12) (Fin 12) ℂ :=
  dfailsProj 2 * dfailsProj 3 * dfailsProj 2 - (1 / 3 : ℂ) • dfailsProj 2

theorem dfails_purity_defect :
    (1 / 12 : ℝ) * (Matrix.trace (dfailsPurityOp * dfailsPurityOp)).re = 4 / 243 := by
  have hPC_P : dfailsProj 2 * dfailsProj 3 * dfailsProj 2 =
      dfailsIsometry 2 * dfailsX 2 3 * (dfailsIsometry 2).conjTranspose := by
    unfold dfailsProj dfailsX dfailsK
    simp only [Matrix.mul_assoc]
  have hT : dfailsPurityOp =
      dfailsIsometry 2 * ((-2 / 9 : ℂ) • dfailsJ) * (dfailsIsometry 2).conjTranspose := by
    unfold dfailsPurityOp
    rw [hPC_P]
    have hdiff : dfailsX 2 3 - (1 / 3 : ℂ) • 1 = (-2 / 9 : ℂ) • dfailsJ := by
      rw [dfailsX_23]
      ext a b; simp; ring
    have hsub : dfailsIsometry 2 * (dfailsX 2 3 - (1 / 3 : ℂ) • 1) *
          (dfailsIsometry 2).conjTranspose =
        dfailsIsometry 2 * dfailsX 2 3 * (dfailsIsometry 2).conjTranspose -
          (1 / 3 : ℂ) • (dfailsIsometry 2 * (dfailsIsometry 2).conjTranspose) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    change dfailsIsometry 2 * dfailsX 2 3 * (dfailsIsometry 2).conjTranspose -
        (1 / 3 : ℂ) • (dfailsIsometry 2 * (dfailsIsometry 2).conjTranspose) = _
    rw [← hsub, hdiff]
  have hT2 : dfailsPurityOp * dfailsPurityOp = (4 / 81 : ℂ) • dfailsProj 2 := by
    rw [hT]
    calc
      dfailsIsometry 2 * ((-2 / 9 : ℂ) • dfailsJ) * (dfailsIsometry 2).conjTranspose *
          (dfailsIsometry 2 * ((-2 / 9 : ℂ) • dfailsJ) * (dfailsIsometry 2).conjTranspose)
          = dfailsIsometry 2 * ((-2 / 9 : ℂ) • dfailsJ) *
              ((dfailsIsometry 2).conjTranspose * dfailsIsometry 2) *
              ((-2 / 9 : ℂ) • dfailsJ) * (dfailsIsometry 2).conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = dfailsIsometry 2 * (((-2 / 9 : ℂ) • dfailsJ) * ((-2 / 9 : ℂ) • dfailsJ)) *
            (dfailsIsometry 2).conjTranspose := by
        rw [dfailsIsometry_isometry 2, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = (4 / 81 : ℂ) • dfailsProj 2 := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [dfailsJ_sq, show (-2 / 9 : ℂ) * (-2 / 9 : ℂ) = 4 / 81 by norm_num, Matrix.mul_one]
        rfl
  rw [hT2, Matrix.trace_smul, dfailsProj_trace]
  norm_num

end PurityDefect

/-! ## Section 7: Exact Characterization of Length-3 Deviations -/

section LengthThree

theorem dfailsModel_prob_three_true (i j k : Fin 4) :
    dfailsModel.probability [(i, true), (j, true), (k, true)] =
      (1 / 3 : ℝ) * ((1 / 4 : ℝ) * (Matrix.trace (dfailsX j i * dfailsX j k)).re) := by
  rw [dfailsModel_probability]
  have hstar : ∀ l, star (dfailsProj l) = dfailsProj l := fun l => (dfailsProj_hermitian l).eq
  rw [wordOperator_cons dfailsProj hstar, wordOperator_cons dfailsProj hstar,
    wordOperator_singleton dfailsProj dfailsProj_idempotent hstar]
  simp only [algebraicOutcome, ↓reduceIte]
  have htr : Matrix.trace (dfailsProj i * (dfailsProj j * dfailsProj k * dfailsProj j) *
      dfailsProj i) = Matrix.trace (dfailsX j i * dfailsX j k) := by
    rw [Matrix.trace_mul_cycle, dfailsProj_idempotent]
    unfold dfailsProj dfailsX dfailsK
    calc
      Matrix.trace (dfailsIsometry i * (dfailsIsometry i).conjTranspose *
          (dfailsIsometry j * (dfailsIsometry j).conjTranspose *
            (dfailsIsometry k * (dfailsIsometry k).conjTranspose) *
            (dfailsIsometry j * (dfailsIsometry j).conjTranspose)))
          = Matrix.trace (((dfailsIsometry i * (dfailsIsometry i).conjTranspose) *
              (dfailsIsometry j * (dfailsIsometry j).conjTranspose) *
              (dfailsIsometry k * (dfailsIsometry k).conjTranspose) * dfailsIsometry j) *
              (dfailsIsometry j).conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((dfailsIsometry j).conjTranspose *
            ((dfailsIsometry i * (dfailsIsometry i).conjTranspose) *
              (dfailsIsometry j * (dfailsIsometry j).conjTranspose) *
              (dfailsIsometry k * (dfailsIsometry k).conjTranspose) * dfailsIsometry j)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (((dfailsIsometry j).conjTranspose * dfailsIsometry i *
              ((dfailsIsometry i).conjTranspose * dfailsIsometry j)) *
            ((dfailsIsometry j).conjTranspose * dfailsIsometry k *
              ((dfailsIsometry k).conjTranspose * dfailsIsometry j))) := by
        simp only [Matrix.mul_assoc]
  rw [htr]
  ring

theorem fixedS_prob_three_true (i j k : Fin 4) :
    nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, true), (k, true)] =
      (1 / 3 : ℝ) * (nativeOverlaps fixedS i j * nativeOverlaps fixedS j k) := by
  unfold nativeWordProbability nativeBranchState
  simp only [List.foldl_cons, List.foldl_nil, nativeOutcome, ↓reduceIte]
  rw [fixedS_quadratic_e3, quadraticMap_smul_right, fixedS_quadratic_atom,
    quadraticMap_smul_right, quadraticMap_smul_right, fixedS_quadratic_atom]
  simp only [albertTrace_smul, (fixedS_isAtom k).2, mul_one]

theorem dfails_diff_three_true (i j k : Fin 4) :
    dfailsModel.probability [(i, true), (j, true), (k, true)] -
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, true), (k, true)] =
      if (i = 2 ∧ j = 3 ∧ k = 2) ∨ (i = 3 ∧ j = 2 ∧ k = 3) then (4 / 243 : ℝ) else 0 := by
  rw [dfailsModel_prob_three_true, fixedS_prob_three_true, dfailsX_mul_trace_re]
  by_cases h : (i = 2 ∧ j = 3 ∧ k = 2) ∨ (i = 3 ∧ j = 2 ∧ k = 3)
  · simp only [h, ↓reduceIte]
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have h23 : nativeOverlaps fixedS 2 3 = 1 / 3 := by
        rw [nativeOverlaps_fixedS_eq]; simp
      have h32 : nativeOverlaps fixedS 3 2 = 1 / 3 := by
        rw [nativeOverlaps_fixedS_eq]; simp
      rw [h23, h32]; norm_num
    · have h32 : nativeOverlaps fixedS 3 2 = 1 / 3 := by
        rw [nativeOverlaps_fixedS_eq]; simp
      have h23 : nativeOverlaps fixedS 2 3 = 1 / 3 := by
        rw [nativeOverlaps_fixedS_eq]; simp
      rw [h32, h23]; norm_num
  · simp only [h, ↓reduceIte]
    ring

theorem dfails_diff_three_mid_false (i j k : Fin 4) :
    dfailsModel.probability [(i, true), (j, false), (k, true)] -
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, false), (k, true)] =
      dfailsModel.probability [(i, true), (j, true), (k, true)] -
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, true), (k, true)] := by
  have htr_d := wordExtractTriangle_dfails i j k
  have htr_f := wordExtractTriangle_fixedS i j k
  have h2 := dfails_length_le_two [(i, true), (k, true)] (by simp)
  unfold wordExtractTriangle at htr_d htr_f
  linarith

theorem dfails_length_three_exact (i j k : Fin 4) (b₀ b₁ b₂ : Bool) :
    dfailsModel.probability [(i, b₀), (j, b₁), (k, b₂)] -
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, b₀), (j, b₁), (k, b₂)] =
      if (i = 2 ∧ j = 3 ∧ k = 2) ∨ (i = 3 ∧ j = 2 ∧ k = 3) then
        (if b₀ == b₂ then (4 / 243 : ℝ) else -(4 / 243 : ℝ))
      else 0 := by
  have hmid :
      dfailsModel.probability [(i, true), (j, b₁), (k, true)] -
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, b₁), (k, true)] =
        dfailsModel.probability [(i, true), (j, true), (k, true)] -
          nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, true), (k, true)] := by
    cases b₁
    · exact dfails_diff_three_mid_false i j k
    · rfl
  have htail : ∀ a₀ : Bool,
      dfailsModel.probability [(i, a₀), (j, b₁), (k, b₂)] -
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, a₀), (j, b₁), (k, b₂)] =
        (if b₂ then (1 : ℝ) else -1) *
          (dfailsModel.probability [(i, a₀), (j, b₁), (k, true)] -
            nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
              [(i, a₀), (j, b₁), (k, true)]) := fun a₀ => by
    cases b₂
    · have h2 := dfails_length_le_two [(i, a₀), (j, b₁)] (by simp)
      change dfailsModel.probability ([(i, a₀), (j, b₁)] ++ [(k, false)]) -
          nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            ([(i, a₀), (j, b₁)] ++ [(k, false)]) = _
      rw [dfails_prob_append_false, fixedS_prob_append_false, h2]
      simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
      ring
    · simp only [↓reduceIte, one_mul]
  have hhead :
      dfailsModel.probability [(i, b₀), (j, b₁), (k, true)] -
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(i, b₀), (j, b₁), (k, true)] =
        (if b₀ then (1 : ℝ) else -1) *
          (dfailsModel.probability [(i, true), (j, b₁), (k, true)] -
            nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
              [(i, true), (j, b₁), (k, true)]) := by
    cases b₀
    · have h2 := dfails_length_le_two [(j, b₁), (k, true)] (by simp)
      change dfailsModel.probability ((i, false) :: [(j, b₁), (k, true)]) -
          nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)
            ((i, false) :: [(j, b₁), (k, true)]) = _
      rw [dfails_prob_cons_false, fixedS_prob_cons_false, h2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring
    · simp only [↓reduceIte, one_mul]
  rw [htail b₀, hhead, hmid, dfails_diff_three_true]
  by_cases h : (i = 2 ∧ j = 3 ∧ k = 2) ∨ (i = 3 ∧ j = 2 ∧ k = 3)
  · simp only [h, ↓reduceIte]
    cases b₀ <;> cases b₂ <;> simp
  · simp only [h, ↓reduceIte]
    ring

theorem dfails_length_three_deviations (w : Word (Fin 4)) (hw : w.length = 3) :
    ((w.map Prod.fst = [2, 3, 2] ∨ w.map Prod.fst = [3, 2, 3]) →
      |dfailsModel.probability w -
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w| = 4 / 243) ∧
    (¬ (w.map Prod.fst = [2, 3, 2] ∨ w.map Prod.fst = [3, 2, 3]) →
      dfailsModel.probability w =
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w) := by
  rcases w with _ | ⟨⟨i, b₀⟩, w₁⟩
  · simp at hw
  · rcases w₁ with _ | ⟨⟨j, b₁⟩, w₂⟩
    · simp at hw
    · rcases w₂ with _ | ⟨⟨k, b₂⟩, w₃⟩
      · simp at hw
      · have hw3 : w₃ = [] := by
          simp only [List.length_cons] at hw
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hw3
        have hf : [(i, b₀), (j, b₁), (k, b₂)].map Prod.fst = [2, 3, 2] ∨
            [(i, b₀), (j, b₁), (k, b₂)].map Prod.fst = [3, 2, 3] ↔
            (i = 2 ∧ j = 3 ∧ k = 2) ∨ (i = 3 ∧ j = 2 ∧ k = 3) := by
          simp
        have hex := dfails_length_three_exact i j k b₀ b₁ b₂
        constructor
        · intro h
          simp only [hf.mp h, ↓reduceIte] at hex
          rw [hex]
          cases b₀ <;> cases b₂ <;> simp <;> norm_num
        · intro h
          have h' : ¬ ((i = 2 ∧ j = 3 ∧ k = 2) ∨ (i = 3 ∧ j = 2 ∧ k = 3)) := fun hc =>
            h (hf.mpr hc)
          simp only [h', ↓reduceIte] at hex
          exact sub_eq_zero.mp hex

end LengthThree

end AlbertSequential.MatchingModels
