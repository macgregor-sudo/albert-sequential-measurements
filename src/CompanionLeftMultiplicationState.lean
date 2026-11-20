/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionOctonionLeftMultiplication
public import ChronologicalWords
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The positive density on the real 24-dimensional carrier, and its signed-word trace. -/
@[expose] public section
noncomputable section
open scoped Matrix
namespace AlbertSequential.NativeAnalysis

abbrev QuaternionColumnCoordinate := Fin 3 × Fin 4

theorem quaternionColumnCoordinate_card : Fintype.card QuaternionColumnCoordinate = 12 := by decide

abbrev LeftModelSectorFrame := Matrix AlbertColumnCoordinate QuaternionColumnCoordinate ℝ

def leftModelSectorProjection (V : LeftModelSectorFrame) :
    Matrix AlbertColumnCoordinate AlbertColumnCoordinate ℝ :=
  V * Vᵀ

theorem leftModelSectorProjection_rank (V : LeftModelSectorFrame) (h : Vᵀ * V = 1) :
    (leftModelSectorProjection V).rank = 12 := by
  rw [leftModelSectorProjection, Matrix.rank_self_mul_transpose,
    ← Matrix.rank_transpose_mul_self, h, Matrix.rank_one, quaternionColumnCoordinate_card]

theorem leftModelSectorProjection_trace (V : LeftModelSectorFrame) (h : Vᵀ * V = 1) :
    (leftModelSectorProjection V).trace = 12 := by
  rw [leftModelSectorProjection, Matrix.trace_mul_comm, h, Matrix.trace_one,
    quaternionColumnCoordinate_card]
  norm_num

def leftModelWeight (a : ℝ) : ℝ := (1 + a) / 2

def leftModelDensity (a : ℝ) (VPlus VMinus : LeftModelSectorFrame) :
    Matrix AlbertColumnCoordinate AlbertColumnCoordinate ℝ :=
  (leftModelWeight a / 12) • leftModelSectorProjection VPlus +
    ((1 - leftModelWeight a) / 12) • leftModelSectorProjection VMinus

theorem leftModelDensity_posSemidef (a : ℝ) (ha : -1 ≤ a) (ha' : a ≤ 1)
    (VPlus VMinus : LeftModelSectorFrame) : (leftModelDensity a VPlus VMinus).PosSemidef := by
  have hv (V : LeftModelSectorFrame) : (leftModelSectorProjection V).PosSemidef := by
    simpa only [leftModelSectorProjection, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Matrix.posSemidef_self_mul_conjTranspose V
  have hPlus : 0 ≤ leftModelWeight a / 12 := by unfold leftModelWeight; linarith
  have hMinus : 0 ≤ (1 - leftModelWeight a) / 12 := by unfold leftModelWeight; linarith
  exact ((hv VPlus).smul hPlus).add ((hv VMinus).smul hMinus)

theorem leftModelDensity_trace (a : ℝ) (VPlus VMinus : LeftModelSectorFrame)
    (hPlus : VPlusᵀ * VPlus = 1) (hMinus : VMinusᵀ * VMinus = 1) :
    (leftModelDensity a VPlus VMinus).trace = 1 := by
  rw [leftModelDensity, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    leftModelSectorProjection_trace VPlus hPlus, leftModelSectorProjection_trace VMinus hMinus]
  simp only [smul_eq_mul]
  ring

theorem leftModelDensity_tracial (VPlus VMinus : LeftModelSectorFrame)
    (h : leftModelSectorProjection VPlus + leftModelSectorProjection VMinus = 1) :
    leftModelDensity 0 VPlus VMinus =
      (1 / 24 : ℝ) • (1 : Matrix AlbertColumnCoordinate AlbertColumnCoordinate ℝ) := by
  rw [leftModelDensity, leftModelWeight]
  norm_num
  rw [← smul_add, h]

theorem leftModelSectorProbability {ι : Type*}
    (P : ι → Matrix AlbertColumnCoordinate AlbertColumnCoordinate ℝ)
    (Q : ι → Matrix QuaternionColumnCoordinate QuaternionColumnCoordinate ℝ)
    (V : LeftModelSectorFrame) (hV : Vᵀ * V = 1)
    (hP : ∀ i, star (P i) = P i) (hQ : ∀ i, star (Q i) = Q i)
    (hPQ : ∀ i, P i * V = V * Q i) (w : Word ι) :
    (leftModelSectorProjection V * wordOperator P w).trace = (wordOperator Q w).trace := by
  have hout (x : Outcome ι) : algebraicOutcome P x * V = V * algebraicOutcome Q x := by
    obtain ⟨i, b⟩ := x
    cases b
    · simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hPQ]
    · exact hPQ i
  have hinter : wordOperator P w * V = V * wordOperator Q w := by
    induction w with
    | nil => simp
    | cons x w ih =>
      rw [wordOperator_cons P hP, wordOperator_cons Q hQ]
      let A := algebraicOutcome P x
      let B := algebraicOutcome Q x
      change (A * wordOperator P w * A) * V = V * (B * wordOperator Q w * B)
      calc
        _ = A * wordOperator P w * (A * V) := by simp only [Matrix.mul_assoc]
        _ = A * (wordOperator P w * V) * B := by
          rw [show A * V = V * B from hout x]
          simp only [Matrix.mul_assoc]
        _ = (A * V) * wordOperator Q w * B := by
          rw [ih]
          simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [show A * V = V * B from hout x]
          simp only [Matrix.mul_assoc]
  rw [leftModelSectorProjection, Matrix.mul_assoc, Matrix.trace_mul_comm V,
    Matrix.mul_assoc, hinter, ← Matrix.mul_assoc, hV, Matrix.one_mul]

theorem leftModelWeightedWordProbability {ι : Type*}
    (P : ι → Matrix AlbertColumnCoordinate AlbertColumnCoordinate ℝ)
    (QPlus QMinus : ι → Matrix QuaternionColumnCoordinate QuaternionColumnCoordinate ℝ)
    (VPlus VMinus : LeftModelSectorFrame) (hPlus : VPlusᵀ * VPlus = 1) (hMinus : VMinusᵀ * VMinus = 1)
    (hP : ∀ i, star (P i) = P i) (hQPlus : ∀ i, star (QPlus i) = QPlus i)
    (hQMinus : ∀ i, star (QMinus i) = QMinus i)
    (hPQPlus : ∀ i, P i * VPlus = VPlus * QPlus i)
    (hPQMinus : ∀ i, P i * VMinus = VMinus * QMinus i) (a : ℝ) (w : Word ι) :
    (leftModelDensity a VPlus VMinus * wordOperator P w).trace =
      leftModelWeight a * ((wordOperator QPlus w).trace / 12) +
        (1 - leftModelWeight a) * ((wordOperator QMinus w).trace / 12) := by
  rw [leftModelDensity, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul,
    leftModelSectorProbability P QPlus VPlus hPlus hP hQPlus hPQPlus,
    leftModelSectorProbability P QMinus VMinus hMinus hP hQMinus hPQMinus]
  simp only [smul_eq_mul]
  ring

end AlbertSequential.NativeAnalysis
