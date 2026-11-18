/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockA.GlennieBimodule
public import AppF.GlennieIngredients
public import ThreeAtomAndFourPoint
public import ComplexWindowDeterminantAndMax
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Window eight-word trace identity for `thm:glennie` (Step 2)

Proves:
1. For unit vectors `u : Fin 3 → ℂ` (`star u ⬝ᵥ u = 1`), `rankOneHermitian u` is a trace-1
   idempotent Hermitian matrix whose image under `standardComplexWindow.embedding` is an atom.
2. Conversely, every `P : Hermitian3` with `IsAtom (standardComplexWindow.embedding P)` equals
   `rankOneHermitian u` for some unit vector `u : Fin 3 → ℂ` (`star u ⬝ᵥ u = 1`).
3. Gram-matrix determinant formula `(P₀ + P₁ + P₂).det = (N_W : ℂ)` and
   `albertCubicNorm (emb P₀ + emb P₁ + emb P₂) = N_W`, where
   `N_W = 1 - o₀₁ - o₀₂ - o₁₂ + 2 * β.re`, `o_ab = Complex.normSq g_ab`, `β = g₀₁ * g₁₂ * star g₀₂`.
4. The eight-word expansion of `(sixProdComm (2 • P₀ - 1) (2 • P₁ - 1) (2 • P₂ - 1)).trace`
   via `AppF.rankOne_mul`, `AppF.trace_rankOne`, `Matrix.trace_mul_cycle`, `AppF.window_T1_im`,
   and `AppF.window_lambda`, proving:
   - `windowLambda (2 • P₀ - 1) (2 • P₁ - 1) (2 • P₂ - 1) = 128 * N_W * β.im`,
   - `tripleDelta (emb P₀) (emb P₁) (emb P₂) = N_W * β.im ^ 2`, and
   - `windowLambda (2 • P₀ - 1) (2 • P₁ - 1) (2 • P₂ - 1) ^ 2 = 2 ^ 14 * albertCubicNorm (emb P₀ + emb P₁ + emb P₂) * tripleDelta (emb P₀) (emb P₁) (emb P₂)`.
-/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false

noncomputable section

/-! ## Section 1: Rank-one Hermitian projections and converse atom characterization -/

/-- Rank-one Hermitian projection `u u*` in `Hermitian3`. -/
def rankOneHermitian (u : Fin 3 → ℂ) : Hermitian3 :=
  ⟨Matrix.vecMulVec u (star u), by
    ext i j
    simp [Matrix.star_apply, Matrix.vecMulVec_apply, mul_comm]⟩

@[simp] theorem rankOneHermitian_coe (u : Fin 3 → ℂ) :
    (rankOneHermitian u : ComplexMatrix3) = Matrix.vecMulVec u (star u) := rfl

theorem rankOneHermitian_mul_self (u : Fin 3 → ℂ) (hu : star u ⬝ᵥ u = 1) :
    (rankOneHermitian u : ComplexMatrix3) * (rankOneHermitian u : ComplexMatrix3) =
      rankOneHermitian u := by
  rw [rankOneHermitian_coe, rankOne_mul, hu, one_smul]

theorem rankOneHermitian_trace (u : Fin 3 → ℂ) (hu : star u ⬝ᵥ u = 1) :
    (rankOneHermitian u : ComplexMatrix3).trace = 1 := by
  rw [rankOneHermitian_coe, trace_rankOne, hu]

theorem albertTrace_standardComplexWindow (M : Hermitian3) :
    albertTrace (standardComplexWindow.embedding M) = (M : ComplexMatrix3).trace.re := by
  simp [albertTrace, complexHermToAlbert, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

theorem tracePairing_standardComplexWindow (A B : Hermitian3) :
    tracePairing (standardComplexWindow.embedding A) (standardComplexWindow.embedding B) =
      ((A : ComplexMatrix3) * (B : ComplexMatrix3)).trace.re := by
  obtain ⟨AB, hAB⟩ := standardComplexWindow.product_closed A B
  rw [tracePairing, ← standardComplexWindow.preserves_product A B AB hAB,
    albertTrace_standardComplexWindow, hAB, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_mul_comm (B : ComplexMatrix3) (A : ComplexMatrix3)]
  simp [Complex.real_smul]
  ring

theorem tracePairing_standardComplexWindow_jordanMul (A B C : Hermitian3) :
    tracePairing (standardComplexWindow.embedding A)
        (jordanMul (standardComplexWindow.embedding B) (standardComplexWindow.embedding C)) =
      (1 / 2 : ℝ) * (((A : ComplexMatrix3) * ((B : ComplexMatrix3) * C + C * B)).trace.re) := by
  obtain ⟨BC, hBC⟩ := standardComplexWindow.product_closed B C
  rw [← standardComplexWindow.preserves_product B C BC hBC,
    tracePairing_standardComplexWindow A BC, hBC, mul_smul_comm, Matrix.trace_smul,
    Complex.real_smul, Complex.mul_re]
  norm_num

theorem jordanMul_embedding_rankOneHermitian (u : Fin 3 → ℂ) (hu : star u ⬝ᵥ u = 1) :
    jordanMul (standardComplexWindow.embedding (rankOneHermitian u))
        (standardComplexWindow.embedding (rankOneHermitian u)) =
      standardComplexWindow.embedding (rankOneHermitian u) := by
  have hsq : (rankOneHermitian u : ComplexMatrix3) =
      (1 / 2 : ℝ) • ((rankOneHermitian u : ComplexMatrix3) * rankOneHermitian u +
        (rankOneHermitian u : ComplexMatrix3) * rankOneHermitian u) := by
    rw [rankOneHermitian_mul_self u hu, ← two_smul ℝ, smul_smul]
    norm_num
  exact (standardComplexWindow.preserves_product _ _ _ hsq).symm

theorem isAtom_embedding_rankOneHermitian (u : Fin 3 → ℂ) (hu : star u ⬝ᵥ u = 1) :
    IsAtom (standardComplexWindow.embedding (rankOneHermitian u)) := by
  refine ⟨jordanMul_embedding_rankOneHermitian u hu, ?_⟩
  rw [albertTrace_standardComplexWindow, rankOneHermitian_trace u hu]
  rfl

theorem exists_rankOneHermitian_of_isAtom (P : Hermitian3)
    (hP : IsAtom (standardComplexWindow.embedding P)) :
    ∃ u : Fin 3 → ℂ, star u ⬝ᵥ u = 1 ∧ P = rankOneHermitian u := by
  obtain ⟨u, hu_norm, hu_eq⟩ := complexWindow_rankOne_of_atom standardComplexWindow P hP
  refine ⟨u, ?_, ?_⟩
  · simpa [dotProduct] using hu_norm
  · apply Subtype.ext
    ext i j
    simpa [rankOneHermitian, Matrix.vecMulVec_apply] using hu_eq i j

/-! ## Section 2: Gram determinant and cubic norm on three rank-one projections -/

section ThreeUnitVectors

variable (u0 u1 u2 : Fin 3 → ℂ)
variable (hu0 : star u0 ⬝ᵥ u0 = 1) (hu1 : star u1 ⬝ᵥ u1 = 1) (hu2 : star u2 ⬝ᵥ u2 = 1)

private def vec3 : Fin 3 → Fin 3 → ℂ
  | 0 => u0
  | 1 => u1
  | 2 => u2

private def Pmat (a : Fin 3) : ComplexMatrix3 :=
  Matrix.vecMulVec (vec3 u0 u1 u2 a) (star (vec3 u0 u1 u2 a))

private def Rmat (a b : Fin 3) : ComplexMatrix3 :=
  Matrix.vecMulVec (vec3 u0 u1 u2 a) (star (vec3 u0 u1 u2 b))

private def gval (a b : Fin 3) : ℂ :=
  star (vec3 u0 u1 u2 a) ⬝ᵥ vec3 u0 u1 u2 b

private theorem gval_symm (a b : Fin 3) :
    gval u0 u1 u2 b a = star (gval u0 u1 u2 a b) := by
  simp [gval, dotProduct, Fin.sum_univ_three, mul_comm]

private theorem gval_mul_conj (a b : Fin 3) :
    gval u0 u1 u2 a b * gval u0 u1 u2 b a = (Complex.normSq (gval u0 u1 u2 a b) : ℂ) := by
  rw [gval_symm u0 u1 u2 a b, Complex.star_def, Complex.mul_conj]

private theorem gval_self (a : Fin 3)
    (hu0 : star u0 ⬝ᵥ u0 = 1) (hu1 : star u1 ⬝ᵥ u1 = 1) (hu2 : star u2 ⬝ᵥ u2 = 1) :
    gval u0 u1 u2 a a = 1 := by
  fin_cases a
  · exact hu0
  · exact hu1
  · exact hu2

private theorem Rmat_mul (a b c d : Fin 3) :
    Rmat u0 u1 u2 a b * Rmat u0 u1 u2 c d = gval u0 u1 u2 b c • Rmat u0 u1 u2 a d :=
  rankOne_mul _ _ _ _

private theorem trace_Rmat (a b : Fin 3) :
    (Rmat u0 u1 u2 a b).trace = gval u0 u1 u2 b a :=
  trace_rankOne _ _

private theorem Pmat_conjTranspose (a : Fin 3) :
    (Pmat u0 u1 u2 a).conjTranspose = Pmat u0 u1 u2 a := by
  ext i j
  simp [Pmat, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

include hu0 hu1 hu2 in
theorem det_sum_rankOneHermitian :
    let P₀ := (rankOneHermitian u0 : ComplexMatrix3)
    let P₁ := (rankOneHermitian u1 : ComplexMatrix3)
    let P₂ := (rankOneHermitian u2 : ComplexMatrix3)
    let g01 := star u0 ⬝ᵥ u1
    let g02 := star u0 ⬝ᵥ u2
    let g12 := star u1 ⬝ᵥ u2
    let β := g01 * g12 * (starRingEnd ℂ) g02
    let o01 := Complex.normSq g01
    let o02 := Complex.normSq g02
    let o12 := Complex.normSq g12
    let N_W := 1 - o01 - o02 - o12 + 2 * β.re
    (P₀ + P₁ + P₂).det = (N_W : ℂ) ∧ (P₀ + P₁ + P₂).det.re = N_W := by
  intro P₀ P₁ P₂ g01 g02 g12 β o01 o02 o12 N_W
  let M : ComplexMatrix3 := Matrix.of fun a i => star (vec3 u0 u1 u2 a i)
  have hsum : P₀ + P₁ + P₂ = M.conjTranspose * M := by
    ext i j
    simp only [P₀, P₁, P₂, rankOneHermitian_coe, M, Matrix.add_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.vecMulVec_apply,
      Fin.sum_univ_three, vec3, star_star, Pi.star_apply]
  have hgram : M * M.conjTranspose = Matrix.of (gval u0 u1 u2) := by
    ext a b
    simp only [M, gval, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      dotProduct, Fin.sum_univ_three, star_star, Pi.star_apply]
  have hdet : (P₀ + P₁ + P₂).det = (N_W : ℂ) := by
    rw [hsum, Matrix.det_mul, mul_comm, ← Matrix.det_mul, hgram, Matrix.det_fin_three]
    simp only [Matrix.of_apply, gval_self u0 u1 u2 0 hu0 hu1 hu2,
      gval_self u0 u1 u2 1 hu0 hu1 hu2, gval_self u0 u1 u2 2 hu0 hu1 hu2,
      gval_symm u0 u1 u2 0 1, gval_symm u0 u1 u2 0 2, gval_symm u0 u1 u2 1 2]
    have h01 : gval u0 u1 u2 0 1 = g01 := rfl
    have h02 : gval u0 u1 u2 0 2 = g02 := rfl
    have h12 : gval u0 u1 u2 1 2 = g12 := rfl
    rw [h01, h02, h12]
    have hn01 : g01 * star g01 = (Complex.normSq g01 : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj]
    have hn02 : g02 * star g02 = (Complex.normSq g02 : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj]
    have hn12 : g12 * star g12 = (Complex.normSq g12 : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj]
    have hβ_sum : β + star β = ((2 * β.re : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.add_conj]
    have hconj_prod : g02 * star g01 * star g12 = star β := by
      simp only [β, Complex.star_def, map_mul, RingHomCompTriple.comp_apply,
        RingHom.id_apply]
      ring
    have hβ_def : g01 * g12 * star g02 = β := rfl
    calc
      1 * 1 * 1 - 1 * g12 * star g12 - g01 * star g01 * 1 + g01 * g12 * star g02 +
          g02 * star g01 * star g12 - g02 * 1 * star g02
          = 1 + (g01 * g12 * star g02 + g02 * star g01 * star g12) -
              g12 * star g12 - g01 * star g01 - g02 * star g02 := by ring
      _ = 1 + (β + star β) - g12 * star g12 - g01 * star g01 - g02 * star g02 := by
            rw [hβ_def, hconj_prod]
      _ = 1 + ((2 * β.re : ℝ) : ℂ) - (Complex.normSq g12 : ℂ) - (Complex.normSq g01 : ℂ) -
            (Complex.normSq g02 : ℂ) := by rw [hβ_sum, hn12, hn01, hn02]
      _ = (N_W : ℂ) := by dsimp only [N_W, o01, o02, o12]; push_cast; ring
  refine ⟨hdet, ?_⟩
  rw [hdet, Complex.ofReal_re]

include hu0 hu1 hu2 in
theorem albertCubicNorm_sum_rankOneHermitian :
    let P₀ := rankOneHermitian u0
    let P₁ := rankOneHermitian u1
    let P₂ := rankOneHermitian u2
    let g01 := star u0 ⬝ᵥ u1
    let g02 := star u0 ⬝ᵥ u2
    let g12 := star u1 ⬝ᵥ u2
    let β := g01 * g12 * (starRingEnd ℂ) g02
    let o01 := Complex.normSq g01
    let o02 := Complex.normSq g02
    let o12 := Complex.normSq g12
    let N_W := 1 - o01 - o02 - o12 + 2 * β.re
    albertCubicNorm (standardComplexWindow.embedding P₀ + standardComplexWindow.embedding P₁ +
      standardComplexWindow.embedding P₂) = N_W := by
  intro P₀ P₁ P₂ g01 g02 g12 β o01 o02 o12 N_W
  rw [← map_add, ← map_add]
  have h := standardComplexWindow_albertCubicNorm_eq_det (P₀ + P₁ + P₂)
  rw [h.1]
  exact (det_sum_rankOneHermitian u0 u1 u2 hu0 hu1 hu2).2

/-! ## Section 3: Eight-word expansion for `windowLambda` and `tripleDelta` -/

private theorem trace_conjTranspose_eq (M : ComplexMatrix3) :
    M.conjTranspose.trace = star M.trace := by
  simp [Matrix.trace, Matrix.conjTranspose_apply]

include hu0 hu1 hu2 in
theorem trace_sixProdComm_symm_rankOne :
    let P₀ := (rankOneHermitian u0 : ComplexMatrix3)
    let P₁ := (rankOneHermitian u1 : ComplexMatrix3)
    let P₂ := (rankOneHermitian u2 : ComplexMatrix3)
    let g01 := star u0 ⬝ᵥ u1
    let g02 := star u0 ⬝ᵥ u2
    let g12 := star u1 ⬝ᵥ u2
    let β := g01 * g12 * (starRingEnd ℂ) g02
    let o01 := Complex.normSq g01
    let o02 := Complex.normSq g02
    let o12 := Complex.normSq g12
    let N_W := 1 - o01 - o02 - o12 + 2 * β.re
    (sixProdComm (2 • P₀ - 1) (2 • P₁ - 1) (2 • P₂ - 1)).trace =
      384 * Complex.I * ((N_W * β.im : ℝ) : ℂ) := by
  intro P₀ P₁ P₂ g01 g02 g12 β o01 o02 o12 N_W
  let C : Fin 3 → Fin 3 → ComplexMatrix3 := fun a b => Pmat u0 u1 u2 a * Pmat u0 u1 u2 b -
    Pmat u0 u1 u2 b * Pmat u0 u1 u2 a
  have hP0 : P₀ = Pmat u0 u1 u2 0 := rfl
  have hP1 : P₁ = Pmat u0 u1 u2 1 := rfl
  have hP2 : P₂ = Pmat u0 u1 u2 2 := rfl
  have hcomm_symm : ∀ a b : Fin 3,
      (2 • Pmat u0 u1 u2 a - 1) * (2 • Pmat u0 u1 u2 b - 1) -
        (2 • Pmat u0 u1 u2 b - 1) * (2 • Pmat u0 u1 u2 a - 1) =
      (4 : ℂ) • C a b := fun a b => by
    dsimp only [C]
    simp only [two_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hq01 : (2 • P₀ - 1) * (2 • P₁ - 1) - (2 • P₁ - 1) * (2 • P₀ - 1) = (4 : ℂ) • C 0 1 := by
    rw [hP0, hP1]; exact hcomm_symm 0 1
  have hq02 : (2 • P₀ - 1) * (2 • P₂ - 1) - (2 • P₂ - 1) * (2 • P₀ - 1) = (4 : ℂ) • C 0 2 := by
    rw [hP0, hP2]; exact hcomm_symm 0 2
  have hq12 : (2 • P₁ - 1) * (2 • P₂ - 1) - (2 • P₂ - 1) * (2 • P₁ - 1) = (4 : ℂ) • C 1 2 := by
    rw [hP1, hP2]; exact hcomm_symm 1 2
  let T1 : ℂ := (C 0 1 * C 0 2 * C 1 2).trace
  let T2 : ℂ := (C 0 1 * C 1 2 * C 0 2).trace
  have hC_skew : ∀ a b : Fin 3, (C a b).conjTranspose = -C a b := fun a b => by
    dsimp only [C]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Pmat_conjTranspose, Pmat_conjTranspose]
    abel
  have hcyc : (C 1 2 * C 0 2 * C 0 1).trace = T2 := by
    dsimp only [T2]
    rw [Matrix.trace_mul_comm (C 1 2 * C 0 2) (C 0 1), ← Matrix.mul_assoc]
  have hT2_eq : T2 = -(starRingEnd ℂ) T1 := by
    have hconj : (C 0 1 * C 0 2 * C 1 2).conjTranspose = -(C 1 2 * C 0 2 * C 0 1) := by
      simp only [Matrix.conjTranspose_mul, hC_skew, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
        Matrix.mul_assoc]
    have htr := trace_conjTranspose_eq (C 0 1 * C 0 2 * C 1 2)
    rw [hconj, Matrix.trace_neg] at htr
    rw [← hcyc, neg_eq_iff_eq_neg.mp htr]
    rfl
  have htrace_six :
      (sixProdComm (2 • P₀ - 1) (2 • P₁ - 1) (2 • P₂ - 1)).trace =
        (-192 : ℂ) * (T1 - (starRingEnd ℂ) T1) := by
    dsimp only [sixProdComm]
    rw [hq01, hq02, hq12]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_neg,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    have hc1 : (C 0 2 * C 1 2 * C 0 1).trace = T1 := by
      dsimp only [T1]
      rw [Matrix.trace_mul_comm (C 0 2 * C 1 2) (C 0 1), ← Matrix.mul_assoc]
    have hc2 : (C 1 2 * C 0 1 * C 0 2).trace = T1 := by
      dsimp only [T1]
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm (C 1 2) (C 0 1 * C 0 2)]
    have hc3 : (C 0 2 * C 0 1 * C 1 2).trace = T2 := by
      dsimp only [T2]
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm (C 0 2)]
    have hc4 : (C 1 2 * C 0 2 * C 0 1).trace = T2 := hcyc
    have hT1_def : (C 0 1 * C 0 2 * C 1 2).trace = T1 := rfl
    have hT2_def : (C 0 1 * C 1 2 * C 0 2).trace = T2 := rfl
    rw [hT1_def, hT2_def, hc1, hc2, hc3, hc4, hT2_eq]
    ring
  -- Compute T1 via 8-word expansion using rankOne_mul and trace_rankOne
  have hT1_val :
      T1 = 3 * ((o01 * o02 * o12 : ℝ) : ℂ) - β ^ 2 +
        (starRingEnd ℂ) β * ((1 - o01 - o02 - o12 : ℝ) : ℂ) := by
    have hP_eq : ∀ a : Fin 3, Pmat u0 u1 u2 a = Rmat u0 u1 u2 a a := fun _ => rfl
    have h8 : T1 =
        (Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 0 0 *
          Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 2 2).trace -
        (Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 0 0 *
          Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 1 1).trace -
        (Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 2 2 *
          Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 2 2).trace +
        (Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 2 2 *
          Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 1 1).trace -
        (Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 0 0 *
          Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 2 2).trace +
        (Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 0 0 *
          Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 1 1).trace +
        (Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 2 2 *
          Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 2 2).trace -
        (Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 2 2 *
          Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 1 1).trace := by
      dsimp only [T1, C]
      simp only [hP_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
      ring
    rw [h8]
    simp only [Rmat_mul, Matrix.smul_mul, trace_Rmat, Matrix.trace_smul,
      smul_eq_mul, gval_self u0 u1 u2 0 hu0 hu1 hu2, gval_self u0 u1 u2 1 hu0 hu1 hu2,
      gval_self u0 u1 u2 2 hu0 hu1 hu2]
    have hg01 : gval u0 u1 u2 0 1 = g01 := rfl
    have hg02 : gval u0 u1 u2 0 2 = g02 := rfl
    have hg12 : gval u0 u1 u2 1 2 = g12 := rfl
    have hg10 : gval u0 u1 u2 1 0 = (starRingEnd ℂ) g01 := by
      rw [gval_symm u0 u1 u2 0 1, Complex.star_def]; rfl
    have hg20 : gval u0 u1 u2 2 0 = (starRingEnd ℂ) g02 := by
      rw [gval_symm u0 u1 u2 0 2, Complex.star_def]; rfl
    have hg21 : gval u0 u1 u2 2 1 = (starRingEnd ℂ) g12 := by
      rw [gval_symm u0 u1 u2 1 2, Complex.star_def]; rfl
    have hO01 : g01 * (starRingEnd ℂ) g01 = (o01 : ℂ) := Complex.mul_conj g01
    have hO02 : g02 * (starRingEnd ℂ) g02 = (o02 : ℂ) := Complex.mul_conj g02
    have hO12 : g12 * (starRingEnd ℂ) g12 = (o12 : ℂ) := Complex.mul_conj g12
    have hβ_conj : (starRingEnd ℂ) β = (starRingEnd ℂ) g01 * (starRingEnd ℂ) g12 * g02 := by
      simp only [β, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [hg01, hg02, hg12, hg10, hg20, hg21]
    calc
      _ = 3 * ((g01 * (starRingEnd ℂ) g01) * (g02 * (starRingEnd ℂ) g02) * (g12 * (starRingEnd ℂ) g12)) -
            (g01 * g12 * (starRingEnd ℂ) g02) ^ 2 +
            ((starRingEnd ℂ) g01 * (starRingEnd ℂ) g12 * g02) *
              (1 - (g01 * (starRingEnd ℂ) g01) - (g02 * (starRingEnd ℂ) g02) - (g12 * (starRingEnd ℂ) g12)) := by
            ring
      _ = 3 * ((o01 : ℂ) * (o02 : ℂ) * (o12 : ℂ)) - β ^ 2 +
            (starRingEnd ℂ) β * (1 - (o01 : ℂ) - (o02 : ℂ) - (o12 : ℂ)) := by
            rw [hO01, hO02, hO12, ← hβ_conj]
      _ = _ := by dsimp only [o01, o02, o12]; push_cast; ring
  have hT1_im : T1.im = -(N_W * β.im) := by
    rw [hT1_val]
    exact window_T1_im g01 g02 g12
  rw [htrace_six]
  exact (window_lambda T1 N_W β.im hT1_im).1

include hu0 hu1 hu2 in
theorem windowLambda_symm_rankOne :
    let P₀ := (rankOneHermitian u0 : ComplexMatrix3)
    let P₁ := (rankOneHermitian u1 : ComplexMatrix3)
    let P₂ := (rankOneHermitian u2 : ComplexMatrix3)
    let g01 := star u0 ⬝ᵥ u1
    let g02 := star u0 ⬝ᵥ u2
    let g12 := star u1 ⬝ᵥ u2
    let β := g01 * g12 * (starRingEnd ℂ) g02
    let o01 := Complex.normSq g01
    let o02 := Complex.normSq g02
    let o12 := Complex.normSq g12
    let N_W := 1 - o01 - o02 - o12 + 2 * β.re
    windowLambda (2 • P₀ - 1) (2 • P₁ - 1) (2 • P₂ - 1) = 128 * N_W * β.im := by
  intro P₀ P₁ P₂ g01 g02 g12 β o01 o02 o12 N_W
  unfold windowLambda windowMatrixLambda
  rw [trace_sixProdComm_symm_rankOne u0 u1 u2 hu0 hu1 hu2]
  have hdiv : (384 * Complex.I * ((N_W * β.im : ℝ) : ℂ)) / Complex.I =
      ((384 * (N_W * β.im) : ℝ) : ℂ) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp
    push_cast
    ring
  rw [hdiv, Complex.ofReal_re]
  ring

include hu0 hu1 hu2 in
theorem windowLambda_symm_rankOne_sq :
    let P₀ := (rankOneHermitian u0 : ComplexMatrix3)
    let P₁ := (rankOneHermitian u1 : ComplexMatrix3)
    let P₂ := (rankOneHermitian u2 : ComplexMatrix3)
    let g01 := star u0 ⬝ᵥ u1
    let g02 := star u0 ⬝ᵥ u2
    let g12 := star u1 ⬝ᵥ u2
    let β := g01 * g12 * (starRingEnd ℂ) g02
    let o01 := Complex.normSq g01
    let o02 := Complex.normSq g02
    let o12 := Complex.normSq g12
    let N_W := 1 - o01 - o02 - o12 + 2 * β.re
    windowLambda (2 • P₀ - 1) (2 • P₁ - 1) (2 • P₂ - 1) ^ 2 =
      2 ^ 14 * N_W * (N_W * β.im ^ 2) := by
  intro P₀ P₁ P₂ g01 g02 g12 β o01 o02 o12 N_W
  dsimp only [P₀, P₁, P₂]
  rw [windowLambda_symm_rankOne u0 u1 u2 hu0 hu1 hu2]
  ring

include hu0 hu1 hu2 in
theorem tripleDelta_rankOne :
    let P₀ := rankOneHermitian u0
    let P₁ := rankOneHermitian u1
    let P₂ := rankOneHermitian u2
    let g01 := star u0 ⬝ᵥ u1
    let g02 := star u0 ⬝ᵥ u2
    let g12 := star u1 ⬝ᵥ u2
    let β := g01 * g12 * (starRingEnd ℂ) g02
    let o01 := Complex.normSq g01
    let o02 := Complex.normSq g02
    let o12 := Complex.normSq g12
    let N_W := 1 - o01 - o02 - o12 + 2 * β.re
    tripleDelta (standardComplexWindow.embedding P₀) (standardComplexWindow.embedding P₁)
      (standardComplexWindow.embedding P₂) = N_W * β.im ^ 2 := by
  intro P₀ P₁ P₂ g01 g02 g12 β o01 o02 o12 N_W
  unfold tripleDelta
  rw [albertCubicNorm_sum_rankOneHermitian u0 u1 u2 hu0 hu1 hu2,
    tracePairing_standardComplexWindow P₀ P₁,
    tracePairing_standardComplexWindow P₁ P₂,
    tracePairing_standardComplexWindow P₀ P₂,
    tracePairing_standardComplexWindow_jordanMul P₀ P₁ P₂]
  have hp : ∀ a b : Fin 3,
      (Rmat u0 u1 u2 a a * Rmat u0 u1 u2 b b).trace = (Complex.normSq (gval u0 u1 u2 a b) : ℂ) := by
    intro a b
    rw [Rmat_mul, Matrix.trace_smul, trace_Rmat, smul_eq_mul, gval_mul_conj]
  have hp01 : ((P₀ : ComplexMatrix3) * P₁).trace.re = o01 := by
    change (Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 1 1).trace.re = o01
    rw [hp 0 1, Complex.ofReal_re]; rfl
  have hp12 : ((P₁ : ComplexMatrix3) * P₂).trace.re = o12 := by
    change (Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 2 2).trace.re = o12
    rw [hp 1 2, Complex.ofReal_re]; rfl
  have hp02 : ((P₀ : ComplexMatrix3) * P₂).trace.re = o02 := by
    change (Rmat u0 u1 u2 0 0 * Rmat u0 u1 u2 2 2).trace.re = o02
    rw [hp 0 2, Complex.ofReal_re]; rfl
  have hp012 : ((P₀ : ComplexMatrix3) * ((P₁ : ComplexMatrix3) * P₂ + (P₂ : ComplexMatrix3) * P₁)).trace.re =
      2 * β.re := by
    change (Rmat u0 u1 u2 0 0 * (Rmat u0 u1 u2 1 1 * Rmat u0 u1 u2 2 2 +
      Rmat u0 u1 u2 2 2 * Rmat u0 u1 u2 1 1)).trace.re = 2 * β.re
    simp only [Matrix.mul_add, Matrix.trace_add, Rmat_mul, Matrix.mul_smul, trace_Rmat,
      Matrix.trace_smul, smul_eq_mul]
    have h1 : gval u0 u1 u2 1 2 * (gval u0 u1 u2 0 1 * gval u0 u1 u2 2 0) = β := by
      rw [gval_symm u0 u1 u2 0 2, Complex.star_def]
      change g12 * (g01 * (starRingEnd ℂ) g02) = β
      dsimp only [β]
      ring
    have h2 : gval u0 u1 u2 2 1 * (gval u0 u1 u2 0 2 * gval u0 u1 u2 1 0) = (starRingEnd ℂ) β := by
      rw [gval_symm u0 u1 u2 1 2, gval_symm u0 u1 u2 0 1, Complex.star_def]
      change (starRingEnd ℂ) g12 * (g02 * (starRingEnd ℂ) g01) = (starRingEnd ℂ) β
      simp only [β, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
      ring
    rw [Complex.add_re, h1, h2, Complex.conj_re]
    ring
  rw [hp01, hp12, hp02, hp012]
  have hnorm : Complex.normSq β = o01 * o12 * o02 := by
    dsimp only [β, o01, o12, o02]
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj]
  have hnorm2 : Complex.normSq β = β.re ^ 2 + β.im ^ 2 := by
    rw [Complex.normSq_apply, sq, sq]
  rw [← hnorm, hnorm2]
  ring

include hu0 hu1 hu2 in
theorem windowLambda_symm_rankOne_sq_eq_cubic_tripleDelta :
    let P₀ := rankOneHermitian u0
    let P₁ := rankOneHermitian u1
    let P₂ := rankOneHermitian u2
    windowLambda (2 • (P₀ : ComplexMatrix3) - 1) (2 • (P₁ : ComplexMatrix3) - 1)
        (2 • (P₂ : ComplexMatrix3) - 1) ^ 2 =
      2 ^ 14 *
        albertCubicNorm (standardComplexWindow.embedding P₀ +
          standardComplexWindow.embedding P₁ + standardComplexWindow.embedding P₂) *
        tripleDelta (standardComplexWindow.embedding P₀)
          (standardComplexWindow.embedding P₁) (standardComplexWindow.embedding P₂) := by
  intro P₀ P₁ P₂
  dsimp only [P₀, P₁, P₂]
  rw [windowLambda_symm_rankOne_sq u0 u1 u2 hu0 hu1 hu2,
    albertCubicNorm_sum_rankOneHermitian u0 u1 u2 hu0 hu1 hu2,
    tripleDelta_rankOne u0 u1 u2 hu0 hu1 hu2]

end ThreeUnitVectors

/-- Packaged Step 2 window trace identity for arbitrary rank-one atoms `P₀, P₁, P₂ : Hermitian3`. -/
theorem windowLambda_symm_sq_of_isAtom (P₀ P₁ P₂ : Hermitian3)
    (h0 : IsAtom (standardComplexWindow.embedding P₀))
    (h1 : IsAtom (standardComplexWindow.embedding P₁))
    (h2 : IsAtom (standardComplexWindow.embedding P₂)) :
    windowLambda (2 • (P₀ : ComplexMatrix3) - 1) (2 • (P₁ : ComplexMatrix3) - 1)
        (2 • (P₂ : ComplexMatrix3) - 1) ^ 2 =
      2 ^ 14 *
        albertCubicNorm (standardComplexWindow.embedding P₀ +
          standardComplexWindow.embedding P₁ + standardComplexWindow.embedding P₂) *
        tripleDelta (standardComplexWindow.embedding P₀)
          (standardComplexWindow.embedding P₁) (standardComplexWindow.embedding P₂) := by
  obtain ⟨u0, hu0, rfl⟩ := exists_rankOneHermitian_of_isAtom P₀ h0
  obtain ⟨u1, hu1, rfl⟩ := exists_rankOneHermitian_of_isAtom P₁ h1
  obtain ⟨u2, hu2, rfl⟩ := exists_rankOneHermitian_of_isAtom P₂ h2
  exact windowLambda_symm_rankOne_sq_eq_cubic_tripleDelta u0 u1 u2 hu0 hu1 hu2

end

end AlbertSequential.AppF
