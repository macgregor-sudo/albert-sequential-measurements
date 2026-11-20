/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ScheduleMatchingSectors
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Trace

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.MatchingModels

/-- The complex two-dimensional representation using the signs of Appendix C.5. -/
def horizonPsi (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![⟨q.re, q.imI⟩, ⟨-q.imJ, -q.imK⟩], ![⟨q.imJ, -q.imK⟩, ⟨q.re, -q.imI⟩]]

theorem horizonPsi_mul (q r : Quaternion ℝ) : horizonPsi (q * r) = horizonPsi q * horizonPsi r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;> apply Complex.ext <;>
    simp [horizonPsi, Complex.mul_re, Complex.mul_im] <;> ring

theorem horizonPsi_star (q : Quaternion ℝ) :
    horizonPsi (star q) = (horizonPsi q).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.conjTranspose_apply] <;> apply Complex.ext <;> simp [horizonPsi]

private def horizonSign (i : Fin 2) : ℂ := ![1, -1] i

private theorem horizonPsi_eq_sign (q : Quaternion ℝ) (i j : Fin 2) :
    horizonPsi q i j = horizonSign i * quatMat2 q i j * horizonSign j := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [horizonSign, horizonPsi, quatMat2]

/-- The six-by-two matrix consisting of the three normalized quaternion blocks. -/
def horizonPhi (b d : ℝ) (i : Fin 4) : Matrix (Fin 6) (Fin 2) ℂ :=
  Matrix.of fun r j =>
    let p := fin3ProdFin2Equiv6.symm r
    horizonPsi (horizonQuaternionicColumns b d i p.1) p.2 j

/-- Projection in the precise basis of Appendix C.5. -/
def horizonSectorMatrix (b d : ℝ) (i : Fin 4) : Matrix (Fin 6) (Fin 6) ℂ :=
  (horizonPhi b d i) * (horizonPhi b d i).conjTranspose

private def horizonBasisSign : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal (fun i => horizonSign (fin3ProdFin2Equiv6.symm i).2)

private theorem horizonBasisSign_sq : horizonBasisSign * horizonBasisSign = 1 := by
  rw [horizonBasisSign, Matrix.diagonal_mul_diagonal]
  have hs (i : Fin 2) : horizonSign i * horizonSign i = 1 := by fin_cases i <;> simp [horizonSign]
  simp [hs, Matrix.diagonal_one]

private theorem horizonBasisSign_star : horizonBasisSign.conjTranspose = horizonBasisSign := by
  rw [horizonBasisSign, Matrix.diagonal_conjTranspose]
  have hs (i : Fin 2) : star (horizonSign i) = horizonSign i := by fin_cases i <;> simp [horizonSign]
  simp [hs]

private def horizonBasisChange (P : Matrix (Fin 6) (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  horizonBasisSign * P * horizonBasisSign

private theorem horizonBasisChange_one : horizonBasisChange 1 = 1 := by
  simpa [horizonBasisChange] using horizonBasisSign_sq

private theorem horizonBasisChange_sub (P Q : Matrix (Fin 6) (Fin 6) ℂ) :
    horizonBasisChange (P - Q) = horizonBasisChange P - horizonBasisChange Q := by
  simp [horizonBasisChange, Matrix.mul_sub, Matrix.sub_mul]

private theorem horizonBasisChange_mul (P Q : Matrix (Fin 6) (Fin 6) ℂ) :
    horizonBasisChange (P * Q) = horizonBasisChange P * horizonBasisChange Q := by
  unfold horizonBasisChange
  rw [show horizonBasisSign * P * horizonBasisSign * (horizonBasisSign * Q * horizonBasisSign) =
    horizonBasisSign * P * (horizonBasisSign * horizonBasisSign) * Q * horizonBasisSign by noncomm_ring,
    horizonBasisSign_sq, mul_one, mul_assoc horizonBasisSign P Q]

private theorem horizonBasisChange_star (P : Matrix (Fin 6) (Fin 6) ℂ) :
    (horizonBasisChange P).conjTranspose = horizonBasisChange P.conjTranspose := by
  simp [horizonBasisChange, Matrix.conjTranspose_mul, horizonBasisSign_star, Matrix.mul_assoc]

private theorem horizonBasisChange_trace (P : Matrix (Fin 6) (Fin 6) ℂ) :
    Matrix.trace (horizonBasisChange P) = Matrix.trace P := by
  rw [horizonBasisChange, Matrix.trace_mul_comm (horizonBasisSign * P),
    ← Matrix.mul_assoc, horizonBasisSign_sq, one_mul]

private theorem horizonBasisChange_wordOperator (P : Fin 4 → Matrix (Fin 6) (Fin 6) ℂ)
    (w : Word (Fin 4)) :
    wordOperator (fun i => horizonBasisChange (P i)) w =
      horizonBasisChange (wordOperator P w) := by
  have hout (a : Outcome (Fin 4)) :
      algebraicOutcome (fun i => horizonBasisChange (P i)) a =
        horizonBasisChange (algebraicOutcome P a) := by
    rcases a with ⟨i, b⟩
    cases b <;> simp [algebraicOutcome, horizonBasisChange_sub, horizonBasisChange_one]
  have hamp (v : Word (Fin 4)) :
      wordAmplitude (fun i => horizonBasisChange (P i)) v =
        horizonBasisChange (wordAmplitude P v) := by
    induction v using List.reverseRecOn with
    | nil => simp [wordAmplitude, horizonBasisChange_one]
    | append_singleton v a ih =>
      rw [wordAmplitude_append, wordAmplitude_append, wordAmplitude_singleton,
        wordAmplitude_singleton, hout, ih, horizonBasisChange_mul]
  rw [wordOperator, wordOperator, hamp, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, horizonBasisChange_star, horizonBasisChange_mul]

private theorem horizonSectorMatrix_eq_basisChange (b d : ℝ) (i : Fin 4) :
    horizonSectorMatrix b d i =
      horizonBasisChange (quatProj6 standardQuaternionicWindow (horizonQuaternionicSector b d)
        (horizonQuaternionicSector_mem b d) i) := by
  let u := horizonQuaternionicColumns b d i
  have hcoord : quatWindowEquiv standardQuaternionicWindow
      ⟨horizonQuaternionicSector b d i, horizonQuaternionicSector_mem b d i⟩ =
        horizonHermitianDyad u := by
    apply standardQuaternionicWindow.injective
    rw [quatWindowEquiv_apply_eq]
    rfl
  change horizonSectorMatrix b d i = horizonBasisChange
    (symplecticQuatMat6 ((quatWindowEquiv standardQuaternionicWindow
      ⟨horizonQuaternionicSector b d i, horizonQuaternionicSector_mem b d i⟩ : QuatHermitian3) :
        QuatMatrix3))
  rw [hcoord]
  ext r s
  rw [horizonBasisChange, horizonBasisSign, Matrix.mul_diagonal, Matrix.diagonal_mul]
  let ri := fin3ProdFin2Equiv6.symm r
  let si := fin3ProdFin2Equiv6.symm s
  change (horizonPsi (u ri.1) * (horizonPsi (u si.1)).conjTranspose) ri.2 si.2 =
    horizonSign ri.2 * quatMat2 (u ri.1 * star (u si.1)) ri.2 si.2 * horizonSign si.2
  rw [← horizonPsi_star, ← horizonPsi_mul]
  exact horizonPsi_eq_sign _ _ _

theorem horizonSectorMatrix_hermitian (b d : ℝ) (i : Fin 4) :
    (horizonSectorMatrix b d i).IsHermitian := by
  rw [Matrix.IsHermitian, horizonSectorMatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem horizonSectorMatrix_idempotent (b d : ℝ) (hd : d ^ 2 = 1 / 2) (i : Fin 4) :
    horizonSectorMatrix b d i * horizonSectorMatrix b d i = horizonSectorMatrix b d i := by
  rw [horizonSectorMatrix_eq_basisChange, ← horizonBasisChange_mul,
    quatProj6_idempotent _ _ _ (horizonQuaternionicSector_isAtom b d hd)]

theorem horizonSectorMatrix_trace (b d : ℝ) (hd : d ^ 2 = 1 / 2) (i : Fin 4) :
    Matrix.trace (horizonSectorMatrix b d i) = 2 := by
  rw [horizonSectorMatrix_eq_basisChange, horizonBasisChange_trace,
    quatProj6_trace _ _ _ (horizonQuaternionicSector_isAtom b d hd)]

theorem horizonSectorMatrix_probability (b d : ℝ) (w : Word (Fin 4)) :
    (1 / 6 : ℝ) * (Matrix.trace (wordOperator (horizonSectorMatrix b d) w)).re =
      nativeWordProbability (horizonQuaternionicSector b d) ((1 / 3 : ℝ) • albertUnit) w := by
  have h : horizonSectorMatrix b d = fun i =>
      horizonBasisChange (quatProj6 standardQuaternionicWindow (horizonQuaternionicSector b d)
        (horizonQuaternionicSector_mem b d) i) := funext (horizonSectorMatrix_eq_basisChange b d)
  rw [h, horizonBasisChange_wordOperator, horizonBasisChange_trace, quatProj6_wordProb_e3]

/-- Direct sum of the Appendix's `+` and `−` frames. -/
def horizonC12Projection (b d : ℝ) (i : Fin 4) : Matrix (Fin 12) (Fin 12) ℂ :=
  blockMat12 (horizonSectorMatrix b d i) (horizonSectorMatrix b (-d) i)

theorem horizonC12Projection_hermitian (b d : ℝ) (i : Fin 4) :
    (horizonC12Projection b d i).IsHermitian :=
  blockMat12_isHermitian (horizonSectorMatrix_hermitian b d i) (horizonSectorMatrix_hermitian b (-d) i)

theorem horizonC12Projection_idempotent (b d : ℝ) (hd : d ^ 2 = 1 / 2) (i : Fin 4) :
    horizonC12Projection b d i * horizonC12Projection b d i = horizonC12Projection b d i :=
  blockMat12_idempotent (horizonSectorMatrix_idempotent b d hd i)
    (horizonSectorMatrix_idempotent b (-d) (by simpa only [neg_sq] using hd) i)

theorem horizonC12Projection_trace (b d : ℝ) (hd : d ^ 2 = 1 / 2) (i : Fin 4) :
    Matrix.trace (horizonC12Projection b d i) = 4 := by
  rw [horizonC12Projection, blockMat12_trace, horizonSectorMatrix_trace b d hd,
    horizonSectorMatrix_trace b (-d) (by simpa only [neg_sq] using hd)]
  norm_num

private theorem matrix_rank_eq_trace {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P * P = P) : (P.rank : ℂ) = Matrix.trace P := by
  have h : IsIdempotentElem P.toLin' := by
    change (Matrix.toLinAlgEquiv' P) * (Matrix.toLinAlgEquiv' P) = Matrix.toLinAlgEquiv' P
    rw [← map_mul, hP]
  have ht := LinearMap.IsProj.trace ((LinearMap.isProj_range_iff_isIdempotentElem P.toLin').mpr h)
  rw [Matrix.trace_toLin'_eq] at ht
  change (Module.finrank ℂ (LinearMap.range P.toLin') : ℂ) = Matrix.trace P
  exact ht.symm

theorem horizonSectorMatrix_rank (b d : ℝ) (hd : d ^ 2 = 1 / 2) (i : Fin 4) :
    (horizonSectorMatrix b d i).rank = 2 := by
  exact_mod_cast (matrix_rank_eq_trace _ (horizonSectorMatrix_idempotent b d hd i)).trans
    (horizonSectorMatrix_trace b d hd i)

theorem horizonC12Projection_rank (b d : ℝ) (hd : d ^ 2 = 1 / 2) (i : Fin 4) :
    (horizonC12Projection b d i).rank = 4 := by
  exact_mod_cast (matrix_rank_eq_trace _ (horizonC12Projection_idempotent b d hd i)).trans
    (horizonC12Projection_trace b d hd i)

/-- Exact C12 projective realization with the state `Tr / 12`. -/
def horizonC12Model (b d : ℝ) (hd : d ^ 2 = 1 / 2) :
    HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)) :=
  c12TraceModel (horizonC12Projection b d) (horizonC12Projection_hermitian b d)
    (horizonC12Projection_idempotent b d hd)

theorem horizonC12Model_probability (b d : ℝ) (hd : d ^ 2 = 1 / 2) (w : Word (Fin 4)) :
    (horizonC12Model b d hd).probability w =
      (1 / 2 : ℝ) * nativeWordProbability (horizonQuaternionicSector b d)
        ((1 / 3 : ℝ) • albertUnit) w +
      (1 / 2 : ℝ) * nativeWordProbability (horizonQuaternionicSector b (-d))
        ((1 / 3 : ℝ) • albertUnit) w := by
  rw [horizonC12Model, c12TraceModel_probability,
    ← horizonSectorMatrix_probability, ← horizonSectorMatrix_probability]
  change (1 / 12 : ℝ) * (Matrix.trace (wordOperator
    (fun i => blockMat12 (horizonSectorMatrix b d i) (horizonSectorMatrix b (-d) i)) w)).re = _
  rw [blockMat12_wordOperator, blockMat12_trace, Complex.add_re]
  ring

/-- The explicitly displayed equal-weight M model and its signed-word agreement. -/
theorem horizon_M_matrix (w : Word (Fin 4)) (hw : w.length ≤ 6) :
    (horizonC12Model (Real.sqrt 2) (Real.sqrt 2)⁻¹ horizon_sign_square).probability w =
      nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w := by
  rw [horizonC12Model_probability, horizon_M_native w hw]; rfl

/-- The explicitly displayed equal-weight S model and its signed-word agreement. -/
theorem horizon_S_matrix (w : Word (Fin 4)) (hw : w.length ≤ 6) :
    (horizonC12Model 1 (Real.sqrt 2)⁻¹ horizon_sign_square).probability w =
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w := by
  rw [horizonC12Model_probability, horizon_S_native w hw]; rfl

/-- The length-seven excess for the exact Appendix matrix model of M. -/
theorem horizon_M_matrix_roundTrip_excess :
    (horizonC12Model (Real.sqrt 2) (Real.sqrt 2)⁻¹ horizon_sign_square).probability
        scheduleFirstRoundTrip -
      nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) scheduleFirstRoundTrip =
      4 / 2187 := by
  rw [horizonC12Model_probability]
  exact horizon_M_native_roundTrip_excess

/-- The length-seven excess for the exact Appendix matrix model of S. -/
theorem horizon_S_matrix_roundTrip_excess :
    (horizonC12Model 1 (Real.sqrt 2)⁻¹ horizon_sign_square).probability scheduleFirstRoundTrip -
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) scheduleFirstRoundTrip =
      1 / 486 := by
  rw [horizonC12Model_probability]
  exact horizon_S_native_roundTrip_excess

end AlbertSequential.MatchingModels
