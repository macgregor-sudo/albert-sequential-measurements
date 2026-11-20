/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationSectors
public import CompanionLeftMultiplicationState
public import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! The literal matrices of the two quaternionic sectors. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix Kronecker
namespace AlbertSequential.NativeAnalysis

def leftModelQuaternionCoordinates (q : Quaternion ℝ) (i : Fin 4) : ℝ :=
  ![q.re, q.imI, q.imJ, q.imK] i

def quaternionCoordinateUnit (i : Fin 4) : Quaternion ℝ :=
  ⟨if i = 0 then 1 else 0, if i = 1 then 1 else 0,
    if i = 2 then 1 else 0, if i = 3 then 1 else 0⟩

def octonionLeftSectorMatrix (c d : ℝ) : Matrix OctonionCoordinate (Fin 4) ℝ :=
  fun i j => octonionRealCoordinates (octonionLeftSector c d (quaternionCoordinateUnit j)) i

theorem octonionLeftSectorMatrix_mulVec (c d : ℝ) (q : Quaternion ℝ) :
    octonionLeftSectorMatrix c d *ᵥ leftModelQuaternionCoordinates q =
      octonionRealCoordinates (octonionLeftSector c d q) := by
  funext i
  obtain ⟨i,j⟩ := i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, octonionLeftSectorMatrix,
    octonionRealCoordinates_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [leftModelQuaternionCoordinates, octonionLeftSector, quaternionCoordinateUnit]

private theorem quaternionCoordinateUnit_dot (i j : Fin 4) :
    octDot (quaternionCoordinateUnit i, 0) (quaternionCoordinateUnit j, 0) =
      (1 : Matrix (Fin 4) (Fin 4) ℝ) i j := by
  rw [octDot_eq_coords (quaternionCoordinateUnit i, 0) (quaternionCoordinateUnit j, 0)]
  fin_cases i <;> fin_cases j <;> norm_num [quaternionCoordinateUnit, Matrix.one_apply]

theorem octonionLeftSectorMatrix_gram (c d e f : ℝ) :
    (octonionLeftSectorMatrix c d)ᵀ * octonionLeftSectorMatrix e f =
      (c * e + d * f) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, octonionLeftSectorMatrix]
  rw [← octonionRealCoordinates_pairing, octonionLeftSector_pairing,
    quaternionCoordinateUnit_dot, Matrix.smul_apply, smul_eq_mul]

def leftModelSectorFrame (c d : ℝ) : LeftModelSectorFrame :=
  (1 : Matrix (Fin 3) (Fin 3) ℝ) ⊗ₖ octonionLeftSectorMatrix c d

private theorem leftModelSectorFrame_transpose (c d : ℝ) :
    (leftModelSectorFrame c d)ᵀ =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) ⊗ₖ (octonionLeftSectorMatrix c d)ᵀ := by
  rw [leftModelSectorFrame, ← Matrix.kroneckerMap_transpose, Matrix.transpose_one]

theorem leftModelSectorFrame_isometry (c d : ℝ) (h : c ^ 2 + d ^ 2 = 1) :
    (leftModelSectorFrame c d)ᵀ * leftModelSectorFrame c d = 1 := by
  rw [leftModelSectorFrame_transpose, leftModelSectorFrame, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, octonionLeftSectorMatrix_gram, ← pow_two, ← pow_two, h,
    one_smul, Matrix.one_kronecker_one]

theorem leftModelSectorFrame_orthogonal (c d : ℝ) :
    (leftModelSectorFrame c d)ᵀ * leftModelSectorFrame (-d) c = 0 := by
  rw [leftModelSectorFrame_transpose, leftModelSectorFrame, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, octonionLeftSectorMatrix_gram,
    show c * (-d) + d * c = 0 by ring, zero_smul, Matrix.kronecker_zero]

private theorem octonionLeftSectorMatrix_split (c d : ℝ) (h : c ^ 2 + d ^ 2 = 1) :
    octonionLeftSectorMatrix c d * (octonionLeftSectorMatrix c d)ᵀ +
        octonionLeftSectorMatrix (-d) c * (octonionLeftSectorMatrix (-d) c)ᵀ = 1 := by
  let S := octonionLeftSectorMatrix c d
  let T := octonionLeftSectorMatrix (-d) c
  have hs : Sᵀ * S = 1 := by
    dsimp only [S]
    rw [octonionLeftSectorMatrix_gram, ← pow_two, ← pow_two, h, one_smul]
  have ht : Tᵀ * T = 1 := by
    dsimp only [T]
    rw [octonionLeftSectorMatrix_gram, ← pow_two, ← pow_two, neg_sq, add_comm, h, one_smul]
  have hst : Sᵀ * T = 0 := by
    dsimp only [S, T]
    rw [octonionLeftSectorMatrix_gram, show c * (-d) + d * c = 0 by ring, zero_smul]
  have hts : Tᵀ * S = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hst
  change S * Sᵀ + T * Tᵀ = 1
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨p, q, hpq⟩ := octonionLeftSector_spans c d h (octonionRealCoordinates.symm x)
  have hx : S *ᵥ leftModelQuaternionCoordinates p + T *ᵥ leftModelQuaternionCoordinates q = x := by
    dsimp only [S, T]
    rw [octonionLeftSectorMatrix_mulVec, octonionLeftSectorMatrix_mulVec,
      ← map_add, hpq, LinearEquiv.apply_symm_apply]
  have hS : (S * Sᵀ + T * Tᵀ) * S = S := by
    rw [Matrix.add_mul, Matrix.mul_assoc S, Matrix.mul_assoc T, hs, hts,
      Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hT : (S * Sᵀ + T * Tᵀ) * T = T := by
    rw [Matrix.add_mul, Matrix.mul_assoc S, Matrix.mul_assoc T, hst, ht,
      Matrix.mul_zero, Matrix.mul_one, zero_add]
  rw [← hx, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS, hT]

theorem leftModelSectorFrames_split (c d : ℝ) (h : c ^ 2 + d ^ 2 = 1) :
    leftModelSectorProjection (leftModelSectorFrame c d) +
      leftModelSectorProjection (leftModelSectorFrame (-d) c) = 1 := by
  rw [leftModelSectorProjection, leftModelSectorProjection,
    leftModelSectorFrame_transpose, leftModelSectorFrame_transpose, leftModelSectorFrame,
    leftModelSectorFrame, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, ← Matrix.kronecker_add, octonionLeftSectorMatrix_split c d h,
    Matrix.one_kronecker_one]


def leftModelSpanColumn (a b : ℝ) (v : Fin 3 → Fin 4 → ℝ) : Fin 3 → Octonion :=
  fun i => leftModelSpan a b (v i 0) (v i 1) (v i 2) (v i 3)

def leftModelQuatColumn (sign : ℝ) (v : Fin 3 → Fin 4 → ℝ) : Fin 3 → Quaternion ℝ :=
  fun i => leftModelQuaternion sign (v i 0) (v i 1) (v i 2) (v i 3)

def quaternionRealLeftColumn (q : Fin 3 → Quaternion ℝ) :
    Matrix QuaternionColumnCoordinate (Fin 4) ℝ :=
  fun i j => leftModelQuaternionCoordinates (q i.1 * quaternionCoordinateUnit j) i.2

def leftModelQuaternionProjection (a b sign : ℝ) (v : Fin 3 → Fin 4 → ℝ) :
    Matrix QuaternionColumnCoordinate QuaternionColumnCoordinate ℝ :=
  let K := quaternionRealLeftColumn (leftModelQuatColumn sign v)
  (octonionColumnNormSq (leftModelSpanColumn a b v))⁻¹ • (K * Kᵀ)

theorem leftModelQuaternionProjection_transpose (a b sign : ℝ) (v : Fin 3 → Fin 4 → ℝ) :
    (leftModelQuaternionProjection a b sign v)ᵀ = leftModelQuaternionProjection a b sign v := by
  simp [leftModelQuaternionProjection, Matrix.transpose_mul]

private theorem leftModelSectorFrame_mul (c d : ℝ)
    (K : Matrix QuaternionColumnCoordinate (Fin 4) ℝ)
    (i : AlbertColumnCoordinate) (j : Fin 4) :
    (leftModelSectorFrame c d * K) i j =
      (octonionLeftSectorMatrix c d *ᵥ (fun t => K (i.1, t) j)) i.2 := by
  obtain ⟨i,k⟩ := i
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [leftModelSectorFrame, Matrix.one_apply, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_irrel]

theorem leftModelColumn_intertwines (a b sign c d : ℝ)
    (hc : a * c + b * d = sign * c) (hd : b * c - a * d = sign * d)
    (v : Fin 3 → Fin 4 → ℝ) :
    octonionLeftColumn (leftModelSpanColumn a b v) * octonionLeftSectorMatrix c d =
      leftModelSectorFrame c d * quaternionRealLeftColumn (leftModelQuatColumn sign v) := by
  ext i j
  rw [leftModelSectorFrame_mul]
  change (octonionLeftColumn (leftModelSpanColumn a b v) *ᵥ
    octonionRealCoordinates (octonionLeftSector c d (quaternionCoordinateUnit j))) i =
    (octonionLeftSectorMatrix c d *ᵥ
      leftModelQuaternionCoordinates (leftModelQuatColumn sign v i.1 * quaternionCoordinateUnit j)) i.2
  rw [octonionLeftColumn_mulVec, octonionLeftSectorMatrix_mulVec]
  dsimp only [leftModelSpanColumn, leftModelQuatColumn]
  rw [octonionLeftSector_intertwines a b sign c d hc hd]

private theorem columnAdjoint_intertwines
    (L : Matrix AlbertColumnCoordinate OctonionCoordinate ℝ)
    (S1 S2 : Matrix OctonionCoordinate (Fin 4) ℝ)
    (T1 T2 : LeftModelSectorFrame) (K1 K2 : Matrix QuaternionColumnCoordinate (Fin 4) ℝ)
    (hS : S1 * S1ᵀ + S2 * S2ᵀ = 1)
    (hT : T1ᵀ * T1 = 1) (hT' : T2ᵀ * T1 = 0)
    (e1 : L * S1 = T1 * K1) (e2 : L * S2 = T2 * K2) : Lᵀ * T1 = S1 * K1ᵀ := by
  have e1' : S1ᵀ * Lᵀ = K1ᵀ * T1ᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose e1
  have e2' : S2ᵀ * Lᵀ = K2ᵀ * T2ᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose e2
  calc
    _ = (S1 * S1ᵀ + S2 * S2ᵀ) * Lᵀ * T1 := by rw [hS, Matrix.one_mul]
    _ = S1 * ((S1ᵀ * Lᵀ) * T1) + S2 * ((S2ᵀ * Lᵀ) * T1) := by
      simp only [Matrix.add_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [e1', e2', Matrix.mul_assoc K1ᵀ, Matrix.mul_assoc K2ᵀ, hT, hT',
        Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero]

private theorem leftProjection_intertwines
    (v : Fin 3 → Octonion) (S : Matrix OctonionCoordinate (Fin 4) ℝ)
    (T : LeftModelSectorFrame) (K : Matrix QuaternionColumnCoordinate (Fin 4) ℝ)
    (h : octonionLeftColumn v * S = T * K)
    (h' : (octonionLeftColumn v)ᵀ * T = S * Kᵀ) :
    octonionLeftProjection v * T =
      T * ((octonionColumnNormSq v)⁻¹ • (K * Kᵀ)) := by
  rw [octonionLeftProjection, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h',
    ← Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem leftModelProjectionIntertwines (a b c d : ℝ)
    (h : c ^ 2 + d ^ 2 = 1)
    (hc : a * c + b * d = c) (hd : b * c - a * d = d)
    (hc' : a * (-d) + b * c = -(-d)) (hd' : b * (-d) - a * c = -c)
    (v : Fin 3 → Fin 4 → ℝ) :
    octonionLeftProjection (leftModelSpanColumn a b v) * leftModelSectorFrame c d =
      leftModelSectorFrame c d * leftModelQuaternionProjection a b 1 v ∧
    octonionLeftProjection (leftModelSpanColumn a b v) * leftModelSectorFrame (-d) c =
      leftModelSectorFrame (-d) c * leftModelQuaternionProjection a b (-1) v := by
  have e1 := leftModelColumn_intertwines a b 1 c d (by simpa using hc) (by simpa using hd) v
  have e2 := leftModelColumn_intertwines a b (-1) (-d) c
    (by simpa using hc') (by simpa using hd') v
  have ht := leftModelSectorFrame_isometry c d h
  have ht' := leftModelSectorFrame_isometry (-d) c (by simpa [add_comm] using h)
  have hst := leftModelSectorFrame_orthogonal c d
  have hts : (leftModelSectorFrame (-d) c)ᵀ * leftModelSectorFrame c d = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
      using congrArg Matrix.transpose hst
  have hsplit := octonionLeftSectorMatrix_split c d h
  refine ⟨leftProjection_intertwines _ _ _ _ e1 ?_,
    leftProjection_intertwines _ _ _ _ e2 ?_⟩
  · exact columnAdjoint_intertwines _ _ _ _ _ _ _ hsplit ht hts e1 e2
  · exact columnAdjoint_intertwines _ _ _ _ _ _ _ (by simpa only [add_comm] using hsplit) ht' hst e2 e1


theorem leftModelQuaternionColumn_normSq (a b sign : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (hs : sign ^ 2 = 1) (v : Fin 3 → Fin 4 → ℝ) :
    octonionColumnNormSq (leftModelSpanColumn a b v) =
      ∑ i, Quaternion.normSq (leftModelQuatColumn sign v i) := by
  unfold octonionColumnNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Quaternion.normSq_def']
  unfold octNormSq
  rw [octDot_eq_coords]
  dsimp [leftModelSpanColumn, leftModelQuatColumn, leftModelSpan, leftModelQuaternion]
  linear_combination (v i 3)^2 * (h - hs)

theorem octonionLeftColumn_rank (v : Fin 3 → Octonion)
    (hv : 0 < octonionColumnNormSq v) : (octonionLeftColumn v).rank = 8 := by
  classical
  rw [← Matrix.rank_transpose_mul_self, octonionLeftColumn_gram]
  have he : octonionColumnNormSq v • (1 : Matrix OctonionCoordinate OctonionCoordinate ℝ) =
      Matrix.diagonal (fun _ : OctonionCoordinate => octonionColumnNormSq v) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  rw [he, Matrix.rank_diagonal]
  exact (Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => hv.ne'))).trans octonionCoordinate_card

theorem leftModelLiteralWeightedModel {ι : Type*} (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (hb : b ≠ 0) (v : ι → Fin 3 → Fin 4 → ℝ)
    (hv : ∀ i, 0 < octonionColumnNormSq (leftModelSpanColumn a b (v i))) :
    ∃ c d : ℝ,
      let P := fun i => octonionLeftProjection (leftModelSpanColumn a b (v i))
      let QPlus := fun i => leftModelQuaternionProjection a b 1 (v i)
      let QMinus := fun i => leftModelQuaternionProjection a b (-1) (v i)
      let VPlus := leftModelSectorFrame c d
      let VMinus := leftModelSectorFrame (-d) c
      let D := leftModelDensity a VPlus VMinus
      (∀ i, (P i).rank = 8) ∧
      (leftModelSectorProjection VPlus).rank = 12 ∧
      (leftModelSectorProjection VMinus).rank = 12 ∧
      VPlusᵀ * VMinus = 0 ∧
      leftModelSectorProjection VPlus + leftModelSectorProjection VMinus = 1 ∧
      (∀ i, P i * VPlus = VPlus * QPlus i ∧ P i * VMinus = VMinus * QMinus i) ∧
      D.PosSemidef ∧ D.trace = 1 ∧
      ∀ w : Word ι, (D * wordOperator P w).trace =
        leftModelWeight a * ((wordOperator QPlus w).trace / 12) +
        (1 - leftModelWeight a) * ((wordOperator QMinus w).trace / 12) := by
  obtain ⟨c, d, hnorm, hc, hd, hc', hd'⟩ := leftModelSectorParameters a b h hb
  have ⟨ha, ha'⟩ : -1 ≤ a ∧ a ≤ 1 :=
    abs_le.mp ((sq_le_one_iff_abs_le_one a).mp (by linarith [sq_nonneg b]))
  have hPlus := leftModelSectorFrame_isometry c d hnorm
  have hMinus := leftModelSectorFrame_isometry (-d) c (by simpa [add_comm] using hnorm)
  have hP i := octonionLeftProjection_transpose (leftModelSpanColumn a b (v i))
  have hQPlus i := leftModelQuaternionProjection_transpose a b 1 (v i)
  have hQMinus i := leftModelQuaternionProjection_transpose a b (-1) (v i)
  have hPQ i := leftModelProjectionIntertwines a b c d hnorm hc hd hc' hd' (v i)
  refine ⟨c, d, ?_⟩
  dsimp only
  refine ⟨fun i => octonionLeftProjection_rank _ (hv i), leftModelSectorProjection_rank _ hPlus,
    leftModelSectorProjection_rank _ hMinus, leftModelSectorFrame_orthogonal c d,
    leftModelSectorFrames_split c d hnorm, hPQ, leftModelDensity_posSemidef a ha ha' _ _,
    leftModelDensity_trace a _ _ hPlus hMinus, ?_⟩
  exact leftModelWeightedWordProbability _ _ _ _ _ hPlus hMinus
    (fun i => show _ᴴ = _ by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hP i)
    (fun i => show _ᴴ = _ by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQPlus i)
    (fun i => show _ᴴ = _ by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hQMinus i)
    (fun i => (hPQ i).1) (fun i => (hPQ i).2) a

end AlbertSequential.NativeAnalysis
