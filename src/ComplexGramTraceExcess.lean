/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ThirteenTracesAndAform

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix

/-- Core Remark 5.4(b), with the Hermitian Gram matrix of arbitrary complex
unit vectors. The matrix identity also holds in dimensions below four. -/
theorem complex_dyad_trace_relation_excess {n : ℕ} (v : Fin 4 → Fin n → ℂ)
    (hv : ∀ i, star (v i) ⬝ᵥ v i = 1) :
    let P := fun i => vecMulVec (v i) (star (v i))
    let G : Matrix (Fin 4) (Fin 4) ℂ := of (fun i j => star (v i) ⬝ᵥ v j)
    let j := fun A B : Matrix (Fin n) (Fin n) ℂ => (1/2 : ℂ) • (A*B+B*A)
    let o := fun i k => (j (P i) (P k)).trace
    let R := fun i k l => (j (j (P i) (P k)) (P l)).trace
    let t := fun i k l m => (j (j (P i) (P k)) (j (P l) (P m))).trace
    (t 0 1 2 3 + t 0 2 1 3 + t 0 3 1 2) -
      (1/2 - 1/2 * (o 0 1 + o 0 2 + o 0 3 + o 1 2 + o 1 3 + o 2 3) +
       1/2 * (o 0 1 * o 2 3 + o 0 2 * o 1 3 + o 0 3 * o 1 2) +
       R 0 1 2 + R 0 1 3 + R 0 2 3 + R 1 2 3) = -(1/2 : ℂ) * G.det := by
  intro P G j o R t
  let A i k := vecMulVec (v i) (star (v k))
  let g i k := star (v i) ⬝ᵥ v k
  have hmul (i j k l : Fin 4) : A i j * A k l = g j k • A i l := by
    simp only [A,g,vecMulVec_mul_vecMulVec,vecMulVec_smul]
  have htr (i j : Fin 4) : (A i j).trace = g j i := by
    exact (trace_vecMulVec _ _).trans (dotProduct_comm _ _)
  have hG (i j) : G i j = g i j := rfl
  have hP (i) : P i = A i i := rfl
  have hdiag (i) : g i i = 1 := hv i
  dsimp only [t,o,R,j]
  simp only [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_smul, hmul, htr, smul_eq_mul]
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_four]
  simp only [Matrix.det_fin_three,Matrix.submatrix_apply,hG,Fin.succAbove,Fin.succ,Fin.castSucc,
    Fin.lt_def,Fin.val_zero,Fin.val_one,Fin.val_two]
  norm_num
  simp only [hdiag]
  ring

end AlbertSequential
