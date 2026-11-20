/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.QuatPair
import Mathlib.Tactic.Ring

public section
noncomputable section

namespace AlbertSequential.MatchingModels

open scoped Matrix BigOperators

abbrev Q := Quaternion ℝ

/-- The anchored four-vector quaternionic Gram chart of Appendix C.
`z`, `u`, `v` are its BC, BD, CD entries. -/
def quatSchurGram (a b c : ℝ) (z u v : Q) : Matrix (Fin 4) (Fin 4) Q :=
  !![1,(a : Q),(b : Q),(c : Q);a,1,z,u;b,star z,1,v;c,star u,star v,1]

def quatSchurLeading (a b : ℝ) (z : Q) : Matrix (Fin 3) (Fin 3) Q :=
  !![1,(a : Q),(b : Q);a,1,z;b,star z,1]

def quatSchurLeadingDet (a b : ℝ) (z : Q) : ℝ :=
  1 - a^2 - b^2 - Quaternion.normSq z + 2*a*b*z.re

private def scalarQuaternion (r : ℝ) : Q := (r : Q)

def quatSchurCofactors (a b : ℝ) (z : Q) : Matrix (Fin 3) (Fin 3) Q :=
  !![scalarQuaternion (1 - Quaternion.normSq z), ↑b * star z - ↑a, ↑a * z - ↑b;
     ↑b * z - ↑a, scalarQuaternion (1 - b^2), scalarQuaternion (a*b) - z;
     ↑a * star z - ↑b, scalarQuaternion (a*b) - star z, scalarQuaternion (1 - a^2)]

def quatSchurTail (c : ℝ) (u v : Q) : Fin 3 → Q := ![(c : Q),u,v]

@[expose] def quatGramOverlap (Θ : Matrix (Fin 4) (Fin 4) Q) (i j : Fin 4) : ℝ :=
  Quaternion.normSq (Θ i j)

@[expose] def quatGramTriangle (Θ : Matrix (Fin 4) (Fin 4) Q) (i j k : Fin 4) : ℝ :=
  (Θ i j * Θ j k * Θ k i).re

@[expose] def quatGramCycle (Θ : Matrix (Fin 4) (Fin 4) Q) (i j k l : Fin 4) : ℝ :=
  (Θ i j * Θ j k * Θ k l * Θ l i).re

def quatGramDoublePairs (Θ : Matrix (Fin 4) (Fin 4) Q) : Fin 3 → ℝ :=
  let x := quatGramCycle Θ 0 1 2 3
  let y := quatGramCycle Θ 0 2 3 1
  let z := quatGramCycle Θ 0 3 1 2
  ![(x+y)/2,(y+z)/2,(x+z)/2]

private theorem quatSchurCofactors_right (a b : ℝ) (z : Q) :
    quatSchurLeading a b z * quatSchurCofactors a b z =
      (quatSchurLeadingDet a b z) • (1 : Matrix (Fin 3) (Fin 3) Q) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Quaternion.ext <;>
    simp [quatSchurLeading, quatSchurCofactors, quatSchurLeadingDet, scalarQuaternion, Matrix.mul_apply,
      Fin.sum_univ_three, Quaternion.normSq_def', -Quaternion.coe_pow] <;> ring

private theorem quatSchurCofactors_left (a b : ℝ) (z : Q) :
    quatSchurCofactors a b z * quatSchurLeading a b z =
      (quatSchurLeadingDet a b z) • (1 : Matrix (Fin 3) (Fin 3) Q) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Quaternion.ext <;>
    simp [quatSchurLeading, quatSchurCofactors, quatSchurLeadingDet, scalarQuaternion, Matrix.mul_apply,
      Fin.sum_univ_three, Quaternion.normSq_def', -Quaternion.coe_pow] <;> ring

def quatSchurLeadingInverse (a b : ℝ) (z : Q) : Matrix (Fin 3) (Fin 3) Q :=
  (quatSchurLeadingDet a b z)⁻¹ • quatSchurCofactors a b z

theorem quatSchurLeadingInverse_spec (a b : ℝ) (z : Q) (h : quatSchurLeadingDet a b z ≠ 0) :
    quatSchurLeading a b z * quatSchurLeadingInverse a b z = 1 ∧
      quatSchurLeadingInverse a b z * quatSchurLeading a b z = 1 := by
  constructor
  · rw [quatSchurLeadingInverse, Matrix.mul_smul, quatSchurCofactors_right, smul_smul,
      inv_mul_cancel₀ h, one_smul]
  · rw [quatSchurLeadingInverse, Matrix.smul_mul, quatSchurCofactors_left, smul_smul,
      inv_mul_cancel₀ h, one_smul]

private theorem dotProduct_smul_quat {n : Type*} [Fintype n] (r : ℝ) (v w : n → Q) :
    v ⬝ᵥ (r • w) = r • (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]

def quatSchurScalar (a b c : ℝ) (z u v : Q) : ℝ :=
  let g := quatSchurTail c u v
  1 - ((star g) ⬝ᵥ (quatSchurLeadingInverse a b z).mulVec g).re

/-- The polynomial identity holds throughout the printed affine Gram chart,
including singular leading blocks when written without an inverse. -/
theorem quatSchurTrace_polynomial (a b c : ℝ) (z u v : Q) :
    let Θ := quatSchurGram a b c z u v
    let t := quatGramDoublePairs Θ
    let g := quatSchurTail c u v
    t 0 + t 1 + t 2 - tauOf (quatGramOverlap Θ) (quatGramTriangle Θ) =
      -(1/2 : ℝ) * (quatSchurLeadingDet a b z -
        ((star g) ⬝ᵥ (quatSchurCofactors a b z).mulVec g).re) := by
  dsimp only
  simp [quatGramDoublePairs, quatGramOverlap, quatGramTriangle, quatGramCycle,
    quatSchurGram, quatSchurTail, quatSchurLeadingDet, quatSchurCofactors, scalarQuaternion, tauOf,
    dotProduct, Matrix.mulVec, Fin.sum_univ_three, Quaternion.normSq_def', -Quaternion.coe_pow]
  ring

/-- Equation (cer:schur) with the actual quaternionic inverse on the leading
block. Invertibility of that block is sufficient for this form. -/
theorem quatSchurTrace (a b c : ℝ) (z u v : Q) (h : quatSchurLeadingDet a b z ≠ 0) :
    let Θ := quatSchurGram a b c z u v
    let t := quatGramDoublePairs Θ
    t 0 + t 1 + t 2 - tauOf (quatGramOverlap Θ) (quatGramTriangle Θ) =
      -(1/2 : ℝ) * quatSchurLeadingDet a b z * quatSchurScalar a b c z u v := by
  dsimp only
  rw [quatSchurTrace_polynomial]
  unfold quatSchurScalar quatSchurLeadingInverse
  dsimp only
  rw [Matrix.smul_mulVec, dotProduct_smul_quat, Quaternion.re_smul, smul_eq_mul]
  field_simp

theorem quatSchurLeadingDet_eq_tripleNorm (a b c : ℝ) (z u v : Q) :
    let Θ := quatSchurGram a b c z u v
    quatSchurLeadingDet a b z =
      1 - quatGramOverlap Θ 0 1 - quatGramOverlap Θ 0 2 - quatGramOverlap Θ 1 2 +
        2 * quatGramTriangle Θ 0 1 2 := by
  simp [quatSchurLeadingDet, quatSchurGram, quatGramOverlap, quatGramTriangle, Quaternion.normSq_coe]
  ring

theorem quatSchurScalar_zero_iff_mem_plane (a b c : ℝ) (z u v : Q)
    (h : quatSchurLeadingDet a b z ≠ 0) :
    let Θ := quatSchurGram a b c z u v
    quatSchurScalar a b c z u v = 0 ↔
      quatGramDoublePairs Θ ∈ planePi (quatGramOverlap Θ) (quatGramTriangle Θ) := by
  dsimp only
  change _ = 0 ↔ _ + _ + _ = _
  conv_rhs => rw [← sub_eq_zero]
  rw [quatSchurTrace a b c z u v h, mul_eq_zero]
  simp [h]

end AlbertSequential.MatchingModels
