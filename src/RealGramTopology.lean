/- SPDX-License-Identifier: Apache-2.0
The closed-PSD argument specializes the
PositiveMatrixCompactness module to the real case. -/
module

public import CanonicalGramTables
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.Compact

/-! Closedness and a division-free coordinate bound for real PSD Gram
matrices. No positive definiteness or nonzero diagonal entry is assumed. -/

@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped BigOperators

theorem isClosed_realGramPSD {I : Type*} [Fintype I] :
    IsClosed {G : Matrix I I ℝ | G.PosSemidef} := by
  classical
  have heq : {G : Matrix I I ℝ | G.PosSemidef} =
      {G : Matrix I I ℝ | G.conjTranspose = G} ∩
      ⋂ c : I → ℝ,
        {G : Matrix I I ℝ | 0 ≤ dotProduct (star c) (Matrix.mulVec G c)} := by
    ext G
    simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [heq]
  refine (isClosed_eq ?_ continuous_id).inter (isClosed_iInter fun c => ?_)
  · fun_prop
  · apply isClosed_le continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

theorem realGram_quadratic_two_coordinates {I : Type*} [Fintype I]
    {G : Matrix I I ℝ} (hG : G.PosSemidef) (i j : I) (z : ℝ) :
    0 ≤ G i i + G i j * z + z * G j i + z * G j j * z := by
  classical
  have h := hG.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j z)
  simpa [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single, single_dotProduct, Pi.star_single, add_mul, mul_add,
    add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] using h

/-- The uniform bound permits both zero diagonal entries and coincident i,j. -/
theorem realGram_entry_bounds {I : Type*} [Fintype I]
    {G : Matrix I I ℝ} (hG : G.PosSemidef)
    (hdiag : ∀ i, G i i ≤ 1) (i j : I) : -1 ≤ G i j ∧ G i j ≤ 1 := by
  have hs : G i j = G j i := by simpa using hG.isHermitian.apply j i
  have hp := realGram_quadratic_two_coordinates hG i j 1
  have hn := realGram_quadratic_two_coordinates hG i j (-1)
  have hi := hdiag i
  have hj := hdiag j
  constructor <;> nlinarith

end AlbertSequential
