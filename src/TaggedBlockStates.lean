/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TaggedKrausFamilies

/-! Block-diagonal states with exact extraction, positivity and trace.
Cross-block coherences are neither encoded nor assumed observable. -/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential
variable {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
  {ι : T → Type*} [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]

def taggedBlockState (B : ∀ t, Matrix (ι t) (ι t) 𝕜) : Matrix (Sigma ι) (Sigma ι) 𝕜 :=
  ∑ t, taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t * B t * (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t).conjTranspose

theorem taggedBlockState_extract_same (s : T) (B : Matrix (ι s) (ι s) 𝕜) :
    (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose *
      (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s * B * (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose) *
        taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s = B := by
  calc
    _ = ((taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose * taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s) *
        B * ((taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose * taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [taggedBlockInclusion_same, Matrix.one_mul, Matrix.mul_one]

theorem taggedBlockState_extract_distinct (s t : T) (hst : s ≠ t)
    (B : Matrix (ι t) (ι t) 𝕜) :
    (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose *
      (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t * B * (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t).conjTranspose) *
        taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s = 0 := by
  calc
    _ = ((taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose * taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t) *
        B * ((taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t).conjTranspose * taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [taggedBlockInclusion_distinct s t hst, Matrix.zero_mul, Matrix.zero_mul]

theorem taggedBlockState_extract (B : ∀ t, Matrix (ι t) (ι t) 𝕜) (s : T) :
    (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose * taggedBlockState B *
      taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s = B s := by
  rw [taggedBlockState, Matrix.mul_sum, Matrix.sum_mul, Finset.sum_eq_single s]
  · exact taggedBlockState_extract_same s (B s)
  · intro t _ hts
    exact taggedBlockState_extract_distinct s t (Ne.symm hts) (B t)
  · simp

theorem taggedBlockState_trace (B : ∀ t, Matrix (ι t) (ι t) 𝕜) :
    Matrix.trace (taggedBlockState B) = ∑ t, Matrix.trace (B t) := by
  rw [taggedBlockState, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, taggedBlockInclusion_same, Matrix.one_mul]

theorem taggedBlockState_positive (B : ∀ t, Matrix (ι t) (ι t) 𝕜)
    (hB : ∀ t, (B t).PosSemidef) : (taggedBlockState B).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun t _ => (hB t).mul_mul_conjTranspose_same _)

theorem taggedBlockState_single (s : T) (B : Matrix (ι s) (ι s) 𝕜) :
    taggedBlockState (Pi.single s B) =
      taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s * B * (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose := by
  unfold taggedBlockState
  rw [Finset.sum_eq_single s]
  · rw [Pi.single_eq_same]
  · intro t _ hts
    rw [Pi.single_eq_of_ne hts, Matrix.mul_zero, Matrix.zero_mul]
  · simp

end AlbertSequential
