/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MeasurePrepareKraus

/-! Rectangular Kraus maps between genuinely different tagged finite blocks.
The matrices are literal coordinate inclusions; empty blocks are allowed. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace AlbertSequential
variable {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
  {ι : T → Type*} [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]

def taggedBlockInclusion (t : T) : Matrix (Σ t, ι t) (ι t) 𝕜 :=
  fun z i => if z = ⟨t,i⟩ then 1 else 0

theorem taggedBlockInclusion_same (t : T) :
    (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t).conjTranspose * taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t = 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, taggedBlockInclusion, Matrix.one_apply,
    eq_comm]

theorem taggedBlockInclusion_distinct (s t : T) (hst : s ≠ t) :
    (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose * taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t = 0 := by
  ext i j
  have hne : (⟨s,i⟩ : Sigma ι) ≠ ⟨t,j⟩ := by
    intro h
    exact hst (congrArg Sigma.fst h)
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, taggedBlockInclusion, hne,
    eq_comm]

theorem taggedBlockInclusion_complete :
    (∑ t, taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t * (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t).conjTranspose) = 1 := by
  ext x y
  rcases x with ⟨s,i⟩
  rcases y with ⟨t,j⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    taggedBlockInclusion, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]
  change (∑ c, ∑ k : ι c, if (⟨t,j⟩ : Sigma ι) = ⟨c,k⟩ then
    if (⟨s,i⟩ : Sigma ι) = ⟨c,k⟩ then (1 : 𝕜) else 0 else 0) =
    if (⟨s,i⟩ : Sigma ι) = ⟨t,j⟩ then 1 else 0
  rw [← Fintype.sum_sigma (fun z : Sigma ι =>
    if (⟨t,j⟩ : Sigma ι) = z then if (⟨s,i⟩ : Sigma ι) = z then (1 : 𝕜) else 0 else 0)]
  simp [eq_comm]
  by_cases h : (⟨s,i⟩ : Sigma ι) = ⟨t,j⟩
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

def taggedBlockKraus (s t : T) (K : Matrix (ι t) (ι s) 𝕜) :
    Matrix (Σ t, ι t) (Σ t, ι t) 𝕜 :=
  taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t * K * (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose

theorem taggedBlockKraus_effect (s t : T) (K : Matrix (ι t) (ι s) 𝕜) :
    (taggedBlockKraus s t K).conjTranspose * taggedBlockKraus s t K =
      taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s * (K.conjTranspose * K) * (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose := by
  simp only [taggedBlockKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t).conjTranspose
    (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t), taggedBlockInclusion_same, Matrix.one_mul]

theorem taggedBlockKraus_action (s t : T) (K : Matrix (ι t) (ι s) 𝕜)
    (Y : Matrix (Σ t, ι t) (Σ t, ι t) 𝕜) :
    taggedBlockKraus s t K * Y * (taggedBlockKraus s t K).conjTranspose =
    taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t * (K *
      ((taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s).conjTranspose * Y * taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) s) * K.conjTranspose) *
      (taggedBlockInclusion (𝕜 := 𝕜) (ι := ι) t).conjTranspose := by
  simp only [taggedBlockKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

end AlbertSequential
