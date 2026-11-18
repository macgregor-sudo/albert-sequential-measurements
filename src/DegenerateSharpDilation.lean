/- SPDX-License-Identifier: Apache-2.0 -/
module
public import RepeatableBinaryDilation
public import SharpDilationFamilies

/-! Retraction channels and the exact zero/unit-effect projection cases.
These cases are essential for a common-corner REPEATABLE dilation. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential
open Matrix

theorem embedFirstBlock_add {d : ℕ} (X Y : ComplexMatrix d) :
    embedFirstBlock (X+Y) = embedFirstBlock X + embedFirstBlock Y := by
  simp [embedFirstBlock, Matrix.mul_add, Matrix.add_mul]

theorem embedFirstBlock_smul {d : ℕ} (c : ℂ) (X : ComplexMatrix d) :
    embedFirstBlock (c • X) = c • embedFirstBlock X := by
  simp [embedFirstBlock, Matrix.mul_smul, Matrix.smul_mul]

theorem embedFirstBlock_conjTranspose {d : ℕ} (X : ComplexMatrix d) :
    (embedFirstBlock X)ᴴ = embedFirstBlock Xᴴ := by
  simp [embedFirstBlock, Matrix.mul_assoc]

theorem embedFirstBlock_mul {d : ℕ} (X Y : ComplexMatrix d) :
    embedFirstBlock X * embedFirstBlock Y = embedFirstBlock (X*Y) := by
  unfold embedFirstBlock
  calc
    _ = firstBlockInclusion d * X *
        ((firstBlockInclusion d)ᴴ * firstBlockInclusion d) * Y *
        (firstBlockInclusion d)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [firstBlockInclusion_isometry, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem compressFirstBlock_embed {d : ℕ} (X : ComplexMatrix d) :
    compressFirstBlock (embedFirstBlock X) = X := by
  unfold compressFirstBlock embedFirstBlock
  calc
    _ = ((firstBlockInclusion d)ᴴ * firstBlockInclusion d) * X *
        ((firstBlockInclusion d)ᴴ * firstBlockInclusion d) := by simp only [Matrix.mul_assoc]
    _ = X := by simp only [firstBlockInclusion_isometry, Matrix.one_mul, Matrix.mul_one]

theorem krausAction_zero_input {d : ℕ} (K : List (ComplexMatrix d)) :
    krausAction K 0 = 0 := by
  induction K with
  | nil => rfl
  | cons V K ih => simpa only [krausAction, List.map_cons, List.sum_cons,
      Matrix.mul_zero, Matrix.zero_mul, zero_add] using ih

theorem krausAction_zero_effect {d : ℕ} (K : List (ComplexMatrix d))
    (hK : krausEffect K = 0) (X : ComplexMatrix d) : krausAction K X = 0 := by
  have hz := kraus_annihilates_effect_kernel K 1 (by rw [hK, Matrix.zero_mul])
  unfold krausAction
  apply List.sum_eq_zero
  intro Y hY
  obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hY
  have hv : V = 0 := by simpa using hz V hV
  simp [hv]

def firstCornerChannelKraus {d : ℕ} (K : List (ComplexMatrix d)) (B : ComplexMatrix d) :
    List (ComplexMatrix (d+d)) :=
  isometricCompletedKraus K (firstBlockInclusion d) (firstBlockInclusion d) (embedFirstBlock B)

theorem firstCornerChannelKraus_effect {d : ℕ}
    (K : List (ComplexMatrix d)) (B : ComplexMatrix d)
    (hK : krausEffect K = 1) (hB : Matrix.trace (B*Bᴴ) = 1) :
    krausEffect (firstCornerChannelKraus K B) = 1 := by
  apply isometricCompletedKraus_effect _ _ _ _ hK
    (firstBlockInclusion_isometry d) (firstBlockInclusion_isometry d)
  rw [embedFirstBlock_conjTranspose, embedFirstBlock_mul, trace_embedFirstBlock, hB]

theorem firstCornerChannelKraus_action {d : ℕ}
    (K : List (ComplexMatrix d)) (B : ComplexMatrix d) (Z : ComplexMatrix (d+d)) :
    krausAction (firstCornerChannelKraus K B) Z =
      embedFirstBlock (krausAction K (compressFirstBlock Z) +
        Matrix.trace ((1-firstBlockInclusion d*(firstBlockInclusion d)ᴴ)*Z) • (B*Bᴴ)) := by
  rw [firstCornerChannelKraus, isometricCompletedKraus_action _ _ _ _ _
    (firstBlockInclusion_isometry d), embedFirstBlock_conjTranspose, embedFirstBlock_mul,
    embedFirstBlock_add, embedFirstBlock_smul]
  rfl

theorem firstCornerChannelKraus_intertwining {d : ℕ}
    (K : List (ComplexMatrix d)) (B X : ComplexMatrix d) :
    krausAction (firstCornerChannelKraus K B) (embedFirstBlock X) =
      embedFirstBlock (krausAction K X) := by
  have hz : (1-firstBlockInclusion d*(firstBlockInclusion d)ᴴ) *
      firstBlockInclusion d = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
      firstBlockInclusion_isometry, Matrix.mul_one, sub_self]
  have hz' : (1-firstBlockInclusion d*(firstBlockInclusion d)ᴴ) * embedFirstBlock X = 0 := by
    unfold embedFirstBlock
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.zero_mul]
  rw [firstCornerChannelKraus_action, compressFirstBlock_embed, hz',
    Matrix.trace_zero, zero_smul, add_zero]

def degenerateKrausDilation {d : ℕ} (r : BinaryKrausRealization d Unit)
    (b : Bool) (B : ComplexMatrix d) : SharpDilationData d Unit where
  projection _ := if b then 1 else 0
  channelKraus _ _ := firstCornerChannelKraus (r.kraus () b) B

theorem degenerateKrausDilation_branch {d : ℕ} (r : BinaryKrausRealization d Unit)
    (b : Bool) (B : ComplexMatrix d) (a : Bool) (Z : ComplexMatrix (d+d)) :
    (degenerateKrausDilation r b B).branch () a Z =
      if a=b then krausAction (firstCornerChannelKraus (r.kraus () b) B) Z else 0 := by
  cases a <;> cases b <;>
    simp [SharpDilationData.branch, SharpDilationData.outcomeProjection,
      degenerateKrausDilation, krausAction_zero_input]

theorem degenerateKrausDilation_isSharpDilation {d : ℕ}
    (r : BinaryKrausRealization d Unit) (b : Bool) (B : ComplexMatrix d)
    (hE : ∀ a, krausEffect (r.kraus () a) = if a=b then 1 else 0)
    (hB : Matrix.trace (B*Bᴴ) = 1) :
    IsSharpDilation r (degenerateKrausDilation r b B) := by
  apply isSharpDilation_of_algebraic_construction
  · intro x
    cases b <;> simp [degenerateKrausDilation]
  · intro x a
    exact firstCornerChannelKraus_effect _ _ (by simpa using hE b) hB
  · intro x
    cases b <;> simp [degenerateKrausDilation, compressFirstBlock, hE,
      firstBlockInclusion_isometry]
  · intro x a Y
    cases x
    rw [degenerateKrausDilation_branch]
    by_cases hab : a=b
    · rw [ite_eq_left hab, hab, firstCornerChannelKraus_intertwining]
    · rw [ite_eq_right hab, krausAction_zero_effect _ (by simpa [hab] using hE a)]
      simp [embedFirstBlock]
  · intro x a Z
    cases x
    rw [degenerateKrausDilation_branch]
    by_cases hab : a=b
    · rw [ite_eq_left hab, firstCornerChannelKraus_action]
      exact ⟨_,rfl⟩
    · rw [ite_eq_right hab]
      exact ⟨0,by simp [embedFirstBlock]⟩

theorem degenerateKrausDilation_repeatable {d : ℕ}
    (r : BinaryKrausRealization d Unit) (b : Bool) (B : ComplexMatrix d) :
    IsRepeatableSharpDilation (degenerateKrausDilation r b B) := by
  intro x a Z hZ
  cases x
  rw [degenerateKrausDilation_branch]
  cases a <;> cases b <;>
    simp [SharpDilationData.outcomeProjection, degenerateKrausDilation]

#print axioms degenerateKrausDilation_isSharpDilation
#print axioms degenerateKrausDilation_repeatable
end AlbertSequential

