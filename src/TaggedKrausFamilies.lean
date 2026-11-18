/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TaggedBlockMatrices
public import RectangularKrausFamilies

/-! Assemble rectangular source-block Kraus families into one stationary map.
Completeness follows from the per-source effect equations on all input blocks. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace AlbertSequential
variable {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
  {ι : T → Type*} [∀ t, Fintype (ι t)] [∀ t, DecidableEq (ι t)]

theorem taggedKraus_effect (s t : T) (K : List (Matrix (ι t) (ι s) 𝕜)) :
    rectangularKrausEffect (K.map (taggedBlockKraus (ι := ι) s t)) =
      taggedBlockInclusion (ι := ι) s * rectangularKrausEffect K *
        (taggedBlockInclusion (ι := ι) s).conjTranspose := by
  induction K with
  | nil => simp [Matrix.mul_zero, Matrix.zero_mul]
  | cons V K ih =>
    simp only [List.map_cons, rectangularKrausEffect_cons, taggedBlockKraus_effect, ih,
      Matrix.mul_add, Matrix.add_mul]

theorem taggedKraus_action (s t : T) (K : List (Matrix (ι t) (ι s) 𝕜))
    (Y : Matrix (Sigma ι) (Sigma ι) 𝕜) :
    rectangularKrausAction (K.map (taggedBlockKraus (ι := ι) s t)) Y =
      taggedBlockInclusion (ι := ι) t * rectangularKrausAction K
        ((taggedBlockInclusion (ι := ι) s).conjTranspose * Y * taggedBlockInclusion s) *
          (taggedBlockInclusion (ι := ι) t).conjTranspose := by
  induction K with
  | nil => simp [Matrix.mul_zero, Matrix.zero_mul]
  | cons V K ih =>
    simp only [List.map_cons, rectangularKrausAction_cons, taggedBlockKraus_action, ih,
      Matrix.mul_add, Matrix.add_mul]

def taggedKrausList (t : T) (K : ∀ s, List (Matrix (ι t) (ι s) 𝕜)) :
    List (Matrix (Sigma ι) (Sigma ι) 𝕜) :=
  (Finset.univ.toList.map (fun s => (K s).map (taggedBlockKraus (ι := ι) s t))).flatten

theorem rectangularKrausEffect_flatten {m n : Type*} [Fintype m]
    (K : List (List (Matrix m n 𝕜))) :
    rectangularKrausEffect K.flatten = (K.map rectangularKrausEffect).sum := by
  induction K with
  | nil => rfl
  | cons L K ih => simp [rectangularKrausEffect_append, ih]

theorem rectangularKrausAction_flatten {m n : Type*} [Fintype n]
    (K : List (List (Matrix m n 𝕜))) (Y : Matrix n n 𝕜) :
    rectangularKrausAction K.flatten Y = (K.map (fun L => rectangularKrausAction L Y)).sum := by
  induction K with
  | nil => rfl
  | cons L K ih => simp [rectangularKrausAction_append, ih]

set_option backward.isDefEq.respectTransparency false in
theorem taggedKrausList_effect (t : T) (K : ∀ s, List (Matrix (ι t) (ι s) 𝕜)) :
    rectangularKrausEffect (taggedKrausList t K) =
      ∑ s, taggedBlockInclusion (ι := ι) s * rectangularKrausEffect (K s) *
        (taggedBlockInclusion (ι := ι) s).conjTranspose := by
  rw [taggedKrausList, rectangularKrausEffect_flatten, List.map_map, Finset.sum_map_toList]
  exact Finset.sum_congr rfl (fun s _ => taggedKraus_effect s t (K s))

set_option backward.isDefEq.respectTransparency false in
theorem taggedKrausList_action (t : T) (K : ∀ s, List (Matrix (ι t) (ι s) 𝕜))
    (Y : Matrix (Sigma ι) (Sigma ι) 𝕜) :
    rectangularKrausAction (taggedKrausList t K) Y =
      ∑ s, taggedBlockInclusion (ι := ι) t * rectangularKrausAction (K s)
        ((taggedBlockInclusion (ι := ι) s).conjTranspose * Y * taggedBlockInclusion s) *
          (taggedBlockInclusion (ι := ι) t).conjTranspose := by
  rw [taggedKrausList, rectangularKrausAction_flatten, List.map_map, Finset.sum_map_toList]
  exact Finset.sum_congr rfl (fun s _ => taggedKraus_action s t (K s) Y)

theorem taggedKrausList_normalized (t u : T)
    (K : ∀ s, List (Matrix (ι t) (ι s) 𝕜)) (L : ∀ s, List (Matrix (ι u) (ι s) 𝕜))
    (h : ∀ s, rectangularKrausEffect (K s) + rectangularKrausEffect (L s) = 1) :
    rectangularKrausEffect (taggedKrausList t K) +
      rectangularKrausEffect (taggedKrausList u L) = 1 := by
  rw [taggedKrausList_effect, taggedKrausList_effect, ← Finset.sum_add_distrib]
  simp_rw [← Matrix.add_mul, ← Matrix.mul_add, h]
  simpa only [Matrix.mul_one] using (taggedBlockInclusion_complete (𝕜 := 𝕜) (ι := ι))

end AlbertSequential
