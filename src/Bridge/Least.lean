/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.Seven
public import Bridge.C12

/-!
# `L_min = 7` from the seven-step exclusion and the ℂ¹² six-step model

Seven belongs to the set: every word of length at most seven beginning with "yes" on test `0`
has length at most seven, so `Bridge.seven_steps_bridge` (at universe `0`) excludes all real,
complex and quaternionic representations. Nothing below seven belongs to it: the ℂ¹² model of
`Bridge.six_step_model_bridge` reproduces every word of length at most six, hence at most `L`.
(The development states the same fact as `MatchingModels.LMinSeven.lMin_e3_eq_seven` for its own
model classes; it is not used here.)
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge

theorem yesFirst_subset {w : Word 4} (hw : w ∈ yesFirstUpTo 7) : w ∈ wordsUpTo 4 7 := by
  unfold yesFirstUpTo at hw
  unfold wordsUpTo
  exact hw.1

theorem wordsUpTo_mono {L L' : ℕ} (h : L ≤ L') {w : Word 4} (hw : w ∈ wordsUpTo 4 L) :
    w ∈ wordsUpTo 4 L' := by
  unfold wordsUpTo at hw ⊢
  exact le_trans hw h

theorem least_separating_bridge (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) :
    IsLeast {L : ℕ | (∀ (𝕜 : Type) (H : Type) [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : ProjectiveRepresentation 4 𝕜 H),
        ¬ ∀ w ∈ wordsUpTo 4 L, M.probability w = wordProbability p maximallyMixed w) ∧
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation 4 S),
        ¬ ∀ w ∈ wordsUpTo 4 L, M.probability w = wordProbability p maximallyMixed w)} 7 := by
  obtain ⟨⟨hH, hQ, -⟩, -⟩ := seven_steps_bridge.{0} p hp hg
  refine ⟨?_, fun L hL => ?_⟩
  · rw [Set.mem_ofPred_eq]
    exact ⟨fun 𝕜 H _ _ _ _ M h => hH 𝕜 H M (fun w hw => h w (yesFirst_subset hw)),
      fun H _ _ _ S M h => hQ H S M (fun w hw => h w (yesFirst_subset hw))⟩
  · rw [Set.mem_ofPred_eq] at hL
    by_contra hlt
    obtain ⟨M, hM⟩ := six_step_model_bridge p hp hg
    exact hL.1 ℂ (EuclideanSpace ℂ (Fin 12)) M
      (fun w hw => hM w (wordsUpTo_mono (by omega) hw))

end AlbertChallenge.Bridge
