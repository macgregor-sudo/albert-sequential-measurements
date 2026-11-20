module

import ReducedFrameResidualRank

open Matrix AlbertSequential
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

example (U : unitary (Matrix n n ℂ)) (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hc : ∀ i, a i ≤ 1) (e : {i // a i - a i * a i ≠ 0} ≃ m) :
    let s := fun i => Real.sqrt (a i)
    let c := fun i => Real.sqrt (1 - a i)
    let V := reducedSpectralFrame U a e.toEmbedding s c
    let W := reducedSpectralFrame U a e.toEmbedding c (fun i => -s i)
    (1 - V * Vᴴ - W * Wᴴ).rank = 0 := by
  intro s c V W
  exact (reducedSpectralFrame_residual_rank U a ha hc e.toEmbedding).trans
    (by rw [Fintype.card_congr e]; exact Nat.sub_self _)

#print axioms AlbertSequential.reducedSpectralFrame_residual_rank
