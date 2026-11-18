/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.Shestakov
public import ThirteenTracesAndAform

/-! # `thm:glennie` in general: the statements

Typed statements; the only proof in this file is the reduction of the "any three atoms in
any order" form to the displayed form (`anyOrder_of_statement`, via the symmetry of `𝒜`).
Both statements are proved in `BlockA.GlennieGeneral` (`glennieViolationStatement_holds`,
`glennieViolationAnyOrder_holds`). Instances: `AppF.glennie_fixedS` (and the other window choices at `S`,
`AppF.GlennieSOrders`), `AppF.glennie_maximizer`.  Proved ingredients: `AppF.GlennieIngredients`. -/

@[expose] public section

namespace AlbertSequential.AppF.Pending

open AlbertSequential.AppF

/-- `thm:glennie`: for atoms `p_A, …, p_D` and `r_x = 2p_x − e`,
`‖F(r_A,r_B,r_C,r_D)‖² = 9·2²¹·N(p_A+p_B+p_C)·𝒜(p_A,p_B,p_C,p_D)`. -/
def GlennieViolationStatement : Prop :=
  ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) →
    tracePairing
        (nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3)))
        (nativeGlennieF (symmetryOf (p 0)) (symmetryOf (p 1)) (symmetryOf (p 2)) (symmetryOf (p 3))) =
      9 * 2 ^ 21 * albertCubicNorm (p 0 + p 1 + p 2) * fourPointInvariant p

/-- The "any three of the atoms, in any order" form. -/
def GlennieViolationAnyOrder : Prop :=
  ∀ (σ : Equiv.Perm (Fin 4)) (p : Fin 4 → Albert), (∀ i, IsAtom (p i)) →
    tracePairing
        (nativeGlennieF (symmetryOf (p (σ 0))) (symmetryOf (p (σ 1))) (symmetryOf (p (σ 2)))
          (symmetryOf (p (σ 3))))
        (nativeGlennieF (symmetryOf (p (σ 0))) (symmetryOf (p (σ 1))) (symmetryOf (p (σ 2)))
          (symmetryOf (p (σ 3)))) =
      9 * 2 ^ 21 * albertCubicNorm (p (σ 0) + p (σ 1) + p (σ 2)) * fourPointInvariant p

theorem anyOrder_of_statement (h : GlennieViolationStatement) : GlennieViolationAnyOrder := by
  intro σ p hp
  have := h (fun i => p (σ i)) (fun i => hp (σ i))
  rw [fourPointInvariant_perm_invariant σ p] at this
  exact this

end AlbertSequential.AppF.Pending
