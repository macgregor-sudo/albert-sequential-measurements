/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.Albert

/-!
# Albert-side headlines in the Challenge's terms

The four-point criterion (`ThreeAtomAndFourPoint.fourPointInvariant_nonneg`,
`fourPointInvariant_pos_iff`), the maximum (`ComplexWindowDeterminantAndMax.prop_max`,
`maximizerConfig_isAtom`, `fourPointInvariant_maximizerConfig`) and the rational quadruple
(`FixedSBinding.fixedS_isAtom`, `ThirteenTracesAndAform.fourPointInvariant_fixedS`), transported
through `Bridge.Albert`.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge

theorem atoms_toT {n : ℕ} {p : Fin n → Albert} (hp : ∀ i, IsAtom (p i)) :
    ∀ i, AlbertSequential.IsAtom ((fun i => toT (p i)) i) :=
  fun i => (isAtom_toT (p i)).2 (hp i)

theorem fourPoint_criterion_bridge (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    0 ≤ fourPointInvariant p ∧ (0 < fourPointInvariant p ↔ Generates p) := by
  rw [← fourPointInvariant_toT, ← generates_toT]
  exact ⟨AlbertSequential.fourPointInvariant_nonneg _ (atoms_toT hp),
    AlbertSequential.fourPointInvariant_pos_iff _ (atoms_toT hp)⟩

theorem fourPointInvariant_pos_of_generates {p : Fin 4 → Albert} (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) : 0 < AlbertSequential.fourPointInvariant (fun i => toT (p i)) := by
  rw [fourPointInvariant_toT]
  exact (fourPoint_criterion_bridge p hp).2.2 hg

theorem quadrupleM_toT : (fun i => toT (quadrupleM i)) = AlbertSequential.maximizerConfig :=
  quadrupleM_eq

theorem quadrupleS_toT : (fun i => toT (quadrupleS i)) = AlbertSequential.fixedS :=
  quadrupleS_eq

theorem quadrupleM_spec_bridge :
    (∀ i, IsAtom (quadrupleM i)) ∧ fourPointInvariant quadrupleM = 4 / 19683 ∧
      ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) → fourPointInvariant p ≤ 4 / 19683 := by
  refine ⟨fun i => ?_, ?_, fun p hp => ?_⟩
  · rw [← isAtom_toT]
    have h := AlbertSequential.maximizerConfig_isAtom i
    rw [← quadrupleM_toT] at h
    exact h
  · rw [← fourPointInvariant_toT, quadrupleM_toT]
    exact AlbertSequential.fourPointInvariant_maximizerConfig
  · rw [← fourPointInvariant_toT]
    exact (AlbertSequential.prop_max.1 _ (atoms_toT hp)).2

theorem quadrupleS_spec_bridge :
    (∀ i, IsAtom (quadrupleS i)) ∧ fourPointInvariant quadrupleS = 1 / 5832 := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [← isAtom_toT]
    have h := AlbertSequential.fixedS_isAtom i
    rw [← quadrupleS_toT] at h
    exact h
  · rw [← fourPointInvariant_toT, quadrupleS_toT]
    exact AlbertSequential.fourPointInvariant_fixedS

end AlbertChallenge.Bridge
