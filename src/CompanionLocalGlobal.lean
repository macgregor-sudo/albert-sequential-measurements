/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThreeAtomAndFourPoint
public import FullSimplexCohomology
public import Mathlib.Tactic.FinCases

/-! The literal companion noncocycle and containment restriction maps. -/
@[expose] public section
noncomputable section

open scoped BigOperators

namespace AlbertSequential

/-- The ordered five atoms printed as the configuration `C`. -/
def companionCConfig : Fin 5 → Albert := Fin.snoc fixedS (diagAtom 2)

theorem companionCConfig_isAtom (i : Fin 5) : IsAtom (companionCConfig i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [companionCConfig, Fin.snoc_last]
    exact diagAtom_isAtom 2
  · simpa [companionCConfig] using fixedS_isAtom j

private theorem first_fixedS_orthogonal_last : jordanMul (fixedS 0) (diagAtom 2) = 0 := by
  apply (atom_tracePairing_eq_zero_iff _ _ (fixedS_isAtom 0) (diagAtom_isAtom 2)).mp
  rw [tracePairing_comm, tracePairing_diagAtom, fixedS_zero]
  rfl

private theorem second_fixedS_orthogonal_last : jordanMul (fixedS 1) (diagAtom 2) = 0 := by
  apply (atom_tracePairing_eq_zero_iff _ _ (fixedS_isAtom 1) (diagAtom_isAtom 2)).mp
  rw [tracePairing_comm, tracePairing_diagAtom, fixedS_one]
  change (1 / 2 : ℝ) * (![1, 1, 0] : Fin 3 → ℝ) 2 = 0
  norm_num

/-- Four facets contain an orthogonal pair. The fifth is the literal `fixedS`. -/
theorem companionCConfig_facetValues :
    (fun i : Fin 5 => fourPointInvariant (i.removeNth companionCConfig)) =
      ![0, 0, 0, 0, 1 / 5832] := by
  funext i
  by_cases hi : i = 4
  · subst i
    have hf : (4 : Fin 5).removeNth companionCConfig = fixedS := by
      funext j
      change companionCConfig ((Fin.last 4).succAbove j) = _
      rw [Fin.succAbove_last, companionCConfig, Fin.snoc_castSucc]
    rw [hf, fourPointInvariant_fixedS]
    rfl
  · have hatom : ∀ k, IsAtom (i.removeNth companionCConfig k) :=
      fun k => companionCConfig_isAtom (i.succAbove k)
    have hdeg : ∃ j k : Fin 4, j ≠ k ∧
        (i.removeNth companionCConfig j = i.removeNth companionCConfig k ∨
          jordanMul (i.removeNth companionCConfig j) (i.removeNth companionCConfig k) = 0) := by
      fin_cases i
      · exact ⟨0, 3, by decide, Or.inr second_fixedS_orthogonal_last⟩
      · exact ⟨0, 3, by decide, Or.inr first_fixedS_orthogonal_last⟩
      · exact ⟨0, 3, by decide, Or.inr first_fixedS_orthogonal_last⟩
      · exact ⟨0, 3, by decide, Or.inr first_fixedS_orthogonal_last⟩
      · exact (hi rfl).elim
    have hz := (fourPointInvariant_eq_zero_iff _ hatom).mpr (lemma_A_degenerate _ hatom hdeg)
    rw [hz]
    fin_cases i <;> first | rfl | exact (hi rfl).elim

/-- Ordered tuple coboundary, without imposing antisymmetry on the cochain. -/
def orderedTupleCoboundary {n : ℕ} {V : Type*} (c : (Fin (n + 1) → V) → ℝ)
    (s : Fin (n + 2) → V) : ℝ :=
  ∑ i : Fin (n + 2), (-1 : ℝ) ^ i.val * c (i.removeNth s)

def fourPointAtomCochain (s : Fin 4 → {a : Albert // IsAtom a}) : ℝ :=
  fourPointInvariant (fun i => (s i).val)

def companionCAtoms (i : Fin 5) : {a : Albert // IsAtom a} :=
  ⟨companionCConfig i, companionCConfig_isAtom i⟩

theorem companionCConfig_coboundary :
    orderedTupleCoboundary fourPointAtomCochain companionCAtoms = 1 / 5832 := by
  change (∑ i : Fin 5, (-1 : ℝ) ^ i.val * fourPointInvariant (i.removeNth companionCConfig)) = _
  simp_rw [congrFun companionCConfig_facetValues]
  norm_num [Fin.sum_univ_succ]

theorem fourPointAtomCochain_not_cocycle :
    ¬ ∀ s : Fin 5 → {a : Albert // IsAtom a}, orderedTupleCoboundary fourPointAtomCochain s = 0 := by
  intro h
  have hc := h companionCAtoms
  rw [companionCConfig_coboundary] at hc
  norm_num at hc

/-- The value of the companion's containment presheaf on a family of indices. -/
def containingQuaternionicWindows {I : Type*} (p : I → Albert) (S : Set I) :
    Set QuaternionicWindow :=
  {Q | ∀ i ∈ S, p i ∈ Q.subalgebra.carrier}

theorem containingQuaternionicWindows_antitone {I : Type*} (p : I → Albert) :
    Antitone (containingQuaternionicWindows p) :=
  fun _ _ h _ hQ i hi => hQ i (h hi)

def restrictContainingQuaternionicWindow {I : Type*} (p : I → Albert) {S T : Set I}
    (h : S ⊆ T) : containingQuaternionicWindows p T → containingQuaternionicWindows p S :=
  fun Q => ⟨Q.val, containingQuaternionicWindows_antitone p h Q.property⟩

theorem restrictContainingQuaternionicWindow_rfl {I : Type*} (p : I → Albert) {S : Set I}
    (Q : containingQuaternionicWindows p S) :
    restrictContainingQuaternionicWindow p (Set.Subset.rfl : S ⊆ S) Q = Q := rfl

theorem restrictContainingQuaternionicWindow_trans {I : Type*} (p : I → Albert)
    {R S T : Set I} (hRS : R ⊆ S) (hST : S ⊆ T) (Q : containingQuaternionicWindows p T) :
    restrictContainingQuaternionicWindow p hRS (restrictContainingQuaternionicWindow p hST Q) =
      restrictContainingQuaternionicWindow p (hRS.trans hST) Q := rfl

theorem containingQuaternionicWindows_univ_nonempty {I : Type*} (p : I → Albert) :
    (containingQuaternionicWindows p Set.univ).Nonempty ↔
      ∃ Q : QuaternionicWindow, ∀ i, p i ∈ Q.subalgebra.carrier := by
  simp [containingQuaternionicWindows, Set.Nonempty]

end AlbertSequential
