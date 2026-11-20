/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PentadArityAndHelly
public import SubalgebraCoordsAndLine
import Mathlib.Order.Lattice.Nat

public section
noncomputable section

namespace AlbertSequential

theorem finite_subset_same_generated_subalgebra (S : Set Albert) :
    ∃ T : Finset Albert, (T : Set Albert) ⊆ S ∧
      generatedSubalgebra (T : Set Albert) = generatedSubalgebra S := by
  classical
  let : Module.Finite ℝ Octonion :=
    inferInstanceAs (FiniteDimensional ℝ (Quaternion ℝ × Quaternion ℝ))
  let : Module.Finite ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  let rank (T : Finset Albert) := Module.finrank ℝ (generatedSubalgebra (T : Set Albert)).carrier
  let R : Set ℕ := {d | ∃ T : Finset Albert, (T : Set Albert) ⊆ S ∧ rank T = d}
  have hR : R.Nonempty := ⟨rank ∅, ∅, by simp, rfl⟩
  have hRb : BddAbove R := by
    refine ⟨Module.finrank ℝ Albert, ?_⟩
    rintro d ⟨T, _, rfl⟩
    exact Submodule.finrank_le _
  obtain ⟨T, hTS, hmax⟩ := Nat.sSup_mem hR hRb
  refine ⟨T, hTS, le_antisymm (generatedSubalgebra_mono hTS) (generatedSubalgebra_le ?_)⟩
  intro s hs
  let U := insert s T
  have hUS : (U : Set Albert) ⊆ S := by simpa [U, Finset.coe_insert, Set.insert_subset_iff, hs]
  have hUT : rank U ≤ rank T := by
    rw [hmax]
    exact le_csSup hRb ⟨U, hUS, rfl⟩
  have hle : generatedSubalgebra (T : Set Albert) ≤ generatedSubalgebra (U : Set Albert) :=
    generatedSubalgebra_mono (by simp [U, Finset.coe_insert, Set.subset_insert])
  have heq : generatedSubalgebra (T : Set Albert) = generatedSubalgebra (U : Set Albert) :=
    nativeJordanSubalgebra_ext (Submodule.eq_of_le_of_finrank_le hle hUT)
  rw [heq]
  exact subset_generatedSubalgebra _ (by simp [U])

theorem irredundant_subset_same_generated_subalgebra (S : Set Albert)
    (hS : ∀ p ∈ S, IsAtom p) :
    ∃ T : Finset Albert, (T : Set Albert) ⊆ S ∧ IsIrredundant T ∧
      generatedSubalgebra (T : Set Albert) = generatedSubalgebra S := by
  classical
  obtain ⟨T, hTS, hT⟩ := finite_subset_same_generated_subalgebra S
  let P (n : ℕ) := ∃ U : Finset Albert, U.card = n ∧ (U : Set Albert) ⊆ S ∧
    generatedSubalgebra (U : Set Albert) = generatedSubalgebra S
  have hP : ∃ n, P n := ⟨T.card, T, rfl, hTS, hT⟩
  obtain ⟨U, hcard, hUS, hU⟩ := Nat.find_spec hP
  refine ⟨U, hUS, (isIrredundant_iff_no_proper_same_gen U (fun p hp => hS p (hUS hp))).mpr ?_, hU⟩
  intro V hVU heq
  have hVS : (V : Set Albert) ⊆ S := (Finset.coe_subset.mpr hVU.subset).trans hUS
  have hmin := Nat.find_min' hP (show P V.card from ⟨V, rfl, hVS, heq.trans hU⟩)
  rw [← hcard] at hmin
  exact (not_lt_of_ge hmin) (Finset.card_lt_card hVU)

/-- A unital subalgebra proper in its indicated rank-three ambient algebra. -/
def LiesInProperH3 (k : CDLevel) (S : Set Albert) : Prop :=
  ∃ B : NativeJordanSubalgebra, B < H3Subalgebra k ∧ S ⊆ B.carrier

theorem liesInProperH3_iff_generated_lt (k : CDLevel) (S : Set Albert) :
    LiesInProperH3 k S ↔ generatedSubalgebra S < H3Subalgebra k := by
  constructor
  · rintro ⟨B, hB, hSB⟩
    exact lt_of_le_of_lt (generatedSubalgebra_le hSB) hB
  · intro h
    exact ⟨_, h, subset_generatedSubalgebra _⟩

/-- The finite-subset criterion quantifies over arbitrary sets of atoms in the ambient. -/
def H3HasHellyProp (k : CDLevel) (h : ℕ) : Prop :=
  ∀ S : Set Albert, (∀ p ∈ S, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier) →
    (∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ h → LiesInProperH3 k T) →
    LiesInProperH3 k S

private theorem irredundant_generating_card_le (k : CDLevel) (T : Finset Albert)
    (ha : ∀ p ∈ T, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier)
    (hi : IsIrredundant T) (hg : generatedSubalgebra (T : Set Albert) = H3Subalgebra k) :
    T.card ≤ arityBound k := by
  let R : Set ℕ := {n | ∃ U : Finset Albert, U.card = n ∧
    (∀ p ∈ U, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier) ∧
    IsIrredundant U ∧ generatedSubalgebra (U : Set Albert) = H3Subalgebra k}
  have heq : sSup R = arityBound k := prop_arity k
  have hbound : BddAbove R := by
    by_contra hn
    have hz : arityBound k = 0 := heq.symm.trans (Nat.sSup_of_not_bddAbove hn)
    cases k <;> simp [arityBound] at hz
  rw [← heq]
  exact le_csSup hbound ⟨T, rfl, ha, hi, hg⟩

theorem h3_helly_iff (k : CDLevel) (h : ℕ) : H3HasHellyProp k h ↔ arityBound k ≤ h := by
  constructor
  · intro hh
    by_contra hn
    have hlt : h < arityBound k := lt_of_not_ge hn
    obtain ⟨T, hcard, ha, hi, hg⟩ := prop_arity_lower k
    have hsmall (U : Finset Albert) (hUT : (U : Set Albert) ⊆ T) (hu : U.card ≤ h) :
        LiesInProperH3 k U := by
      rw [liesInProperH3_iff_generated_lt, ← hg]
      have hUV : U ⊂ T := by
        refine lt_of_le_of_ne (Finset.coe_subset.mp hUT) ?_
        intro heq
        rw [heq, hcard] at hu
        exact (not_le_of_gt hlt) hu
      exact lt_of_le_of_ne (generatedSubalgebra_mono hUT)
        ((isIrredundant_iff_no_proper_same_gen T (fun p hp => (ha p hp).1)).mp hi U hUV)
    have himpossible := hh T ha hsmall
    rw [liesInProperH3_iff_generated_lt, hg] at himpossible
    exact (lt_irrefl _) himpossible
  · intro h S ha hall
    have hgen : generatedSubalgebra S ≤ H3Subalgebra k := generatedSubalgebra_le (fun p hp => (ha p hp).2)
    by_cases heq : generatedSubalgebra S = H3Subalgebra k
    · obtain ⟨T, hTS, hi, hg⟩ := irredundant_subset_same_generated_subalgebra S (fun p hp => (ha p hp).1)
      have hcard := irredundant_generating_card_le k T (fun p hp => ha p (hTS hp)) hi (hg.trans heq)
      have ht := hall T hTS (hcard.trans h)
      rw [liesInProperH3_iff_generated_lt, hg, heq] at ht
      exact ((lt_irrefl _) ht).elim
    · exact (liesInProperH3_iff_generated_lt _ _).mpr (lt_of_le_of_ne hgen heq)

theorem h3_helly_number (k : CDLevel) : sInf {h | H3HasHellyProp k h} = arityBound k := by
  have hmem : arityBound k ∈ {h | H3HasHellyProp k h} := (h3_helly_iff k _).mpr le_rfl
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ fun h hh => (h3_helly_iff k h).mp hh)

theorem h3_helly_geometric (k : CDLevel) (S : Set Albert)
    (hS : ∀ p ∈ S, IsAtom p ∧ p ∈ (H3Subalgebra k).carrier) :
    LiesInProperH3 k S ↔
      ∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ arityBound k → LiesInProperH3 k T := by
  constructor
  · rintro ⟨B, hB, hSB⟩ T hTS _
    exact ⟨B, hB, hTS.trans hSB⟩
  · exact (h3_helly_iff k _).mpr le_rfl S hS

end AlbertSequential
