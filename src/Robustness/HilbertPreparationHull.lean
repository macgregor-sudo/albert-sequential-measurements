/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Robustness.PreparationHull
public import Robustness.ComplexSharpDisturbance
public import Robustness.QuaternionicSharpDisturbance

/-! Preparation hulls on the physical real, complex, and right-quaternionic trace-class carriers. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.HilbertTrace

open PreparationHull SharpDisturbance
open scoped ENNReal

section Real

variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis B ℝ H) (M : I → RealInstrument b)

def realPreparationHull (initial : signedFiniteTrace b) : Set (signedFiniteTrace b) :=
  traceNormPreparationHull (realTraceNorm b) (signedTrace b) (realBranch b M) initial

theorem real_word_readout_lipschitz (x y : signedFiniteTrace b) (w : Word I) :
    |signedTrace b (wordMap (realBranch b M) w x) - signedTrace b (wordMap (realBranch b M) w y)| ≤
      realTraceNorm b (x - y) := by
  let C := {x : signedFiniteTrace b | x.val.IsPositive}
  apply word_readout_lipschitz_of_decomposition (C := C) (signedTrace b) (realBranch b M) (realTraceNorm b)
  · intro X hX
    rw [signedTrace_eq_positiveTrace_toReal b X hX]
    exact ENNReal.toReal_nonneg
  · rintro ⟨i,a⟩ X hX
    cases a
    · exact (M i).zero_positive X hX
    · exact (M i).one_positive X hX
  · rintro ⟨i,a⟩ X hX
    cases a
    · change signedTrace b ((M i).branchZero X) ≤ _
      rw [(M i).signedTrace_branchZero b X]
      linarith [((M i).massOne_dominated b X hX).1]
    · exact ((M i).massOne_dominated b X hX).2
  · intro X
    let D := Classical.choose (realModulus_exists b X)
    obtain ⟨hD, hs⟩ := Classical.choose_spec (realModulus_exists b X)
    obtain ⟨u, v, hu, hv, he, hm⟩ := real_signedTrace_jordan_decomposition b X D hD hs
    exact ⟨u, hu, v, hv, he, hm⟩

theorem real_native_table_of_preparationHull (p : I → Albert) (initial z : signedFiniteTrace b)
    (hmatch : ∀ w, signedTrace b (wordMap (realBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ realPreparationHull b M initial) :
    ∃ ρ ∈ nativeReachableStateSpace p, ∀ w,
      signedTrace b (wordMap (realBranch b M) w z) = nativeWordProbability p ρ w :=
  native_table_of_mem_traceNormPreparationHull p (signedTrace b) (realBranch b M) initial
    (realTraceNorm b) hmatch (real_word_readout_lipschitz b M) hz

theorem real_preparationHull_certainty (p : I → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : signedFiniteTrace b)
    (hmatch : ∀ w, signedTrace b (wordMap (realBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ realPreparationHull b M initial) (q : Outcome I)
    (hq : signedTrace b (realBranch b M q z) = 1) (u : Word I) :
    signedTrace b (wordMap (realBranch b M) (q :: u) z) = signedTrace b (wordMap (realBranch b M) u z) :=
  certainty_in_traceNormPreparationHull p (fun i => (hp i).1) (signedTrace b) (realBranch b M) initial
    (realTraceNorm b) hmatch (real_word_readout_lipschitz b M) hz q hq u

theorem real_certain_disturbed_not_mem_preparationHull (p : I → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : signedFiniteTrace b)
    (hmatch : ∀ w, signedTrace b (wordMap (realBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (q : Outcome I) (hq : signedTrace b (realBranch b M q z) = 1) (u : Word I)
    (hd : signedTrace b (wordMap (realBranch b M) (q :: u) z) ≠ signedTrace b (wordMap (realBranch b M) u z)) :
    z ∉ realPreparationHull b M initial :=
  fun hz => hd (real_preparationHull_certainty b M p hp initial z hmatch hz q hq u)

end Real

section Complex

variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis B ℂ H) (M : I → ComplexInstrument b)

def complexPreparationHull (initial : signedFiniteTrace b) : Set (signedFiniteTrace b) :=
  traceNormPreparationHull (complexTraceNorm b) (signedTrace b) (complexBranch b M) initial

theorem complex_word_readout_lipschitz (x y : signedFiniteTrace b) (w : Word I) :
    |signedTrace b (wordMap (complexBranch b M) w x) - signedTrace b (wordMap (complexBranch b M) w y)| ≤
      complexTraceNorm b (x - y) := by
  let C := {x : signedFiniteTrace b | x.val.IsPositive}
  apply word_readout_lipschitz_of_decomposition (C := C) (signedTrace b) (complexBranch b M) (complexTraceNorm b)
  · intro X hX
    rw [signedTrace_eq_positiveTrace_toReal b X hX]
    exact ENNReal.toReal_nonneg
  · rintro ⟨i,a⟩ X hX
    cases a
    · exact (M i).zero_positive X hX
    · exact (M i).one_positive X hX
  · rintro ⟨i,a⟩ X hX
    cases a
    · change signedTrace b ((M i).branchZero X) ≤ _
      rw [(M i).signedTrace_branchZero b X]
      linarith [((M i).massOne_dominated b X hX).1]
    · exact ((M i).massOne_dominated b X hX).2
  · intro X
    obtain ⟨u, v, hu, hv, he, hm⟩ := complex_signedTrace_jordan_decomposition b X
    exact ⟨u, hu, v, hv, he, hm⟩

theorem complex_native_table_of_preparationHull (p : I → Albert) (initial z : signedFiniteTrace b)
    (hmatch : ∀ w, signedTrace b (wordMap (complexBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ complexPreparationHull b M initial) :
    ∃ ρ ∈ nativeReachableStateSpace p, ∀ w,
      signedTrace b (wordMap (complexBranch b M) w z) = nativeWordProbability p ρ w :=
  native_table_of_mem_traceNormPreparationHull p (signedTrace b) (complexBranch b M) initial
    (complexTraceNorm b) hmatch (complex_word_readout_lipschitz b M) hz

theorem complex_preparationHull_certainty (p : I → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : signedFiniteTrace b)
    (hmatch : ∀ w, signedTrace b (wordMap (complexBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ complexPreparationHull b M initial) (q : Outcome I)
    (hq : signedTrace b (complexBranch b M q z) = 1) (u : Word I) :
    signedTrace b (wordMap (complexBranch b M) (q :: u) z) = signedTrace b (wordMap (complexBranch b M) u z) :=
  certainty_in_traceNormPreparationHull p (fun i => (hp i).1) (signedTrace b) (complexBranch b M) initial
    (complexTraceNorm b) hmatch (complex_word_readout_lipschitz b M) hz q hq u

theorem complex_certain_disturbed_not_mem_preparationHull (p : I → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : signedFiniteTrace b)
    (hmatch : ∀ w, signedTrace b (wordMap (complexBranch b M) w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (q : Outcome I) (hq : signedTrace b (complexBranch b M q z) = 1) (u : Word I)
    (hd : signedTrace b (wordMap (complexBranch b M) (q :: u) z) ≠
      signedTrace b (wordMap (complexBranch b M) u z)) : z ∉ complexPreparationHull b M initial :=
  fun hz => hd (complex_preparationHull_certainty b M p hp initial z hmatch hz q hq u)

end Complex

section Quaternionic

variable {H B I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis B ℝ H) (S : RightQuaternionicHilbertStructure H)
variable (M : I → QuaternionicInstrument b S)

local notation "Carrier" => quaternionicSignedFiniteTrace b S
local notation "qTrace" => quaternionicSignedTrace b S
local notation "qBranch" => quaternionicBranch b S M

def quaternionicPreparationHull (initial : Carrier) : Set Carrier :=
  traceNormPreparationHull (quaternionicTraceNorm b S) qTrace qBranch initial

theorem quaternionic_word_readout_lipschitz (x y : Carrier) (w : Word I) :
    |qTrace (wordMap qBranch w x) - qTrace (wordMap qBranch w y)| ≤ quaternionicTraceNorm b S (x - y) := by
  let C := {x : Carrier | x.val.IsPositive}
  apply word_readout_lipschitz_of_decomposition (C := C) qTrace qBranch (quaternionicTraceNorm b S)
  · intro X hX
    change 0 ≤ (1 / 4 : ℝ) * signedTrace b (quaternionicCarrierInclusion b S X)
    rw [signedTrace_eq_positiveTrace_toReal b _ hX]
    positivity
  · rintro ⟨i,a⟩ X hX
    cases a
    · exact (M i).zero_positive X hX
    · exact (M i).one_positive X hX
  · rintro ⟨i,a⟩ X hX
    cases a
    · change qTrace ((M i).branchZero X) ≤ _
      rw [(M i).signedTrace_branchZero b S X]
      linarith [((M i).massOne_dominated b S X hX).1]
    · exact ((M i).massOne_dominated b S X hX).2
  · intro X
    obtain ⟨u, v, hu, hv, he, hm⟩ := quaternionic_signedTrace_jordan_decomposition b S X
    exact ⟨u, hu, v, hv, he, hm⟩

theorem quaternionic_native_table_of_preparationHull (p : I → Albert) (initial z : Carrier)
    (hmatch : ∀ w, qTrace (wordMap qBranch w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ quaternionicPreparationHull b S M initial) :
    ∃ ρ ∈ nativeReachableStateSpace p, ∀ w, qTrace (wordMap qBranch w z) = nativeWordProbability p ρ w :=
  native_table_of_mem_traceNormPreparationHull p qTrace qBranch initial (quaternionicTraceNorm b S)
    hmatch (quaternionic_word_readout_lipschitz b S M) hz

theorem quaternionic_preparationHull_certainty (p : I → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : Carrier)
    (hmatch : ∀ w, qTrace (wordMap qBranch w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (hz : z ∈ quaternionicPreparationHull b S M initial) (q : Outcome I)
    (hq : qTrace (qBranch q z) = 1) (u : Word I) :
    qTrace (wordMap qBranch (q :: u) z) = qTrace (wordMap qBranch u z) :=
  certainty_in_traceNormPreparationHull p (fun i => (hp i).1) qTrace qBranch initial (quaternionicTraceNorm b S)
    hmatch (quaternionic_word_readout_lipschitz b S M) hz q hq u

theorem quaternionic_certain_disturbed_not_mem_preparationHull (p : I → Albert) (hp : ∀ i, IsAtom (p i))
    (initial z : Carrier)
    (hmatch : ∀ w, qTrace (wordMap qBranch w initial) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)
    (q : Outcome I) (hq : qTrace (qBranch q z) = 1) (u : Word I)
    (hd : qTrace (wordMap qBranch (q :: u) z) ≠ qTrace (wordMap qBranch u z)) :
    z ∉ quaternionicPreparationHull b S M initial :=
  fun hz => hd (quaternionic_preparationHull_certainty b S M p hp initial z hmatch hz q hq u)

end Quaternionic

end AlbertSequential.HilbertTrace
