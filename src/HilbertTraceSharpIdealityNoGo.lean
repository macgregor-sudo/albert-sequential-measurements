/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AlgebraicProjectiveNoGo
public import Robustness.ComplexTraceProjectiveWords
public import Robustness.ComplexSharpDisturbance
public import Robustness.QuaternionicSharpDisturbance

/-! A sharp trace-class simulator of a generating Albert menu must disturb
some state in a certainty face. The result holds over all three fields. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.HilbertTrace

open SharpDisturbance

section Real

variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis B ℝ H)
local notation "Op" => H →L[ℝ] H
local notation "Carrier" => signedFiniteTrace b
local notation "tr" => signedTrace b
local notation "pair" => signedTracePairing b

private theorem realInstrument_idealTest_of_sharp_fixed_faces
    (M : RealInstrument b) (P : Op) (hP : IsStarProjection P)
    (hmass : ∀ X, M.massOne b X = pair P X)
    (hone : ∀ X, IsRealDensity b X → tr (M.branchOne X) = 1 → M.branchOne X = X)
    (hzero : ∀ X, IsRealDensity b X → tr (M.branchZero X) = 1 → M.branchZero X = X) :
    M.IsIdealTest b := by
  have hsand (Q : Op) (hQ : IsStarProjection Q) (X : Carrier) :
      tr (realSandwich b Q X) = pair Q X := by
    rw [signedTrace_realSandwich, hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq]
  let L : RealInstrument b :=
    { branchOne := realSandwich b P
      branchZero := realSandwich b (1-P)
      one_positive := realSandwich_positive b P
      zero_positive := realSandwich_positive b (1-P)
      trace_preserving X := by
        rw [map_add, hsand P hP, hsand (1-P) hP.one_sub, realTracePairing_complement_eq]
        ring }
  have hL (X : Carrier) : L.massOne b X = pair P X := hsand P hP X
  have hLI : L.IsIdealTest b :=
    (RealInstrument.idealTest_iff_projection b L).mpr ⟨P,hP,rfl,rfl,hL⟩
  refine ⟨hone, ?_, ?_⟩
  · intro X hX h0
    apply hzero X hX
    rw [M.signedTrace_branchZero b, hX.2, h0, sub_zero]
  · rintro ⟨X,F,hX,hF,hFX,hvanish⟩
    apply hLI.2.2
    refine ⟨X,F,hX,hF,hFX,fun Y hY hcert => hvanish Y hY ?_⟩
    simpa only [hmass Y, hL Y] using hcert

/-- Whole-face ideality fails for a sharp trace-class realization of the
generating Albert menu over real Hilbert space. -/
theorem real_sharp_simulator_ideality_failure {I : Type*}
    (p : I → Albert) (hp : ∀ i, IsAtom (p i)) (hgen : GeneratesAlbert p) (ρ : Albert)
    (M : I → RealInstrument b) (P : I → Op) (hP : ∀ i, IsStarProjection (P i))
    (hmass : ∀ i X, (M i).massOne b X = pair (P i) X)
    (initial : Carrier) (hd : IsRealDensity b initial)
    (hword : ∀ w, tr (wordMap (realBranch b M) w initial) = nativeWordProbability p ρ w) :
    ∃ (q : Outcome I) (X : Carrier),
      IsRealDensity b X ∧ tr (realBranch b M q X) = 1 ∧ realBranch b M q X ≠ X := by
  classical
  by_contra! hfixed
  have hi (i : I) : (M i).IsIdealTest b := by
    apply realInstrument_idealTest_of_sharp_fixed_faces b (M i) (P i) (hP i) (hmass i)
    · exact hfixed (i,true)
    · exact hfixed (i,false)
  have hfamily (i : I) := (RealInstrument.idealTest_iff_projection b (M i)).mp (hi i)
  choose Q hQ h1 h0 htrace using hfamily
  have hmaps : realBranch b M = fun q => realSandwich b (algebraicOutcome Q q) := by
    funext q
    rcases q with ⟨i,a⟩
    cases a
    · exact h0 i
    · exact h1 i
  let N := realTraceProjectiveModel b Q hQ initial hd
  apply algebraicProjective_not_matches_generating_atoms N.toAlgebraic p hp hgen ρ
  intro w
  rw [N.toAlgebraic_probability]
  dsimp only [N]
  rw [realTraceProjectiveModel_probability, ← hmaps]
  exact hword w

end Real

section Complex

variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis B ℂ H)
local notation "Op" => H →L[ℂ] H
local notation "Carrier" => signedFiniteTrace b
local notation "tr" => signedTrace b
local notation "pair" => signedTracePairing b

private theorem complexInstrument_idealTest_of_sharp_fixed_faces
    (M : ComplexInstrument b) (P : Op) (hP : IsStarProjection P)
    (hmass : ∀ X, M.massOne b X = pair P X)
    (hone : ∀ X, IsComplexDensity b X → tr (M.branchOne X) = 1 → M.branchOne X = X)
    (hzero : ∀ X, IsComplexDensity b X → tr (M.branchZero X) = 1 → M.branchZero X = X) :
    M.IsIdealTest b := by
  have hsand (Q : Op) (hQ : IsStarProjection Q) (X : Carrier) :
      tr (complexSandwich b Q X) = pair Q X := by
    rw [signedTrace_complexSandwich, hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq]
  let L : ComplexInstrument b :=
    { branchOne := complexSandwich b P
      branchZero := complexSandwich b (1-P)
      one_positive := complexSandwich_positive b P
      zero_positive := complexSandwich_positive b (1-P)
      trace_preserving X := by
        rw [map_add, hsand P hP, hsand (1-P) hP.one_sub, complexTracePairing_complement_eq]
        ring }
  have hL (X : Carrier) : L.massOne b X = pair P X := hsand P hP X
  have hLI : L.IsIdealTest b :=
    (ComplexInstrument.idealTest_iff_projection b L).mpr ⟨P,hP,rfl,rfl,hL⟩
  refine ⟨hone, ?_, ?_⟩
  · intro X hX h0
    apply hzero X hX
    rw [M.signedTrace_branchZero b, hX.2, h0, sub_zero]
  · rintro ⟨X,F,hX,hF,hFX,hvanish⟩
    apply hLI.2.2
    refine ⟨X,F,hX,hF,hFX,fun Y hY hcert => hvanish Y hY ?_⟩
    simpa only [hmass Y, hL Y] using hcert

/-- Whole-face ideality fails for a sharp trace-class realization of the
generating Albert menu over complex Hilbert space. -/
theorem complex_sharp_simulator_ideality_failure {I : Type*}
    (p : I → Albert) (hp : ∀ i, IsAtom (p i)) (hgen : GeneratesAlbert p) (ρ : Albert)
    (M : I → ComplexInstrument b) (P : I → Op) (hP : ∀ i, IsStarProjection (P i))
    (hmass : ∀ i X, (M i).massOne b X = pair (P i) X)
    (initial : Carrier) (hd : IsComplexDensity b initial)
    (hword : ∀ w, tr (wordMap (complexBranch b M) w initial) = nativeWordProbability p ρ w) :
    ∃ (q : Outcome I) (X : Carrier),
      IsComplexDensity b X ∧ tr (complexBranch b M q X) = 1 ∧ complexBranch b M q X ≠ X := by
  classical
  by_contra! hfixed
  have hi (i : I) : (M i).IsIdealTest b := by
    apply complexInstrument_idealTest_of_sharp_fixed_faces b (M i) (P i) (hP i) (hmass i)
    · exact hfixed (i,true)
    · exact hfixed (i,false)
  have hfamily (i : I) := (ComplexInstrument.idealTest_iff_projection b (M i)).mp (hi i)
  choose Q hQ h1 h0 htrace using hfamily
  have hmaps : complexBranch b M = fun q => complexSandwich b (algebraicOutcome Q q) := by
    funext q
    rcases q with ⟨i,a⟩
    cases a
    · exact h0 i
    · exact h1 i
  let N := complexTraceProjectiveModel b Q hQ initial hd
  apply algebraicProjective_not_matches_generating_atoms N.toAlgebraic p hp hgen ρ
  intro w
  rw [N.toAlgebraic_probability]
  dsimp only [N]
  rw [complexTraceProjectiveModel_probability, ← hmaps]
  exact hword w

end Complex

section Quaternionic

variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis B ℝ H) (S : RightQuaternionicHilbertStructure H)
local notation "Op" => S.toOperatorStructure.operatorAlgebra
local notation "Carrier" => quaternionicSignedFiniteTrace b S
local notation "tr" => quaternionicSignedTrace b S
local notation "pair" => quaternionicTracePairing b S

private theorem quaternionicInstrument_idealTest_of_sharp_fixed_faces
    (M : QuaternionicInstrument b S) (P : Op) (hP : IsStarProjection P)
    (hmass : ∀ X, M.massOne b S X = pair P X)
    (hone : ∀ X, IsQuaternionicDensity b S X → tr (M.branchOne X) = 1 → M.branchOne X = X)
    (hzero : ∀ X, IsQuaternionicDensity b S X → tr (M.branchZero X) = 1 → M.branchZero X = X) :
    M.IsIdealTest b S := by
  have hsand (Q : Op) (hQ : IsStarProjection Q) (X : Carrier) :
      tr (quaternionicSandwich b S Q X) = pair Q X := by
    rw [signedTrace_quaternionicSandwich, hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq]
  let L : QuaternionicInstrument b S :=
    { branchOne := quaternionicSandwich b S P
      branchZero := quaternionicSandwich b S (1-P)
      one_positive := quaternionicSandwich_positive b S P
      zero_positive := quaternionicSandwich_positive b S (1-P)
      trace_preserving X := by
        rw [map_add, hsand P hP, hsand (1-P) hP.one_sub, quaternionicTracePairing_complement_eq]
        ring }
  have hL (X : Carrier) : L.massOne b S X = pair P X := hsand P hP X
  have hLI : L.IsIdealTest b S :=
    (QuaternionicInstrument.idealTest_iff_projection b S L).mpr ⟨P,hP,rfl,rfl,hL⟩
  refine ⟨hone, ?_, ?_⟩
  · intro X hX h0
    apply hzero X hX
    rw [M.signedTrace_branchZero b S, hX.2, h0, sub_zero]
  · rintro ⟨X,F,hX,hF,hFX,hvanish⟩
    apply hLI.2.2
    refine ⟨X,F,hX,hF,hFX,fun Y hY hcert => hvanish Y hY ?_⟩
    simpa only [hmass Y, hL Y] using hcert

/-- Whole-face ideality fails for a sharp trace-class realization of the
generating Albert menu over quaternionic Hilbert space. -/
theorem quaternionic_sharp_simulator_ideality_failure {I : Type*}
    (p : I → Albert) (hp : ∀ i, IsAtom (p i)) (hgen : GeneratesAlbert p) (ρ : Albert)
    (M : I → QuaternionicInstrument b S) (P : I → Op) (hP : ∀ i, IsStarProjection (P i))
    (hmass : ∀ i X, (M i).massOne b S X = pair (P i) X)
    (initial : Carrier) (hd : IsQuaternionicDensity b S initial)
    (hword : ∀ w, tr (wordMap (quaternionicBranch b S M) w initial) = nativeWordProbability p ρ w) :
    ∃ (q : Outcome I) (X : Carrier),
      IsQuaternionicDensity b S X ∧ tr (quaternionicBranch b S M q X) = 1 ∧ quaternionicBranch b S M q X ≠ X := by
  classical
  by_contra! hfixed
  have hi (i : I) : (M i).IsIdealTest b S := by
    apply quaternionicInstrument_idealTest_of_sharp_fixed_faces b S (M i) (P i) (hP i) (hmass i)
    · exact hfixed (i,true)
    · exact hfixed (i,false)
  have hfamily (i : I) := (QuaternionicInstrument.idealTest_iff_projection b S (M i)).mp (hi i)
  choose Q hQ h1 h0 htrace using hfamily
  have hmaps : quaternionicBranch b S M = fun q => quaternionicSandwich b S (algebraicOutcome Q q) := by
    funext q
    rcases q with ⟨i,a⟩
    cases a
    · exact h0 i
    · exact h1 i
  let N := quaternionicTraceProjectiveModel b S Q hQ initial hd
  apply algebraicProjective_not_matches_generating_atoms N.toAlgebraic p hp hgen ρ
  intro w
  rw [N.toAlgebraic_probability]
  dsimp only [N]
  rw [quaternionicTraceProjectiveModel_probability, ← hmaps]
  exact hword w

end Quaternionic

end AlbertSequential.HilbertTrace
