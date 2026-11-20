module

import AdaptiveWordExperiments
import CompanionThreeFrameContainment
import NativeOneTestConsequences

open AlbertSequential AlbertSequential.NativeAnalysis

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization 68 (Fin 4), IsRealKrausRealization r ∧
      ∀ (t : AdaptiveWordExperiment (Fin 4) Bool),
        t.run (fun a X => krausAction (r.kraus a.1 a.2) X) (fun X => (Matrix.trace X).re)
          (fun b => if b then 1 else 0) r.initial =
        t.run (fun a X => quadraticMap (nativeOutcome p a) X) albertTrace
          (fun b => if b then 1 else 0) ((1 / 3 : ℝ) • albertUnit) := by
  obtain ⟨r, hr, hm⟩ := exists_nativeFour_adaptive_instrument_68 p hp
  exact ⟨r, hr, fun t => hm Bool t (fun b => if b then 1 else 0)⟩

example (F : Fin 3 → NativeJordanFrame) (s : Fin 4 → Fin 3 × Fin 3) :
    ∃ Q : QuaternionicWindow, ∀ i, (F (s i).1).atom (s i).2 ∈ Q.subalgebra.carrier :=
  four_atoms_from_three_frames_contained F s

example (p ρ : Albert) (hp : IsAtom p) :
    nativeWordProbability (fun _ : Unit => p) ρ [((), true), ((), false)] = 0 :=
  (native_same_test_two_state_model p ρ hp [true, false]).trans (by rfl)

#print axioms AdaptiveWordExperiment.run_eq_of_all_word_probabilities
#print axioms exists_nativeFour_adaptive_instrument_68
#print axioms four_atoms_from_three_frames_contained
#print axioms fourPointInvariant_from_three_frames_zero
#print axioms native_same_test_two_state_model
#print axioms native_same_test_postStates
#print axioms native_fixedHead_matches_some_density
