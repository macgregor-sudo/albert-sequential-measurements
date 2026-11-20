/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeFiniteInstrumentSimulation
public import Robustness.WordContractions

/-! Finite adaptive experiments preserve exact all-word table agreement. -/
@[expose] public section
noncomputable section

namespace AlbertSequential

/-- The two continuations of a test are chosen by the answer. Independent
classical randomization can choose between experiments at any point. -/
inductive AdaptiveWordExperiment (I O : Type*) where
  | result (label : O)
  | test (i : I) (yes no : AdaptiveWordExperiment I O)
  | randomize (weight : Set.Icc (0 : ℝ) 1) (left right : AdaptiveWordExperiment I O)

namespace AdaptiveWordExperiment

variable {I O E F : Type*}

/-- Sum of terminal scores weighted by the masses of the actual updated states. -/
def run (update : Outcome I → E → E) (mass : E → ℝ) (score : O → ℝ) :
    AdaptiveWordExperiment I O → E → ℝ
  | .result label, x => score label * mass x
  | .test i yes no, x =>
    run update mass score yes (update (i, true) x) + run update mass score no (update (i, false) x)
  | .randomize weight left right, x =>
    weight.val * run update mass score left x + (1 - weight.val) * run update mass score right x

/-- Evaluation by the word table uses the full chronological history at each leaf. -/
def evaluate (table : Word I → ℝ) (score : O → ℝ) : AdaptiveWordExperiment I O → Word I → ℝ
  | .result label, w => score label * table w
  | .test i yes no, w =>
    evaluate table score yes (w ++ [(i, true)]) + evaluate table score no (w ++ [(i, false)])
  | .randomize weight left right, w =>
    weight.val * evaluate table score left w + (1 - weight.val) * evaluate table score right w

theorem run_eq_evaluate (update : Outcome I → E → E) (mass : E → ℝ) (score : O → ℝ)
    (x : E) (t : AdaptiveWordExperiment I O) (w : Word I) :
    t.run update mass score (chronologicalState update x w) =
      t.evaluate (fun v => mass (chronologicalState update x v)) score w := by
  induction t generalizing w with
  | result => rfl
  | test i yes no ihYes ihNo =>
    simp only [run, evaluate, chronologicalState_append_singleton, ← ihYes, ← ihNo,
      chronologicalState_append_singleton]
  | randomize weight left right ihLeft ihRight => simp only [run, evaluate, ihLeft, ihRight]

theorem run_eq_of_all_word_probabilities
    (f : Outcome I → E → E) (g : Outcome I → F → F) (m : E → ℝ) (n : F → ℝ)
    (x : E) (y : F) (h : ∀ w : Word I, m (chronologicalState f x w) = n (chronologicalState g y w))
    (t : AdaptiveWordExperiment I O) (score : O → ℝ) :
    t.run f m score x = t.run g n score y := by
  exact (run_eq_evaluate f m score x t []).trans
    ((congrArg (fun table => t.evaluate table score []) (funext h)).trans
      (run_eq_evaluate g n score y t []).symm)

end AdaptiveWordExperiment

/-- The same 68-dimensional realization works for every finite adaptive
selection of the four tested atoms, including random selection. -/
theorem exists_nativeFour_adaptive_instrument_68 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization 68 (Fin 4), IsRealKrausRealization r ∧
      ∀ (O : Type*) (t : AdaptiveWordExperiment (Fin 4) O) (score : O → ℝ),
        t.run (fun a X => krausAction (r.kraus a.1 a.2) X) (fun X => (Matrix.trace X).re)
          score r.initial =
        t.run (fun a X => quadraticMap (nativeOutcome p a) X) albertTrace
          score ((1 / 3 : ℝ) • albertUnit) := by
  obtain ⟨r, hr, htable⟩ := NativeAnalysis.exists_nativeFour_instrument_68 p hp
  refine ⟨r, hr, fun O t score => ?_⟩
  exact AdaptiveWordExperiment.run_eq_of_all_word_probabilities _ _ _ _ _ _ htable t score

end AlbertSequential
