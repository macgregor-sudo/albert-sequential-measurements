module

import SingleAtomQubit

open AlbertSequential
open scoped ComplexOrder

example (p : Albert) (hp : IsAtom p) :
    Disjoint (Submodule.span ℝ ({p} : Set Albert))
      (Submodule.span ℝ ({albertUnit - p} : Set Albert)) :=
  singleAtom_complementary_spans_disjoint p hp

example (p : Albert) (hp : IsAtom p) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℂ, star P = P ∧ P * P = P ∧ P.rank = 1 ∧
      ∀ ρ : Albert, IsDensity ρ → ∃ τ : Matrix (Fin 2) (Fin 2) ℂ,
        τ.PosSemidef ∧ τ.trace = 1 ∧
        ∀ w : Word Unit, (τ * wordOperator (fun _ => P) w).trace.re =
          nativeWordProbability (fun _ => p) ρ w :=
  singleAtom_qubit_word_model p hp

#print axioms singleAtom_complementary_spans_disjoint
#print axioms singleAtom_qubit_word_model
