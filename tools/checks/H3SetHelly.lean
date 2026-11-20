module

import H3SetHelly
import H3PrimitiveAtoms
import PentadInvariantIndependence

open AlbertSequential

example : (sInf {h | H3HasHellyProp .R h}, sInf {h | H3HasHellyProp .C h},
      sInf {h | H3HasHellyProp .H h}, sInf {h | H3HasHellyProp .O h}) = (3, 4, 4, 5) := by
  rw [h3_helly_number, h3_helly_number, h3_helly_number, h3_helly_number]
  rfl

example (S : Set Albert) (hS : ∀ x ∈ S, IsAtom x ∧ x ∈ (H3Subalgebra .C).carrier) :
    LiesInProperH3 .C S ↔
      ∀ T : Finset Albert, (T : Set Albert) ⊆ S → T.card ≤ 4 → LiesInProperH3 .C T :=
  h3_helly_geometric .C S hS

example (k : CDLevel) (p : (H3Subalgebra k).carrier) :
    (H3Subalgebra k).restrictedProduct.IsPrimitive p ↔ IsAtom p.val :=
  h3_primitive_iff_atom k p

example : ¬ ∃ D : (Fin 5 → ℝ) → Prop, ∀ p : Fin 5 → Albert, Function.Injective p →
      (∀ i, IsAtom (p i)) →
      (D (fun k => fourPointInvariant (fun j : Fin 4 => p (k.succAbove j))) ↔ GeneratesAlbert p) :=
  no_determination_by_deleted_fourPointInvariants

#print axioms finite_subset_same_generated_subalgebra
#print axioms irredundant_subset_same_generated_subalgebra
#print axioms h3_helly_iff
#print axioms h3_helly_number
#print axioms h3_helly_geometric
#print axioms h3_primitive_iff_atom
#print axioms quaternionicComparisonPentad_distinct
#print axioms pentad_quaternionic_same_deleted_invariants
#print axioms no_determination_by_deleted_fourPointInvariants
