module

import FiniteArrowOfTime

open AlbertSequential AlbertSequential.FiniteArrowOfTime

universe u v

example {I : Type u} {A : I → Type v} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (N : ℕ) (t : FiniteArrowOfTime.Table A N) :
    (∃ R : FiniteArrowOfTime.Register A N, R.table = t) ↔ IsCausal t ∧ ∀ h, 0 ≤ t h :=
  exists_register_iff t

example {I : Type u} {A : I → Type v} [Finite I] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (N : ℕ) (t : FiniteArrowOfTime.Table A N) :
    t ∈ affineSpan ℝ (Set.range (FiniteArrowOfTime.Register.table (A := A) (N := N))) ↔ IsCausal t :=
  mem_affineSpan_registerTables_iff t

#print axioms AlbertSequential.FiniteArrowOfTime.Register.table_causal
#print axioms AlbertSequential.FiniteArrowOfTime.exists_register_iff
#print axioms AlbertSequential.FiniteArrowOfTime.mem_affineSpan_registerTables_iff
