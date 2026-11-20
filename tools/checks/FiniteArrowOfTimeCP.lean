module

import FiniteArrowOfTimeCP

open AlbertSequential AlbertSequential.FiniteArrowOfTime

universe u v

example {I : Type u} {A : I → Type v} [∀ i, Fintype (A i)]
    {N d : ℕ} (R : FiniteArrowOfTime.Register A N) (e : History A N ≃ Fin d) :
    let r := R.diagonalCP e id
    IsNormalizedFiniteCPModel r ∧
      ∀ h : History A N, ∀ w : InstrumentWord A, finiteCPWordProbability r h w = R.run h w :=
  ⟨R.diagonalCP_normalized e id, R.diagonalCP_probability e id⟩

example {I : Type u} {A : I → Type v} [Finite I] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (N : ℕ) (t : FiniteArrowOfTime.Table A N) :
    (∃ (d : ℕ) (r : RawFiniteCPModel d Unit I A),
      IsNormalizedFiniteCPModel r ∧ ∀ h : History A N,
        finiteCPWordProbability r () h.val = t h) ↔ IsCausal t ∧ ∀ h, 0 ≤ t h :=
  exists_diagonalCP_iff t

example {I : Type u} {A : I → Type v} [Finite I] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (N : ℕ) (t : FiniteArrowOfTime.Table A N) :
    t ∈ affineSpan ℝ {s : FiniteArrowOfTime.Table A N | HasFiniteCPRealization s} ↔ IsCausal t :=
  mem_affineSpan_cpTables_iff t

#print axioms AlbertSequential.FiniteArrowOfTime.Register.diagonalCP_normalized
#print axioms AlbertSequential.FiniteArrowOfTime.Register.diagonalCP_probability
#print axioms AlbertSequential.FiniteArrowOfTime.cpTable_causal
#print axioms AlbertSequential.FiniteArrowOfTime.exists_diagonalCP_iff
#print axioms AlbertSequential.FiniteArrowOfTime.mem_affineSpan_cpTables_iff
