module

import QuaternionicGramReadout
import ComplexDensityChord

open AlbertSequential AlbertSequential.MatchingModels AlbertSequential.WindowProbability
open scoped Matrix ComplexOrder

example (a b c : ℝ) (z u v : Quaternion ℝ) (h : quatSchurLeadingDet a b z ≠ 0) :
    let Θ := quatSchurGram a b c z u v
    let t := quatGramDoublePairs Θ
    t 0 + t 1 + t 2 - tauOf (quatGramOverlap Θ) (quatGramTriangle Θ) =
      -(1/2 : ℝ) * quatSchurLeadingDet a b z * quatSchurScalar a b c z u v :=
  quatSchurTrace a b c z u v h

example (a b c d e f : ℝ) (h1 h2 h3 : Quaternion ℝ)
    (h : quatSchurLeadingDet a b (d • h1) ≠ 0) :
    let Θ := quatSchurGram a b c (d • h1) (e • star h3) (f • h2)
    quatSchurScalar a b c (d • h1) (e • star h3) (f • h2) = 0 ↔
      quatGramDoublePairs Θ ∈ planePi (quatGramOverlap Θ) (quatGramTriangle Θ) :=
  quatSchurScalar_zero_iff_mem_plane a b c _ _ _ h

example (x : Fin 4 → Fin 4 → Quaternion ℝ) :
    quatGramCycle (quatColumnGram x) 0 1 2 3 =
      (quatColumnDyad (x 0) * quatColumnDyad (x 1) * quatColumnDyad (x 2) *
        quatColumnDyad (x 3)).trace.re :=
  quatGramCycle_eq_dyad_trace x 0 1 2 3

example (σ H : ComplexMatrix3) (hσ : σ.PosDef) (htrace : σ.trace = 1)
    (hH : H.IsHermitian) (hzero : H ≠ 0) (htrH : H.trace = 0) :
    ∃ sMin sMax : ℝ, sMin < 0 ∧ 0 < sMax ∧
      (∀ s : ℝ, (σ + s • H).PosSemidef ↔ sMin ≤ s ∧ s ≤ sMax) ∧
      (σ + sMin • H).rank ≤ 2 ∧ (σ + sMax • H).rank ≤ 2 := by
  obtain ⟨lo,hi,hlo,hhi,hint,hrlo,hrhi,_⟩ := complexDensity_rankTwo_chord σ H hσ htrace hH hzero htrH
  exact ⟨lo,hi,hlo,hhi,hint,hrlo,hrhi⟩

#print axioms quatSchurLeadingInverse_spec
#print axioms quatSchurTrace_polynomial
#print axioms quatSchurTrace
#print axioms quatSchurLeadingDet_eq_tripleNorm
#print axioms quatSchurScalar_zero_iff_mem_plane
#print axioms quatGramOverlap_eq_dyad_trace
#print axioms quatGramTriangle_eq_dyad_trace
#print axioms quatGramCycle_eq_dyad_trace
#print axioms quatGramDoublePair_eq_jordan_trace
#print axioms complexDensity_rankTwo_chord
#print axioms complexDensity_chord_quaternionic_atoms
