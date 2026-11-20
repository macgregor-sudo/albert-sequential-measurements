module

import ClassicalDensityRegister
import NativePureStates
import HilbertBargmannTraces

set_option warningAsError true

open AlbertSequential
open scoped InnerProductSpace

example {E ι : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
    (T : Outcome ι → E →ₗ[ℝ] E)
    (hpos : ∀ a x, x ∈ P.squareCone → T a x ∈ P.squareCone)
    (hn : ∀ i x, P.canonicalTraceOfFormallyReal hfr (T (i,true) x + T (i,false) x) =
      P.canonicalTraceOfFormallyReal hfr x) :
    ∃ R : ClassicalBinaryRegister ι {x : E // P.IsCanonicalDensity hfr x},
      (∀ a s, R.probability a s = P.canonicalTraceOfFormallyReal hfr (T a s.val)) ∧
      (∀ a s, R.probability a s • (R.next a s).val = T a s.val) ∧
      (∀ s w, R.wordProbability s w =
        P.canonicalTraceOfFormallyReal hfr (w.foldl (fun x a => T a x) s.val)) :=
  P.exists_classical_density_register hfr T hpos hn

example {E ι : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
    (p : ι → E) (hp : ∀ i, P.product (p i) (p i) = p i) :
    ∃ R : ClassicalBinaryRegister ι {x : E // P.IsCanonicalDensity hfr x}, ∀ s w,
      R.wordProbability s w = P.canonicalTraceOfFormallyReal hfr (P.sequentialBranchState p s.val w) :=
  P.exists_classical_register_for_ideal_tests hfr p hp

example (p : Albert) : p ∈ Set.extremePoints ℝ {ρ : Albert | IsDensity ρ} ↔ IsAtom p :=
  nativePureState_iff_atom p

open AlbertSequential.Bargmann.Hilbert

example {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ H) (a b c d : H) :
    (Summable (fun i => ‖⟪e i, (jordanPair a b * jordanPair c d) (e i)⟫_ℂ‖)) ∧
    doubleTrace e a b c d = ((cycle a b c d).re + (cycle a b d c).re) / 2 ∧
    doubleTrace e a b c d = doubleTrace f a b c d := by
  exact ⟨(hasSum_double e a b c d).summable.norm, doubleTrace_eq e a b c d,
    (doubleTrace_eq e a b c d).trans (doubleTrace_eq f a b c d).symm⟩

example {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : HilbertBasis ι ℂ H) (a b c d : H) :
    doubleTrace e a c b d + doubleTrace e a d b c - doubleTrace e a b c d = (cycle a c b d).re :=
  (omega_eq e a b c d).1

#print axioms ClassicalBinaryRegister.transition_apply
#print axioms UnitalJordanProduct.exists_classical_density_register
#print axioms UnitalJordanProduct.exists_classical_register_for_ideal_tests
#print axioms nativeDensity_eq_convexHull_atoms
#print axioms nativePureState_iff_atom
#print axioms hasSum_cycle
#print axioms hasSum_double
#print axioms doubleTrace_eq
#print axioms omega_eq
