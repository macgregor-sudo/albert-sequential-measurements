module

import QuaternionicHellySix
import HilbertTraceReal
import HilbertTraceComplex
import HilbertTraceQuaternionic
open AlbertSequential AlbertSequential.HilbertTrace
example : IsLeast {n : ℕ | QuaternionicHellyProperty n} 6 := quaternionicHelly_isLeast
example : Module.finrank ℝ (generatedSubalgebra (Set.range paperLineHellySix)).carrier = 8 :=
  paperLineHellySix_generated_finrank
example {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H) {T : H →L[ℝ] H} (hp : T.IsPositive) :
    positiveTrace b T = positiveTrace c T := real_positiveTrace_basis_independent b c hp
#print axioms quaternionicHelly_six_iso
#print axioms quaternionicHelly_isLeast
#print axioms paperLineHelly_generated_structure
#print axioms quaternionicHelly_projective
#print axioms paperLineHellySix_projective_nonconverse
#print axioms positiveTrace_hasSum_rankOne
#print axioms real_positiveTrace_hasSum_rankOne
#print axioms quaternionicDyad_normalized_trace
