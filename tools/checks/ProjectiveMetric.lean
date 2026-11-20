module

import CompanionProjectiveMetricInvariant

open AlbertSequential AlbertSequential.NativeAnalysis AlbertSequential.ProjectiveMetricInvariant

example : ∃ f : Albert ≃ₗ[ℝ] Albert, (∀ x, albertCubicNorm (f x) = albertCubicNorm x) ∧
    (∀ g : NativeAlbertAutomorphism, ∀ p : Fin 4 → Albert,
      fourPointInvariant (fun i => g.linearEquiv (p i)) = fourPointInvariant p) ∧
    let p := fun i => (albertTrace (f (maximizerConfig i)))⁻¹ • f (maximizerConfig i)
    (∀ i, IsAtom (p i)) ∧ fourPointInvariant p < fourPointInvariant maximizerConfig :=
  ⟨rescale, rescale_cubicNorm, compactAutomorphism_invariant,
    fun i => rescaledAtom_isAtom (maximizerConfig_isAtom i), rescaled_maximalMenu_invariant_lt⟩

example (p q : {p : Albert // IsAtom p}) :
    tracePairing (atomRayRescaling p) (atomRayRescaling.symm q) = 0 ↔ tracePairing p q = 0 :=
  rescaledAtom_incidence_iff p.property q.property

#print axioms rescale_cubicNorm
#print axioms atomRayRescaling
#print axioms rescaledAtom_incidence_iff
#print axioms compactAutomorphism_invariant
#print axioms rescaled_maximalMenu_overlap
#print axioms rescaled_maximalMenu_invariant_lt
#print axioms invariant_constant_of_dense_transitive_locus
