module

import TracePolynomialSupport
import GeneratingMenuStabilizer
import NativeAutomorphisms

open AlbertSequential AlbertSequential.NativeAnalysis

universe u

example {I : Type u} (p : I → Albert) (hp : GeneratesAlbert p) (g : NativeAlbertAutomorphism)
    (hg : ∀ i, g.linearEquiv (p i) = p i) : g = nativeAutomorphismIdentity :=
  automorphisms_eq_on_generating_menu p hp g nativeAutomorphismIdentity (fun i => hg i)

example (x : Fin 13 → ℝ) :
    expandedTraceTerms.length = 52 ∧
    (expandedTraceTerms.map Prod.snd).Nodup ∧
    ((expandedTraceTerms.map (fun t => (t.1 : ℝ) * (t.2.map x).prod)).sum) =
      fourPointOmegaPoly
        (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
        (-x 10 + x 11 + x 12) (x 10 - x 11 + x 12) (x 10 + x 11 - x 12) := by
  refine ⟨expandedTraceTerms_support.1, expandedTraceTerms_support.2.1, ?_⟩
  rw [expandedTraceTerms_eval]
  unfold fourPointTracePoly
  congr 1 <;> ring

example (p : Fin 4 → Albert) (s : Fin 4 → ℝ) :
    (expandedTraceTerms.map
      (fun t => (t.1 : ℝ) * (t.2.map (expandedTraceCoordinates (fun i => s i • p i))).prod)).sum =
      s 0 ^ 3 * s 1 ^ 3 * s 2 ^ 3 * s 3 ^ 3 * fourPointInvariant p := by
  rw [expandedTraceTerms_native, fourPointInvariant_multihomogeneous]
  ring

#print axioms agree_on_generated_of_agree_on_menu
#print axioms automorphisms_eq_on_generating_menu
#print axioms expandedTraceTerms_support
#print axioms expandedTraceTerms_eval
#print axioms expandedTraceTerms_native
#print axioms fourPointInvariant_multihomogeneous
