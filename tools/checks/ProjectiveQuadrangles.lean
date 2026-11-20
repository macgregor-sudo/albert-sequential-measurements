module

import CompanionFreudenthalPolar
import CompanionQuadrangleTransitivity

set_option warningAsError true

open AlbertSequential AlbertSequential.NativeAnalysis AlbertSequential.WindowProbability
open AlbertSequential.ProjectiveMetricInvariant

example {a b q : AlbertAtomSpace} (hab : a ≠ b)
    (hqa : tracePairing q.val a.val = 0) (hqb : tracePairing q.val b.val = 0) :
    (1 - tracePairing a.val b.val)⁻¹ • albertCross a.val b.val = q.val :=
  normalized_freudenthal_product_eq_polar hab hqa hqb

example (p q : Fin 4 → AlbertAtomSpace) (hp : p ∈ quadrangleLocus) (hq : q ∈ quadrangleLocus) :
    ∃ g : CubicRayEquiv, (∀ x, albertCubicNorm (g.linearEquiv x) = albertCubicNorm x) ∧
      (∀ i, g.pointMap (p i) = q i) ∧
      ∀ a : AlbertAtomSpace, ∃! b : AlbertAtomSpace, ∀ x : AlbertAtomSpace,
        tracePairing b.val (g.pointMap x).val = 0 ↔ tracePairing a.val x.val = 0 := by
  obtain ⟨g, hg, hpq⟩ := quadrangle_projective_transitive p q hp hq
  refine ⟨g, fun x => ?_, hpq, g.existsUnique_lineMap⟩
  rw [g.map_norm, hg, one_mul]

example (f : (Fin 4 → AlbertAtomSpace) → ℝ) (hf : Continuous f)
    (hi : ∀ g : CubicRayEquiv, g.scale = 1 → ∀ p, f (fun i => g.pointMap (p i)) = f p)
    (p q : Fin 4 → AlbertAtomSpace) : f p = f q :=
  (continuous_projective_four_point_invariant_constant f hf hi p).trans
    (continuous_projective_four_point_invariant_constant f hf hi q).symm

#print axioms normalized_freudenthal_product_eq_polar
#print axioms freudenthal_product_incidence_iff
#print axioms cubicNorm_weightedAtoms_eq_zero_iff
#print axioms CubicRayEquiv.existsUnique_lineMap
#print axioms quadrangle_first_three_axes
#print axioms quadrangle_projective_normal_form
#print axioms quadrangle_projective_transitive
#print axioms continuous_projective_four_point_invariant_constant
