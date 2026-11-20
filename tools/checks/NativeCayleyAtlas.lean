module

import Bridge.Atoms
import NativeCayleyManifold
import NativeCayleyHomogeneous

open AlbertSequential AlbertSequential.NativeCayley AlbertSequential.WindowProbability
open Set
open scoped ContDiff Manifold

noncomputable section

example (p : Albert) :
    IsAtom p ↔ jordanMul p p = p ∧ p ≠ 0 ∧
      ¬ ∃ q r : Albert, jordanMul q q = q ∧ jordanMul r r = r ∧ q ≠ 0 ∧ r ≠ 0 ∧
        jordanMul q r = 0 ∧ p = q + r :=
  NativeAnalysis.isAtom_iff_primitive p

example : ChartedSpace (Fin 16 → ℝ) {p : Albert // IsAtom p} := inferInstance

example : IsManifold (𝓘(ℝ, (Fin 16 → ℝ))) ω {p : Albert // IsAtom p} := inferInstance

example : Module.finrank ℝ (Fin 16 → ℝ) = 16 := cayleyModel_finrank

example (i : Fin 3) : {p : AlbertAtomSpace | 0 < p.val.1 i} ≃ₜ (Fin 16 → ℝ) :=
  pivotRegionHomeomorph i

example : (⋃ i : Fin 3, {p : AlbertAtomSpace | 0 < p.val.1 i}) = univ :=
  iUnion_pivotChart_source

example (i j : Fin 3) :
    ((pivotChart i).symm.trans (pivotChart j)).source =
      {x : Fin 16 → ℝ | 0 < (chartEmbedding i x).1 j} := by
  rw [OpenPartialHomeomorph.trans_source]
  change (univ ∩ {x : Fin 16 → ℝ | 0 < (chartEmbedding i x).1 j}) = _
  exact univ_inter _

example (i j : Fin 3) :
    ContDiffOn ℝ ω (chartCoordinates j ∘ chartEmbedding i)
      {x : Fin 16 → ℝ | 0 < (chartEmbedding i x).1 j} := by
  have h := contDiffOn_pivotChart_transition i j (n := ω)
  rw [OpenPartialHomeomorph.trans_source] at h
  change ContDiffOn ℝ ω (chartCoordinates j ∘ chartEmbedding i)
    (univ ∩ {x : Fin 16 → ℝ | 0 < (chartEmbedding i x).1 j}) at h
  simpa only [univ_inter] using h

example : IsCompact {p : Albert | IsAtom p} := isCompact_nativeAtomSet

example : CompactSpace AlbertAutomorphismGroup := inferInstance

example : IsTopologicalGroup AlbertAutomorphismGroup := inferInstance

example (p : AlbertAtomSpace) :
    IsClosed (MulAction.stabilizer AlbertAutomorphismGroup p : Set AlbertAutomorphismGroup) :=
  isClosed_atomStabilizer p

example (p : AlbertAtomSpace) :
    (AlbertAutomorphismGroup ⧸ MulAction.stabilizer AlbertAutomorphismGroup p) ≃ₜ
      {q : Albert // IsAtom q} :=
  atomStabilizerQuotientHomeomorph p

example (p : AlbertAtomSpace) (g : AlbertAutomorphismGroup) :
    atomStabilizerQuotientHomeomorph p (QuotientGroup.mk g) = g • p :=
  atomStabilizerQuotientHomeomorph_apply p g

#print axioms NativeAnalysis.isAtom_iff_primitive
#print axioms firstPivotCoordinates_affineAtomEmbedding
#print axioms affineAtomEmbedding_firstPivotCoordinates
#print axioms pivotRegionHomeomorph
#print axioms iUnion_pivotChart_source
#print axioms contDiffOn_pivotChart_transition
#print axioms instCayleyAnalyticManifold
#print axioms cayleyModel_finrank
#print axioms continuous_atomAction
#print axioms isClosed_atomStabilizer
#print axioms atomStabilizerQuotientHomeomorph
#print axioms atomStabilizerQuotientHomeomorph_apply
