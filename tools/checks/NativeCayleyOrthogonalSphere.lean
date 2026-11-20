module

import NativeCayleyOrthogonalSphereSmooth

open AlbertSequential AlbertSequential.NativeCayley AlbertSequential.WindowProbability
open Metric Set Topology
open scoped ContDiff Manifold

noncomputable section

example (p : {p : Albert // IsAtom p}) :
    {q : {q : Albert // IsAtom q} | tracePairing p.val q.val = 0} ≃ₜ
      (sphere (0 : EuclideanSpace ℝ (Fin 9)) 1 : Type) :=
  orthogonalAtomSphere p

example (q : {q : AlbertAtomSpace | tracePairing (diagAtom 0) q.val = 0}) :
    (firstOrthogonalAtomSphere q).val 0 = q.val.val.1 1 - q.val.val.1 2 := rfl

example (q : {q : AlbertAtomSpace | tracePairing (diagAtom 0) q.val = 0}) (i : Fin 8) :
    (firstOrthogonalAtomSphere q).val i.succ =
      octonionChartCoordinates.symm ((2 : ℝ) • q.val.val.2 2) i := rfl

example (p : AlbertAtomSpace) :
    range (orthogonalSphereAtom p) = {q : AlbertAtomSpace | tracePairing p.val q.val = 0} :=
  range_orthogonalSphereAtom p

example (p : AlbertAtomSpace) : IsClosedEmbedding (orthogonalSphereAtom p) :=
  isClosedEmbedding_orthogonalSphereAtom p

example (p : AlbertAtomSpace) :
    ContMDiff (𝓡 8) (𝓘(ℝ, Fin 16 → ℝ)) ω (orthogonalSphereAtom p) :=
  contMDiff_orthogonalSphereAtom p

example (p : AlbertAtomSpace) (x : sphere (0 : EuclideanSpace ℝ (Fin 9)) 1) :
    Function.Injective (mfderiv (𝓡 8) (𝓘(ℝ, Fin 16 → ℝ)) (orthogonalSphereAtom p) x) :=
  mfderiv_orthogonalSphereAtom_injective p x

#print axioms isClosed_orthogonalAtomLocus
#print axioms contDiff_orthogonalSphereCoordinates
#print axioms contDiff_orthogonalSphereEmbedding
#print axioms orthogonalSphereCoordinates_mem
#print axioms orthogonalSphereEmbedding_isAtom
#print axioms firstOrthogonalAtomSphere
#print axioms orthogonalAtomLocusHomeomorph
#print axioms orthogonalAtomSphere
#print axioms range_orthogonalSphereAtom
#print axioms isClosedEmbedding_orthogonalSphereAtom
#print axioms contMDiff_nativeAtom_val
#print axioms contMDiff_orthogonalSphereAtom
#print axioms mfderiv_orthogonalSphereAtom_injective
