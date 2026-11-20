module

import PaperComplexWindowNormalForm

noncomputable section

open AlbertSequential

example (W : ComplexWindow) (g : NativeAlbertAutomorphism) (y z : Albert)
    (hz : W.Contains z) :
    W.Contains (nativeWindowOrthogonalProjection W y) ∧
    tracePairing (y - nativeWindowOrthogonalProjection W y) z = 0 ∧
    nativeWindowOrthogonalProjection W z = z ∧
    nativeWindowOrthogonalProjection (W.transport g) (g.linearEquiv y) =
      g.linearEquiv (nativeWindowOrthogonalProjection W y) := by
  refine ⟨nativeWindowOrthogonalProjection_mem W y,
    nativeWindowOrthogonalProjection_residual W y z hz,
    nativeWindowOrthogonalProjection_fixes W hz, ?_⟩
  exact LinearMap.congr_fun (nativeWindowOrthogonalProjection_transport W g) y

example (W : ComplexWindow) (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hpair : IsWindowTrianglePairwise p)
    (hfourth : jordanMul (p 0) (p 3) ≠ 0 ∨ jordanMul (p 1) (p 3) ≠ 0 ∨
      jordanMul (p 2) (p 3) ≠ 0) :
    ∃ N : WindowTriangleNormalForm p,
      N.permutation 3 = 3 ∧ 0 < tracePairing (p (N.permutation 0)) (p 3) ∧
      windowDelta W (p 0) (p 1) (p 2) = N.B₀ ^ 2 * N.B₁ ^ 4 * N.C₀ ^ 2 * N.C₂ ^ 2 * N.C₃ ^ 2 ∧
      fourPointInvariant (fun i => p (N.permutation i)) = fourPointInvariant p ∧
      (∀ x, InGeneratedAlgebra ![p (N.permutation 0), p (N.permutation 1), p (N.permutation 2)] x ↔
        InGeneratedAlgebra ![p 0, p 1, p 2] x) := by
  obtain ⟨N⟩ := paperWindowTriangle_a hp hpair hfourth
  exact ⟨N, N.fixesFourth, N.fourthOverlap, N.windowDelta W, N.invariant_relabel, N.generated_relabel⟩

example (W : ComplexWindow) (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hδ : windowDelta W (p 0) (p 1) (p 2) ≠ 0) :
    (∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → i ≠ j →
      0 < tracePairing (p i) (p j) ∧ tracePairing (p i) (p j) < 1) ∧
    ∃ (N : WindowTriangleNormalForm p) (G : ComplexWindow),
      (∀ x, x ∈ G.toSubalgebra.carrier ↔ InGeneratedAlgebra ![p 0, p 1, p 2] x) ∧
      (G.transport N.automorphism).toSubalgebra.carrier = standardComplexWindow.toSubalgebra.carrier ∧
      ∀ y, nativeWindowOrthogonalProjection standardComplexWindow (N.automorphism.linearEquiv y) =
        N.automorphism.linearEquiv (nativeWindowOrthogonalProjection G y) := by
  obtain ⟨_, hover, N, G, hgen, hgG, hP⟩ := paperWindowTriangle_b hp hδ
  exact ⟨hover, N, G, hgen, hgG, fun y => LinearMap.congr_fun hP y⟩

example (W : ComplexWindow) (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hδ : windowDelta W (p 0) (p 1) (p 2) = 0) :
    fourPointInvariant p = 0 :=
  paperWindowTriangle_c W hp hδ

#print axioms paperWindowTriangle_a
#print axioms paperWindowTriangle_b
#print axioms paperWindowTriangle_c
#print axioms WindowTriangleNormalForm.windowDelta
#print axioms WindowTriangleNormalForm.invariant_relabel
#print axioms WindowTriangleNormalForm.generated_relabel
#print axioms WindowTriangleNormalForm.generated
#print axioms nativeWindowOrthogonalProjection_residual
#print axioms nativeWindowOrthogonalProjection_transport
#print axioms tripleDelta_normal_form
#print axioms tripleDelta_nonzero_some_overlap
#print axioms prop_windowdet
