/- SPDX-License-Identifier: Apache-2.0 -/
module

import LengthSeven.WalkTolerance.Native

set_option autoImplicit false

open AlbertSequential AlbertSequential.Ends AlbertSequential.LengthSeven
open AlbertSequential.LengthSeven.LemmaA AlbertSequential.LengthSeven.LemmaA.WalkTolerance

universe u

example {V : Type u} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (p : Fin 4 → Albert) (hp : ∀ a, IsAtom (p a)) (e : ℝ)
    (he : 0 ≤ e)
    (h : ∀ w : Word Letter, w.length ≤ 6 →
      |W.normSq (W.vec w) - nativeWordProbability p (p 0) w| ≤ e)
    (i j : Fin 28) :
    |W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) - gram28 (nativeTraceData p) i j| ≤
      gramCost (nativeTraceData p) * Real.sqrt e :=
  gram_within_atoms W p hp e he h i j

example {A : Type u} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A)
    (p : Fin 4 → Albert) (hp : ∀ a, IsAtom (p a))
    (he : uniformSevenError p M.probability ≤ 1 / 12) :
    ∃ q : 0 < M.probability [(0, true)], ∀ i j : Fin 28,
      let W := WalkForm.ofAlgebraic M q
      |W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) - gram28 (nativeTraceData p) i j| ≤
        (Real.sqrt 8 * gramCost (nativeTraceData p)) * Real.sqrt (uniformSevenError p M.probability) :=
  gram_within_e3 M p hp he

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) ℝ H)
    (p : Fin 4 → Albert) (hp : ∀ a, IsAtom (p a))
    (he : uniformSevenError p (fun w => M.state (M.wordEffect w)) ≤ 1 / 12) :
    ∃ q : 0 < M.toAlgebraic.probability [(0, true)], ∀ i j : Fin 28,
      let W := WalkForm.ofHilbert M q
      |W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) - gram28 (nativeTraceData p) i j| ≤
        (Real.sqrt 8 * gramCost (nativeTraceData p)) *
          Real.sqrt (uniformSevenError p (fun w => M.state (M.wordEffect w))) :=
  gram_within_e3_hilbert M p hp he

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) ℂ H)
    (p : Fin 4 → Albert) (hp : ∀ a, IsAtom (p a))
    (he : uniformSevenError p (fun w => M.state (M.wordEffect w)) ≤ 1 / 12) :
    ∃ q : 0 < M.toAlgebraic.probability [(0, true)], ∀ i j : Fin 28,
      let W := WalkForm.ofHilbert M q
      |W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) - gram28 (nativeTraceData p) i j| ≤
        (Real.sqrt 8 * gramCost (nativeTraceData p)) *
          Real.sqrt (uniformSevenError p (fun w => M.state (M.wordEffect w))) :=
  gram_within_e3_hilbert M p hp he

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData (Fin 4) Q)
    (p : Fin 4 → Albert) (hp : ∀ a, IsAtom (p a))
    (he : uniformSevenError p (fun w => M.state (M.wordEffect w)) ≤ 1 / 12) :
    ∃ q : 0 < M.toAlgebraic.probability [(0, true)], ∀ i j : Fin 28,
      let W := WalkForm.ofQuaternionic M q
      |W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)) - gram28 (nativeTraceData p) i j| ≤
        (Real.sqrt 8 * gramCost (nativeTraceData p)) *
          Real.sqrt (uniformSevenError p (fun w => M.state (M.wordEffect w))) :=
  gram_within_e3_quaternionic M p hp he

#print axioms WalkForm.purity_pair_within
#print axioms WalkForm.r1_within
#print axioms WalkForm.r2_within
#print axioms WalkForm.p3_within
#print axioms WalkForm.r3_within
#print axioms WalkForm.delete_within
#print axioms lemmaA_within
#print axioms gram_within_atoms
#print axioms gram_within_e3
#print axioms gram_within_e3_hilbert
#print axioms gram_within_e3_quaternionic
