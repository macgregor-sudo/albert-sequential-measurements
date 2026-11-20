module

import LengthSeven.WalkReductionComplete
open AlbertSequential.LengthSeven
example {V : Type*} [AddCommGroup V] [Module ℝ V] (W : AlgebraicWalkSpace V)
    (τ : TraceData) (h : AlgebraicWalkHypotheses W τ) (u v : List Letter)
    (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    W.form (W.pathVec u) (W.pathVec v) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (walkTraceCoordinates τ) (walkUpsilon (u ++ v.reverse)) :=
  algebraicWalk_gram_eq_upsilon W τ h u v hu hv
#print axioms algebraicWalk_L_eq_upsilon
#print axioms algebraicWalk_gram_eq_upsilon
