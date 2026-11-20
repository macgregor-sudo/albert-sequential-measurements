module

import GeneralEJAFrameTransport

open AlbertSequential

example {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) (c : Fin 3 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (x : P.frameJointSpace c (UnitalJordanProduct.frameOffDiagonalPattern 0 1))
    (hxnorm : P.canonicalTraceOfFormallyReal hfr (P.product x.val x.val) = 2)
    (y : P.frameJointSpace c (UnitalJordanProduct.frameOffDiagonalPattern 1 2)) :
    let e := P.frameOffDiagonalLinearEquiv_of_traceUnit hfr c hc hor hunit
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 2) x hxnorm
    (e y).val = (2 : ℝ) • P.product x.val y.val ∧
      P.canonicalTraceOfFormallyReal hfr (P.product (e y).val (e y).val) =
        P.canonicalTraceOfFormallyReal hfr (P.product y.val y.val) :=
  ⟨P.frameOffDiagonalLinearEquiv_of_traceUnit_apply hfr c hc hor hunit
      (by decide) (by decide) (by decide) x hxnorm y,
    P.frameOffDiagonalLinearEquiv_of_traceUnit_preserves_trace_square hfr c hc hor hunit
      (by decide) (by decide) (by decide) x hxnorm y⟩

#print axioms UnitalJordanProduct.exists_frameOffDiagonal_traceUnit
#print axioms UnitalJordanProduct.frameOffDiagonal_shared_trace_square
#print axioms UnitalJordanProduct.frameOffDiagonalLinearEquiv_of_traceUnit
#print axioms UnitalJordanProduct.frameOffDiagonalLinearEquiv_of_traceUnit_preserves_trace_square
