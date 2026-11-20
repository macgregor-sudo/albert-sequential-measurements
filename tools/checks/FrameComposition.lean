module

import GeneralEJAFrameComposition

open AlbertSequential

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (c : Fin 3 → E)
    (hc : ∀ r, P.IsPrimitive (c r)) (hor : ∀ r s, r ≠ s → P.product (c r) (c s) = 0)
    (hunit : ∑ r, c r = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) :
    let W := P.frameOffDiagonalSpace c 0 2
    let B := P.frameOffDiagonalTraceForm (P.formallyReal_of_associative_inner hinner) c 0 2
    ∃ (m : W →ₗ[ℝ] W →ₗ[ℝ] W) (e : W), B e e = 1 ∧
      (∀ x, m e x = x ∧ m x e = x) ∧
      ∀ x y, B (m x y) (m x y) = B x x * B y y := by
  obtain ⟨C⟩ := P.exists_peirceTriangleCoordinates_of_simple c hc hor hunit hinner hsimple
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 2)
  exact ⟨C.product, C.unit, C.unit_form, fun x => ⟨C.unit_left x, C.unit_right x⟩, C.form_composition⟩

#print axioms UnitalJordanProduct.exists_peirceTriangleCoordinates_of_traceUnits
#print axioms UnitalJordanProduct.exists_peirceTriangleCoordinates_of_simple
