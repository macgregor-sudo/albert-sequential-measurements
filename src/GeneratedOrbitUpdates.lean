/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneratedReflectionOrbit
public import NativeOrbitLifts

/-! Native quadratic-update and reflection transport for a general primitive menu. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : UnitalJordanProduct E) (q : I → E)
def menuOutcomeUpdate (a : Outcome I) : Module.End ℝ E :=
  P.quadraticRepresentation (P.sequentialOutcome q a)

theorem menuReflectionUpdate_eq (i : I) (x : E) :
    sequentialReflectionUpdate (P.menuOutcomeUpdate q) i x = P.idempotentReflection (q i) x := by
  rw [P.idempotentReflection_apply]
  rfl

abbrev primitiveMenuAction (w : List I) := reflectionWordUpdate (P.menuOutcomeUpdate q) w

theorem menuAction_cons (i : I) (w : List I) (x : E) :
    primitiveMenuAction P q (i::w) x = P.idempotentReflection (q i) (primitiveMenuAction P q w x) :=
  P.menuReflectionUpdate_eq q i _

theorem menuAction_point (w : List I) (i : I) :
    primitiveMenuAction P q w (q i) = P.reflectedMenuPoint q w i := by
  induction w with
  | nil => rfl
  | cons k w ih => rw [P.menuAction_cons, ih]; rfl

theorem menuAction_append (w v : List I) (x : E) :
    primitiveMenuAction P q (w ++ v) x = primitiveMenuAction P q w (primitiveMenuAction P q v x) := by
  induction w with
  | nil => rfl
  | cons k w ih => simp only [List.cons_append, P.menuAction_cons, ih]

variable (hq : ∀ i, P.IsPrimitive (q i))
include hq
omit hq in
private theorem conjugate_quad (w : List I) (a x : E) :
    P.quadraticRepresentation (primitiveMenuAction P q w a) x =
      primitiveMenuAction P q w (P.quadraticRepresentation a (primitiveMenuAction P q w.reverse x)) := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    simp only [P.menuAction_cons, P.idempotentReflection_quadratic, ih,
      List.reverse_cons, P.menuAction_append]
    rfl

private theorem menuAction_unit (w : List I) : primitiveMenuAction P q w P.unit = P.unit := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [P.menuAction_cons, ih, P.idempotentReflection_unit _ (hq i).1]

omit hq in
theorem menuOrbit_corner (w : List I) (i : I) (x : E) :
    orbitCornerUpdate (P.menuOutcomeUpdate q) w i x =
      P.quadraticRepresentation (P.reflectedMenuPoint q w i) x := by
  rw [← P.menuAction_point, conjugate_quad]
  rfl

theorem menuOrbit_reflection (w : List I) (i : I) (x : E) :
    orbitReflectionUpdate (P.menuOutcomeUpdate q) w i x =
      P.idempotentReflection (P.reflectedMenuPoint q w i) x := by
  change primitiveMenuAction P q w (sequentialReflectionUpdate (P.menuOutcomeUpdate q) i _) = _
  rw [P.menuReflectionUpdate_eq]
  have h : (2 : ℝ) • P.reflectedMenuPoint q w i - P.unit = primitiveMenuAction P q w ((2 : ℝ) • q i - P.unit) := by
    rw [map_sub, map_smul, P.menuAction_point, menuAction_unit P q hq]
  change primitiveMenuAction P q w _ = P.quadraticRepresentation ((2 : ℝ) • P.reflectedMenuPoint q w i - P.unit) x
  rw [h, conjugate_quad]
  rfl

theorem reflectedMenuPoint_conjugate (a b : ReflectionOrbitLabel I) :
    P.reflectedMenuPoint q (reflectedOrbitLabel a b).1 (reflectedOrbitLabel a b).2 =
      P.idempotentReflection (P.reflectedMenuPoint q a.1 a.2) (P.reflectedMenuPoint q b.1 b.2) := by
  rw [← P.menuOrbit_reflection q hq]
  change P.reflectedMenuPoint q (a.1 ++ [a.2] ++ a.1.reverse ++ b.1) b.2 = _
  simp only [← P.menuAction_point, P.menuAction_append, orbitReflectionUpdate, LinearMap.comp_apply]
  rfl

end AlbertSequential.UnitalJordanProduct
