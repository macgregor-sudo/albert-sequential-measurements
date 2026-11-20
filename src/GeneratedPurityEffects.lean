/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAGenerated
public import EuclideanPrimitiveCorner
public import PurityResiduals

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

section Effects

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (P : UnitalJordanProduct E) (p : ι → E)

/-- The actual effect-prefix map, with the first outcome acting outermost. -/
def sequentialEffectTransform : Word ι → E →ₗ[ℝ] E
  | [] => LinearMap.id
  | a :: w => (P.quadraticRepresentation (P.sequentialOutcome p a)).comp (sequentialEffectTransform w)

@[simp] theorem sequentialEffectTransform_nil (x : E) : P.sequentialEffectTransform p [] x = x := rfl

@[simp] theorem sequentialEffectTransform_cons (a : Outcome ι) (w : Word ι) (x : E) :
    P.sequentialEffectTransform p (a :: w) x =
      P.quadraticRepresentation (P.sequentialOutcome p a) (P.sequentialEffectTransform p w x) := rfl

theorem sequentialEffectTransform_unit (w : Word ι) :
    P.sequentialEffectTransform p w P.unit = P.sequentialWordEffect p w := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [sequentialEffectTransform_cons,ih,sequentialWordEffect]

theorem sequentialEffectTransform_append (u v : Word ι) (x : E) :
    P.sequentialEffectTransform p (u ++ v) x =
      P.sequentialEffectTransform p u (P.sequentialEffectTransform p v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => rw [List.cons_append,sequentialEffectTransform_cons,sequentialEffectTransform_cons,ih]

theorem sequentialOutcome_square (hp : ∀ i, P.product (p i) (p i) = p i) (a : Outcome ι) :
    P.product (P.sequentialOutcome p a) (P.sequentialOutcome p a) = P.sequentialOutcome p a := by
  rcases a with ⟨i,s⟩
  cases s with
  | true => exact hp i
  | false =>
    have hu : P.product (p i) P.unit = p i := (P.commutative _ _).trans (P.unit_left _)
    change P.product (P.unit-p i) (P.unit-p i) = P.unit-p i
    simp only [map_sub,LinearMap.sub_apply,P.unit_left,hu,hp]
    abel

private theorem quadratic_unit_left (x : E) : P.quadraticRepresentation P.unit x = x := by
  rw [quadraticRepresentation_apply]
  simp only [P.unit_left,two_smul,add_sub_cancel_right]

private theorem quadratic_scale_left (r : ℝ) (a x : E) :
    P.quadraticRepresentation (r • a) x = r ^ 2 • P.quadraticRepresentation a x := by
  simp only [quadraticRepresentation_apply,map_smul,LinearMap.smul_apply,smul_smul,smul_sub]
  module

/-- The mirror excludes the last outcome. The empty word uses the unit quadratic. -/
theorem sequentialWordEffect_quadratic_mirror (hp : ∀ i, P.product (p i) (p i) = p i)
    (v : Word ι) (x : E) :
    P.sequentialEffectTransform p (v ++ purityMirror v) x =
      P.quadraticRepresentation (P.sequentialWordEffect p v) x := by
  induction v generalizing x with
  | nil => exact (P.quadratic_unit_left x).symm
  | cons a w ih =>
    cases w with
    | nil =>
      change P.quadraticRepresentation (P.sequentialOutcome p a) x =
        P.quadraticRepresentation (P.quadraticRepresentation (P.sequentialOutcome p a) P.unit) x
      rw [P.quadraticRepresentation_unit,P.sequentialOutcome_square p hp]
    | cons b w =>
      have hmirror : purityMirror (a :: b :: w) = purityMirror (b :: w) ++ [a] := by
        simp only [purityMirror,List.dropLast_cons_cons,List.reverse_cons]
      rw [hmirror,List.cons_append,← List.append_assoc]
      change P.sequentialEffectTransform p (a :: (((b :: w) ++ purityMirror (b :: w)) ++ [a])) x =
        P.quadraticRepresentation
          (P.quadraticRepresentation (P.sequentialOutcome p a) (P.sequentialWordEffect p (b :: w))) x
      rw [P.sequentialEffectTransform_cons,
        P.sequentialEffectTransform_append p ((b :: w) ++ purityMirror (b :: w)) [a],
        ih,P.sequentialEffectTransform_cons,P.sequentialEffectTransform_nil,
        P.quadraticRepresentation_fundamental]

end Effects

section Generated

open scoped InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (p : ι → E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))

local notation "B" => P.generatedMenuProduct p
local notation "hB" => P.generatedMenuProduct_inner p hinner
local notation "hfr" => P.formallyReal_of_associative_inner hinner
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation "pairing" => P.canonicalTraceFormOfFormallyReal hfr

def generatedMenuOutcome (q : Outcome ι) : P.generatedMenuCarrier p :=
  (B).sequentialOutcome (P.generatedMenuTest p) q

omit [FiniteDimensional ℝ E] in
@[simp] theorem generatedMenuOutcome_val (q : Outcome ι) :
    (P.generatedMenuOutcome p q).val = P.sequentialOutcome p q := by
  rcases q with ⟨i,s⟩
  cases s <;> rfl

/-- The denominator is the ambient trace square. The primitive hypothesis is
on the generated carrier. -/
theorem generated_primitive_quadratic_coefficient (q x : P.generatedMenuCarrier p)
    (hq : (B).IsPrimitive q) :
    P.quadraticRepresentation q.val x.val = (pairing q.val x.val / pairing q.val q.val) • q.val := by
  let r := inner ℝ q x / inner ℝ q q
  have hc := congrArg Subtype.val ((B).primitive_quadraticRepresentation_coefficient hB q x hq)
  change P.quadraticRepresentation q.val x.val = r • q.val at hc
  have hq0 : q.val ≠ 0 := fun he => hq.2.1 (Subtype.ext he)
  have hqidem : P.product q.val q.val = q.val := congrArg Subtype.val hq.1
  have hden : pairing q.val q.val ≠ 0 :=
    (P.canonicalTraceFormOfFormallyReal_positive hfr _ hq0).ne'
  have hnum : r * pairing q.val q.val = pairing q.val x.val := by
    calc
      _ = pairing q.val (r • q.val) := by rw [map_smul,smul_eq_mul]
      _ = pairing q.val (P.quadraticRepresentation q.val x.val) := by rw [hc]
      _ = pairing (P.quadraticRepresentation q.val q.val) x.val :=
        (P.canonicalTrace_quadraticRepresentation_pairing hfr q.val q.val x.val).symm
      _ = _ := by rw [P.quadraticRepresentation_idempotent_self _ hqidem]
  rw [hc,(eq_div_iff hden).mpr hnum]

/-- The literal scalar λ_q(θ(v)), using the ambient pairing. -/
def generatedPurityCoefficient (q : Outcome ι) (v : Word ι) : ℝ :=
  pairing (P.sequentialOutcome p q) (P.sequentialWordEffect p v) /
    pairing (P.sequentialOutcome p q) (P.sequentialOutcome p q)

theorem generatedPurityCoefficient_eq_branchTrace_div (q : Outcome ι) (v : Word ι) :
    P.generatedPurityCoefficient p hinner q v =
      τ (P.sequentialBranchState p (P.sequentialOutcome p q) v) /
        pairing (P.sequentialOutcome p q) (P.sequentialOutcome p q) := by
  rw [generatedPurityCoefficient,P.canonicalTrace_sequentialBranchState]
  rfl

theorem generatedPurity_compress_effect (q : Outcome ι)
    (hq : (B).IsPrimitive (P.generatedMenuOutcome p q)) (v : Word ι) :
    P.quadraticRepresentation (P.sequentialOutcome p q) (P.sequentialWordEffect p v) =
      P.generatedPurityCoefficient p hinner q v • P.sequentialOutcome p q := by
  have hc := P.generated_primitive_quadratic_coefficient p hinner (P.generatedMenuOutcome p q)
    ((B).sequentialWordEffect (P.generatedMenuTest p) v) hq
  simpa only [generatedMenuOutcome_val,generatedMenu_sequentialWordEffect,generatedPurityCoefficient] using hc

theorem generatedPurity_three_effects (hp : ∀ i, P.product (p i) (p i) = p i)
    (q : Outcome ι) (hq : (B).IsPrimitive (P.generatedMenuOutcome p q)) (v : Word ι) :
    let c := P.generatedPurityCoefficient p hinner q v
    let a := P.sequentialOutcome p q
    P.sequentialWordEffect p ([q] ++ v ++ purityMirror v ++ [q]) = c ^ 2 • a ∧
    P.sequentialWordEffect p ([q] ++ v) = c • a ∧ P.sequentialWordEffect p [q] = a := by
  intro c a
  have hid : P.product a a = a := P.sequentialOutcome_square p hp q
  have hshort : P.sequentialWordEffect p [q] = a := by
    change P.quadraticRepresentation a P.unit = a
    rw [P.quadraticRepresentation_unit,hid]
  have hcomp : P.quadraticRepresentation a (P.sequentialWordEffect p v) = c • a :=
    P.generatedPurity_compress_effect p hinner q hq v
  refine ⟨?_,hcomp,hshort⟩
  change P.sequentialWordEffect p (q :: (((v ++ purityMirror v) ++ [q]))) = c ^ 2 • a
  rw [sequentialWordEffect,← P.sequentialEffectTransform_unit p (v ++ purityMirror v ++ [q]),
    P.sequentialEffectTransform_append p (v ++ purityMirror v) [q],
    P.sequentialWordEffect_quadratic_mirror p hp,
    P.sequentialEffectTransform_cons,P.sequentialEffectTransform_nil]
  change P.quadraticRepresentation a
    (P.quadraticRepresentation (P.sequentialWordEffect p v) (P.quadraticRepresentation a P.unit)) = _
  rw [← P.quadraticRepresentation_fundamental,hcomp,P.quadratic_scale_left,
    P.quadraticRepresentation_unit,hid]

/-- The three actual words give zero effect in the ambient EJA. -/
theorem generatedPurity_effect_residual (hp : ∀ i, P.product (p i) (p i) = p i)
    (q : Outcome ι) (hq : (B).IsPrimitive (P.generatedMenuOutcome p q)) (v : Word ι) :
    let c := P.generatedPurityCoefficient p hinner q v
    P.sequentialWordEffect p ([q] ++ v ++ purityMirror v ++ [q]) -
      (2 * c) • P.sequentialWordEffect p ([q] ++ v) +
      c ^ 2 • P.sequentialWordEffect p [q] = 0 := by
  intro c
  obtain ⟨h₁,h₂,h₃⟩ := P.generatedPurity_three_effects p hinner hp q hq v
  rw [h₁,h₂,h₃]
  module

/-- Probability-side residual for every raw initial state and prefix. -/
theorem generatedPurity_probability_residual (hp : ∀ i, P.product (p i) (p i) = p i)
    (q : Outcome ι) (hq : (B).IsPrimitive (P.generatedMenuOutcome p q)) (v t : Word ι) (ρ : E) :
    let c := P.generatedPurityCoefficient p hinner q v
    let f := fun w => τ (P.sequentialBranchState p ρ w)
    f (t ++ [q] ++ v ++ purityMirror v ++ [q]) -
      2 * c * f (t ++ [q] ++ v) + c ^ 2 * f (t ++ [q]) = 0 := by
  intro c f
  let φ := P.canonicalPairingFunctional hfr (P.sequentialBranchState p ρ t)
  have hpre (w : Word ι) : f (t ++ w) = φ (P.sequentialWordEffect p w) := by
    change τ (P.sequentialBranchState p ρ (t ++ w)) = _
    unfold sequentialBranchState
    rw [List.foldl_append]
    exact P.canonicalTrace_sequentialBranchState hfr p (P.sequentialBranchState p ρ t) w
  simp only [List.append_assoc,hpre]
  have h := congrArg φ (P.generatedPurity_effect_residual p hinner hp q hq v)
  simpa only [map_add,map_sub,map_smul,map_zero,smul_eq_mul,c,List.append_assoc] using h

end Generated
end AlbertSequential.UnitalJordanProduct
