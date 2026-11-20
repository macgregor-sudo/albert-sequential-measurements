/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceQuaternionicEffect

/-! The right-quaternionic trace-class instrument and its actual weighted trace. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H)

local notation "Op" => S.toOperatorStructure.operatorAlgebra
local notation "Carrier" => quaternionicSignedFiniteTrace b S
local notation "qTrace" => quaternionicSignedTrace b S
local notation "qPair" => quaternionicTracePairing b S

def IsQuaternionicDensity (T : Carrier) : Prop := T.val.IsPositive ∧ qTrace T = 1

def IsQuaternionicEffect (A : Op) : Prop := A.val.IsPositive ∧ (1 - A.val).IsPositive

structure QuaternionicInstrument where
  branchOne : Carrier →ₗ[ℝ] Carrier
  branchZero : Carrier →ₗ[ℝ] Carrier
  one_positive : ∀ X, X.val.IsPositive → (branchOne X).val.IsPositive
  zero_positive : ∀ X, X.val.IsPositive → (branchZero X).val.IsPositive
  trace_preserving : ∀ X, qTrace (branchOne X + branchZero X) = qTrace X

namespace QuaternionicInstrument

variable (M : QuaternionicInstrument b S)

def massOne : Carrier →ₗ[ℝ] ℝ := (quaternionicSignedTrace b S).comp M.branchOne

def IsIdealTest : Prop :=
  (∀ X, IsQuaternionicDensity b S X → M.massOne b S X = 1 → M.branchOne X = X) ∧
  (∀ X, IsQuaternionicDensity b S X → M.massOne b S X = 0 → M.branchZero X = X) ∧
  ¬ ∃ (T : Carrier) (F : Op),
    IsQuaternionicDensity b S T ∧ IsQuaternionicEffect S F ∧ qPair F T = 1 ∧
    ∀ X, IsQuaternionicDensity b S X → (M.massOne b S X = 0 ∨ M.massOne b S X = 1) → qPair F X = 0

theorem signedTrace_branchZero (X : Carrier) :
    qTrace (M.branchZero X) = qTrace X - M.massOne b S X := by
  have h := M.trace_preserving X
  rw [map_add] at h
  change qTrace (M.branchZero X) = qTrace X - qTrace (M.branchOne X)
  linarith

theorem massOne_dominated (X : Carrier) (hX : X.val.IsPositive) :
    0 ≤ M.massOne b S X ∧ M.massOne b S X ≤ qTrace X := by
  have hnonneg (T : Carrier) (hT : T.val.IsPositive) : 0 ≤ qTrace T := by
    change 0 ≤ (1 / 4 : ℝ) * signedTrace b (quaternionicCarrierInclusion b S T)
    rw [signedTrace_eq_positiveTrace_toReal b _ hT]
    positivity
  refine ⟨hnonneg _ (M.one_positive X hX), ?_⟩
  have hz := hnonneg _ (M.zero_positive X hX)
  rw [M.signedTrace_branchZero b S X] at hz
  exact sub_nonneg.mp hz

theorem exists_measuredEffect : ∃ A : Op, IsQuaternionicEffect S A ∧
    ∀ X : Carrier, M.massOne b S X = qPair A X := by
  obtain ⟨A, hp, hc, hA⟩ := exists_quaternionic_effect_of_trace_dominated b S
    (M.massOne b S) (M.massOne_dominated b S)
  exact ⟨A, ⟨hp, hc⟩, hA⟩

end QuaternionicInstrument

def quaternionicVectorDyad (x : H) : Carrier :=
  ⟨quaternionicDyad S x x, quaternionicDyad_mem_signedFiniteTrace b S x⟩

theorem quaternionicVectorDyad_positive (x : H) : (quaternionicVectorDyad b S x).val.IsPositive :=
  quaternionicDyad_self_isPositive S x

theorem quaternionicVectorDyad_pairing (A : Op) (x : H) :
    qPair A (quaternionicVectorDyad b S x) = ⟪A.val x, x⟫_ℝ := by
  let Q := S.toOperatorStructure
  let g := signedTracePairingLinear b A.val (fun T => (real_summable_tracePairing b A.val T).of_norm)
  have hsum : quaternionicCarrierInclusion b S (quaternionicVectorDyad b S x) =
      realVectorDyad b x + realVectorDyad b (S.rightScalar quaternionI x) +
        realVectorDyad b (S.rightScalar quaternionJ x) + realVectorDyad b (S.rightScalar quaternionK x) :=
    Subtype.ext rfl
  have hK : star (S.rightScalar quaternionK) * S.rightScalar quaternionK = 1 := by
    rw [S.rightScalar_quaternionK]
    change star (Q.rightJ * Q.rightI) * (Q.rightJ * Q.rightI) = 1
    rw [star_mul]
    calc
      _ = star Q.rightI * (star Q.rightJ * Q.rightJ) * Q.rightI := by simp only [mul_assoc]
      _ = _ := by rw [Q.rightJ_star_mul, mul_one, Q.rightI_star_mul]
  have hrot (q : Quaternion ℝ) (h : star (S.rightScalar q) * S.rightScalar q = 1) :
      ⟪A.val (S.rightScalar q x), S.rightScalar q x⟫_ℝ = ⟪A.val x, x⟫_ℝ := by
    have hA := (S.mem_operatorAlgebra_iff_rightLinear A.val).mp A.property
    rw [hA q x, ← (S.rightScalar q).adjoint_inner_right]
    have hs : ContinuousLinearMap.adjoint (S.rightScalar q) (S.rightScalar q x) = x :=
      congrArg (fun R : H →L[ℝ] H => R x) h
    rw [hs]
  change (1 / 4 : ℝ) * g (quaternionicCarrierInclusion b S (quaternionicVectorDyad b S x)) = _
  rw [hsum, map_add, map_add, map_add]
  change (1 / 4 : ℝ) * (signedTracePairing b A.val (realVectorDyad b x) +
    signedTracePairing b A.val (realVectorDyad b (S.rightScalar quaternionI x)) +
    signedTracePairing b A.val (realVectorDyad b (S.rightScalar quaternionJ x)) +
    signedTracePairing b A.val (realVectorDyad b (S.rightScalar quaternionK x))) = _
  simp only [realVectorDyad_pairing, hrot quaternionI Q.rightI_star_mul,
    hrot quaternionJ Q.rightJ_star_mul, hrot quaternionK hK]
  ring

theorem quaternionic_density_of_unit_vector (x : H) (hx : ‖x‖ = 1) :
    IsQuaternionicDensity b S (quaternionicVectorDyad b S x) := by
  refine ⟨quaternionicVectorDyad_positive b S x, ?_⟩
  change qTrace ⟨quaternionicDyad S x x, quaternionicDyad_mem_signedFiniteTrace b S x⟩ = 1
  rw [quaternionicSignedTrace_dyad, hx, one_pow]

theorem quaternionic_signedTrace_pos_iff {T : Carrier} (hT : T.val.IsPositive) :
    0 < qTrace T ↔ T.val ≠ 0 := by
  change 0 < (1 / 4 : ℝ) * signedTrace b (quaternionicCarrierInclusion b S T) ↔ _
  rw [mul_pos_iff_of_pos_left (by norm_num : 0 < (1 / 4 : ℝ))]
  exact real_signedTrace_pos_iff b hT

theorem quaternionic_pairing_nonneg_zero_iff (A : Op) (T : Carrier)
    (hA : A.val.IsPositive) (hT : T.val.IsPositive) :
    0 ≤ qPair A T ∧ (qPair A T = 0 ↔ A.val * T.val = 0) := by
  have h := real_signedTracePairing_nonneg_zero_iff b A.val (quaternionicCarrierInclusion b S T) hA hT
  change 0 ≤ (1 / 4 : ℝ) * signedTracePairing b A.val (quaternionicCarrierInclusion b S T) ∧
    ((1 / 4 : ℝ) * signedTracePairing b A.val (quaternionicCarrierInclusion b S T) = 0 ↔ _)
  refine ⟨mul_nonneg (by norm_num) h.1, ?_⟩
  rw [mul_eq_zero, or_iff_right (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  exact h.2

theorem quaternionic_tracePairing_eq_zero_of_mul_eq_zero (A : Op) (X : Carrier)
    (h : A.val * X.val = 0) : qPair A X = 0 := by
  change (1 / 4 : ℝ) * signedTracePairing b A.val (quaternionicCarrierInclusion b S X) = 0
  rw [real_tracePairing_eq_zero_of_mul_eq_zero b A.val _ h, mul_zero]

theorem quaternionicTracePairing_complement_eq (A : Op) (X : Carrier) :
    qPair (1 - A) X = qTrace X - qPair A X := by
  change (1 / 4 : ℝ) * signedTracePairing b (1 - A.val) (quaternionicCarrierInclusion b S X) =
    (1 / 4 : ℝ) * signedTrace b (quaternionicCarrierInclusion b S X) -
      (1 / 4 : ℝ) * signedTracePairing b A.val (quaternionicCarrierInclusion b S X)
  rw [realTracePairing_complement_eq, mul_sub]

theorem quaternionic_density_pairing_eq_one_iff (A : Op) (hA : IsQuaternionicEffect S A)
    (X : Carrier) (hX : IsQuaternionicDensity b S X) : qPair A X = 1 ↔ (1 - A.val) * X.val = 0 := by
  have h := (quaternionic_pairing_nonneg_zero_iff b S (1 - A) X hA.2 hX.1).2
  change qPair (1 - A) X = 0 ↔ (1 - A.val) * X.val = 0 at h
  rw [← h, quaternionicTracePairing_complement_eq, hX.2, sub_eq_zero, eq_comm]

theorem quaternionic_projection_isEffect {P : Op} (hP : IsStarProjection P) : IsQuaternionicEffect S P :=
  real_projection_isEffect (hP.map S.toOperatorStructure.operatorValue)

def quaternionicSandwich (P : Op) : Carrier →ₗ[ℝ] Carrier :=
  (((signedFiniteTrace b).subtype.comp (realSandwich b P.val)).comp
    (quaternionicCarrierInclusion b S)).codRestrict Carrier (by
      intro X
      exact quaternionicSignedFiniteTrace_sandwich b S P X)

theorem quaternionicSandwich_positive (P : Op) (X : Carrier) (hX : X.val.IsPositive) :
    (quaternionicSandwich b S P X).val.IsPositive := hX.conj_adjoint P.val

theorem signedTrace_quaternionicSandwich (P : Op) (X : Carrier) :
    qTrace (quaternionicSandwich b S P X) = qPair (star P * P) X := by
  change (1 / 4 : ℝ) * signedTrace b (realSandwich b P.val (quaternionicCarrierInclusion b S X)) =
    (1 / 4 : ℝ) * signedTracePairing b (star P.val * P.val) (quaternionicCarrierInclusion b S X)
  rw [signedTrace_realSandwich]

theorem quaternionic_signedFiniteTrace_decomposition (T : Carrier) :
    ∃ X Y : Carrier, X.val.IsPositive ∧ Y.val.IsPositive ∧ T = X - Y := by
  obtain ⟨X, Y, hX, hY, hT⟩ := T.property.1
  let U : signedFiniteTrace b := ⟨X, hX.mem_signedFiniteTrace b⟩
  let V : signedFiniteTrace b := ⟨Y, hY.mem_signedFiniteTrace b⟩
  have hEq : quaternionicCarrierInclusion b S T = U - V := Subtype.ext hT
  have hAvg := congrArg (quaternionicAverage b S) hEq
  rw [quaternionicAverage_inclusion, map_sub] at hAvg
  exact ⟨quaternionicAverage b S U, quaternionicAverage b S V, quaternionicAverage_positive b S U hX.1,
    quaternionicAverage_positive b S V hY.1, hAvg⟩

end AlbertSequential.HilbertTrace
