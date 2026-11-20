/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceComplexEffect
public import HilbertTraceEndpointProjections

/-! Complex trace-class states, effects, instruments and their certainty faces. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℂ H)

def IsComplexDensity (T : signedFiniteTrace b) : Prop := T.val.IsPositive ∧ signedTrace b T = 1

def IsComplexEffect (A : H →L[ℂ] H) : Prop := A.IsPositive ∧ (1 - A).IsPositive

structure ComplexInstrument where
  branchOne : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b
  branchZero : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b
  one_positive : ∀ X, X.val.IsPositive → (branchOne X).val.IsPositive
  zero_positive : ∀ X, X.val.IsPositive → (branchZero X).val.IsPositive
  trace_preserving : ∀ X, signedTrace b (branchOne X + branchZero X) = signedTrace b X

namespace ComplexInstrument

variable (M : ComplexInstrument b)

def massOne : signedFiniteTrace b →ₗ[ℝ] ℝ := (signedTrace b).comp M.branchOne

def IsIdealTest : Prop :=
  (∀ X, IsComplexDensity b X → M.massOne b X = 1 → M.branchOne X = X) ∧
  (∀ X, IsComplexDensity b X → M.massOne b X = 0 → M.branchZero X = X) ∧
  ¬ ∃ (S : signedFiniteTrace b) (F : H →L[ℂ] H),
    IsComplexDensity b S ∧ IsComplexEffect F ∧ signedTracePairing b F S = 1 ∧
      ∀ X, IsComplexDensity b X → (M.massOne b X = 0 ∨ M.massOne b X = 1) →
        signedTracePairing b F X = 0

theorem signedTrace_branchZero (X : signedFiniteTrace b) :
    signedTrace b (M.branchZero X) = signedTrace b X - M.massOne b X := by
  have h := M.trace_preserving X
  rw [map_add] at h
  change signedTrace b (M.branchZero X) = signedTrace b X - signedTrace b (M.branchOne X)
  linarith

theorem massOne_dominated (X : signedFiniteTrace b) (hX : X.val.IsPositive) :
    0 ≤ M.massOne b X ∧ M.massOne b X ≤ signedTrace b X := by
  have hone := signedTrace_eq_positiveTrace_toReal b (M.branchOne X) (M.one_positive X hX)
  have hzero := signedTrace_eq_positiveTrace_toReal b (M.branchZero X) (M.zero_positive X hX)
  have h₀ : 0 ≤ signedTrace b (M.branchZero X) := hzero ▸ ENNReal.toReal_nonneg
  refine ⟨hone ▸ ENNReal.toReal_nonneg, ?_⟩
  rw [M.signedTrace_branchZero b X] at h₀
  exact sub_nonneg.mp h₀

theorem exists_measuredEffect : ∃ A : H →L[ℂ] H, IsComplexEffect A ∧
    ∀ X : signedFiniteTrace b, M.massOne b X = signedTracePairing b A X := by
  obtain ⟨A, hp, hc, hA⟩ := exists_complex_effect_of_trace_dominated b (M.massOne b) (M.massOne_dominated b)
  exact ⟨A, ⟨hp, hc⟩, hA⟩

end ComplexInstrument

omit [CompleteSpace H] in
theorem complexVectorDyad_positive (x : H) : (complexVectorDyad b x).val.IsPositive :=
  InnerProductSpace.isPositive_rankOne_self x

omit [CompleteSpace H] in
theorem complexVectorDyad_pairing (A : H →L[ℂ] H) (x : H) :
    signedTracePairing b A (complexVectorDyad b x) = RCLike.re ⟪A x, x⟫_ℂ := by
  change signedTracePairing b A ⟨InnerProductSpace.rankOne ℂ x x, rankOne_mem_signedFiniteTrace b x⟩ = _
  exact signedTracePairing_rankOne b A x

theorem complexVectorDyad_trace (x : H) : signedTrace b (complexVectorDyad b x) = ‖x‖ ^ 2 := by
  change signedTracePairing b 1 (complexVectorDyad b x) = _
  rw [complexVectorDyad_pairing, one_apply_eq_self, inner_self_eq_norm_sq]

theorem complex_density_of_unit_vector (x : H) (hx : ‖x‖ = 1) : IsComplexDensity b (complexVectorDyad b x) := by
  refine ⟨complexVectorDyad_positive b x, ?_⟩
  rw [complexVectorDyad_trace, hx, one_pow]

theorem complex_signedTrace_pos_iff {X : signedFiniteTrace b} (hX : X.val.IsPositive) :
    0 < signedTrace b X ↔ X.val ≠ 0 := by
  have hfin := (IsPositiveFiniteTrace.of_mem_signedFiniteTrace b X.property hX).2
  rw [signedTrace_eq_positiveTrace_toReal b X hX, ENNReal.toReal_pos_iff,
    and_iff_left (lt_top_iff_ne_top.mpr hfin),
    pos_iff_ne_zero]
  exact not_congr (complex_positiveTrace_eq_zero_iff b hX)

omit [CompleteSpace H] in
theorem complex_tracePairing_eq_zero_of_mul_eq_zero (A : H →L[ℂ] H) (X : signedFiniteTrace b)
    (h : A * X.val = 0) : signedTracePairing b A X = 0 := by
  unfold signedTracePairing
  have hz (i : ι) : A (X.val (b i)) = 0 := congrArg (fun B : H →L[ℂ] H => B (b i)) h
  simp only [hz, inner_zero_left, map_zero, tsum_zero]

theorem complex_density_pairing_eq_one_iff (A : H →L[ℂ] H) (hA : IsComplexEffect A)
    (X : signedFiniteTrace b) (hX : IsComplexDensity b X) :
    signedTracePairing b A X = 1 ↔ (1 - A) * X.val = 0 := by
  rw [← (complex_signedTracePairing_nonneg_zero_iff b (1 - A) X hA.2 hX.1).2,
    complexTracePairing_complement_eq, hX.2, sub_eq_zero, eq_comm]

theorem complex_projection_isEffect {P : H →L[ℂ] H} (hP : IsStarProjection P) : IsComplexEffect P := by
  have hp {T : H →L[ℂ] H} (hT : IsStarProjection T) : T.IsPositive := by
    have h := ContinuousLinearMap.isPositive_adjoint_comp_self T
    change (star T * T).IsPositive at h
    rwa [hT.isSelfAdjoint.star_eq, hT.isIdempotentElem.eq] at h
  exact ⟨hp hP, hp hP.one_sub⟩

def complexSandwich (P : H →L[ℂ] H) : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b where
  toFun X := ⟨P * X.val * star P, by exact complex_signedFiniteTrace_sandwich b P X⟩
  map_add' X Y := by
    apply Subtype.ext
    change P * (X.val + Y.val) * star P = P * X.val * star P + P * Y.val * star P
    rw [mul_add, add_mul]
  map_smul' t X := by
    apply Subtype.ext
    change P * (t • X.val) * star P = t • (P * X.val * star P)
    rw [mul_smul_comm, smul_mul_assoc]

theorem complexSandwich_positive (P : H →L[ℂ] H) (X : signedFiniteTrace b) (hX : X.val.IsPositive) :
    (complexSandwich b P X).val.IsPositive := hX.conj_adjoint P

/-- Cyclicity in the form used by an actual trace-class sandwich. -/
theorem signedTrace_complexSandwich (P : H →L[ℂ] H) (X : signedFiniteTrace b) :
    signedTrace b (complexSandwich b P X) = signedTracePairing b (star P * P) X := by
  let f := (signedTrace b).comp (complexSandwich b P)
  let g := signedTracePairingLinear b (star P * P)
    (fun T => (complex_summable_tracePairing b (star P * P) T).of_norm)
  have hp (T : signedFiniteTrace b) (hT : T.val.IsPositive) : f T = g T := by
    obtain ⟨B, _, _, hB⟩ := exists_selfAdjoint_factor hT
    have hfin := (IsPositiveFiniteTrace.of_mem_signedFiniteTrace b T.property hT).2
    rw [← hB, positiveTrace_comp_adjoint] at hfin
    have hmul : (complexSandwich b P T).val = (P ∘L B) ∘L ContinuousLinearMap.adjoint (P ∘L B) := by
      change P * T.val * star P = (P * B) * star (P * B)
      have hBmul : B * star B = T.val := hB
      rw [← hBmul, star_mul]
      simp only [mul_assoc]
    change signedTrace b (complexSandwich b P T) = signedTracePairing b (star P * P) T
    rw [signedTrace_eq_positiveTrace_toReal b _ (complexSandwich_positive b P T hT), hmul,
      positiveTrace_comp_adjoint, hilbertSchmidtMassSq,
      ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
      signedTracePairing_eq_factor_sum b b (star P * P) B T hB hfin]
    refine tsum_congr fun i => ?_
    change (ENNReal.ofReal (‖P (B (b i))‖ ^ 2)).toReal =
      RCLike.re ⟪ContinuousLinearMap.adjoint P (P (B (b i))), B (b i)⟫_ℂ
    rw [ENNReal.toReal_ofReal (sq_nonneg _), P.adjoint_inner_left, inner_self_eq_norm_sq]
  obtain ⟨U₀, V₀, hU, hV, hX⟩ := X.property
  let U : signedFiniteTrace b := ⟨U₀, hU.mem_signedFiniteTrace b⟩
  let V : signedFiniteTrace b := ⟨V₀, hV.mem_signedFiniteTrace b⟩
  have hd : X = U - V := Subtype.ext hX
  change f X = g X
  rw [hd, map_sub, map_sub, hp U hU.1, hp V hV.1]

end AlbertSequential.HilbertTrace
