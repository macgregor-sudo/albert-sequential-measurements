/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceQuaternionicCarrier
public import HilbertTraceRealInstrument

/-! Positive trace-preserving averaging onto the right-quaternionic commutant. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H)

def quaternionicCarrierInclusion : quaternionicSignedFiniteTrace b S →ₗ[ℝ] signedFiniteTrace b :=
  Submodule.inclusion inf_le_left

private theorem sandwich_comp (R T : H →L[ℝ] H) (X : signedFiniteTrace b) :
    realSandwich b R (realSandwich b T X) = realSandwich b (R * T) X := by
  apply Subtype.ext
  change R * (T * X.val * star T) * star R = (R * T) * X.val * star (R * T)
  simp only [star_mul, mul_assoc]

private theorem sandwich_neg (R : H →L[ℝ] H) (X : signedFiniteTrace b) :
    realSandwich b (-R) X = realSandwich b R X := by
  apply Subtype.ext
  change (-R) * X.val * star (-R) = R * X.val * star R
  rw [star_neg, neg_mul, neg_mul_neg]

private theorem sandwich_one (X : signedFiniteTrace b) : realSandwich b 1 X = X := by
  apply Subtype.ext
  change (1 : H →L[ℝ] H) * X.val * star 1 = _
  rw [star_one, one_mul, mul_one]

private theorem sandwich_involutive (R : H →L[ℝ] H) (hR : R * R = -1) (X : signedFiniteTrace b) :
    realSandwich b R (realSandwich b R X) = X := by
  rw [sandwich_comp, hR, sandwich_neg, sandwich_one]

/-- The arithmetic mean of the identity map and a unitary sandwich. -/
def phaseAverage (R : H →L[ℝ] H) : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b :=
  (1 / 2 : ℝ) • (LinearMap.id + realSandwich b R)

private theorem phaseAverage_positive (R : H →L[ℝ] H) (X : signedFiniteTrace b)
    (hX : X.val.IsPositive) : (phaseAverage b R X).val.IsPositive :=
  (hX.add (realSandwich_positive b R X hX)).smul_of_nonneg (by norm_num)

private theorem phaseAverage_trace (R : H →L[ℝ] H) (hR : star R * R = 1) (X : signedFiniteTrace b) :
    signedTrace b (phaseAverage b R X) = signedTrace b X := by
  change signedTrace b ((1 / 2 : ℝ) • (X + realSandwich b R X)) = _
  rw [map_smul, map_add, signedTrace_realSandwich, hR, smul_eq_mul]
  change 1 / 2 * (signedTrace b X + signedTrace b X) = _
  ring

private theorem phaseAverage_isFixed (R : H →L[ℝ] H) (hR : R * R = -1) (X : signedFiniteTrace b) :
    realSandwich b R (phaseAverage b R X) = phaseAverage b R X := by
  change realSandwich b R ((1 / 2 : ℝ) • (X + realSandwich b R X)) =
    (1 / 2 : ℝ) • (X + realSandwich b R X)
  rw [map_smul, map_add, sandwich_involutive b R hR, add_comm]

private theorem phaseAverage_on_conjugate (R : H →L[ℝ] H) (hR : R * R = -1)
    (X : signedFiniteTrace b) : phaseAverage b R (realSandwich b R X) = phaseAverage b R X := by
  change (1 / 2 : ℝ) • (realSandwich b R X + realSandwich b R (realSandwich b R X)) =
    (1 / 2 : ℝ) • (X + realSandwich b R X)
  rw [sandwich_involutive b R hR, add_comm]

private theorem sandwich_commutes_phaseAverage (R T : H →L[ℝ] H) (h : R * T = -(T * R))
    (X : signedFiniteTrace b) : realSandwich b R (phaseAverage b T X) =
      phaseAverage b T (realSandwich b R X) := by
  change realSandwich b R ((1 / 2 : ℝ) • (X + realSandwich b T X)) =
    (1 / 2 : ℝ) • (realSandwich b R X + realSandwich b T (realSandwich b R X))
  rw [map_smul, map_add, sandwich_comp, sandwich_comp, h, sandwich_neg]

private theorem fixed_iff_commutes (R : H →L[ℝ] H) (hR : star R * R = 1) (hR' : R * star R = 1)
    (X : signedFiniteTrace b) : realSandwich b R X = X ↔ R * X.val = X.val * R := by
  constructor
  · intro h
    have hh := congrArg (fun Y : signedFiniteTrace b => Y.val * R) h
    change R * X.val * star R * R = X.val * R at hh
    simpa only [mul_assoc, hR, mul_one] using hh
  · intro h
    apply Subtype.ext
    change R * X.val * star R = X.val
    rw [h, mul_assoc, hR', mul_one]

/-- The two consecutive generator averages on the real signed carrier. -/
def phasePairAverage : signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b :=
  (phaseAverage b S.toOperatorStructure.rightI).comp (phaseAverage b S.toOperatorStructure.rightJ)

private theorem rightI_mul_star : S.toOperatorStructure.rightI * star S.toOperatorStructure.rightI = 1 := by
  let Q := S.toOperatorStructure
  change Q.rightI * star Q.rightI = 1
  rw [Q.star_rightI, mul_neg, Q.rightI_sq, neg_neg]

private theorem rightJ_mul_star : S.toOperatorStructure.rightJ * star S.toOperatorStructure.rightJ = 1 := by
  let Q := S.toOperatorStructure
  change Q.rightJ * star Q.rightJ = 1
  rw [Q.star_rightJ, mul_neg, Q.rightJ_sq, neg_neg]

private theorem phasePairAverage_mem (X : signedFiniteTrace b) :
    (phasePairAverage b S X).val ∈ quaternionicSignedFiniteTrace b S := by
  let Q := S.toOperatorStructure
  refine ⟨(phasePairAverage b S X).property, (Q.mem_operatorAlgebra_iff _).mpr ⟨?_, ?_⟩⟩
  · apply (fixed_iff_commutes b Q.rightI Q.rightI_star_mul (rightI_mul_star S) _).mp
    exact phaseAverage_isFixed b Q.rightI Q.rightI_sq _
  · apply (fixed_iff_commutes b Q.rightJ Q.rightJ_star_mul (rightJ_mul_star S) _).mp
    change realSandwich b Q.rightJ (phaseAverage b Q.rightI (phaseAverage b Q.rightJ X)) = _
    have hanti : Q.rightJ * Q.rightI = -(Q.rightI * Q.rightJ) := by
      rw [Q.anticommute, neg_neg]
    rw [sandwich_commutes_phaseAverage b _ _ hanti, phaseAverage_isFixed b Q.rightJ Q.rightJ_sq]
    rfl

/-- The positive trace-preserving projection of real trace-class operators onto the quaternionic
commutant, obtained by averaging conjugations by the actual two right phases. -/
def quaternionicAverage : signedFiniteTrace b →ₗ[ℝ] quaternionicSignedFiniteTrace b S :=
  (((signedFiniteTrace b).subtype).comp (phasePairAverage b S)).codRestrict
    (quaternionicSignedFiniteTrace b S) (by intro X; exact phasePairAverage_mem b S X)

theorem quaternionicAverage_positive (X : signedFiniteTrace b) (hX : X.val.IsPositive) :
    (quaternionicAverage b S X).val.IsPositive :=
  phaseAverage_positive b _ _ (phaseAverage_positive b _ X hX)

theorem quaternionicAverage_trace (X : signedFiniteTrace b) :
    4 * quaternionicSignedTrace b S (quaternionicAverage b S X) = signedTrace b X := by
  let Q := S.toOperatorStructure
  change 4 * ((1 / 4 : ℝ) * signedTrace b (phaseAverage b Q.rightI (phaseAverage b Q.rightJ X))) = _
  rw [phaseAverage_trace b Q.rightI Q.rightI_star_mul, phaseAverage_trace b Q.rightJ Q.rightJ_star_mul]
  ring

theorem quaternionicAverage_inclusion (X : quaternionicSignedFiniteTrace b S) :
    quaternionicAverage b S (quaternionicCarrierInclusion b S X) = X := by
  let Q := S.toOperatorStructure
  obtain ⟨hi, hj⟩ := (Q.mem_operatorAlgebra_iff X.val).mp X.property.2
  let Y := quaternionicCarrierInclusion b S X
  have hI : realSandwich b Q.rightI Y = Y :=
    (fixed_iff_commutes b Q.rightI Q.rightI_star_mul (rightI_mul_star S) _).mpr hi
  have hJ : realSandwich b Q.rightJ Y = Y :=
    (fixed_iff_commutes b Q.rightJ Q.rightJ_star_mul (rightJ_mul_star S) _).mpr hj
  have havg {R : H →L[ℝ] H} (h : realSandwich b R Y = Y) : phaseAverage b R Y = Y := by
    change (1 / 2 : ℝ) • (Y + realSandwich b R Y) = Y
    rw [h, ← two_smul ℝ, smul_smul]
    norm_num
  apply Subtype.ext
  change (phaseAverage b Q.rightI (phaseAverage b Q.rightJ Y)).val = X.val
  rw [havg hJ, havg hI]
  rfl

theorem quaternionicAverage_conj_I (X : signedFiniteTrace b) :
    quaternionicAverage b S (realSandwich b S.toOperatorStructure.rightI X) = quaternionicAverage b S X := by
  let Q := S.toOperatorStructure
  apply Subtype.ext
  change (phaseAverage b Q.rightI (phaseAverage b Q.rightJ (realSandwich b Q.rightI X))).val = _
  rw [← sandwich_commutes_phaseAverage b _ _ Q.anticommute, phaseAverage_on_conjugate b Q.rightI Q.rightI_sq]
  rfl

theorem quaternionicAverage_conj_J (X : signedFiniteTrace b) :
    quaternionicAverage b S (realSandwich b S.toOperatorStructure.rightJ X) = quaternionicAverage b S X := by
  let Q := S.toOperatorStructure
  apply Subtype.ext
  change (phaseAverage b Q.rightI (phaseAverage b Q.rightJ (realSandwich b Q.rightJ X))).val = _
  rw [phaseAverage_on_conjugate b Q.rightJ Q.rightJ_sq]
  rfl

end AlbertSequential.HilbertTrace
