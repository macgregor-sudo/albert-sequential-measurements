/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTracePairing
public import HilbertTraceModulus
public import HilbertTraceQuaternionic

/-! The normalized trace on the actual right-quaternionic operator carrier. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℝ H) (S : RightQuaternionicHilbertStructure H)

/-- The actual right-linear operators in the realified signed finite-trace carrier. -/
def quaternionicSignedFiniteTrace : Submodule ℝ (H →L[ℝ] H) :=
  signedFiniteTrace b ⊓ S.toOperatorStructure.operatorAlgebra.toSubalgebra.toSubmodule

theorem mem_quaternionicSignedFiniteTrace_iff (T : H →L[ℝ] H) :
    T ∈ quaternionicSignedFiniteTrace b S ↔ T ∈ signedFiniteTrace b ∧ S.IsRightLinear T := by
  exact and_congr_right (fun _ => S.mem_operatorAlgebra_iff_rightLinear T)

/-- The real part of the quaternionic trace is one quarter of the real trace. -/
def quaternionicSignedTrace : quaternionicSignedFiniteTrace b S →ₗ[ℝ] ℝ :=
  (1 / 4 : ℝ) • (signedTrace b).comp (Submodule.inclusion inf_le_left)

theorem quaternionicDyad_mem_signedFiniteTrace (u : H) :
    quaternionicDyad S u u ∈ quaternionicSignedFiniteTrace b S := by
  refine ⟨IsPositiveFiniteTrace.mem_signedFiniteTrace b ?_, quaternionicDyad_mem_operatorAlgebra S u u⟩
  refine ⟨quaternionicDyad_self_isPositive S u, ?_⟩
  rw [positiveTrace_quaternionicDyad_self]
  exact ENNReal.ofReal_ne_top

theorem quaternionicSignedTrace_dyad (u : H) :
    quaternionicSignedTrace b S ⟨quaternionicDyad S u u, quaternionicDyad_mem_signedFiniteTrace b S u⟩ =
      ‖u‖ ^ 2 := by
  change (1 / 4 : ℝ) * signedTrace b ⟨quaternionicDyad S u u, _⟩ = _
  rw [signedTrace_eq_positiveTrace_toReal _ _ (quaternionicDyad_self_isPositive S u)]
  change (1 / 4 : ℝ) * (positiveTrace b (quaternionicDyad S u u)).toReal = _
  rw [← quaternionicDyad_normalized_trace b S u]
  ring

/-- The real part of the native quaternionic trace pairing with an actual right-linear operator. -/
def quaternionicTracePairing (A : S.toOperatorStructure.operatorAlgebra) :
    quaternionicSignedFiniteTrace b S →ₗ[ℝ] ℝ :=
  (1 / 4 : ℝ) • (signedTracePairingLinear b A.val (fun T =>
    (real_summable_tracePairing b A.val T).of_norm)).comp (Submodule.inclusion inf_le_left)

theorem quaternionicSignedFiniteTrace_sandwich (A : S.toOperatorStructure.operatorAlgebra)
    (T : quaternionicSignedFiniteTrace b S) :
    A.val ∘L T.val ∘L ContinuousLinearMap.adjoint A.val ∈ quaternionicSignedFiniteTrace b S := by
  refine ⟨real_signedFiniteTrace_sandwich b A.val ⟨T.val, T.property.1⟩, ?_⟩
  change A.val * (T.val * star A.val) ∈ S.toOperatorStructure.operatorAlgebra
  exact mul_mem A.property (mul_mem T.property.2 (star_mem A.property))

private theorem real_modulus_commutes_with_unitary {T D R : H →L[ℝ] H}
    (hD : D.IsPositive) (hDsq : D * D = T * T) (hRT : R * T = T * R)
    (hR : star R * R = 1) (hR' : R * star R = 1) : R * D = D * R := by
  let E := R * D * star R
  have hE : E.IsPositive := hD.conj_adjoint R
  have hRT2 : R * (T * T) = (T * T) * R :=
    ((show Commute R T from hRT).mul_right (show Commute R T from hRT)).eq
  have hEsq : E * E = T * T := by
    calc
      E * E = R * (D * (star R * R) * D) * star R := by simp only [E, mul_assoc]
      _ = R * (T * T) * star R := by rw [hR, mul_one, hDsq]
      _ = (T * T) * (R * star R) := by rw [hRT2, mul_assoc]
      _ = T * T := by rw [hR', mul_one]
  have hED : E = D := real_positive_square_root_unique hE hD (hEsq.trans hDsq.symm)
  have hd := congrArg (fun A : H →L[ℝ] H => A * R) hED
  simpa only [E, mul_assoc, hR, mul_one] using hd

/-- The ordinary modulus of a right-linear self-adjoint operator is right-linear. -/
theorem quaternionic_modulus_mem_operatorAlgebra (T : S.toOperatorStructure.operatorAlgebra)
    (D : H →L[ℝ] H) (hD : D.IsPositive) (hDsq : D * D = T.val * T.val) :
    D ∈ S.toOperatorStructure.operatorAlgebra := by
  let Q := S.toOperatorStructure
  obtain ⟨hi, hj⟩ := (Q.mem_operatorAlgebra_iff T.val).mp T.property
  have hri : Q.rightI * star Q.rightI = 1 := by
    rw [Q.star_rightI, mul_neg, Q.rightI_sq, neg_neg]
  have hrj : Q.rightJ * star Q.rightJ = 1 := by
    rw [Q.star_rightJ, mul_neg, Q.rightJ_sq, neg_neg]
  exact (Q.mem_operatorAlgebra_iff D).mpr ⟨
    real_modulus_commutes_with_unitary hD hDsq hi Q.rightI_star_mul hri,
    real_modulus_commutes_with_unitary hD hDsq hj Q.rightJ_star_mul hrj⟩

/-- The realified finite-modulus criterion on the underlying actual right-linear operators. -/
theorem quaternionic_mem_signedFiniteTrace_iff_modulus (T : S.toOperatorStructure.operatorAlgebra)
    (D : H →L[ℝ] H) (hT : IsSelfAdjoint T.val) (hD : D.IsPositive)
    (hDsq : D * D = T.val * T.val) :
    T.val ∈ quaternionicSignedFiniteTrace b S ↔ positiveTrace b D ≠ ∞ := by
  rw [mem_quaternionicSignedFiniteTrace_iff]
  have h := real_mem_signedFiniteTrace_iff_modulus b T.val D hT hD hDsq
  exact ⟨fun hm => h.mp hm.1,
    fun hfin => ⟨h.mpr hfin, (S.mem_operatorAlgebra_iff_rightLinear T.val).mp T.property⟩⟩

end AlbertSequential.HilbertTrace
