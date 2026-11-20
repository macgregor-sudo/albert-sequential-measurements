/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceQuaternionicInstrument
public import HilbertTraceBasisPairing

/-! Comparing the normalized realified trace with quaternionic basis diagonals. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace BigOperators

namespace AlbertSequential.HilbertTrace

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem quaternionicSignedFiniteTrace_basis_eq (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H)
    (S : RightQuaternionicHilbertStructure H) :
    quaternionicSignedFiniteTrace b S = quaternionicSignedFiniteTrace c S := by
  unfold quaternionicSignedFiniteTrace
  rw [real_signedFiniteTrace_basis_eq b c]

theorem quaternionicTracePairing_basis_eq (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H)
    (S : RightQuaternionicHilbertStructure H) (A : S.toOperatorStructure.operatorAlgebra)
    (X : quaternionicSignedFiniteTrace b S) (Y : quaternionicSignedFiniteTrace c S) (h : X.val = Y.val) :
    quaternionicTracePairing b S A X = quaternionicTracePairing c S A Y := by
  change (1 / 4 : ℝ) * signedTracePairing b A.val (quaternionicCarrierInclusion b S X) =
    (1 / 4 : ℝ) * signedTracePairing c A.val (quaternionicCarrierInclusion c S Y)
  rw [real_signedTracePairing_basis_eq b c A.val (quaternionicCarrierInclusion b S X)
    (quaternionicCarrierInclusion c S Y) h]

/-- In a real Hilbert basis expanded from four orthogonal unit phases of each quaternionic basis
vector, the weighted normalized trace is exactly the real part of the quaternionic diagonal sum.
The usual phases are `1, I, J, K`; a different unit phase expansion gives the same calculation. -/
theorem quaternionicTracePairing_eq_quaternionic_diagonal
    (b : HilbertBasis (ι × Fin 4) ℝ H) (S : RightQuaternionicHilbertStructure H)
    (A : S.toOperatorStructure.operatorAlgebra) (T : quaternionicSignedFiniteTrace b S)
    (u : ι → H) (phase : Fin 4 → Quaternion ℝ) (hunit : ∀ j, ‖phase j‖ = 1)
    (hb : ∀ i j, b (i,j) = S.rightScalar (phase j) (u i)) :
    quaternionicTracePairing b S A T =
      ∑' i, (S.quaternionInner (A.val (T.val (u i))) (u i)).re := by
  let f (p : ι × Fin 4) := RCLike.re ⟪A.val (T.val (b p)), b p⟫_ℝ
  let g (i : ι) := (S.quaternionInner (A.val (T.val (u i))) (u i)).re
  have hs : Summable f := (real_summable_tracePairing b A.val (quaternionicCarrierInclusion b S T)).of_norm
  have hA := (S.mem_operatorAlgebra_iff_rightLinear A.val).mp A.property
  have hT := (S.mem_operatorAlgebra_iff_rightLinear T.val).mp T.property.2
  have hf (i j) : f (i,j) = g i := by
    change RCLike.re ⟪A.val (T.val (b (i,j))), b (i,j)⟫_ℝ = _
    rw [hb, hT (phase j) (u i), hA (phase j) (T.val (u i)), RCLike.re_to_real]
    let R : H →ₗᵢ[ℝ] H := ⟨(S.rightScalar (phase j)).toLinearMap, by
      intro y
      change ‖S.rightScalar (phase j) y‖ = ‖y‖
      rw [S.norm_rightScalar, hunit, mul_one]⟩
    change ⟪R (A.val (T.val (u i))), R (u i)⟫_ℝ = g i
    rw [R.inner_map_map]
    exact (S.inner_re _ _).symm
  change (1 / 4 : ℝ) * (∑' p, f p) = ∑' i, g i
  calc
    _ = (1 / 4 : ℝ) * ∑' i, ∑' j, f (i,j) := by
      rw [hs.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
    _ = (1 / 4 : ℝ) * ∑' i, 4 * g i := by
      congr 1
      refine tsum_congr fun i => ?_
      simp [hf, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
    _ = ∑' i, g i := by rw [tsum_mul_left]; ring

/-- The normalized native pairing in any real Hilbert basis may be evaluated using a
four-phase expansion of a quaternionic basis. -/
theorem quaternionicTracePairing_eq_quaternionic_diagonal_of_basis_change
    (b : HilbertBasis κ ℝ H) (c : HilbertBasis (ι × Fin 4) ℝ H)
    (S : RightQuaternionicHilbertStructure H) (A : S.toOperatorStructure.operatorAlgebra)
    (T : quaternionicSignedFiniteTrace b S) (u : ι → H) (phase : Fin 4 → Quaternion ℝ)
    (hunit : ∀ j, ‖phase j‖ = 1) (hc : ∀ i j, c (i,j) = S.rightScalar (phase j) (u i)) :
    quaternionicTracePairing b S A T =
      ∑' i, (S.quaternionInner (A.val (T.val (u i))) (u i)).re := by
  let U : quaternionicSignedFiniteTrace c S := ⟨T.val, quaternionicSignedFiniteTrace_basis_eq b c S ▸ T.property⟩
  exact (quaternionicTracePairing_basis_eq b c S A T U rfl).trans
    (quaternionicTracePairing_eq_quaternionic_diagonal c S A U u phase hunit hc)

end AlbertSequential.HilbertTrace
