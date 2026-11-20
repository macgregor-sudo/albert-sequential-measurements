/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Basis-independent positive trace and dyad expansion on Hilbert spaces. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace AlbertSequential.HilbertTrace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {ι κ : Type*}

omit [CompleteSpace H] in
theorem hasSum_normSq_inner (b : HilbertBasis ι 𝕜 H) (x : H) :
    HasSum (fun i => ‖⟪b i, x⟫_𝕜‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).hasSum (b.hasSum_inner_mul_inner x x)
  rw [RCLike.reCLM_apply, inner_self_eq_norm_sq] at h
  refine h.congr_fun fun i => ?_
  rw [← inner_conj_symm, RCLike.mul_conj, RCLike.norm_conj,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]

omit [CompleteSpace H] in
theorem tsum_ofReal_normSq_inner (b : HilbertBasis ι 𝕜 H) (x : H) :
    ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_𝕜‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg ‖⟪b i, x⟫_𝕜‖)
    (hasSum_normSq_inner b x).summable, (hasSum_normSq_inner b x).tsum_eq]

/-- The square of the Hilbert–Schmidt norm, allowing an infinite value. -/
def hilbertSchmidtMassSq (b : HilbertBasis ι 𝕜 H) (A : H →L[𝕜] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)

theorem hilbertSchmidtMassSq_adjoint (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 H)
    (A : H →L[𝕜] H) :
    hilbertSchmidtMassSq b A = hilbertSchmidtMassSq c (ContinuousLinearMap.adjoint A) := by
  calc
    hilbertSchmidtMassSq b A = ∑' i, ∑' j, ENNReal.ofReal (‖⟪c j, A (b i)⟫_𝕜‖ ^ 2) :=
      tsum_congr fun i => (tsum_ofReal_normSq_inner c (A (b i))).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪c j, A (b i)⟫_𝕜‖ ^ 2) := tsum_comm
    _ = hilbertSchmidtMassSq c (ContinuousLinearMap.adjoint A) := by
      refine tsum_congr fun j => ?_
      rw [← tsum_ofReal_normSq_inner b (ContinuousLinearMap.adjoint A (c j))]
      refine tsum_congr fun i => ?_
      rw [← A.adjoint_inner_left (b i) (c j), norm_inner_symm]

theorem hilbertSchmidtMassSq_basis_independent (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 H)
    (A : H →L[𝕜] H) : hilbertSchmidtMassSq b A = hilbertSchmidtMassSq c A := by
  rw [hilbertSchmidtMassSq_adjoint b c A,
    hilbertSchmidtMassSq_adjoint c c (ContinuousLinearMap.adjoint A),
    ContinuousLinearMap.adjoint_adjoint]

/-- The extended diagonal trace. On positive inputs its summands are nonnegative. -/
def positiveTrace (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re ⟪T (b i), b i⟫_𝕜)

theorem positiveTrace_adjoint_comp_self (b : HilbertBasis ι 𝕜 H) (A : H →L[𝕜] H) :
    positiveTrace b (ContinuousLinearMap.adjoint A ∘L A) = hilbertSchmidtMassSq b A := by
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.comp_apply, A.adjoint_inner_left, inner_self_eq_norm_sq]

omit [CompleteSpace H] in
theorem positiveTrace_rankOne (b : HilbertBasis ι 𝕜 H) (x : H) :
    positiveTrace b (InnerProductSpace.rankOne 𝕜 x x) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← tsum_ofReal_normSq_inner b x]
  refine tsum_congr fun i => ?_
  rw [InnerProductSpace.rankOne_apply, inner_smul_left, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.ofReal_re, norm_inner_symm]

omit [CompleteSpace H] in
theorem positiveTrace_add (b : HilbertBasis ι 𝕜 H) {T S : H →L[𝕜] H}
    (hT : T.IsPositive) (hS : S.IsPositive) :
    positiveTrace b (T + S) = positiveTrace b T + positiveTrace b S := by
  unfold positiveTrace
  rw [← tsum_add]
  refine tsum_congr fun i => ?_
  rw [add_apply, inner_add_left]
  change ENNReal.ofReal ((RCLike.reCLM : 𝕜 →L[ℝ] ℝ) (_ + _)) = _
  rw [map_add, RCLike.reCLM_apply,
    ENNReal.ofReal_add (hT.re_inner_nonneg_left (b i)) (hS.re_inner_nonneg_left (b i))]

/-- A Hilbert–Schmidt factor gives an operator-norm convergent sum of positive dyads. -/
theorem hasSum_rankOne_of_hilbertSchmidt (b : HilbertBasis ι 𝕜 H) (A : H →L[𝕜] H)
    (h : hilbertSchmidtMassSq b A ≠ ∞) :
    HasSum (fun i => InnerProductSpace.rankOne 𝕜 (A (b i)) (A (b i)))
      (A ∘L ContinuousLinearMap.adjoint A) := by
  have hsq : Summable (fun i => ‖A (b i)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using (ENNReal.summable_toReal h)
  have hnorm : Summable (fun i => ‖InnerProductSpace.rankOne 𝕜 (A (b i)) (A (b i))‖) := by
    simpa only [InnerProductSpace.norm_rankOne, pow_two] using hsq
  have hsum := hnorm.of_norm.hasSum
  convert hsum using 1
  ext x
  let E : (H →L[𝕜] H) →L[𝕜] H := ContinuousLinearMap.apply 𝕜 H x
  have h₁ := E.hasSum hsum
  have h₂ := A.hasSum (b.hasSum_repr (ContinuousLinearMap.adjoint A x))
  have h₂' : HasSum (fun i => InnerProductSpace.rankOne 𝕜 (A (b i)) (A (b i)) x)
      (A (ContinuousLinearMap.adjoint A x)) := by
    refine h₂.congr_fun fun i => ?_
    rw [b.repr_apply_apply, map_smul, InnerProductSpace.rankOne_apply, A.adjoint_inner_right]
  exact h₂'.unique h₁

end AlbertSequential.HilbertTrace
