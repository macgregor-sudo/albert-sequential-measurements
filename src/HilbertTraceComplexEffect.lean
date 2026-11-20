/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertTraceDensity
public import HilbertTraceRiesz

/-! Complex-linear recovery of the measured effect on the native trace-class carrier. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace AlbertSequential.HilbertTrace

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis ι ℂ H)

def complexVectorDyad (x : H) : signedFiniteTrace b :=
  ⟨InnerProductSpace.rankOne ℂ x x, rankOne_mem_signedFiniteTrace b x⟩

private def symmetricComplexDyad (x y : H) : signedFiniteTrace b :=
  ⟨(1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ y x), by
    have h : InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ y x =
        (complexVectorDyad b (x + y)).val - (complexVectorDyad b x).val - (complexVectorDyad b y).val := by
      change _ = InnerProductSpace.rankOne ℂ (x + y) (x + y) -
        InnerProductSpace.rankOne ℂ x x - InnerProductSpace.rankOne ℂ y y
      simp only [map_add, add_apply]
      abel
    rw [h]
    exact (signedFiniteTrace b).smul_mem _ ((signedFiniteTrace b).sub_mem
      ((signedFiniteTrace b).sub_mem (complexVectorDyad b (x + y)).property
        (complexVectorDyad b x).property) (complexVectorDyad b y).property)⟩

private theorem symmetricComplexDyad_comm (x y : H) :
    symmetricComplexDyad b x y = symmetricComplexDyad b y x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ y x) = _
  rw [add_comm]
  rfl

private theorem symmetricComplexDyad_self (x : H) :
    symmetricComplexDyad b x x = complexVectorDyad b x := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ x x + InnerProductSpace.rankOne ℂ x x) = _
  rw [← two_smul ℝ, smul_smul]
  norm_num [complexVectorDyad]

private theorem symmetricComplexDyad_add_left (x y z : H) :
    symmetricComplexDyad b (x + y) z = symmetricComplexDyad b x z + symmetricComplexDyad b y z := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ (x + y) z + InnerProductSpace.rankOne ℂ z (x + y)) =
    (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ x z + InnerProductSpace.rankOne ℂ z x) +
      (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ y z + InnerProductSpace.rankOne ℂ z y)
  simp only [map_add, add_apply, smul_add]
  abel

private theorem symmetricComplexDyad_smul_left (r : ℝ) (x y : H) :
    symmetricComplexDyad b (r • x) y = r • symmetricComplexDyad b x y := by
  have hl : InnerProductSpace.rankOne ℂ (r • x) y = r • InnerProductSpace.rankOne ℂ x y := by
    ext z
    change ⟪y, z⟫_ℂ • (r • x) = r • (⟪y, z⟫_ℂ • x)
    exact smul_comm _ _ _
  have hr : InnerProductSpace.rankOne ℂ y (r • x) = r • InnerProductSpace.rankOne ℂ y x := by
    ext z
    change ⟪(r : ℂ) • x, z⟫_ℂ • y = r • (⟪x, z⟫_ℂ • y)
    rw [inner_smul_left]
    change ((star (r : ℂ)) * ⟪x, z⟫_ℂ) • y = _
    have hs : star (r : ℂ) = (r : ℂ) := by simp
    rw [hs, mul_smul]
    rfl
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ (r • x) y + InnerProductSpace.rankOne ℂ y (r • x)) =
    r • ((1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ y x))
  rw [hl, hr, ← smul_add, smul_comm]

omit [CompleteSpace H] in
private theorem rankOne_imaginary_phase (x y : H) :
    InnerProductSpace.rankOne ℂ (Complex.I • x) (Complex.I • y) = InnerProductSpace.rankOne ℂ x y := by
  ext z
  rw [InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul]
  have h (w : ℂ) : (star Complex.I * w) * Complex.I = w := by
    calc
      _ = (star Complex.I * Complex.I) * w := by ring
      _ = w := by simp [Complex.conj_I, Complex.I_mul_I]
  exact congrArg (fun w : ℂ => w • x) (h _)

private theorem symmetricComplexDyad_phase (x y : H) :
    symmetricComplexDyad b (Complex.I • x) (Complex.I • y) = symmetricComplexDyad b x y := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (InnerProductSpace.rankOne ℂ (Complex.I • x) (Complex.I • y) +
    InnerProductSpace.rankOne ℂ (Complex.I • y) (Complex.I • x)) = _
  rw [rankOne_imaginary_phase, rankOne_imaginary_phase]
  rfl

private def complexBranchBilinear (f : signedFiniteTrace b →ₗ[ℝ] ℝ) : H →ₗ[ℝ] H →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => f (symmetricComplexDyad b x y))
    (fun x y z => by rw [symmetricComplexDyad_add_left, map_add])
    (fun r x y => by rw [symmetricComplexDyad_smul_left, map_smul])
    (fun x y z => by rw [symmetricComplexDyad_comm b x (y + z), symmetricComplexDyad_add_left,
      map_add, symmetricComplexDyad_comm b y x, symmetricComplexDyad_comm b z x])
    (fun r x y => by rw [symmetricComplexDyad_comm b x (r • y), symmetricComplexDyad_smul_left,
      map_smul, symmetricComplexDyad_comm b y x])

theorem complexTracePairing_complement_eq (A : H →L[ℂ] H) (T : signedFiniteTrace b) :
    signedTracePairing b (1 - A) T = signedTrace b T - signedTracePairing b A T := by
  unfold signedTracePairing
  change (∑' i, RCLike.re ⟪(1 - A) (T.val (b i)), b i⟫_ℂ) =
    (∑' i, RCLike.re ⟪T.val (b i), b i⟫_ℂ) - ∑' i, RCLike.re ⟪A (T.val (b i)), b i⟫_ℂ
  rw [← (summable_signedFiniteTrace_diagonal b T).tsum_sub (complex_summable_tracePairing b A T).of_norm]
  refine tsum_congr fun i => ?_
  rw [sub_apply, one_apply_eq_self, inner_sub_left]
  exact map_sub (RCLike.reCLM : ℂ →L[ℝ] ℝ) _ _

attribute [local instance] InnerProductSpace.complexToReal

omit [CompleteSpace H] in
private theorem complex_inner_real_imaginary_phase (x y : H) :
    ⟪Complex.I • x, Complex.I • y⟫_ℝ = ⟪x, y⟫_ℝ := by
  change (inner ℂ (Complex.I • x) (Complex.I • y)).re = (inner ℂ x y).re
  rw [inner_smul_left, inner_smul_right]
  congr 1
  change star Complex.I * (Complex.I * inner ℂ x y) = inner ℂ x y
  rw [← mul_assoc]
  simp [Complex.conj_I, Complex.I_mul_I]

private def complexOperatorOfCommuteI (A : H →L[ℝ] H)
    (hA : ∀ x, A (Complex.I • x) = Complex.I • A x) : H →L[ℂ] H where
  toFun := A
  map_add' := map_add A
  map_smul' z x := by
    change A (z • x) = z • A x
    conv_lhs => rw [← Complex.re_add_im z, add_smul, mul_smul]
    conv_rhs => rw [← Complex.re_add_im z, add_smul, mul_smul]
    change A (z.re • x + z.im • (Complex.I • x)) = z.re • A x + z.im • (Complex.I • A x)
    rw [map_add, map_smul, map_smul, hA]
  cont := A.continuous

private theorem complex_positive_of_real_restriction {A : H →L[ℝ] H} {L : H →L[ℂ] H}
    (hA : A.IsPositive) (hL : ∀ x, L x = A x) : L.IsPositive := by
  have hre (x y : H) : (inner ℂ (L x) y).re = (inner ℂ x (L y)).re := by
    rw [hL, hL]
    change ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ
    exact hA.isSelfAdjoint.isSymmetric x y
  have hLself : IsSelfAdjoint L := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (by
    intro x y
    change inner ℂ (L x) y = inner ℂ x (L y)
    apply Complex.ext (hre x y)
    have hi := hre x (Complex.I • y)
    rw [map_smul, inner_smul_right, inner_smul_right] at hi
    simpa [Complex.mul_re] using hi)
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨hLself, fun x => ?_⟩
  change 0 ≤ (inner ℂ (L x) x).re
  rw [hL]
  change 0 ≤ ⟪A x, x⟫_ℝ
  exact hA.re_inner_nonneg_left x

/-- The measured effect recovered by real Riesz is genuinely complex-linear and pairs with every
self-adjoint trace-class operator. -/
theorem exists_complex_effect_of_trace_dominated (f : signedFiniteTrace b →ₗ[ℝ] ℝ)
    (hf : ∀ T : signedFiniteTrace b, T.val.IsPositive → 0 ≤ f T ∧ f T ≤ signedTrace b T) :
    ∃ A : H →L[ℂ] H, A.IsPositive ∧ (1 - A).IsPositive ∧
      ∀ T : signedFiniteTrace b, f T = signedTracePairing b A T := by
  let B := complexBranchBilinear b f
  have hB (x y : H) : B x y = B y x := by
    change f (symmetricComplexDyad b x y) = f (symmetricComplexDyad b y x)
    rw [symmetricComplexDyad_comm]
  have hD (x : H) : B x x = f (complexVectorDyad b x) := by
    change f (symmetricComplexDyad b x x) = _
    rw [symmetricComplexDyad_self]
  have hmin (x : H) : 0 ≤ B x x := by
    rw [hD]
    exact (hf (complexVectorDyad b x) (InnerProductSpace.isPositive_rankOne_self x)).1
  have hmax (x : H) : B x x ≤ ‖x‖ ^ 2 := by
    have h := (hf (complexVectorDyad b x) (InnerProductSpace.isPositive_rankOne_self x)).2
    have ht : signedTrace b (complexVectorDyad b x) = ‖x‖ ^ 2 := by
      change signedTracePairing b 1 ⟨InnerProductSpace.rankOne ℂ x x, rankOne_mem_signedFiniteTrace b x⟩ = _
      rw [signedTracePairing_rankOne, one_apply_eq_self, inner_self_eq_norm_sq]
    rwa [hD, ← ht]
  obtain ⟨A, hA, hAc, hq⟩ := exists_positiveContraction_of_diagonal_bilinear B hB hmin hmax
  have hI (x : H) : A (Complex.I • x) = Complex.I • A x := by
    apply ext_inner_right ℝ
    intro z
    have hz : ∃ y : H, Complex.I • y = z := by
      refine ⟨(-Complex.I) • z, ?_⟩
      rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    obtain ⟨y, rfl⟩ := hz
    rw [hq, complex_inner_real_imaginary_phase, hq]
    change f (symmetricComplexDyad b (Complex.I • x) (Complex.I • y)) = f (symmetricComplexDyad b x y)
    rw [symmetricComplexDyad_phase]
  let L := complexOperatorOfCommuteI A hI
  have hLc : (1 - L).IsPositive := complex_positive_of_real_restriction hAc (fun x => rfl)
  have hL : L.IsPositive := complex_positive_of_real_restriction hA (fun x => rfl)
  let g := signedTracePairingLinear b L (fun T => (complex_summable_tracePairing b L T).of_norm)
  have hg (T : signedFiniteTrace b) (hT : T.val.IsPositive) :
      0 ≤ g T ∧ g T ≤ signedTrace b T := by
    change 0 ≤ signedTracePairing b L T ∧ signedTracePairing b L T ≤ signedTrace b T
    refine ⟨(complex_signedTracePairing_nonneg_zero_iff b L T hL hT).1, ?_⟩
    have h := (complex_signedTracePairing_nonneg_zero_iff b (1 - L) T hLc hT).1
    rw [complexTracePairing_complement_eq] at h
    exact sub_nonneg.mp h
  have hvec (x : H) : f (complexVectorDyad b x) = g (complexVectorDyad b x) := by
    change f (complexVectorDyad b x) = signedTracePairing b L
      ⟨InnerProductSpace.rankOne ℂ x x, rankOne_mem_signedFiniteTrace b x⟩
    rw [signedTracePairing_rankOne]
    change f (complexVectorDyad b x) = ⟪A x, x⟫_ℝ
    rw [hq, hD]
  have hfg : f = g := positiveFunctional_ext_of_rankOne b (fun h => by
    obtain ⟨S, _, _, hS⟩ := exists_selfAdjoint_factor h
    exact ⟨S, hS⟩) f g hf hg hvec
  exact ⟨L, hL, hLc, fun T => LinearMap.congr_fun hfg T⟩

end AlbertSequential.HilbertTrace
