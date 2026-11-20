/- SPDX-License-Identifier: Apache-2.0 -/
module
public import HilbertTraceComplexInstrument
public import HilbertTraceRealInstrument
public import HilbertTraceModulus
public import Robustness.RealOperatorSpectralRounding
public import Robustness.SignedTraceMass

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace AlbertSequential.HilbertTrace

section Common
variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
    (b : HilbertBasis ι 𝕜 H)

theorem signedTrace_nonneg_of_positive (T : signedFiniteTrace b) (hT : T.val.IsPositive) :
    0 ≤ signedTrace b T := by
  rw [signedTrace_eq_positiveTrace_toReal b T hT]
  exact ENNReal.toReal_nonneg

/-- Orthogonal positive and negative parts minimize total positive trace mass. -/
theorem signedTrace_orthogonal_parts_minimal
    (sand : (H →L[𝕜] H) → (signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b))
    (hsand : ∀ P T, (sand P T).val = P * T.val * star P)
    (hsplit : ∀ P, IsStarProjection P → ∀ T,
      signedTrace b (sand P T) + signedTrace b (sand (1 - P) T) = signedTrace b T)
    {T U V X Y : signedFiniteTrace b} (hU : U.val.IsPositive) (hV : V.val.IsPositive)
    (hVU : V.val * U.val = 0) (hT : T = U - V)
    (hX : X.val.IsPositive) (hY : Y.val.IsPositive) (hXY : T = X - Y) :
    signedTrace b U + signedTrace b V ≤ signedTrace b X + signedTrace b Y := by
  let K := V.val.ker
  let : CompleteSpace K := V.val.isComplete_ker.completeSpace_coe
  let P := K.starProjection
  let Q := 1 - P
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hQ : IsStarProjection Q := hP.one_sub
  have hPU : P * U.val = U.val := by
    ext z
    apply Submodule.starProjection_eq_self_iff.mpr
    exact congrArg (fun A : H →L[𝕜] H => A z) hVU
  have hUP : U.val * P = U.val := by
    have h := congrArg star hPU
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hU.isSelfAdjoint.star_eq] using h
  have hVP : V.val * P = 0 := by
    ext z
    exact K.starProjection_apply_mem z
  have hPV : P * V.val = 0 := by
    have h := congrArg star hVP
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hV.isSelfAdjoint.star_eq, star_zero] using h
  have hQU : Q * U.val = 0 := by
    change (1 - P) * U.val = 0
    rw [sub_mul, one_mul, hPU, sub_self]
  have hQV : Q * V.val = V.val := by
    change (1 - P) * V.val = V.val
    rw [sub_mul, one_mul, hPV, sub_zero]
  have hVQ : V.val * Q = V.val := by
    change V.val * (1 - P) = V.val
    rw [mul_sub, mul_one, hVP, sub_zero]
  have hcompressP : sand P T = U := by
    apply Subtype.ext
    rw [hsand, hP.isSelfAdjoint.star_eq, hT]
    change P * (U.val - V.val) * P = U.val
    rw [mul_sub, hPU, hPV, sub_zero, hUP]
  have hcompressQ : sand Q T = -V := by
    apply Subtype.ext
    rw [hsand, hQ.isSelfAdjoint.star_eq, hT]
    change Q * (U.val - V.val) * Q = -V.val
    rw [mul_sub Q U.val V.val, hQU, hQV, zero_sub, neg_mul, hVQ]
  have hn (D : H →L[𝕜] H) (Z : signedFiniteTrace b) (hZ : Z.val.IsPositive) :
      0 ≤ signedTrace b (sand D Z) := by
    apply signedTrace_nonneg_of_positive b
    rw [hsand]
    exact hZ.conj_adjoint D
  have htraceP := congrArg (signedTrace b) hcompressP
  have htraceQ := congrArg (signedTrace b) hcompressQ
  rw [hXY, map_sub, map_sub] at htraceP htraceQ
  rw [map_neg] at htraceQ
  linarith [hsplit P hP X, hsplit P hP Y, hn Q X hX, hn P Y hY]

end Common

section Complex
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H)

theorem complex_projection_trace_split {P : H →L[ℂ] H} (hP : IsStarProjection P)
    (X : signedFiniteTrace b) :
    signedTrace b (complexSandwich b P X) + signedTrace b (complexSandwich b (1 - P) X) =
      signedTrace b X := by
  rw [signedTrace_complexSandwich, signedTrace_complexSandwich, hP.isSelfAdjoint.star_eq,
    hP.isIdempotentElem, hP.one_sub.isSelfAdjoint.star_eq, hP.one_sub.isIdempotentElem,
    complexTracePairing_complement_eq b]
  ring

theorem complex_signedTrace_orthogonal_decomposition (X : signedFiniteTrace b) :
    ∃ U V : signedFiniteTrace b, U.val.IsPositive ∧ V.val.IsPositive ∧
      V.val * U.val = 0 ∧ X = U - V ∧
      signedTrace b U + signedTrace b V = (positiveTrace b (CFC.abs X.val)).toReal := by
  let U := X.val⁺
  let V := X.val⁻
  have hX := signedFiniteTrace_isSelfAdjoint b X
  have hU : U.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.posPart_nonneg X.val)
  have hV : V.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.negPart_nonneg X.val)
  have hAbs : U + V = CFC.abs X.val := CFC.posPart_add_negPart X.val hX
  have hfin := (complex_mem_signedFiniteTrace_iff_modulus b X.val hX).mp X.property
  rw [← hAbs, positiveTrace_add b hU hV, ENNReal.add_ne_top] at hfin
  let u : signedFiniteTrace b := ⟨U, IsPositiveFiniteTrace.mem_signedFiniteTrace b ⟨hU, hfin.1⟩⟩
  let v : signedFiniteTrace b := ⟨V, IsPositiveFiniteTrace.mem_signedFiniteTrace b ⟨hV, hfin.2⟩⟩
  refine ⟨u, v, hU, hV, CFC.negPart_mul_posPart X.val, Subtype.ext (CFC.posPart_sub_negPart X.val hX).symm, ?_⟩
  rw [signedTrace_eq_positiveTrace_toReal b u hU, signedTrace_eq_positiveTrace_toReal b v hV,
    ← hAbs, positiveTrace_add b hU hV, ENNReal.toReal_add hfin.1 hfin.2]

def complexSignedTraceMass : SignedTraceMassData (signedFiniteTrace b) where
  positive := {X | X.val.IsPositive}
  trace := signedTrace b
  zero_positive := ContinuousLinearMap.isPositive_zero
  add_positive := fun _ hx _ hy => hx.add hy
  smul_positive r hr X hX := by
    change (r • X.val).IsPositive
    rw [← algebraMap_smul ℂ r X.val]
    exact hX.smul_of_nonneg (RCLike.ofReal_nonneg.mpr hr)
  positive_trace := fun X hX hx =>
    (complex_signedTrace_pos_iff b hX).mpr (fun h => hx (Subtype.ext h))
  exists_minimum := by
    intro X
    obtain ⟨U, V, hU, hV, hVU, hX, _⟩ := complex_signedTrace_orthogonal_decomposition b X
    exact ⟨U, V, hU, hV, hX, fun p hp n hn hx =>
      signedTrace_orthogonal_parts_minimal b (complexSandwich b) (fun _ _ => rfl)
        (fun _ hP => complex_projection_trace_split b hP) hU hV hVU hX hp hn hx⟩

theorem complex_traceNorm_eq_trace_modulus (X : (complexSignedTraceMass b).WithNorm) :
    ‖X‖ = (positiveTrace b (CFC.abs (show signedFiniteTrace b from X).val)).toReal := by
  change (complexSignedTraceMass b).mass X = _
  obtain ⟨U, V, hU, hV, hVU, hX, hmass⟩ := complex_signedTrace_orthogonal_decomposition b X
  rw [← hmass]
  apply le_antisymm ((complexSignedTraceMass b).mass_le hU hV hX)
  obtain ⟨p, n, hp, hn, hx, hm⟩ := (complexSignedTraceMass b).minimum X
  rw [hm]
  exact signedTrace_orthogonal_parts_minimal b (complexSandwich b) (fun _ _ => rfl)
    (fun _ hP => complex_projection_trace_split b hP) hU hV hVU hX hp hn hx

end Complex

section Real
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H)

theorem real_projection_trace_split {P : H →L[ℝ] H} (hP : IsStarProjection P)
    (X : signedFiniteTrace b) :
    signedTrace b (realSandwich b P X) + signedTrace b (realSandwich b (1 - P) X) =
      signedTrace b X := by
  rw [signedTrace_realSandwich, signedTrace_realSandwich, hP.isSelfAdjoint.star_eq,
    hP.isIdempotentElem, hP.one_sub.isSelfAdjoint.star_eq, hP.one_sub.isIdempotentElem,
    realTracePairing_complement_eq b]
  ring

theorem real_signedTrace_orthogonal_decomposition (X : signedFiniteTrace b)
    (D : H →L[ℝ] H) (hD : D.IsPositive) (hDsq : D * D = X.val * X.val) :
    ∃ U V : signedFiniteTrace b, U.val.IsPositive ∧ V.val.IsPositive ∧
      V.val * U.val = 0 ∧ X = U - V ∧ D = U.val + V.val ∧
      signedTrace b U + signedTrace b V = (positiveTrace b D).toReal := by
  have hX := signedFiniteTrace_isSelfAdjoint b X
  obtain ⟨U, V, hU, hV, _, hVU, hsub, hadd⟩ := real_operator_parts X.val D hX hD hDsq
  have hfin := (real_mem_signedFiniteTrace_iff_modulus b X.val D hX hD hDsq).mp X.property
  rw [hadd, positiveTrace_add b hU hV, ENNReal.add_ne_top] at hfin
  let u : signedFiniteTrace b := ⟨U, IsPositiveFiniteTrace.mem_signedFiniteTrace b ⟨hU, hfin.1⟩⟩
  let v : signedFiniteTrace b := ⟨V, IsPositiveFiniteTrace.mem_signedFiniteTrace b ⟨hV, hfin.2⟩⟩
  refine ⟨u, v, hU, hV, hVU, Subtype.ext hsub, hadd, ?_⟩
  rw [signedTrace_eq_positiveTrace_toReal b u hU, signedTrace_eq_positiveTrace_toReal b v hV,
    hadd, positiveTrace_add b hU hV, ENNReal.toReal_add hfin.1 hfin.2]

def realSignedTraceMass : SignedTraceMassData (signedFiniteTrace b) where
  positive := {X | X.val.IsPositive}
  trace := signedTrace b
  zero_positive := ContinuousLinearMap.isPositive_zero
  add_positive := fun _ hx _ hy => hx.add hy
  smul_positive := fun _ hr _ hX => hX.smul_of_nonneg hr
  positive_trace := fun X hX hx =>
    (real_signedTrace_pos_iff b hX).mpr (fun h => hx (Subtype.ext h))
  exists_minimum := by
    intro X
    have hs := signedFiniteTrace_isSelfAdjoint b X
    have hP : (X.val * X.val).IsPositive := by
      have h := ContinuousLinearMap.isPositive_adjoint_comp_self X.val
      change (star X.val * X.val).IsPositive at h
      rwa [hs.star_eq] at h
    obtain ⟨U, V, hU, hV, hVU, hX, _, _⟩ := real_signedTrace_orthogonal_decomposition b X
      (realPositiveSquareRoot _ hP) (realPositiveSquareRoot_positive_and_square _ hP).1
      (realPositiveSquareRoot_positive_and_square _ hP).2
    exact ⟨U, V, hU, hV, hX, fun p hp n hn hx =>
      signedTrace_orthogonal_parts_minimal b (realSandwich b) (fun _ _ => rfl)
        (fun _ hP => real_projection_trace_split b hP) hU hV hVU hX hp hn hx⟩

theorem real_traceNorm_eq_trace_modulus (X : (realSignedTraceMass b).WithNorm)
    (D : H →L[ℝ] H) (hD : D.IsPositive)
    (hDsq : D * D = (show signedFiniteTrace b from X).val * (show signedFiniteTrace b from X).val) :
    ‖X‖ = (positiveTrace b D).toReal := by
  change (realSignedTraceMass b).mass X = _
  obtain ⟨U, V, hU, hV, hVU, hX, _, hmass⟩ := real_signedTrace_orthogonal_decomposition b X D hD hDsq
  rw [← hmass]
  apply le_antisymm ((realSignedTraceMass b).mass_le hU hV hX)
  obtain ⟨p, n, hp, hn, hx, hm⟩ := (realSignedTraceMass b).minimum X
  rw [hm]
  exact signedTrace_orthogonal_parts_minimal b (realSandwich b) (fun _ _ => rfl)
    (fun _ hP => real_projection_trace_split b hP) hU hV hVU hX hp hn hx

end Real
end AlbertSequential.HilbertTrace
