/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PartnerVarianceGram
public import ScheduleMatchingSectors

@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven

open scoped BigOperators
open AlbertSequential.MatchingModels
open AlbertSequential.PartnerVariance

private def mTraces (ω : Letter → ℝ) : TraceData where
  o _ _ := 1 / 3
  R _ _ _ := 1 / 9
  om := ω
  o_symm _ _ := rfl
  R_symm12 _ _ _ := rfl
  R_symm23 _ _ _ := rfl

private def omegaM : Letter → ℝ := ![0,1/27,1/27,1/27]
private def omegaPlus : Letter → ℝ := ![0,1/27,0,2/27]
private def omegaMinus : Letter → ℝ := ![0,1/27,2/27,0]

private theorem omega_midpoint : (fun i : Letter => (1 / 2 : ℝ) * omegaPlus i +
    (1 - 1 / 2) * omegaMinus i) = omegaM := by
  funext i
  fin_cases i <;> norm_num [omegaM, omegaPlus, omegaMinus]

set_option maxHeartbeats 1000000 in
private theorem affine_partners_equal : printedPhiAffine (mTraces omegaPlus) =
    printedPhiAffine (mTraces omegaMinus) := by
  norm_num [printedPhiAffine, printedSignedGram, printedCCAffine, printedSignedRow, rowTrace,
    mTraces, printedTraces, printedOrder, omegaPlus, omegaMinus, printedSign,
    printedGramTable, ccAffine, Fin.sum_univ_succ]

private theorem affine_M_partner : printedPhiAffine (mTraces omegaPlus) =
      printedPhiAffine (mTraces omegaM) ∧
    printedPhiAffine (mTraces omegaMinus) = printedPhiAffine (mTraces omegaM) := by
  have h := printedPhiAffine_omegas (mTraces omegaM) omegaPlus omegaMinus (1 / 2)
  change printedPhiAffine (mTraces (fun i => (1 / 2 : ℝ) * omegaPlus i + (1 - 1 / 2) * omegaMinus i)) = _ at h
  rw [omega_midpoint] at h
  change printedPhiAffine (mTraces omegaM) = (1 / 2 : ℝ) * printedPhiAffine (mTraces omegaPlus) +
    (1 - 1 / 2) * printedPhiAffine (mTraces omegaMinus) at h
  rw [← affine_partners_equal] at h
  have he : printedPhiAffine (mTraces omegaPlus) = printedPhiAffine (mTraces omegaM) := by linarith
  exact ⟨he, affine_partners_equal.symm.trans he⟩

private theorem printedPhiValue_M_raw : printedPhiValue (mTraces omegaM) = -4 / 27 := by
  norm_num [printedPhiValue, printedSignedGram, printedSignedRow, rowTrace, mTraces,
    printedTraces, printedOrder, omegaM, printedSign, printedGramTable, Fin.sum_univ_succ]

private theorem printedPhiValue_partners_raw :
    printedPhiValue (mTraces omegaPlus) = 788 / 729 ∧
    printedPhiValue (mTraces omegaMinus) = 788 / 729 := by
  obtain ⟨qM, qPlus, qMinus, result⟩ := printed_partner_variance
  have h (ω : Letter → ℝ) :
      printedPhiValue (mTraces ω) = printedPhiAffine (mTraces ω) -
        56 * quadraticCC (ω 1) (ω 2) (ω 3) := by
    rw [quadraticCC_eq]
    exact printedPhi_variance_decomposition (mTraces ω)
  have hM := h omegaM
  change printedPhiValue (mTraces omegaM) = printedPhiAffine (mTraces omegaM) -
    56 * quadraticCC (1/27) (1/27) (1/27) at hM
  rw [printedPhiValue_M_raw, qM] at hM
  constructor
  · rw [h, affine_M_partner.1]
    change printedPhiAffine (mTraces omegaM) - 56 * quadraticCC (1/27) 0 (2/27) = _
    rw [qPlus]
    linarith only [hM, result]
  · rw [h, affine_M_partner.2]
    change printedPhiAffine (mTraces omegaM) - 56 * quadraticCC (1/27) (2/27) 0 = _
    rw [qMinus]
    linarith only [hM, result]

private theorem phiValue_agrees_on_used_traces (τ : TraceData)
    (ho : ∀ i j, i ≠ j → τ.o i j = 1 / 3)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → τ.R i j k = 1 / 9)
    (ω : Letter → ℝ) (hw : τ.om = ω) : printedPhiValue τ = printedPhiValue (mTraces ω) := by
  have he (s : Fin 6) : rowTrace τ s = rowTrace (mTraces ω) s := by
    let t := printedOrder 1 2 3 s
    have h : IsOrderingBCD t.1 t.2.1 t.2.2 := by
      fin_cases s <;> decide
    rcases h with ⟨hx,hy,hz,hxy,hyz,hxz⟩
    change printedTraces τ t.1 t.2.1 t.2.2 = printedTraces (mTraces ω) t.1 t.2.1 t.2.2
    simp [printedTraces, mTraces, hw, ho 0 t.1 hx.symm, ho 0 t.2.1 hy.symm, ho 0 t.2.2 hz.symm,
      ho t.1 t.2.1 hxy, ho t.1 t.2.2 hxz, ho t.2.1 t.2.2 hyz,
      hr 0 t.1 t.2.1 hx.symm hy.symm hxy, hr 0 t.1 t.2.2 hx.symm hz.symm hxz,
      hr 0 t.2.1 t.2.2 hy.symm hz.symm hyz, hr t.1 t.2.1 t.2.2 hxy hxz hyz]
  simp only [printedPhiValue, printedSignedGram, he]

theorem printedPhiValue_maximizer : printedPhiValue (nativeTraceData maximizerConfig) = -4 / 27 := by
  obtain ⟨ho,hr,_,_,_,w₁,w₂,w₃,_⟩ := maximizerConfig_traces 1
  have hω : (nativeTraceData maximizerConfig).om = omegaM := by
    funext i
    fin_cases i <;> simp [nativeTraceData, omegaM, w₁, w₂, w₃]
  exact (phiValue_agrees_on_used_traces _ ho hr omegaM hω).trans printedPhiValue_M_raw

private theorem overlaps_all (τ : TraceData) (a : ℝ)
    (h01 : τ.o 0 1 = a) (h02 : τ.o 0 2 = a) (h03 : τ.o 0 3 = a)
    (h12 : τ.o 1 2 = a) (h13 : τ.o 1 3 = a) (h23 : τ.o 2 3 = a) :
    ∀ i j, i ≠ j → τ.o i j = a := by
  have hs : ∀ i j, i < j → τ.o i j = a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Fin.lt_def] at hij
    all_goals assumption
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hs i j h
  · exact (τ.o_symm i j).trans (hs j i h)

private theorem triangles_all (τ : TraceData) (a : ℝ)
    (h012 : τ.R 0 1 2 = a) (h013 : τ.R 0 1 3 = a)
    (h023 : τ.R 0 2 3 = a) (h123 : τ.R 1 2 3 = a) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k → τ.R i j k = a := by
  have hs (i j k : Letter) (hij : i < j) (hjk : j < k) : τ.R i j k = a := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [Fin.lt_def] at hij hjk
    all_goals assumption
  have hleft (i j k : Letter) (hij : i < j) (hik : i ≠ k) (hjk : j ≠ k) : τ.R i j k = a := by
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · exact hs i j k hij hjk
    rcases lt_or_gt_of_ne hik with hik | hki
    · exact (τ.R_symm23 i j k).trans (hs i k j hik hkj)
    · exact (τ.R_symm23 i j k).trans ((τ.R_symm12 i k j).trans (hs k i j hki hij))
  intro i j k hij hik hjk
  rcases lt_or_gt_of_ne hij with h | h
  · exact hleft i j k h hik hjk
  · exact (τ.R_symm12 i j k).trans (hleft j i k h hjk hik)

theorem printedPhiValue_M_partner (s : Bool) :
    printedPhiValue (nativeTraceData (horizonMSector s)) = 788 / 729 := by
  let d : ℝ := if s then (Real.sqrt 2)⁻¹ else -(Real.sqrt 2)⁻¹
  let p := horizonMSector s
  have hds : d ^ 2 = 1 / 2 := by cases s <;> simp [d]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨h01,h02,h03,h12,h13,h23,r012,r013,r023,r123,t₁,t₂,t₃⟩ :=
    horizonQuaternionicSector_traces (Real.sqrt 2) d hds
  have ho : ∀ i j, i ≠ j → (nativeTraceData p).o i j = 1 / 3 :=
    overlaps_all _ _ (by norm_num [hsqrt] at h01 ⊢; exact h01) h02 h03 h12 h13 h23
  have hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → (nativeTraceData p).R i j k = 1 / 9 :=
    triangles_all _ _ (by norm_num [hsqrt] at r012 ⊢; exact r012)
      (by norm_num [hsqrt] at r013 ⊢; exact r013) r023 r123
  have hω : (nativeTraceData p).om = if s then omegaPlus else omegaMinus := by
    have hn : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    change fpDoublePair1 p = _ at t₁
    change fpDoublePair2 p = _ at t₂
    change fpDoublePair3 p = _ at t₃
    funext i
    cases s <;> fin_cases i <;> norm_num [nativeTraceData, fpOmega1, fpOmega2, fpOmega3,
      omegaPlus, omegaMinus, t₁, t₂, t₃, hsqrt, d, mul_neg, mul_inv_cancel₀ hn]
  rw [phiValue_agrees_on_used_traces _ ho hr _ hω]
  cases s
  · exact printedPhiValue_partners_raw.2
  · exact printedPhiValue_partners_raw.1

end AlbertSequential.LengthSeven
