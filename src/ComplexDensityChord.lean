/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QuaternionicDensityLift
import Mathlib.Analysis.Matrix.Order
import WindowProbabilityGaussianRank

public section
noncomputable section

namespace AlbertSequential.WindowProbability

open scoped Matrix MatrixOrder ComplexOrder

private theorem rank_le_two_of_det_zero (M : ComplexMatrix3) (hM : M.det = 0) : M.rank ≤ 2 := by
  have hle := M.rank_le_width
  have hne : M.rank ≠ 3 := by
    intro he
    refine (complexMatrix_rank_eq_card_iff_det_ne_zero M).mp ?_ hM
    simpa using he
  omega

/-- In every nonzero traceless Hermitian direction at a positive-definite
density there are two singular densities. The positive cone cuts out exactly
the closed interval between the two parameters. -/
theorem complexDensity_rankTwo_chord (σ H : ComplexMatrix3) (hσ : σ.PosDef)
    (htrace : σ.trace = 1) (hH : H.IsHermitian) (hzero : H ≠ 0) (htrH : H.trace = 0) :
    ∃ sMin sMax : ℝ, sMin < 0 ∧ 0 < sMax ∧
      (∀ s : ℝ, (σ + s • H).PosSemidef ↔ sMin ≤ s ∧ s ≤ sMax) ∧
      (σ + sMin • H).rank ≤ 2 ∧ (σ + sMax • H).rank ≤ 2 ∧
      (σ + sMin • H).trace = 1 ∧ (σ + sMax • H).trace = 1 ∧
      ∃ weight : ℝ, 0 < weight ∧ weight < 1 ∧ σ = weight • (σ + sMax • H) + (1 - weight) • (σ + sMin • H) := by
  let R := CFC.sqrt σ
  have hRs : star R = R := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).isHermitian.eq
  have hRR : R * R = σ := by rw [← sq]; exact CFC.sq_sqrt σ
  have hRdet : IsUnit R.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have h := congrArg Matrix.det hRR
    rw [Matrix.det_mul, hz, zero_mul] at h
    exact (Matrix.isUnit_iff_isUnit_det σ |>.mp hσ.isUnit).ne_zero h.symm
  have hRu : IsUnit R := (Matrix.isUnit_iff_isUnit_det R).mpr hRdet
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRdet
  have hiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRdet
  let B := R⁻¹ * H * R⁻¹
  have hB : B.IsHermitian := by
    change star (R⁻¹ * H * R⁻¹) = R⁻¹ * H * R⁻¹
    have hs : star R⁻¹ = R⁻¹ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        ← Matrix.star_eq_conjTranspose, hRs]
    rw [star_mul, star_mul, hs, show star H = H from hH.eq, ← Matrix.mul_assoc]
  have hconj : R * B * star R = H := by
    rw [hRs]
    change R * (R⁻¹ * H * R⁻¹) * R = H
    calc
      _ = (R * R⁻¹) * H * (R⁻¹ * R) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hRi, hiR, one_mul, mul_one]
  have hline (s : ℝ) : σ + s • H = R * (1 + s • B) * star R := by
    rw [Matrix.mul_add, Matrix.add_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul, hconj,
      show R * star R = σ by rw [hRs, hRR]]
  have hneg : ¬ B.PosSemidef := by
    intro h
    have hp : H.PosSemidef := hconj ▸ (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hRu).mpr h
    exact hzero (hp.trace_eq_zero_iff.mp htrH)
  have hpos : ¬ (-B).PosSemidef := by
    intro h
    have hh : (R * (-B) * star R).PosSemidef := (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hRu).mpr h
    rw [Matrix.mul_neg, Matrix.neg_mul, hconj] at hh
    exact hzero (neg_eq_zero.mp (hh.trace_eq_zero_iff.mp (by simp [htrH])))
  let U : Matrix (Fin 3) (Fin 3) ℂ := hB.eigenvectorUnitary.val
  have hU : IsUnit U := Unitary.isUnit_coe
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  let μ : Fin 3 → ℝ := hB.eigenvalues
  have hspec : B = U * Matrix.diagonal (fun i => (μ i : ℂ)) * star U := hB.spectral_theorem
  have hfeature (s : ℝ) : 1 + s • B =
        U * Matrix.diagonal (fun i => ((1 + s * μ i : ℝ) : ℂ)) * star U := by
    have hd : Matrix.diagonal (fun i => ((1 + s * μ i : ℝ) : ℂ)) =
        1 + s • Matrix.diagonal (fun i => (μ i : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [hij, Complex.real_smul]
    rw [hd, Matrix.mul_add, Matrix.add_mul, mul_one, hUU, Matrix.mul_smul, Matrix.smul_mul, ← hspec]
  have hcrit (s : ℝ) : (σ + s • H).PosSemidef ↔ ∀ i : Fin 3, 0 ≤ 1 + s * μ i := by
    rw [hline, Matrix.IsUnit.posSemidef_star_right_conjugate_iff hRu, hfeature,
      Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU,
      Matrix.posSemidef_diagonal_iff]
    exact ⟨fun h i => Complex.zero_le_real.mp (h i), fun h i => Complex.zero_le_real.mpr (h i)⟩
  have heNeg : ∃ i : Fin 3, μ i < 0 := by
    by_contra! h
    exact hneg (hB.posSemidef_iff_eigenvalues_nonneg.mpr h)
  have hePos : ∃ i : Fin 3, 0 < μ i := by
    by_contra! h
    apply hpos
    have he : -B = U * Matrix.diagonal (fun i => (-(μ i) : ℂ)) * star U := by
      rw [hspec, ← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [he, Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU, Matrix.posSemidef_diagonal_iff]
    intro i
    simpa only [Complex.ofReal_neg] using Complex.zero_le_real.mpr (neg_nonneg.mpr (h i))
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ μ (by simp)
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ μ (by simp)
  have him : μ i < 0 := by obtain ⟨k,hk⟩ := heNeg; exact (hi k (Finset.mem_univ _)).trans_lt hk
  have hjp : 0 < μ j := by obtain ⟨k,hk⟩ := hePos; exact hk.trans_le (hj k (Finset.mem_univ _))
  let sMin : ℝ := (-1) / μ j
  let sMax : ℝ := (-1) / μ i
  have hMin : sMin < 0 := div_neg_of_neg_of_pos (by norm_num) hjp
  have hMax : 0 < sMax := div_pos_of_neg_of_neg (by norm_num) him
  have hzMin : sMin * μ j = -1 := div_mul_cancel₀ _ hjp.ne'
  have hzMax : sMax * μ i = -1 := div_mul_cancel₀ _ him.ne
  have hinterval (s : ℝ) : (σ + s • H).PosSemidef ↔ sMin ≤ s ∧ s ≤ sMax := by
    rw [hcrit]
    constructor
    · intro h
      exact ⟨le_of_mul_le_mul_right (by linarith [h j]) hjp,
        (mul_le_mul_right_of_neg him).mp (by linarith [h i])⟩
    · rintro ⟨hsMin,hsMax⟩ k
      by_cases hs : 0 ≤ s
      · linarith [mul_le_mul_of_nonneg_left (hi k (Finset.mem_univ _)) hs,
          mul_le_mul_of_nonpos_right hsMax him.le]
      · linarith [mul_le_mul_of_nonpos_left (hj k (Finset.mem_univ _)) (le_of_not_ge hs),
          mul_le_mul_of_nonneg_right hsMin hjp.le]
  have hrank (s : ℝ) (k : Fin 3) (hs : s * μ k = -1) : (σ + s • H).rank ≤ 2 := by
    apply rank_le_two_of_det_zero
    have hd : (Matrix.diagonal (fun i => ((1 + s * μ i : ℝ) : ℂ))).det = 0 := by
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hs, add_neg_cancel]; rfl)
    rw [hline, hfeature]
    simp only [Matrix.det_mul, hd, mul_zero, zero_mul]
  have htr (s : ℝ) : (σ + s • H).trace = 1 := by simp [Matrix.trace_add, Matrix.trace_smul, htrace, htrH]
  let weight := -sMin / (sMax - sMin)
  have hden : 0 < sMax - sMin := by linarith
  have hl : 0 < weight := div_pos (neg_pos.mpr hMin) hden
  have hl' : weight < 1 := (div_lt_one hden).mpr (by linarith)
  have hweight : weight * sMax + (1 - weight) * sMin = 0 := by
    dsimp only [weight]
    field_simp
    ring
  refine ⟨sMin, sMax, hMin, hMax, hinterval, hrank _ _ hzMin, hrank _ _ hzMax, htr _, htr _, weight, hl, hl', ?_⟩
  calc
    σ = (weight + (1 - weight)) • σ + (weight * sMax + (1 - weight) * sMin) • H := by
      rw [hweight, zero_smul, add_zero, show weight + (1 - weight) = 1 by ring, one_smul]
    _ = _ := by module

/-- The two chord endpoints lift to actual native atom dyads in the standard
quaternionic window, with their specified complex projections. -/
theorem complexDensity_chord_quaternionic_atoms (σ H : ComplexMatrix3) (hσ : σ.PosDef)
    (htrace : σ.trace = 1) (hH : H.IsHermitian) (hzero : H ≠ 0) (htrH : H.trace = 0) :
    ∃ (sMin sMax weight : ℝ) (pMin pMax : Albert),
      sMin < 0 ∧ 0 < sMax ∧ 0 < weight ∧ weight < 1 ∧
      IsAtom pMin ∧ IsAtom pMax ∧
      pMin ∈ standardQuaternionicWindow.subalgebra.carrier ∧
      pMax ∈ standardQuaternionicWindow.subalgebra.carrier ∧
      projectedMatrix standardComplexWindow pMin = σ + sMin • H ∧
      projectedMatrix standardComplexWindow pMax = σ + sMax • H ∧
      σ = weight • projectedMatrix standardComplexWindow pMax +
        (1 - weight) • projectedMatrix standardComplexWindow pMin := by
  obtain ⟨sMin,sMax,hm,hp,hint,hrm,hrp,htm,htp,weight,hw,hw',hcomb⟩ :=
    complexDensity_rankTwo_chord σ H hσ htrace hH hzero htrH
  have hle : sMin ≤ sMax := (hm.trans hp).le
  obtain ⟨Zm,_,_,ham,hwm,hpm⟩ :=
    complexDensity_rank_le_two_quaternionicLift _ ((hint sMin).mpr ⟨le_rfl,hle⟩) htm hrm
  obtain ⟨Zp,_,_,hap,hwp,hpp⟩ :=
    complexDensity_rank_le_two_quaternionicLift _ ((hint sMax).mpr ⟨hle,le_rfl⟩) htp hrp
  exact ⟨sMin,sMax,weight,quaternionicDyadFromTwoColumns Zm,quaternionicDyadFromTwoColumns Zp,
    hm,hp,hw,hw',ham,hap,hwm,hwp,hpm,hpp,by simpa only [hpm,hpp] using hcomb⟩

end AlbertSequential.WindowProbability
