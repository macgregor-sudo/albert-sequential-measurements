/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralFlagEvaluation
public import WindowProbabilitySpectralChart
public import WindowProbabilityGramCongruence

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set NormedSpace
open scoped Matrix Matrix.Norms.Frobenius

private def angularInclude (v : Fin 6 → ℝ) : Fin 9 → ℝ := ![0, 0, 0, v 0, v 1, v 2, v 3, v 4, v 5]

private def angularExtract (q : Fin 9 → ℝ) : Fin 6 → ℝ := ![q 3, q 4, q 5, q 6, q 7, q 8]

/-- Label the upper entries 01, 02, 12 by their adjacent real coordinate pairs. -/
def spectralAngularOffsets (v : Fin 6 → ℝ) : Fin 3 → ℂ := ![⟨v 0,v 1⟩, ⟨v 2,v 3⟩, ⟨v 4,v 5⟩]

private theorem continuous_angularInclude : Continuous angularInclude := by
  apply continuous_pi
  intro i
  fin_cases i <;> first | exact continuous_const | exact continuous_apply _

private theorem continuous_angularExtract : Continuous angularExtract := by
  apply continuous_pi
  intro i
  fin_cases i <;> exact continuous_apply _

theorem continuous_spectralAngularOffsets : Continuous spectralAngularOffsets := by
  have hc (i j : Fin 6) : Continuous (fun v : Fin 6 → ℝ => (⟨v i, v j⟩ : ℂ)) := by
    have re : Continuous (fun v : Fin 6 → ℝ => (v i : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_apply i)
    have im : Continuous (fun v : Fin 6 → ℝ => (v j : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_apply j)
    have h : (fun v : Fin 6 → ℝ => (⟨v i, v j⟩ : ℂ)) =
        fun v => (v i : ℂ) + (v j : ℂ) * Complex.I := by
      funext v
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [h]
    exact re.add (im.mul continuous_const)
  apply continuous_pi
  intro i
  fin_cases i <;> exact hc _ _

private theorem angularInclude_zero : angularInclude 0 = 0 := by
  funext i
  fin_cases i <;> rfl

private theorem angularExtract_include (v : Fin 6 → ℝ) : angularExtract (angularInclude v) = v := by
  funext i
  fin_cases i <;> rfl

private theorem spectralVariations_angularInclude (v : Fin 6 → ℝ) : spectralVariations (angularInclude v) = 0 := by
  funext i
  fin_cases i <;> rfl

private theorem spectralOrbitOffsets_angularInclude (v : Fin 6 → ℝ) :
    spectralOrbitOffsets (angularInclude v) = spectralAngularOffsets v := by
  funext i
  fin_cases i <;> rfl

private theorem angularInclude_extract_of_zero_variation (q : Fin 9 → ℝ) (hq : spectralVariations q = 0) :
    angularInclude (angularExtract q) = q := by
  have eq (i : Fin 3) := congrFun hq i
  funext i
  fin_cases i
  · exact (eq 0).symm
  · exact (eq 1).symm
  · exact (eq 2).symm
  all_goals rfl

def spectralAngularFlag (v : Fin 6 → ℝ) : SpectralFlag :=
  spectralFlagOfUnitary (spectralExpUnitary (spectralAngularOffsets v))

theorem continuous_spectralAngularFlag : Continuous spectralAngularFlag :=
  continuous_spectralFlagOfUnitary.comp (continuous_spectralExpUnitary.comp continuous_spectralAngularOffsets)

theorem spectralAngularFlag_zero : spectralAngularFlag 0 = spectralFlagOfUnitary 1 := by
  have hw : spectralAngularOffsets 0 = 0 := by
    funext i
    fin_cases i <;> rfl
  have hk : spectralSkewMatrix 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spectralSkewMatrix, mkHerm3Matrix] <;>
      apply Complex.ext <;> simp
  have hu : spectralExpUnitary 0 = 1 := by
    apply Subtype.ext
    rw [spectralExpUnitary_val, hk, NormedSpace.exp_zero]
    rfl
  rw [spectralAngularFlag, hw, hu]

private def flagCoords (F : SpectralFlag) : Fin 9 → ℝ := hermitianMatrixRealCoordinates F.val

private theorem continuous_flagCoords : Continuous flagCoords :=
  spectralMatrixOutput.continuous.comp continuous_subtype_val

private theorem spectralConjugate_isHermitian (U : SpectralUnitary) (c : Fin 3 → ℝ) :
    (spectralConjugate U c).IsHermitian := by
  rw [← spectralFlagEvaluate_unitary]
  exact spectralFlagEvaluate_isHermitian c _

private theorem coordinate_eq_of_Hermitian {X Y : ComplexMatrix3} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (h : hermitianMatrixRealCoordinates X = hermitianMatrixRealCoordinates Y) : X = Y :=
  congrArg Subtype.val (hermitianMatrixRealCoordinateEquiv.injective
    (show hermitianMatrixRealCoordinateEquiv ⟨X, hX⟩ = hermitianMatrixRealCoordinateEquiv ⟨Y, hY⟩ from h))

theorem strictAnti_fin3_iff (c : Fin 3 → ℝ) : StrictAnti c ↔ c 1 < c 0 ∧ c 2 < c 1 := by
  constructor
  · exact fun h => ⟨h (by decide : (0 : Fin 3) < 1), h (by decide : (1 : Fin 3) < 2)⟩
  · rintro ⟨h01,h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;>
      first | exact h01 | exact h12 | exact h12.trans h01

theorem isOpen_strictAnti_fin3 : IsOpen {c : Fin 3 → ℝ | StrictAnti c} := by
  have h : {c : Fin 3 → ℝ | StrictAnti c} = {c : Fin 3 → ℝ | c 1 < c 0} ∩ {c : Fin 3 → ℝ | c 2 < c 1} :=
    Set.ext fun c => strictAnti_fin3_iff c
  rw [h]
  exact (isOpen_lt (continuous_apply 1) (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 2) (continuous_apply 1))

private theorem continuous_shiftedSpectralVariations :
    Continuous (fun q : Fin 9 → ℝ => flagReferenceEigenvalues + spectralVariations q) := by
  apply continuous_const.add
  apply continuous_pi
  intro i
  fin_cases i <;> exact continuous_apply _

private theorem spectralExpChart_reference (q : Fin 9 → ℝ) :
    spectralExpChart flagReferenceEigenvalues q = hermitianMatrixRealCoordinates
      (spectralConjugate (spectralExpUnitary (spectralOrbitOffsets q))
        (flagReferenceEigenvalues + spectralVariations q)) := by
  rw [spectralExpChart_apply]
  unfold spectralConjugate complexUnitaryConjugate spectralDiagonal
  have hStar : star (exp (spectralSkewMatrix (spectralOrbitOffsets q))) =
      exp (-spectralSkewMatrix (spectralOrbitOffsets q)) := spectralExpUnitary_star_val _
  simp only [spectralExpUnitary_val, hStar, Pi.add_apply]

private theorem spectralExpChart_reference_angularInclude (v : Fin 6 → ℝ) :
    spectralExpChart flagReferenceEigenvalues (angularInclude v) = flagCoords (spectralAngularFlag v) := by
  rw [spectralExpChart_reference, spectralVariations_angularInclude, spectralOrbitOffsets_angularInclude, add_zero]
  rfl

/-- A bounded open six-coordinate chart at the reference flag with its genuine inverse. -/
structure SpectralAngularChart where
  source : Set (Fin 6 → ℝ)
  openSource : IsOpen source
  zeroMem : 0 ∈ source
  source_ball : source ⊆ Metric.ball 0 1
  openImage : IsOpen (spectralAngularFlag '' source)
  inverse : SpectralFlag → Fin 6 → ℝ
  leftInverse : Set.LeftInvOn inverse spectralAngularFlag source
  continuousInverse : ContinuousOn inverse (spectralAngularFlag '' source)

theorem exists_spectralAngularChart : Nonempty SpectralAngularChart := by
  obtain ⟨e, hzero, he⟩ := spectralExpChart_localHomeomorph flagReferenceEigenvalues
    flagReferenceEigenvalues_strictAnti.injective
  let B : Set (Fin 6 → ℝ) := Metric.ball 0 1
  let Z := angularInclude ⁻¹' e.source ∩ B
  let V := e.source ∩ ((fun q => flagReferenceEigenvalues + spectralVariations q) ⁻¹'
    {c | StrictAnti c} ∩ angularExtract ⁻¹' B)
  have hcontinuousB : IsOpen B := Metric.isOpen_ball
  have hB0 : 0 ∈ B := Metric.mem_ball_self zero_lt_one
  have hZ : IsOpen Z := (e.open_source.preimage continuous_angularInclude).inter hcontinuousB
  have hV : IsOpen V := e.open_source.inter
    ((isOpen_strictAnti_fin3.preimage continuous_shiftedSpectralVariations).inter
      (hcontinuousB.preimage continuous_angularExtract))
  have h0 : 0 ∈ Z := ⟨by rwa [mem_preimage, angularInclude_zero], hB0⟩
  have hEval (q : Fin 9 → ℝ) : e q = hermitianMatrixRealCoordinates
      (spectralConjugate (spectralExpUnitary (spectralOrbitOffsets q))
        (flagReferenceEigenvalues + spectralVariations q)) :=
    (congrFun he q).trans (spectralExpChart_reference q)
  have hSlice (v : Fin 6 → ℝ) : e (angularInclude v) = flagCoords (spectralAngularFlag v) :=
    (congrFun he _).trans (spectralExpChart_reference_angularInclude v)
  have himage : spectralAngularFlag '' Z = flagCoords ⁻¹' (e '' V) := by
    ext F
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨angularInclude v, ⟨hv.1, ?_, ?_⟩, hSlice v⟩
      · change StrictAnti (flagReferenceEigenvalues + spectralVariations (angularInclude v))
        simpa only [spectralVariations_angularInclude, add_zero] using flagReferenceEigenvalues_strictAnti
      · change angularExtract (angularInclude v) ∈ B
        rw [angularExtract_include]
        exact hv.2
    · rintro ⟨q, hq, heq⟩
      obtain ⟨U, rfl⟩ := spectralFlagOfUnitary_surjective F
      let A := spectralExpUnitary (spectralOrbitOffsets q)
      let c := flagReferenceEigenvalues + spectralVariations q
      have hCoords : hermitianMatrixRealCoordinates (spectralConjugate A c) =
          hermitianMatrixRealCoordinates (spectralConjugate U flagReferenceEigenvalues) :=
        (hEval q).symm.trans heq
      have hMatrix := coordinate_eq_of_Hermitian (spectralConjugate_isHermitian A c)
        (spectralConjugate_isHermitian U flagReferenceEigenvalues) hCoords
      have hspec := spectralConjugate_eigenvalues_eq hq.2.1 flagReferenceEigenvalues_strictAnti hMatrix
      have hvzero : spectralVariations q = 0 := add_left_cancel (hspec.trans (add_zero _).symm)
      have hrest := angularInclude_extract_of_zero_variation q hvzero
      refine ⟨angularExtract q, ⟨?_, hq.2.2⟩, ?_⟩
      · change angularInclude (angularExtract q) ∈ e.source
        rw [hrest]
        exact hq.1
      · apply Subtype.ext
        change spectralConjugate (spectralExpUnitary (spectralAngularOffsets (angularExtract q)))
          flagReferenceEigenvalues = spectralConjugate U flagReferenceEigenvalues
        rw [← spectralOrbitOffsets_angularInclude, hrest]
        exact hspec ▸ hMatrix
  refine ⟨⟨Z, hZ, h0, inter_subset_right, ?_, fun F => angularExtract (e.symm (flagCoords F)), ?_, ?_⟩⟩
  · rw [himage]
    exact (e.isOpen_image_of_subset_source hV inter_subset_left).preimage continuous_flagCoords
  · intro v hv
    change angularExtract (e.symm (flagCoords (spectralAngularFlag v))) = v
    rw [← hSlice, e.left_inv hv.1, angularExtract_include]
  · apply continuous_angularExtract.comp_continuousOn
    apply e.continuousOn_symm.comp continuous_flagCoords.continuousOn
    rw [himage]
    intro x hx
    obtain ⟨q, hq, hEq⟩ := hx
    rw [← hEq]
    exact e.map_source hq.1

end AlbertSequential.WindowProbability
