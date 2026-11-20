/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilityComplexAmbient
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped Matrix

abbrev SpectralUnitary := Matrix.unitaryGroup (Fin 3) ℂ

/-- A fixed strictly descending simple spectrum encoding an ordered eigenflag. -/
def flagReferenceEigenvalues : Fin 3 → ℝ := ![3, 2, 1]

theorem flagReferenceEigenvalues_strictAnti : StrictAnti flagReferenceEigenvalues := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num [flagReferenceEigenvalues]

def spectralDiagonal (c : Fin 3 → ℝ) : ComplexMatrix3 :=
  Matrix.diagonal fun i => (c i : ℂ)

def spectralConjugate (U : SpectralUnitary) (c : Fin 3 → ℝ) : ComplexMatrix3 :=
  complexUnitaryConjugate U (spectralDiagonal c)

theorem spectralConjugate_one (c : Fin 3 → ℝ) : spectralConjugate 1 c = spectralDiagonal c := by
  simp [spectralConjugate, complexUnitaryConjugate]

theorem spectralConjugate_mul (U V : SpectralUnitary) (c : Fin 3 → ℝ) :
    spectralConjugate (U * V) c = complexUnitaryConjugate U (spectralConjugate V c) := by
  change ((U : ComplexMatrix3) * (V : ComplexMatrix3)) * spectralDiagonal c *
    star ((U : ComplexMatrix3) * (V : ComplexMatrix3)) = _
  simp only [spectralConjugate, complexUnitaryConjugate, star_mul, mul_assoc]

theorem spectralConjugate_spectrum (U : SpectralUnitary) (c : Fin 3 → ℝ) :
    spectrum ℂ (spectralConjugate U c) = Set.range (fun i => (c i : ℂ)) := by
  calc
    _ = spectrum ℂ (spectralDiagonal c) :=
      AlgEquiv.spectrum_eq (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U).toAlgEquiv _
    _ = _ := spectrum_diagonal _

theorem strictAnti_fin3_eq_of_range_eq {c μ : Fin 3 → ℝ} (hc : StrictAnti c) (hμ : StrictAnti μ)
    (hrange : Set.range c = Set.range μ) : c = μ := by
  have hmax (ν : Fin 3 → ℝ) (hν : StrictAnti ν) (i : Fin 3) : ν i ≤ ν 0 :=
    hν.antitone (Fin.zero_le i)
  have hmin (ν : Fin 3 → ℝ) (hν : StrictAnti ν) (i : Fin 3) : ν 2 ≤ ν i := by
    apply hν.antitone
    change i.val ≤ 2
    omega
  have hcμ (i : Fin 3) : ∃ j, μ j = c i := by
    have h : c i ∈ Set.range μ := hrange ▸ Set.mem_range_self i
    exact h
  have hμc (i : Fin 3) : ∃ j, c j = μ i := by
    have h : μ i ∈ Set.range c := hrange.symm ▸ Set.mem_range_self i
    exact h
  obtain ⟨i₀, hi₀⟩ := hcμ 0
  obtain ⟨j₀, hj₀⟩ := hμc 0
  obtain ⟨i₂, hi₂⟩ := hcμ 2
  obtain ⟨j₂, hj₂⟩ := hμc 2
  have h0 : c 0 = μ 0 := le_antisymm (hi₀ ▸ hmax μ hμ i₀) (hj₀ ▸ hmax c hc j₀)
  have h2 : c 2 = μ 2 := le_antisymm (hj₂ ▸ hmin c hc j₂) (hi₂ ▸ hmin μ hμ i₂)
  obtain ⟨i, hi⟩ := hcμ 1
  have h1 : c 1 = μ 1 := by
    fin_cases i
    · have h : c 1 = c 0 := hi.symm.trans h0.symm
      exact (by decide : (1 : Fin 3) ≠ 0) (hc.injective h) |>.elim
    · exact hi.symm
    · have h : c 1 = c 2 := hi.symm.trans h2.symm
      exact (by decide : (1 : Fin 3) ≠ 2) (hc.injective h) |>.elim
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Equality of unitary conjugates determines the decreasing spectrum. -/
theorem spectralConjugate_eigenvalues_eq {c μ : Fin 3 → ℝ} (hc : StrictAnti c) (hμ : StrictAnti μ)
    {U V : SpectralUnitary} (h : spectralConjugate U c = spectralConjugate V μ) : c = μ := by
  apply strictAnti_fin3_eq_of_range_eq hc hμ
  have hs := congrArg (spectrum ℂ) h
  rw [spectralConjugate_spectrum, spectralConjugate_spectrum] at hs
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ : ((c i : ℝ) : ℂ) ∈ Set.range (fun j => (μ j : ℂ)) := hs ▸ Set.mem_range_self i
    exact ⟨j, Complex.ofReal_injective hj⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ : ((μ j : ℝ) : ℂ) ∈ Set.range (fun i => (c i : ℂ)) := hs.symm ▸ Set.mem_range_self j
    exact ⟨i, Complex.ofReal_injective hi⟩

private theorem spectralConjugate_fixed_all {W : SpectralUnitary} {c : Fin 3 → ℝ}
    (hc : Function.Injective c) (h : spectralConjugate W c = spectralDiagonal c)
    (μ : Fin 3 → ℝ) : spectralConjugate W μ = spectralDiagonal μ := by
  let M : ComplexMatrix3 := W
  have hm : M * spectralDiagonal c = spectralDiagonal c * M := by
    have H := congrArg (fun X : ComplexMatrix3 => X * M) h
    change (M * spectralDiagonal c * star M) * M = spectralDiagonal c * M at H
    rwa [mul_assoc (M * spectralDiagonal c), Unitary.coe_star_mul_self W, mul_one] at H
  have hzero (i j : Fin 3) (hij : i ≠ j) : M i j = 0 := by
    have he := congrArg (fun X : ComplexMatrix3 => X i j) hm
    simp only [spectralDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hz : M i j * ((c j : ℂ) - (c i : ℂ)) = 0 := by
      rw [mul_sub, he, mul_comm ((c i : ℝ) : ℂ), sub_self]
    exact (mul_eq_zero.mp hz).resolve_right (fun hab =>
      hij ((hc (Complex.ofReal_injective (sub_eq_zero.mp hab))).symm))
  have hc : M * spectralDiagonal μ = spectralDiagonal μ * M := by
    ext i j
    simp only [spectralDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = j
    · subst j
      exact mul_comm _ _
    · simp [hzero i j hij]
  change M * spectralDiagonal μ * star M = spectralDiagonal μ
  have hUnit : M * star M = 1 := by
    change (W : ComplexMatrix3) * star (W : ComplexMatrix3) = 1
    rw [← Unitary.coe_star]
    exact Unitary.coe_mul_star_self W
  rw [hc, mul_assoc, hUnit, mul_one]

/-- Two unitaries agreeing on a simple diagonal agree on every diagonal. -/
theorem spectralConjugate_eq_of_simple {c : Fin 3 → ℝ} (hc : Function.Injective c)
    {U V : SpectralUnitary} (h : spectralConjugate U c = spectralConjugate V c)
    (μ : Fin 3 → ℝ) : spectralConjugate U μ = spectralConjugate V μ := by
  have hW : spectralConjugate (V⁻¹ * U) c = spectralDiagonal c := by
    rw [spectralConjugate_mul, h, ← spectralConjugate_mul, inv_mul_cancel, spectralConjugate_one]
  have h := spectralConjugate_fixed_all hc hW μ
  have hh := congrArg (complexUnitaryConjugate V) h
  rw [← spectralConjugate_mul, ← mul_assoc, mul_inv_cancel, one_mul] at hh
  exact hh

/-- The ordered eigenvalues and fixed flag are the entire spectral ambiguity. -/
theorem spectralConjugate_eq_iff_of_strictAnti {c μ : Fin 3 → ℝ} (hc : StrictAnti c) (hμ : StrictAnti μ)
    (U V : SpectralUnitary) : spectralConjugate U c = spectralConjugate V μ ↔
      c = μ ∧ spectralConjugate U flagReferenceEigenvalues = spectralConjugate V flagReferenceEigenvalues := by
  constructor
  · intro h
    have hsame := spectralConjugate_eigenvalues_eq hc hμ h
    subst μ
    exact ⟨rfl, spectralConjugate_eq_of_simple hc.injective h flagReferenceEigenvalues⟩
  · rintro ⟨rfl, h⟩
    exact spectralConjugate_eq_of_simple flagReferenceEigenvalues_strictAnti.injective h c

def spectralFlagOrbit : Set ComplexMatrix3 := Set.range (fun U => spectralConjugate U flagReferenceEigenvalues)

abbrev SpectralFlag := spectralFlagOrbit

def spectralFlagOfUnitary (U : SpectralUnitary) : SpectralFlag :=
  ⟨_, Set.mem_range_self U⟩

theorem spectralFlagOfUnitary_surjective : Function.Surjective spectralFlagOfUnitary := by
  rintro ⟨X, ⟨U, rfl⟩⟩
  exact ⟨U, rfl⟩

theorem continuous_spectralConjugate (c : Fin 3 → ℝ) : Continuous (fun U : SpectralUnitary => spectralConjugate U c) := by
  change Continuous (fun U : SpectralUnitary => (U : ComplexMatrix3) * spectralDiagonal c * star (U : ComplexMatrix3))
  exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul continuous_subtype_val.star

theorem isCompact_spectralFlagOrbit : IsCompact spectralFlagOrbit := by
  let : CompactSpace SpectralUnitary := isCompact_iff_compactSpace.mp (isCompact_complexUnitaryGroup (Fin 3))
  exact isCompact_range (continuous_spectralConjugate flagReferenceEigenvalues)

instance : CompactSpace SpectralFlag := isCompact_iff_compactSpace.mp isCompact_spectralFlagOrbit

theorem continuous_spectralFlagOfUnitary : Continuous spectralFlagOfUnitary :=
  (continuous_spectralConjugate flagReferenceEigenvalues).subtype_mk _

theorem conjugate_mem_spectralFlagOrbit (U : SpectralUnitary) {X : ComplexMatrix3}
    (hX : X ∈ spectralFlagOrbit) : complexUnitaryConjugate U X ∈ spectralFlagOrbit := by
  obtain ⟨V, rfl⟩ := hX
  exact ⟨U * V, spectralConjugate_mul U V flagReferenceEigenvalues⟩

instance : MulAction SpectralUnitary SpectralFlag where
  smul U X := ⟨complexUnitaryConjugate U X.val, conjugate_mem_spectralFlagOrbit U X.property⟩
  one_smul X := by
    apply Subtype.ext
    change (1 : ComplexMatrix3) * X.val * star (1 : ComplexMatrix3) = X.val
    simp
  mul_smul U V X := by
    apply Subtype.ext
    change ((U : ComplexMatrix3) * (V : ComplexMatrix3)) * X.val *
      star ((U : ComplexMatrix3) * (V : ComplexMatrix3)) =
      (U : ComplexMatrix3) * ((V : ComplexMatrix3) * X.val * star (V : ComplexMatrix3)) *
        star (U : ComplexMatrix3)
    simp only [star_mul, mul_assoc]

theorem spectralFlag_smul_unitary (U V : SpectralUnitary) :
    U • spectralFlagOfUnitary V = spectralFlagOfUnitary (U * V) :=
  Subtype.ext (spectralConjugate_mul U V flagReferenceEigenvalues).symm

theorem continuous_spectralFlagAction : Continuous (fun p : SpectralUnitary × SpectralFlag => p.1 • p.2) := by
  have h1 : Continuous (fun p : SpectralUnitary × SpectralFlag => (p.1 : ComplexMatrix3)) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous (fun p : SpectralUnitary × SpectralFlag => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((h1.matrix_mul h2).matrix_mul h1.star).subtype_mk _

theorem continuous_spectralFlagSMul (U : SpectralUnitary) : Continuous (fun X : SpectralFlag => U • X) := by
  have h : Continuous (fun X : SpectralFlag => ((U : ComplexMatrix3) * X.val * star (U : ComplexMatrix3))) :=
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  exact h.subtype_mk _

def spectralFlagTranslate (U : SpectralUnitary) : SpectralFlag ≃ₜ SpectralFlag where
  toEquiv := MulAction.toPerm U
  continuous_toFun := continuous_spectralFlagSMul U
  continuous_invFun := continuous_spectralFlagSMul U⁻¹

theorem spectralFlag_transitive (X : SpectralFlag) : ∃ U : SpectralUnitary, U • spectralFlagOfUnitary 1 = X := by
  obtain ⟨U, rfl⟩ := spectralFlagOfUnitary_surjective X
  exact ⟨U, (spectralFlag_smul_unitary U 1).trans (congrArg spectralFlagOfUnitary (mul_one U))⟩

/-- Left Haar probability pushed to the compact orbit of ordered eigenflags. -/
def spectralFlagHaarProbability : Measure SpectralFlag :=
  (Measure.haarMeasure (allComplexUnitaries (Fin 3))).map spectralFlagOfUnitary

instance : IsProbabilityMeasure spectralFlagHaarProbability := by
  have : IsProbabilityMeasure (Measure.haarMeasure (allComplexUnitaries (Fin 3))) :=
    ⟨Measure.haarMeasure_self⟩
  exact (Measure.isProbabilityMeasure_map_iff continuous_spectralFlagOfUnitary.measurable.aemeasurable).mpr
    inferInstance

theorem measurePreserving_spectralFlagTranslate (U : SpectralUnitary) :
    MeasurePreserving (spectralFlagTranslate U) spectralFlagHaarProbability spectralFlagHaarProbability := by
  let H := Measure.haarMeasure (allComplexUnitaries (Fin 3))
  have hOrbit := continuous_spectralFlagOfUnitary.measurable
  have hT := (spectralFlagTranslate U).continuous.measurable
  have hMul := measurePreserving_mul_left H U
  refine ⟨hT, ?_⟩
  unfold spectralFlagHaarProbability
  change (H.map spectralFlagOfUnitary).map (spectralFlagTranslate U) = H.map spectralFlagOfUnitary
  rw [Measure.map_map hT hOrbit, show spectralFlagTranslate U ∘ spectralFlagOfUnitary =
    spectralFlagOfUnitary ∘ (U * ·) from funext (spectralFlag_smul_unitary U),
    ← Measure.map_map hOrbit hMul.measurable, hMul.map_eq]

theorem spectralFlagHaarProbability_unique (μ : Measure SpectralFlag) [IsProbabilityMeasure μ]
    (hμ : ∀ U : SpectralUnitary, MeasurePreserving (spectralFlagTranslate U) μ μ) :
    μ = spectralFlagHaarProbability := by
  let : SecondCountableTopology ComplexMatrix3 := inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℂ))
  let : SecondCountableTopology SpectralFlag :=
    inferInstanceAs (SecondCountableTopology {X : ComplexMatrix3 // X ∈ spectralFlagOrbit})
  let H := complexUnitaryHaarProbability (Fin 3)
  have h := invariantProbability_eq_orbitMap continuous_spectralFlagAction.measurable
    (spectralFlagOfUnitary 1) spectralFlag_transitive H μ hμ
  have h' := invariantProbability_eq_orbitMap continuous_spectralFlagAction.measurable
    (spectralFlagOfUnitary 1) spectralFlag_transitive H spectralFlagHaarProbability
    measurePreserving_spectralFlagTranslate
  exact h.trans h'.symm

end AlbertSequential.WindowProbability
