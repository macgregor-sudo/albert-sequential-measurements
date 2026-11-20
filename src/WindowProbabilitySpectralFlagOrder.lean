/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralFlagEvaluation
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set
open scoped Matrix ComplexOrder

/-- Mathlib's descending Hermitian eigenvalues indexed by the literal `Fin 3`. -/
def sortedHermitianSpectrum {X : ComplexMatrix3} (hX : X.IsHermitian) : Fin 3 → ℝ :=
  hX.eigenvalues₀ ∘ finCongr (Fintype.card_fin 3).symm

theorem sortedHermitianSpectrum_antitone {X : ComplexMatrix3} (hX : X.IsHermitian) :
    Antitone (sortedHermitianSpectrum hX) :=
  fun _ _ h => hX.eigenvalues₀_antitone h

theorem sortedHermitianSpectrum_range_eq {X : ComplexMatrix3} (hX : X.IsHermitian) :
    Set.range (sortedHermitianSpectrum hX) = Set.range hX.eigenvalues := by
  let e : Fin (Fintype.card (Fin 3)) ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
  let ord : Fin 3 ≃ Fin (Fintype.card (Fin 3)) := finCongr (Fintype.card_fin 3).symm
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨e (ord i), ?_⟩
    change hX.eigenvalues₀ (e.symm (e (ord i))) = hX.eigenvalues₀ (ord i)
    rw [e.symm_apply_apply]
  · rintro ⟨i, rfl⟩
    refine ⟨ord.symm (e.symm i), ?_⟩
    change hX.eigenvalues₀ (ord (ord.symm (e.symm i))) = hX.eigenvalues₀ (e.symm i)
    rw [ord.apply_symm_apply]

private theorem injective_of_fin3_range_eq {d c : Fin 3 → ℝ} (h : Set.range d = Set.range c)
    (hc : Function.Injective c) : Function.Injective d := by
  have hex (i : Fin 3) : ∃ j, d j = c i := by
    have hi : c i ∈ Set.range d := h.symm ▸ Set.mem_range_self i
    exact hi
  choose f hf using hex
  have hi : Function.Injective f := fun i j hij => hc ((hf i).symm.trans ((congrArg d hij).trans (hf j)))
  have hs := Finite.injective_iff_surjective.mp hi
  intro i j hij
  obtain ⟨i', rfl⟩ := hs i
  obtain ⟨j', rfl⟩ := hs j
  exact congrArg f (hc ((hf i').symm.trans (hij.trans (hf j'))))

theorem eigenvalues_range_spectralConjugate (U : SpectralUnitary) (c : Fin 3 → ℝ)
    (hX : (spectralConjugate U c).IsHermitian) : Set.range hX.eigenvalues = Set.range c := by
  have he := hX.spectrum_eq_image_range
  change spectrum ℂ (spectralConjugate U c) = Complex.ofReal '' Set.range hX.eigenvalues at he
  rw [spectralConjugate_spectrum] at he
  ext y
  constructor
  · intro hy
    have hc : (y : ℂ) ∈ Set.range (fun i => (c i : ℂ)) := he.symm ▸ mem_image_of_mem _ hy
    obtain ⟨i, hi⟩ := hc
    exact ⟨i, Complex.ofReal_injective hi⟩
  · rintro ⟨i, rfl⟩
    have hh : ((c i : ℝ) : ℂ) ∈ Complex.ofReal '' Set.range hX.eigenvalues := he ▸ Set.mem_range_self i
    obtain ⟨z, hz, hzc⟩ := hh
    rwa [Complex.ofReal_injective hzc] at hz

/-- On every ordered angular conjugation image, the actual sorted spectrum is the input diagonal. -/
theorem sortedHermitianSpectrum_spectralConjugate (U : SpectralUnitary) (c : Fin 3 → ℝ)
    (hc : StrictAnti c) (hX : (spectralConjugate U c).IsHermitian) : sortedHermitianSpectrum hX = c := by
  have he := (sortedHermitianSpectrum_range_eq hX).trans (eigenvalues_range_spectralConjugate U c hX)
  exact strictAnti_fin3_eq_of_range_eq
    ((sortedHermitianSpectrum_antitone hX).strictAnti_of_injective (injective_of_fin3_range_eq he hc.injective)) hc he

theorem sortedHermitianSpectrum_pos {X : ComplexMatrix3} (hX : X.PosDef) (i : Fin 3) :
    0 < sortedHermitianSpectrum hX.isHermitian i := by
  have h := sortedHermitianSpectrum_range_eq hX.isHermitian
  obtain ⟨j, hj⟩ : sortedHermitianSpectrum hX.isHermitian i ∈ Set.range hX.isHermitian.eigenvalues :=
    h ▸ Set.mem_range_self i
  exact hj ▸ hX.eigenvalues_pos j

end AlbertSequential.WindowProbability
