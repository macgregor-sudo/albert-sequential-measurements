/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySpectralChart
public import Mathlib.MeasureTheory.Constructions.Pi

/-! The volume-preserving split of the nine real spectral coordinates and the
corresponding exact Fubini factorization. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Set MeasureTheory
open scoped ENNReal

/-- The first three real coordinates are the eigenvalue coordinates. The
last six are the real coordinates of the three complex angular entries. -/
def spectralProductCoordinates : (Fin 9 → ℝ) ≃ᵐ ((Fin 3 → ℝ) × (Fin 6 → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 ⊕ Fin 6 => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 6 => ℝ))

/-- The coordinate split preserves the actual product Lebesgue measure. -/
theorem measurePreserving_spectralProductCoordinates :
    MeasurePreserving spectralProductCoordinates volume
      ((volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 6 → ℝ))) := by
  have h₀ := volume_measurePreserving_piCongrLeft
    (fun _ : Fin 3 ⊕ Fin 6 => ℝ) finSumFinEquiv.symm
  have h₁ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 6 => ℝ)
  have h : MeasurePreserving spectralProductCoordinates volume volume := h₁.comp h₀
  simpa only [Measure.volume_eq_prod] using h

/-- The first projection of the product is the exact eigenvalue variation. -/
theorem spectralProductCoordinates_fst (q : Fin 9 → ℝ) :
    (spectralProductCoordinates q).1 = spectralVariations q := by
  funext i
  fin_cases i <;> rfl

/-- The six chart coordinates are the real and imaginary parts of the three exact offsets. -/
theorem spectralProductCoordinates_snd (q : Fin 9 → ℝ) :
    (spectralProductCoordinates q).2 =
      ![(spectralOrbitOffsets q 0).re, (spectralOrbitOffsets q 0).im,
        (spectralOrbitOffsets q 1).re, (spectralOrbitOffsets q 1).im,
        (spectralOrbitOffsets q 2).re, (spectralOrbitOffsets q 2).im] := by
  funext i
  fin_cases i <;> rfl

/-- Fubini separates a nonnegative eigenvalue weight and angular weight on the
literal spectral-coordinate product region. -/
theorem lintegral_spectralProductCoordinates_mul (D : Set (Fin 3 → ℝ)) (A : Set (Fin 6 → ℝ))
    (hD : MeasurableSet D) (hA : MeasurableSet A)
    (f : (Fin 3 → ℝ) → ℝ≥0∞) (g : (Fin 6 → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ q in spectralProductCoordinates ⁻¹' (D ×ˢ A),
      f (spectralProductCoordinates q).1 * g (spectralProductCoordinates q).2) =
    (∫⁻ x in D, f x) * ∫⁻ v in A, g v := by
  let p := spectralProductCoordinates
  have hp := measurePreserving_spectralProductCoordinates
  have hm : Measurable (fun r : (Fin 3 → ℝ) × (Fin 6 → ℝ) => f r.1 * g r.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  change (∫⁻ q in p ⁻¹' (D ×ˢ A), f (p q).1 * g (p q).2) = _
  have he : (∫⁻ q in p ⁻¹' (D ×ˢ A), f (p q).1 * g (p q).2) =
      ∫⁻ r in D ×ˢ A, f r.1 * g r.2 ∂(volume.prod volume) := by
    rw [← hp.map_eq, setLIntegral_map (hD.prod hA) hm hp.measurable]
  rw [he, ← Measure.prod_restrict, lintegral_prod_mul hf.aemeasurable hg.aemeasurable]

end AlbertSequential.WindowProbability
