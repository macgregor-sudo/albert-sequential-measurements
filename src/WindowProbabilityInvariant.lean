/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Prod

/-! Uniqueness of the invariant probability for the transitive action on
the atoms, once it is supplied with a probability Haar measure. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set

/-- For a transitive measurable group action, an invariant probability
is the orbit pushforward of any right-invariant probability on the group. -/
theorem invariantProbability_eq_orbitMap {G A : Type*} [Group G] [MulAction G A]
    [MeasurableSpace G] [MeasurableSpace A] [MeasurableMul G]
    (hact : Measurable fun a : G × A => a.1 • a.2)
    (a₀ : A) (htrans : ∀ a : A, ∃ g : G, g • a₀ = a)
    (H : Measure G) [IsProbabilityMeasure H] [H.IsMulRightInvariant]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (hinv : ∀ g : G, MeasurePreserving (fun a : A => g • a) μ μ) :
    μ = H.map (fun g => g • a₀) := by
  have horbit : Measurable fun g : G => g • a₀ := hact.comp measurable_prodMk_right
  ext s hs
  let E : Set (G × A) := (fun z : G × A => z.1 • z.2) ⁻¹' s
  have hE : MeasurableSet E := hact hs
  have hμ (g : G) : μ (Prod.mk g ⁻¹' E) = μ s := by
    change μ ((fun a : A => g • a) ⁻¹' s) = μ s
    rw [← Measure.map_apply (hinv g).measurable hs, (hinv g).map_eq]
  have hH (a : A) : H ((fun g => (g, a)) ⁻¹' E) = H.map (fun g => g • a₀) s := by
    obtain ⟨g, rfl⟩ := htrans a
    have hr := measurePreserving_mul_right H g
    have hs' : MeasurableSet ((fun x : G => x • a₀) ⁻¹' s) := horbit hs
    rw [Measure.map_apply horbit hs]
    change H ((fun x : G => x • (g • a₀)) ⁻¹' s) = _
    simp_rw [← mul_smul]
    change H ((· * g) ⁻¹' ((fun x : G => x • a₀) ⁻¹' s)) = _
    rw [← Measure.map_apply hr.measurable hs', hr.map_eq]
  calc
    μ s = (H.prod μ) E := by rw [Measure.prod_apply hE]; simp_rw [hμ]; simp
    _ = H.map (fun g => g • a₀) s := by rw [Measure.prod_apply_symm hE]; simp_rw [hH]; simp

end AlbertSequential.WindowProbability
