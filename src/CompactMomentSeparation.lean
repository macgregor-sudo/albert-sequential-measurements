/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteCoordinateExtraction
public import FiniteTableSeparation
public import MomentTopology
public import NativeWordDuality

/-! A common finite linear separator from actual all-word moment exclusion.
No native no-match, generation, short horizon or Hilbert bridge is assumed proved. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open AlbertSequential.NativeAnalysis
open scoped BigOperators

def finiteCoordinatesFunctional {n : ℕ} (F : Finset (Word (Fin n)))
    (c : F → ℝ) : FiniteRealWordFunctional n :=
  ⟨Finset.univ.toList.map (fun i : F => (c i, i.val))⟩

theorem finiteCoordinatesFunctional_evaluate {n : ℕ}
    (F : Finset (Word (Fin n))) (c : F → ℝ) (f : Word (Fin n) → ℝ) :
    (finiteCoordinatesFunctional F c).evaluate f = tableLinearForm c (fun i : F => f i) := by
  simp only [finiteCoordinatesFunctional, FiniteRealWordFunctional.evaluate,
    List.map_map, Function.comp_def, Finset.sum_map_toList, tableLinearForm]

theorem finiteCoordinatesFunctional_horizon {n : ℕ}
    (F : Finset (Word (Fin n))) (c : F → ℝ) :
    (finiteCoordinatesFunctional F c).HasHorizon (F.sup List.length) := by
  intro t ht
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
  exact Finset.le_sup (f := List.length) i.property

private theorem moment_probability_empty {n : ℕ} (m : ProjectionMoments n)
    (hm : AdmissibleProjectionMoments n m) : momentWordProbability m [] = 1 := by
  simpa [momentWordProbability, effectPolynomial, amplitudePolynomial,
    polynomialStar, polynomialMultiply, polynomialMoment] using hm.normalized

private theorem convex_moment_coordinate_image {n : ℕ}
    (F : Finset (Word (Fin n))) :
    Convex ℝ ((fun m => fun i : F => momentWordProbability m i) ''
      projectionMomentDomain n) := by
  rintro x ⟨m,hm,rfl⟩ y ⟨k,hk,rfl⟩ a b ha hb hab
  refine ⟨a • m + b • k, convex_projectionMomentDomain n hm hk ha hb hab, ?_⟩
  funext i
  exact polynomialMoment_combination (effectPolynomial i.val) a b m k

private theorem convex_native_coordinate_image {n : ℕ}
    (p : Fin n → Albert) (states : Set Albert) (hstates : Convex ℝ states)
    (F : Finset (Word (Fin n))) :
    Convex ℝ ((fun ρ => fun i : F => nativeWordProbability p ρ i) '' states) := by
  rintro x ⟨ρ,hρ,rfl⟩ y ⟨σ,hσ,rfl⟩ a b ha hb hab
  refine ⟨a • ρ + b • σ, hstates hρ hσ ha hb hab, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    nativeWordProbability_add, nativeWordProbability_smul]

/-- Uniform exclusion of all pairs of states and moment models gives one
finite real word functional, with explicit trace-one normalization. -/
theorem uniformMomentSeparator_of_compact_noMatch {n : ℕ}
    (p : Fin n → Albert) (states : Set Albert)
    (hc : IsCompact states) (hv : Convex ℝ states)
    (htr : ∀ ρ ∈ states, albertTrace ρ = 1)
    (hnone : NoMomentMatch p states) : UniformMomentSeparator p states := by
  classical
  obtain ⟨F,hempty,hF⟩ := exists_finite_distinguishing_coordinates_containing
    (isCompact_projectionMomentDomain n) hc
    (fun w m => momentWordProbability m w)
    (fun w ρ => nativeWordProbability p ρ w)
    continuous_momentWordProbability (continuous_nativeWordProbability p)
    hnone ([] : Word (Fin n))
  let M : Set (F → ℝ) := (fun m => fun i : F => momentWordProbability m i) ''
    projectionMomentDomain n
  let N : Set (F → ℝ) := (fun ρ => fun i : F => nativeWordProbability p ρ i) '' states
  have hMc : IsCompact M := (isCompact_projectionMomentDomain n).image
    (continuous_pi fun i => continuous_momentWordProbability i.val)
  have hNc : IsCompact N := hc.image
    (continuous_pi fun i => continuous_nativeWordProbability p i.val)
  have hdisj : Disjoint N M :=
    (disjoint_coordinate_images_of_distinguishing (projectionMomentDomain n) states
      (fun w m => momentWordProbability m w)
      (fun w ρ => nativeWordProbability p ρ w) F hF).symm
  obtain ⟨c,γ,hγ,hN,hM⟩ := finiteCompactConvex_normalizedSeparation
    hNc (convex_native_coordinate_image p states hv F)
    hMc (convex_moment_coordinate_image F) hdisj ⟨[],hempty⟩
    (by
      rintro x ⟨ρ,hρ,rfl⟩
      exact htr ρ hρ)
    (by
      rintro x ⟨m,hm,rfl⟩
      exact moment_probability_empty m hm)
  refine ⟨F.sup List.length, finiteCoordinatesFunctional F c, γ, hγ,
    finiteCoordinatesFunctional_horizon F c, ?_, ?_⟩
  · intro m hm
    rw [finiteCoordinatesFunctional_evaluate]
    exact hγ.le.trans (hM _ ⟨m,hm,rfl⟩)
  · intro ρ hρ
    rw [finiteCoordinatesFunctional_evaluate]
    exact hN _ ⟨ρ,hρ,rfl⟩

/-- The shared exact contract is inhabited, including empty state sets. -/
theorem compactMomentSeparationContract (n : ℕ) : CompactMomentSeparationContract n :=
  ⟨uniformMomentSeparator_of_compact_noMatch⟩

end AlbertSequential
