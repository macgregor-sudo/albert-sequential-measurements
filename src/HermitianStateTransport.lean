/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HermitianJordanEmbedding

/-! State transport into a supplied Jordan image using its ordinary trace form.
Uniqueness concerns the representative in the image, not all ambient densities.
Embedding existence and classification are not assumptions disguised as proofs. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential.FaithfulHermitianJordanEmbedding
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {P : UnitalJordanProduct E} {d : ℕ} (ι : FaithfulHermitianJordanEmbedding P d)

def liftedFunctional (f : E →ₗ[ℝ] ℝ) : ι.Element →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (f.comp ι.elementLinearEquiv.toLinearMap)

def traceRepresentative (f : E →ₗ[ℝ] ℝ) : E :=
  ((InnerProductSpace.toDual ℝ ι.Element).symm (ι.liftedFunctional f)).value

theorem traceRepresentative_pairing (f : E →ₗ[ℝ] ℝ) (x : E) :
    ι.traceForm (ι.traceRepresentative f) x = f x := by
  exact InnerProductSpace.toDual_symm_apply
    (x := (⟨x⟩ : ι.Element)) (y := ι.liftedFunctional f)

theorem traceRepresentative_unique (f : E →ₗ[ℝ] ℝ) (z : E)
    (hz : ∀ x, ι.traceForm z x = f x) : z = ι.traceRepresentative f := by
  apply sub_eq_zero.mp
  apply (ι.traceForm_self_eq_zero _).mp
  change (Matrix.trace (ι.map (z-ι.traceRepresentative f) *
    ι.map (z-ι.traceRepresentative f))).re = 0
  rw [map_sub, sub_mul, Matrix.trace_sub, Complex.sub_re]
  rw [← map_sub]
  change ι.traceForm z (z-ι.traceRepresentative f) -
    ι.traceForm (ι.traceRepresentative f) (z-ι.traceRepresentative f) = 0
  rw [hz, ι.traceRepresentative_pairing, sub_self]

theorem exists_unique_trace_representative (f : E →ₗ[ℝ] ℝ) :
    ∃! z : E, ∀ x, (Matrix.trace (ι.map z * ι.map x)).re = f x := by
  refine ⟨ι.traceRepresentative f, ι.traceRepresentative_pairing f, ?_⟩
  intro z hz
  exact ι.traceRepresentative_unique f z hz

theorem trace_representative_square (f : E →ₗ[ℝ] ℝ)
    (hf : ∀ x, 0 ≤ f (P.product x x)) (z : E)
    (hz : ∀ x, ι.traceForm z x = f x) : ∃ y, z = P.product y y := by
  let z' : ι.Element := ⟨z⟩
  have hp : z' ∈ ι.elementProduct.squareCone := by
    apply (ι.elementProduct.squareCone_self_dual ι.elementProduct_associative z').mpr
    rintro y ⟨v, rfl⟩
    change 0 ≤ ι.traceForm z (P.product v.value v.value)
    rw [hz]
    exact hf v.value
  obtain ⟨v, hv⟩ := hp
  exact ⟨v.value, congrArg Element.value hv⟩

theorem trace_representative_positive (f : E →ₗ[ℝ] ℝ)
    (hf : ∀ x, 0 ≤ f (P.product x x)) (z : E)
    (hz : ∀ x, ι.traceForm z x = f x) : (ι.map z).PosSemidef := by
  obtain ⟨v, rfl⟩ := ι.trace_representative_square f hf z hz
  rw [ι.map_square]
  have h := Matrix.posSemidef_conjTranspose_mul_self (ι.map v)
  rwa [ι.hermitian v] at h

theorem trace_representative_trace_one (f : E →ₗ[ℝ] ℝ)
    (hf : ∀ x, 0 ≤ f (P.product x x)) (hnorm : f P.unit = 1) (z : E)
    (hz : ∀ x, ι.traceForm z x = f x) : Matrix.trace (ι.map z) = 1 := by
  have hp := ι.trace_representative_positive f hf z hz
  have hr : (Matrix.trace (ι.map z)).re = 1 := by
    have h := hz P.unit
    simpa only [traceForm, ι.unit, mul_one, hnorm] using h
  exact Complex.ext hr (Complex.nonneg_iff.mp hp.trace_nonneg).2.symm

/-- Ordinary unnormalized matrix trace; no trace-preservation hypothesis on ι. -/
theorem exists_unique_positive_trace_representative (f : E →ₗ[ℝ] ℝ)
    (hf : ∀ x, 0 ≤ f (P.product x x)) (hnorm : f P.unit = 1) :
    ∃! z : E, (ι.map z).PosSemidef ∧ Matrix.trace (ι.map z) = 1 ∧
      ∀ x, (Matrix.trace (ι.map z * ι.map x)).re = f x := by
  refine ⟨ι.traceRepresentative f, ⟨?_, ?_, ι.traceRepresentative_pairing f⟩, ?_⟩
  · exact ι.trace_representative_positive f hf _ (ι.traceRepresentative_pairing f)
  · exact ι.trace_representative_trace_one f hf hnorm _ (ι.traceRepresentative_pairing f)
  · intro z hz
    exact ι.traceRepresentative_unique f z hz.2.2

end AlbertSequential.FaithfulHermitianJordanEmbedding
