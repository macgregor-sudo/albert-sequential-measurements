/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAWordTransport

/-! The literal (complex) trace and the same representing density through all words of core 4.9. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential.FaithfulHermitianJordanEmbedding
variable {E : Type*} [AddCommGroup E] [Module ℝ E] {P : UnitalJordanProduct E} {d : ℕ}
  (ι : FaithfulHermitianJordanEmbedding P d)

theorem complex_traceForm (z x : E) :
    Matrix.trace (ι.map z * ι.map x) = (ι.traceForm z x : ℂ) := by
  symm
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace (ι.map z * ι.map x)) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    (ι.hermitian x).eq, (ι.hermitian z).eq, Matrix.trace_mul_comm]

theorem explicit_state_all_words {I : Type*} (p : I → E)
    (hp : ∀ i, P.product (p i) (p i) = p i)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x, 0 ≤ f (P.product x x)) (hnorm : f P.unit = 1) :
    ∃! z : E, (ι.map z).PosSemidef ∧ Matrix.trace (ι.map z) = 1 ∧
      (∀ x, Matrix.trace (ι.map z * ι.map x) = (f x : ℂ)) ∧
      (∀ i, (ι.map (p i)).IsHermitian ∧ ι.map (p i) * ι.map (p i) = ι.map (p i)) ∧
      ∀ w, Matrix.trace (ι.map z * wordOperator (ι.map ∘ p) w) = (f (P.sequentialWordEffect p w) : ℂ) := by
  obtain ⟨z, ⟨hz, ht, hall⟩, hu⟩ := ι.exists_unique_positive_trace_representative f hf hnorm
  have he (x : E) : Matrix.trace (ι.map z * ι.map x) = (f x : ℂ) :=
    (ι.complex_traceForm z x).trans (congrArg Complex.ofReal (hall x))
  refine ⟨z, ⟨hz, ht, he, fun i => ⟨ι.hermitian _, ?_⟩, fun w => ?_⟩, ?_⟩
  · rw [← ι.map_square, hp]
  · rw [← ι.map_sequentialWordEffect]; exact he _
  · rintro y ⟨hy, hyt, heval, _, _⟩
    exact hu y ⟨hy, hyt, fun x => congrArg Complex.re (heval x)⟩

theorem explicit_state_subalgebra_words {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : UnitalJordanProduct V) (j : E →ₗ[ℝ] V) (hj : j P.unit = Q.unit)
    (hm : ∀ x y, j (P.product x y) = Q.product (j x) (j y)) (p : I → E)
    (f : V →ₗ[ℝ] ℝ) (w : Word I) :
    Matrix.trace (ι.map (ι.traceRepresentative (f.comp j)) * wordOperator (ι.map ∘ p) w) =
      (f (Q.sequentialWordEffect (j ∘ p) w) : ℂ) := by
  rw [← ι.map_sequentialWordEffect, ι.complex_traceForm, ι.traceRepresentative_pairing,
    LinearMap.comp_apply, P.map_sequentialWordEffect Q j hj hm]

end AlbertSequential.FaithfulHermitianJordanEmbedding
