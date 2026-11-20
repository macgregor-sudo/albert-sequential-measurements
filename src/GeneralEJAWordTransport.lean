/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Bridge.Criterion
public import HermitianStateTransport
public import JordanIdealProjections
public import JordanStateRiesz

/-! Word probabilities for a finite Euclidean Jordan algebra, and transport
to a finite complex projective model through a faithful Hermitian embedding. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

def sequentialOutcome (P : UnitalJordanProduct E) (p : ι → E) (a : Outcome ι) : E :=
  if a.2 then p a.1 else P.unit - p a.1

/-- The first outcome is the outermost quadratic update on effects. -/
def sequentialWordEffect (P : UnitalJordanProduct E) (p : ι → E) : Word ι → E
  | [] => P.unit
  | a :: w => P.quadraticRepresentation (P.sequentialOutcome p a) (P.sequentialWordEffect p w)

def sequentialBranchState (P : UnitalJordanProduct E) (p : ι → E) (ρ : E) (w : Word ι) : E :=
  w.foldl (fun x a => P.quadraticRepresentation (P.sequentialOutcome p a) x) ρ

theorem map_sequentialWordEffect
    (P : UnitalJordanProduct E) (Q : UnitalJordanProduct F) (f : E →ₗ[ℝ] F)
    (hunit : f P.unit = Q.unit)
    (hprod : ∀ x y, f (P.product x y) = Q.product (f x) (f y)) (p : ι → E) (w : Word ι) :
    f (P.sequentialWordEffect p w) = Q.sequentialWordEffect (f ∘ p) w := by
  induction w with
  | nil => exact hunit
  | cons a w ih =>
    have hout : f (P.sequentialOutcome p a) = Q.sequentialOutcome (f ∘ p) a := by
      rcases a with ⟨i, b⟩
      cases b <;> simp [sequentialOutcome, hunit]
    simp only [sequentialWordEffect, quadraticRepresentation_apply,
      map_sub, map_smul, hprod, hout, ih]

section CanonicalTrace

variable [FiniteDimensional ℝ E] (P : UnitalJordanProduct E) (hfr : P.FormallyReal)

theorem canonicalTrace_quadraticRepresentation_pairing (a x y : E) :
    P.canonicalTraceFormOfFormallyReal hfr (P.quadraticRepresentation a x) y =
      P.canonicalTraceFormOfFormallyReal hfr x (P.quadraticRepresentation a y) := by
  have hself (b u v : E) :
      P.canonicalTraceFormOfFormallyReal hfr (P.product b u) v =
        P.canonicalTraceFormOfFormallyReal hfr u (P.product b v) := by
    rw [P.commutative b u, P.canonicalTraceFormOfFormallyReal_associative hfr]
  simp only [quadraticRepresentation_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply]
  rw [hself, hself, hself]

/-- The effect-side expectation equals the trace of the chronological state
updates with the canonical primitive-normalized trace. -/
theorem canonicalTrace_sequentialBranchState (p : ι → E) (ρ : E) (w : Word ι) :
    P.canonicalTraceOfFormallyReal hfr (P.sequentialBranchState p ρ w) =
      P.canonicalPairingFunctional hfr ρ (P.sequentialWordEffect p w) := by
  induction w generalizing ρ with
  | nil => exact (P.canonicalTraceFormOfFormallyReal_unit hfr ρ).symm
  | cons a w ih =>
    change P.canonicalTraceOfFormallyReal hfr
        (P.sequentialBranchState p (P.quadraticRepresentation (P.sequentialOutcome p a) ρ) w) =
      P.canonicalPairingFunctional hfr ρ
        (P.quadraticRepresentation (P.sequentialOutcome p a) (P.sequentialWordEffect p w))
    rw [ih]
    exact P.canonicalTrace_quadraticRepresentation_pairing hfr _ _ _

end CanonicalTrace
end AlbertSequential.UnitalJordanProduct

namespace AlbertSequential.FaithfulHermitianJordanEmbedding

open AlbertChallenge.Bridge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {P : UnitalJordanProduct E} {d : ℕ}
  (embedding : FaithfulHermitianJordanEmbedding P d)

theorem map_sequentialWordEffect {ι : Type*} (p : ι → E) (w : Word ι) :
    embedding.map (P.sequentialWordEffect p w) = wordOperator (embedding.map ∘ p) w := by
  induction w with
  | nil => rw [UnitalJordanProduct.sequentialWordEffect, wordOperator_nil, embedding.unit]
  | cons a w ih =>
    rw [UnitalJordanProduct.sequentialWordEffect, embedding.map_quadratic, ih,
      wordOperator_cons (embedding.map ∘ p) (fun i => (embedding.hermitian (p i)).eq)]
    have hout : embedding.map (P.sequentialOutcome p a) =
        algebraicOutcome (embedding.map ∘ p) a := by
      rcases a with ⟨i, b⟩
      cases b <;> simp [UnitalJordanProduct.sequentialOutcome, algebraicOutcome, embedding.unit]
    rw [hout]

include embedding in
/-- An actual finite Hermitian embedding yields a projective representation
of every idempotent menu for each positive normalized initial functional. -/
theorem exists_projectiveRepresentation_of_embedding {n : ℕ}
    (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x, 0 ≤ f (P.product x x)) (hunit : f P.unit = 1) :
    ∃ M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)),
      M.HasDensityState ∧ ∀ w, M.probability w = f (P.sequentialWordEffect p w) := by
  obtain ⟨z, hz, _⟩ := embedding.exists_unique_positive_trace_representative f hf hunit
  obtain ⟨hpos, htr, heval⟩ := hz
  have hherm (i : Fin n) : (embedding.map (p i)).IsHermitian := embedding.hermitian _
  have hidem (i : Fin n) :
      embedding.map (p i) * embedding.map (p i) = embedding.map (p i) := by
    rw [← embedding.map_square, hp i]
  let M := matrixRepresentation (embedding.map ∘ p) hherm hidem (embedding.map z) hpos htr
  refine ⟨M, ?_, ?_⟩
  · refine ⟨MatchingModels.matToCLM (embedding.map z), matToCLM_isPositive hpos, ?_, ?_⟩
    · rw [trace_matToCLM, htr]
    · intro T
      exact matrixRepresentation_state _ hherm hidem _ hpos htr T
  · intro w
    rw [show M = matrixRepresentation (embedding.map ∘ p) hherm hidem
      (embedding.map z) hpos htr by rfl, matrixRepresentation_probability,
      ← embedding.map_sequentialWordEffect]
    exact heval _

end AlbertSequential.FaithfulHermitianJordanEmbedding

namespace AlbertSequential.UnitalJordanProduct

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)

/-- Ignoring an orthogonal ideal of zero state weight preserves the value
of every element. The vanishing uses positivity on the whole ideal. -/
theorem state_eq_on_projection_of_zero_complement_weight
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x, 0 ≤ f (P.product x x))
    (hzero : f (P.idealUnit Iᗮ) = 0) (x : E) :
    f (I.starProjection x) = f x := by
  let C := P.orthogonalIdealProduct hinner Iᗮ (P.isJordanIdeal_orthogonal hinner I hI)
  let fC := f.comp Iᗮ.subtype
  have hfr : C.FormallyReal :=
    C.formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner _ _)
  have hvan : fC = 0 := C.positiveFunctional_unit_zero hfr fC (fun y => hf y.val) hzero
  have hx := LinearMap.congr_fun hvan
    (⟨x - I.starProjection x, I.sub_starProjection_mem_orthogonal x⟩ : Iᗮ)
  change f (x - I.starProjection x) = 0 at hx
  rw [map_sub, sub_eq_zero] at hx
  exact hx.symm

/-- The all-word complex projective model after discarding an actual
orthogonal ideal of zero weight, when the surviving ideal has a finite
faithful Hermitian embedding. -/
theorem exists_projectiveRepresentation_of_zero_complement_weight {n d : ℕ}
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I)
    (embedding : FaithfulHermitianJordanEmbedding (P.orthogonalIdealProduct hinner I hI) d)
    (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x, 0 ≤ f (P.product x x))
    (hnorm : f P.unit = 1) (hzero : f (P.idealUnit Iᗮ) = 0) :
    ∃ M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)),
      M.HasDensityState ∧ ∀ w, M.probability w = f (P.sequentialWordEffect p w) := by
  let Q := P.orthogonalIdealProduct hinner I hI
  let projection := I.orthogonalProjectionOnto.toLinearMap
  let fI := f.comp I.subtype
  have hmap (x y : E) : projection (P.product x y) = Q.product (projection x) (projection y) :=
    P.idealProjection_product_subtype hinner I hI x y
  have hstate (x : E) : fI (projection x) = f x :=
    P.state_eq_on_projection_of_zero_complement_weight hinner I hI f hf hzero x
  have hide (i : Fin n) : Q.product (projection (p i)) (projection (p i)) = projection (p i) := by
    rw [← hmap, hp i]
  have hpositive (x : I) : 0 ≤ fI (Q.product x x) := hf x.val
  have hunit : fI Q.unit = 1 := (hstate P.unit).trans hnorm
  obtain ⟨M, hM, hw⟩ := embedding.exists_projectiveRepresentation_of_embedding
    (projection ∘ p) hide fI hpositive hunit
  refine ⟨M, hM, fun w => ?_⟩
  rw [hw, ← P.map_sequentialWordEffect Q projection rfl hmap p w, hstate]

end AlbertSequential.UnitalJordanProduct
