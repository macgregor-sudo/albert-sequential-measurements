/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicHilbertCompletion

/-! Exact chronological vectors, orthogonal projection generators and dense
cyclic span for the full real cyclic representation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
section
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

def cyclicGenerator (M : AlgebraicProjectiveData ι A) (i : ι) : CyclicWordAlgebra M :=
  cyclicWordElement M [(i,true)]

@[simp] theorem cyclicGenerator_value (M : AlgebraicProjectiveData ι A) (i : ι) :
    (cyclicGenerator M i : A)=M.projection i := by
  simp [cyclicGenerator,cyclicWordElement,wordAmplitude_singleton,algebraicOutcome]

theorem cyclicGenerator_isStarProjection (M : AlgebraicProjectiveData ι A) (i : ι) :
    IsStarProjection (cyclicGenerator M i) := by
  constructor
  · apply Subtype.ext
    change (cyclicGenerator M i : A)*(cyclicGenerator M i : A)=(cyclicGenerator M i : A)
    rw [cyclicGenerator_value,M.idempotent]
  · apply Subtype.ext
    change star (cyclicGenerator M i : A)=(cyclicGenerator M i : A)
    rw [cyclicGenerator_value,M.selfAdjoint]

def cyclicHilbertProjection (M : AlgebraicProjectiveData ι A) (i : ι) :
    CyclicHilbert M →L[ℝ] CyclicHilbert M := cyclicHilbertRepresentation M (cyclicGenerator M i)

theorem cyclicHilbertProjection_isStarProjection (M : AlgebraicProjectiveData ι A) (i : ι) :
    IsStarProjection (cyclicHilbertProjection M i) :=
  (cyclicGenerator_isStarProjection M i).map (cyclicHilbertRepresentation M)

theorem cyclicWordElement_nil (M : AlgebraicProjectiveData ι A) : cyclicWordElement M []=1 := by
  apply Subtype.ext
  exact wordAmplitude_nil M.projection

theorem cyclicWordElement_cons (M : AlgebraicProjectiveData ι A) (a : Outcome ι) (w : Word ι) :
    cyclicWordElement M (a::w)=cyclicWordElement M w*cyclicWordElement M [a] := by
  apply Subtype.ext
  change wordAmplitude M.projection (a::w)=wordAmplitude M.projection w*wordAmplitude M.projection [a]
  rw [wordAmplitude_singleton]
  exact wordAmplitude_cons M.projection a w

theorem cyclicHilbertRepresentation_outcome (M : AlgebraicProjectiveData ι A) (a : Outcome ι) :
    cyclicHilbertRepresentation M (cyclicWordElement M [a])=
      algebraicOutcome (cyclicHilbertProjection M) a := by
  rcases a with ⟨i,b⟩
  cases b with
  | true => rfl
  | false =>
    have he : cyclicWordElement M [(i,false)]=1-cyclicGenerator M i := by
      apply Subtype.ext
      simp [cyclicWordElement,wordAmplitude_singleton,algebraicOutcome,cyclicGenerator_value]
    rw [he,map_sub,map_one]
    rfl

theorem cyclicHilbertRepresentation_word (M : AlgebraicProjectiveData ι A) (w : Word ι) :
    cyclicHilbertRepresentation M (cyclicWordElement M w)=
      wordAmplitude (cyclicHilbertProjection M) w := by
  induction w with
  | nil => rw [cyclicWordElement_nil,map_one,wordAmplitude_nil]
  | cons a w ih =>
    rw [cyclicWordElement_cons,map_mul,ih,cyclicHilbertRepresentation_outcome,wordAmplitude_cons]

theorem cyclicHilbertAction_vector (M : AlgebraicProjectiveData ι A) (z : CyclicWordAlgebra M) :
    cyclicHilbertRepresentation M z (cyclicHilbertVector M)=
      (cyclicPreHilbertMk M (cyclicWordAlgebraEquiv M z) : CyclicHilbert M) := by
  change cyclicHilbertAction M z (cyclicPreHilbertMk M 1 : CyclicHilbert M)=_
  rw [cyclicHilbertAction_coe,cyclicPreRepresentation_mk,mul_one]

/-- The original star-symmetric state is the actual vector state on the
ENTIRE word algebra, not merely on individual word effects. -/
theorem cyclicHilbert_vector_state (M : AlgebraicProjectiveData ι A)
    (z : CyclicWordAlgebra M) :
    inner ℝ (cyclicHilbertVector M)
      (cyclicHilbertRepresentation M z (cyclicHilbertVector M))=M.state (z : A) := by
  rw [cyclicHilbertAction_vector]
  change inner ℝ (cyclicPreHilbertMk M 1 : CyclicHilbert M)
    (cyclicPreHilbertMk M (cyclicWordAlgebraEquiv M z) : CyclicHilbert M)=_
  rw [UniformSpace.Completion.inner_coe,cyclicPreHilbert_inner_mk]
  simp only [OneMemClass.coe_one,star_one,one_mul]
  rfl

theorem cyclicHilbert_word_probability (M : AlgebraicProjectiveData ι A) (w : Word ι) :
    ‖wordAmplitude (cyclicHilbertProjection M) w (cyclicHilbertVector M)‖^2=M.probability w := by
  rw [←cyclicHilbertRepresentation_word,cyclicHilbertAction_vector,
    UniformSpace.Completion.norm_coe,cyclicPreHilbert_norm_sq]
  rfl

def cyclicOrbitLinear (M : AlgebraicProjectiveData ι A) :
    CyclicWordAlgebra M →ₗ[ℝ] CyclicHilbert M where
  toFun z := cyclicHilbertRepresentation M z (cyclicHilbertVector M)
  map_add' z w := congrArg (fun T : CyclicHilbert M →L[ℝ] CyclicHilbert M => T (cyclicHilbertVector M))
    (cyclicHilbertAction_add M z w)
  map_smul' r z := congrArg (fun T : CyclicHilbert M →L[ℝ] CyclicHilbert M => T (cyclicHilbertVector M))
    (cyclicHilbertAction_smul M r z)

theorem cyclicHilbert_cyclic (M : AlgebraicProjectiveData ι A) :
    Dense (Submodule.span ℝ (Set.range (fun w : Word ι =>
      wordAmplitude (cyclicHilbertProjection M) w (cyclicHilbertVector M))) : Set (CyclicHilbert M)) := by
  let S := Submodule.span ℝ (Set.range (fun w : Word ι =>
    wordAmplitude (cyclicHilbertProjection M) w (cyclicHilbertVector M)))
  have hs : Submodule.span ℝ (Set.range (cyclicWordElement M)) ≤ S.comap (cyclicOrbitLinear M) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    change cyclicHilbertRepresentation M (cyclicWordElement M w) (cyclicHilbertVector M) ∈ S
    rw [cyclicHilbertRepresentation_word]
    exact Submodule.subset_span ⟨w,rfl⟩
  rw [cyclicWordAlgebra_span_words] at hs
  apply (UniformSpace.Completion.denseRange_coe (α := CyclicPreHilbert M)).mono
  rintro _ ⟨q,rfl⟩
  obtain ⟨x,rfl⟩ := cyclicPreHilbertMk_surjective M q
  let z := (cyclicWordAlgebraEquiv M).symm x
  have hz : cyclicOrbitLinear M z ∈ S := hs (Submodule.mem_top)
  change cyclicHilbertRepresentation M z (cyclicHilbertVector M) ∈ S at hz
  rw [cyclicHilbertAction_vector] at hz
  change (cyclicPreHilbertMk M x : CyclicHilbert M) ∈ S
  simpa only [z,AlgEquiv.apply_symm_apply] using hz

end
end AlbertSequential
