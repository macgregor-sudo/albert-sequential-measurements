/- SPDX-License-Identifier: Apache-2.0 -/
module
public import EvaluatedSquareSoundness
public import SequentialEffectLifts
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Star.Unitary

@[expose] public section
noncomputable section
namespace AlbertSequential.ReflectionCertificate
open MonoidAlgebra
variable {ι A : Type*}

/-- Presentation of the free product of one group of order two per test. -/
def reflectionRelations (ι : Type*) : Set (FreeGroup ι) :=
  Set.range fun i : ι => FreeGroup.of i * FreeGroup.of i

abbrev ReflectionGroup (ι : Type*) := PresentedGroup (reflectionRelations ι)
abbrev CertificateRing (ι : Type*) := MonoidAlgebra ℝ (ReflectionGroup ι)

/-- The real group-algebra involution, extended from inversion of group elements. -/
def adjoint (F : CertificateRing ι) : CertificateRing ι :=
  F.coeff.sum fun g r => single g⁻¹ r

def outcome (a : Outcome ι) : CertificateRing ι :=
  let R := MonoidAlgebra.of ℝ (ReflectionGroup ι) (PresentedGroup.of a.1)
  let P := (1/2 : ℝ) • (1 + R)
  if a.2 then P else 1 - P

def wordEffect : Word ι → CertificateRing ι
  | [] => 1
  | a :: w => outcome a * wordEffect w * outcome a

section Model
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] (M : AlgebraicProjectiveData ι A)

def modelInvolution (i : ι) : unitary A :=
  ⟨projectionReflection M.projection i, by
    constructor <;> rw [projectionReflection_star _ M.selfAdjoint, projectionReflection_square _ M.idempotent]⟩

def groupEvaluation : ReflectionGroup ι →* unitary A :=
  PresentedGroup.toGroup (f := modelInvolution M) (by
    rintro _ ⟨i,rfl⟩
    apply Subtype.ext
    simp only [map_mul, FreeGroup.lift_apply_of, Submonoid.coe_mul, OneMemClass.coe_one,
      modelInvolution, projectionReflection_square _ M.idempotent])

def evaluation : CertificateRing ι →ₐ[ℝ] A :=
  MonoidAlgebra.lift ℝ A _ ((unitary A).subtype.comp (groupEvaluation M))

theorem evaluation_adjoint (F : CertificateRing ι) :
    evaluation M (adjoint F) = star (evaluation M F) := by
  classical
  conv_rhs => rw [← MonoidAlgebra.sum_coeff_single F]
  simp only [adjoint, Finsupp.sum, map_sum, evaluation, MonoidAlgebra.lift_single,
    MonoidHom.comp_apply, Submonoid.coe_subtype, map_inv, ← Unitary.star_eq_inv,
    Unitary.coe_star, star_sum, star_smul, star_trivial]

theorem evaluation_outcome (a : Outcome ι) :
    evaluation M (outcome a) = algebraicOutcome M.projection a := by
  obtain ⟨i,b⟩ := a
  have hr : evaluation M (MonoidAlgebra.of ℝ (ReflectionGroup ι) (PresentedGroup.of i)) =
      projectionReflection M.projection i := by
    simp [evaluation, groupEvaluation, modelInvolution]
  have hp : (1/2 : ℝ) • (1 + projectionReflection M.projection i) = M.projection i := by
    rw [projectionReflection, show (1 : A) + ((2 : ℝ) • M.projection i - 1) = (2 : ℝ) • M.projection i by abel, smul_smul]
    norm_num
  cases b <;> simp only [outcome, algebraicOutcome, Bool.false_eq_true, ↓reduceIte, map_sub, map_one, map_smul, map_add, hr, hp]

theorem evaluation_wordEffect (w : Word ι) :
    evaluation M (wordEffect w) = wordOperator M.projection w := by
  induction w with
  | nil => simp [wordEffect]
  | cons a w ih => rw [wordEffect, map_mul, map_mul, evaluation_outcome, ih, wordOperator_cons _ M.selfAdjoint]

/-- A certificate is an identity in the real group ring before evaluation in any model. -/
def SquareIdentity (terms : List (ℝ × Word ι)) (squares : List (ℚ × CertificateRing ι)) : Prop :=
  (terms.map (fun t => t.1 • wordEffect t.2)).sum =
    (squares.map (fun t => (t.1 : ℝ) • (adjoint t.2 * t.2))).sum

private theorem sound_for_functional (φ : A →ₗ[ℝ] ℝ) (hφ : ∀ T, 0 ≤ φ (star T * T))
    (terms : List (ℝ × Word ι)) (squares : List (ℚ × CertificateRing ι))
    (hw : ∀ t ∈ squares, 0 < t.1) (h : SquareIdentity terms squares) :
    0 ≤ (terms.map (fun t => t.1 * φ (wordOperator M.projection t.2))).sum := by
  have eq := congrArg (fun x => φ (evaluation M x)) h
  simp only [map_list_sum, List.map_map, Function.comp_def, map_smul, map_mul, evaluation_adjoint,
    evaluation_wordEffect, smul_eq_mul] at eq
  rw [eq]
  apply List.sum_nonneg
  intro r hr
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  exact mul_nonneg (by exact_mod_cast (hw t ht).le) (hφ _)

/-- Companion Lemma 2.3 for arbitrary real word coefficients, including an initial yes test. -/
theorem groupRing_squareIdentity_sound (terms : List (ℝ × Word ι))
    (squares : List (ℚ × CertificateRing ι)) (hw : ∀ t ∈ squares, 0 < t.1)
    (h : SquareIdentity terms squares) :
    0 ≤ (terms.map (fun t => t.1 * M.probability t.2)).sum ∧
    ∀ i, 0 ≤ (terms.map (fun t => t.1 * M.probability ((i,true)::t.2))).sum := by
  refine ⟨sound_for_functional M M.state M.state_positive terms squares hw h,?_⟩
  intro i
  let P := M.projection i
  let φ := M.state.comp ((LinearMap.mulRight ℝ P).comp (LinearMap.mulLeft ℝ P))
  have hp (T : A) : 0 ≤ φ (star T * T) := by
    change 0 ≤ M.state ((P*(star T*T))*P)
    simpa only [star_mul, P, M.selfAdjoint, mul_assoc] using M.state_positive (T*P)
  simpa only [AlgebraicProjectiveData.probability, wordOperator_cons _ M.selfAdjoint,
    algebraicOutcome, ↓reduceIte, φ, P, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply] using sound_for_functional M φ hp terms squares hw h

end Model
end AlbertSequential.ReflectionCertificate
