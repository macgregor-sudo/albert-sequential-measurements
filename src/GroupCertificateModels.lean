/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectionGroupCertificate
public import BoundedWordEffects
public import QuaternionicProjectiveData

@[expose] public section
namespace AlbertSequential.ReflectionCertificate
variable {ι : Type*}

/-- The unprefixed and prefixed soundness conclusions for a word probability function. -/
def SoundOnTable (terms : List (ℝ × Word ι)) (prob : Word ι → ℝ) : Prop :=
  0 ≤ (terms.map (fun t => t.1 * prob t.2)).sum ∧
    ∀ i, 0 ≤ (terms.map (fun t => t.1 * prob ((i,true)::t.2))).sum

theorem sound_on_algebraic_model {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData ι A) (terms : List (ℝ × Word ι))
    (squares : List (ℚ × CertificateRing ι)) (hw : ∀ t ∈ squares, 0 < t.1)
    (h : SquareIdentity terms squares) : SoundOnTable terms M.probability := by
  let : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm
  exact groupRing_squareIdentity_sound M terms squares hw h

theorem sound_on_hilbert_model {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData ι 𝕜 H)
    (terms : List (ℝ × Word ι)) (squares : List (ℚ × CertificateRing ι))
    (hw : ∀ t ∈ squares, 0 < t.1) (h : SquareIdentity terms squares) :
    SoundOnTable terms M.probability := by
  exact (congrArg (SoundOnTable terms) (funext M.toAlgebraic_probability)).mp
    (sound_on_algebraic_model M.toAlgebraic terms squares hw h)

theorem sound_on_quaternionic_model {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData ι Q)
    (terms : List (ℝ × Word ι)) (squares : List (ℚ × CertificateRing ι))
    (hw : ∀ t ∈ squares, 0 < t.1) (h : SquareIdentity terms squares) :
    SoundOnTable terms (fun w => M.state (M.wordEffect w)) := by
  exact (congrArg (SoundOnTable terms) (funext M.toAlgebraic_probability)).mp
    (sound_on_algebraic_model M.toAlgebraic terms squares hw h)

end AlbertSequential.ReflectionCertificate
