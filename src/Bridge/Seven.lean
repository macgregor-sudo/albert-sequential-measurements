/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.Models
public import Uniform.Main

/-!
# Seven steps exclude every representation (Challenge terms)

It rests on `Uniform.Main`
(`AlbertSequential.LengthSeven.Uniform.uniform_lengthSeven_e3_algebraic`,
`uniform_lengthSix_pA_algebraic`). Each Challenge model class is turned into the development's algebraic comparator by
`Bridge.Models`; generation gives `𝒜 > 0` by the four-point criterion.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge

universe v

theorem seven_of_algebraic {A : Type*} {_ : Ring A} {_ : StarRing A} {_ : Module ℝ A}
    {_ : IsScalarTower ℝ A A} {_ : SMulCommClass ℝ A A} {_ : StarModule ℝ A}
    (M : AlbertSequential.AlgebraicProjectiveData (Fin 4) A) (g : Word 4 → ℝ)
    (hM : ∀ w, M.probability w = g w) (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) :
    ¬ ∀ w ∈ yesFirstUpTo 7, g w = wordProbability p maximallyMixed w := by
  intro h
  apply AlbertSequential.LengthSeven.Uniform.uniform_lengthSeven_e3_algebraic (fun i => toT (p i))
    (atoms_toT hp) (fourPointInvariant_pos_of_generates hp hg) M
  intro w hw h0
  have hmem : w ∈ yesFirstUpTo 7 := by unfold yesFirstUpTo; exact ⟨hw, h0⟩
  rw [hM w, h w hmem, maximallyMixed_toT, wordProbability_toT]

theorem six_of_algebraic {A : Type*} {_ : Ring A} {_ : StarRing A} {_ : Module ℝ A}
    {_ : IsScalarTower ℝ A A} {_ : SMulCommClass ℝ A A} {_ : StarModule ℝ A}
    (M : AlbertSequential.AlgebraicProjectiveData (Fin 4) A) (g : Word 4 → ℝ)
    (hM : ∀ w, M.probability w = g w) (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) :
    ¬ ∀ w ∈ wordsUpTo 4 6, g w = wordProbability p (p 0) w := by
  intro h
  apply AlbertSequential.LengthSeven.Uniform.uniform_lengthSix_pA_algebraic (fun i => toT (p i))
    (atoms_toT hp) (fourPointInvariant_pos_of_generates hp hg) M
  intro u hu
  have hmem : u ∈ wordsUpTo 4 6 := by unfold wordsUpTo; exact hu
  rw [hM u, h u hmem]
  exact (wordProbability_toT p (p 0) u).symm

theorem seven_steps_bridge (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hg : Generates p) :
    NoRepresentationOn.{v} p maximallyMixed (yesFirstUpTo 7) ∧
      NoRepresentationOn.{v} p (p 0) (wordsUpTo 4 6) := by
  refine ⟨⟨fun 𝕜 H _ _ _ _ M => ?_, fun H _ _ _ S M => ?_, fun A _ _ _ _ M => ?_⟩,
    ⟨fun 𝕜 H _ _ _ _ M => ?_, fun H _ _ _ S M => ?_, fun A _ _ _ _ M => ?_⟩⟩
  · exact seven_of_algebraic (ofProjectiveRepresentation M) _
      (ofProjectiveRepresentation_probability M) p hp hg
  · exact seven_of_algebraic (ofQuaternionicRepresentation M) _
      (ofQuaternionicRepresentation_probability M) p hp hg
  · exact seven_of_algebraic (ofAlgebraicModel M) _ (ofAlgebraicModel_probability M) p hp hg
  · exact six_of_algebraic (ofProjectiveRepresentation M) _
      (ofProjectiveRepresentation_probability M) p hp hg
  · exact six_of_algebraic (ofQuaternionicRepresentation M) _
      (ofQuaternionicRepresentation_probability M) p hp hg
  · exact six_of_algebraic (ofAlgebraicModel M) _ (ofAlgebraicModel_probability M) p hp hg

end AlbertChallenge.Bridge
