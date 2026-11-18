/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Uniform.Main
public import HilbertModelSeparation
public import AlgebraicProjectiveNoGo
public import PentadArityAndHelly

/-! # Composing corollaries: cor:fp:noideal and thm:pentad (b)

Both are a few lines from earlier results (the all-history reconstruction and the
obstruction `algebraicProjective_not_matches_generating_atoms`, its Hilbert/quaternionic
forms, `fourPointInvariant_pos_iff`, `pentadF_isAtom`, `pentadF_generatesAlbert`); no
separation contract is assumed. `cor:fp:noideal` is also recovered from the native
length-seven chain (`noideal_of_uniform_*`), which is a different route to the same statement.
-/

@[expose] public section

namespace AlbertSequential.LengthSeven.Uniform

open AlbertSequential AlbertSequential.LengthSeven

/- Lean 4.36 / Mathlib v4.36.0: `Real.lt` is no longer an `irreducible_def`; in this non-module file
defeq checks of `0 < fourPointInvariant p` would evaluate the invariant. No proof here needs its body. -/
attribute [local irreducible] fourPointInvariant

/-! ## cor:fp:noideal (four atoms, `𝒜 > 0`, state `e/3`; in fact any native initial element) -/

section NoIdeal

variable (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
include hp hA

theorem noideal_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData Letter A) (ρ : Albert) : ¬ M.Matches p ρ :=
  algebraicProjective_not_matches_generating_atoms M p hp ((fourPointInvariant_pos_iff p hp).1 hA) ρ

theorem noideal_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData Letter 𝕜 H) (ρ : Albert) : ¬ M.Matches p ρ :=
  HilbertModelSeparation.hilbert_not_matches_generating_atoms M p hp
    ((fourPointInvariant_pos_iff p hp).1 hA) ρ

theorem noideal_rightQuaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (S : RightQuaternionicHilbertStructure H)
    (M : QuaternionicProjectiveData Letter S.toOperatorStructure) (ρ : Albert) :
    ¬ (∀ w, M.state (M.wordEffect w) = nativeWordProbability p ρ w) :=
  HilbertModelSeparation.rightQuaternionic_not_matches_generating_atoms S M p hp
    ((fourPointInvariant_pos_iff p hp).1 hA) ρ

/-- cor:fp:noideal at `e/3` from the native length-seven chain (without `algebraicProjective_not_matches_generating_atoms`). -/
theorem noideal_of_uniform_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData Letter A) : ¬ M.Matches p ((1 / 3 : ℝ) • albertUnit) :=
  fun hm => uniform_lengthSeven_e3_algebraic p hp hA M fun w _ _ => hm w

theorem noideal_of_uniform_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData Letter 𝕜 H) : ¬ M.Matches p ((1 / 3 : ℝ) • albertUnit) :=
  fun hm => uniform_lengthSeven_e3_hilbert p hp hA M fun w _ _ => hm w

theorem noideal_of_uniform_quaternionic {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData Letter Q) :
    ¬ (∀ w, M.state (M.wordEffect w) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :=
  fun hm => uniform_lengthSeven_e3_quaternionic p hp hA M fun w _ _ => hm w

end NoIdeal

/-! ## thm:pentad (b): the five tests `F` have no sequential projective representation,
for any native initial element (in particular any state of `𝕁`) -/

theorem pentad_b_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 5) A) (ρ : Albert) : ¬ M.Matches pentadF ρ :=
  algebraicProjective_not_matches_generating_atoms M pentadF pentadF_isAtom
    pentadF_generatesAlbert ρ

theorem pentad_b_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 5) 𝕜 H) (ρ : Albert) : ¬ M.Matches pentadF ρ :=
  HilbertModelSeparation.hilbert_not_matches_generating_atoms M pentadF pentadF_isAtom
    pentadF_generatesAlbert ρ

theorem pentad_b_rightQuaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (S : RightQuaternionicHilbertStructure H)
    (M : QuaternionicProjectiveData (Fin 5) S.toOperatorStructure) (ρ : Albert) :
    ¬ (∀ w, M.state (M.wordEffect w) = nativeWordProbability pentadF ρ w) :=
  HilbertModelSeparation.rightQuaternionic_not_matches_generating_atoms S M pentadF
    pentadF_isAtom pentadF_generatesAlbert ρ

end AlbertSequential.LengthSeven.Uniform
