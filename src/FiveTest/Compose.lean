/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertModelSeparation
public import PentadArityAndHelly
public import ThreeAtomAndFourPoint

/-! # Two composing theorems

cor:fp:noideal and thm:pentad(b) follow from the all-history obstruction
`algebraicProjective_not_matches_generating_atoms` (with its Hilbert and right-quaternionic
forms) together with `fourPointInvariant_pos_iff` (thm:fourpoint) or `pentadF_generatesAlbert`.
No separation contract is used.  Lean scope is broader than printed: every Jordan state `ρ`
(the paper's cor:fp:noideal is stated from `e/3`). -/

set_option autoImplicit false

@[expose] public section

namespace AlbertSequential.FiveTest

/-- **cor:fp:noideal** (algebraic class (I) form): four atoms with `𝒜 > 0` have no sequential
projective representation reproducing all word probabilities, from any state. -/
theorem cor_fp_noideal_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : AlgebraicProjectiveData (Fin 4) A) (ρ : Albert) : ¬ M.Matches p ρ :=
  algebraicProjective_not_matches_generating_atoms M p hp
    ((fourPointInvariant_pos_iff p hp).1 hA) ρ

/-- **cor:fp:noideal**, real or complex Hilbert spaces. -/
theorem cor_fp_noideal {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : HilbertProjectiveData (Fin 4) 𝕜 H) (ρ : Albert) : ¬ M.Matches p ρ :=
  HilbertModelSeparation.hilbert_not_matches_generating_atoms M p hp ((fourPointInvariant_pos_iff p hp).1 hA) ρ

/-- **cor:fp:noideal**, right-quaternionic Hilbert spaces. -/
theorem cor_fp_noideal_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (S : RightQuaternionicHilbertStructure H)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : QuaternionicProjectiveData (Fin 4) S.toOperatorStructure) (ρ : Albert) :
    ¬ (∀ w, M.state (M.wordEffect w) = nativeWordProbability p ρ w) :=
  HilbertModelSeparation.rightQuaternionic_not_matches_generating_atoms S M p hp
    ((fourPointInvariant_pos_iff p hp).1 hA) ρ

/-- **thm:pentad(b)** (algebraic form), unconditionally: for no state do the five tests of `𝖥`
have a sequential projective representation. -/
theorem thm_pentad_b_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 5) A) (ρ : Albert) : ¬ M.Matches pentadF ρ :=
  algebraicProjective_not_matches_generating_atoms M pentadF pentadF_isAtom
    pentadF_generatesAlbert ρ

/-- **thm:pentad(b)**, real or complex Hilbert spaces, any dimension, ranks and state. -/
theorem thm_pentad_b {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 5) 𝕜 H) (ρ : Albert) : ¬ M.Matches pentadF ρ :=
  HilbertModelSeparation.hilbert_not_matches_generating_atoms M pentadF pentadF_isAtom pentadF_generatesAlbert ρ

/-- **thm:pentad(b)**, right-quaternionic Hilbert spaces. -/
theorem thm_pentad_b_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (S : RightQuaternionicHilbertStructure H)
    (M : QuaternionicProjectiveData (Fin 5) S.toOperatorStructure) (ρ : Albert) :
    ¬ (∀ w, M.state (M.wordEffect w) = nativeWordProbability pentadF ρ w) :=
  HilbertModelSeparation.rightQuaternionic_not_matches_generating_atoms S M pentadF pentadF_isAtom
    pentadF_generatesAlbert ρ

end AlbertSequential.FiveTest
