module

import NativeTaggedNonprojectiveEffects
import ComplexWindowDeterminantAndMax
import SharpDilationSemantics
import ChoiCompletePositivity
import NativeReachableDensity

open scoped Matrix
open AlbertSequential AlbertSequential.NativeAnalysis

example : ∃ r : BinaryKrausRealization 69 (Fin 4), IsRealKrausRealization r ∧
    (∀ w, binaryKrausProbability r w =
      nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w) ∧
    (∀ j a, IsCompletelyPositiveMatrixMap (krausAction (r.kraus j a))) ∧
    (∀ j X, Matrix.trace (krausAction (r.kraus j true) X + krausAction (r.kraus j false) X) =
      Matrix.trace X) ∧
    ∃ j, let K := r.kraus j true
      let A := krausEffect K
      A * A ≠ A ∧ ¬ ∃ B : ComplexMatrix 69, B.IsHermitian ∧ B * B = A ∧
        ∀ X, krausAction K X = B * X * B := by
  have hg : GeneratesAlbert maximizerConfig :=
    (fourPointInvariant_pos_iff _ maximizerConfig_isAtom).mp (by
      rw [fourPointInvariant_maximizerConfig]; norm_num)
  obtain ⟨r, hr, hm, j, hj⟩ := exists_nativeGeneral_nonprojective_simulation
    maximizerConfig maximizerConfig_isAtom hg _ native_maximally_mixed_density
  refine ⟨r, hr, hm, fun k a => krausAction_completelyPositive (r.kraus k a), ?_, j, hj.1, ?_⟩
  · intro k X
    rw [Matrix.trace_add, trace_krausAction, trace_krausAction, ← Matrix.trace_add,
      ← Matrix.add_mul, r.normalized, Matrix.one_mul]
  · rintro ⟨B, _, hB, hact⟩
    exact hj.2 (by rw [hact 1, Matrix.mul_one, hB])

example (ρ : Albert) (hρ : IsDensity ρ) :
    let z := nativeGeneralScalarStates maximizerConfig ρ
    let hz := nativeGeneralScalarStates_density maximizerConfig maximizerConfig_isAtom ρ hρ
    let K := nativeTaggedKraus maximizerConfig maximizerConfig_isAtom z hz Option.some (3, true)
    let J : Matrix (Sigma (nativeTaggedBlock (S := Option (Fin 4)) (n := 4))) SpinorCoordinate ℝ :=
      taggedBlockInclusion (ι := nativeTaggedBlock) (Sum.inr 2)
    let A := rectangularKrausEffect K
    A * A ≠ A ∧ rectangularKrausAction K 1 ≠ A ∧
      (Jᴴ * A * J).charpoly = Polynomial.X ^ 8 * (Polynomial.X - Polynomial.C (2/3 : ℝ)) ^ 8 := by
  dsimp only
  have h : tracePairing (maximizerConfig 2) (maximizerConfig 3) = 1 / 3 :=
    (maximizerConfig_traces 1).1 2 3 (by decide)
  have h0 : 0 < tracePairing (maximizerConfig 2) (maximizerConfig 3) := by rw [h]; norm_num
  have h1 : tracePairing (maximizerConfig 2) (maximizerConfig 3) < 1 := by rw [h]; norm_num
  obtain ⟨hne, hp⟩ := nativeTaggedKraus_yes_effect_open_overlap maximizerConfig
    maximizerConfig_isAtom _ (nativeGeneralScalarStates_density _ maximizerConfig_isAtom ρ hρ)
    Option.some 2 3 h0 h1
  refine ⟨hne, nativeTaggedKraus_yes_action_one_ne_effect maximizerConfig maximizerConfig_isAtom _
    (nativeGeneralScalarStates_density _ maximizerConfig_isAtom ρ hρ) Option.some 2 3 h1, ?_⟩
  rw [h] at hp
  convert hp using 3; norm_num

#print axioms exists_atom_overlap_open_of_generates
#print axioms nativeTaggedKraus_yes_effect_corner
#print axioms nativeTaggedKraus_yes_effect_open_overlap
#print axioms nativeTaggedKraus_yes_action_one_ne_effect
#print axioms exists_nativeGeneral_nonprojective_simulation
