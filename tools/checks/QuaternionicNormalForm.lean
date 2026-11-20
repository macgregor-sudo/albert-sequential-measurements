module

import QuaternionicFourAtomNormalForm

open AlbertSequential

example (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hmem : ∀ i, p i ∈ standardQuaternionicWindow.subalgebra.carrier) :
    ∃ ψ : JordanSubalgebraIso standardQuaternionicWindow.subalgebra
      standardQuaternionicWindow.subalgebra,
      (∀ x, albertTrace (ψ.toLinearEquiv x).1 = albertTrace x.1) ∧
      ∃ X Y : Quaternion ℝ, ∃ D₀ : ℝ, 0 ≤ D₀ ∧
        (ψ.toLinearEquiv ⟨p 3, hmem 3⟩).1 =
          octDyad ![octonionScalar D₀, quatEmbed1 X, quatEmbed1 Y] := by
  obtain ⟨ψ, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, ht, _, _, _, _, hD₀, _, _, _, hform⟩ :=
    lemma_A_zero_quaternionic_normal_form p hp hmem
  exact ⟨ψ, ht, X, Y, D₀, hD₀, congrFun hform 3⟩

#print axioms exists_quatAuto_to_sparseFourConfigOct
#print axioms NativeAlbertAutomorphism.onStandardQuaternionicWindow_apply
#print axioms lemma_A_zero_quaternionic_normal_form
#print axioms lemma_A_zero_of_quat
