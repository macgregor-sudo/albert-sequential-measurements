/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CliffordDefectData

/-! Exact terminal scalar telescope. Symmetry of the pairing suffices; no
skew-adjointness, square relation, Clifford relation or positivity is assumed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
section ScalarTelescope
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
  (φ : A →ₗ[ℝ] ℝ) (hstar : ∀ x, φ (star x) = φ x)

include hstar in
theorem cliffordGramVector_square (N : Fin 3 → A) (ξ : A) (s : CliffordScalarParameters) :
    realStarPairing φ (cliffordGramVector N ξ s) (cliffordGramVector N ξ s) =
      realStarPairing φ (cliffordTripleVector N ξ) (cliffordTripleVector N ξ) +
        2 * (∑ i : Fin 3, s.q i * realStarPairing φ (cliffordTripleVector N ξ) (N i * ξ)) +
        ∑ i : Fin 3, ∑ j : Fin 3, s.q i * s.q j * realStarPairing φ (N i * ξ) (N j * ξ) := by
  simp only [Fin.sum_univ_three]
  simp only [CliffordScalarParameters.q, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [cliffordGramVector, realStarPairing_add_left, realStarPairing_add_right,
    realStarPairing_sub_left, realStarPairing_sub_right,
    realStarPairing_smul_left, realStarPairing_smul_right]
  rw [realStarPairing_symmetric φ hstar (N 0 * ξ) (cliffordTripleVector N ξ),
    realStarPairing_symmetric φ hstar (N 1 * ξ) (cliffordTripleVector N ξ),
    realStarPairing_symmetric φ hstar (N 2 * ξ) (cliffordTripleVector N ξ)]
  ring

include hstar in
theorem scalarCliffordDefect_telescope (N : Fin 3 → A) (ξ : A) (s : CliffordScalarParameters) :
    s.discriminant * realStarPairing φ ξ ξ =
      realStarPairing φ (cliffordDataError N ξ s) (cliffordVolume N * ξ + s.d0 • ξ) -
        realStarPairing φ (cliffordVolumeError N ξ s)
          (cliffordVolume N * ξ + cliffordGramVector N ξ s) -
        cliffordNormDefect φ N ξ s -
        2 * (∑ i : Fin 3, s.q i * cliffordCrossDefect φ N ξ s i) -
        ∑ i : Fin 3, ∑ j : Fin 3, s.q i * s.q j * cliffordGramDefect φ N ξ s i j := by
  rw [cliffordDataError, cliffordVolumeError, realStarPairing_sub_add φ hstar,
    realStarPairing_sub_add φ hstar, realStarPairing_smul_left, realStarPairing_smul_right,
    cliffordGramVector_square φ hstar]
  simp only [cliffordNormDefect, cliffordCrossDefect, cliffordGramDefect, Fin.sum_univ_three]
  simp only [CliffordScalarParameters.discriminant, CliffordScalarParameters.q,
    CliffordScalarParameters.expectedCross, CliffordScalarParameters.gramMatrix,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

end ScalarTelescope
end AlbertSequential
