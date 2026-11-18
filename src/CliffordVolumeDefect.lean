/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CliffordDefectData

/-! Exact volume reversal with its Clifford defects still present. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
section VolumeDefect
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

omit [StarRing A] [StarModule ℝ A] in
theorem cliffordVolumeError_expansion (N : Fin 3 → A) (ξ : A) (s : CliffordScalarParameters) :
    cliffordVolumeError N ξ s =
      -(1 / 2 : ℝ) • cliffordPairDefect N s 1 2 (N 0 * ξ) +
        (1 / 2 : ℝ) • (N 1 * cliffordPairDefect N s 0 2 ξ) -
        (1 / 2 : ℝ) • cliffordPairDefect N s 0 1 (N 2 * ξ) := by
  simp only [cliffordVolumeError, cliffordVolume, cliffordGramVector,
    cliffordTripleVector, cliffordPairDefect, CliffordScalarParameters.gramMatrix,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_add, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc,
    smul_add, smul_sub, smul_smul]
  module

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
theorem cliffordVolume_selfAdjoint (N : Fin 3 → A)
    (hN : ∀ i, star (N i) = -N i) : star (cliffordVolume N) = cliffordVolume N := by
  simp only [cliffordVolume, star_smul, star_trivial, star_sub, star_mul,
    hN, mul_neg, neg_mul, neg_neg, mul_assoc]
  congr 1
  abel

end VolumeDefect
end AlbertSequential
