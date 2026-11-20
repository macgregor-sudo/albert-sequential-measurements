/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.HigherJetHermitian
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The dimensions of the precise common kernels of the two higher jets. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF
open HigherJetCoefficients

private def realAssociatorCoordinates : realAssociatorSpace ≃ₗ[ℝ] (Fin 3 → ℝ) × Quaternion ℝ where
  toFun x := (![x.val.1.imI, x.val.1.imJ, x.val.1.imK], x.val.2)
  invFun v := ⟨(⟨0, v.1 0, v.1 1, v.1 2⟩, v.2), rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Quaternion.ext
      · exact x.property.symm
      · rfl
      · rfl
      · rfl
    · rfl
  right_inv v := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  map_add' x y := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl

private def quaternionicAssociatorCoordinates : quaternionicAssociatorSpace ≃ₗ[ℝ] Quaternion ℝ where
  toFun x := x.val.2
  invFun q := ⟨(0, q), rfl⟩
  left_inv x := Subtype.ext (Prod.ext x.property.symm rfl)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realAssociatorSpace_finrank : Module.finrank ℝ realAssociatorSpace = 7 := by
  rw [realAssociatorCoordinates.finrank_eq]
  norm_num [Module.finrank_prod, Module.finrank_pi_fintype, Quaternion.finrank_eq_four]

theorem quaternionicAssociatorSpace_finrank : Module.finrank ℝ quaternionicAssociatorSpace = 4 :=
  quaternionicAssociatorCoordinates.finrank_eq.trans Quaternion.finrank_eq_four

theorem HigherJetCoefficients.leadingIdeal_finrank (b : HigherJetBase) :
    Module.finrank ℝ (leadingIdeal b) = match b with | .real => 7 | .quaternionic => 4 := by
  rw [leadingIdeal, ← (Submodule.equivMapOfInjective (leadingMonomial b)
    (leadingMonomial_injective b) b.leadingSpace).finrank_eq]
  cases b
  · exact realAssociatorSpace_finrank
  · exact quaternionicAssociatorSpace_finrank

/-- The actual entrywise kernel inside the Hermitian thickening. -/
def higherJetHermitianKernel (b : HigherJetBase) : Submodule ℝ (HigherJetHermitian b b.threshold) where
  carrier := {M | ∀ i j, M.val i j ∈ leadingIdeal b}
  zero_mem' := fun _ _ => (leadingIdeal b).zero_mem
  add_mem' hM hN i j := (leadingIdeal b).add_mem (hM i j) (hN i j)
  smul_mem' r _ hM i j := (leadingIdeal b).smul_mem r (hM i j)

private def kernelOfUpperEntries (b : HigherJetBase)
    (v : leadingIdeal b × leadingIdeal b × leadingIdeal b) : higherJetHermitianKernel b := by
  let s := conjugate b b.threshold
  let M : CoefficientMatrix (HigherJetCoefficients b b.threshold) :=
    !![0, v.1, v.2.1; s v.1, 0, v.2.2; s v.2.1, s v.2.2, 0]
  have hs (x : HigherJetCoefficients b b.threshold) : s (s x) = x := conjugate_involutive b b.threshold x
  refine ⟨⟨M, ?_⟩, ?_⟩
  · intro i j
    change s (M j i) = M i j
    fin_cases i <;> fin_cases j <;> simp [M, hs]
  · intro i j
    change M i j ∈ leadingIdeal b
    fin_cases i <;> fin_cases j <;> simp [M]
    all_goals exact leadingIdeal_conj b _ (Subtype.property _)

private def higherJetKernelUpperEquiv (b : HigherJetBase) :
    higherJetHermitianKernel b ≃ₗ[ℝ] leadingIdeal b × leadingIdeal b × leadingIdeal b where
  toFun M := (⟨M.val.val 0 1, M.property 0 1⟩, ⟨M.val.val 0 2, M.property 0 2⟩,
    ⟨M.val.val 1 2, M.property 1 2⟩)
  invFun := kernelOfUpperEntries b
  left_inv M := by
    have hdiag (i : Fin 3) : M.val.val i i = 0 :=
      leadingIdeal_fixed_eq_zero b _ (M.property i i) (M.val.property i i)
    have hsym (i j : Fin 3) : conjugate b b.threshold (M.val.val j i) = M.val.val i j :=
      M.val.property i j
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kernelOfUpperEntries, hdiag, hsym]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exactly three independent off-diagonal entries remain in the common kernel. -/
theorem higherJetHermitianKernel_finrank (b : HigherJetBase) :
    Module.finrank ℝ (higherJetHermitianKernel b) =
      match b with | .real => 21 | .quaternionic => 12 := by
  rw [(higherJetKernelUpperEquiv b).finrank_eq]
  have e (b : HigherJetBase) : leadingIdeal b ≃ₗ[ℝ] b.leadingSpace :=
    (Submodule.equivMapOfInjective (leadingMonomial b) (leadingMonomial_injective b) b.leadingSpace).symm
  cases b
  · let R := (e .real).trans realAssociatorCoordinates
    rw [(R.prodCongr (R.prodCongr R)).finrank_eq]
    norm_num [Module.finrank_prod, Module.finrank_pi_fintype, Quaternion.finrank_eq_four]
  · let H := (e .quaternionic).trans quaternionicAssociatorCoordinates
    rw [(H.prodCongr (H.prodCongr H)).finrank_eq]
    norm_num [Module.finrank_prod, Quaternion.finrank_eq_four]

end AlbertSequential.AppF
