/- SPDX-License-Identifier: Apache-2.0 -/
module
public import InstrumentFactorization
public import LinearMapChoi

/-! The finite factorization for an arbitrary ordinary completely positive
complex-linear map, without requiring Kraus data as input. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential

/-- With the established input-first Choi convention, this transpose is the
usual effect Phi*(I). Kraus binding identifies it with sum K* K. -/
def matrixMapEffect {d : ℕ} (Phi : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d) :
    ComplexMatrix d := (choiOutputTrace (linearMapChoi Phi)).transpose

theorem exists_completelyPositive_channel_factorization {d : ℕ}
    (Phi : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d)
    (hPhi : IsCompletelyPositiveMatrixMap Phi) {τ : ComplexMatrix d}
    (hτ : IsMatrixDensity τ) :
    ∃ S : ComplexMatrix d, ∃ F : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d,
      S.PosSemidef ∧ S * S = matrixMapEffect Phi ∧
      IsCompletelyPositiveMatrixMap F ∧
      (∀ Y, Matrix.trace (F Y) = Matrix.trace Y) ∧
      ∀ X, Phi X = F (S * X * S) := by
  obtain ⟨K, hK⟩ := (choi_positive_iff_kraus (linearMapChoi Phi)).mp
    ((linearMapChoi_positive_iff Phi).mpr hPhi)
  obtain ⟨S, L, hS, hSS, hL, hfactor⟩ := exists_kraus_channel_factorization K hτ
  let F := choiLinearMap (krausChoi L)
  have hFx (Y : ComplexMatrix d) : F Y = krausAction L Y := krausChoi_action L Y
  have hPhix (Y : ComplexMatrix d) : Phi Y = krausAction K Y :=
    (choiAction_linearMapChoi Phi Y).symm.trans (hK Y)
  have he : matrixMapEffect Phi = krausEffect K := by
    unfold matrixMapEffect
    rw [choi_kraus_effect_binding (linearMapChoi Phi) K hK, Matrix.transpose_transpose]
  refine ⟨S, F, hS, he.symm ▸ hSS, ?_, ?_, ?_⟩
  · exact (choi_positive_iff_completelyPositive (krausChoi L)).mp (krausChoi_positive L)
  · exact (choi_trace_preservation_iff (krausChoi L)).mp (by
      rw [krausChoi_outputTrace, hL, Matrix.transpose_one])
  · intro X
    rw [hPhix, hFx, hfactor]

#print axioms exists_completelyPositive_channel_factorization
end AlbertSequential
