/- SPDX-License-Identifier: Apache-2.0 -/
module
public import MinimalSpectralDilation
public import MinimalSpectralFrameAssembly

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix
open scoped ComplexOrder

/-- The input corner and the two branch frames of a binary effect on precisely
the specified ancilla, whenever it can hold the defect eigenspace. -/
theorem exists_optimalSpectralFrames {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (hAc : (1 - A).PosSemidef) (hr : (A - A^2).rank ≤ Fintype.card m) :
    let s := binarySpectralSupport hA hAc
    let J : Matrix (n ⊕ m) n ℂ := fromRows 1 0
    ∃ P : Matrix (n ⊕ m) (n ⊕ m) ℂ,
      Pᴴ = P ∧ P*P = P ∧ Jᴴ*P*J = A ∧
      Nonempty (SharpDilationChannelFrame J P s.yes.root ×
        SharpDilationChannelFrame J (1-P) s.no.root) := by
  classical
  let U := hA.isHermitian.eigenvectorUnitary
  let a := hA.isHermitian.eigenvalues
  have hdiag : unitaryRealDiagonal U a = A := hA.isHermitian.spectral_theorem.symm
  have hcdiag : unitaryRealDiagonal U (fun i => 1 - a i) = 1 - A := by
    rw [← unitaryRealDiagonal_sub, unitaryRealDiagonal_one, hdiag]
  have hc : ∀ i, a i ≤ 1 := fun i => sub_nonneg.mp
    ((unitaryRealDiagonal_positive_iff U _).mp (hcdiag.symm ▸ hAc) i)
  rw [← hdiag, rank_spectralDefect] at hr
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hr
  obtain ⟨hV,hW,hVW,hVJ,hWJ,hJ⟩ := reducedSpectralFrame_data U a hA.eigenvalues_nonneg hc e
  have pair := pairedSharpDilationChannelFrame_of_partialFrames _ _ _ _ _ hV hW hVW hVJ hWJ hJ
  obtain ⟨hP,hPP,_,_⟩ := sharpDilationProjectors_of_partialFrame hV
  refine ⟨_, hP, hPP, ?_, ⟨pair⟩⟩
  have hleft := congrArg Matrix.conjTranspose hVJ
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, unitaryRealDiagonal_hermitian] at hleft
  rw [← Matrix.mul_assoc, hleft, Matrix.mul_assoc, hVJ, unitaryRealDiagonal_mul]
  exact (congrArg (unitaryRealDiagonal U) (funext fun i => Real.mul_self_sqrt (hA.eigenvalues_nonneg i))).trans hdiag

end AlbertSequential
