/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilitySpectralFlag
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Matrix.PEquiv

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.WindowProbability

open Set
open scoped Matrix

def referenceProjectorPolynomial {A : Type*} [Ring A] [Algebra ℂ A] (X : A) (i : Fin 3) : A :=
  ![(1 / 2 : ℂ) • ((X - 1) * (X - 2)), -((X - 1) * (X - 3)),
    (1 / 2 : ℂ) • ((X - 2) * (X - 3))] i

private theorem map_referenceProjectorPolynomial {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (X : A) (i : Fin 3) :
    f (referenceProjectorPolynomial X i) = referenceProjectorPolynomial (f X) i := by
  have h₂ : f (2 : A) = 2 := by simpa only [Nat.cast_ofNat] using map_natCast f 2
  have h₃ : f (3 : A) = 3 := by simpa only [Nat.cast_ofNat] using map_natCast f 3
  fin_cases i <;> simp [referenceProjectorPolynomial, h₂, h₃]

private theorem referenceProjectorPolynomial_diagonal (i : Fin 3) :
    referenceProjectorPolynomial (spectralDiagonal flagReferenceEigenvalues) i =
      Matrix.diagonal (fun j : Fin 3 => if i = j then (1 : ℂ) else 0) := by
  let f := Matrix.diagonalAlgHom (n := Fin 3) (α := ℂ) (R := ℂ)
  let x := fun j => (flagReferenceEigenvalues j : ℂ)
  change referenceProjectorPolynomial (f x) i = f _
  rw [← map_referenceProjectorPolynomial]
  apply congrArg f
  funext j
  fin_cases i <;> fin_cases j <;> norm_num [x, flagReferenceEigenvalues, referenceProjectorPolynomial,
    Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.one_apply, Pi.ofNat_apply, smul_eq_mul]

/-- Vary only the eigenvalues of the ordered flag, by evaluating the exact
three spectral projector polynomials of its reference matrix. -/
def spectralFlagEvaluate (c : Fin 3 → ℝ) (F : SpectralFlag) : ComplexMatrix3 :=
  ∑ i : Fin 3, (c i : ℂ) • referenceProjectorPolynomial F.val i

theorem spectralFlagEvaluate_unitary (c : Fin 3 → ℝ) (U : SpectralUnitary) :
    spectralFlagEvaluate c (spectralFlagOfUnitary U) = spectralConjugate U c := by
  let f := (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U).toAlgEquiv.toAlgHom
  change (∑ i : Fin 3, (c i : ℂ) • referenceProjectorPolynomial
    (f (spectralDiagonal flagReferenceEigenvalues)) i) = f (spectralDiagonal c)
  simp_rw [← map_referenceProjectorPolynomial f, ← map_smul, ← map_sum]
  apply congrArg f
  simp_rw [referenceProjectorPolynomial_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [spectralDiagonal, Matrix.smul_apply]
  · simp [spectralDiagonal, hij, Matrix.smul_apply]

theorem continuous_spectralFlagEvaluate :
    Continuous (fun p : (Fin 3 → ℝ) × SpectralFlag => spectralFlagEvaluate p.1 p.2) := by
  let Domain := (Fin 3 → ℝ) × SpectralFlag
  have hF : Continuous (fun p : Domain => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hsub (N : ComplexMatrix3) : Continuous (fun p : Domain => p.2.val - N) :=
    hF.sub continuous_const
  have hhalf : Continuous (fun _ : Domain => (1 / 2 : ℂ)) := continuous_const
  apply continuous_finsetSum _
  intro i _
  apply (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst)).smul
  fin_cases i
  · exact hhalf.smul ((hsub 1).matrix_mul (hsub 2))
  · exact ((hsub 1).matrix_mul (hsub 3)).neg
  · exact hhalf.smul ((hsub 2).matrix_mul (hsub 3))

theorem spectralFlagEvaluate_injective_of_strictAnti :
    InjOn (fun p : (Fin 3 → ℝ) × SpectralFlag => spectralFlagEvaluate p.1 p.2)
      {p | StrictAnti p.1} := by
  rintro ⟨c, F⟩ (hc : StrictAnti c) ⟨μ, G⟩ (hμ : StrictAnti μ) h
  obtain ⟨U, rfl⟩ := spectralFlagOfUnitary_surjective F
  obtain ⟨V, rfl⟩ := spectralFlagOfUnitary_surjective G
  change spectralFlagEvaluate c (spectralFlagOfUnitary U) = spectralFlagEvaluate μ (spectralFlagOfUnitary V) at h
  rw [spectralFlagEvaluate_unitary, spectralFlagEvaluate_unitary] at h
  obtain ⟨hSpectrum, hFlag⟩ := (spectralConjugate_eq_iff_of_strictAnti hc hμ U V).mp h
  exact Prod.ext hSpectrum (Subtype.ext hFlag)

theorem spectralFlagEvaluate_isHermitian (c : Fin 3 → ℝ) (F : SpectralFlag) :
    (spectralFlagEvaluate c F).IsHermitian := by
  obtain ⟨U, rfl⟩ := spectralFlagOfUnitary_surjective F
  rw [spectralFlagEvaluate_unitary]
  have h : (spectralDiagonal c).IsHermitian := Matrix.isHermitian_diagonal_iff.mpr (fun i => by
    simp [IsSelfAdjoint, Complex.conj_ofReal])
  have hs : IsSelfAdjoint (spectralDiagonal c) := h
  exact hs.map (Unitary.conjStarAlgAut ℂ ComplexMatrix3 U)

private theorem star_permutationMatrix (e : Fin 3 ≃ Fin 3) :
    star (e.toPEquiv.toMatrix : ComplexMatrix3) = e.symm.toPEquiv.toMatrix := by
  ext i j
  simp [Matrix.star_apply, PEquiv.toMatrix_apply, Equiv.eq_symm_apply, eq_comm]

private def spectralPermutationUnitary (e : Fin 3 ≃ Fin 3) : SpectralUnitary :=
  ⟨e.toPEquiv.toMatrix, Matrix.mem_unitaryGroup_iff'.mpr (by
    rw [star_permutationMatrix, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
      Equiv.symm_trans_self, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl])⟩

private theorem spectralConjugate_permutation (e : Fin 3 ≃ Fin 3) (c : Fin 3 → ℝ) :
    spectralConjugate (spectralPermutationUnitary e) c = spectralDiagonal (c ∘ e) := by
  change e.toPEquiv.toMatrix * spectralDiagonal c * star (e.toPEquiv.toMatrix : ComplexMatrix3) = _
  rw [star_permutationMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [spectralDiagonal, Matrix.submatrix_apply, Matrix.diagonal_apply, Function.comp_apply,
    e.injective.eq_iff]

/-- Every Hermitian matrix with simple spectrum has an evaluation pair
with descending eigenvalues and a flag in the fixed compact orbit. -/
theorem exists_spectralFlagEvaluate_of_simple (X : ComplexMatrix3) (hX : X.IsHermitian)
    (hsimple : Function.Injective hX.eigenvalues) :
    ∃ (c : Fin 3 → ℝ) (F : SpectralFlag), StrictAnti c ∧ spectralFlagEvaluate c F = X := by
  let U := hX.eigenvectorUnitary
  let ord : Fin 3 ≃ Fin (Fintype.card (Fin 3)) := finCongr (Fintype.card_fin 3).symm
  let given : Fin (Fintype.card (Fin 3)) ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
  let c := hX.eigenvalues₀ ∘ ord
  let e := given.symm.trans ord.symm
  have horder : StrictMono ord := fun _ _ h => h
  have hc : c ∘ e = hX.eigenvalues := by
    funext i
    change hX.eigenvalues₀ (ord (ord.symm (given.symm i))) = hX.eigenvalues₀ (given.symm i)
    rw [ord.apply_symm_apply]
  have hi : Function.Injective hX.eigenvalues₀ := by
    intro i j h
    have he : hX.eigenvalues (given i) = hX.eigenvalues (given j) := by
      change hX.eigenvalues₀ (given.symm (given i)) = hX.eigenvalues₀ (given.symm (given j))
      simpa only [Equiv.symm_apply_apply] using h
    exact given.injective (hsimple he)
  refine ⟨c, spectralFlagOfUnitary (U * spectralPermutationUnitary e),
    ((hX.eigenvalues₀_antitone).strictAnti_of_injective hi).comp_strictMono horder, ?_⟩
  rw [spectralFlagEvaluate_unitary, spectralConjugate_mul, spectralConjugate_permutation, hc]
  exact hX.spectral_theorem.symm

end AlbertSequential.WindowProbability
