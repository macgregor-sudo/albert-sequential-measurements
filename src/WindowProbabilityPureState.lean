/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGaussian

/-! The deterministic partial-trace identity for the companion's
complex induced states in the product basis. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory
open scoped Matrix BigOperators ComplexOrder

/-- Squared Hilbert-space norm of the complex matrix in the product basis. -/
def complexMatrixEnergy {k : ℕ} (Z : Matrix (Fin 3) (Fin k) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (Z i j)

theorem complexMatrixEnergy_nonneg {k : ℕ} (Z : Matrix (Fin 3) (Fin k) ℂ) :
    0 ≤ complexMatrixEnergy Z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem trace_complexGaussianGram_eq_energy {k : ℕ} (Z : Matrix (Fin 3) (Fin k) ℂ) :
    (Z * Z.conjTranspose).trace = (complexMatrixEnergy Z : ℂ) := by
  simp only [complexMatrixEnergy, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_sum]

/-- Unit-vector normalization in the canonical product basis of
`ℂ³ ⊗ ℂᵏ`. -/
def normalizedComplexPureVector (k : ℕ) (Z : Matrix (Fin 3) (Fin k) ℂ) :
    Fin 3 × Fin k → ℂ :=
  fun p => (((Real.sqrt (complexMatrixEnergy Z))⁻¹ : ℝ) : ℂ) * Z p.1 p.2

/-- The coefficient matrix of the partial trace of `|u⟩⟨u|` over the
second tensor factor, in the canonical product basis. -/
def partialTraceComplexPureVector (k : ℕ) (u : Fin 3 × Fin k → ℂ) : ComplexMatrix 3 :=
  fun i j => ∑ a, u (i, a) * star (u (j, a))

private theorem normalizedComplexPureVector_scale {k : ℕ} (Z : Matrix (Fin 3) (Fin k) ℂ) :
    ((Real.sqrt (complexMatrixEnergy Z))⁻¹)^2 = (complexMatrixEnergy Z)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (complexMatrixEnergy_nonneg Z)]

theorem normSq_normalizedComplexPureVector {k : ℕ} (Z : Matrix (Fin 3) (Fin k) ℂ) (hZ : Z ≠ 0) :
    ∑ p : Fin 3 × Fin k, Complex.normSq (normalizedComplexPureVector k Z p) = 1 := by
  have h : complexMatrixEnergy Z ≠ 0 := by
    intro he
    apply hZ
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    rw [trace_complexGaussianGram_eq_energy, he, Complex.ofReal_zero]
  rw [Fintype.sum_prod_type]
  simp only [normalizedComplexPureVector, Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum]
  change ((Real.sqrt (complexMatrixEnergy Z))⁻¹ * (Real.sqrt (complexMatrixEnergy Z))⁻¹) *
    complexMatrixEnergy Z = 1
  rw [← pow_two, normalizedComplexPureVector_scale]
  exact inv_mul_cancel₀ h

/-- The normalized Gram matrix is exactly the partial trace of the
normalized pure vector. The equality also holds at the totalized zero input. -/
theorem partialTrace_normalizedComplexPureVector {k : ℕ} (Z : Matrix (Fin 3) (Fin k) ℂ) :
    partialTraceComplexPureVector k (normalizedComplexPureVector k Z) = normalizedComplexGram k Z := by
  let c : ℝ := (Real.sqrt (complexMatrixEnergy Z))⁻¹
  have hc : (c : ℂ) * (c : ℂ) = ((complexMatrixEnergy Z : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← pow_two, normalizedComplexPureVector_scale Z]
  ext i j
  change (∑ a, ((c : ℂ) * Z i a) * star ((c : ℂ) * Z j a)) =
    (Matrix.trace (Z * Z.conjTranspose))⁻¹ * (Z * Z.conjTranspose) i j
  rw [trace_complexGaussianGram_eq_energy, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [star_mul, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← hc]
  ring

/-- Normalizing the complex Gaussian matrix gives a unit pure vector
almost surely, with the same tensor product convention throughout. -/
theorem ae_normSq_normalizedComplexPureVector (k : ℕ) (hk : 0 < k) :
    ∀ᵐ Z ∂standardComplexGaussianMatrix k,
      ∑ p : Fin 3 × Fin k, Complex.normSq (normalizedComplexPureVector k Z p) = 1 := by
  filter_upwards [ae_gaussianMatrix_ne_zero k hk] with Z hZ
  exact normSq_normalizedComplexPureVector Z hZ

end AlbertSequential.WindowProbability
