/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ComplexPositiveFactor

/-! Finite spectral square roots and support inverses, over both real and
complex scalars. Zero eigenvalues are retained and inverted as zero. -/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

def unitaryRealDiagonal (U : unitary (Matrix n n 𝕜)) (f : n → ℝ) : Matrix n n 𝕜 :=
  (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) U) (Matrix.diagonal (fun i => (f i : 𝕜)))

theorem unitaryRealDiagonal_mul (U : unitary (Matrix n n 𝕜)) (f g : n → ℝ) :
    unitaryRealDiagonal U f * unitaryRealDiagonal U g =
      unitaryRealDiagonal U (fun i => f i * g i) := by
  unfold unitaryRealDiagonal
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp

theorem unitaryRealDiagonal_sub (U : unitary (Matrix n n 𝕜)) (f g : n → ℝ) :
    unitaryRealDiagonal U f - unitaryRealDiagonal U g =
      unitaryRealDiagonal U (fun i => f i - g i) := by
  unfold unitaryRealDiagonal
  rw [← map_sub, Matrix.diagonal_sub]
  congr 1
  ext i
  simp

@[simp] theorem unitaryRealDiagonal_zero (U : unitary (Matrix n n 𝕜)) :
    unitaryRealDiagonal U (fun _ => 0) = 0 := by
  simp [unitaryRealDiagonal]

@[simp] theorem unitaryRealDiagonal_one (U : unitary (Matrix n n 𝕜)) :
    unitaryRealDiagonal U (fun _ => 1) = 1 := by
  simp [unitaryRealDiagonal]

theorem unitaryRealDiagonal_hermitian (U : unitary (Matrix n n 𝕜)) (f : n → ℝ) :
    (unitaryRealDiagonal U f).conjTranspose = unitaryRealDiagonal U f := by
  change star ((Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) U) _) = (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) U) _
  rw [← map_star]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · simp [hij, Ne.symm hij]

theorem unitaryRealDiagonal_positive (U : unitary (Matrix n n 𝕜))
    (f : n → ℝ) (hf : ∀ i, 0 ≤ f i) : (unitaryRealDiagonal U f).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => (f i : 𝕜))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (by intro i; exact_mod_cast hf i)
  simpa [unitaryRealDiagonal, Unitary.conjStarAlgAut_apply,
    Function.comp_def, Matrix.star_eq_conjTranspose] using
      hd.mul_mul_conjTranspose_same (U : Matrix n n 𝕜)

structure FiniteSpectralSupport (A : Matrix n n 𝕜) where
  root : Matrix n n 𝕜
  inverseRoot : Matrix n n 𝕜
  support : Matrix n n 𝕜
  root_positive : root.PosSemidef
  root_hermitian : root.conjTranspose = root
  inverse_hermitian : inverseRoot.conjTranspose = inverseRoot
  support_hermitian : support.conjTranspose = support
  root_sq : root * root = A
  inverse_root : inverseRoot * root = support
  root_inverse : root * inverseRoot = support
  inverse_effect : inverseRoot * A * inverseRoot = support
  support_sq : support * support = support
  effect_complement : A * (1 - support) = 0
  root_complement : root * (1 - support) = 0

/-- Construct support data in one supplied unitary diagonalization. This lets
complementary effects use the same basis in the doubled-space construction. -/
def finiteSpectralSupportOfRepresentation {A : Matrix n n 𝕜}
    (U : unitary (Matrix n n 𝕜)) (l : n → ℝ) (hl : ∀ i, 0 ≤ l i)
    (ha : unitaryRealDiagonal U l = A) :
    FiniteSpectralSupport A := by
  let s : n → ℝ := fun i => Real.sqrt (l i)
  let r : n → ℝ := fun i => (s i)⁻¹
  let p : n → ℝ := fun i => if s i = 0 then 0 else 1
  have hs (i : n) : s i * s i = l i := Real.mul_self_sqrt (hl i)
  have hrs (i : n) : r i * s i = p i := by
    by_cases hi : s i = 0
    · simp [r, p, hi]
    · simp [r, p, hi]
  have hsr (i : n) : s i * r i = p i := by rw [mul_comm]; exact hrs i
  have hrar (i : n) : r i * l i * r i = p i := by
    rw [← hs i]
    calc
      r i * (s i * s i) * r i = (r i * s i) * (s i * r i) := by ring
      _ = p i * p i := by rw [hrs, hsr]
      _ = p i := by simp only [p]; split_ifs <;> norm_num
  have hp (i : n) : p i * p i = p i := by simp only [p]; split_ifs <;> norm_num
  have hlp (i : n) : l i * (1 - p i) = 0 := by
    by_cases hi : s i = 0
    · have hl : l i = 0 := by rw [← hs i, hi]; simp
      simp [hl]
    · simp [p, hi]
  have hsp (i : n) : s i * (1 - p i) = 0 := by
    by_cases hi : s i = 0 <;> simp [p, hi]
  refine ⟨unitaryRealDiagonal U s, unitaryRealDiagonal U r, unitaryRealDiagonal U p,
    unitaryRealDiagonal_positive U s (fun i => Real.sqrt_nonneg _),
    unitaryRealDiagonal_hermitian U s, unitaryRealDiagonal_hermitian U r,
    unitaryRealDiagonal_hermitian U p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [unitaryRealDiagonal_mul]; simpa only [hs] using ha
  · rw [unitaryRealDiagonal_mul]; congr 1; exact funext hrs
  · rw [unitaryRealDiagonal_mul]; congr 1; exact funext hsr
  · rw [← ha, unitaryRealDiagonal_mul, unitaryRealDiagonal_mul]
    congr 1; exact funext hrar
  · rw [unitaryRealDiagonal_mul]; congr 1; exact funext hp
  · rw [← ha, ← unitaryRealDiagonal_one U, unitaryRealDiagonal_sub,
      unitaryRealDiagonal_mul]
    simp only [hlp, unitaryRealDiagonal_zero]
  · rw [← unitaryRealDiagonal_one U, unitaryRealDiagonal_sub, unitaryRealDiagonal_mul]
    simp only [hsp, unitaryRealDiagonal_zero]

/-- All support data are constructed from the actual finite Hermitian spectral
theorem. This is not a square-root or invertibility assumption. -/
def finiteSpectralSupport {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    FiniteSpectralSupport A :=
  finiteSpectralSupportOfRepresentation hA.isHermitian.eigenvectorUnitary
    hA.isHermitian.eigenvalues hA.eigenvalues_nonneg hA.isHermitian.spectral_theorem.symm

#print axioms finiteSpectralSupport
end AlbertSequential
