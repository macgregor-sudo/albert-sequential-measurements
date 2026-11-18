/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FiniteSpectralSupport

/-! The two support square roots are constructed in one actual eigenbasis.
Their commutation is proved, rather than assumed from independent choices. -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

theorem unitaryRealDiagonal_positive_iff (U : unitary (Matrix n n 𝕜)) (f : n → ℝ) :
    (unitaryRealDiagonal U f).PosSemidef ↔ ∀ i, 0 ≤ f i := by
  unfold unitaryRealDiagonal
  rw [Unitary.conjStarAlgAut_apply,
    Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe (U := U)),
    Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h i; exact_mod_cast h i
  · intro h i; exact_mod_cast h i

structure BinarySpectralSupport (A : Matrix n n 𝕜) where
  yes : FiniteSpectralSupport A
  no : FiniteSpectralSupport (1 - A)
  roots_commute : yes.root * no.root = no.root * yes.root

def binarySpectralSupport {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hAc : (1 - A).PosSemidef) : BinarySpectralSupport A := by
  let U := hA.isHermitian.eigenvectorUnitary
  let l := hA.isHermitian.eigenvalues
  have ha : unitaryRealDiagonal U l = A := hA.isHermitian.spectral_theorem.symm
  have hac : unitaryRealDiagonal U (fun i => 1 - l i) = 1 - A := by
    rw [← unitaryRealDiagonal_sub, unitaryRealDiagonal_one, ha]
  have hlc : ∀ i, 0 ≤ 1 - l i :=
    (unitaryRealDiagonal_positive_iff U _).mp (hac.symm ▸ hAc)
  refine ⟨finiteSpectralSupportOfRepresentation U l hA.eigenvalues_nonneg ha,
    finiteSpectralSupportOfRepresentation U (fun i => 1 - l i) hlc hac, ?_⟩
  change unitaryRealDiagonal U (fun i => Real.sqrt (l i)) *
      unitaryRealDiagonal U (fun i => Real.sqrt (1 - l i)) =
    unitaryRealDiagonal U (fun i => Real.sqrt (1 - l i)) *
      unitaryRealDiagonal U (fun i => Real.sqrt (l i))
  rw [unitaryRealDiagonal_mul, unitaryRealDiagonal_mul]
  congr 1
  funext i
  exact mul_comm _ _

theorem binarySpectralSupport_sum_squares {A : Matrix n n 𝕜}
    (s : BinarySpectralSupport A) : s.yes.root * s.yes.root + s.no.root * s.no.root = 1 := by
  rw [s.yes.root_sq, s.no.root_sq]
  abel

#print axioms binarySpectralSupport
end AlbertSequential
