module

import OctonionicHolonomyAssociative
import OppositeCliffordIrreducible

open AlbertSequential AlbertSequential.MatchingModels

noncomputable section

set_option maxHeartbeats 500000 in
example (q : Fin 4 → Albert) (hq : ∀ i, IsAtom (q i))
    (ho : ∀ i j : Fin 4, i ≠ j → 0 < fpOverlap q i j) :
    ∃ h : Fin 3 → Octonion,
      OctonionicHolonomyData q h ∧
      Dtet (fpOverlap q) (fpTriangle q) (tVec q) =
        (1 / 4 : ℝ) * octNormSq (octAssociator (h 0) (h 1) (h 2)) ∧
      (Dtet (fpOverlap q) (fpTriangle q) (tVec q) = 0 ↔
        ∃ φ : Quaternion ℝ →ₗ[ℝ] Octonion,
          IsQuatEmbedding φ ∧ ∀ i, octIm (h i) ∈ Set.range φ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, H⟩ := native_octonionicHolonomies q hq ho
  exact ⟨_, H, H.determinant, H.determinant_zero_iff_quaternionic⟩

example : ¬ ∃ r : ℝ, oppositeCliffordAction 0 * oppositeCliffordAction 1 * oppositeCliffordAction 2 =
    r • (1 : Module.End ℝ QuaternionCliffordSectors) := by
  rintro ⟨r, hr⟩
  exact oppositeCliffordAction_nonScalar r hr

#print axioms native_octonionicHolonomies
#print axioms OctonionicHolonomyData.unitary
#print axioms OctonionicHolonomyData.clifford
#print axioms OctonionicHolonomyData.face
#print axioms OctonionicHolonomyData.oriented_triple
#print axioms OctonionicHolonomyData.determinant
#print axioms OctonionicHolonomyData.determinant_imaginary
#print axioms OctonionicHolonomyData.determinant_zero_iff_quaternionic
#print axioms oppositeCliffordGenerator_unitary
#print axioms oppositeCliffordGenerator_anti
#print axioms oppositeCliffordAction_square
#print axioms oppositeCliffordAction_anti
#print axioms oppositeCliffordAction_nonScalar
#print axioms oppositeCliffordSector_irreducible
