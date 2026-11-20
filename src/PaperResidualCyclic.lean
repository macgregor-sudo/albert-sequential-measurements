/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PaperRobustVectors
public import CyclicWordVectors

/-! The companion's vector residual statements in the checked real cyclic model of an
arbitrary sequential projective representation. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential AlbertSequential.LengthSeven

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm
attribute [local irreducible] fourPointInvariant

/-- The actual A.2 vector decomposition for every algebraic projective table, evaluated in
its real cyclic Hilbert representation with the unconditioned corner `P_A Ω`. -/
theorem gram_norm_cyclic_eq_table_add_residuals
    (M : AlgebraicProjectiveData Letter A) (vecs : List (ℚ × List Letter))
    (pairs : List (ℚ × Entry)) (hPairs : pairs.map (fun p => (p.1, p.2.u1, p.2.u2)) = pairSpec vecs)
    (hok : pairs.all (fun p => p.2.ok) = true) :
    let P := cyclicHilbertProjection M
    let Ω := cyclicHilbertVector M
    let ζ := P 0 Ω
    ‖residualGramVector P ζ vecs‖ ^ 2 =
      evalF (fun w => M.probability ((0,true) :: w)) (gramTableTerms pairs) +
      ((gramResidualOccurrences pairs).map fun o =>
        (o.1 : ℝ) * ⟪wordAmplitude P (yesWord o.2.α) ζ, robustResidualVector P ζ o.2⟫_ℝ).sum := by
  have h := gram_norm_unconditioned_eq_table_add_residuals (cyclicHilbertProjection M)
    (cyclicHilbertProjection_isStarProjection M) (cyclicHilbertVector M) vecs pairs hPairs hok
  have hprob : residualVectorProbability (cyclicHilbertProjection M) (cyclicHilbertVector M) =
      M.probability := funext (cyclicHilbert_word_probability M)
  rw [hprob] at h
  exact h

/-- The three-history residual in the cyclic model is read from the original model's
unconditioned probabilities, including the leading `yes A` on each term. -/
theorem robustResidualVector_cyclic_square (M : AlgebraicProjectiveData Letter A) (d : Defect) :
    let P := cyclicHilbertProjection M
    let Ω := cyclicHilbertVector M
    ‖robustResidualVector P (P 0 Ω) d‖ ^ 2 = M.probability ((0,true) :: d.long) -
      2 * (d.c : ℝ) * M.probability ((0,true) :: d.mid) +
      (d.c : ℝ) ^ 2 * M.probability ((0,true) :: d.short) := by
  let P := cyclicHilbertProjection M
  let Ω := cyclicHilbertVector M
  have hprob := fun w => (residualVectorProbability_prefix P Ω w).trans
    (cyclicHilbert_word_probability M ((0,true) :: w))
  have h := robustResidualVector_square P (cyclicHilbertProjection_isStarProjection M) (P 0 Ω) d
  simpa only [hprob] using h

/-- The actual A.4 residual telescope in the real cyclic representation, at any base.
The determinant uses the original native menu; the base-dependent word polynomials are
evaluated with the corresponding relabelled projections. -/
theorem atomCornerResidualTelescope_cyclicIdentity (M : AlgebraicProjectiveData (Fin 4) A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) (j : Fin 4) :
    let pj := p ∘ Equiv.swap 0 j
    let Pj := cyclicHilbertProjection M ∘ Equiv.swap 0 j
    let Ω := cyclicHilbertVector M
    let s := CornerHolonomy.finiteTetrahedronParameters (nativeOverlaps p)
      (nativeTriangles p) (nativeCornerQ p)
    let occ := cornerResidualTelescopeOccurrences (BlockB.atomCornerData pj) (BlockB.atomCornerScalar pj)
    ((Matrix.of s.gramMatrix).det - s.d0 ^ 2) * M.probability [(j,true)] =
      (occ.map fun o => ⟪o.leftElement Pj Ω, o.leaf.residualElement Pj Ω⟫_ℝ).sum := by
  let pj := p ∘ Equiv.swap 0 j
  let Pj := cyclicHilbertProjection M ∘ Equiv.swap 0 j
  let Ω := cyclicHilbertVector M
  have hpj (i) : IsAtom (pj i) := hp (Equiv.swap 0 j i)
  have hAj : 0 < fourPointInvariant pj := BlockB.fourPointInvariant_swapBase p j hA
  have hPj (i) : IsStarProjection (Pj i) := cyclicHilbertProjection_isStarProjection M (Equiv.swap 0 j i)
  have h := cornerResidualTelescope_vectorIdentity (BlockB.atomCornerData pj)
    (BlockB.atomCornerScalar pj) (BlockB.atomCorner_conditions pj hpj hAj) Pj hPj Ω
  have hprob : ‖Pj 0 Ω‖ ^ 2 = M.probability [(j,true)] := by
    simpa only [Pj, Function.comp_apply, Equiv.swap_apply_left, wordAmplitude_singleton,
      algebraicOutcome, ite_true] using cyclicHilbert_word_probability M [(j,true)]
  dsimp only at h ⊢
  rw [← CliffordScalarParameters.discriminant_eq_det,
    BlockB.atomCorner_discriminant_swapBase p hp hA j, CliffordScalarParameters.discriminant_eq_det,
    BlockB.atomCornerData_scalarParameters_eq_finiteTetrahedron p hp hA, hprob] at h
  exact h

end AlbertSequential.LengthSeven.Robust
