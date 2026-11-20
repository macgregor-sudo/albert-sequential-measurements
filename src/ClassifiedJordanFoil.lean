/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanTableFoil
public import JordanExceptionalWeightLimit
public import HurwitzRankThreeClassification

/-! The unconditional convex-hull foil and exceptional-weight limit of 4.15–4.16. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace AlbertSequential

theorem allSimpleFactorsAlbertOrHermitian_native : AllSimpleFactorsAlbertOrHermitian :=
  fun _ _ _ _ P hinner => P.simpleFactorsAlbertOrHermitian_native hinner

theorem finiteJordanTables_eq_convexHull (n : ℕ) :
    finiteJordanTables.{0} n =
      convexHull ℝ (finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n) :=
  finiteJordanTables_eq_convexHull_of_classifiedFactors allSimpleFactorsAlbertOrHermitian_native n

theorem finiteJordan_linear_inequality_iff {n : ℕ} (L : (Word (Fin n) → ℝ) →ₗ[ℝ] ℝ)
    (hQ : ∀ f ∈ finiteHilbertProjectiveTables.{0} ℂ n, 0 ≤ L f) :
    (∀ f ∈ finiteJordanTables.{0} n, 0 ≤ L f) ↔ ∀ f ∈ nativeAlbertTables n, 0 ≤ L f :=
  finiteJordan_linear_inequality_iff_of_classifiedFactors allSimpleFactorsAlbertOrHermitian_native L hQ

namespace UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    {k : ℕ} (I : Fin k → (P.generatedMenuProduct p).AlbertIdeal)

/-- The family enumerates the distinct exceptional summands defining the printed sum. -/
theorem exceptionalWeight_no_uniform_margin
    (hp : ∀ i, P.product (p i) (p i) = p i)
    (horth : ∀ a b, a ≠ b → (I a).carrier ≤ (I b).carrierᗮ)
    (hcomplete : ∀ J : (P.generatedMenuProduct p).AlbertIdeal, ∃ i, (I i).carrier = J.carrier)
    (j : Fin k) (hcomp : P.exceptionalUnit p I ≠ P.unit) (c : FiniteRealWordFunctional n)
    (γ : ℝ) (hγ : 0 < γ) :
    ¬ ((∀ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
        0 ≤ c.evaluate M.probability) ∧
      (∀ ρ, P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ →
        0 < P.exceptionalWeight p hinner I ρ →
        c.evaluate (fun w => P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
          (P.sequentialBranchState p ρ w)) ≤ -γ)) :=
  P.noUniformMargin_exceptionalWeight p hinner I
    ((P.generatedMenuProduct p).simpleFactorsAlbertOrHermitian_native (P.generatedMenuProduct_inner p hinner))
    hp horth hcomplete j hcomp c γ hγ
end UnitalJordanProduct
end AlbertSequential
