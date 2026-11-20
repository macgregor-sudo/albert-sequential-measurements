/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanDensityCompactness
public import GeneralEJASpecialFactors
public import HilbertModelSeparation

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open scoped InnerProductSpace BigOperators

universe uR uC uQ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) {n : ℕ} (p : Fin n → E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    {k : ℕ} (I : Fin k → (P.generatedMenuProduct p).AlbertIdeal)

local notation "B" => P.generatedMenuProduct p
local notation "hfr" => P.formallyReal_of_associative_inner hinner

/-- The sum of the units of the specified actual Albert summands of the generated menu. -/
def exceptionalUnit : E := ∑ i, ((B).idealUnit (I i).carrier).val

def exceptionalWeight (ρ : E) : ℝ :=
  P.canonicalTraceFormOfFormallyReal hfr ρ (P.exceptionalUnit p I)

def exceptionalWeightSlice (ε : ℝ) : Set E :=
  {ρ | P.IsCanonicalDensity hfr ρ ∧ ε ≤ P.exceptionalWeight p hinner I ρ}

theorem isCompact_exceptionalWeightSlice (ε : ℝ) :
    IsCompact (P.exceptionalWeightSlice p hinner I ε) := by
  change IsCompact ({ρ | P.IsCanonicalDensity hfr ρ} ∩ {ρ | ε ≤ P.exceptionalWeight p hinner I ρ})
  apply (P.isCompact_canonicalDensity hfr).inter_right
  apply isClosed_le continuous_const
  exact ((P.canonicalTraceFormOfFormallyReal hfr).flip
    (P.exceptionalUnit p I)).toContinuousLinearMap.continuous

theorem convex_exceptionalWeightSlice (ε : ℝ) :
    Convex ℝ (P.exceptionalWeightSlice p hinner I ε) := by
  intro x hx y hy a b ha hb hab
  refine ⟨P.convex_canonicalDensity hinner hfr hx.1 hy.1 ha hb hab,?_⟩
  change ε ≤ P.canonicalTraceFormOfFormallyReal hfr (a • x + b • y) (P.exceptionalUnit p I)
  rw [map_add,map_smul,map_smul,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply]
  change ε ≤ a * P.exceptionalWeight p hinner I x + b * P.exceptionalWeight p hinner I y
  calc
    ε = a * ε + b * ε := by rw [← add_mul,hab,one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)

private def tableCoordinate (w : Word (Fin n)) : E →ₗ[ℝ] ℝ :=
  (P.canonicalTraceFormOfFormallyReal hfr).flip (P.sequentialWordEffect p w)

private theorem tableCoordinate_trace (ρ : E) (w : Word (Fin n)) :
    P.tableCoordinate p hinner w ρ =
      P.canonicalTraceOfFormallyReal hfr (P.sequentialBranchState p ρ w) :=
  (P.canonicalTrace_sequentialBranchState hfr p ρ w).symm

private theorem moment_probability_nil (m : ProjectionMoments n)
    (hm : AdmissibleProjectionMoments n m) : momentWordProbability m [] = 1 := by
  simpa [momentWordProbability,effectPolynomial,amplitudePolynomial,
    polynomialStar,polynomialMultiply,polynomialMoment] using hm.normalized

private theorem no_moment_match_on_exceptionalWeightSlice (menu : P.IsBPrimitiveMenu p)
    (ε : ℝ) (hε : 0 < ε) (m : ProjectionMoments n) (hm : AdmissibleProjectionMoments n m)
    (ρ : E) (hρ : ρ ∈ P.exceptionalWeightSlice p hinner I ε) :
    ∃ w, momentWordProbability m w ≠ P.tableCoordinate p hinner w ρ := by
  by_contra! heq
  have hpos : 0 < ∑ i, P.canonicalTraceFormOfFormallyReal hfr ρ ((B).idealUnit (I i).carrier).val := by
    have h := hε.trans_le hρ.2
    simpa only [exceptionalWeight,exceptionalUnit,map_sum] using h
  have hsome : ∃ i, 0 < P.canonicalTraceFormOfFormallyReal hfr ρ ((B).idealUnit (I i).carrier).val := by
    by_contra! h
    exact (not_le_of_gt hpos) (Finset.sum_nonpos fun i _ => h i)
  obtain ⟨i,hi⟩ := hsome
  apply P.no_algebraicModel_of_BPrimitiveMenu_albertWeight p hinner menu (I i) ρ hρ.1 hi
    (momentsToProjectiveData m hm)
  intro w
  rw [realizedMoments_probability,heq,P.tableCoordinate_trace]

/-- One finite moment-observable inequality excludes the entire slice of canonical
densities above a fixed positive total exceptional weight. -/
theorem uniformMomentSeparator_exceptionalWeight (menu : P.IsBPrimitiveMenu p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (L : ℕ) (c : FiniteRealWordFunctional n) (γ : ℝ), 0 < γ ∧ c.HasHorizon L ∧
      (∀ m, AdmissibleProjectionMoments n m → 0 ≤ c.evaluate (momentWordProbability m)) ∧
      ∀ ρ ∈ P.exceptionalWeightSlice p hinner I ε,
        c.evaluate (fun w => P.canonicalTraceOfFormallyReal hfr (P.sequentialBranchState p ρ w)) ≤ -γ := by
  classical
  let D := P.exceptionalWeightSlice p hinner I ε
  obtain ⟨F,hempty,hF⟩ := exists_finite_distinguishing_coordinates_containing
    (isCompact_projectionMomentDomain n) (P.isCompact_exceptionalWeightSlice p hinner I ε)
    (fun w m => momentWordProbability m w) (fun w ρ => P.tableCoordinate p hinner w ρ)
    continuous_momentWordProbability (fun w => (P.tableCoordinate p hinner w).toContinuousLinearMap.continuous)
    (P.no_moment_match_on_exceptionalWeightSlice p hinner I menu ε hε) ([] : Word (Fin n))
  let M := (fun m => fun w : F => momentWordProbability m w) '' projectionMomentDomain n
  let N := (fun ρ => fun w : F => P.tableCoordinate p hinner w ρ) '' D
  have hMc : IsCompact M := (isCompact_projectionMomentDomain n).image
    (continuous_pi fun w => continuous_momentWordProbability w.val)
  have hNc : IsCompact N := (P.isCompact_exceptionalWeightSlice p hinner I ε).image
    (continuous_pi fun w => (P.tableCoordinate p hinner w.val).toContinuousLinearMap.continuous)
  have hMv : Convex ℝ M := by
    rintro _ ⟨m,hm,rfl⟩ _ ⟨l,hl,rfl⟩ a b ha hb hab
    refine ⟨a • m + b • l,convex_projectionMomentDomain n hm hl ha hb hab,?_⟩
    funext w
    exact polynomialMoment_combination (effectPolynomial w.val) a b m l
  have hNv : Convex ℝ N := by
    rintro _ ⟨ρ,hρ,rfl⟩ _ ⟨σ,hσ,rfl⟩ a b ha hb hab
    refine ⟨a • ρ + b • σ,P.convex_exceptionalWeightSlice p hinner I ε hρ hσ ha hb hab,?_⟩
    funext w
    exact (map_add _ _ _).trans (by rw [map_smul,map_smul]; rfl)
  have hdisj : Disjoint N M :=
    (disjoint_coordinate_images_of_distinguishing (projectionMomentDomain n) D
      (fun w m => momentWordProbability m w) (fun w ρ => P.tableCoordinate p hinner w ρ) F hF).symm
  obtain ⟨c,γ,hγ,hN,hM⟩ := finiteCompactConvex_normalizedSeparation
    hNc hNv hMc hMv hdisj ⟨[],hempty⟩
    (by
      rintro _ ⟨ρ,hρ,rfl⟩
      change P.tableCoordinate p hinner [] ρ = 1
      rw [P.tableCoordinate_trace]
      exact hρ.1.2)
    (by
      rintro _ ⟨m,hm,rfl⟩
      exact moment_probability_nil m hm)
  refine ⟨F.sup List.length,finiteCoordinatesFunctional F c,γ,hγ,finiteCoordinatesFunctional_horizon F c,?_,?_⟩
  · intro m hm
    rw [finiteCoordinatesFunctional_evaluate]
    exact hγ.le.trans (hM _ ⟨m,hm,rfl⟩)
  · intro ρ hρ
    rw [finiteCoordinatesFunctional_evaluate]
    have hcoordinates :
        (fun w : F => P.canonicalTraceOfFormallyReal hfr (P.sequentialBranchState p ρ w.val)) =
          (fun w : F => P.tableCoordinate p hinner w.val ρ) :=
      funext (fun w => (P.tableCoordinate_trace p hinner ρ w.val).symm)
    rw [hcoordinates]
    exact hN _ ⟨ρ,hρ,rfl⟩

/-- The same coefficients work for the three actual class-(I) model fields. -/
theorem uniformHilbertSeparator_exceptionalWeight (menu : P.IsBPrimitiveMenu p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (L : ℕ) (c : FiniteRealWordFunctional n) (γ : ℝ),
      0 < γ ∧ c.HasHorizon L ∧
      (∀ (H : Type uR) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (M : HilbertProjectiveData (Fin n) ℝ H), 0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ (H : Type uC) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : HilbertProjectiveData (Fin n) ℂ H), 0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ (H : Type uQ) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (S : RightQuaternionicHilbertStructure H) (M : QuaternionicProjectiveData (Fin n) S.toOperatorStructure),
        0 ≤ c.evaluate (fun w => M.state (M.wordEffect w))) ∧
      ∀ ρ ∈ P.exceptionalWeightSlice p hinner I ε,
        c.evaluate (fun w => P.canonicalTraceOfFormallyReal hfr (P.sequentialBranchState p ρ w)) ≤ -γ := by
  obtain ⟨L,c,γ,hγ,hL,hc,hstate⟩ := P.uniformMomentSeparator_exceptionalWeight p hinner I menu ε hε
  refine ⟨L,c,γ,hγ,hL,?_,?_,?_,hstate⟩
  · intro H _ _ _ M
    exact HilbertModelSeparation.hilbertFunctional_nonnegative c hc M
  · intro H _ _ _ M
    exact HilbertModelSeparation.hilbertFunctional_nonnegative c hc M
  · intro H _ _ _ S M
    exact HilbertModelSeparation.rightQuaternionicFunctional_nonnegative c hc S M

end AlbertSequential.UnitalJordanProduct
