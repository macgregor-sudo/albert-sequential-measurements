/- SPDX-License-Identifier: Apache-2.0 -/
module
public import HurwitzRankThreeClassification
public import GeneralEJATableSpeciality

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)

/-- The Jordan product admits a faithful real-linear realization in an associative algebra. -/
def HasAssociativeJordanEmbedding : Prop :=
  ∃ (A : Type) (hR : NonUnitalRing A) (hM : Module ℝ A),
    letI := hR
    letI := hM
    ∃ (_ : IsScalarTower ℝ A A) (_ : SMulCommClass ℝ A A)
      (f : E →ₗ[ℝ] A), Function.Injective f ∧
      ∀ x y, f (P.product x y) = (1 / 2 : ℝ) • (f x * f y + f y * f x)

/-- If no Albert factor occurs, the genuine simple-factor embeddings assemble into
one faithful ordinary complex Hermitian representation. -/
theorem finiteHermitianEmbedding_of_no_albertIdeal_native
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hno : ¬ Nonempty P.AlbertIdeal) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
  classical
  obtain ⟨s, hI, D, hsimple, _, _, _, hprod, hunit, _, _, _⟩ :=
    P.exists_simple_unital_product_equivalence hinner
  let Q (i : s) := P.orthogonalIdealProduct hinner i.val (hI i.val i.property)
  have hfactor (i : s) : ∃ d, Nonempty (FaithfulHermitianJordanEmbedding (Q i) d) := by
    exact (P.simpleFactorsAlbertOrHermitian_native hinner i.val (hsimple i.val i.property)).resolve_left
      (fun ⟨J, _⟩ => hno ⟨J⟩)
  obtain ⟨d, ⟨M⟩⟩ := exists_faithfulHermitianJordanEmbedding_of_factors Q hfactor
  refine ⟨d, ⟨{
    map := M.map.comp D.toLinearMap
    injective := M.injective.comp D.injective
    hermitian := fun x => M.hermitian (D x)
    unit := ?_
    jordan := ?_ }⟩⟩
  · change M.map (D P.unit) = 1
    rw [hunit]
    exact M.unit
  · intro x y
    have h : D (P.product x y) = (factorProduct Q).product (D x) (D y) := funext (hprod x y)
    change M.map (D (P.product x y)) =
      (1 / 2 : ℝ) • (M.map (D x) * M.map (D y) + M.map (D y) * M.map (D x))
    rw [h, M.jordan]

theorem finiteHermitianEmbedding_or_albertIdeal_native
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    (∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d)) ∨ Nonempty P.AlbertIdeal := by
  by_cases h : Nonempty P.AlbertIdeal
  · exact Or.inr h
  · exact Or.inl (P.finiteHermitianEmbedding_of_no_albertIdeal_native hinner h)

theorem not_albertIdeal_of_associativeJordanEmbedding_native
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (h : P.HasAssociativeJordanEmbedding) : ¬ Nonempty P.AlbertIdeal := by
  obtain ⟨A, hR, hM, hT, hC, f, hinj, hprod⟩ := h
  let := hR
  let := hM
  let := hT
  let := hC
  rintro ⟨I⟩
  exact I.not_injective_associativeJordanMap hinner f hprod hinj

theorem finiteHermitianEmbedding_iff_associativeJordanEmbedding_native
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)) :
    (∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d)) ↔ P.HasAssociativeJordanEmbedding := by
  constructor
  · rintro ⟨d, ⟨M⟩⟩
    exact ⟨Matrix (Fin d) (Fin d) ℂ, inferInstance, inferInstance, inferInstance, inferInstance,
      M.map, M.injective, M.jordan⟩
  · intro h
    exact P.finiteHermitianEmbedding_of_no_albertIdeal_native hinner
      (P.not_albertIdeal_of_associativeJordanEmbedding_native hinner h)

/-- Core Theorem 4.11(a) with the actual generated algebra and no classification premise. -/
theorem exists_projectiveRepresentation_of_zeroAlbertWeights_in_generatedMenu_native {n : ℕ}
    (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (ρ : E) (hρ : P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ)
    (hzero : ∀ I : (P.generatedMenuProduct p).AlbertIdeal,
      P.canonicalTraceFormOfFormallyReal (P.formallyReal_of_associative_inner hinner) ρ
        ((P.generatedMenuProduct p).idealUnit I.carrier).val = 0) :
    ∃ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧ ∀ w, M.probability w =
        P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
          (P.sequentialBranchState p ρ w) :=
  P.exists_projectiveRepresentation_of_zeroAlbertWeights_in_generatedMenu_of_classifiedFactors p hp hinner
    ((P.generatedMenuProduct p).simpleFactorsAlbertOrHermitian_native (P.generatedMenuProduct_inner p hinner))
    ρ hρ hzero

/-- A special generated algebra represents every canonical state by a finite complex model. -/
theorem exists_projectiveRepresentation_of_special_generatedMenu_native {n : ℕ}
    (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hspecial : (P.generatedMenuProduct p).HasAssociativeJordanEmbedding)
    (ρ : E) (hρ : P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ) :
    ∃ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧ ∀ w, M.probability w =
        P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
          (P.sequentialBranchState p ρ w) :=
  P.exists_projectiveRepresentation_of_zeroAlbertWeights_in_generatedMenu_native p hp hinner ρ hρ
    (fun I => ((P.generatedMenuProduct p).not_albertIdeal_of_associativeJordanEmbedding_native
      (P.generatedMenuProduct_inner p hinner) hspecial ⟨I⟩).elim)

/-- For B-primitive menus, the finite exact model exists exactly when every
Albert summand has zero weight. The arbitrary-model exclusions use the same
positive-weight theorem over each of the three fields. -/
theorem exists_projectiveRepresentation_iff_zeroAlbertWeights_of_BPrimitive_native {n : ℕ}
    (p : Fin n → E) (hp : ∀ i, P.product (p i) (p i) = p i) (hprimitive : P.IsBPrimitiveMenu p)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (ρ : E) (hρ : P.IsCanonicalDensity (P.formallyReal_of_associative_inner hinner) ρ) :
    (∃ (d : ℕ) (M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧ ∀ w, M.probability w =
        P.canonicalTraceOfFormallyReal (P.formallyReal_of_associative_inner hinner)
          (P.sequentialBranchState p ρ w)) ↔
    ∀ I : (P.generatedMenuProduct p).AlbertIdeal,
      P.canonicalTraceFormOfFormallyReal (P.formallyReal_of_associative_inner hinner) ρ
        ((P.generatedMenuProduct p).idealUnit I.carrier).val = 0 := by
  constructor
  · rintro ⟨d, M, _, hM⟩ I
    let B := P.generatedMenuProduct p
    let c := B.idealUnit I.carrier
    let hfr := P.formallyReal_of_associative_inner hinner
    let ω := P.canonicalPairingFunctional hfr ρ
    have hpos : ∀ x, 0 ≤ ω (P.product x x) :=
      (P.canonicalTraceRepresentative_positive_iff hfr ω).mp (by
        rw [P.canonicalTraceRepresentative_pairingFunctional]
        exact hρ.1)
    have hc := B.idealUnit_idempotent (P.generatedMenuProduct_inner p hinner) I.carrier I.isIdeal
    have hc' : P.product c.val c.val = c.val := congrArg Subtype.val hc
    have hnonneg : 0 ≤ ω c.val := hc' ▸ hpos c.val
    change ω c.val = 0
    by_contra hne
    have hpositive := lt_of_le_of_ne hnonneg (Ne.symm hne)
    apply P.no_algebraicModel_of_BPrimitiveMenu_albertWeight p hinner hprimitive I ρ hρ hpositive
      (AlbertChallenge.Bridge.ofProjectiveRepresentation M)
    intro w
    rw [AlbertChallenge.Bridge.ofProjectiveRepresentation_probability]
    exact hM w
  · exact P.exists_projectiveRepresentation_of_zeroAlbertWeights_in_generatedMenu_native p hp hinner ρ hρ

/-- Proposition 4.14(c) for abstract associative speciality and both table classes. -/
theorem canonicalProjectiveTables_iff_special_native
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hfr : P.FormallyReal) :
    ((∀ n, P.canonicalProjectiveTables hfr n ⊆ hilbertProjectiveTables.{0} ℂ n) ↔
      (∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n)) ∧
    ((∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n) ↔
      P.HasAssociativeJordanEmbedding) := by
  obtain ⟨hclasses, hfinite⟩ := P.canonicalProjectiveTables_iff_of_hermitian_or_albert hinner hfr
    (P.finiteHermitianEmbedding_or_albertIdeal_native hinner)
  exact ⟨hclasses, hfinite.trans (P.finiteHermitianEmbedding_iff_associativeJordanEmbedding_native hinner)⟩

/-- The three equivalent speciality conditions in core Corollary 4.13. -/
theorem special_iff_all_tables_and_four_tables_native
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hfr : P.FormallyReal) :
    (P.HasAssociativeJordanEmbedding ↔ ∀ n, P.canonicalProjectiveTables hfr n ⊆ hilbertProjectiveTables.{0} ℂ n) ∧
    ((∀ n, P.canonicalProjectiveTables hfr n ⊆ hilbertProjectiveTables.{0} ℂ n) ↔
      P.canonicalProjectiveTables hfr 4 ⊆ hilbertProjectiveTables.{0} ℂ 4) := by
  obtain ⟨hclasses, hspecial⟩ := P.canonicalProjectiveTables_iff_special_native hinner hfr
  have hall := (hclasses.trans hspecial).symm
  refine ⟨hall, ⟨fun h => h 4, fun hfour => hall.mp ?_⟩⟩
  apply (P.finiteHermitianEmbedding_iff_associativeJordanEmbedding_native hinner).mp
  apply P.finiteHermitianEmbedding_of_no_albertIdeal_native hinner
  intro hideal
  obtain ⟨f, hf, hnot⟩ := (Classical.choice hideal).exists_canonicalProjectiveTable_not_complex hinner hfr
  exact hnot (hfour hf)

end AlbertSequential.UnitalJordanProduct
