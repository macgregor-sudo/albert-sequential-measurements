/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAAlbertIdeal
public import GeneralEJAOperatorCompression
public import SpinFactorTables

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential

universe v

theorem finiteComplexTables_subset_complex (n : ℕ) :
    finiteHilbertProjectiveTables.{v} ℂ n ⊆ hilbertProjectiveTables.{v} ℂ n := by
  rintro f ⟨H, hN, hI, hC, _, M, hM⟩
  exact ⟨H, hN, hI, hC, M, hM⟩

namespace UnitalJordanProduct

section FiniteRealization

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {P : UnitalJordanProduct E}

/-- An actual real-linear unital Jordan embedding into complex self-adjoint operators. -/
def HasUnitalSelfAdjointOperatorEmbedding (P : UnitalJordanProduct E) : Prop :=
  ∃ (H : Type) (hN : NormedAddCommGroup H),
    letI := hN
    ∃ (hI : InnerProductSpace ℂ H) (hC : CompleteSpace H),
      letI := hI
      letI := hC
      ∃ f : E →ₗ[ℝ] (H →L[ℂ] H), Function.Injective f ∧ f P.unit = 1 ∧
        (∀ x, IsSelfAdjoint (f x)) ∧
        ∀ x y, f (P.product x y) = (1 / 2 : ℝ) • (f x * f y + f y * f x)

open MatchingModels AlbertChallenge.Bridge in
theorem finiteHermitianEmbedding_iff_unitalSelfAdjointOperators :
    (∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d)) ↔ P.HasUnitalSelfAdjointOperatorEmbedding := by
  constructor
  · rintro ⟨d, ⟨embedding⟩⟩
    let f : E →ₗ[ℝ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
      { toFun x := matToCLM (embedding.map x)
        map_add' x y := by rw [map_add, matToCLM_add]
        map_smul' a x := by rw [map_smul, matToCLM_real_smul]; rfl }
    refine ⟨EuclideanSpace ℂ (Fin d), inferInstance, inferInstance, inferInstance, f, ?_, ?_, ?_, ?_⟩
    · intro x y h
      change matToCLM (embedding.map x) = matToCLM (embedding.map y) at h
      apply embedding.injective
      simpa only [clmMatrix_matToCLM] using congrArg clmMatrix h
    · change matToCLM (embedding.map P.unit) = 1
      rw [embedding.unit, matToCLM_one]
    · intro x
      exact matToCLM_isSelfAdjoint (embedding.hermitian x)
    · intro x y
      change matToCLM (embedding.map (P.product x y)) = (1 / 2 : ℝ) •
        (matToCLM (embedding.map x) * matToCLM (embedding.map y) +
          matToCLM (embedding.map y) * matToCLM (embedding.map x))
      rw [embedding.jordan, matToCLM_real_smul, matToCLM_add, matToCLM_mul, matToCLM_mul]
      rfl
  · rintro ⟨H, hN, hI, hC, f, hinjective, hunit, hself, hproduct⟩
    let := hN
    let := hI
    let := hC
    exact P.exists_faithfulHermitianJordanEmbedding_of_operators f hinjective hunit hself hproduct

/-- A faithful Hermitian realization represents every canonical table in finite dimension. -/
theorem canonicalProjectiveTables_subset_of_hermitianEmbedding {d : ℕ}
    (embedding : FaithfulHermitianJordanEmbedding P d) (hfr : P.FormallyReal) (n : ℕ) :
    P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n := by
  rintro f ⟨p, ρ, hp, hρ, hwords⟩
  let φ := P.canonicalPairingFunctional hfr ρ
  have hpositive : ∀ x, 0 ≤ φ (P.product x x) :=
    (P.canonicalTraceRepresentative_positive_iff hfr φ).mp (by
      rw [P.canonicalTraceRepresentative_pairingFunctional]
      exact hρ.1)
  have hnorm : φ P.unit = 1 := (P.canonicalTraceFormOfFormallyReal_unit hfr ρ).trans hρ.2
  obtain ⟨M, _, hM⟩ := embedding.exists_projectiveRepresentation_of_embedding p hp φ hpositive hnorm
  let A := AlbertChallenge.Bridge.ofProjectiveRepresentation M
  let R := cyclicHilbertModel A
  let hfinite := hilbertOperatorAlgebra_finiteReal (𝕜 := ℂ) (H := EuclideanSpace ℂ (Fin d))
  let _ : FiniteDimensional ℝ (CyclicHilbert A) :=
    @cyclicHilbert_finite_of_ambient (Fin n) (HilbertOperatorAlgebra ℂ (EuclideanSpace ℂ (Fin d)))
      _ _ _ _ _ _ A hfinite
  let _ : FiniteDimensional ℂ (RealHilbertComplexification (CyclicHilbert A)) := complexification_finiteDimensional
  apply mem_finiteHilbertProjectiveTables_of_model R.complexExtensionModel
  intro w
  exact (R.complexExtensionModel_probability w).trans ((cyclicHilbertModel_probability A w).trans
    ((AlbertChallenge.Bridge.ofProjectiveRepresentation_probability M w).trans ((hM w).trans (hwords w))))

theorem canonicalProjectiveTables_subset_of_operatorEmbedding
    (h : P.HasUnitalSelfAdjointOperatorEmbedding) (hfr : P.FormallyReal) (n : ℕ) :
    P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n := by
  obtain ⟨_, ⟨embedding⟩⟩ := finiteHermitianEmbedding_iff_unitalSelfAdjointOperators.mpr h
  exact canonicalProjectiveTables_subset_of_hermitianEmbedding embedding hfr n

end FiniteRealization

section AlbertObstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {P : UnitalJordanProduct E}

/-- A genuine Albert ideal gives a four-test table outside the complex class in every dimension. -/
theorem AlbertIdeal.exists_canonicalProjectiveTable_not_complex (I : P.AlbertIdeal)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hfr : P.FormallyReal) :
    ∃ f ∈ P.canonicalProjectiveTables hfr 4, f ∉ hilbertProjectiveTables.{v} ℂ 4 := by
  obtain ⟨p, ρ, hp, hρ, hno⟩ := I.exists_four_test_obstruction_of_albertIdeal hinner
  let f := fun w => P.canonicalPairingFunctional hfr ρ (P.sequentialWordEffect p w)
  refine ⟨f, ⟨p, ρ, hp, hρ, fun _ => rfl⟩, ?_⟩
  rintro ⟨H, hN, hI, hC, M, hM⟩
  let := hN
  let := hI
  let := hC
  apply hno _ M.toAlgebraic
  intro w
  exact (hM w).trans (P.canonicalTrace_sequentialBranchState hfr p ρ w).symm

/-- Restriction to the Albert ideal prevents an injective algebraic Jordan embedding. -/
theorem AlbertIdeal.not_injective_associativeJordanMap (I : P.AlbertIdeal)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    {A : Type*} [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (f : E →ₗ[ℝ] A)
    (hf : ∀ x y, f (P.product x y) = (1 / 2 : ℝ) • (f x * f y + f y * f x)) :
    ¬ Function.Injective f := by
  intro hinj
  let η := f.comp I.inclusion
  have hη : IsJordanHom η := by
    intro x y
    change f (I.inclusion (jordanMul x y)) =
      (1 / 2 : ℝ) • (f (I.inclusion x) * f (I.inclusion y) + f (I.inclusion y) * f (I.inclusion x))
    rw [← I.inclusion_product hinner]
    exact hf _ _
  have hz := albertJordanHom_eq_zero A η hη
  have hzero : f (I.inclusion (diagAtom 0)) = f 0 := by
    rw [map_zero]
    change η (diagAtom 0) = 0
    rw [hz]
    rfl
  have hdiag : diagAtom 0 = 0 := by
    simpa only [I.projection_inclusion, map_zero] using congrArg I.projection (hinj hzero)
  have htrace := (diagAtom_isAtom 0).2
  rw [hdiag, NativeAnalysis.albertTrace_zero] at htrace
  exact zero_ne_one htrace

/-- Proposition 4.14(c) on the two actual cases furnished by a classification proof. -/
theorem canonicalProjectiveTables_iff_of_hermitian_or_albert
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hfr : P.FormallyReal)
    (hcases : (∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d)) ∨ Nonempty P.AlbertIdeal) :
    ((∀ n, P.canonicalProjectiveTables hfr n ⊆ hilbertProjectiveTables.{0} ℂ n) ↔
      (∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n)) ∧
    ((∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n) ↔
      ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d)) := by
  have hfinite_of_embedding (h : ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d)) :
      ∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n := by
    obtain ⟨_, ⟨embedding⟩⟩ := h
    exact canonicalProjectiveTables_subset_of_hermitianEmbedding embedding hfr
  have hinfinite_of_finite
      (h : ∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n) :
      ∀ n, P.canonicalProjectiveTables hfr n ⊆ hilbertProjectiveTables.{0} ℂ n :=
    fun n => (h n).trans (finiteComplexTables_subset_complex n)
  have hembedding_of_infinite
      (h : ∀ n, P.canonicalProjectiveTables hfr n ⊆ hilbertProjectiveTables.{0} ℂ n) :
      ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
    rcases hcases with hembedding | hideal
    · exact hembedding
    · let I := Classical.choice hideal
      obtain ⟨f, hf, hno⟩ := I.exists_canonicalProjectiveTable_not_complex hinner hfr
      exact (hno (h 4 hf)).elim
  exact ⟨⟨fun h => hfinite_of_embedding (hembedding_of_infinite h), hinfinite_of_finite⟩,
    ⟨fun h => hembedding_of_infinite (hinfinite_of_finite h), hfinite_of_embedding⟩⟩

theorem canonicalProjectiveTables_iff_operatorSpecial_of_hermitian_or_albert
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hfr : P.FormallyReal)
    (hcases : (∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d)) ∨ Nonempty P.AlbertIdeal) :
    ((∀ n, P.canonicalProjectiveTables hfr n ⊆ hilbertProjectiveTables.{0} ℂ n) ↔
      (∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n)) ∧
    ((∀ n, P.canonicalProjectiveTables hfr n ⊆ finiteHilbertProjectiveTables.{0} ℂ n) ↔
      P.HasUnitalSelfAdjointOperatorEmbedding) := by
  obtain ⟨hfinite, hspecial⟩ := canonicalProjectiveTables_iff_of_hermitian_or_albert hinner hfr hcases
  exact ⟨hfinite, hspecial.trans finiteHermitianEmbedding_iff_unitalSelfAdjointOperators⟩

end AlbertObstruction

end UnitalJordanProduct
end AlbertSequential
