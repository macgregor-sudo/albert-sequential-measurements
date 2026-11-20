/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanOperatorTables
public import NativeAlbertTableMixtures

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential
open UnitalJordanProduct NativeAnalysis
open scoped BigOperators

theorem convex_finiteJordanTables (n : ℕ) : Convex ℝ (finiteJordanTables.{0} n) := by
  intro f hf g hg a b ha hb hab
  let tables : Fin 2 → Word (Fin n) → ℝ := ![f,g]
  let weights : Fin 2 → ℝ := ![a,b]
  have ht (k : Fin 2) : tables k ∈ finiteJordanTables.{0} n := by fin_cases k <;> assumption
  have hw (k : Fin 2) : 0 ≤ weights k := by fin_cases k <;> assumption
  simpa [tables,weights,Fin.sum_univ_two] using finiteJordanTables_sum_mem tables weights ht hw
    (by simpa [weights,Fin.sum_univ_two] using hab)

theorem convexHull_projective_union_albert_subset_finiteJordan (n : ℕ) :
    convexHull ℝ (finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n) ⊆
      finiteJordanTables.{0} n :=
  convexHull_min (Set.union_subset (finiteComplexTables_subset_finiteJordan n)
    (nativeAlbertTables_subset_finiteJordan n)) (convex_finiteJordanTables n)

namespace UnitalJordanProduct
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (P : UnitalJordanProduct E)
  (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))

private theorem AlbertIdeal.factor_words_mem_nativeAlbertTables {P : UnitalJordanProduct E}
    (I : P.AlbertIdeal) (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    {n : ℕ} (p : Fin n → I.carrier)
    (hp : ∀ i, (P.orthogonalIdealProduct hinner I.carrier I.isIdeal).product (p i) (p i) = p i)
    (ω : I.carrier →ₗ[ℝ] ℝ)
    (hpos : ∀ x, 0 ≤ ω ((P.orthogonalIdealProduct hinner I.carrier I.isIdeal).product x x))
    (hunit : ω (P.orthogonalIdealProduct hinner I.carrier I.isIdeal).unit = 1) :
    (fun w => ω ((P.orthogonalIdealProduct hinner I.carrier I.isIdeal).sequentialWordEffect p w)) ∈
      nativeAlbertTables n := by
  let Q := P.orthogonalIdealProduct hinner I.carrier I.isIdeal
  let φ := ω.comp I.identify.symm.toLinearMap
  have hm (x y : I.carrier) : I.identify (Q.product x y) =
      nativeAlbertProduct.product (I.identify x) (I.identify y) := I.product x y
  have hu : I.identify Q.unit = nativeAlbertProduct.unit := I.unit
  have hφpos (x : Albert) : 0 ≤ φ (jordanMul x x) := by
    have h := hm (I.identify.symm x) (I.identify.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    change I.identify (Q.product (I.identify.symm x) (I.identify.symm x)) = jordanMul x x at h
    change 0 ≤ ω (I.identify.symm (jordanMul x x))
    rw [← h,I.identify.symm_apply_apply]
    exact hpos _
  have hφunit : φ albertUnit = 1 := by
    change ω (I.identify.symm albertUnit) = 1
    rw [show albertUnit = I.identify Q.unit from hu.symm,I.identify.symm_apply_apply]
    exact hunit
  refine ⟨I.identify ∘ p,traceRepresentative φ,fun i => ?_,
    NativeAnalysis.normalized_positiveFunctional_density φ hφpos hφunit,?_⟩
  · change nativeAlbertProduct.product (I.identify (p i)) (I.identify (p i)) = I.identify (p i)
    rw [← hm,hp]
  · intro w
    have h := Q.map_sequentialWordEffect nativeAlbertProduct I.identify.toLinearMap hu hm p w
    change I.identify (Q.sequentialWordEffect p w) =
      nativeAlbertProduct.sequentialWordEffect (I.identify ∘ p) w at h
    rw [nativeWordProbability_eq_pairing,traceRepresentative_pairing,← nativeAlbertProduct_wordEffect,← h]
    change ω (I.identify.symm (I.identify _)) = _
    rw [I.identify.symm_apply_apply]

private theorem factor_words_mem_native_of_class {J : Submodule ℝ E}
    (hJ : P.IsJordanIdeal J) (hc : ∃ I : P.AlbertIdeal, I.carrier = J)
    {n : ℕ} (p : Fin n → J)
    (hp : ∀ i, (P.orthogonalIdealProduct hinner J hJ).product (p i) (p i) = p i)
    (ω : J →ₗ[ℝ] ℝ)
    (hpos : ∀ x, 0 ≤ ω ((P.orthogonalIdealProduct hinner J hJ).product x x))
    (hunit : ω (P.orthogonalIdealProduct hinner J hJ).unit = 1) :
    (fun w => ω ((P.orthogonalIdealProduct hinner J hJ).sequentialWordEffect p w)) ∈
      nativeAlbertTables n := by
  obtain ⟨I,rfl⟩ := hc
  exact AlbertIdeal.factor_words_mem_nativeAlbertTables I hinner p hp ω hpos hunit

private theorem factor_words_mem_complexTables {V : Type} [AddCommGroup V] [Module ℝ V]
    (Q : UnitalJordanProduct V) {n d : ℕ} (embed : FaithfulHermitianJordanEmbedding Q d)
    (p : Fin n → V) (hp : ∀ i, Q.product (p i) (p i) = p i)
    (ω : V →ₗ[ℝ] ℝ) (hpos : ∀ x, 0 ≤ ω (Q.product x x)) (hunit : ω Q.unit = 1) :
    (fun w => ω (Q.sequentialWordEffect p w)) ∈ finiteHilbertProjectiveTables.{0} ℂ n := by
  obtain ⟨M,_,hM⟩ := embed.exists_projectiveRepresentation_of_embedding p hp ω hpos hunit
  let A := AlbertChallenge.Bridge.ofProjectiveRepresentation M
  let R := cyclicHilbertModel A
  let hfinite := hilbertOperatorAlgebra_finiteReal (𝕜 := ℂ) (H := EuclideanSpace ℂ (Fin d))
  let : FiniteDimensional ℝ (CyclicHilbert A) :=
    @cyclicHilbert_finite_of_ambient (Fin n) (HilbertOperatorAlgebra ℂ (EuclideanSpace ℂ (Fin d)))
      _ _ _ _ _ _ A hfinite
  let : FiniteDimensional ℂ (RealHilbertComplexification (CyclicHilbert A)) := complexification_finiteDimensional
  apply mem_finiteHilbertProjectiveTables_of_model R.complexExtensionModel
  intro w
  exact (R.complexExtensionModel_probability w).trans ((cyclicHilbertModel_probability A w).trans
    ((AlbertChallenge.Bridge.ofProjectiveRepresentation_probability M w).trans (hM w)))

/-- Forward inclusion of the foil identity on the actual orthogonal ideals.
Only the simple-factor classification is an input. -/
theorem canonicalProjectiveTables_subset_foil_of_classifiedFactors
    (hclass : P.SimpleFactorsAlbertOrHermitian hinner) (n : ℕ) (hfr : P.FormallyReal) :
    P.canonicalProjectiveTables hfr n ⊆
      convexHull ℝ (finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n) := by
  classical
  intro f hf
  obtain ⟨p,ω,hp,hpos,hunit,hw⟩ := (P.mem_canonicalProjectiveTables_iff_functional hfr).mp hf
  obtain ⟨s,hI,D,hsimple,_,_,_,hprod,hunitD,_,hsum,hInv⟩ :=
    P.exists_simple_unital_product_equivalence hinner
  let R (i : s) := P.orthogonalIdealProduct hinner i.val (hI i.val i.property)
  let π (i : s) : E →ₗ[ℝ] i.val := (LinearMap.proj i).comp D.toLinearMap
  let pI (i : s) (j : Fin n) := π i (p j)
  let ξ (i : s) := ω.comp i.val.subtype
  let weight (i : s) := ξ i (R i).unit
  let g (i : s) := (weight i)⁻¹ • ξ i
  let T (i : s) (w : Word (Fin n)) := g i ((R i).sequentialWordEffect (pI i) w)
  let K := Finset.univ.filter fun i : s => weight i ≠ 0
  have hξpos (i : s) (x : i.val) : 0 ≤ ξ i ((R i).product x x) := hpos x.val
  have hweight (i : s) : 0 ≤ weight i := by
    have h := hξpos i (R i).unit
    rwa [(R i).unit_left] at h
  have hpI (i : s) (j : Fin n) : (R i).product (pI i j) (pI i j) = pI i j := by
    change (R i).product (D (p j) i) (D (p j) i) = D (p j) i
    rw [← hprod,hp]
  have hsumAll : ∑ i : s, weight i = 1 := by
    change ∑ i : s, ω (P.idealUnit i.val) = 1
    rw [← map_sum,hsum,hunit]
  have hsumK : ∑ i ∈ K, weight i = 1 := by
    rw [Finset.sum_filter_ne_zero]
    exact hsumAll
  have hmem (i : s) (hi : i ∈ K) :
      T i ∈ finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n := by
    have hnonzero := (Finset.mem_filter.mp hi).2
    have hgnorm : g i (R i).unit = 1 := inv_mul_cancel₀ hnonzero
    have hgpos (x : i.val) : 0 ≤ g i ((R i).product x x) :=
      mul_nonneg (inv_nonneg.mpr (hweight i)) (hξpos i x)
    rcases hclass i.val (hsimple _ i.property) with hAlbert | ⟨d,⟨e⟩⟩
    · exact Or.inr (factor_words_mem_native_of_class P hinner (hI _ i.property) hAlbert
        (pI i) (hpI i) (g i) hgpos hgnorm)
    · left
      exact factor_words_mem_complexTables (R i) e (pI i) (hpI i) (g i) hgpos hgnorm
  have hdecomposition : ∑ i ∈ K, weight i • T i = f := by
    funext w
    rw [Finset.sum_apply,← hw w]
    have hterm (i : s) : (weight i • T i) w =
        ξ i (D (P.sequentialWordEffect p w) i) := by
      have hcomponent := P.map_sequentialWordEffect (R i) (π i) (congrFun hunitD i)
        (fun x y => hprod x y i) p w
      change D (P.sequentialWordEffect p w) i = (R i).sequentialWordEffect (pI i) w at hcomponent
      change weight i * g i ((R i).sequentialWordEffect (pI i) w) = _
      rw [← hcomponent]
      by_cases hi : weight i = 0
      · let hR := (R i).formallyReal_of_associative_inner (P.orthogonalIdealProduct_inner hinner _ _)
        have hz : ξ i = 0 := (R i).positiveFunctional_unit_zero hR (ξ i) (hξpos i) hi
        simp [hi,hz]
      · change weight i * ((weight i)⁻¹ * _) = _
        rw [← mul_assoc,mul_inv_cancel₀ hi,one_mul]
    simp only [hterm]
    have hx (i : s) (hi : i ∉ K) : ξ i (D (P.sequentialWordEffect p w) i) = 0 := by
      rw [← hterm]
      have hzero : weight i = 0 := by simpa [K] using hi
      simp [hzero]
    rw [Finset.sum_subset (Finset.subset_univ K) (fun i _ hi => hx i hi)]
    change ∑ i : s, ω (D (P.sequentialWordEffect p w) i).val = _
    rw [← map_sum,← hInv,D.symm_apply_apply]
  rw [← hdecomposition]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hweight i) hsumK
    (fun i hi => subset_convexHull ℝ _ (hmem i hi))

end UnitalJordanProduct
/-- The classification input states the exact existing simple-factor
classification premise for every finite-dimensional Euclidean Jordan carrier. -/
def AllSimpleFactorsAlbertOrHermitian : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z)),
    P.SimpleFactorsAlbertOrHermitian hinner

/-- The actual convex hull identity, conditional on the complete
simple-factor classification. No topological closure is taken. -/
theorem finiteJordanTables_eq_convexHull_of_classifiedFactors
    (hclass : AllSimpleFactorsAlbertOrHermitian) (n : ℕ) :
    finiteJordanTables.{0} n =
      convexHull ℝ (finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n) := by
  apply Set.Subset.antisymm _ (convexHull_projective_union_albert_subset_finiteJordan n)
  rintro f ⟨E,hE,hR,hD,P,hfr,hf⟩
  let := hE
  let := hR
  let := hD
  let B := P.canonicalTraceFormOfFormallyReal hfr
  let V := PositiveFormModel.Model E
  let C : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E B
    (P.canonicalTraceFormOfFormallyReal_symmetric hfr)
    (P.canonicalTraceFormOfFormallyReal_positive hfr)
  let : InnerProductSpace.Core ℝ V := C
  let : NormedAddCommGroup V := C.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V ≃ₗ[ℝ] E := PositiveFormModel.linearEquiv E
  let Q := P.transportProduct e
  have hinnerQ (x y z : V) : inner ℝ (Q.product x y) z = inner ℝ x (Q.product y z) := by
    change B (e (Q.product x y)) (e z) = B (e x) (e (Q.product y z))
    simpa only [Q,P.transportProduct_apply] using
      P.canonicalTraceFormOfFormallyReal_associative hfr (e x) (e y) (e z)
  have hQfr := P.transportProduct_formallyReal hfr e
  apply Q.canonicalProjectiveTables_subset_foil_of_classifiedFactors hinnerQ (hclass V Q hinnerQ) n hQfr
  obtain ⟨p,ω,hp,hpos,hunit,hw⟩ := (P.mem_canonicalProjectiveTables_iff_functional hfr).mp hf
  apply (Q.mem_canonicalProjectiveTables_iff_functional hQfr).mpr
  refine ⟨e.symm ∘ p,ω.comp e.toLinearMap,fun i => ?_,fun x => ?_,?_,fun w => ?_⟩
  · apply e.injective
    simp [Q,Function.comp_apply,hp]
  · change 0 ≤ ω (e (Q.product x x))
    dsimp only [Q]
    rw [P.transportProduct_apply]
    exact hpos _
  · change ω (e Q.unit) = 1
    dsimp only [Q]
    rw [P.transportProduct_unit,hunit]
  · change ω (e (Q.sequentialWordEffect (e.symm ∘ p) w)) = f w
    have h := Q.map_sequentialWordEffect P e.toLinearMap (P.transportProduct_unit e)
      (P.transportProduct_apply e) (e.symm ∘ p) w
    change e (Q.sequentialWordEffect (e.symm ∘ p) w) =
      P.sequentialWordEffect (e ∘ e.symm ∘ p) w at h
    rw [h]
    have hc : e ∘ e.symm ∘ p = p := funext fun i => e.apply_symm_apply (p i)
    rw [hc,hw]

/-- The foil equivalence for any linear word inequality, including all
finitely supported inequalities and arbitrary empty-word coefficients. -/
theorem finiteJordan_linear_inequality_iff_of_classifiedFactors
    (hclass : AllSimpleFactorsAlbertOrHermitian) {n : ℕ}
    (L : (Word (Fin n) → ℝ) →ₗ[ℝ] ℝ)
    (hQ : ∀ f ∈ finiteHilbertProjectiveTables.{0} ℂ n, 0 ≤ L f) :
    (∀ f ∈ finiteJordanTables.{0} n, 0 ≤ L f) ↔
      ∀ f ∈ nativeAlbertTables n, 0 ≤ L f := by
  constructor
  · intro h f hf
    exact h f (nativeAlbertTables_subset_finiteJordan n hf)
  · intro h
    rw [finiteJordanTables_eq_convexHull_of_classifiedFactors hclass n]
    have hconv : Convex ℝ {f | 0 ≤ L f} := by
      intro f hf g hg a b ha hb _
      change 0 ≤ L (a • f + b • g)
      rw [map_add,map_smul,map_smul]
      exact add_nonneg (mul_nonneg ha hf) (mul_nonneg hb hg)
    have hs : finiteHilbertProjectiveTables.{0} ℂ n ∪ nativeAlbertTables n ⊆ {f | 0 ≤ L f} :=
      Set.union_subset (fun f hf => hQ f hf) (fun f hf => h f hf)
    exact fun _ hf => convexHull_min hs hconv hf

end AlbertSequential
