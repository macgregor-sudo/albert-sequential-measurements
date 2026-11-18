/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanSimpleIdealDecomposition
public import JordanIdealProjections
public import OrthogonalSubspaceComponents

/-! Actual simple unital factors, actual product equivalence and componentwise
quadratic updates. No identification/classification of the factors is made. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem exists_simple_unital_product_equivalence
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    ∃ (s : Finset (Submodule ℝ E)) (hI : ∀ I∈s,P.IsJordanIdeal I)
      (e : E ≃ₗ[ℝ] ((i : s) → (i.val : Submodule ℝ E))),
      (∀ I∈s,P.IsSimpleJordanIdeal I) ∧
      (∀ I∈s,∀ K∈s,I≠K → I≤Kᗮ) ∧ s.sup id=⊤ ∧
      (∀ i : s,(P.orthogonalIdealProduct hinner i.val (hI i.val i.property)).IsSimpleJordan) ∧
      (∀ x y (i : s),e (P.product x y) i=
        (P.orthogonalIdealProduct hinner i.val (hI i.val i.property)).product (e x i) (e y i)) ∧
      e P.unit=(fun i : s => (P.orthogonalIdealProduct hinner i.val (hI i.val i.property)).unit) ∧
      (∀ a x (i : s),e (P.quadraticRepresentation a x) i=
        (P.orthogonalIdealProduct hinner i.val (hI i.val i.property)).quadraticRepresentation (e a i) (e x i)) ∧
      (∑ i : s,P.idealUnit i.val)=P.unit ∧
      (∀ v : ((i : s) → (i.val : Submodule ℝ E)),e.symm v=∑ i,(v i).val) := by
  classical
  obtain ⟨s,hs,horth,htop⟩ := P.exists_simpleIdeal_decomposition_top hinner
  let hI : ∀ I∈s,P.IsJordanIdeal I := fun I hI => (hs I hI).1
  let spaces : s → Submodule ℝ E := fun i => i.val
  have ho : ∀ i j : s,i≠j → spaces i≤(spaces j)ᗮ := by
    intro i j hij
    exact horth i.val i.property j.val j.property (fun h => hij (Subtype.ext h))
  have ht : (⨆ i : s,spaces i)=⊤ := by
    simpa only [spaces,iSup_subtype,Finset.sup_eq_iSup,id_eq] using htop
  let e := OrthogonalSubspaceComponents.decompositionEquiv spaces ho ht
  refine ⟨s,hI,e,hs,horth,htop,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact (P.simple_ideal_iff_restricted_simple hinner i.val (hI i.val i.property)).mp (hs i.val i.property)
  · intro x y i
    exact P.idealProjection_product_subtype hinner i.val (hI i.val i.property) x y
  · funext i
    exact P.idealProjection_unit_subtype hinner i.val (hI i.val i.property)
  · intro a x i
    exact P.idealProjection_quadraticRepresentation hinner i.val (hI i.val i.property) a x
  · exact OrthogonalSubspaceComponents.sumComponents_components spaces ho ht P.unit
  · intro v
    rfl

end AlbertSequential.UnitalJordanProduct
