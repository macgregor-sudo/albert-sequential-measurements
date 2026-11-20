/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ClassifiedJordanFoil
public import GeneralEJAClassifiedTables

/-! The finite family summed over in core 4.16 exists intrinsically. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))

private theorem AlbertIdeal.no_special_subfactor (J : P.AlbertIdeal) (K : Submodule ℝ E)
    (hK : P.IsJordanIdeal K) (hne : K ≠ ⊥) (hle : K ≤ J.carrier) (d : ℕ)
    (M : FaithfulHermitianJordanEmbedding (P.orthogonalIdealProduct hinner K hK) d) : False := by
  let f := M.map.comp (K.orthogonalProjectionOnto.toLinearMap.comp J.inclusion)
  have hf : IsJordanHom f := by
    intro x y
    change M.map (K.orthogonalProjectionOnto (J.inclusion (jordanMul x y))) = _
    rw [← J.inclusion_product hinner, P.idealProjection_product_subtype hinner K hK, M.jordan]
    rfl
  have hz := albertJordanHom_eq_zero _ f hf
  apply hne
  apply le_antisymm _ bot_le
  intro x hx
  have he := LinearMap.congr_fun hz (J.projection x)
  change M.map (K.orthogonalProjectionOnto (J.inclusion (J.projection x))) = 0 at he
  rw [J.inclusion_projection_of_mem (hle hx)] at he
  have he' := M.injective (he.trans M.map.map_zero.symm)
  change x = 0
  exact (K.starProjection_eq_self_iff.mpr hx).symm.trans (congrArg Subtype.val he')

include hinner in
/-- The family contains exactly the distinct carriers of all native exceptional ideals. -/
theorem exists_complete_exceptional_ideal_family :
    ∃ (k : ℕ) (I : Fin k → P.AlbertIdeal),
      (∀ i j, i ≠ j → (I i).carrier ≤ (I j).carrierᗮ) ∧
      (∀ J : P.AlbertIdeal, ∃ i, (I i).carrier = J.carrier) := by
  classical
  obtain ⟨s,hI,_,hs,ho,_,_,_,_,_,hu,_⟩ := P.exists_simple_unital_product_equivalence hinner
  let t := s.filter (fun K => ∃ J : P.AlbertIdeal, J.carrier = K)
  have ht (i : t) := (Finset.mem_filter.mp i.property).2
  let e := Fintype.equivFin t
  let I (i : Fin (Fintype.card t)) := (ht (e.symm i)).choose
  have hc (i) : (I i).carrier = (e.symm i).val := (ht _).choose_spec
  refine ⟨_,I,?_,?_⟩
  · intro i j hij
    rw [hc,hc]
    exact ho _ (Finset.mem_filter.mp (e.symm i).property).1 _
      (Finset.mem_filter.mp (e.symm j).property).1 (fun h => hij (e.symm.injective (Subtype.ext h)))
  · intro J
    have hx : J.inclusion albertUnit ≠ 0 := by
      intro h
      have he := congrArg J.projection h
      rw [J.projection_inclusion,map_zero] at he
      have ha := congrArg (fun a : Albert => a.1 0) he
      exact one_ne_zero (show (1 : ℝ) = 0 from ha)
    let x := J.inclusion albertUnit
    have hsum : (∑ i : s, P.product x (P.idealUnit i.val)) ≠ 0 := by
      rw [← map_sum,hu,P.commutative,P.unit_left]
      exact hx
    obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    let K := i.val
    have hsK := hs K i.property
    have hle : K ≤ J.carrier := by
      rcases hsK.2.2 (K ⊓ J.carrier) (P.isJordanIdeal_inf _ _ hsK.1 J.isIdeal) inf_le_left with h | h
      · exfalso
        apply hi
        have hm : P.product x (P.idealUnit K) ∈ K ⊓ J.carrier :=
          ⟨hsK.1 _ (P.idealUnit_mem _) _, by rw [P.commutative]; exact J.isIdeal _ (J.inclusion_mem _) _⟩
        simpa [h] using hm
      · exact h.symm.le.trans inf_le_right
    rcases P.simpleFactorsAlbertOrHermitian_native hinner K hsK with ⟨L,hL⟩ | ⟨d,⟨M⟩⟩
    · have hdim : Module.finrank ℝ K = Module.finrank ℝ J.carrier := by
        rw [← hL,L.identify.finrank_eq,J.identify.finrank_eq]
      have he := Submodule.eq_of_le_of_finrank_eq hle hdim
      let j : t := ⟨K, Finset.mem_filter.mpr ⟨i.property,⟨L,hL⟩⟩⟩
      exact ⟨e j,(hc _).trans (by simpa [j] using he)⟩
    · exact (AlbertIdeal.no_special_subfactor P hinner J _ hsK.1 hsK.2.1 hle d M).elim

end AlbertSequential.UnitalJordanProduct
