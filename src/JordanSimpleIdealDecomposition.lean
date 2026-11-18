/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanIdealRestriction

/-! Minimum-dimensional nonzero ideals give a finite orthogonal family of
genuinely simple unital factors, without classifying those factors. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem exists_minimal_nonzero_jordanIdeal (J : Submodule ℝ E)
    (hJ : P.IsJordanIdeal J) (hne : J≠⊥) :
    ∃ I : Submodule ℝ E,I≤J ∧ P.IsSimpleJordanIdeal I := by
  classical
  let prop : ℕ→Prop := fun n => ∃ I : Submodule ℝ E,
    P.IsJordanIdeal I ∧ I≠⊥ ∧ I≤J ∧ Module.finrank ℝ I=n
  have hex : ∃ n,prop n := ⟨Module.finrank ℝ J,J,hJ,hne,le_rfl,rfl⟩
  obtain ⟨I,hI,hI0,hIJ,hdim⟩ := Nat.find_spec hex
  refine ⟨I,hIJ,hI,hI0,?_⟩
  intro K hK hKI
  by_cases hK0 : K=⊥
  · exact Or.inl hK0
  · right
    have hmin : Module.finrank ℝ I≤Module.finrank ℝ K := by
      rw [hdim]
      exact Nat.find_min' hex ⟨K,hK,hK0,hKI.trans hIJ,rfl⟩
    exact Submodule.eq_of_le_of_finrank_eq hKI
      (Nat.le_antisymm (Submodule.finrank_mono hKI) hmin)

theorem exists_simpleIdeal_decomposition
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (J : Submodule ℝ E) (hJ : P.IsJordanIdeal J) :
    ∃ s : Finset (Submodule ℝ E),
      (∀ I∈s,P.IsSimpleJordanIdeal I ∧ I≤J) ∧
      (∀ I∈s,∀ K∈s,I≠K → I≤Kᗮ) ∧ s.sup id=J := by
  classical
  suffices H : ∀ n,∀ J : Submodule ℝ E,Module.finrank ℝ J=n → P.IsJordanIdeal J →
      ∃ s : Finset (Submodule ℝ E),
        (∀ I∈s,P.IsSimpleJordanIdeal I ∧ I≤J) ∧
        (∀ I∈s,∀ K∈s,I≠K → I≤Kᗮ) ∧ s.sup id=J by
    exact H _ J rfl hJ
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro J hdim hJ
    by_cases hJ0 : J=⊥
    · subst J
      exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨I,hIJ,hI⟩ := P.exists_minimal_nonzero_jordanIdeal J hJ hJ0
    let R : Submodule ℝ E := Iᗮ⊓J
    have hR : P.IsJordanIdeal R := P.isJordanIdeal_inf _ _
      (P.isJordanIdeal_orthogonal hinner I hI.1) hJ
    have hRdim : Module.finrank ℝ R<n := by
      have hsum := Submodule.finrank_add_inf_finrank_orthogonal hIJ
      have hIpos : 0<Module.finrank ℝ I := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact hI.2.1 (Submodule.finrank_eq_zero.mp hz)
      change Module.finrank ℝ I+Module.finrank ℝ R=Module.finrank ℝ J at hsum
      omega
    obtain ⟨s,hs,horth,hsup⟩ := ih _ hRdim R rfl hR
    refine ⟨insert I s,?_,?_,?_⟩
    · intro K hK
      rcases Finset.mem_insert.mp hK with rfl | hK
      · exact ⟨hI,hIJ⟩
      · exact ⟨(hs K hK).1,(hs K hK).2.trans inf_le_right⟩
    · intro K hK L hL hKL
      rcases Finset.mem_insert.mp hK with hKeq | hKold
      · rcases Finset.mem_insert.mp hL with hLeq | hLold
        · exact (hKL (hKeq.trans hLeq.symm)).elim
        · rw [hKeq]
          exact Submodule.le_orthogonal_iff_le_orthogonal.mpr ((hs L hLold).2.trans inf_le_left)
      · rcases Finset.mem_insert.mp hL with hLeq | hLold
        · rw [hLeq]
          exact (hs K hKold).2.trans inf_le_left
        · exact horth K hKold L hLold hKL
    · rw [Finset.sup_insert,hsup]
      exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hIJ

theorem exists_simpleIdeal_decomposition_top
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    ∃ s : Finset (Submodule ℝ E),
      (∀ I∈s,P.IsSimpleJordanIdeal I) ∧
      (∀ I∈s,∀ K∈s,I≠K → I≤Kᗮ) ∧ s.sup id=⊤ := by
  obtain ⟨s,hs,ho,ht⟩ := P.exists_simpleIdeal_decomposition hinner ⊤ P.isJordanIdeal_top
  exact ⟨s,fun I hI => (hs I hI).1,ho,ht⟩

theorem exists_genuine_simple_factor_decomposition
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    ∃ (s : Finset (Submodule ℝ E)) (hs : ∀ I∈s,P.IsJordanIdeal I),
      (∀ I∈s,I≠⊥) ∧
      (∀ I∈s,∀ K∈s,I≠K → I≤Kᗮ) ∧ s.sup id=⊤ ∧
      ∀ I (hI : I∈s),(P.orthogonalIdealProduct hinner I (hs I hI)).IsSimpleJordan := by
  obtain ⟨s,hs,ho,ht⟩ := P.exists_simpleIdeal_decomposition_top hinner
  refine ⟨s,fun I hI => (hs I hI).1,fun I hI => (hs I hI).2.1,ho,ht,?_⟩
  intro I hI
  exact (P.simple_ideal_iff_restricted_simple hinner I (hs I hI).1).mp (hs I hI)

end AlbertSequential.UnitalJordanProduct
