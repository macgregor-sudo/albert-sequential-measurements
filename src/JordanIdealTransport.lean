/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanIdeals
public import JordanProductTransport

/-! Actual algebraic Jordan-ideal/simple-factor transport. Only genuine
product-preserving linear equivalences are used, with no norm assumption. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] (P : UnitalJordanProduct E)

theorem isJordanIdeal_comap_equiv (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) :
    Q.IsJordanIdeal (I.comap e.toLinearMap) := by
  intro x hx y
  change e (Q.product y x)∈I
  rw [he]
  exact hI (e x) hx (e y)

theorem isJordanIdeal_map_equiv (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y))
    (I : Submodule ℝ F) (hI : Q.IsJordanIdeal I) :
    P.IsJordanIdeal (I.map e.toLinearMap) := by
  rintro x ⟨a,ha,rfl⟩ y
  refine ⟨Q.product (e.symm y) a,hI a ha (e.symm y),?_⟩
  change e (Q.product (e.symm y) a)=P.product y (e a)
  rw [he,LinearEquiv.apply_symm_apply]

theorem simpleJordanIdeal_map_equiv (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y))
    (I : Submodule ℝ F) (hI : Q.IsSimpleJordanIdeal I) :
    P.IsSimpleJordanIdeal (I.map e.toLinearMap) := by
  refine ⟨P.isJordanIdeal_map_equiv Q e he I hI.1,?_,?_⟩
  · intro hbot
    apply hI.2.1
    apply (Submodule.eq_bot_iff I).mpr
    intro x hx
    have hm : e x∈I.map e.toLinearMap := ⟨x,hx,rfl⟩
    rw [hbot] at hm
    exact e.injective (hm.trans (map_zero e).symm)
  · intro K hK hKI
    let L := K.comap e.toLinearMap
    have hL : Q.IsJordanIdeal L := P.isJordanIdeal_comap_equiv Q e he K hK
    have hLI : L≤I := by
      intro x hx
      obtain ⟨y,hy,hey⟩ := hKI hx
      exact (e.injective hey) ▸ hy
    have hback : L.map e.toLinearMap=K := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
        change e (e.symm x)∈K
        simpa only [LinearEquiv.apply_symm_apply] using hx
    rcases hI.2.2 L hL hLI with hbot | htop
    · left
      rw [← hback,hbot,Submodule.map_bot]
    · right
      rw [← hback,htop]

theorem isSimpleJordan_iff_top_simpleIdeal :
    P.IsSimpleJordan ↔ P.IsSimpleJordanIdeal (⊤ : Submodule ℝ E) := by
  constructor
  · rintro ⟨hu,hminimal⟩
    refine ⟨P.isJordanIdeal_top,?_,fun I hI _ => hminimal I hI⟩
    intro hbot
    have hm : P.unit∈(⊤ : Submodule ℝ E) := trivial
    exact hu ((le_of_eq hbot) hm)
  · rintro ⟨_,hne,hminimal⟩
    refine ⟨?_,fun I hI => hminimal I hI le_top⟩
    intro hu
    apply hne
    apply (Submodule.eq_bot_iff _).mpr
    intro x _
    have h := P.unit_left x
    rw [hu,P.product.map_zero,LinearMap.zero_apply] at h
    exact h.symm

theorem isSimpleJordan_linearEquiv (Q : UnitalJordanProduct F) (e : F ≃ₗ[ℝ] E)
    (he : ∀ x y,e (Q.product x y)=P.product (e x) (e y))
    (hQ : Q.IsSimpleJordan) : P.IsSimpleJordan := by
  have htop := P.simpleJordanIdeal_map_equiv Q e he ⊤ (Q.isSimpleJordan_iff_top_simpleIdeal.mp hQ)
  have hmap : (⊤ : Submodule ℝ F).map e.toLinearMap=⊤ := by
    apply top_unique
    intro x _
    exact ⟨e.symm x,trivial,e.apply_symm_apply x⟩
  rw [hmap] at htop
  exact P.isSimpleJordan_iff_top_simpleIdeal.mpr htop

end AlbertSequential.UnitalJordanProduct
