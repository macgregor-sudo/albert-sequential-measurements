/- SPDX-License-Identifier: Apache-2.0 -/
module
public import JordanIdealOrthogonal

/-! Ideals of the actual restricted unital product correspond to ambient
Jordan ideals below that subspace. Thus simplicity is genuine factor simplicity. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem restricted_ideal_comap
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (K : Submodule ℝ E)
    (hK : P.IsJordanIdeal K) :
    (P.orthogonalIdealProduct hinner I hI).IsJordanIdeal (K.comap I.subtype) := by
  intro x hx y
  exact hK x.val hx y.val

theorem restricted_ideal_map
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (K : Submodule ℝ I)
    (hK : (P.orthogonalIdealProduct hinner I hI).IsJordanIdeal K) :
    P.IsJordanIdeal (K.map I.subtype) := by
  rintro x ⟨a,ha,rfl⟩ y
  let yI := I.orthogonalProjectionOnto y
  have hzero := P.ideal_orthogonal_product_zero hinner I hI a.val
    (y-I.starProjection y) a.property (I.sub_starProjection_mem_orthogonal y)
  rw [P.commutative a.val (y-I.starProjection y),P.product.map_sub,LinearMap.sub_apply] at hzero
  refine ⟨(P.orthogonalIdealProduct hinner I hI).product yI a,hK a ha yI,?_⟩
  exact (sub_eq_zero.mp hzero).symm

theorem subtype_map_comap_eq (I K : Submodule ℝ E) (hKI : K≤I) :
    (K.comap I.subtype).map I.subtype=K := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x,hKI hx⟩,hx,rfl⟩

theorem subtype_comap_map_eq (I : Submodule ℝ E) (K : Submodule ℝ I) :
    (K.map I.subtype).comap I.subtype=K := by
  ext x
  constructor
  · rintro ⟨y,hy,hval⟩
    have heq : y=x := Subtype.ext hval
    exact heq ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem idealUnit_ne_zero
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) (hne : I≠⊥) : P.idealUnit I≠0 := by
  intro hu
  apply hne
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have h := P.idealUnit_left hinner I hI x hx
  rw [hu,P.product.map_zero,LinearMap.zero_apply] at h
  exact h.symm

theorem simple_ideal_iff_restricted_simple
    (hinner : ∀ x y z,inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (I : Submodule ℝ E) (hI : P.IsJordanIdeal I) :
    P.IsSimpleJordanIdeal I ↔ (P.orthogonalIdealProduct hinner I hI).IsSimpleJordan := by
  constructor
  · rintro ⟨_,hne,hminimal⟩
    refine ⟨?_,?_⟩
    · intro hu
      exact P.idealUnit_ne_zero hinner I hI hne (congrArg Subtype.val hu)
    · intro K hK
      have hmap := P.restricted_ideal_map hinner I hI K hK
      have hle : K.map I.subtype≤I := by rintro x ⟨y,_,rfl⟩; exact y.property
      rcases hminimal (K.map I.subtype) hmap hle with hbot | htop
      · left
        apply (Submodule.eq_bot_iff _).mpr
        intro x hx
        have hm : x.val∈K.map I.subtype := ⟨x,hx,rfl⟩
        rw [hbot] at hm
        exact Subtype.ext hm
      · right
        apply top_unique
        intro x _
        have hm : x.val∈K.map I.subtype := by rw [htop]; exact x.property
        obtain ⟨y,hy,hval⟩ := hm
        exact (Subtype.ext hval : y=x) ▸ hy
  · rintro ⟨hu,hminimal⟩
    refine ⟨hI,?_,?_⟩
    · intro hbot
      have hm := (le_of_eq hbot) (P.idealUnit_mem I)
      apply hu
      exact Subtype.ext hm
    · intro K hK hKI
      have hcomap := P.restricted_ideal_comap hinner I hI K hK
      rcases hminimal (K.comap I.subtype) hcomap with hbot | htop
      · left
        apply (Submodule.eq_bot_iff _).mpr
        intro x hx
        have hm : (⟨x,hKI hx⟩ : I)∈K.comap I.subtype := hx
        rw [hbot] at hm
        exact congrArg Subtype.val hm
      · right
        apply le_antisymm hKI
        intro x hx
        have hm : (⟨x,hx⟩ : I)∈K.comap I.subtype := by rw [htop]; trivial
        exact hm

end AlbertSequential.UnitalJordanProduct
