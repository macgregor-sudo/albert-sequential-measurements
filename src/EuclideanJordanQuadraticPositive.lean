/- SPDX-License-Identifier: Apache-2.0 -/
module
public import EuclideanJordanSquareCone
public import EuclideanPrimitiveCorner
public import JordanPrimitiveSpectralResolution

/-! Quadratic maps preserve actual squares in finite positive-form Jordan data.
Primitive-ray positivity is proved from FF and exact primitive compression,
not a rank/classification/trace-normalization premise. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

theorem orthogonal_expansion_product_component {ι : Type*} [Fintype ι]
    (c : ι→E) (lam : ι→ℝ) (hc : ∀ i, P.product (c i) (c i)=c i)
    (horth : ∀ i j, i≠j → P.product (c i) (c j)=0) (i : ι) :
    P.product (∑ j,lam j • c j) (c i)=lam i • c i := by
  classical
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply]
  rw [Finset.sum_eq_single i]
  · rw [hc i]
  · intro j _ hji
    rw [horth j i hji,smul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem quadraticRepresentation_orthogonal_component {ι : Type*} [Fintype ι]
    (c : ι→E) (lam : ι→ℝ) (hc : ∀ i, P.product (c i) (c i)=c i)
    (horth : ∀ i j, i≠j → P.product (c i) (c j)=0) (i : ι) :
    P.quadraticRepresentation (∑ j,lam j • c j) (c i)=(lam i)^2 • c i := by
  let a := ∑ j,lam j • c j
  have hi : P.product a (c i)=lam i • c i :=
    P.orthogonal_expansion_product_component c lam hc horth i
  have hs : P.product (P.product a a) (c i)=(lam i)^2 • c i := by
    dsimp only [a]
    rw [P.square_of_orthogonal_expansion c lam hc horth,
      P.orthogonal_expansion_product_component c (fun j => (lam j)^2) hc horth i]
  change P.quadraticRepresentation a (c i)=_
  rw [P.quadraticRepresentation_apply,hi,map_smul,hi,hs]
  simp only [smul_smul,pow_two]
  module

end AlbertSequential.UnitalJordanProduct

namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

/-- Literal scalar range, with the actual primitive norm denominator retained. -/
theorem primitive_image_quadraticRepresentation_scalar
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a q z : E) (hq : P.IsPrimitive q) :
    P.quadraticRepresentation (P.quadraticRepresentation a q) z=
      (inner ℝ q (P.quadraticRepresentation a z)/inner ℝ q q) •
        P.quadraticRepresentation a q := by
  rw [P.quadraticRepresentation_fundamental,
    P.primitive_quadraticRepresentation_coefficient hinner q _ hq,map_smul]

/-- A primitive image is zero or an explicitly proved positive primitive ray. -/
theorem primitive_image_zero_or_positive_ray
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a q : E) (hq : P.IsPrimitive q) :
    P.quadraticRepresentation a q=0 ∨
      ∃ (r : E) (t : ℝ), P.IsPrimitive r ∧ 0<t ∧
        P.quadraticRepresentation a q=t • r := by
  classical
  let x := P.quadraticRepresentation a q
  change x=0 ∨ ∃ (r : E) (t : ℝ), P.IsPrimitive r ∧ 0<t ∧ x=t • r
  by_cases hx : x=0
  · exact Or.inl hx
  right
  obtain ⟨n,lam,c,hc,horth,_,hres⟩ := P.primitive_spectral_resolution hinner x
  have hex : ∃ i, lam i≠0 := by
    by_contra hn
    have hall (i : Fin n) : lam i=0 := by
      by_contra hi
      exact hn ⟨i,hi⟩
    apply hx
    rw [hres]
    simp only [hall,zero_smul,Finset.sum_const_zero]
  obtain ⟨i,hli⟩ := hex
  have heigen : P.quadraticRepresentation x (c i)=(lam i)^2 • c i := by
    rw [hres]
    exact P.quadraticRepresentation_orthogonal_component c lam (fun j => (hc j).1) horth i
  let t := inner ℝ q (P.quadraticRepresentation a (c i))/inner ℝ q q
  have hrange : P.quadraticRepresentation x (c i)=t • x :=
    P.primitive_image_quadraticRepresentation_scalar hinner a q (c i) hq
  have himage : (lam i)^2 • c i=t • x := heigen.symm.trans hrange
  have hN : 0 < inner ℝ (c i) (c i) := real_inner_self_pos.mpr (hc i).2.1
  have hinnerEq := congrArg (fun v : E => inner ℝ v (c i)) himage
  simp only [real_inner_smul_left] at hinnerEq
  rw [hres,P.orthogonal_expansion_inner_component hinner c lam horth i] at hinnerEq
  have hprod : ((lam i-t)*lam i)*inner ℝ (c i) (c i)=0 := by
    nlinarith [hinnerEq]
  have hfirst : (lam i-t)*lam i=0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hN)
  have hdiff : lam i-t=0 := (mul_eq_zero.mp hfirst).resolve_right hli
  have ht : t=lam i := (sub_eq_zero.mp hdiff).symm
  have hscaled := congrArg (fun v : E => (lam i)⁻¹ • v) himage
  rw [ht] at hscaled
  simp only [smul_smul] at hscaled
  have hcoef : (lam i)⁻¹*(lam i)^2=lam i := by
    rw [pow_two,← mul_assoc,inv_mul_cancel₀ hli,one_mul]
  rw [hcoef,inv_mul_cancel₀ hli,one_smul] at hscaled
  have hxray : x=lam i • c i := hscaled.symm
  have hmass : 0 ≤ inner ℝ x P.unit := by
    change 0 ≤ inner ℝ (P.quadraticRepresentation a q) P.unit
    rw [P.quadraticRepresentation_inner hinner a q P.unit,
      P.quadraticRepresentation_unit]
    exact P.idempotent_inner_square_nonneg hinner q a hq.1
  have hcunit : inner ℝ (c i) P.unit=inner ℝ (c i) (c i) := by
    simpa only [(hc i).1] using P.square_inner_unit hinner (c i)
  rw [hxray,real_inner_smul_left,hcunit] at hmass
  have hnonneg : 0≤lam i := nonneg_of_mul_nonneg_left hmass hN
  have hpos : 0<lam i := lt_of_le_of_ne hnonneg hli.symm
  exact ⟨c i,lam i,hc i,hpos,hxray⟩

theorem primitive_image_mem_squareCone
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a q : E) (hq : P.IsPrimitive q) : P.quadraticRepresentation a q∈P.squareCone := by
  rcases P.primitive_image_zero_or_positive_ray hinner a q hq with hz | ⟨r,t,hr,ht,himage⟩
  · rw [hz]
    exact P.zero_mem_squareCone
  · rw [himage]
    exact P.nonnegative_smul_mem_squareCone r ⟨r,hr.1.symm⟩ t ht.le

theorem sum_mem_squareCone {ι : Type*}
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (s : Finset ι) (f : ι→E) (hf : ∀ i∈s,f i∈P.squareCone) :
    (∑ i∈s,f i)∈P.squareCone := by
  let C : AddSubmonoid E :=
    { carrier := P.squareCone
      zero_mem' := P.zero_mem_squareCone
      add_mem' := fun hx hy => P.add_mem_squareCone hinner _ _ hx hy }
  exact C.sum_mem hf

/-- All filters a preserve actual squares, including negative/singular filters. -/
theorem quadraticRepresentation_preserves_squareCone
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a b : E) (hb : b∈P.squareCone) : P.quadraticRepresentation a b∈P.squareCone := by
  obtain ⟨y,rfl⟩ := hb
  obtain ⟨n,lam,c,hc,horth,_,hy⟩ := P.primitive_spectral_resolution hinner y
  rw [hy,P.square_of_orthogonal_expansion c lam (fun i => (hc i).1) horth,map_sum]
  apply P.sum_mem_squareCone hinner Finset.univ
  intro i _
  rw [map_smul]
  exact P.nonnegative_smul_mem_squareCone _
    (P.primitive_image_mem_squareCone hinner a (c i) (hc i)) ((lam i)^2) (sq_nonneg _)

end AlbertSequential.UnitalJordanProduct
