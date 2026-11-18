/- SPDX-License-Identifier: Apache-2.0 -/
module

public import UnitalJordanProduct
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The E1*E0 fusion rule and proper corner inclusions from actual Jordan
polarization. No Peirce grading or primitive refinement is an assumed field. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

theorem peirceOne_zero_product (q x y : E) (hq : P.product q q=q)
    (hx : P.product q x=x) (hy : P.product q y=0) : P.product x y=0 := by
  have hqxy : P.product q (P.product x y)=0 := by
    rw [P.peirceOne_commute q x y hq hx,hy,map_zero]
  have h := P.cyclic_identity q x y q
  simpa only [P.commutative y q,hy,P.commutative x q,hx,hq,
    P.commutative (P.product x y) q,hqxy,map_zero,LinearMap.zero_apply,
    sub_zero,zero_sub,zero_add,add_zero,P.commutative y x] using h

theorem cross_corner_product_zero (r s x y : E) (hr : P.product r r=r)
    (hs : P.product s s=s) (hrs : P.product r s=0)
    (hx : P.product r x=x) (hy : P.product s y=y) : P.product x y=0 := by
  have hsr : P.product s r=0 := by rw [P.commutative,hrs]
  have hry : P.product r y=0 := by
    rw [P.commutative]
    exact P.peirceOne_zero_product s y r hs hy hsr
  exact P.peirceOne_zero_product r x y hr hx hry

theorem corner_le_of_orthogonal_sum (r s q : E) (hr : P.product r r=r)
    (hrs : P.product r s=0) (hsum : r+s=q) : P.peirceOne r≤P.peirceOne q := by
  intro x hx
  rw [P.mem_peirceOne] at hx ⊢
  have hxs : P.product x s=0 := P.peirceOne_zero_product r x s hr hx hrs
  rw [← hsum,map_add,LinearMap.add_apply,hx,P.commutative s x,hxs,add_zero]

theorem corner_lt_of_orthogonal_sum (r s q : E) (hr : P.product r r=r)
    (hs : P.product s s=s) (hrs : P.product r s=0) (hsum : r+s=q)
    (hs0 : s≠0) : P.peirceOne r<P.peirceOne q := by
  apply lt_of_le_of_ne (P.corner_le_of_orthogonal_sum r s q hr hrs hsum)
  intro heq
  have hsQ : s∈P.peirceOne q := by
    rw [P.mem_peirceOne,← hsum,map_add,LinearMap.add_apply,hrs,hs,zero_add]
  have hsR : s∈P.peirceOne r := by rw [heq]; exact hsQ
  have hfixed := (P.mem_peirceOne r s).mp hsR
  rw [hrs] at hfixed
  exact hs0 hfixed.symm

theorem corner_finrank_lt_of_orthogonal_sum [FiniteDimensional ℝ E]
    (r s q : E) (hr : P.product r r=r) (hs : P.product s s=s)
    (hrs : P.product r s=0) (hsum : r+s=q) (hs0 : s≠0) :
    Module.finrank ℝ (P.peirceOne r)<Module.finrank ℝ (P.peirceOne q) :=
  Submodule.finrank_lt_finrank_of_lt
    (P.corner_lt_of_orthogonal_sum r s q hr hs hrs hsum hs0)

end AlbertSequential.UnitalJordanProduct
