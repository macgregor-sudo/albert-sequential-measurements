/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAGenerated
public import GeneralEJALowRankClassification

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (P : UnitalJordanProduct E) (p : ι → E)

/-- Definition 4.10 applied to one member of a specified menu. -/
def IsBPrimitiveTest (i : ι) : Prop :=
  let B := P.generatedMenuProduct p
  let q := P.generatedMenuTest p i
  q ≠ 0 ∧ q ≠ B.unit ∧ (B.IsPrimitive q ∨ B.IsPrimitive (B.unit-q))

theorem isBPrimitiveMenu_iff_tests :
    P.IsBPrimitiveMenu p ↔ ∀ i, p i ≠ 0 → p i ≠ P.unit → P.IsBPrimitiveTest p i := by
  constructor
  · intro hm i h0 h1
    have hn0 : P.generatedMenuTest p i ≠ 0 := fun h => h0 (congrArg Subtype.val h)
    have hn1 : P.generatedMenuTest p i ≠ (P.generatedMenuProduct p).unit := fun h => h1 (congrArg Subtype.val h)
    exact ⟨hn0,hn1,((hm i).resolve_left hn0).resolve_left hn1⟩
  · intro hm i
    by_cases h0 : p i = 0
    · exact Or.inl (Subtype.ext h0)
    by_cases h1 : p i = P.unit
    · exact Or.inr (Or.inl (Subtype.ext h1))
    exact Or.inr (Or.inr (hm i h0 h1).2.2)

theorem primitive_generated_of_ambient (x : P.generatedMenuCarrier p) (hx : P.IsPrimitive x.val) :
    (P.generatedMenuProduct p).IsPrimitive x := by
  refine ⟨Subtype.ext hx.1,fun h => hx.2.1 (congrArg Subtype.val h),?_⟩
  intro a b ha hb hab hs
  exact (hx.2.2 a.val b.val (congrArg Subtype.val ha) (congrArg Subtype.val hb)
    (congrArg Subtype.val hab) (congrArg Subtype.val hs)).imp Subtype.ext Subtype.ext

theorem isBPrimitiveTest_of_ambient (i : ι) (h0 : p i ≠ 0) (h1 : p i ≠ P.unit)
    (h : P.IsPrimitive (p i) ∨ P.IsPrimitive (P.unit-p i)) : P.IsBPrimitiveTest p i :=
  ⟨fun he => h0 (congrArg Subtype.val he), fun he => h1 (congrArg Subtype.val he),
    h.imp (P.primitive_generated_of_ambient p _) (P.primitive_generated_of_ambient p _)⟩

variable [FiniteDimensional ℝ E]

private theorem idempotent_primitive_or_large (hfr : P.FormallyReal) {x : E}
    (hx : P.product x x = x) (hn : x ≠ 0) :
    P.IsPrimitive x ∨ 2 ≤ P.canonicalTraceOfFormallyReal hfr x := by
  obtain ⟨n,c,hc,_,_,hs⟩ := P.primitive_refinement x hx
  have ht : P.canonicalTraceOfFormallyReal hfr x = n := by
    rw [← hs,map_sum]
    simp only [fun i => P.canonicalTraceOfFormallyReal_primitive hfr (c i) (hc i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  cases n with
  | zero => exact (hn (by simpa using hs.symm)).elim
  | succ k =>
    cases k with
    | zero => exact Or.inl ((show c 0 = x by simpa using hs) ▸ hc 0)
    | succ k => right; rw [ht]; exact_mod_cast (show 2 ≤ k+2 by omega)

theorem isBPrimitiveTest_of_rank_le_three (hfr : P.FormallyReal)
    (hr : P.canonicalTraceOfFormallyReal hfr P.unit ≤ 3) (i : ι)
    (hp : P.product (p i) (p i) = p i) (h0 : p i ≠ 0) (h1 : p i ≠ P.unit) :
    P.IsBPrimitiveTest p i := by
  apply P.isBPrimitiveTest_of_ambient p i h0 h1
  have hu (x : E) : P.product x P.unit = x := by rw [P.commutative,P.unit_left]
  have hh : P.product (P.unit-p i) (P.unit-p i) = P.unit-p i := by
    simp only [map_sub,LinearMap.sub_apply,P.unit_left,hu,hp]; abel
  rcases P.idempotent_primitive_or_large hfr hp h0 with h | h
  · exact Or.inl h
  rcases P.idempotent_primitive_or_large hfr hh (sub_ne_zero.mpr (Ne.symm h1)) with hc | hc
  · exact Or.inr hc
  rw [map_sub] at hc
  linarith

end AlbertSequential.UnitalJordanProduct
