/- SPDX-License-Identifier: Apache-2.0 -/
module

public import JordanPeirceFusion
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Push

/-! Finite-dimensional primitive refinement by strict corner-dimension descent.
Neither a spectral theorem nor a trace/classification premise is assumed. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

def IsPrimitiveRefinement {n : ℕ} (q : E) (c : Fin n → E) : Prop :=
  (∀ i, P.IsPrimitive (c i)) ∧ (∀ i, P.product q (c i)=c i) ∧
  (∀ i j, i≠j → P.product (c i) (c j)=0) ∧ (∑ i, c i)=q

theorem primitive_refinement [FiniteDimensional ℝ E] (q : E)
    (hq : P.product q q=q) : ∃ (n : ℕ) (c : Fin n → E), P.IsPrimitiveRefinement q c := by
  classical
  let R (q : E) := ∃ (n : ℕ) (c : Fin n → E), P.IsPrimitiveRefinement q c
  suffices H : ∀ k : ℕ, ∀ q : E, P.product q q=q →
      Module.finrank ℝ (P.peirceOne q)=k → R q from H _ q hq rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro q hq hdim
    by_cases hq0 : q=0
    · refine ⟨0,Fin.elim0,?_,?_,?_,?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · simp only [Fin.sum_univ_zero,hq0]
    by_cases hprim : P.IsPrimitive q
    · refine ⟨1,fun _ => q,(fun _ => hprim),(fun _ => hq),?_,?_⟩
      · intro i j hij
        exact (hij (Subsingleton.elim i j)).elim
      · simp only [Fin.sum_univ_one]
    have hsplit : ∃ r s : E, P.product r r=r ∧ P.product s s=s ∧
        P.product r s=0 ∧ r+s=q ∧ r≠0 ∧ s≠0 := by
      have hnot : ¬∀ r s : E, P.product r r=r → P.product s s=s →
          P.product r s=0 → r+s=q → r=0 ∨ s=0 := fun h => hprim ⟨hq,hq0,h⟩
      push Not at hnot
      exact hnot
    obtain ⟨r,s,hr,hs,hrs,hsum,hr0,hs0⟩ := hsplit
    have hsr : P.product s r=0 := by rw [P.commutative,hrs]
    have hsum' : s+r=q := by rw [add_comm,hsum]
    have hrdim : Module.finrank ℝ (P.peirceOne r)<k := by
      simpa only [hdim] using P.corner_finrank_lt_of_orthogonal_sum r s q hr hs hrs hsum hs0
    have hsdim : Module.finrank ℝ (P.peirceOne s)<k := by
      simpa only [hdim] using P.corner_finrank_lt_of_orthogonal_sum s r q hs hr hsr hsum' hr0
    obtain ⟨nr,cr,hrprim,hrlocal,hrorth,hrsum⟩ := ih _ hrdim r hr rfl
    obtain ⟨ns,cs,hsprim,hslocal,hsorth,hssum⟩ := ih _ hsdim s hs rfl
    let C : Fin (nr+ns) → E := Fin.addCases cr cs
    have hrQ (i : Fin nr) : P.product q (cr i)=cr i :=
      (P.mem_peirceOne q _).mp
        (P.corner_le_of_orthogonal_sum r s q hr hrs hsum
          ((P.mem_peirceOne r _).mpr (hrlocal i)))
    have hsQ (i : Fin ns) : P.product q (cs i)=cs i :=
      (P.mem_peirceOne q _).mp
        (P.corner_le_of_orthogonal_sum s r q hs hsr hsum'
          ((P.mem_peirceOne s _).mpr (hslocal i)))
    refine ⟨nr+ns,C,?_,?_,?_,?_⟩
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        simpa only [C,Fin.addCases_left] using hrprim i
      · intro i
        simpa only [C,Fin.addCases_right] using hsprim i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        simpa only [C,Fin.addCases_left] using hrQ i
      · intro i
        simpa only [C,Fin.addCases_right] using hsQ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i j
        refine Fin.addCases ?_ ?_ j
        · intro j hij
          simpa only [C,Fin.addCases_left] using
            hrorth i j (fun h => hij (congrArg (Fin.castAdd ns) h))
        · intro j _
          simpa only [C,Fin.addCases_left,Fin.addCases_right] using
            P.cross_corner_product_zero r s (cr i) (cs j) hr hs hrs (hrlocal i) (hslocal j)
      · intro i j
        refine Fin.addCases ?_ ?_ j
        · intro j _
          simpa only [C,Fin.addCases_left,Fin.addCases_right] using
            P.cross_corner_product_zero s r (cs i) (cr j) hs hr hsr (hslocal i) (hrlocal j)
        · intro j hij
          simpa only [C,Fin.addCases_right] using
            hsorth i j (fun h => hij (congrArg (Fin.natAdd nr) h))
    · simp only [C,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
      rw [hrsum,hssum,hsum]

end AlbertSequential.UnitalJordanProduct
