/- SPDX-License-Identifier: Apache-2.0 -/
module

public import JordanSpectralResolution
public import JordanPrimitiveRefinement
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Choose

/-! Primitive frame refinement of the exact distinct spectral decomposition.
The original coefficients are retained on descendants; repeated values are
allowed here as in the printed primitive-frame statement. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem primitive_spectral_resolution
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a : E) :
    ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → E),
      (∀ i, P.IsPrimitive (c i)) ∧
      (∀ i j, i≠j → P.product (c i) (c j)=0) ∧
      (∑ i, c i)=P.unit ∧ a=∑ i, lam i • c i := by
  classical
  obtain ⟨n,lam,c,_,hc,horth,hsum,ha⟩ := P.spectral_resolution hinner a
  choose k d hd using fun i : Fin n => P.primitive_refinement (c i) (hc i).2
  let I := (i : Fin n) × Fin (k i)
  let f : I → E := fun ij => d ij.1 ij.2
  let w : I → ℝ := fun ij => lam ij.1
  have hfprim (ij : I) : P.IsPrimitive (f ij) := (hd ij.1).1 ij.2
  have hflocal (ij : I) : P.product (c ij.1) (f ij)=f ij := (hd ij.1).2.1 ij.2
  have hfortho (ij kl : I) (hne : ij≠kl) : P.product (f ij) (f kl)=0 := by
    by_cases hi : ij.1=kl.1
    · rcases ij with ⟨i,j⟩
      rcases kl with ⟨l,m⟩
      change i=l at hi
      subst l
      apply (hd i).2.2.1 j m
      exact fun h => hne (by subst m; rfl)
    · exact P.cross_corner_product_zero (c ij.1) (c kl.1) (f ij) (f kl)
        (hc ij.1).2 (hc kl.1).2 (horth ij.1 kl.1 hi) (hflocal ij) (hflocal kl)
  have hfsum : (∑ ij : I, f ij)=P.unit := by
    change (∑ ij : (i : Fin n) × Fin (k i), d ij.1 ij.2)=P.unit
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ i : Fin n, c i := Finset.sum_congr rfl (fun i _ => (hd i).2.2.2)
      _ = _ := hsum
  have hfa : a=∑ ij : I, w ij • f ij := by
    change a=∑ ij : (i : Fin n) × Fin (k i), lam ij.1 • d ij.1 ij.2
    rw [Fintype.sum_sigma]
    calc
      a = ∑ i, lam i • c i := ha
      _ = ∑ i : Fin n, lam i • ∑ j : Fin (k i), d i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(hd i).2.2.2]
      _ = _ := by simp only [Finset.smul_sum]
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun i => w (e i),fun i => f (e i),?_,?_,?_,?_⟩
  · intro i
    exact hfprim (e i)
  · intro i j hne
    exact hfortho (e i) (e j) (fun h => hne (e.injective h))
  · calc
      _ = ∑ ij : I, f ij := Equiv.sum_comp e f
      _ = _ := hfsum
  · rw [hfa]
    exact (Equiv.sum_comp e (fun ij : I => w ij • f ij)).symm

end AlbertSequential.UnitalJordanProduct
