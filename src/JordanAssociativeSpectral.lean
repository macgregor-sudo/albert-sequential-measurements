/- SPDX-License-Identifier: Apache-2.0 -/
module

public import EuclideanJordanForm
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! A self-adjoint multiplication operator resolves the unit into orthogonal
idempotents in an associative Jordan subalgebra. All products remain literal. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
open Module.End
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem associative_spectral_resolution
    (hprod : ∀ x y z, P.product (P.product x y) z=P.product x (P.product y z))
    (hinner : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (a : E) :
    ∃ (n : ℕ) (lam : Fin n → ℝ) (c : Fin n → E), Function.Injective lam ∧
      (∀ i, c i≠0 ∧ P.product (c i) (c i)=c i) ∧
      (∀ i j, i≠j → P.product (c i) (c j)=0) ∧
      (∑ i, c i)=P.unit ∧ a=∑ i, lam i • c i := by
  classical
  let T : E →ₗ[ℝ] E := P.product a
  have hT : T.IsSymmetric := P.product_inner hinner a
  let I := Eigenvalues T
  let d := hT.diagonalization P.unit
  let c : I → E := fun mu => (d mu : E)
  have hc (mu : I) : T (c mu)=(mu : ℝ) • c mu :=
    mem_eigenspace_iff.mp (d mu).property
  have hsum : (∑ mu : I, c mu)=P.unit := by
    simpa only [LinearMap.IsSymmetric.diagonalization_symm_apply] using
      hT.diagonalization.symm_apply_apply P.unit
  have hscale (u v : E) (mu : ℝ) (hu : T u=mu • u) :
      T (P.product u v)=mu • P.product u v := by
    change P.product a (P.product u v)=_
    rw [← hprod a u v]
    change P.product (T u) v=_
    rw [hu]
    exact LinearMap.congr_fun (P.product.map_smul mu u) v
  have hzero (u v : E) (mu nu : ℝ) (hu : T u=mu • u)
      (hv : T v=nu • v) (hne : mu≠nu) : P.product u v=0 := by
    have hu' := hscale u v mu hu
    have hv' : T (P.product u v)=nu • P.product u v := by
      simpa only [P.commutative v u] using hscale v u nu hv
    have h : (mu-nu) • P.product u v=0 := by
      rw [sub_smul,← hu',← hv',sub_self]
    rcases smul_eq_zero.mp h with hscalar | hvec
    · exact (hne (sub_eq_zero.mp hscalar)).elim
    · exact hvec
  have horth (mu nu : I) (hne : mu≠nu) : P.product (c mu) (c nu)=0 := by
    apply hzero (c mu) (c nu) mu nu (hc mu) (hc nu)
    exact fun h => hne (Subtype.ext h)
  have hidem (mu : I) : P.product (c mu) (c mu)=c mu := by
    have hsumProd : (∑ nu : I, P.product (c nu) (c mu))=c mu := by
      have h := congrArg (fun z => P.product z (c mu)) hsum
      simpa only [map_sum,LinearMap.sum_apply,P.unit_left] using h
    have hsingle : (∑ nu : I, P.product (c nu) (c mu))=P.product (c mu) (c mu) :=
      Finset.sum_eq_single mu (fun nu _ hne => horth nu mu hne)
        (fun hnot => (hnot (Finset.mem_univ mu)).elim)
    exact hsingle.symm.trans hsumProd
  have ha : a=∑ mu : I, (mu : ℝ) • c mu := by
    calc
      a = T P.unit := by change a=P.product a P.unit; rw [P.commutative,P.unit_left]
      _ = T (∑ mu : I, c mu) := by rw [hsum]
      _ = ∑ mu : I, T (c mu) := map_sum T _ _
      _ = _ := Finset.sum_congr rfl (fun mu _ => hc mu)
  let S : Finset I := Finset.univ.filter (fun mu => c mu≠0)
  have hfilter (f : I → E) (hf : ∀ mu, c mu=0 → f mu=0) :
      (∑ mu ∈ S, f mu)=∑ mu : I, f mu := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro mu _ hnot
    apply hf mu
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ mu,hne⟩)
  have hsumS : (∑ mu ∈ S, c mu)=P.unit := by
    rw [hfilter c (fun _ h => h)]
    exact hsum
  have haS : a=∑ mu ∈ S, (mu : ℝ) • c mu := by
    rw [hfilter (fun mu => (mu : ℝ) • c mu) (fun _ h => by rw [h,smul_zero])]
    exact ha
  let e := S.equivFin.symm
  refine ⟨S.card,fun i => ((e i : I) : ℝ),fun i => c (e i),?_,?_,?_,?_,?_⟩
  · intro i j h
    exact e.injective (Subtype.ext (Subtype.ext h))
  · intro i
    exact ⟨(Finset.mem_filter.mp (e i).property).2,hidem (e i)⟩
  · intro i j hne
    apply horth
    exact fun h => hne (e.injective (Subtype.ext h))
  · calc
      _ = ∑ mu : S, c mu := Equiv.sum_comp e (fun mu : S => c mu)
      _ = ∑ mu ∈ S, c mu := Finset.sum_coe_sort S c
      _ = _ := hsumS
  · rw [haS,← Finset.sum_coe_sort S (fun mu => (mu : ℝ) • c mu)]
    exact (Equiv.sum_comp e (fun mu : S => ((mu : I) : ℝ) • c mu)).symm

end AlbertSequential.UnitalJordanProduct
