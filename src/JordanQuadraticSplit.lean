/- SPDX-License-Identifier: Apache-2.0 -/
module

public import UnitalJordanProduct
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! A two-root relation produces an explicit orthogonal idempotent split.
This is a small symbolic verification of the preceding natural algebraic proof,
not a search/certificate computation or an assumed spectral theorem. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

/-- If x²=a*x+b*q with b>0 and x outside ℝq, the two distinct real roots
construct a nontrivial orthogonal splitting of the local unit q. -/
theorem exists_split_of_quadratic_relation (q x : E) (a b : ℝ)
    (hq : P.product q q=q) (hqx : P.product q x=x)
    (hxx : P.product x x=a • x+b • q) (hb : 0<b)
    (houtside : x∉Submodule.span ℝ {q}) :
    ∃ r s : E, P.product r r=r ∧ P.product s s=s ∧
      P.product r s=0 ∧ r+s=q ∧ r≠0 ∧ s≠0 := by
  let t := Real.sqrt (a^2+4*b)
  have hdisc : 0<a^2+4*b := by nlinarith [sq_nonneg a]
  have ht : 0<t := Real.sqrt_pos.mpr hdisc
  have ht0 : t≠0 := ne_of_gt ht
  have ht2 : t^2=a^2+4*b := Real.sq_sqrt (le_of_lt hdisc)
  let c := (1 : ℝ)/t
  let d := (t-a)/(2*t)
  have hc : c≠0 := one_div_ne_zero ht0
  have hca : c*c*a+2*c*d=c := by
    dsimp [c,d]
    field_simp [ht0]
    <;> ring
  have hcb : c*c*b+d*d=d := by
    dsimp [c,d]
    field_simp [ht0]
    nlinarith [ht2]
  let r := c • x+d • q
  let s := q-r
  have hqr : P.product q r=r := by
    simp only [r, map_add, map_smul, RingHom.id_apply, hqx, hq]
  have hrr : P.product r r=r := by
    simp only [r, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      RingHom.id_apply, P.commutative x q, hxx, hqx, hq, smul_add, smul_smul]
    calc
      _ = (c*c*a+2*c*d) • x+(c*c*b+d*d) • q := by module
      _ = _ := by rw [hca,hcb]
  have hss : P.product s s=s := by
    dsimp [s]
    simp only [map_sub, LinearMap.sub_apply, P.commutative r q, hqr, hq, hrr]
    abel
  have hrs : P.product r s=0 := by
    simp only [s, map_sub, P.commutative r q, hqr, hrr, sub_self]
  have hnot : r∉Submodule.span ℝ {q} := by
    intro hr
    have hd : d • q ∈ Submodule.span ℝ {q} :=
      Submodule.smul_mem _ d (Submodule.mem_span_singleton_self q)
    have hcx : c • x ∈ Submodule.span ℝ {q} := by
      have h := Submodule.sub_mem (Submodule.span ℝ {q}) hr hd
      convert h using 1
      dsimp [r]
      abel
    have h := Submodule.smul_mem (Submodule.span ℝ {q}) (c⁻¹) hcx
    have hx : x∈Submodule.span ℝ {q} := by
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
    exact houtside hx
  have hr0 : r≠0 := by
    intro hr
    exact hnot (hr ▸ Submodule.zero_mem _)
  have hs0 : s≠0 := by
    intro hs
    have hrq : r=q := (sub_eq_zero.mp hs).symm
    apply hnot
    rw [hrq]
    exact Submodule.mem_span_singleton_self q
  refine ⟨r,s,hrr,hss,hrs,?_,hr0,hs0⟩
  dsimp [s]
  abel

end AlbertSequential.UnitalJordanProduct
