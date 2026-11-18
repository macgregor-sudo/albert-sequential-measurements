/- SPDX-License-Identifier: Apache-2.0 -/
module
public import UnitalJordanProduct
public import CompactConvexHull
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Formal reality supplies a functional strictly positive on all nonzero
actual squares. No square-cone closure/convexity or global associative form is
used. The auxiliary Euclidean structure is arbitrary and only a proof device. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

theorem formallyReal_fintype (hfr : P.FormallyReal) {ι : Type*} [Fintype ι]
    (x : ι → E) (hzero : (∑ i, P.product (x i) (x i))=0) : ∀ i, x i=0 := by
  classical
  let e := Fintype.equivFin ι
  have hsum : (∑ i : Fin (Fintype.card ι),
      P.product (x (e.symm i)) (x (e.symm i)))=0 := by
    rw [← Fintype.sum_equiv e (fun i => P.product (x i) (x i))
      (fun i => P.product (x (e.symm i)) (x (e.symm i))) (fun i => by simp)]
    exact hzero
  intro i
  simpa using hfr _ (fun j => x (e.symm j)) hsum (e i)

def normalizedSquares : Set E :=
  (fun x => P.product x x) '' Metric.sphere (0 : E) 1

theorem product_square_continuous : Continuous (fun x : E => P.product x x) := by
  letI : IsModuleTopology ℝ E := isModuleTopologyOfFiniteDimensional
  exact (IsModuleTopology.continuous_bilinear_of_finite_left P.product).comp
    (continuous_id.prodMk continuous_id)

theorem normalizedSquares_compact : IsCompact P.normalizedSquares :=
  (isCompact_sphere (0 : E) 1).image P.product_square_continuous

theorem zero_not_mem_convexHull_normalizedSquares (hfr : P.FormallyReal) :
    (0 : E) ∉ convexHull ℝ P.normalizedSquares := by
  classical
  intro hz
  obtain ⟨ι,inst,w,z,hw,hsum,hzmem,hzero⟩ :=
    mem_convexHull_iff_exists_fintype.mp hz
  letI := inst
  choose x hx hxsq using hzmem
  have hnorm (i : ι) : ‖x i‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx i
  have hsq (i : ι) :
      P.product (Real.sqrt (w i) • x i) (Real.sqrt (w i) • x i)=w i • z i := by
    rw [P.product.map_smul,LinearMap.smul_apply,map_smul,smul_smul,
      Real.mul_self_sqrt (hw i)]
    exact congrArg (fun v => w i • v) (hxsq i)
  have hscaled : ∀ i, Real.sqrt (w i) • x i=0 :=
    P.formallyReal_fintype hfr (fun i => Real.sqrt (w i) • x i)
      ((Finset.sum_congr rfl (fun i _ => hsq i)).trans hzero)
  have hwzero (i : ι) : w i=0 := by
    rcases smul_eq_zero.mp (hscaled i) with hroot | hxzero
    · exact (Real.sqrt_eq_zero (hw i)).mp hroot
    · have := hnorm i
      rw [hxzero,norm_zero] at this
      exact (zero_ne_one this).elim
  have : (0 : ℝ)=1 := by simpa only [hwzero,Finset.sum_const_zero] using hsum
  exact zero_ne_one this

theorem exists_square_positive_functional (hfr : P.FormallyReal) :
    ∃ f : E →ₗ[ℝ] ℝ, ∀ x : E, x≠0 → 0<f (P.product x x) := by
  have hcomp := FiniteConvexity.compact_convexHull P.normalizedSquares P.normalizedSquares_compact
  obtain ⟨f,u,hfu,hf⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ P.normalizedSquares) hcomp.isClosed
      (P.zero_not_mem_convexHull_normalizedSquares hfr)
  refine ⟨f.toLinearMap,?_⟩
  intro x hx
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx
  let y : E := ‖x‖⁻¹ • x
  have hy : ‖y‖=1 := by
    simp only [y,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn,inv_mul_cancel₀ hn.ne']
  have hymem : P.product y y∈P.normalizedSquares :=
    ⟨y,by simpa only [Metric.mem_sphere,dist_zero_right] using hy,rfl⟩
  have hupos : 0<u := by simpa only [map_zero] using hfu
  have hpos : 0<f (P.product y y) :=
    hupos.trans (hf _ (subset_convexHull ℝ _ hymem))
  have hxy : P.product x x=(‖x‖*‖x‖) • P.product y y := by
    have hxy' : x=‖x‖ • y := by simp [y,smul_smul,hn.ne']
    conv_lhs => rw [hxy',P.product.map_smul,LinearMap.smul_apply,map_smul,smul_smul]
  rw [hxy,map_smul]
  exact mul_pos (mul_pos hn hn) hpos

end AlbertSequential.UnitalJordanProduct
