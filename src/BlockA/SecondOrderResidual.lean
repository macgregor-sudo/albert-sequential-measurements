/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.SecondOrderQuotient
public import AcceptedRootAtomAdapter
public import NativeWordDuality
public import UniversalProjectionAlgebra
public import ChronologicalWords
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Normed.Operator.Asymptotics
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Second-order residual near a complex subalgebra (`cor:so:residual`) and projective equalities (`prop:cer:noequality`(a))

Formalizes the analytic `C³` residual corollary (companion `cor:so:residual`), building atop `AppF.SecondOrderQuotient` (`Dq`, `redq`, `JTerm`, `term_value_mem_K`),
and the projective-equality characterization (`prop:cer:noequality`(a)) connecting operational
real finite-dimensional projective equalities, `AlgebraicProjectiveData`, `UniversalProjectionAlgebra`,
the free-product group algebra `ℝ[ℤ₂^{*n}]`, and `JTerm.VanishesOnSpecialIdempotents`.

All `NormedAddCommGroup` / `NormedSpace` instances on `Octonion` and `Albert` are `scoped` to
`AlbertSequential.AppF` (definitionally compatible with `Defs` and `NativeTopology`) so no global
instance diamond is exported. A completely norm-free `∀ l : Albert →ₗ[ℝ] ℝ` linear-functional
version (`cor_so_residual_linearFunctional`) is also provided.
-/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open scoped Topology Matrix
open Asymptotics Filter Set

/-! ## Section 1: Scoped normed-space structure on `Octonion` and `Albert` -/

@[instance_reducible]
def octNormedProd : NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ) := inferInstance

@[instance_reducible]
def octNormedSpaceProd : NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ) := inferInstance

@[instance_reducible]
def octMetricProd : MetricSpace Octonion :=
  MetricSpace.replaceTopology (U := inferInstance)
    (octNormedProd.toMetricSpace : MetricSpace Octonion) rfl

@[instance_reducible] private def octBaseAdd : AddCommGroup Octonion := inferInstance
@[instance_reducible] private def octBaseTop : TopologicalSpace Octonion := inferInstance
@[instance_reducible] private def octBaseMod : Module ℝ Octonion := inferInstance

/-- Scoped norm on `Octonion`, extending `Defs`'s `AddCommGroup` and `NativeTopology`'s
`TopologicalSpace` definitionally. -/
scoped instance instNormedAddCommGroupOctonion : NormedAddCommGroup Octonion where
  toAddCommGroup := inferInstance
  toMetricSpace := octMetricProd
  norm x := @norm (Quaternion ℝ × Quaternion ℝ) octNormedProd.toNorm x
  dist_eq x y := octNormedProd.dist_eq x y

scoped instance instNormedSpaceOctonion : NormedSpace ℝ Octonion where
  toModule := inferInstance
  norm_smul_le r x := @NormedSpace.norm_smul_le ℝ (Quaternion ℝ × Quaternion ℝ) _ _
    octNormedSpaceProd r x

@[instance_reducible]
def albertNormedProd : NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)) :=
  inferInstance

@[instance_reducible]
def albertNormedSpaceProd : NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)) :=
  inferInstance

@[instance_reducible]
def albertMetricProd : MetricSpace Albert :=
  MetricSpace.replaceTopology (U := inferInstance)
    (albertNormedProd.toMetricSpace : MetricSpace Albert) rfl

@[instance_reducible] private def albertBaseAdd : AddCommGroup Albert := inferInstance
@[instance_reducible] private def albertBaseTop : TopologicalSpace Albert := inferInstance
@[instance_reducible] private def albertBaseMod : Module ℝ Albert := inferInstance

/-- Scoped norm on `Albert`, extending `Defs`'s `AddCommGroup` and `NativeTopology`'s
`TopologicalSpace` definitionally. -/
scoped instance instNormedAddCommGroupAlbert : NormedAddCommGroup Albert where
  toAddCommGroup := inferInstance
  toMetricSpace := albertMetricProd
  norm x := @norm ((Fin 3 → ℝ) × (Fin 3 → Octonion)) albertNormedProd.toNorm x
  dist_eq x y := albertNormedProd.dist_eq x y

scoped instance instNormedSpaceAlbert : NormedSpace ℝ Albert where
  toModule := inferInstance
  norm_smul_le r x := @NormedSpace.norm_smul_le ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)) _ _
    albertNormedSpaceProd r x

-- Definitional compatibility checks against `Defs` and `NativeTopology`.
example : (instNormedAddCommGroupOctonion).toAddCommGroup = octBaseAdd := rfl
example : (instNormedAddCommGroupOctonion).toUniformSpace.toTopologicalSpace = octBaseTop := rfl
example : (instNormedSpaceOctonion).toModule = octBaseMod := rfl
example : (instNormedAddCommGroupAlbert).toAddCommGroup = albertBaseAdd := rfl
example : (instNormedAddCommGroupAlbert).toUniformSpace.toTopologicalSpace = albertBaseTop := rfl
example : (instNormedSpaceAlbert).toModule = albertBaseMod := rfl

private def octLinearEquiv : Octonion ≃ₗ[ℝ] (Quaternion ℝ × Quaternion ℝ) :=
  LinearEquiv.refl ℝ (Quaternion ℝ × Quaternion ℝ)

private def albertLinearEquiv :
    Albert ≃ₗ[ℝ] ((Fin 3 → ℝ) × (Fin 3 → (Quaternion ℝ × Quaternion ℝ))) :=
  LinearEquiv.refl ℝ ((Fin 3 → ℝ) × (Fin 3 → (Quaternion ℝ × Quaternion ℝ)))

scoped instance instFiniteDimensionalOctonion : FiniteDimensional ℝ Octonion :=
  octLinearEquiv.symm.finiteDimensional

scoped instance instFiniteDimensionalAlbert : FiniteDimensional ℝ Albert :=
  albertLinearEquiv.symm.finiteDimensional

/-- `jordanMul` as a `ℝ`-bilinear map. -/
def jordanMulBilin : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert where
  toFun x :=
    { toFun := fun y => jordanMul x y
      map_add' := jordanMul_add_right x
      map_smul' := fun r y => jordanMul_smul_right r x y }
  map_add' x y := LinearMap.ext fun z => jordanMul_add_left x y z
  map_smul' r x := LinearMap.ext fun z => jordanMul_smul_left r x z

/-- `jordanMul` as a continuous bilinear map on `Albert`. -/
def jordanMulCLM : Albert →L[ℝ] Albert →L[ℝ] Albert :=
  let f : Albert →ₗ[ℝ] (Albert →L[ℝ] Albert) :=
    { toFun := fun x => (jordanMulBilin x).toContinuousLinearMap
      map_add' := fun x y => by
        ext z
        exact jordanMul_add_left x y z
      map_smul' := fun r x => by
        ext z
        exact jordanMul_smul_left r x z }
  f.toContinuousLinearMap

@[simp] theorem jordanMulCLM_apply (x y : Albert) : jordanMulCLM x y = jordanMul x y := rfl

theorem jordanMul_isBoundedBilinearMap :
    IsBoundedBilinearMap ℝ (fun p : Albert × Albert => jordanMul p.1 p.2) where
  add_left := jordanMul_add_left
  smul_left := jordanMul_smul_left
  add_right := jordanMul_add_right
  smul_right := jordanMul_smul_right
  bound := by
    refine ⟨‖jordanMulCLM‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg jordanMulCLM) one_pos,
      fun x y => ?_⟩
    rw [← jordanMulCLM_apply]
    refine (jordanMulCLM.le_opNorm₂ x y).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg x))
      (norm_nonneg y)

theorem contDiff_jordanMul {n : WithTop ℕ∞} {f g : ℝ → Albert}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun t => jordanMul (f t) (g t)) := by
  simpa only [Function.comp_apply, jordanMulCLM_apply] using
    (jordanMulCLM.contDiff.comp hf).clm_apply hg

theorem contDiffAt_jordanMul {n : WithTop ℕ∞} {f g : ℝ → Albert} {t₀ : ℝ}
    (hf : ContDiffAt ℝ n f t₀) (hg : ContDiffAt ℝ n g t₀) :
    ContDiffAt ℝ n (fun t => jordanMul (f t) (g t)) t₀ := by
  simpa only [Function.comp_apply, jordanMulCLM_apply] using
    (jordanMulCLM.contDiff.contDiffAt.comp t₀ hf).clm_apply hg

theorem deriv_jordanMul {f g : ℝ → Albert} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    deriv (fun s => jordanMul (f s) (g s)) t =
      jordanMul (f t) (deriv g t) + jordanMul (deriv f t) (g t) := by
  simpa only [jordanMulCLM_apply] using
    jordanMulCLM.deriv_of_bilinear (fun _ => hf) (fun _ => hg)

theorem hasDerivAt_jordanMul {f g : ℝ → Albert} {f' g' : Albert} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => jordanMul (f s) (g s)) (jordanMul (f t) g' + jordanMul f' (g t)) t := by
  simpa only [jordanMulCLM_apply] using
    (jordanMulCLM.hasDerivAt_of_bilinear (fun _ => hf) (fun _ => hg))

/-- A linear map on `Albert` is continuous, hence preserves `ContDiff`. -/
theorem contDiffAt_of_forall_linearMap {n : ℕ∞} {f : ℝ → Albert} {t₀ : ℝ}
    (hf : ∀ l : Albert →ₗ[ℝ] ℝ, ContDiffAt ℝ n (fun t => l (f t)) t₀) :
    ContDiffAt ℝ n f t₀ := by
  have hd : ∀ i : Fin 3, ContDiffAt ℝ n (fun t => (f t).1 i) t₀ := fun i =>
    hf { toFun := fun x => x.1 i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have ho : ∀ k : Fin 3, ContDiffAt ℝ n (fun t => (f t).2 k) t₀ := fun k => by
    have h1r : ContDiffAt ℝ n (fun t => ((f t).2 k).1.re) t₀ :=
      hf { toFun := fun x => (x.2 k).1.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h1i : ContDiffAt ℝ n (fun t => ((f t).2 k).1.imI) t₀ :=
      hf { toFun := fun x => (x.2 k).1.imI, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h1j : ContDiffAt ℝ n (fun t => ((f t).2 k).1.imJ) t₀ :=
      hf { toFun := fun x => (x.2 k).1.imJ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h1k : ContDiffAt ℝ n (fun t => ((f t).2 k).1.imK) t₀ :=
      hf { toFun := fun x => (x.2 k).1.imK, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h2r : ContDiffAt ℝ n (fun t => ((f t).2 k).2.re) t₀ :=
      hf { toFun := fun x => (x.2 k).2.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h2i : ContDiffAt ℝ n (fun t => ((f t).2 k).2.imI) t₀ :=
      hf { toFun := fun x => (x.2 k).2.imI, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h2j : ContDiffAt ℝ n (fun t => ((f t).2 k).2.imJ) t₀ :=
      hf { toFun := fun x => (x.2 k).2.imJ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h2k : ContDiffAt ℝ n (fun t => ((f t).2 k).2.imK) t₀ :=
      hf { toFun := fun x => (x.2 k).2.imK, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    let eQ : (Fin 4 → ℝ) ≃L[ℝ] Quaternion ℝ :=
      { toFun := fun v => ⟨v 0, v 1, v 2, v 3⟩
        invFun := fun q => ![q.re, q.imI, q.imJ, q.imK]
        left_inv := fun v => by funext i; fin_cases i <;> rfl
        right_inv := fun q => by apply Quaternion.ext <;> rfl
        map_add' := fun _ _ => by apply Quaternion.ext <;> rfl
        map_smul' := fun _ _ => by apply Quaternion.ext <;> rfl
        continuous_toFun :=
          LinearMap.continuous_of_finiteDimensional
            ({ toFun := fun v : Fin 4 → ℝ => (⟨v 0, v 1, v 2, v 3⟩ : Quaternion ℝ)
               map_add' := fun _ _ => by apply Quaternion.ext <;> rfl
               map_smul' := fun _ _ => by apply Quaternion.ext <;> rfl } :
              (Fin 4 → ℝ) →ₗ[ℝ] Quaternion ℝ)
        continuous_invFun :=
          LinearMap.continuous_of_finiteDimensional
            ({ toFun := fun q : Quaternion ℝ => ![q.re, q.imI, q.imJ, q.imK]
               map_add' := fun _ _ => by funext i; fin_cases i <;> rfl
               map_smul' := fun _ _ => by funext i; fin_cases i <;> rfl } :
              Quaternion ℝ →ₗ[ℝ] (Fin 4 → ℝ)) }
    have hq1 : ContDiffAt ℝ n (fun t => ((f t).2 k).1) t₀ := by
      have hv : ContDiffAt ℝ n (fun t => ![((f t).2 k).1.re, ((f t).2 k).1.imI,
          ((f t).2 k).1.imJ, ((f t).2 k).1.imK]) t₀ := by
        rw [contDiffAt_pi]
        intro j; fin_cases j <;> assumption
      exact (eQ.toContinuousLinearMap.contDiff.contDiffAt.comp t₀ hv).congr_of_eventuallyEq
        (Eventually.of_forall fun t => by apply Quaternion.ext <;> rfl)
    have hq2 : ContDiffAt ℝ n (fun t => ((f t).2 k).2) t₀ := by
      have hv : ContDiffAt ℝ n (fun t => ![((f t).2 k).2.re, ((f t).2 k).2.imI,
          ((f t).2 k).2.imJ, ((f t).2 k).2.imK]) t₀ := by
        rw [contDiffAt_pi]
        intro j; fin_cases j <;> assumption
      exact (eQ.toContinuousLinearMap.contDiff.contDiffAt.comp t₀ hv).congr_of_eventuallyEq
        (Eventually.of_forall fun t => by apply Quaternion.ext <;> rfl)
    let eOct : (Quaternion ℝ × Quaternion ℝ) ≃L[ℝ] Octonion :=
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id }
    exact eOct.toContinuousLinearMap.contDiff.contDiffAt.comp t₀ (hq1.prodMk hq2)
  have h1 : ContDiffAt ℝ n (fun t => (f t).1) t₀ := contDiffAt_pi.2 hd
  have h2 : ContDiffAt ℝ n (fun t => (f t).2) t₀ := contDiffAt_pi.2 ho
  let eAlb : ((Fin 3 → ℝ) × (Fin 3 → Octonion)) ≃L[ℝ] Albert :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  exact (eAlb.toContinuousLinearMap.contDiff.contDiffAt.comp t₀ (h1.prodMk h2)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => Prod.mk.eta)

theorem contDiff_of_forall_linearMap {n : ℕ∞} {f : ℝ → Albert}
    (hf : ∀ l : Albert →ₗ[ℝ] ℝ, ContDiff ℝ n (fun t => l (f t))) :
    ContDiff ℝ n f :=
  contDiff_iff_contDiffAt.2 fun _ => contDiffAt_of_forall_linearMap fun l => (hf l).contDiffAt

/-! ## Section 2: 1D `C³` Taylor theorem (`O(t³)`) and 2-jet homomorphism into `J3` -/

/-- Second-order Taylor expansion at `0` with `O(t³)` remainder for any `C³` curve into a real
normed space, proved via three applications of the mean value theorem (`MeanValue`). -/
theorem taylor_two_isBigO_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiffAt ℝ 3 f 0) :
    (fun t => f t - (f 0 + t • deriv f 0 + (t ^ 2 / 2) • deriv (deriv f) 0)) =O[𝓝 0]
      (fun t => t ^ 3) := by
  obtain ⟨u, huo, h0u, hfu⟩ := hf.contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem (mem_univ 0), univ_inter] at hfu
  obtain ⟨δ₀, hδ₀_pos, hball₀⟩ := Metric.isOpen_iff.mp huo 0 h0u
  have hf_ball : ContDiffOn ℝ 3 f (Metric.ball 0 δ₀) := hfu.mono hball₀
  have hf1 : ContDiffOn ℝ 2 (deriv f) (Metric.ball 0 δ₀) :=
    hf_ball.deriv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hf2 : ContDiffOn ℝ 1 (deriv (deriv f)) (Metric.ball 0 δ₀) :=
    hf1.deriv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hc3 : ContinuousOn (deriv (deriv (deriv f))) (Metric.ball 0 δ₀) :=
    hf2.continuousOn_deriv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hc3_at : ContinuousAt (deriv (deriv (deriv f))) 0 :=
    hc3.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ₀_pos))
  set C : ℝ := ‖deriv (deriv (deriv f)) 0‖ + 1
  have hC_nonneg : 0 ≤ C := by positivity
  have h_ev : ∀ᶠ y in 𝓝 0, ‖deriv (deriv (deriv f)) y‖ < C :=
    hc3_at.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨δ₁, hδ₁_pos, hball₁⟩ := Metric.mem_nhds_iff.mp h_ev
  set δ : ℝ := min δ₀ δ₁
  have hδ_pos : 0 < δ := lt_min hδ₀_pos hδ₁_pos
  set g : ℝ → E := fun t => f t - (f 0 + t • deriv f 0 + (t ^ 2 / 2) • deriv (deriv f) 0)
  set g1 : ℝ → E := fun t => deriv f t - (deriv f 0 + t • deriv (deriv f) 0)
  set g2 : ℝ → E := fun t => deriv (deriv f) t - deriv (deriv f) 0
  have hg2_zero : g2 0 = 0 := sub_self _
  have hg1_zero : g1 0 = 0 := by simp [g1]
  have hg_zero : g 0 = 0 := by simp [g]
  have hdiff0 : ∀ t ∈ Metric.ball (0 : ℝ) δ, DifferentiableAt ℝ f t := fun t ht =>
    ((hf_ball.differentiableOn (by norm_num)) t (Metric.ball_subset_ball (min_le_left _ _) ht)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (min_le_left _ _) ht))
  have hdiff1 : ∀ t ∈ Metric.ball (0 : ℝ) δ, DifferentiableAt ℝ (deriv f) t := fun t ht =>
    ((hf1.differentiableOn (by norm_num)) t (Metric.ball_subset_ball (min_le_left _ _) ht)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (min_le_left _ _) ht))
  have hdiff2 : ∀ t ∈ Metric.ball (0 : ℝ) δ, DifferentiableAt ℝ (deriv (deriv f)) t := fun t ht =>
    ((hf2.differentiableOn (by norm_num)) t (Metric.ball_subset_ball (min_le_left _ _) ht)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (min_le_left _ _) ht))
  have hg2_deriv : ∀ t ∈ Metric.ball (0 : ℝ) δ,
      HasDerivWithinAt g2 (deriv (deriv (deriv f)) t) (Metric.ball 0 δ) t := fun t ht =>
    ((hdiff2 t ht).hasDerivAt.sub_const _).hasDerivWithinAt
  have hg1_deriv : ∀ t ∈ Metric.ball (0 : ℝ) δ,
      HasDerivWithinAt g1 (g2 t) (Metric.ball 0 δ) t := fun t ht => by
    have hp1 := (hdiff1 t ht).hasDerivAt
    have hp2 := (hasDerivAt_const t (deriv f 0)).add ((hasDerivAt_id t).smul_const (deriv (deriv f) 0))
    have hsub : HasDerivAt (fun s => deriv f s - (deriv f 0 + s • deriv (deriv f) 0))
        (deriv (deriv f) t - (0 + (1 : ℝ) • deriv (deriv f) 0)) t := hp1.sub hp2
    rw [zero_add, one_smul] at hsub
    exact hsub.hasDerivWithinAt
  have hg_deriv : ∀ t ∈ Metric.ball (0 : ℝ) δ,
      HasDerivWithinAt g (g1 t) (Metric.ball 0 δ) t := fun t ht => by
    have hp0 := (hdiff0 t ht).hasDerivAt
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      have := ((hasDerivAt_pow 2 t).div_const 2)
      convert this using 1
      ring
    have hp1 := ((hasDerivAt_const t (f 0)).add ((hasDerivAt_id t).smul_const (deriv f 0))).add
      (hsq.smul_const (deriv (deriv f) 0))
    have hsub : HasDerivAt (fun s => f s - (f 0 + s • deriv f 0 + (s ^ 2 / 2) • deriv (deriv f) 0))
        (deriv f t - (0 + (1 : ℝ) • deriv f 0 + t • deriv (deriv f) 0)) t := hp0.sub hp1
    rw [zero_add, one_smul] at hsub
    exact hsub.hasDerivWithinAt
  refine IsBigO.of_bound C ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ_pos] with t ht
  have hsub : Metric.closedBall (0 : ℝ) |t| ⊆ Metric.ball (0 : ℝ) δ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [Metric.mem_ball, dist_zero_right] at ht ⊢
    exact lt_of_le_of_lt hy ht
  have h2_bound : ∀ y ∈ Metric.closedBall (0 : ℝ) |t|, ‖g2 y‖ ≤ C * |t| := fun y hy => by
    have hb := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le hg2_deriv
      (fun z hz => le_of_lt (hball₁ (Metric.ball_subset_ball (min_le_right _ _) hz)))
      (Metric.mem_ball_self hδ_pos) (hsub hy)
    rw [hg2_zero, sub_zero, sub_zero, Real.norm_eq_abs] at hb
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hy
    exact hb.trans (mul_le_mul_of_nonneg_left hy hC_nonneg)
  have h1_bound : ∀ y ∈ Metric.closedBall (0 : ℝ) |t|, ‖g1 y‖ ≤ C * |t| ^ 2 := fun y hy => by
    have hb := (convex_closedBall (0 : ℝ) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hg1_deriv z (hsub hz)).mono hsub) h2_bound
      (Metric.mem_closedBall_self (abs_nonneg t)) hy
    rw [hg1_zero, sub_zero, sub_zero, Real.norm_eq_abs] at hb
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hy
    calc
      ‖g1 y‖ ≤ C * |t| * |y| := hb
      _ ≤ C * |t| * |t| := mul_le_mul_of_nonneg_left hy (mul_nonneg hC_nonneg (abs_nonneg t))
      _ = C * |t| ^ 2 := by ring
  have h0_bound := (convex_closedBall (0 : ℝ) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hg_deriv z (hsub hz)).mono hsub) h1_bound
    (Metric.mem_closedBall_self (abs_nonneg t))
    (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs])
  rw [hg_zero, sub_zero, sub_zero, Real.norm_eq_abs] at h0_bound
  refine h0_bound.trans_eq ?_
  rw [Real.norm_eq_abs, abs_pow]
  ring

/-- The 2-jet `(f 0, f'(0), (1/2) f''(0))` of a curve `f : ℝ → Albert` at `0`. -/
def jet2 (f : ℝ → Albert) : J3 :=
  (f 0, deriv f 0, (1 / 2 : ℝ) • deriv (deriv f) 0)

theorem jet2_const (c : Albert) : jet2 (fun _ => c) = (c, 0, 0) := by
  have h1 : deriv (fun _ : ℝ => c) = fun _ => 0 := funext fun x => deriv_const x c
  simp [jet2, h1, deriv_const]

theorem jet2_add {f g : ℝ → Albert} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    jet2 (fun t => f t + g t) = jet2 f + jet2 g := by
  have hf1 : DifferentiableAt ℝ f 0 := hf.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ g 0 := hg.differentiableAt (by norm_num)
  have h1 : deriv (fun t => f t + g t) 0 = deriv f 0 + deriv g 0 :=
    (hf1.hasDerivAt.add hg1.hasDerivAt).deriv
  have hfg1 : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (fun s => f s + g s) t = deriv f t + deriv g t := by
    filter_upwards [(hf.eventually (by norm_num)).and (hg.eventually (by norm_num))] with t ⟨htf, htg⟩
    exact ((htf.differentiableAt (by norm_num)).hasDerivAt.add
      (htg.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hf2 : DifferentiableAt ℝ (deriv f) 0 :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg2 : DifferentiableAt ℝ (deriv g) 0 :=
    (hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : deriv (deriv (fun s => f s + g s)) 0 = deriv (deriv f) 0 + deriv (deriv g) 0 := by
    rw [Filter.EventuallyEq.deriv_eq hfg1]
    exact (hf2.hasDerivAt.add hg2.hasDerivAt).deriv
  simp only [jet2, h1, h2, Prod.mk_add_mk, smul_add]

theorem jet2_smul (r : ℝ) {f : ℝ → Albert} (hf : ContDiffAt ℝ 2 f 0) :
    jet2 (fun t => r • f t) = r • jet2 f := by
  have hf1 : DifferentiableAt ℝ f 0 := hf.differentiableAt (by norm_num)
  have h1 : deriv (fun t => r • f t) 0 = r • deriv f 0 :=
    (hf1.hasDerivAt.const_smul r).deriv
  have hs1 : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (fun s => r • f s) t = r • deriv f t := by
    filter_upwards [hf.eventually (by norm_num)] with t htf
    exact ((htf.differentiableAt (by norm_num)).hasDerivAt.const_smul r).deriv
  have hf2 : DifferentiableAt ℝ (deriv f) 0 :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : deriv (deriv (fun s => r • f s)) 0 = r • deriv (deriv f) 0 := by
    rw [Filter.EventuallyEq.deriv_eq hs1]
    exact (hf2.hasDerivAt.const_smul r).deriv
  simp only [jet2, h1, h2, Prod.smul_mk, smul_comm r (1 / 2 : ℝ)]

theorem jet2_jordanMul {f g : ℝ → Albert} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    jet2 (fun t => jordanMul (f t) (g t)) = j3mul (jet2 f) (jet2 g) := by
  have hf1 : DifferentiableAt ℝ f 0 := hf.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ g 0 := hg.differentiableAt (by norm_num)
  have hfd : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t :=
    (hf.eventually (by norm_num)).mono fun _ ht => ht.differentiableAt (by norm_num)
  have hgd : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ g t :=
    (hg.eventually (by norm_num)).mono fun _ ht => ht.differentiableAt (by norm_num)
  have hm1 : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (fun s => jordanMul (f s) (g s)) t =
      jordanMul (f t) (deriv g t) + jordanMul (deriv f t) (g t) := by
    filter_upwards [hfd, hgd] with t hft hgt
    exact deriv_jordanMul hft hgt
  have hdf : DifferentiableAt ℝ (deriv f) 0 :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (deriv g) 0 :=
    (hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have ht1 : DifferentiableAt ℝ (fun t => jordanMul (f t) (deriv g t)) 0 :=
    (hasDerivAt_jordanMul hf1.hasDerivAt hdg.hasDerivAt).differentiableAt
  have ht2 : DifferentiableAt ℝ (fun t => jordanMul (deriv f t) (g t)) 0 :=
    (hasDerivAt_jordanMul hdf.hasDerivAt hg1.hasDerivAt).differentiableAt
  have h2 : deriv (deriv (fun s => jordanMul (f s) (g s))) 0 =
      jordanMul (f 0) (deriv (deriv g) 0) +
        (2 : ℝ) • jordanMul (deriv f 0) (deriv g 0) +
        jordanMul (deriv (deriv f) 0) (g 0) := by
    rw [Filter.EventuallyEq.deriv_eq hm1]
    have hadd : deriv (fun x => jordanMul (f x) (deriv g x) + jordanMul (deriv f x) (g x)) 0 =
        deriv (fun x => jordanMul (f x) (deriv g x)) 0 +
          deriv (fun x => jordanMul (deriv f x) (g x)) 0 :=
      (ht1.hasDerivAt.add ht2.hasDerivAt).deriv
    rw [hadd,
      (hasDerivAt_jordanMul hf1.hasDerivAt hdg.hasDerivAt).deriv,
      (hasDerivAt_jordanMul hdf.hasDerivAt hg1.hasDerivAt).deriv,
      two_smul]
    abel
  have hj1 : deriv (fun s => jordanMul (f s) (g s)) 0 =
      jordanMul (f 0) (deriv g 0) + jordanMul (deriv f 0) (g 0) := deriv_jordanMul hf1 hg1
  simp only [jet2, j3mul, hj1, h2]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  simp only [smul_add, jordanMul_smul_left, jordanMul_smul_right, smul_smul]
  norm_num

/-! ## Section 3: `JTerm` evaluation, 2-jets of idempotents, and `standardComplexWindow` residual -/

/-- Native evaluation of a Jordan-polynomial term `T : JTerm n` in `Albert`. -/
def JTerm.evalAlbert {n : ℕ} (p : Fin n → Albert) : JTerm n → Albert
  | .var k => p k
  | .one => albertUnit
  | .add s t => evalAlbert p s + evalAlbert p t
  | .smul r t => r • evalAlbert p t
  | .mul s t => jordanMul (evalAlbert p s) (evalAlbert p t)

theorem contDiffAt_evalAlbert {n : ℕ} {m : WithTop ℕ∞} {p : Fin n → ℝ → Albert} {t₀ : ℝ}
    (hp : ∀ k, ContDiffAt ℝ m (p k) t₀) (T : JTerm n) :
    ContDiffAt ℝ m (fun t => T.evalAlbert (fun k => p k t)) t₀ := by
  induction T with
  | var k => exact hp k
  | one => exact contDiffAt_const
  | add s t hs ht => exact hs.add ht
  | smul r t ht => exact (contDiffAt_const (c := r)).smul ht
  | mul s t hs ht => exact contDiffAt_jordanMul hs ht

theorem contDiff_evalAlbert {n : ℕ} {m : WithTop ℕ∞} {p : Fin n → ℝ → Albert}
    (hp : ∀ k, ContDiff ℝ m (p k)) (T : JTerm n) :
    ContDiff ℝ m (fun t => T.evalAlbert (fun k => p k t)) :=
  contDiff_iff_contDiffAt.2 fun _ => contDiffAt_evalAlbert (fun k => (hp k).contDiffAt) T

theorem jet2_evalAlbert {n : ℕ} {p : Fin n → ℝ → Albert}
    (hp : ∀ k, ContDiffAt ℝ 2 (p k) 0) (T : JTerm n) :
    jet2 (fun t => T.evalAlbert (fun k => p k t)) = T.evalE (fun k => jet2 (p k)) := by
  induction T with
  | var k => rfl
  | one => exact jet2_const albertUnit
  | add s t hs ht =>
    dsimp only [JTerm.evalAlbert, JTerm.evalE]
    rw [jet2_add (contDiffAt_evalAlbert hp s) (contDiffAt_evalAlbert hp t), hs, ht]
  | smul r t ht =>
    dsimp only [JTerm.evalAlbert, JTerm.evalE]
    rw [jet2_smul r (contDiffAt_evalAlbert hp t), ht]
  | mul s t hs ht =>
    dsimp only [JTerm.evalAlbert, JTerm.evalE]
    rw [jet2_jordanMul (contDiffAt_evalAlbert hp s) (contDiffAt_evalAlbert hp t), hs, ht]

theorem jet2_mem_E2 {p : ℝ → Albert} (hp0 : standardComplexWindow.Contains (p 0)) :
    jet2 p ∈ E2 :=
  hp0

theorem jet2_idempotent {p : ℝ → Albert} (hp : ContDiffAt ℝ 2 p 0)
    (hidem : ∀ t, jordanMul (p t) (p t) = p t) :
    j3mul (jet2 p) (jet2 p) = jet2 p := by
  rw [← jet2_jordanMul hp hp]
  exact congrArg jet2 (funext hidem)

theorem mem_Wperp_implies_tracePairing_zero {v : Albert} (hv : v ∈ Wperp)
    {w : Albert} (hw : standardComplexWindow.Contains w) :
    tracePairing w v = 0 := by
  obtain ⟨h0j, h0k, h0s, h1j, h1k, h1s, h2j, h2k, h2s⟩ := (standardComplexWindow_contains_iff w).1 hw
  obtain ⟨hv1, hv2⟩ := hv
  have ho0 : octDot (w.2 0) (v.2 0) = 0 := by
    rw [octDot_eq_coords, h0j, h0k]
    have h0s' : (w.2 0).2 = 0 := h0s
    simp [h0s', (hv2 0).1, (hv2 0).2]
  have ho1 : octDot (w.2 1) (v.2 1) = 0 := by
    rw [octDot_eq_coords, h1j, h1k]
    have h1s' : (w.2 1).2 = 0 := h1s
    simp [h1s', (hv2 1).1, (hv2 1).2]
  have ho2 : octDot (w.2 2) (v.2 2) = 0 := by
    rw [octDot_eq_coords, h2j, h2k]
    have h2s' : (w.2 2).2 = 0 := h2s
    simp [h2s', (hv2 2).1, (hv2 2).2]
  rw [tracePairing_eq_coords, hv1 0, hv1 1, hv1 2, ho0, ho1, ho2]
  ring

theorem mem_Wperp_iff_tracePairing_zero (v : Albert) :
    v ∈ Wperp ↔ ∀ w : Albert, standardComplexWindow.Contains w → tracePairing w v = 0 := by
  refine ⟨fun hv w hw => mem_Wperp_implies_tracePairing_zero hv hw, fun h => ?_⟩
  refine ⟨fun i => ?_, fun k => ⟨?_, ?_⟩⟩
  · let w : Albert := (fun j => if j = i then (1 : ℝ) else 0, fun _ => 0)
    have hw : standardComplexWindow.Contains w := by
      rw [standardComplexWindow_contains_iff]
      simp [w]
    have ht := h w hw
    rw [tracePairing_eq_coords, octDot_eq_coords, octDot_eq_coords, octDot_eq_coords] at ht
    fin_cases i <;> (dsimp; simp [w] at ht; linarith)
  · let w : Albert := (0, fun j => if j = k then (⟨1, 0, 0, 0⟩, 0) else 0)
    have hw : standardComplexWindow.Contains w := by
      rw [standardComplexWindow_contains_iff]
      fin_cases k <;> simp [w]
    have ht := h w hw
    rw [tracePairing_eq_coords, octDot_eq_coords, octDot_eq_coords, octDot_eq_coords] at ht
    fin_cases k <;> (dsimp; simp [w] at ht; linarith)
  · let w : Albert := (0, fun j => if j = k then (⟨0, 1, 0, 0⟩, 0) else 0)
    have hw : standardComplexWindow.Contains w := by
      rw [standardComplexWindow_contains_iff]
      fin_cases k <;> simp [w]
    have ht := h w hw
    rw [tracePairing_eq_coords, octDot_eq_coords, octDot_eq_coords, octDot_eq_coords] at ht
    fin_cases k <;> (dsimp; simp [w] at ht; linarith)

private theorem deriv_clm_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Albert →L[ℝ] F) {f : ℝ → Albert} {t : ℝ} (hf : DifferentiableAt ℝ f t) :
    deriv (fun s => L (f s)) t = L (deriv f t) :=
  (L.hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt).deriv

/-- Second-order residual for an arbitrary `JTerm` vanishing on special idempotents evaluated
along `C³` idempotent curves based in `standardComplexWindow`. -/
theorem standardWindow_residual_of_specialVanishing {n : ℕ}
    (T : JTerm n) (hT : T.VanishesOnSpecialIdempotents)
    (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k, ContDiff ℝ 3 (p k))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, standardComplexWindow.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => T.evalAlbert (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 3 r ∧
      r 0 = 0 ∧
      deriv r 0 = 0 ∧
      Q ∈ Wperp ∧
      (∀ w : Albert, standardComplexWindow.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3)) := by
  intro r Q
  have hr_diff : ContDiff ℝ 3 r := contDiff_evalAlbert hp_diff T
  have hp2 : ∀ k, ContDiffAt ℝ 2 (p k) 0 := fun k => (hp_diff k).contDiffAt.of_le (by norm_num)
  have hjet : jet2 r = T.evalE (fun k => jet2 (p k)) := jet2_evalAlbert hp2 T
  have hmem : T.evalE (fun k => jet2 (p k)) ∈ Kso :=
    term_value_mem_K T hT (fun k => jet2 (p k)) (fun k => jet2_mem_E2 (hp_base k))
      (fun k => jet2_idempotent (hp2 k) (hp_idem k))
  rw [← hjet] at hmem
  rcases hmem with ⟨hr0, hdr0, hQ⟩
  dsimp [jet2] at hr0 hdr0 hQ
  have hQ_orth : ∀ w : Albert, standardComplexWindow.Contains w → tracePairing w Q = 0 :=
    fun w hw => mem_Wperp_implies_tracePairing_zero hQ hw
  have hbigO : (fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3) := by
    have ht := taylor_two_isBigO_cube hr_diff.contDiffAt
    refine ht.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
    dsimp only
    rw [hr0, hdr0, smul_zero, add_zero, zero_add]
    change r t - (t ^ 2 / 2) • deriv (deriv r) 0 = r t - t ^ 2 • ((1 / 2 : ℝ) • deriv (deriv r) 0)
    rw [smul_smul, div_eq_mul_one_div]
  have hbigO_l : ∀ l : Albert →ₗ[ℝ] ℝ,
      (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3) := fun l => by
    let L : Albert →L[ℝ] ℝ := l.toContinuousLinearMap
    have hcomp := (L.isBigO_comp (fun t => r t - t ^ 2 • Q) (𝓝 0)).trans hbigO
    simpa [L, Function.comp_def] using hcomp
  exact ⟨hr_diff, hr0, hdr0, hQ, hQ_orth, hbigO, hbigO_l⟩

/-! ## Section 4: Word combinations, free product `ℤ₂^{*n}`, and `prop:cer:noequality`(a) -/

/-- Linear combination of chronological native word effects on `Albert`. -/
def nativeWordCombinationEffect {ι : Type*} (c : Word ι →₀ ℝ) (p : ι → Albert) : Albert :=
  c.sum (fun w a => a • nativeWordEffect p w)

/-- Linear functional `x ↦ tracePairing ρ x` on `Albert`. -/
def tracePairingLM (ρ : Albert) : Albert →ₗ[ℝ] ℝ where
  toFun := tracePairing ρ
  map_add' := tracePairing_add_right ρ
  map_smul' r x := by
    unfold tracePairing
    rw [jordanMul_smul_right, albertTrace_smul]
    rfl

@[simp] theorem tracePairingLM_apply (ρ x : Albert) : tracePairingLM ρ x = tracePairing ρ x := rfl

theorem tracePairing_nativeWordCombinationEffect {ι : Type*}
    (c : Word ι →₀ ℝ) (p : ι → Albert) (ρ : Albert) :
    tracePairing ρ (nativeWordCombinationEffect c p) =
      c.sum (fun w a => a * nativeWordProbability p ρ w) := by
  rw [← tracePairingLM_apply, nativeWordCombinationEffect, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  dsimp only
  rw [map_smul, tracePairingLM_apply, smul_eq_mul, NativeAnalysis.nativeWordProbability_eq_pairing]

/-- `JTerm` encoding of a single binary outcome `(k, b)`. -/
def outcomeJTerm {n : ℕ} (a : Outcome (Fin n)) : JTerm n :=
  if a.2 then .var a.1 else .add .one (.smul (-1) (.var a.1))

/-- `JTerm` encoding of the quadratic operator `U_u(x) = 2 u ∘ (u ∘ x) - (u ∘ u) ∘ x`. -/
def quadJTerm {n : ℕ} (u x : JTerm n) : JTerm n :=
  .add (.smul 2 (.mul u (.mul u x))) (.smul (-1) (.mul (.mul u u) x))

/-- `JTerm` encoding of a chronological measurement word `w`. -/
def wordJTerm {n : ℕ} : Word (Fin n) → JTerm n
  | [] => .one
  | a :: w => quadJTerm (outcomeJTerm a) (wordJTerm w)

/-- Unital associative quadratic word operator, agreeing with `wordOperator` for self-adjoint
projections and well-defined in any associative ring without a star operation. -/
def wordQuadOperator {ι A : Type*} [Ring A] (P : ι → A) : Word ι → A
  | [] => 1
  | a :: w => algebraicOutcome P a * wordQuadOperator P w * algebraicOutcome P a

theorem wordQuadOperator_eq_wordOperator {ι A : Type*} [Ring A] [StarRing A]
    (P : ι → A) (hstar : ∀ i, star (P i) = P i) (w : Word ι) :
    wordQuadOperator P w = wordOperator P w := by
  induction w with
  | nil => exact (wordOperator_nil P).symm
  | cons a w ih =>
    rw [wordOperator_cons P hstar, wordQuadOperator, ih]

theorem evalAlbert_outcomeJTerm {n : ℕ} (p : Fin n → Albert) (a : Outcome (Fin n)) :
    (outcomeJTerm a).evalAlbert p = nativeOutcome p a := by
  rcases a with ⟨k, b⟩
  cases b <;> simp [outcomeJTerm, nativeOutcome, JTerm.evalAlbert, sub_eq_add_neg]

theorem evalAlbert_quadJTerm {n : ℕ} (p : Fin n → Albert) (u x : JTerm n) :
    (quadJTerm u x).evalAlbert p = quadraticMap (u.evalAlbert p) (x.evalAlbert p) := by
  unfold quadraticMap
  dsimp [quadJTerm, JTerm.evalAlbert]
  rw [neg_one_smul, sub_eq_add_neg, two_smul, two_smul]

theorem evalAlbert_wordJTerm {n : ℕ} (p : Fin n → Albert) (w : Word (Fin n)) :
    (wordJTerm w).evalAlbert p = nativeWordEffect p w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [wordJTerm, evalAlbert_quadJTerm, evalAlbert_outcomeJTerm, ih]
    rfl

theorem evalS_outcomeJTerm {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (P : Fin n → A) (a : Outcome (Fin n)) :
    (outcomeJTerm a).evalS P = algebraicOutcome P a := by
  rcases a with ⟨k, b⟩
  cases b <;> simp [outcomeJTerm, algebraicOutcome, JTerm.evalS, sub_eq_add_neg]

private theorem evalS_quad_identity {A : Type*} [Ring A] [Algebra ℝ A] (U X : A) :
    (2 : ℝ) • ((1 / 2 : ℝ) • (U * ((1 / 2 : ℝ) • (U * X + X * U)) +
      ((1 / 2 : ℝ) • (U * X + X * U)) * U)) +
      (-1 : ℝ) • ((1 / 2 : ℝ) • (((1 / 2 : ℝ) • (U * U + U * U)) * X +
        X * ((1 / 2 : ℝ) • (U * U + U * U)))) = U * X * U := by
  have hUU : (1 / 2 : ℝ) • (U * U + U * U) = U * U := by
    rw [← two_smul ℝ (U * U), smul_smul]
    norm_num
  have h1 : (2 : ℝ) • ((1 / 2 : ℝ) • (U * ((1 / 2 : ℝ) • (U * X + X * U)) +
      ((1 / 2 : ℝ) • (U * X + X * U)) * U)) =
      (1 / 2 : ℝ) • ((U * U * X + U * X * U) + (U * X * U + X * U * U)) := by
    rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_add]
    simp only [mul_add, add_mul, mul_assoc]
  have h2 : (-1 : ℝ) • ((1 / 2 : ℝ) • (((1 / 2 : ℝ) • (U * U + U * U)) * X +
      X * ((1 / 2 : ℝ) • (U * U + U * U)))) =
      (-1 / 2 : ℝ) • (U * U * X + X * U * U) := by
    rw [hUU, smul_smul, ← mul_assoc X U U]
    norm_num
  rw [h1, h2]
  simp only [smul_add, add_assoc]
  have ha : (1 / 2 : ℝ) • (U * U * X) + ((-1 / 2 : ℝ) • (U * U * X) +
      (-1 / 2 : ℝ) • (X * U * U)) = (-1 / 2 : ℝ) • (X * U * U) := by
    rw [← add_assoc, ← add_smul]
    norm_num
  have hb : (1 / 2 : ℝ) • (U * X * U) + ((1 / 2 : ℝ) • (U * X * U) +
      ((1 / 2 : ℝ) • (X * U * U) + (-1 / 2 : ℝ) • (X * U * U))) = U * X * U := by
    have hc : (1 / 2 : ℝ) • (X * U * U) + (-1 / 2 : ℝ) • (X * U * U) = 0 := by
      rw [← add_smul]
      norm_num
    rw [hc, add_zero, ← add_smul]
    norm_num
  calc
    (1 / 2 : ℝ) • (U * U * X) + ((1 / 2 : ℝ) • (U * X * U) +
        ((1 / 2 : ℝ) • (U * X * U) + ((1 / 2 : ℝ) • (X * U * U) +
          ((-1 / 2 : ℝ) • (U * U * X) + (-1 / 2 : ℝ) • (X * U * U)))))
      = (1 / 2 : ℝ) • (U * U * X) + ((-1 / 2 : ℝ) • (U * U * X) +
          ((1 / 2 : ℝ) • (U * X * U) + ((1 / 2 : ℝ) • (U * X * U) +
            ((1 / 2 : ℝ) • (X * U * U) + (-1 / 2 : ℝ) • (X * U * U))))) := by abel
    _ = (1 / 2 : ℝ) • (U * X * U) + ((1 / 2 : ℝ) • (U * X * U) +
          ((1 / 2 : ℝ) • (X * U * U) + (-1 / 2 : ℝ) • (X * U * U))) := by
        rw [← add_assoc ((1 / 2 : ℝ) • (U * U * X)), show (1 / 2 : ℝ) • (U * U * X) + (-1 / 2 : ℝ) • (U * U * X) = 0 by rw [← add_smul]; norm_num, zero_add]
    _ = U * X * U := hb

theorem evalS_quadJTerm {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (P : Fin n → A) (u x : JTerm n) :
    (quadJTerm u x).evalS P = u.evalS P * x.evalS P * u.evalS P := by
  dsimp [quadJTerm, JTerm.evalS]
  exact evalS_quad_identity (u.evalS P) (x.evalS P)

theorem evalS_wordJTerm {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (P : Fin n → A) (w : Word (Fin n)) :
    (wordJTerm w).evalS P = wordQuadOperator P w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [wordJTerm, evalS_quadJTerm, evalS_outcomeJTerm, ih]
    rfl

/-- `JTerm` encoding of a finite list of weighted words. -/
def wordListJTerm {n : ℕ} : List (ℝ × Word (Fin n)) → JTerm n
  | [] => .smul 0 .one
  | (a, w) :: xs => .add (.smul a (wordJTerm w)) (wordListJTerm xs)

theorem evalAlbert_wordListJTerm {n : ℕ} (p : Fin n → Albert)
    (l : List (ℝ × Word (Fin n))) :
    (wordListJTerm l).evalAlbert p = (l.map fun t => t.1 • nativeWordEffect p t.2).sum := by
  induction l with
  | nil => simp [wordListJTerm, JTerm.evalAlbert]
  | cons x xs ih =>
    rcases x with ⟨a, w⟩
    simp [wordListJTerm, JTerm.evalAlbert, evalAlbert_wordJTerm, ih]

theorem evalS_wordListJTerm {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (P : Fin n → A) (l : List (ℝ × Word (Fin n))) :
    (wordListJTerm l).evalS P = (l.map fun t => t.1 • wordQuadOperator P t.2).sum := by
  induction l with
  | nil => simp [wordListJTerm, JTerm.evalS]
  | cons x xs ih =>
    rcases x with ⟨a, w⟩
    simp [wordListJTerm, JTerm.evalS, evalS_wordJTerm, ih]

/-- `JTerm` encoding of a finitely supported real word combination `c : Word (Fin n) →₀ ℝ`. -/
def wordCombinationJTerm {n : ℕ} (c : Word (Fin n) →₀ ℝ) : JTerm n :=
  wordListJTerm (c.support.toList.map fun w => (c w, w))

private theorem sum_toList_eq {α M : Type*} [AddCommMonoid M] (s : Finset α) (f : α → M) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

theorem evalAlbert_wordCombinationJTerm {n : ℕ} (c : Word (Fin n) →₀ ℝ) (p : Fin n → Albert) :
    (wordCombinationJTerm c).evalAlbert p = nativeWordCombinationEffect c p := by
  rw [wordCombinationJTerm, evalAlbert_wordListJTerm, List.map_map]
  exact sum_toList_eq c.support (fun w => c w • nativeWordEffect p w)

theorem evalS_wordCombinationJTerm {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (c : Word (Fin n) →₀ ℝ) (P : Fin n → A) :
    (wordCombinationJTerm c).evalS P = c.sum (fun w a => a • wordQuadOperator P w) := by
  rw [wordCombinationJTerm, evalS_wordListJTerm, List.map_map]
  exact sum_toList_eq c.support (fun w => c w • wordQuadOperator P w)

/-! ### Free product `ℤ₂^{*n}`, group algebra `ℝ[ℤ₂^{*n}]`, and Cayley ball representation -/

/-- Reduced letter words in the free product `ℤ₂^{*n}` (`n` generators of order 2). -/
def IsReducedLetters {n : ℕ} : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | i :: j :: l => i ≠ j ∧ IsReducedLetters (j :: l)

/-- Elements of the free product `ℤ₂^{*n}` represented by reduced words. -/
abbrev RWord (n : ℕ) := { l : List (Fin n) // IsReducedLetters l }

/-- Left-multiplication toggle by generator `k` on a reduced letter list. -/
def toggleLetter {n : ℕ} (k : Fin n) : List (Fin n) → List (Fin n)
  | [] => [k]
  | j :: l => if k = j then l else k :: j :: l

private theorem isReducedLetters_tail {n : ℕ} {j : Fin n} {l : List (Fin n)}
    (h : IsReducedLetters (j :: l)) : IsReducedLetters l := by
  cases l with
  | nil => trivial
  | cons _ _ => exact h.2

theorem isReducedLetters_toggleLetter {n : ℕ} (k : Fin n) {l : List (Fin n)}
    (h : IsReducedLetters l) : IsReducedLetters (toggleLetter k l) := by
  cases l with
  | nil => trivial
  | cons j l' =>
    dsimp [toggleLetter]
    split_ifs with hkj
    · exact isReducedLetters_tail h
    · exact ⟨hkj, h⟩

/-- Left action of generator `k` on `RWord n`. -/
def rwordToggle {n : ℕ} (k : Fin n) (x : RWord n) : RWord n :=
  ⟨toggleLetter k x.1, isReducedLetters_toggleLetter k x.2⟩

theorem toggleLetter_toggleLetter {n : ℕ} (k : Fin n) {l : List (Fin n)}
    (hl : IsReducedLetters l) : toggleLetter k (toggleLetter k l) = l := by
  cases l with
  | nil => simp [toggleLetter]
  | cons j l' =>
    dsimp [toggleLetter]
    split_ifs with hkj
    · cases l' with
      | nil => simp [toggleLetter, hkj]
      | cons m rest =>
        have hjm : j ≠ m := hl.1
        subst hkj
        simp [toggleLetter, hjm]
    · simp [toggleLetter]

theorem rwordToggle_rwordToggle {n : ℕ} (k : Fin n) (x : RWord n) :
    rwordToggle k (rwordToggle k x) = x :=
  Subtype.ext (toggleLetter_toggleLetter k x.2)

theorem length_toggleLetter_le {n : ℕ} (k : Fin n) (l : List (Fin n)) :
    (toggleLetter k l).length ≤ l.length + 1 := by
  cases l with
  | nil => simp [toggleLetter]
  | cons j l' =>
    dsimp [toggleLetter]
    by_cases hkj : k = j
    · simp only [hkj, ↓reduceIte, List.length_cons]
      exact Nat.le_succ_of_le (Nat.le_succ _)
    · simp [hkj]

/-- Left action of an arbitrary list of generators on `RWord n`. -/
def actLetters {n : ℕ} (u : List (Fin n)) (y : RWord n) : RWord n :=
  u.foldr rwordToggle y

theorem actLetters_nil {n : ℕ} (y : RWord n) : actLetters ([] : List (Fin n)) y = y := rfl

theorem actLetters_cons {n : ℕ} (k : Fin n) (u : List (Fin n)) (y : RWord n) :
    actLetters (k :: u) y = rwordToggle k (actLetters u y) := rfl

theorem actLetters_concat {n : ℕ} (u : List (Fin n)) (y z : RWord n) :
    actLetters (actLetters u y).1 z = actLetters u (actLetters y.1 z) := by
  induction u with
  | nil => rfl
  | cons k u' ih =>
    rw [actLetters_cons, actLetters_cons, ← ih]
    rcases hr : actLetters u' y with ⟨r, hr_red⟩
    cases r with
    | nil => rfl
    | cons j rest =>
      by_cases hkj : k = j
      · have hstep : rwordToggle k ⟨j :: rest, hr_red⟩ = ⟨rest, isReducedLetters_tail hr_red⟩ :=
          Subtype.ext (by simp [rwordToggle, toggleLetter, hkj])
        rw [hstep]
        change actLetters rest z = rwordToggle k (rwordToggle j (actLetters rest z))
        rw [hkj, rwordToggle_rwordToggle]
      · have hstep : rwordToggle k ⟨j :: rest, hr_red⟩ =
            ⟨k :: j :: rest, ⟨hkj, hr_red⟩⟩ :=
          Subtype.ext (by simp [rwordToggle, toggleLetter, hkj])
        rw [hstep, actLetters_cons]

theorem actLetters_self_empty {n : ℕ} (x : RWord n) :
    actLetters x.1 ⟨[], trivial⟩ = x := by
  rcases x with ⟨l, hl⟩
  induction l with
  | nil => rfl
  | cons i l' ih =>
    cases l' with
    | nil => rfl
    | cons j rest =>
      have hsub := ih (isReducedLetters_tail hl)
      rw [actLetters_cons, hsub]
      apply Subtype.ext
      dsimp [rwordToggle, toggleLetter]
      simp [hl.1]

instance instMonoidRWord (n : ℕ) : Monoid (RWord n) where
  one := ⟨[], trivial⟩
  mul x y := actLetters x.1 y
  one_mul _ := rfl
  mul_one x := actLetters_self_empty x
  mul_assoc x y z := actLetters_concat x.1 y z

/-- Canonical involutive generator `r_k` in `RWord n`. -/
def rwordGen {n : ℕ} (k : Fin n) : RWord n := ⟨[k], trivial⟩

theorem rwordGen_mul_left {n : ℕ} (k : Fin n) (x : RWord n) :
    rwordGen k * x = rwordToggle k x := rfl

@[simp] theorem rwordGen_mul_rwordGen {n : ℕ} (k : Fin n) :
    rwordGen k * rwordGen k = 1 := by
  apply Subtype.ext
  change toggleLetter k [k] = []
  simp [toggleLetter]

/-- Lift any tuple of involutions (`s k * s k = 1`) to a monoid hom `RWord n →* A`. -/
def rwordLift {n : ℕ} {A : Type*} [Monoid A] (s : Fin n → A)
    (hs : ∀ k, s k * s k = 1) : RWord n →* A where
  toFun x := (x.1.map s).prod
  map_one' := rfl
  map_mul' x y := by
    have hstep : ∀ (k : Fin n) (l : List (Fin n)),
        ((toggleLetter k l).map s).prod = s k * (l.map s).prod := by
      intro k l
      cases l with
      | nil => simp [toggleLetter]
      | cons j l' =>
        dsimp [toggleLetter]
        split_ifs with hkj
        · subst hkj
          simp only [List.map_cons, List.prod_cons, ← mul_assoc, hs k, one_mul]
        · simp [List.map_cons, List.prod_cons]
    have hact : ∀ (u : List (Fin n)) (z : RWord n),
        ((actLetters u z).1.map s).prod = (u.map s).prod * (z.1.map s).prod := by
      intro u z
      induction u with
      | nil => simp [actLetters_nil]
      | cons k u' ih =>
        rw [actLetters_cons]
        change ((toggleLetter k (actLetters u' z).1).map s).prod = _
        rw [hstep, ih, List.map_cons, List.prod_cons, mul_assoc]
    exact hact x.1 y

@[simp] theorem rwordLift_gen {n : ℕ} {A : Type*} [Monoid A] (s : Fin n → A)
    (hs : ∀ k, s k * s k = 1) (k : Fin n) :
    rwordLift s hs (rwordGen k) = s k := by
  change ([k].map s).prod = s k
  simp

/-- The real group algebra `ℝ[ℤ₂^{*n}]` of the `n`-fold free product of `ℤ₂`. -/
abbrev GroupAlgebra (n : ℕ) := MonoidAlgebra ℝ (RWord n)

/-- Canonical reflection element `r_k` in `GroupAlgebra n`. -/
def groupGen (n : ℕ) (k : Fin n) : GroupAlgebra n := MonoidAlgebra.single (rwordGen k) 1

/-- Canonical projection element `p̄_k = (1 + r_k) / 2` in `GroupAlgebra n`. -/
def groupProj (n : ℕ) (k : Fin n) : GroupAlgebra n := (1 / 2 : ℝ) • (1 + groupGen n k)

theorem groupGen_mul_self (n : ℕ) (k : Fin n) : groupGen n k * groupGen n k = 1 := by
  rw [groupGen, MonoidAlgebra.single_mul_single, rwordGen_mul_rwordGen, one_mul,
    MonoidAlgebra.one_def]

theorem groupProj_mul_self (n : ℕ) (k : Fin n) : groupProj n k * groupProj n k = groupProj n k := by
  dsimp [groupProj]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have h : (1 + groupGen n k) * (1 + groupGen n k) = (2 : ℝ) • (1 + groupGen n k) := by
    simp only [mul_add, add_mul, one_mul, mul_one, groupGen_mul_self, two_smul]
    abel
  rw [h, smul_smul]
  norm_num

theorem reflection_of_idempotent_sq {A : Type*} [Ring A] [Algebra ℝ A] {P : A}
    (hP : P * P = P) :
    ((2 : ℝ) • P - 1) * ((2 : ℝ) • P - 1) = 1 := by
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, mul_one, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, hP, smul_smul]
  have h1 : (2 : ℝ) * 2 = 4 := by norm_num
  rw [h1]
  have h4 : (4 : ℝ) • P - (2 : ℝ) • P - (2 : ℝ) • P = 0 := by
    rw [sub_sub, ← add_smul, show (2 : ℝ) + 2 = 4 by norm_num, sub_self]
  calc
    (4 : ℝ) • P - (2 : ℝ) • P - ((2 : ℝ) • P - 1)
      = ((4 : ℝ) • P - (2 : ℝ) • P - (2 : ℝ) • P) + 1 := by abel
    _ = 1 := by rw [h4, zero_add]

/-- Universal algebra homomorphism `ℝ[ℤ₂^{*n}] →ₐ[ℝ] A` induced by any idempotent tuple `P_k`
in a unital associative real algebra `A`, sending `r_k ↦ 2 P_k - 1` and `p̄_k ↦ P_k`. -/
def groupAlgLift {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (P : Fin n → A) (hP : ∀ k, P k * P k = P k) : GroupAlgebra n →ₐ[ℝ] A :=
  MonoidAlgebra.lift ℝ A (RWord n)
    (rwordLift (fun k => (2 : ℝ) • P k - 1) fun k => reflection_of_idempotent_sq (hP k))

theorem groupAlgLift_groupGen {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (P : Fin n → A) (hP : ∀ k, P k * P k = P k) (k : Fin n) :
    groupAlgLift P hP (groupGen n k) = (2 : ℝ) • P k - 1 := by
  simp [groupAlgLift, groupGen]

theorem groupAlgLift_groupProj {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (P : Fin n → A) (hP : ∀ k, P k * P k = P k) (k : Fin n) :
    groupAlgLift P hP (groupProj n k) = P k := by
  rw [groupProj, map_smul, map_add, map_one, groupAlgLift_groupGen]
  have h : (1 : A) + ((2 : ℝ) • P k - 1) = (2 : ℝ) • P k := by abel
  rw [h, smul_smul]
  norm_num

/-- Image `E(c)` in the free-product group algebra `ℝ[ℤ₂^{*n}]`. -/
def freeProductImage {n : ℕ} (c : Word (Fin n) →₀ ℝ) : GroupAlgebra n :=
  c.sum (fun w a => a • wordQuadOperator (groupProj n) w)

theorem groupAlgLift_freeProductImage {n : ℕ} {A : Type} [Ring A] [Algebra ℝ A]
    (P : Fin n → A) (hP : ∀ k, P k * P k = P k) (c : Word (Fin n) →₀ ℝ) :
    groupAlgLift P hP (freeProductImage c) = (wordCombinationJTerm c).evalS P := by
  rw [evalS_wordCombinationJTerm, freeProductImage, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  clear hw
  rw [map_smul]
  congr 1
  induction w with
  | nil => simp [wordQuadOperator]
  | cons a w ih =>
    rw [wordQuadOperator, wordQuadOperator, map_mul, map_mul, ih]
    rcases a with ⟨k, b⟩
    cases b <;> simp [algebraicOutcome, groupAlgLift_groupProj]

/-- Algebra isomorphism retraction `UniversalProjectionAlgebra n →ₐ[ℝ] GroupAlgebra n`. -/
def universalToGroupAlg (n : ℕ) : UniversalProjectionAlgebra n →ₐ[ℝ] GroupAlgebra n :=
  RingQuot.liftAlgHom ℝ ⟨FreeAlgebra.lift ℝ (groupProj n), by
    intro x y h
    cases h with
    | generator k => simp [groupProj_mul_self]⟩

theorem universalToGroupAlg_proj (n : ℕ) (k : Fin n) :
    universalToGroupAlg n (universalProjection k) = groupProj n k := by
  simp [universalToGroupAlg, universalProjection, projectionQuotient]

theorem universalToGroupAlg_eval (n : ℕ) (c : Word (Fin n) →₀ ℝ) :
    universalToGroupAlg n (c.sum (fun w a => a • wordOperator (universalProjection (n := n)) w)) =
      freeProductImage c := by
  rw [freeProductImage, Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  clear hw
  rw [map_smul, ← wordQuadOperator_eq_wordOperator _ universalProjection_selfAdjoint]
  congr 1
  induction w with
  | nil => simp [wordQuadOperator]
  | cons a w ih =>
    rw [wordQuadOperator, wordQuadOperator, map_mul, map_mul, ih]
    rcases a with ⟨k, b⟩
    cases b <;> simp [algebraicOutcome, universalToGroupAlg_proj]

/-- Cayley ball of reduced words of length at most `M`. -/
abbrev Ball (n M : ℕ) := { x : RWord n // x.1.length ≤ M }

private def ballEmbed (n M : ℕ) (x : Ball n M) : Fin M → Option (Fin n) :=
  fun i => x.1.1[i.1]?

private theorem list_eq_of_getElem?_eq {α : Type*} (M : ℕ) :
    ∀ (l₁ l₂ : List α), l₁.length ≤ M → l₂.length ≤ M →
      (∀ i : Fin M, l₁[i.1]? = l₂[i.1]?) → l₁ = l₂ := by
  induction M with
  | zero =>
    intro l₁ l₂ h1 h2 _
    have hl1 : l₁ = [] := List.eq_nil_iff_length_eq_zero.mpr (Nat.le_zero.mp h1)
    have hl2 : l₂ = [] := List.eq_nil_iff_length_eq_zero.mpr (Nat.le_zero.mp h2)
    rw [hl1, hl2]
  | succ M ih =>
    intro l₁ l₂ h1 h2 heq
    cases l₁ with
    | nil =>
      cases l₂ with
      | nil => rfl
      | cons b bs =>
        have h0 := heq ⟨0, Nat.succ_pos M⟩
        simp at h0
    | cons a as =>
      cases l₂ with
      | nil =>
        have h0 := heq ⟨0, Nat.succ_pos M⟩
        simp at h0
      | cons b bs =>
        have h0 := heq ⟨0, Nat.succ_pos M⟩
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
        have htail : as = bs := ih as bs (Nat.le_of_succ_le_succ h1)
          (Nat.le_of_succ_le_succ h2) fun i => by
            have hs := heq i.succ
            simpa using hs
        rw [h0, htail]

private theorem ballEmbed_injective (n M : ℕ) : Function.Injective (ballEmbed n M) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact list_eq_of_getElem?_eq M x.1.1 y.1.1 x.2 y.2 (congr_fun h)

noncomputable instance instFiniteBall (n M : ℕ) : Finite (Ball n M) :=
  Finite.of_injective (ballEmbed n M) (ballEmbed_injective n M)

noncomputable instance instFintypeBall (n M : ℕ) : Fintype (Ball n M) :=
  Fintype.ofFinite (Ball n M)

/-- Involutive toggle on `Ball n M`, fixing boundary words whose toggle leaves the ball. -/
def ballToggle {n : ℕ} (M : ℕ) (k : Fin n) (x : Ball n M) : Ball n M :=
  if h : (rwordToggle k x.1).1.length ≤ M then ⟨rwordToggle k x.1, h⟩ else x

theorem ballToggle_involutive {n : ℕ} (M : ℕ) (k : Fin n) :
    Function.Involutive (ballToggle M k) := by
  intro x
  dsimp [ballToggle]
  split_ifs with h1 h2
  · exact Subtype.ext (rwordToggle_rwordToggle k x.1)
  · exfalso
    apply h2
    rw [rwordToggle_rwordToggle]
    exact x.2
  · simp [h1]

/-- Symmetric reflection matrix on `Ball n M` associated to generator `k`. -/
def ballReflection (n M : ℕ) (k : Fin n) : Matrix (Ball n M) (Ball n M) ℝ :=
  Matrix.of fun u v => if ballToggle M k v = u then 1 else 0

theorem ballReflection_transpose (n M : ℕ) (k : Fin n) :
    (ballReflection n M k)ᵀ = ballReflection n M k := by
  ext u v
  simp only [Matrix.transpose_apply, ballReflection, Matrix.of_apply]
  have hiff : ballToggle M k u = v ↔ ballToggle M k v = u :=
    ⟨fun h => by rw [← h, ballToggle_involutive M k], fun h => by rw [← h, ballToggle_involutive M k]⟩
  simp only [hiff]

theorem ballReflection_mul_self (n M : ℕ) (k : Fin n) :
    ballReflection n M k * ballReflection n M k = 1 := by
  ext u v
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hinv : ∀ x, ballToggle M k (ballToggle M k x) = x := ballToggle_involutive M k
  have h1 : ∀ w : Ball n M,
      ballReflection n M k u w * ballReflection n M k w v =
        if w = ballToggle M k u then (if ballToggle M k v = w then 1 else 0) else 0 := by
    intro w
    dsimp [ballReflection]
    by_cases hw : w = ballToggle M k u
    · have h1w : ballToggle M k w = u := by rw [hw, hinv]
      by_cases h2w : ballToggle M k v = w <;> simp [hw, h1w, h2w, hinv]
    · have h1w : ballToggle M k w ≠ u := fun heq => hw (by rw [← heq, hinv])
      simp [hw, h1w, hinv]
  simp_rw [h1, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  by_cases huv : u = v
  · subst huv; simp [ballToggle_involutive M k]
  · have hneq : ballToggle M k v ≠ ballToggle M k u := fun heq =>
      huv ((ballToggle_involutive M k).injective heq).symm
    simp [huv, hneq]

/-- Orthogonal projection matrix on `Ball n M` associated to generator `k`. -/
def ballProj (n M : ℕ) (k : Fin n) : Matrix (Ball n M) (Ball n M) ℝ :=
  (1 / 2 : ℝ) • (1 + ballReflection n M k)

theorem ballProj_transpose (n M : ℕ) (k : Fin n) :
    (ballProj n M k)ᵀ = ballProj n M k := by
  simp [ballProj, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
    ballReflection_transpose]

theorem ballProj_mul_self (n M : ℕ) (k : Fin n) :
    ballProj n M k * ballProj n M k = ballProj n M k := by
  dsimp [ballProj]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have h : (1 + ballReflection n M k) * (1 + ballReflection n M k) =
      (2 : ℝ) • (1 + ballReflection n M k) := by
    simp only [mul_add, add_mul, one_mul, mul_one, ballReflection_mul_self, two_smul]
    abel
  rw [h, smul_smul]
  norm_num

private def WithinLength {n : ℕ} (k : ℕ) (z : GroupAlgebra n) : Prop :=
  ∀ x ∈ z.coeff.support, x.1.length ≤ k

private theorem withinLength_one {n : ℕ} : WithinLength 0 (1 : GroupAlgebra n) := by
  intro x hx
  rw [Finsupp.mem_support_iff, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single] at hx
  by_cases h : (1 : RWord n) = x
  · subst h; rfl
  · simp [Finsupp.single_apply, h] at hx

private theorem withinLength_add {n k : ℕ} {z₁ z₂ : GroupAlgebra n}
    (h1 : WithinLength k z₁) (h2 : WithinLength k z₂) : WithinLength k (z₁ + z₂) := by
  intro x hx
  rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_add, Finsupp.add_apply] at hx
  by_cases hx1 : z₁.coeff x = 0
  · rw [hx1, zero_add] at hx
    exact h2 x (Finsupp.mem_support_iff.mpr hx)
  · exact h1 x (Finsupp.mem_support_iff.mpr hx1)

private theorem withinLength_smul {n k : ℕ} (r : ℝ) {z : GroupAlgebra n}
    (hz : WithinLength k z) : WithinLength k (r • z) := by
  intro x hx
  rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hx
  exact hz x (Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hx))

private theorem withinLength_sub {n k : ℕ} {z₁ z₂ : GroupAlgebra n}
    (h1 : WithinLength k z₁) (h2 : WithinLength k z₂) : WithinLength k (z₁ - z₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ z₂]
  exact withinLength_add h1 (withinLength_smul (-1) h2)

private theorem withinLength_mono {n k m : ℕ} {z : GroupAlgebra n} (hkm : k ≤ m)
    (hz : WithinLength k z) : WithinLength m z :=
  fun x hx => (hz x hx).trans hkm

private theorem coeff_groupGen_mul {n : ℕ} (i : Fin n) (z : GroupAlgebra n) (x : RWord n) :
    (groupGen n i * z).coeff x = z.coeff (rwordToggle i x) := by
  have hH : ∀ d ∈ z.coeff.support, rwordGen i * d = x ↔ d = rwordToggle i x := by
    intro d _
    rw [rwordGen_mul_left]
    exact ⟨fun h => by rw [← h, rwordToggle_rwordToggle], fun h => by rw [h, rwordToggle_rwordToggle]⟩
  rw [groupGen, MonoidAlgebra.coeff_single_mul_eq_mul_coeff (rwordToggle i x) hH]
  simp

private theorem withinLength_groupGen_mul {n k : ℕ} (i : Fin n) {z : GroupAlgebra n}
    (hz : WithinLength k z) : WithinLength (k + 1) (groupGen n i * z) := by
  intro x hx
  rw [Finsupp.mem_support_iff, coeff_groupGen_mul] at hx
  have hy := hz (rwordToggle i x) (Finsupp.mem_support_iff.mpr hx)
  calc
    x.1.length = (rwordToggle i (rwordToggle i x)).1.length := by rw [rwordToggle_rwordToggle]
    _ ≤ (rwordToggle i x).1.length + 1 := length_toggleLetter_le i _
    _ ≤ k + 1 := Nat.add_le_add_right hy 1

private def restrictVec {n : ℕ} (M : ℕ) (z : GroupAlgebra n) : Ball n M → ℝ :=
  fun u => z.coeff u.1

private theorem restrictVec_add {n M : ℕ} (z₁ z₂ : GroupAlgebra n) :
    restrictVec M (z₁ + z₂) = restrictVec M z₁ + restrictVec M z₂ := rfl

private theorem restrictVec_sub {n M : ℕ} (z₁ z₂ : GroupAlgebra n) :
    restrictVec M (z₁ - z₂) = restrictVec M z₁ - restrictVec M z₂ := rfl

private theorem restrictVec_smul {n M : ℕ} (r : ℝ) (z : GroupAlgebra n) :
    restrictVec M (r • z) = r • restrictVec M z := rfl

private theorem ballReflection_mulVec {n k M : ℕ} (hkM : k < M) (i : Fin n)
    {z : GroupAlgebra n} (hz : WithinLength k z) :
    ballReflection n M i *ᵥ restrictVec M z = restrictVec M (groupGen n i * z) := by
  ext u
  rw [Matrix.mulVec, dotProduct]
  have hinv : ∀ x, ballToggle M i (ballToggle M i x) = x := ballToggle_involutive M i
  have hterm : ∀ v : Ball n M, ballReflection n M i u v * restrictVec M z v =
      if v = ballToggle M i u then z.coeff v.1 else 0 := by
    intro v
    dsimp [ballReflection, restrictVec]
    by_cases hv : v = ballToggle M i u
    · have h1v : ballToggle M i v = u := by rw [hv, hinv]
      simp [hv, h1v, hinv]
    · have h1v : ballToggle M i v ≠ u := fun heq => hv (by rw [← heq, hinv])
      simp [hv, h1v, hinv]
  simp_rw [hterm, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  dsimp [restrictVec]
  rw [coeff_groupGen_mul]
  dsimp [ballToggle]
  split_ifs with hlen
  · rfl
  · have hlt : k < (rwordToggle i u.1).1.length := lt_trans hkM (Nat.lt_of_not_le hlen)
    have hrhs : z.coeff (rwordToggle i u.1) = 0 := by
      by_contra hne
      exact Nat.not_le_of_lt hlt (hz _ (Finsupp.mem_support_iff.mpr hne))
    have hu_len : M ≤ u.1.1.length := by
      have h1 := Nat.lt_of_not_le hlen
      have h2 := length_toggleLetter_le i u.1.1
      change (rwordToggle i u.1).1.length ≤ u.1.1.length + 1 at h2
      omega
    have hk_lt_u : k < u.1.1.length := lt_of_lt_of_le hkM hu_len
    have hlhs : z.coeff u.1 = 0 := by
      by_contra hne
      exact Nat.not_le_of_lt hk_lt_u (hz _ (Finsupp.mem_support_iff.mpr hne))
    rw [hlhs, hrhs]

private theorem ballOutcome_mulVec {n k M : ℕ} (hkM : k < M) (a : Outcome (Fin n))
    {z : GroupAlgebra n} (hz : WithinLength k z) :
    WithinLength (k + 1) (algebraicOutcome (groupProj n) a * z) ∧
      algebraicOutcome (ballProj n M) a *ᵥ restrictVec M z =
        restrictVec M (algebraicOutcome (groupProj n) a * z) := by
  rcases a with ⟨i, b⟩
  have h1z : WithinLength (k + 1) z := withinLength_mono (Nat.le_succ k) hz
  have hgz : WithinLength (k + 1) (groupGen n i * z) := withinLength_groupGen_mul i hz
  have hrefl : ballReflection n M i *ᵥ restrictVec M z = restrictVec M (groupGen n i * z) :=
    ballReflection_mulVec hkM i hz
  cases b
  · have heq_alg : algebraicOutcome (groupProj n) (i, false) * z =
        (1 / 2 : ℝ) • (z - groupGen n i * z) := by
      simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte, groupProj,
        sub_mul, one_mul, Algebra.smul_mul_assoc, add_mul]
      calc
        z - (1 / 2 : ℝ) • (z + groupGen n i * z)
          = ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • z) -
              ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (groupGen n i * z)) := by
            rw [← two_smul ℝ ((1 / 2 : ℝ) • z), smul_smul,
              show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul, smul_add]
        _ = (1 / 2 : ℝ) • (z - groupGen n i * z) := by rw [smul_sub]; abel
    have heq_mat : algebraicOutcome (ballProj n M) (i, false) *ᵥ restrictVec M z =
        (1 / 2 : ℝ) • (restrictVec M z - ballReflection n M i *ᵥ restrictVec M z) := by
      simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte, ballProj,
        Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec]
      calc
        restrictVec M z - (1 / 2 : ℝ) • (restrictVec M z + ballReflection n M i *ᵥ restrictVec M z)
          = ((1 / 2 : ℝ) • restrictVec M z + (1 / 2 : ℝ) • restrictVec M z) -
              ((1 / 2 : ℝ) • restrictVec M z +
                (1 / 2 : ℝ) • (ballReflection n M i *ᵥ restrictVec M z)) := by
            rw [← two_smul ℝ ((1 / 2 : ℝ) • restrictVec M z), smul_smul,
              show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul, smul_add]
        _ = (1 / 2 : ℝ) • (restrictVec M z - ballReflection n M i *ᵥ restrictVec M z) := by
            rw [smul_sub]; abel
    refine ⟨?_, ?_⟩
    · rw [heq_alg]
      exact withinLength_smul _ (withinLength_sub h1z hgz)
    · rw [heq_mat, heq_alg, hrefl, restrictVec_smul, restrictVec_sub]
  · have heq_alg : algebraicOutcome (groupProj n) (i, true) * z =
        (1 / 2 : ℝ) • (z + groupGen n i * z) := by
      simp only [algebraicOutcome, ↓reduceIte, groupProj, Algebra.smul_mul_assoc, add_mul, one_mul]
    have heq_mat : algebraicOutcome (ballProj n M) (i, true) *ᵥ restrictVec M z =
        (1 / 2 : ℝ) • (restrictVec M z + ballReflection n M i *ᵥ restrictVec M z) := by
      simp only [algebraicOutcome, ↓reduceIte, ballProj, Matrix.smul_mulVec,
        Matrix.add_mulVec, Matrix.one_mulVec]
    refine ⟨?_, ?_⟩
    · rw [heq_alg]
      exact withinLength_smul _ (withinLength_add h1z hgz)
    · rw [heq_mat, heq_alg, hrefl, restrictVec_smul, restrictVec_add]

private theorem wordQuadOperator_ball_mulVec {n : ℕ} (w : Word (Fin n)) :
    ∀ (k M : ℕ) (z : GroupAlgebra n), k + 2 * w.length ≤ M → WithinLength k z →
      WithinLength (k + 2 * w.length) (wordQuadOperator (groupProj n) w * z) ∧
        wordQuadOperator (ballProj n M) w *ᵥ restrictVec M z =
          restrictVec M (wordQuadOperator (groupProj n) w * z) := by
  induction w with
  | nil =>
    intro k M z _ hz
    simpa [wordQuadOperator] using hz
  | cons a w' ih =>
    intro k M z hkM hz
    simp only [List.length_cons, Nat.mul_succ] at hkM ⊢
    have hk_lt : k < M := by omega
    obtain ⟨hz1, hv1⟩ := ballOutcome_mulVec hk_lt a hz
    obtain ⟨hz2, hv2⟩ := ih (k + 1) M _ (by omega) hz1
    have hk2_lt : k + 1 + 2 * w'.length < M := by omega
    obtain ⟨hz3, hv3⟩ := ballOutcome_mulVec hk2_lt a hz2
    refine ⟨?_, ?_⟩
    · convert hz3 using 1
      · omega
      · simp [wordQuadOperator, mul_assoc]
    · simp only [wordQuadOperator, ← Matrix.mulVec_mulVec, hv1, hv2, hv3, mul_assoc]

private theorem finset_sum_mulVec {α R : Type*} [Fintype α] [Semiring R] {ι : Type*}
    (s : Finset ι) (f : ι → Matrix α α R) (v : α → R) :
    (∑ i ∈ s, f i) *ᵥ v = ∑ i ∈ s, f i *ᵥ v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | insert i s hi ih => simp [Finset.sum_insert hi, Matrix.add_mulVec, ih]

private theorem withinLength_finset_sum {n M : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → GroupAlgebra n) (hf : ∀ i ∈ s, WithinLength M (f i)) :
    WithinLength M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x hx
    simp at hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact withinLength_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem freeProductImage_eq_zero_of_ballVanishing {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    let M : ℕ := 2 * c.support.sup List.length
    (c.sum (fun w a => a • wordOperator (ballProj n M) w) = 0) →
    freeProductImage c = 0 := by
  intro M hball
  have hstar : ∀ k, star (ballProj n M k) = ballProj n M k := fun k => by
    ext u v
    simp only [Matrix.star_apply, star_trivial]
    exact congrArg (fun m : Matrix (Ball n M) (Ball n M) ℝ => m u v) (ballProj_transpose n M k)
  have hsub : ∀ w ∈ c.support, 0 + 2 * w.length ≤ M := fun w hw => by
    rw [zero_add]
    exact Nat.mul_le_mul_left 2 (Finset.le_sup (f := List.length) hw)
  have heff : ∀ w ∈ c.support,
      WithinLength M (wordQuadOperator (groupProj n) w) ∧
        wordOperator (ballProj n M) w *ᵥ restrictVec M 1 =
          restrictVec M (wordQuadOperator (groupProj n) w) := fun w hw => by
    obtain ⟨hw1, hw2⟩ := wordQuadOperator_ball_mulVec w 0 M 1 (hsub w hw) withinLength_one
    rw [mul_one] at hw1 hw2
    rw [wordQuadOperator_eq_wordOperator _ hstar] at hw2
    exact ⟨withinLength_mono (hsub w hw) hw1, hw2⟩
  have hsum_wl : WithinLength M (freeProductImage c) := by
    rw [freeProductImage, Finsupp.sum]
    exact withinLength_finset_sum c.support _ fun w hw =>
      withinLength_smul (c w) (heff w hw).1
  have hvec_zero : restrictVec M (freeProductImage c) = 0 := by
    have hmul : (c.sum (fun w a => a • wordOperator (ballProj n M) w)) *ᵥ restrictVec M 1 = 0 := by
      rw [hball, Matrix.zero_mulVec]
    rw [Finsupp.sum, finset_sum_mulVec] at hmul
    have hsum_eq : (∑ w ∈ c.support, (c w • wordOperator (ballProj n M) w) *ᵥ restrictVec M 1) =
        restrictVec M (freeProductImage c) := by
      calc
        (∑ w ∈ c.support, (c w • wordOperator (ballProj n M) w) *ᵥ restrictVec M 1)
          = ∑ w ∈ c.support, c w • (wordOperator (ballProj n M) w *ᵥ restrictVec M 1) := by
            refine Finset.sum_congr rfl fun w _ => ?_
            exact Matrix.smul_mulVec (c w) (wordOperator (ballProj n M) w) (restrictVec M 1)
        _ = ∑ w ∈ c.support, restrictVec M (c w • wordQuadOperator (groupProj n) w) := by
            refine Finset.sum_congr rfl fun w hw => ?_
            rw [(heff w hw).2, ← restrictVec_smul]
        _ = restrictVec M (∑ w ∈ c.support, c w • wordQuadOperator (groupProj n) w) := by
            ext u
            simp [restrictVec, MonoidAlgebra.coeff_sum]
    rw [← hsum_eq, hmul]
  ext x
  by_cases hx : x ∈ (freeProductImage c).coeff.support
  · have hx_len : x.1.length ≤ M := hsum_wl x hx
    have h0 := congr_fun hvec_zero ⟨x, hx_len⟩
    exact h0
  · rw [Finsupp.notMem_support_iff.mp hx]
    rfl

private def matrixReindexAlgHom {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Matrix α α ℝ →ₐ[ℝ] Matrix β β ℝ where
  toFun := Matrix.reindex e e
  map_one' := by simp [Matrix.reindex_apply]
  map_mul' A B := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  map_zero' := by simp [Matrix.reindex_apply]
  map_add' A B := by
    ext i j
    simp [Matrix.reindex_apply]
  commutes' r := by
    ext i j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.reindex_apply, Matrix.one_apply]

private theorem matrixReindexAlgHom_star {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (A : Matrix α α ℝ) :
    star (matrixReindexAlgHom e A) = matrixReindexAlgHom e (star A) := by
  ext i j
  simp only [Matrix.star_apply, star_trivial]
  rfl

private theorem matrixReindexAlgHom_transpose {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (A : Matrix α α ℝ) :
    (matrixReindexAlgHom e A)ᵀ = matrixReindexAlgHom e (Aᵀ) := rfl

private theorem matrixReindexAlgHom_injective {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Function.Injective (matrixReindexAlgHom e) :=
  (Matrix.reindex e e).injective

private theorem matrix_eq_zero_of_dotProduct_eq_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hAsym : Aᵀ = A)
    (hquad : ∀ v : Fin N → ℝ, dotProduct v v = 1 → dotProduct v (A *ᵥ v) = 0) :
    A = 0 := by
  have hall : ∀ v : Fin N → ℝ, dotProduct v (A *ᵥ v) = 0 := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    · have hpos : 0 < dotProduct v v := by
        have hne : ∃ i, v i ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hv (funext hcon)
        rcases hne with ⟨i₀, hi₀⟩
        have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin N)), 0 ≤ v i * v i :=
          fun i _ => mul_self_nonneg (v i)
        have hlt : 0 < v i₀ * v i₀ := mul_self_pos.mpr hi₀
        exact Finset.sum_pos' hnonneg ⟨i₀, Finset.mem_univ i₀, hlt⟩
      let r : ℝ := Real.sqrt (dotProduct v v)
      have hr_pos : 0 < r := Real.sqrt_pos.mpr hpos
      have hr_sq : r * r = dotProduct v v := Real.mul_self_sqrt hpos.le
      let u : Fin N → ℝ := r⁻¹ • v
      have hu : dotProduct u u = 1 := by
        simp only [u, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← hr_sq]
        field_simp [hr_pos.ne']
      have h0 := hquad u hu
      have hscaled : dotProduct u (A *ᵥ u) = (r⁻¹ * r⁻¹) * dotProduct v (A *ᵥ v) := by
        simp only [u, dotProduct_smul, smul_dotProduct, Matrix.mulVec_smul, smul_eq_mul]
        ring
      rw [hscaled] at h0
      exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (inv_ne_zero hr_pos.ne')
        (inv_ne_zero hr_pos.ne'))
  ext i j
  let ei : Fin N → ℝ := fun k => if k = i then 1 else 0
  let ej : Fin N → ℝ := fun k => if k = j then 1 else 0
  have hei : dotProduct ei (A *ᵥ ei) = A i i := by
    simp [ei, Matrix.mulVec, dotProduct]
  have hej : dotProduct ej (A *ᵥ ej) = A j j := by
    simp [ej, Matrix.mulVec, dotProduct]
  have heij : dotProduct (ei + ej) (A *ᵥ (ei + ej)) = A i i + A i j + A j i + A j j := by
    simp only [ei, ej, Matrix.mulVec, dotProduct, Pi.add_apply]
    simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
    ring
  have hsym : A j i = A i j := by
    change Aᵀ i j = A i j
    rw [hAsym]
  have h1 := hall ei
  have h2 := hall ej
  have h3 := hall (ei + ej)
  rw [hei] at h1
  rw [hej] at h2
  rw [heij, h1, h2, hsym] at h3
  change A i j = 0
  linarith

/-- Operational projective equality (`prop:cer:noequality`(a)): a real linear combination of
chronological measurement words is a projective equality iff its expected value vanishes in every
finite-dimensional real Hilbert projective realization `(ℝ^N, P₁, ..., Pₙ, v)`. -/
def IsProjectiveEquality {n : ℕ} (c : Word (Fin n) →₀ ℝ) : Prop :=
  ∀ (N : ℕ) (P : Fin n → Matrix (Fin N) (Fin N) ℝ),
    (∀ k, (P k)ᵀ = P k ∧ P k * P k = P k) →
    ∀ v : Fin N → ℝ, dotProduct v v = 1 →
    c.sum (fun w a => a * dotProduct v (wordOperator P w *ᵥ v)) = 0

private theorem wordOperator_matrix_transpose {ι : Type*} {N : ℕ}
    (P : ι → Matrix (Fin N) (Fin N) ℝ) (w : Word ι) :
    (wordOperator P w)ᵀ = wordOperator P w := by
  have h := wordOperator_star P w
  ext i j
  have hij := congrFun (congrFun h i) j
  simpa [Matrix.star_apply] using hij

private theorem dotProduct_wordCombination_eq {ι : Type*} {N : ℕ}
    (c : Word ι →₀ ℝ) (P : ι → Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    dotProduct v ((c.sum (fun w a => a • wordOperator P w)) *ᵥ v) =
      c.sum (fun w a => a * dotProduct v (wordOperator P w *ᵥ v)) := by
  rw [Finsupp.sum, Finsupp.sum, finset_sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Characterization `prop:cer:noequality`(a) connecting finite-dimensional real projective
equalities, matrix operator vanishing, `GroupAlgebra n = ℝ[ℤ₂^{*n}]`, `UniversalProjectionAlgebra n`,
`AlgebraicProjectiveData`, and `JTerm.VanishesOnSpecialIdempotents`. -/
theorem prop_cer_noequality_a {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    List.TFAE [
      IsProjectiveEquality c,
      ∀ (N : ℕ) (P : Fin n → Matrix (Fin N) (Fin N) ℝ),
        (∀ k, (P k)ᵀ = P k ∧ P k * P k = P k) →
        c.sum (fun w a => a • wordOperator P w) = 0,
      freeProductImage c = 0,
      c.sum (fun w a => a • wordOperator (fun k => universalProjection (n := n) k) w) = 0,
      (wordCombinationJTerm c).VanishesOnSpecialIdempotents,
      ∀ (A : Type) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin n) A),
        c.sum (fun w a => a * M.probability w) = 0
    ] := by
  have h12 : IsProjectiveEquality c →
      ∀ (N : ℕ) (P : Fin n → Matrix (Fin N) (Fin N) ℝ),
        (∀ k, (P k)ᵀ = P k ∧ P k * P k = P k) →
        c.sum (fun w a => a • wordOperator P w) = 0 := by
    intro hc N P hP
    apply matrix_eq_zero_of_dotProduct_eq_zero
    · rw [Finsupp.sum, Matrix.transpose_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Matrix.transpose_smul, wordOperator_matrix_transpose P w]
    · intro v hv
      rw [dotProduct_wordCombination_eq]
      exact hc N P hP v hv
  have h23 : (∀ (N : ℕ) (P : Fin n → Matrix (Fin N) (Fin N) ℝ),
        (∀ k, (P k)ᵀ = P k ∧ P k * P k = P k) →
        c.sum (fun w a => a • wordOperator P w) = 0) →
      freeProductImage c = 0 := by
    intro hmat
    let M : ℕ := 2 * c.support.sup List.length
    let e : Ball n M ≃ Fin (Fintype.card (Ball n M)) := Fintype.equivFin (Ball n M)
    let f : Matrix (Ball n M) (Ball n M) ℝ →ₐ[ℝ]
        Matrix (Fin (Fintype.card (Ball n M))) (Fin (Fintype.card (Ball n M))) ℝ :=
      matrixReindexAlgHom e
    let P : Fin n → Matrix (Fin (Fintype.card (Ball n M))) (Fin (Fintype.card (Ball n M))) ℝ :=
      fun k => f (ballProj n M k)
    have hP : ∀ k, (P k)ᵀ = P k ∧ P k * P k = P k := fun k => by
      refine ⟨?_, ?_⟩
      · rw [matrixReindexAlgHom_transpose, ballProj_transpose]
      · rw [← map_mul, ballProj_mul_self]
    have hzero := hmat (Fintype.card (Ball n M)) P hP
    have hmap : f (c.sum (fun w a => a • wordOperator (ballProj n M) w)) = 0 := by
      have hamp : ∀ w : Word (Fin n),
          f (wordAmplitude (ballProj n M) w) = wordAmplitude P w := by
        intro w
        induction w using List.reverseRecOn with
        | nil => simp [wordAmplitude]
        | append_singleton w' a ih =>
          rw [wordAmplitude_append_singleton, wordAmplitude_append_singleton, map_mul, ih]
          rcases a with ⟨k, b⟩
          cases b <;> simp [algebraicOutcome, P]
      rw [Finsupp.sum, map_sum, ← hzero, Finsupp.sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [map_smul]
      congr 1
      dsimp only [wordOperator, f]
      rw [map_mul, ← matrixReindexAlgHom_star]
      change star (f (wordAmplitude (ballProj n M) w)) * f (wordAmplitude (ballProj n M) w) = _
      rw [hamp w]
    have hball : c.sum (fun w a => a • wordOperator (ballProj n M) w) = 0 :=
      matrixReindexAlgHom_injective e (hmap.trans (map_zero f).symm)
    exact freeProductImage_eq_zero_of_ballVanishing c hball
  have h35 : freeProductImage c = 0 → (wordCombinationJTerm c).VanishesOnSpecialIdempotents := by
    intro hfree A _ _ P hP
    rw [← groupAlgLift_freeProductImage P hP, hfree, map_zero]
  have h54 : (wordCombinationJTerm c).VanishesOnSpecialIdempotents →
      c.sum (fun w a => a • wordOperator (fun k => universalProjection (n := n) k) w) = 0 := by
    intro hspec
    have h0 := hspec (UniversalProjectionAlgebra n) universalProjection universalProjection_idempotent
    rw [evalS_wordCombinationJTerm] at h0
    rw [← h0, Finsupp.sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [wordQuadOperator_eq_wordOperator _ universalProjection_selfAdjoint]
  have h43 : c.sum (fun w a => a • wordOperator (fun k => universalProjection (n := n) k) w) = 0 →
      freeProductImage c = 0 := by
    intro hupa
    rw [← universalToGroupAlg_eval, hupa, map_zero]
  have h56 : (wordCombinationJTerm c).VanishesOnSpecialIdempotents →
      ∀ (A : Type) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin n) A),
        c.sum (fun w a => a * M.probability w) = 0 := by
    intro hspec A _ _ _ _ _ _ M
    let _ : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm
    have h0 := hspec A M.projection M.idempotent
    rw [evalS_wordCombinationJTerm] at h0
    have hst : M.state (c.sum (fun w a => a • wordQuadOperator M.projection w)) = 0 := by
      rw [h0, map_zero]
    rw [Finsupp.sum, map_sum] at hst
    rw [Finsupp.sum, ← hst]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, smul_eq_mul, AlgebraicProjectiveData.probability,
      wordQuadOperator_eq_wordOperator _ M.selfAdjoint]
  have h61 : (∀ (A : Type) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin n) A),
        c.sum (fun w a => a * M.probability w) = 0) →
      IsProjectiveEquality c := by
    intro halg N P hP v hv
    let M : AlgebraicProjectiveData (Fin n) (Matrix (Fin N) (Fin N) ℝ) :=
      { projection := P
        idempotent := fun k => (hP k).2
        selfAdjoint := fun k => by
          ext i j
          simpa [Matrix.star_apply] using congrFun (congrFun (hP k).1 i) j
        state :=
          { toFun := fun X => dotProduct v (X *ᵥ v)
            map_add' := fun X Y => by simp [Matrix.add_mulVec, dotProduct_add]
            map_smul' := fun r X => by simp [Matrix.smul_mulVec, dotProduct_smul] }
        state_unit := by simp [Matrix.one_mulVec, hv]
        state_star := fun X => by
          have hstar : star X = Xᵀ := by
            ext i j; simp [Matrix.star_apply]
          dsimp
          rw [hstar, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]
        state_positive := fun X => by
          have hstar : star X = Xᵀ := by
            ext i j; simp [Matrix.star_apply]
          dsimp
          rw [hstar, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
          exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((X *ᵥ v) i) }
    exact halg (Matrix (Fin N) (Fin N) ℝ) M
  tfae_have 1 → 2 := h12
  tfae_have 2 → 3 := h23
  tfae_have 3 → 5 := h35
  tfae_have 5 → 4 := h54
  tfae_have 4 → 3 := h43
  tfae_have 5 → 6 := h56
  tfae_have 6 → 1 := h61
  tfae_finish

theorem isProjectiveEquality_iff_specialVanishing {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    IsProjectiveEquality c ↔ (wordCombinationJTerm c).VanishesOnSpecialIdempotents :=
  (prop_cer_noequality_a c).out 1 5

theorem isProjectiveEquality_iff_freeProductZero {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    IsProjectiveEquality c ↔ freeProductImage c = 0 :=
  (prop_cer_noequality_a c).out 1 3

theorem isProjectiveEquality_iff_universalAlgebraZero {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    IsProjectiveEquality c ↔
      c.sum (fun w a => a • wordOperator (fun k => universalProjection (n := n) k) w) = 0 :=
  (prop_cer_noequality_a c).out 1 4

theorem isProjectiveEquality_iff_algebraicProjectiveData {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    IsProjectiveEquality c ↔
      ∀ (A : Type) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin n) A),
        c.sum (fun w a => a * M.probability w) = 0 :=
  (prop_cer_noequality_a c).out 1 6

/-! ## Section 5: Transport along `NativeAlbertAutomorphism` and `cor:so:residual` headlines -/

theorem map_nativeOutcome {ι : Type*} (g : NativeAlbertAutomorphism) (p : ι → Albert)
    (a : Outcome ι) :
    g.linearEquiv (nativeOutcome p a) = nativeOutcome (fun k => g.linearEquiv (p k)) a := by
  rcases a with ⟨k, b⟩
  cases b <;> simp [nativeOutcome, map_sub, g.preserves_unit]

theorem map_nativeWordEffect {ι : Type*} (g : NativeAlbertAutomorphism) (p : ι → Albert)
    (w : Word ι) :
    g.linearEquiv (nativeWordEffect p w) = nativeWordEffect (fun k => g.linearEquiv (p k)) w := by
  induction w with
  | nil => exact g.preserves_unit
  | cons a w ih =>
    simp only [nativeWordEffect, g.map_quadraticMap, map_nativeOutcome, ih]

theorem map_nativeWordCombinationEffect {ι : Type*} (g : NativeAlbertAutomorphism)
    (c : Word ι →₀ ℝ) (p : ι → Albert) :
    g.linearEquiv (nativeWordCombinationEffect c p) =
      nativeWordCombinationEffect c (fun k => g.linearEquiv (p k)) := by
  simp only [nativeWordCombinationEffect, Finsupp.sum, map_sum, map_smul, map_nativeWordEffect]

private theorem deriv_linearEquiv_comp (e : Albert ≃ₗ[ℝ] Albert) {f : ℝ → Albert} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) :
    deriv (fun s => e (f s)) t = e (deriv f t) :=
  deriv_clm_comp e.toLinearMap.toContinuousLinearMap hf

private theorem deriv2_linearEquiv_comp (e : Albert ≃ₗ[ℝ] Albert) {f : ℝ → Albert}
    (hf : ContDiffAt ℝ 2 f 0) :
    deriv (deriv (fun s => e (f s))) 0 = e (deriv (deriv f) 0) := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (fun s => e (f s)) t = e (deriv f t) := by
    filter_upwards [hf.eventually (by norm_num)] with t htf
    exact deriv_linearEquiv_comp e (htf.differentiableAt (by norm_num))
  have hdf : DifferentiableAt ℝ (deriv f) 0 :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_linearEquiv_comp e hdf]

/-- `cor:so:residual` for any `ComplexWindow` `W` and any word combination `c` whose `JTerm`
vanishes on all special idempotent tuples (`VanishesOnSpecialIdempotents`). -/
theorem cor_so_residual_from_specialVanishing {n : ℕ} (W : ComplexWindow)
    (c : Word (Fin n) →₀ ℝ) (hc : (wordCombinationJTerm c).VanishesOnSpecialIdempotents)
    (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k, ContDiff ℝ 3 (p k))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, W.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 3 r ∧
      r 0 = 0 ∧
      deriv r 0 = 0 ∧
      (∀ w : Albert, W.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ ρ : Albert, W.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
          (fun t => t ^ 3)) := by
  intro r Q
  obtain ⟨g, hg⟩ := native_complexWindow_conjugate_standard W
  let pg : Fin n → ℝ → Albert := fun k t => g.linearEquiv (p k t)
  let G : Albert →L[ℝ] Albert := g.linearEquiv.toLinearMap.toContinuousLinearMap
  have hpg_diff : ∀ k, ContDiff ℝ 3 (pg k) := fun k => G.contDiff.comp (hp_diff k)
  have hpg_idem : ∀ k t, jordanMul (pg k t) (pg k t) = pg k t := fun k t => by
    dsimp [pg]
    rw [← g.preserves_product, hp_idem k t]
  have hpg_base : ∀ k, standardComplexWindow.Contains (pg k 0) := fun k => by
    obtain ⟨M, hM⟩ := hp_base k
    exact ⟨M, by rw [← hg M, hM]⟩
  have hstd := standardWindow_residual_of_specialVanishing (wordCombinationJTerm c) hc pg
    hpg_diff hpg_idem hpg_base
  rcases hstd with ⟨hrg_diff, hrg0, hdrg0, hQg_perp, hQg_orth, _, _⟩
  have hrg_eq : (fun t => (wordCombinationJTerm c).evalAlbert (fun k => pg k t)) =
      fun t => g.linearEquiv (r t) := by
    funext t
    rw [evalAlbert_wordCombinationJTerm, ← map_nativeWordCombinationEffect g c (fun k => p k t)]
  have hr_eq : r = fun t => (wordCombinationJTerm c).evalAlbert (fun k => p k t) := by
    funext t
    exact (evalAlbert_wordCombinationJTerm c (fun k => p k t)).symm
  have hr_diff : ContDiff ℝ 3 r := by
    rw [hr_eq]
    exact contDiff_evalAlbert hp_diff (wordCombinationJTerm c)
  have hr0 : r 0 = 0 := by
    apply g.linearEquiv.injective
    rw [map_zero]
    have h0 := congr_fun hrg_eq 0
    rw [← h0]
    exact hrg0
  have hdr0 : deriv r 0 = 0 := by
    apply g.linearEquiv.injective
    rw [map_zero, ← deriv_linearEquiv_comp g.linearEquiv (hr_diff.differentiable (by norm_num) 0)]
    have hfun : (fun t => g.linearEquiv (r t)) =
        fun t => (wordCombinationJTerm c).evalAlbert (fun k => pg k t) := hrg_eq.symm
    rw [hfun]
    exact hdrg0
  have hQg_eq : (1 / 2 : ℝ) • deriv (deriv fun t => (wordCombinationJTerm c).evalAlbert
      (fun k => pg k t)) 0 = g.linearEquiv Q := by
    rw [hrg_eq, deriv2_linearEquiv_comp g.linearEquiv (hr_diff.contDiffAt.of_le (by norm_num)),
      map_smul]
  have hQ_orth : ∀ w : Albert, W.Contains w → tracePairing w Q = 0 := by
    intro w ⟨M, hM⟩
    have hwg : standardComplexWindow.Contains (g.linearEquiv w) :=
      ⟨M, by rw [← hM, hg M]⟩
    have h0 := hQg_orth (g.linearEquiv w) hwg
    rw [hQg_eq, g.map_tracePairing] at h0
    exact h0
  have hbigO : (fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3) := by
    have ht := taylor_two_isBigO_cube hr_diff.contDiffAt
    refine ht.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
    dsimp only
    rw [hr0, hdr0, smul_zero, add_zero, zero_add]
    change r t - (t ^ 2 / 2) • deriv (deriv r) 0 = r t - t ^ 2 • ((1 / 2 : ℝ) • deriv (deriv r) 0)
    rw [smul_smul, div_eq_mul_one_div]
  have hbigO_l : ∀ l : Albert →ₗ[ℝ] ℝ,
      (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3) := fun l => by
    let L : Albert →L[ℝ] ℝ := l.toContinuousLinearMap
    have hcomp := (L.isBigO_comp (fun t => r t - t ^ 2 • Q) (𝓝 0)).trans hbigO
    simpa [L, Function.comp_def] using hcomp
  have hprob : ∀ ρ : Albert, W.Contains ρ →
      (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
        (fun t => t ^ 3) := by
    intro ρ hρ
    have hl := hbigO_l (tracePairingLM ρ)
    refine hl.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
    dsimp only
    rw [tracePairingLM_apply, tracePairing_sub_right, tracePairing_smul_right,
      hQ_orth ρ hρ, mul_zero, sub_zero, tracePairing_nativeWordCombinationEffect]
  exact ⟨hr_diff, hr0, hdr0, hQ_orth, hbigO, hbigO_l, hprob⟩

/-- **Headline (`cor:so:residual`)**: For any complex subalgebra window `W`, any projective
equality `c : Word (Fin n) →₀ ℝ` (`IsProjectiveEquality c`), and any `C³` idempotent test curves
`p_k : ℝ → Albert` based in `W` (`p_k(0) ∈ W`), the word combination effect
`r(t) = ∑_w c(w) E_w(p(t))` is `C³`, has vanishing constant and linear jets (`r(0) = 0`,
`r'(0) = 0`), has quadratic term `Q = (1/2) r''(0) ∈ W^⊥`, satisfies `r(t) - t² Q = O(t³)` as
`t → 0`, and induces `O(t³)` probability combinations on every `ρ ∈ W`. -/
theorem cor_so_residual {n : ℕ} (W : ComplexWindow)
    (c : Word (Fin n) →₀ ℝ) (hc : IsProjectiveEquality c)
    (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k, ContDiff ℝ 3 (p k))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, W.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 3 r ∧
      r 0 = 0 ∧
      deriv r 0 = 0 ∧
      (∀ w : Albert, W.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ ρ : Albert, W.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
          (fun t => t ^ 3)) :=
  cor_so_residual_from_specialVanishing W c
    ((isProjectiveEquality_iff_specialVanishing c).1 hc) p hp_diff hp_idem hp_base

/-- Atom-hypothesis version of `cor_so_residual` (`IsAtom (p k t)` implies idempotence). -/
theorem cor_so_residual_of_atoms {n : ℕ} (W : ComplexWindow)
    (c : Word (Fin n) →₀ ℝ) (hc : IsProjectiveEquality c)
    (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k, ContDiff ℝ 3 (p k))
    (hp_atom : ∀ k t, IsAtom (p k t))
    (hp_base : ∀ k, W.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 3 r ∧
      r 0 = 0 ∧
      deriv r 0 = 0 ∧
      (∀ w : Albert, W.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ ρ : Albert, W.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
          (fun t => t ^ 3)) :=
  cor_so_residual W c hc p hp_diff (fun k t => (hp_atom k t).1) hp_base

/-- `UniversalProjectionAlgebra` form of `cor:so:residual`. -/
theorem cor_so_residual_from_universalAlgebra {n : ℕ} (W : ComplexWindow)
    (c : Word (Fin n) →₀ ℝ)
    (hc : c.sum (fun w a => a • wordOperator (fun k => universalProjection (n := n) k) w) = 0)
    (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k, ContDiff ℝ 3 (p k))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, W.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 3 r ∧
      r 0 = 0 ∧
      deriv r 0 = 0 ∧
      (∀ w : Albert, W.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ ρ : Albert, W.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
          (fun t => t ^ 3)) :=
  cor_so_residual W c ((isProjectiveEquality_iff_universalAlgebraZero c).2 hc)
    p hp_diff hp_idem hp_base

/-- `AlgebraicProjectiveData` form of `cor:so:residual`. -/
theorem cor_so_residual_from_algebraicProjectiveData {n : ℕ} (W : ComplexWindow)
    (c : Word (Fin n) →₀ ℝ)
    (hc : ∀ (A : Type) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin n) A),
        c.sum (fun w a => a * M.probability w) = 0)
    (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k, ContDiff ℝ 3 (p k))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, W.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 3 r ∧
      r 0 = 0 ∧
      deriv r 0 = 0 ∧
      (∀ w : Albert, W.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ ρ : Albert, W.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
          (fun t => t ^ 3)) :=
  cor_so_residual W c ((isProjectiveEquality_iff_algebraicProjectiveData c).2 hc)
    p hp_diff hp_idem hp_base

/-- Standard-window `cor:so:residual`, additionally concluding `Q ∈ Wperp`. -/
theorem cor_so_residual_standardWindow {n : ℕ}
    (c : Word (Fin n) →₀ ℝ) (hc : IsProjectiveEquality c)
    (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k, ContDiff ℝ 3 (p k))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, standardComplexWindow.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    ContDiff ℝ 3 r ∧
      r 0 = 0 ∧
      deriv r 0 = 0 ∧
      Q ∈ Wperp ∧
      (∀ w : Albert, standardComplexWindow.Contains w → tracePairing w Q = 0) ∧
      ((fun t => r t - t ^ 2 • Q) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ ρ : Albert, standardComplexWindow.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
          (fun t => t ^ 3)) := by
  intro r Q
  have hc_spec := (isProjectiveEquality_iff_specialVanishing c).1 hc
  have hstd := standardWindow_residual_of_specialVanishing (wordCombinationJTerm c) hc_spec
    p hp_diff hp_idem hp_base
  have hr_pt : ∀ t, (wordCombinationJTerm c).evalAlbert (fun k => p k t) = r t :=
    fun t => evalAlbert_wordCombinationJTerm c (fun k => p k t)
  dsimp only at hstd
  simp only [hr_pt] at hstd
  rcases hstd with ⟨hr_diff, hr0, hdr0, hQ_perp, hQ_orth, hbigO, hbigO_l⟩
  have hprob : ∀ ρ : Albert, standardComplexWindow.Contains ρ →
      (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
        (fun t => t ^ 3) := by
    intro ρ hρ
    have hl := hbigO_l (tracePairingLM ρ)
    refine hl.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun _ => rfl)
    dsimp only
    rw [tracePairingLM_apply, tracePairing_sub_right, tracePairing_smul_right,
      hQ_orth ρ hρ, mul_zero, sub_zero, tracePairing_nativeWordCombinationEffect]
  exact ⟨hr_diff, hr0, hdr0, hQ_perp, hQ_orth, hbigO, hbigO_l, hprob⟩

/-- Completely norm-free linear-functional formulation of `cor:so:residual` whose type signature
uses no scoped `NormedAddCommGroup` / `NormedSpace` instance on `Albert`. -/
theorem cor_so_residual_linearFunctional {n : ℕ} (W : ComplexWindow)
    (c : Word (Fin n) →₀ ℝ) (hc : IsProjectiveEquality c)
    (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k (l : Albert →ₗ[ℝ] ℝ), ContDiff ℝ 3 (fun t => l (p k t)))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, W.Contains (p k 0)) :
    let r : ℝ → Albert := fun t => nativeWordCombinationEffect c (fun k => p k t)
    let Q : Albert := (1 / 2 : ℝ) • deriv (deriv r) 0
    (∀ l : Albert →ₗ[ℝ] ℝ, ContDiff ℝ 3 (fun t => l (r t))) ∧
      r 0 = 0 ∧
      deriv r 0 = 0 ∧
      (∀ w : Albert, W.Contains w → tracePairing w Q = 0) ∧
      (∀ l : Albert →ₗ[ℝ] ℝ, (fun t => l (r t - t ^ 2 • Q)) =O[𝓝 0] (fun t => t ^ 3)) ∧
      (∀ ρ : Albert, W.Contains ρ →
        (fun t => c.sum (fun w a => a * nativeWordProbability (fun k => p k t) ρ w)) =O[𝓝 0]
          (fun t => t ^ 3)) := by
  intro r Q
  have hp' : ∀ k, ContDiff ℝ 3 (p k) := fun k => contDiff_of_forall_linearMap (hp_diff k)
  obtain ⟨hr_diff, hr0, hdr0, hQ_orth, _, hbigO_l, hprob⟩ :=
    cor_so_residual W c hc p hp' hp_idem hp_base
  have hr_l : ∀ l : Albert →ₗ[ℝ] ℝ, ContDiff ℝ 3 (fun t => l (r t)) := fun l =>
    (l.toContinuousLinearMap).contDiff.comp hr_diff
  exact ⟨hr_l, hr0, hdr0, hQ_orth, hbigO_l, hprob⟩

end

end AlbertSequential.AppF

-- Verify the norm-free theorem compiles with no scoped `NormedAddCommGroup Albert` in scope.
section NormFreeSignatureCheck
open AlbertSequential

example {n : ℕ} (W : ComplexWindow) (c : Word (Fin n) →₀ ℝ)
    (hc : AppF.IsProjectiveEquality c) (p : Fin n → ℝ → Albert)
    (hp_diff : ∀ k (l : Albert →ₗ[ℝ] ℝ), ContDiff ℝ 3 (fun t => l (p k t)))
    (hp_idem : ∀ k t, jordanMul (p k t) (p k t) = p k t)
    (hp_base : ∀ k, W.Contains (p k 0)) :=
  AppF.cor_so_residual_linearFunctional W c hc p hp_diff hp_idem hp_base

end NormFreeSignatureCheck
