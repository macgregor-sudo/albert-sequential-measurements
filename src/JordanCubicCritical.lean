/- SPDX-License-Identifier: Apache-2.0 -/
module

public import UnitalJordanProduct
public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-! Cubic maximum for a real commutative algebra with a positive associative
inner product. Finite dimension supplies continuity of the bilinear product.
No spectral decomposition or primitive-corner assertion is assumed. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (P : UnitalJordanProduct E)

/-- Algebraic bilinearity automatically becomes continuous in finite dimension. -/
def continuousProduct : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).toLinearMap.comp
      P.product)

@[simp] theorem continuousProduct_apply (x y : E) :
    P.continuousProduct x y=P.product x y := rfl

def cubic (x : E) : ℝ := inner ℝ (P.product x x) x

/-- Associativity identifies each differentiated cubic term with <x²,y>. -/
theorem cubic_pairing (hassoc : ∀ x y z, inner ℝ (P.product x y) z=
    inner ℝ x (P.product y z)) (x y : E) :
    inner ℝ (P.product x y) x=inner ℝ (P.product x x) y := by
  rw [P.commutative x y, hassoc y x x, real_inner_comm]

theorem hasStrictFDerivAt_cubic
    (hassoc : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z))
    (x : E) : HasStrictFDerivAt P.cubic
      ((3 : ℝ) • innerSL ℝ (P.product x x)) x := by
  have hprod := P.continuousProduct.hasStrictFDerivAt_of_bilinear
    (hasStrictFDerivAt_id x) (hasStrictFDerivAt_id x)
  have h := hprod.inner ℝ (hasStrictFDerivAt_id x)
  convert h using 1
  · rfl
  · ext y
    change (3 : ℝ) * inner ℝ (P.product x x) y =
      inner ℝ (P.product x x) y + inner ℝ (P.product x y+P.product y x) x
    rw [inner_add_left, P.cubic_pairing hassoc x y,
      P.commutative y x, P.cubic_pairing hassoc x y]
    ring

/-- Compact-sphere stationarity on an arbitrary nontrivial subspace W.
The derivative is an ambient inner product restricted to W, so no assumption
that x² belongs to W is introduced. -/
theorem exists_cubic_critical (W : Submodule ℝ E) [Nontrivial W]
    (hassoc : ∀ x y z, inner ℝ (P.product x y) z=inner ℝ x (P.product y z)) :
    ∃ x : W, ‖x‖=1 ∧ ∃ a : ℝ,
      ∀ y : W, inner ℝ (P.product x.val x.val) y.val=a * inner ℝ x.val y.val := by
  let F : W → ℝ := fun x => P.cubic x.val
  have hF (x : W) : HasStrictFDerivAt F
      (((3 : ℝ) • innerSL ℝ (P.product x.val x.val)).comp W.subtypeL) x :=
    (P.hasStrictFDerivAt_cubic hassoc x.val).comp x W.subtypeL.hasStrictFDerivAt
  have hcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun x => (hF x).hasFDerivAt.continuousAt)
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : W) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ)≤1)) hcont.continuousOn
  have hnorm : ‖x‖=1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  let F' : StrongDual ℝ W :=
    ((3 : ℝ) • innerSL ℝ (P.product x.val x.val)).comp W.subtypeL
  let G' : StrongDual ℝ W := (2 : ℝ) • innerSL ℝ x
  have hset : {y : W | ‖y‖^2=‖x‖^2}=Metric.sphere 0 1 := by
    ext y
    simp only [Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right, hnorm]
    constructor
    · intro hy
      nlinarith [norm_nonneg y]
    · intro hy
      rw [hy]
  have hext : IsLocalExtrOn F {y : W | ‖y‖^2=‖x‖^2} x := by
    rw [hset]
    exact Or.inr hmax.isLocalMaxOn
  obtain ⟨a, b, hab, hmul⟩ :=
    hext.exists_multipliers_of_hasStrictFDerivAt_1d
      (hasStrictFDerivAt_norm_sq x) (hF x)
  have hb : b≠0 := by
    intro hb0
    have hxmul := DFunLike.congr_fun hmul x
    simp only [add_apply, smul_apply,
      zero_apply, hb0, zero_smul, add_zero, innerSL_apply_apply, smul_eq_mul] at hxmul
    have hxx : inner ℝ x x=1 := by rw [real_inner_self_eq_norm_sq, hnorm]; norm_num
    rw [hxx] at hxmul
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hxmul
    have ha0 : a=0 := by nlinarith
    exact hab (by simp only [ha0, hb0, Prod.mk_eq_zero, and_self])
  refine ⟨x, hnorm, -(2*a)/(3*b), ?_⟩
  intro y
  have hy := DFunLike.congr_fun hmul y
  simp only [add_apply, smul_apply,
    zero_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Submodule.coe_inner, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hy
  change a * (2 * inner ℝ x.val y.val)+
    b * (3 * inner ℝ (P.product x.val x.val) y.val)=0 at hy
  field_simp [hb]
  nlinarith

end AlbertSequential.UnitalJordanProduct
