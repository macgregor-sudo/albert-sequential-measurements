/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.HigherJetCoefficientIdeal
public import AppF.HermitianCoefficientKernel
import Mathlib.Tactic.Abel

/-! The literal real and quaternionic Hermitian thickenings and their universal kernels. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.AppF
open HigherJetCoefficients

theorem HigherJetBase.project_conj (b : HigherJetBase) (u : Octonion) :
    b.project (octonionConj u) = octonionConj (b.project u) := by
  cases b
  · change octonionScalar (octonionReal (octonionConj u)) = octonionConj (octonionScalar (octonionReal u))
    rw [octonionConj_scalar, octonionReal_conj]
  · change ((star u.1, 0) : Octonion) = (star u.1, -0)
    rw [neg_zero]

def HigherJetCoefficients.conjugate (b : HigherJetBase) (m : Fin 4) :
    HigherJetCoefficients b m →ₗ[ℝ] HigherJetCoefficients b m where
  toFun x := ⟨fun i => octonionConj (x.val i),
    ⟨by rw [b.project_conj, base x], fun i hi => by
      change octonionConj (x.val i) = 0
      rw [support x i hi, octonionConj_zero]⟩⟩
  map_add' x y := Subtype.ext (funext fun i => octonionConj_add (x.val i) (y.val i))
  map_smul' r x := Subtype.ext (funext fun i => octonionConj_smul r (x.val i))

theorem HigherJetCoefficients.conjugate_involutive (b : HigherJetBase) (m : Fin 4) :
    Function.Involutive (conjugate b m) :=
  fun x => Subtype.ext (funext fun i => octonionConj_conj (x.val i))

theorem HigherJetCoefficients.conjugate_unit (b : HigherJetBase) (m : Fin 4) :
    conjugate b m (unit b m) = unit b m := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [conjugate, unit, octonionConj_scalar, octonionConj_zero]

theorem HigherJetCoefficients.conjugate_product (b : HigherJetBase) (m : Fin 4)
    (x y : HigherJetCoefficients b m) :
    conjugate b m (product x y) = product (conjugate b m y) (conjugate b m x) := by
  apply Subtype.ext
  funext i
  by_cases hi : i ≤ m
  · fin_cases i <;>
      simp_all [conjugate, product, octonionJetProduct, octonionConj_add, octonionConj_mul] <;> abel
  · simp [conjugate, product, hi, octonionConj_zero]

theorem HigherJetBase.leadingSpace_conj (b : HigherJetBase) (u : Octonion)
    (hu : u ∈ b.leadingSpace) : octonionConj u ∈ b.leadingSpace := by
  cases b
  · change octonionReal u = 0 at hu
    change octonionReal (octonionConj u) = 0
    rwa [octonionReal_conj]
  · change u.1 = 0 at hu
    change star u.1 = 0
    simp [hu]

theorem HigherJetBase.leadingSpace_real_zero (b : HigherJetBase) (u : Octonion)
    (hu : u ∈ b.leadingSpace) : octonionReal u = 0 := by
  cases b
  · exact hu
  · change u.1 = 0 at hu
    change u.1.re = 0
    simp [hu]

theorem HigherJetCoefficients.leadingIdeal_conj (b : HigherJetBase)
    (x : HigherJetCoefficients b b.threshold) (hx : x ∈ leadingIdeal b) :
    conjugate b b.threshold x ∈ leadingIdeal b := by
  obtain ⟨hzero, htop⟩ := (mem_leadingIdeal b x).mp hx
  apply (mem_leadingIdeal b _).mpr
  constructor
  · intro i hi
    change octonionConj (x.val i) = 0
    rw [hzero i hi, octonionConj_zero]
  · exact b.leadingSpace_conj _ htop

theorem HigherJetCoefficients.leadingIdeal_fixed_eq_zero (b : HigherJetBase)
    (x : HigherJetCoefficients b b.threshold) (hx : x ∈ leadingIdeal b)
    (hfix : conjugate b b.threshold x = x) : x = 0 := by
  obtain ⟨hzero, htop⟩ := (mem_leadingIdeal b x).mp hx
  apply Subtype.ext
  funext i
  change x.val i = 0
  by_cases hi : i = b.threshold
  · subst i
    have h := congrArg (fun y : HigherJetCoefficients b b.threshold => y.val b.threshold) hfix
    change octonionConj (x.val b.threshold) = x.val b.threshold at h
    rw [octonionConj_eq_neg_of_real_zero (b.leadingSpace_real_zero _ htop)] at h
    have hz : (2 : ℝ) • x.val b.threshold = 0 := by
      rw [two_smul]
      nth_rw 2 [← h]
      exact add_neg_cancel _
    have hv := congrArg (fun z : Octonion => (2 : ℝ)⁻¹ • z) hz
    change (2 : ℝ)⁻¹ • ((2 : ℝ) • x.val b.threshold) = (2 : ℝ)⁻¹ • (0 : Octonion) at hv
    rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul, smul_zero] at hv
  · exact hzero i hi

/-- The literal Hermitian matrices over the specified truncated coefficient algebra. -/
abbrev HigherJetHermitian (b : HigherJetBase) (m : Fin 4) :=
  coefficientHermitian (conjugate b m)

def HigherJetHermitian.product (b : HigherJetBase) (m : Fin 4) :
    HigherJetHermitian b m → HigherJetHermitian b m → HigherJetHermitian b m :=
  coefficientHermitianProduct (conjugate b m) bilinear (conjugate_product b m)

theorem higherJetHermitian_special_below (b : HigherJetBase) (m : Fin 4) (hm : m < b.threshold) :
    ∃ f : HigherJetHermitian b m →ₗ[ℝ]
        CoefficientMatrix (Module.End ℝ (HigherJetCoefficients b m ⧸
          (⊥ : Submodule ℝ (HigherJetCoefficients b m)))),
      Function.Injective f ∧ IsCoefficientJordanMap (conjugate b m) bilinear (conjugate_product b m) f := by
  obtain ⟨f, hfinj, _, hf⟩ := exists_injective_specialCoefficientMap_below b m hm
  exact ⟨coefficientEntrywiseMap (conjugate b m) f, coefficientEntrywiseMap_injective _ f hfinj,
    coefficientEntrywiseMap_jordan _ _ _ f hf⟩

set_option maxHeartbeats 1200000 in
/-- Every associative-target Jordan map kills exactly the stated common kernel. -/
theorem higherJetHermitian_universal_kernel (b : HigherJetBase)
    (M : HigherJetHermitian b b.threshold) :
    (∀ i j, M.val i j ∈ leadingIdeal b) ↔
      ∀ (A : Type) [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
        (f : HigherJetHermitian b b.threshold →ₗ[ℝ] A),
          IsCoefficientJordanMap (conjugate b b.threshold) bilinear (conjugate_product b b.threshold) f →
          f M = 0 := by
  constructor
  · intro hM A _ _ _ _ f hf
    let C := HigherJetCoefficients b b.threshold
    let μ : C →ₗ[ℝ] C →ₗ[ℝ] C := bilinear
    have hspan : Submodule.span ℝ (Set.range (fun t : C × C × C =>
        μ (μ t.1 t.2.1) t.2.2 - μ t.1 (μ t.2.1 t.2.2))) = leadingIdeal b :=
      span_associators_eq_leadingIdeal b
    exact coefficientJordanMap_kills_associatorIdeal (C := C) (A := A)
      (conjugate b b.threshold) μ (conjugate_product b b.threshold) (unit b b.threshold)
      (conjugate_unit b b.threshold) (conjugate_involutive b b.threshold)
      (fun x => product_unit_left x) (fun x => product_unit_right x)
      (leadingIdeal b) hspan (leadingIdeal_conj b) (leadingIdeal_fixed_eq_zero b) f hf M hM
  · intro hall
    obtain ⟨f, hker, _, hf⟩ := exists_specialCoefficientMap_at_threshold b
    have hz := hall _ (coefficientEntrywiseMap (conjugate b b.threshold) f)
      (coefficientEntrywiseMap_jordan _ _ _ f hf)
    have hentries := (coefficientEntrywiseMap_eq_zero _ f M).mp hz
    simpa only [hker] using hentries

end AlbertSequential.AppF
