/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJAWordTransport

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))

/-- The canonical densities are a compact sphere image under the actual Jordan square. -/
theorem isCompact_canonicalDensity (hfr : P.FormallyReal) :
    IsCompact {ρ | P.IsCanonicalDensity hfr ρ} := by
  let B := P.canonicalTraceFormOfFormallyReal hfr
  let V := PositiveFormModel.Model E
  let C : InnerProductSpace.Core ℝ V := PositiveFormModel.innerCore E B
    (P.canonicalTraceFormOfFormallyReal_symmetric hfr) (P.canonicalTraceFormOfFormallyReal_positive hfr)
  let : InnerProductSpace.Core ℝ V := C
  let : NormedAddCommGroup V := C.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let e : V ≃ₗ[ℝ] E := PositiveFormModel.linearEquiv E
  let φ (x : V) := P.product (e x) (e x)
  have hφ : Continuous φ :=
    P.product_square_continuous.comp e.toLinearMap.toContinuousLinearMap.continuous
  have hnorm (x : V) : P.canonicalTraceOfFormallyReal hfr (φ x) = ‖x‖ ^ 2 := by
    change inner ℝ x x = ‖x‖ ^ 2
    exact real_inner_self_eq_norm_sq x
  have heq : {ρ | P.IsCanonicalDensity hfr ρ} = φ '' Metric.sphere (0 : V) 1 := by
    ext ρ
    constructor
    · rintro ⟨⟨a,ha⟩,ht⟩
      refine ⟨e.symm a,?_ ,?_⟩
      · rw [Metric.mem_sphere,dist_zero_right]
        have hh := hnorm (e.symm a)
        change P.canonicalTraceOfFormallyReal hfr (P.product (e (e.symm a)) (e (e.symm a))) = _ at hh
        rw [e.apply_symm_apply,← ha,ht] at hh
        nlinarith [norm_nonneg (e.symm a)]
      · change P.product (e (e.symm a)) (e (e.symm a)) = ρ
        rw [e.apply_symm_apply,← ha]
    · rintro ⟨x,hx,rfl⟩
      have h : ‖x‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
      exact ⟨⟨e x,rfl⟩,by simp only [hnorm,h,one_pow]⟩
  rw [heq]
  exact (isCompact_sphere (0 : V) 1).image hφ

include hinner in
theorem convex_canonicalDensity (hfr : P.FormallyReal) :
    Convex ℝ {ρ | P.IsCanonicalDensity hfr ρ} := by
  intro ρ hρ σ hσ a b ha hb hab
  refine ⟨P.squareCone_convex hinner hρ.1 hσ.1 ha hb hab,?_⟩
  rw [map_add,map_smul,map_smul,hρ.2,hσ.2,smul_eq_mul,smul_eq_mul,mul_one,mul_one]
  exact hab

end AlbertSequential.UnitalJordanProduct
