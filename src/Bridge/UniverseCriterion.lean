/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Bridge.PrintedCriterion
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

@[expose] public section
noncomputable section
namespace AlbertChallenge.Bridge
open AlbertChallenge
universe v
private abbrev EH (d : ℕ) := EuclideanSpace ℂ (Fin d)
private abbrev LH (d : ℕ) := EuclideanSpace ℂ (ULift.{v} (Fin d))

/-- Reindex a finite complex projective representation without changing any word probability. -/
theorem exists_liftFiniteProjectiveRepresentation {n d : ℕ}
    (M : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))) :
    ∃ N : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (ULift.{v} (Fin d))),
      ∀ w, N.probability w = M.probability w := by
  let e : EH d ≃ₗᵢ[ℂ] LH.{v} d := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ Equiv.ulift.symm
  let g := e.conjStarAlgEquiv
  let N : ProjectiveRepresentation n ℂ (LH.{v} d) := {
    projection := fun i => g (M.projection i)
    isStarProjection := fun i => by
      obtain ⟨hi,hs⟩ := (isStarProjection_iff' (p := M.projection i)).mp (M.isStarProjection i)
      exact isStarProjection_iff'.mpr ⟨(map_mul g _ _).symm.trans (congrArg g hi),
        (map_star g _).symm.trans (congrArg g hs)⟩
    state := M.state.comp g.symm.toAlgEquiv.toLinearMap
    state_one := by change M.state (g.symm 1) = 1; rw [map_one,M.state_one]
    state_nonneg := fun T hT => M.state_nonneg _ ((LinearMap.isPositive_linearIsometryEquiv_conj_iff e.symm).mpr hT.toLinearMap) }
  refine ⟨N, ?_⟩
  intro w
  unfold ProjectiveRepresentation.probability
  change Complex.re (M.state (g.symm (wordOperator (fun i => g (M.projection i)) w))) = _
  rw [← wordOperator_map g,g.symm_apply_apply]
  rfl

/-- Reindex the finite density witness into the universe of any proposed model. -/
theorem hasClassIModel_of_finite {n d : ℕ} (p : Fin n → Albert) (ρ : Albert)
    (M : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)))
    (hm : ∀ w, M.probability w = wordProbability p ρ w) : HasClassIModel.{v} p ρ := by
  obtain ⟨N, hN⟩ := exists_liftFiniteProjectiveRepresentation.{v} M
  exact HasClassIModel.complex N (fun w => (hN w).trans (hm w))

theorem proper_iff_hasClassIModel {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    AlbertSequential.generatedSubalgebra (Set.range (fun i => toT (p i))) ≠ ⊤ ↔
      ∃ ρ, IsDensity ρ ∧ HasClassIModel.{v} p ρ := by
  constructor
  · intro h
    obtain ⟨ρ,hρ⟩ := exists_isDensity
    obtain ⟨d,M,_,hm⟩ := (printed_albert_criterion p hp).2.1.mp h ρ hρ
    exact ⟨ρ,hρ,hasClassIModel_of_finite p ρ M hm⟩
  · rintro ⟨ρ,_,hM⟩ he
    exact no_classI_of_generates p hp ((generates_toT p).mp
      ((AlbertSequential.generatesAlbert_iff_generatedSubalgebra_eq_top _).mpr he)) ρ hM

end AlbertChallenge.Bridge

namespace AlbertSequential
open AlbertChallenge.Bridge MatchingModels
universe v

theorem nativeOperatorSpecial_iff_proper (B : NativeJordanSubalgebra) :
    NativeOperatorSpecial.{v} B ↔ B ≠ ⊤ := by
  refine ⟨fun h => h.proper,fun h => ?_⟩
  obtain ⟨d,_,⟨b⟩⟩ := (proper_iff_special B).mp h
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.ulift.symm : Fin d ≃ ULift.{v} (Fin d))
  let g := e.conjStarAlgEquiv
  let F : B.carrier →ₗ[ℝ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) := {
    toFun := fun x => matToCLM (b.map x)
    map_add' := fun x y => by rw [map_add,matToCLM_add]
    map_smul' := fun r x => by rw [map_smul,matToCLM_real_smul]; rfl }
  let G := g.toAlgEquiv.toLinearMap.restrictScalars ℝ
  apply NativeOperatorSpecial.witness (G.comp F)
  · intro x y he
    change g (matToCLM (b.map x)) = g (matToCLM (b.map y)) at he
    apply b.injective
    simpa only [clmMatrix_matToCLM] using congrArg clmMatrix (g.injective he)
  · intro x
    change star (g (matToCLM (b.map x))) = _
    rw [← map_star, (matToCLM_isSelfAdjoint (b.hermitian x)).star_eq]
    rfl
  · intro x y
    have hf : F ⟨jordanMul x.val y.val,B.product_mem _ x.property _ y.property⟩ =
        (1/2 : ℝ) • (F x * F y + F y * F x) := by
      change matToCLM (b.map _) = _
      rw [b.jordan,matToCLM_real_smul,matToCLM_add,matToCLM_mul,matToCLM_mul]
      rfl
    change G (F _) = _
    rw [hf,G.map_smul,G.map_add]
    change (1/2 : ℝ) • (g (_ * _) + g (_ * _)) = _
    rw [map_mul,map_mul]
    rfl

end AlbertSequential
