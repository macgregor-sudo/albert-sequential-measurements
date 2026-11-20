/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Bridge.Criterion

@[expose] public section
noncomputable section
namespace AlbertSequential

universe v

/-- Operator speciality on the given native Jordan subalgebra. -/
inductive NativeOperatorSpecial (B : NativeJordanSubalgebra) : Prop where
  | witness {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (f : B.carrier →ₗ[ℝ] (H →L[ℂ] H)) (inj : Function.Injective f)
      (herm : ∀ x, IsSelfAdjoint (f x))
      (product : ∀ x y, f ⟨jordanMul x.val y.val, B.product_mem _ x.property _ y.property⟩ =
        (1/2 : ℝ) • (f x * f y + f y * f x))

theorem NativeOperatorSpecial.proper {B : NativeJordanSubalgebra} (h : NativeOperatorSpecial.{v} B) : B ≠ ⊤ := by
  rintro rfl
  obtain ⟨f,hinj,_,hprod⟩ := h
  let η := f.comp (Submodule.topEquiv (R := ℝ) (M := Albert)).symm.toLinearMap
  have hj : IsJordanHom η := fun x y => hprod ⟨x,trivial⟩ ⟨y,trivial⟩
  have hzero := albertJordanHom_eq_zero _ η hj
  have he : η albertUnit = η 0 := by rw [hzero]; rfl
  have hu : albertUnit = 0 := (Submodule.topEquiv (R := ℝ) (M := Albert)).symm.injective (hinj he)
  have ht := congrArg albertTrace hu
  rw [NativeAnalysis.albertTrace_zero] at ht
  norm_num [albertUnit,albertTrace] at ht

open MatchingModels in
theorem nativeOperatorSpecial_of_proper (B : NativeJordanSubalgebra) (h : B ≠ ⊤) :
    NativeOperatorSpecial.{0} B := by
  obtain ⟨d,_,⟨e⟩⟩ := (proper_iff_special B).mp h
  let g : B.carrier →ₗ[ℝ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
    { toFun := fun x => matToCLM (e.map x)
      map_add' := fun x y => by rw [map_add, matToCLM_add]
      map_smul' := fun r x => by rw [map_smul,matToCLM_real_smul]; rfl }
  apply NativeOperatorSpecial.witness g
  · intro x y he
    apply e.injective
    change matToCLM (e.map x) = matToCLM (e.map y) at he
    simpa only [AlbertChallenge.Bridge.clmMatrix_matToCLM] using congrArg AlbertChallenge.Bridge.clmMatrix he
  · exact fun x => matToCLM_isSelfAdjoint (e.hermitian x)
  · intro x y
    change matToCLM (e.map _) = _
    rw [e.jordan, matToCLM_real_smul, matToCLM_add,matToCLM_mul,matToCLM_mul]
    rfl

end AlbertSequential

namespace AlbertChallenge.Bridge
open AlbertChallenge
universe v

/-- A physical model over one of the three stated scalar fields. -/
inductive HasClassIModel {n : ℕ} (p : Fin n → Albert) (ρ : Albert) : Prop where
  | real {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (M : ProjectiveRepresentation n ℝ H) (hw : ∀ w, M.probability w = wordProbability p ρ w)
  | complex {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (M : ProjectiveRepresentation n ℂ H) (hw : ∀ w, M.probability w = wordProbability p ρ w)
  | quaternionic {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation n S)
      (hw : ∀ w, M.probability w = wordProbability p ρ w)

theorem no_classI_of_generates {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) (ρ : Albert) : ¬ HasClassIModel.{v} p ρ := by
  have hn := no_representation_bridge.{v} p hp hg ρ
  rintro (⟨M,h⟩ | ⟨M,h⟩ | ⟨S,M,h⟩)
  · exact hn.1 ℝ _ M (fun w _ => h w)
  · exact hn.1 ℂ _ M (fun w _ => h w)
  · exact hn.2.1 _ S M (fun w _ => h w)

/-- Core Theorem 4.1, with the actual generated subalgebra and separate
finite complex density models for each input state. -/
theorem printed_albert_criterion {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    let B := AlbertSequential.generatedSubalgebra (Set.range (fun i => toT (p i)))
    (B ≠ ⊤ ↔ AlbertSequential.NativeOperatorSpecial.{0} B) ∧
    (B ≠ ⊤ ↔ ∀ ρ, IsDensity ρ → ∃ (d : ℕ) (M : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))),
      M.HasDensityState ∧ ∀ w, M.probability w = wordProbability p ρ w) ∧
    (B ≠ ⊤ ↔ ∃ ρ, IsDensity ρ ∧ HasClassIModel.{0} p ρ) := by
  intro B
  have he : B = ⊤ ↔ Generates p :=
    (AlbertSequential.generatesAlbert_iff_generatedSubalgebra_eq_top _).symm.trans (generates_toT p)
  have hc := (albert_criterion_bridge p hp).2.1
  have finiteFromProper := fun h : B ≠ ⊤ => hc.mp (fun hg => h (he.mpr hg))
  refine ⟨⟨AlbertSequential.nativeOperatorSpecial_of_proper B,fun h => h.proper⟩, ⟨?_,?_⟩, ⟨?_,?_⟩⟩
  · intro h ρ hρ
    obtain ⟨d,_,_,hf⟩ := finiteFromProper h
    obtain ⟨M,_,hd,hw⟩ := hf ρ hρ
    exact ⟨d,M,hd,hw⟩
  · intro hf heq
    obtain ⟨ρ,hρ⟩ := exists_isDensity
    obtain ⟨_,M,_,hw⟩ := hf ρ hρ
    exact no_classI_of_generates p hp (he.mp heq) ρ (.complex M hw)
  · intro h
    obtain ⟨d,_,_,hf⟩ := finiteFromProper h
    obtain ⟨ρ,hρ⟩ := exists_isDensity
    obtain ⟨M,_,_,hw⟩ := hf ρ hρ
    exact ⟨ρ,hρ,.complex M hw⟩
  · rintro ⟨ρ,_,hm⟩ heq
    exact no_classI_of_generates p hp (he.mp heq) ρ hm

end AlbertChallenge.Bridge
