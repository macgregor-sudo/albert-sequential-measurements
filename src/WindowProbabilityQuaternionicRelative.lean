/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityQuaternionicLaw
public import WindowProbabilityAlbertWindowLaw
public import QuaternionicHellySix

/-! Transport from any native quaternionic ambient and complex window to the standard carrier. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory
open scoped AlbertSequential.WindowProbability Matrix

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : FiniteDimensional ℝ Albert :=
  NativeAnalysis.recoveredCoordinateEquiv.symm.finiteDimensional

/-- The supplied Hermitian parametrizations induce a native unital Jordan isomorphism. -/
def complexWindowIso (W W' : ComplexWindow) : JordanSubalgebraIso W.toSubalgebra W'.toSubalgebra := by
  let E : Hermitian3 ≃ₗ[ℝ] W.toSubalgebra.carrier := LinearEquiv.ofInjective W.embedding W.injective
  let E' : Hermitian3 ≃ₗ[ℝ] W'.toSubalgebra.carrier := LinearEquiv.ofInjective W'.embedding W'.injective
  refine ⟨E.symm.trans E', ?_, ?_⟩
  · have h1 : E 1 = ⟨albertUnit, W.toSubalgebra.unit_mem⟩ := Subtype.ext W.unit
    change E' (E.symm ⟨albertUnit, W.toSubalgebra.unit_mem⟩) = _
    rw [← h1, LinearEquiv.symm_apply_apply]
    exact Subtype.ext W'.unit
  · intro p q
    let A := E.symm p
    let B := E.symm q
    obtain ⟨C, hC⟩ := W.product_closed A B
    have hp : W.embedding A = p.val := congrArg Subtype.val (E.apply_symm_apply p)
    have hq : W.embedding B = q.val := congrArg Subtype.val (E.apply_symm_apply q)
    have hP : E C = ⟨jordanMul p.val q.val, W.toSubalgebra.product_mem _ p.property _ q.property⟩ := by
      apply Subtype.ext
      change W.embedding C = jordanMul p.val q.val
      rw [W.preserves_product A B C hC, hp, hq]
    change E' (E.symm ⟨jordanMul p.val q.val, _⟩) = _
    rw [← hP, LinearEquiv.symm_apply_apply]
    exact Subtype.ext (W'.preserves_product A B C hC)

/-- The trace pairing is preserved by a trace-preserving native Jordan isomorphism. -/
theorem tracePairing_jordanSubalgebraIso {V V' : NativeJordanSubalgebra}
    (g : JordanSubalgebraIso V V')
    (hg : ∀ p : V.carrier, albertTrace (g.toLinearEquiv p).val = albertTrace p.val)
    (p q : V.carrier) :
    tracePairing (g.toLinearEquiv p).val (g.toLinearEquiv q).val = tracePairing p.val q.val := by
  let z : V.carrier := ⟨jordanMul p.val q.val, V.product_mem _ p.property _ q.property⟩
  have hz := hg z
  rw [g.map_jordan p q] at hz
  exact hz

/-- Transport the actual Hermitian coordinates through a trace-preserving
unital Jordan isomorphism of native ambient subalgebras. -/
def transportComplexWindowInto {V V' : NativeJordanSubalgebra}
    (g : JordanSubalgebraIso V V')
    (hg : ∀ p : V.carrier, albertTrace (g.toLinearEquiv p).val = albertTrace p.val)
    (W : ComplexWindow) (hW : W.toSubalgebra.carrier ≤ V.carrier) : ComplexWindow := by
  let F := W.embedding.codRestrict V.carrier (fun M => hW ⟨M, rfl⟩)
  let E := V'.carrier.subtype.comp (g.toLinearEquiv.toLinearMap.comp F)
  refine ⟨E, ?_, ?_, W.product_closed, ?_, ?_⟩
  · intro A B h
    apply W.injective
    exact congrArg Subtype.val (g.toLinearEquiv.injective (Subtype.ext h))
  · have h1 : F 1 = ⟨albertUnit, V.unit_mem⟩ := Subtype.ext W.unit
    change (g.toLinearEquiv (F 1)).val = albertUnit
    rw [h1, g.map_unit]
  · intro A B C hC
    have hF : F C = ⟨jordanMul (F A).val (F B).val,
        V.product_mem _ (F A).property _ (F B).property⟩ := Subtype.ext (W.preserves_product A B C hC)
    change (g.toLinearEquiv (F C)).val = jordanMul (g.toLinearEquiv (F A)).val (g.toLinearEquiv (F B)).val
    rw [hF, g.map_jordan]
  · intro M
    change albertTrace (g.toLinearEquiv (F M)).val = (M : ComplexMatrix3).trace.re
    rw [hg]
    exact W.preserves_trace M

theorem transportComplexWindowInto_embedding {V V' : NativeJordanSubalgebra}
    (g : JordanSubalgebraIso V V')
    (hg : ∀ p : V.carrier, albertTrace (g.toLinearEquiv p).val = albertTrace p.val)
    (W : ComplexWindow) (hW : W.toSubalgebra.carrier ≤ V.carrier) (M : Hermitian3) :
    (transportComplexWindowInto g hg W hW).embedding M =
      (g.toLinearEquiv ⟨W.embedding M, hW ⟨M, rfl⟩⟩).val := rfl

theorem transportComplexWindowInto_le {V V' : NativeJordanSubalgebra}
    (g : JordanSubalgebraIso V V')
    (hg : ∀ p : V.carrier, albertTrace (g.toLinearEquiv p).val = albertTrace p.val)
    (W : ComplexWindow) (hW : W.toSubalgebra.carrier ≤ V.carrier) :
    (transportComplexWindowInto g hg W hW).toSubalgebra.carrier ≤ V'.carrier := by
  rintro _ ⟨M, rfl⟩
  exact (g.toLinearEquiv ⟨W.embedding M, hW ⟨M, rfl⟩⟩).property

theorem projectedMatrix_transportComplexWindowInto {V V' : NativeJordanSubalgebra}
    (g : JordanSubalgebraIso V V')
    (hg : ∀ p : V.carrier, albertTrace (g.toLinearEquiv p).val = albertTrace p.val)
    (W : ComplexWindow) (hW : W.toSubalgebra.carrier ≤ V.carrier) (p : V.carrier) :
    projectedMatrix (transportComplexWindowInto g hg W hW) (g.toLinearEquiv p).val =
      projectedMatrix W p.val := by
  unfold projectedMatrix windowProj
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [transportComplexWindowInto_embedding, tracePairing_jordanSubalgebraIso g hg]

/-- The actual native quaternionic ray obtained before trace normalization. -/
def quaternionicTwoColumnRayLaw : Measure Albert :=
  (standardComplexGaussianMatrix 2).map quaternionicDyadFromTwoColumns

instance : IsProbabilityMeasure quaternionicTwoColumnRayLaw := by
  unfold quaternionicTwoColumnRayLaw
  infer_instance

theorem projectedMatrix_quaternionicTwoColumnRayLaw :
    quaternionicTwoColumnRayLaw.map (projectedMatrix standardComplexWindow) =
      (standardComplexGaussianMatrix 2).map (fun Z : Matrix (Fin 3) (Fin 2) ℂ => Z * Z.conjTranspose) := by
  unfold quaternionicTwoColumnRayLaw
  rw [Measure.map_map (measurable_projectedMatrix _) measurable_quaternionicDyadFromTwoColumns]
  congr 1
  funext Z
  exact projectedMatrix_quaternionicDyadFromTwoColumns Z

theorem projectedMatrix_quaternionicTwoColumnSampleLaw_same_carrier (W : ComplexWindow)
    (hW : W.toSubalgebra.carrier = standardComplexWindow.toSubalgebra.carrier) :
    quaternionicTwoColumnSampleLaw.map (projectedMatrix W) = inducedComplexStateLaw 2 := by
  have h : quaternionicTwoColumnSampleLaw = quaternionicTwoColumnRayLaw.map normalizeAlbert := by
    unfold quaternionicTwoColumnSampleLaw quaternionicTwoColumnRayLaw
    rw [Measure.map_map measurable_normalizeAlbert measurable_quaternionicDyadFromTwoColumns]
  rw [h, map_projectedMatrix_normalizeAlbert, map_projectedMatrix_eq_gram_of_same_carrier
    2 quaternionicTwoColumnRayLaw standardComplexWindow W hW projectedMatrix_quaternionicTwoColumnRayLaw]
  have hM : Measurable (fun Z : Matrix (Fin 3) (Fin 2) ℂ => Z * Z.conjTranspose) := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    fun_prop
  rw [Measure.map_map measurable_normalizeMatrix hM]
  rfl

private theorem quaternionicAmbient_normalized_atom_map {V : NativeJordanSubalgebra}
    (g : JordanSubalgebraIso V (H3Subalgebra .H)) (x : V.carrier) :
    albertTrace (g.toLinearEquiv x).val = albertTrace x.val := by
  have h := quaternionicIso_preserves_trace g.symm (g.toLinearEquiv x)
  change albertTrace (g.toLinearEquiv.symm (g.toLinearEquiv x)).val = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

private theorem transportQuaternionicAtomMeasure {V : NativeJordanSubalgebra}
    (φ : JordanSubalgebraIso V (H3Subalgebra .H))
    (μ : Measure V.carrier) (ha : ∀ᵐ p ∂μ, IsAtom p.val) :
    ∀ᵐ p ∂μ.map φ.toLinearEquiv, IsAtom p.val := by
  have hm : Measurable φ.toLinearEquiv := φ.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hset : MeasurableSet {p : (H3Subalgebra .H).carrier | IsAtom p.val} :=
    measurable_subtype_coe measurableSet_atomSet
  rw [ae_map_iff hm.aemeasurable hset]
  filter_upwards [ha] with p hp
  refine ⟨?_, (quaternionicAmbient_normalized_atom_map φ p).trans hp.2⟩
  have h : (⟨jordanMul p.val p.val, V.product_mem _ p.property _ p.property⟩ : V.carrier) = p :=
    Subtype.ext hp.1
  have hh := φ.map_jordan p p
  rw [h] at hh
  exact (congrArg Subtype.val hh).symm

private theorem transportQuaternionicInvariantMeasure {V : NativeJordanSubalgebra}
    (φ : JordanSubalgebraIso V (H3Subalgebra .H)) (μ : Measure V.carrier)
    (hInv : ∀ g : JordanSubalgebraIso V V, μ.map g.toLinearEquiv = μ)
    (U : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H)) :
    (μ.map φ.toLinearEquiv).map U.toLinearEquiv = μ.map φ.toLinearEquiv := by
  let VU := (φ.trans U).trans φ.symm
  have hφ : Measurable φ.toLinearEquiv := φ.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hU : Measurable U.toLinearEquiv := U.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hVU : Measurable VU.toLinearEquiv := VU.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hcomp : U.toLinearEquiv ∘ φ.toLinearEquiv = φ.toLinearEquiv ∘ VU.toLinearEquiv := by
    funext p
    change U.toLinearEquiv (φ.toLinearEquiv p) =
      φ.toLinearEquiv (φ.toLinearEquiv.symm (U.toLinearEquiv (φ.toLinearEquiv p)))
    rw [LinearEquiv.apply_symm_apply]
  rw [Measure.map_map hU hφ, hcomp, ← Measure.map_map hφ hVU, hInv VU]

private theorem nativeJordanSubalgebra_eq_of_carrier_eq {A B : NativeJordanSubalgebra}
    (h : A.carrier = B.carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

private theorem rel_quaternionicComplexWindow_normalize (W : ComplexWindow)
    (hW : W.toSubalgebra.carrier ≤ (H3Subalgebra .H).carrier) :
    ∃ ψ : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H),
      (transportComplexWindowInto ψ (quaternionicAmbient_normalized_atom_map ψ) W hW).toSubalgebra.carrier =
        standardComplexWindow.toSubalgebra.carrier := by
  have hIso : Nonempty (JordanSubalgebraIso (H3Subalgebra .C) W.toSubalgebra) := by
    rw [nativeJordanSubalgebra_eq_of_carrier_eq H3Subalgebra_C_eq_standardComplexWindow]
    exact ⟨complexWindowIso standardComplexWindow W⟩
  obtain ⟨ψ, hψ⟩ := subalgebra_H3H_iso_H3C_ambient_conjugate W.toSubalgebra hW hIso
  refine ⟨ψ, ?_⟩
  let W' := transportComplexWindowInto ψ (quaternionicAmbient_normalized_atom_map ψ) W hW
  have hle : W'.toSubalgebra.carrier ≤ standardComplexWindow.toSubalgebra.carrier := by
    rintro _ ⟨M, rfl⟩
    rw [← H3Subalgebra_C_eq_standardComplexWindow]
    obtain ⟨_, hm⟩ := hψ (W.embedding M) ⟨M, rfl⟩
    exact hm
  have hdim (A : ComplexWindow) : Module.finrank ℝ A.toSubalgebra.carrier = Module.finrank ℝ Hermitian3 :=
    (LinearEquiv.ofInjective A.embedding A.injective).finrank_eq.symm
  exact Submodule.eq_of_le_of_finrank_eq hle ((hdim W').trans (hdim standardComplexWindow).symm)

/-- Companion Proposition 5.1 in an arbitrary native quaternionic ambient and
an arbitrary contained complex window, for every invariant atom probability. -/
theorem quaternionicAmbientWindow_probability_law_of_iso (V : NativeJordanSubalgebra)
    (W : ComplexWindow) (hW : W.toSubalgebra.carrier ≤ V.carrier)
    (iso : JordanSubalgebraIso V (H3Subalgebra .H))
    (μ : Measure V.carrier) [IsProbabilityMeasure μ] (ha : ∀ᵐ p ∂μ, IsAtom p.val)
    (hInv : ∀ g : JordanSubalgebraIso V V, μ.map g.toLinearEquiv = μ) :
    μ.map (fun p => projectedMatrix W p.val) = inducedComplexStateLaw 2 := by
  let htrace := quaternionicAmbient_normalized_atom_map iso
  let W' := transportComplexWindowInto iso htrace W hW
  have hW' := transportComplexWindowInto_le iso htrace W hW
  obtain ⟨ψ, hψ⟩ := rel_quaternionicComplexWindow_normalize W' hW'
  let htraceψ := quaternionicAmbient_normalized_atom_map ψ
  let W'' := transportComplexWindowInto ψ htraceψ W' hW'
  let μH := μ.map iso.toLinearEquiv
  have hm : Measurable iso.toLinearEquiv := iso.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hψm : Measurable ψ.toLinearEquiv := ψ.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have : IsProbabilityMeasure μH :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 ‹IsProbabilityMeasure μ›
  have hAt : ∀ᵐ p ∂μH, IsAtom p.val := transportQuaternionicAtomMeasure iso μ ha
  have hIH (g : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H)) :
      μH.map g.toLinearEquiv = μH := transportQuaternionicInvariantMeasure iso μ hInv g
  let f := fun p : V.carrier => projectedMatrix W p.val
  let f' := fun p : (H3Subalgebra .H).carrier => projectedMatrix W' p.val
  let f'' := fun p : (H3Subalgebra .H).carrier => projectedMatrix W'' p.val
  have hf' : Measurable f' := (measurable_projectedMatrix _).comp measurable_subtype_coe
  have hf'' : Measurable f'' := (measurable_projectedMatrix _).comp measurable_subtype_coe
  have hF : f = f' ∘ iso.toLinearEquiv :=
    funext fun p => (projectedMatrix_transportComplexWindowInto iso htrace W hW p).symm
  have hF' : f' = f'' ∘ ψ.toLinearEquiv :=
    funext fun p => (projectedMatrix_transportComplexWindowInto ψ htraceψ W' hW' p).symm
  change μ.map f = inducedComplexStateLaw 2
  rw [hF, ← Measure.map_map hf' hm]
  change μH.map f' = _
  rw [hF', ← Measure.map_map hf'' hψm, hIH ψ]
  change μH.map (projectedMatrix W'' ∘ Subtype.val) = _
  rw [← Measure.map_map (measurable_projectedMatrix _) measurable_subtype_coe,
    standardQuaternionicAmbient_eq_nativeSampleLaw μH hAt hIH]
  exact projectedMatrix_quaternionicTwoColumnSampleLaw_same_carrier W'' hψ

end AlbertSequential.WindowProbability
