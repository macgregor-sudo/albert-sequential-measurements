/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityQuaternionicAtoms

/-! Compact quaternionic unitary comparison on the actual native atom carrier. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory Set
open scoped AlbertSequential.WindowProbability Matrix

/-- The actual quaternionic unitary group is compact in the entrywise topology. -/
theorem isCompact_quaternionicUnitary : IsCompact (unitary QuatMatrix3 : Set QuatMatrix3) := by
  have hp : IsCompact {A : QuatMatrix3 | ∀ i j, A i j ∈ Metric.closedBall (0 : Quaternion ℝ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall _ _
  apply hp.of_isClosed_subset isClosed_unitary
  intro A hA i j
  let U : unitary QuatMatrix3 := ⟨A, hA⟩
  have h := quatNormSq_sum_unitary_mulVec U (Pi.single j 1)
  change (∑ i, quatNormSq ((A *ᵥ Pi.single j 1) i)) = _ at h
  have hE : (∑ i, quatNormSq ((Pi.single j 1 : Fin 3 → Quaternion ℝ) i)) = 1 := by
    rw [Fintype.sum_eq_single j]
    · simp [quatNormSq]
    · intro i hij
      simp [Pi.single_eq_of_ne hij, quatNormSq]
  have hn : (∑ i, quatNormSq (A i j)) = 1 := by
    rw [Matrix.mulVec_single_one, hE] at h
    exact h
  have hsq : ‖A i j‖ * ‖A i j‖ ≤ 1 := by
    calc
      _ = quatNormSq (A i j) := by rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']; rfl
      _ ≤ ∑ a, quatNormSq (A a j) :=
        Finset.single_le_sum (f := fun a : Fin 3 => quatNormSq (A a j))
          (fun a _ => by unfold quatNormSq; positivity) (Finset.mem_univ i)
      _ = 1 := hn
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg (A i j)]

/-- The whole quaternionic unitary group viewed as a positive compact. -/
def allQuaternionicUnitaries : TopologicalSpace.PositiveCompacts (unitary QuatMatrix3) := by
  let : CompactSpace (unitary QuatMatrix3) := isCompact_iff_compactSpace.mp isCompact_quaternionicUnitary
  exact ⟨⟨univ, isCompact_univ⟩, by simp⟩

/-- Right Haar probability of the literal matrix group. -/
def quaternionicUnitaryHaarProbability : Measure (unitary QuatMatrix3) :=
  (Measure.haarMeasure allQuaternionicUnitaries).inv

instance : IsProbabilityMeasure quaternionicUnitaryHaarProbability := by
  have : IsProbabilityMeasure (Measure.haarMeasure allQuaternionicUnitaries) := ⟨Measure.haarMeasure_self⟩
  unfold quaternionicUnitaryHaarProbability Measure.inv
  infer_instance

instance : quaternionicUnitaryHaarProbability.IsMulRightInvariant := by
  unfold quaternionicUnitaryHaarProbability
  infer_instance

/-- The exact native carrier automorphism induced by quaternionic unitary conjugation. -/
def quaternionicUnitaryIso (U : unitary QuatMatrix3) :
    JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H) :=
  assocCD_unitaryIso assocCD_H (star U.val)
    (by rw [star_star]; exact (Unitary.mem_iff.mp U.property).2)
    (by rw [star_star]; exact (Unitary.mem_iff.mp U.property).1)

theorem quatMatrixToAlbert_quaternionicUnitaryIso_apply (U : unitary QuatMatrix3) (M : QuatHermitian3) :
    ((quaternionicUnitaryIso U).toLinearEquiv (assocHermEquiv assocCD_H M)).val =
      quatMatrixToAlbert quatEmbed1 (U.val * M.val * star U.val) := by
  let E := assocHermEquiv assocCD_H
  change quatMatrixToAlbert quatEmbed1 (star (star U.val) * (E.symm (E M)).val * star U.val) = _
  rw [LinearEquiv.symm_apply_apply, star_star]

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

private def quatAtomMatrices : Set QuatMatrix3 :=
  {M | IsSelfAdjoint M ∧ IsAtom (quatMatrixToAlbert quatEmbed1 M)}

private theorem measurableSet_quatAtomMatrices : MeasurableSet quatAtomMatrices := by
  change MeasurableSet ({M : QuatMatrix3 | IsSelfAdjoint M} ∩
    quatMatrixToAlbert quatEmbed1 ⁻¹' {x | IsAtom x})
  refine MeasurableSet.inter ?_ (measurable_quatMatrixToAlbert measurableSet_atomSet)
  exact (isClosed_eq (continuous_id.matrix_conjTranspose : Continuous (fun A : QuatMatrix3 => star A))
    continuous_id).measurableSet

private abbrev QuatAtomicMatrix := ↥quatAtomMatrices

private theorem quatUnitaryConjugate_herm (U : unitary QuatMatrix3) {M : QuatMatrix3}
    (h : IsSelfAdjoint M) : IsSelfAdjoint (U.val * M * star U.val) := by
  change star (U.val * M * star U.val) = _
  rw [star_mul, star_mul, star_star, h.star_eq, Matrix.mul_assoc]

private theorem quatUnitaryConjugate_atom (U : unitary QuatMatrix3) {M : QuatMatrix3}
    (h : M ∈ quatAtomMatrices) : U.val * M * star U.val ∈ quatAtomMatrices := by
  refine ⟨quatUnitaryConjugate_herm U h.1, ?_⟩
  let N : QuatHermitian3 := ⟨M, h.1⟩
  change IsAtom (quatMatrixToAlbert quatEmbed1 (U.val * N.val * star U.val))
  rw [← quatMatrixToAlbert_quaternionicUnitaryIso_apply U N]
  exact iso_maps_atom (k := .H) (quaternionicUnitaryIso U) _ h.2

private instance : MulAction (unitary QuatMatrix3) QuatAtomicMatrix where
  smul U M := ⟨U.val * M.val * star U.val, quatUnitaryConjugate_atom U M.property⟩
  one_smul M := Subtype.ext (by change (1 : QuatMatrix3) * M.val * star (1 : QuatMatrix3) = M.val; simp)
  mul_smul U V M := by
    apply Subtype.ext
    change U.val * V.val * M.val * star (U.val * V.val) =
      U.val * (V.val * M.val * star V.val) * star U.val
    simp only [star_mul, mul_assoc]

private theorem measurable_quatConjugation {α : Type*} [MeasurableSpace α]
    {A B : α → QuatMatrix3} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x => A x * B x * star (A x)) := by
  have hmul {f g : α → QuatMatrix3} (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun x => f x * g x) := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun x => ∑ k, f x i k * g x k j)
    have ev (a b : Fin 3) : Measurable (fun M : QuatMatrix3 => M a b) :=
      (measurable_pi_apply b).comp (measurable_pi_apply a)
    exact Finset.measurable_fun_sum _ fun k _ => ((ev i k).comp hf).mul ((ev k j).comp hg)
  have hs : Measurable (fun x => star (A x)) :=
    (continuous_id.matrix_conjTranspose : Continuous (fun M : QuatMatrix3 => star M)).measurable.comp hA
  exact hmul (hmul hA hB) hs

private theorem measurable_quatAtomicMatrixAction :
    Measurable (fun p : (unitary QuatMatrix3) × QuatAtomicMatrix => p.1 • p.2) := by
  have hA : Measurable (fun p : (unitary QuatMatrix3) × QuatAtomicMatrix => p.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have hB : Measurable (fun p : (unitary QuatMatrix3) × QuatAtomicMatrix => p.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  exact (measurable_quatConjugation hA hB).subtype_mk

private def quatCoordinateAtomMatrix : QuatAtomicMatrix := by
  let v : Fin 3 → Quaternion ℝ := Pi.single 0 1
  refine ⟨normalizedQuaternionicMatrixDyad v, normalizedQuaternionicMatrixDyad_hermitian v, ?_⟩
  rw [quatMatrixToAlbert_normalizedQuaternionicMatrixDyad]
  have hn : ∑ i, quatNormSq (v i) = 1 := by
    rw [Fintype.sum_eq_single 0]
    · simp [v, quatNormSq]
    · intro i hi
      simp [v, Pi.single_eq_of_ne hi, quatNormSq]
  have ha := quatDyad_isAtom quatEmbed1 quatEmbed1_isQuatEmbedding v 1 one_ne_zero hn
  rw [normalizeAlbert, ha.2, inv_one, one_smul]
  exact ha

private theorem quatAtomicMatrix_transitive (M : QuatAtomicMatrix) :
    ∃ U : unitary QuatMatrix3, U • quatCoordinateAtomMatrix = M := by
  let A : QuatHermitian3 := ⟨M.val, M.property.1⟩
  let E := assocHermEquiv assocCD_H
  let p := quatMatrixToAlbert quatEmbed1 M.val
  have hp : p ∈ standardQuaternionicWindow.subalgebra.carrier :=
    H3Subalgebra_H_eq_standardQuaternionicWindow ▸ (E A).property
  obtain ⟨U, hU⟩ := standardQuaternionicAtom_in_unitaryOrbit p M.property.2 hp
  use U
  apply Subtype.ext
  let B : QuatHermitian3 := ⟨(U • quatCoordinateAtomMatrix).val, (U • quatCoordinateAtomMatrix).property.1⟩
  have hAB : E A = E B := Subtype.ext hU
  exact congrArg (fun N : QuatHermitian3 => N.val) (E.injective hAB).symm

set_option maxHeartbeats 1800000 in
private theorem quatAtomicMatrix_meas_invariant_eq_haar
    (μ : Measure QuatMatrix3) [IsProbabilityMeasure μ]
    (ha : ∀ᵐ M ∂μ, M ∈ quatAtomMatrices)
    (hi : ∀ U : unitary QuatMatrix3, μ.map (fun M : QuatMatrix3 => U.val * M * star U.val) = μ) :
    μ = quaternionicUnitaryHaarProbability.map
      (fun U => U.val * quatCoordinateAtomMatrix.val * star U.val) := by
  let val : QuatAtomicMatrix → QuatMatrix3 := Subtype.val
  let μa := μ.comap val
  have hm : MeasurableEmbedding val := MeasurableEmbedding.subtype_coe measurableSet_quatAtomMatrices
  have ht : μa.map val = μ :=
    (map_comap_subtype_coe measurableSet_quatAtomMatrices μ).trans (Measure.restrict_eq_self_of_ae_mem ha)
  have : IsProbabilityMeasure μa :=
    (Measure.isProbabilityMeasure_map_iff hm.measurable.aemeasurable).mp (ht ▸ ‹IsProbabilityMeasure μ›)
  have hμ (U : unitary QuatMatrix3) : MeasurePreserving (fun M : QuatAtomicMatrix => U • M) μa μa := by
    have hA : Measurable (fun M : QuatAtomicMatrix => U • M) := by
      have hj : Measurable (fun M : QuatAtomicMatrix => U.val * M.val * star U.val) :=
        measurable_quatConjugation measurable_const measurable_subtype_coe
      exact hj.subtype_mk
    have hB : Measurable (fun M : QuatMatrix3 => U.val * M * star U.val) :=
      measurable_quatConjugation measurable_const measurable_id
    refine ⟨hA, hm.map_injective ?_⟩
    rw [Measure.map_map hm.measurable hA]
    change μa.map ((fun M : QuatMatrix3 => U.val * M * star U.val) ∘ val) = _
    rw [← Measure.map_map hB hm.measurable, ht, hi U]
  have horbit : Measurable (fun U : unitary QuatMatrix3 => U • quatCoordinateAtomMatrix) := by
    have hj : Measurable (fun U : unitary QuatMatrix3 =>
        U.val * quatCoordinateAtomMatrix.val * star U.val) :=
      measurable_quatConjugation measurable_subtype_coe measurable_const
    exact hj.subtype_mk
  have he := invariantProbability_eq_orbitMap measurable_quatAtomicMatrixAction quatCoordinateAtomMatrix
    quatAtomicMatrix_transitive quaternionicUnitaryHaarProbability μa hμ
  rw [← ht, he, Measure.map_map hm.measurable horbit]
  rfl

private theorem ae_quaternionicMatrixDyadSampleLaw_mem :
    ∀ᵐ M ∂quaternionicMatrixDyadSampleLaw, M ∈ quatAtomMatrices := by
  have hA : ∀ᵐ M ∂quaternionicMatrixDyadSampleLaw, IsAtom (quatMatrixToAlbert quatEmbed1 M) := by
    apply ae_of_ae_map measurable_quatMatrixToAlbert.aemeasurable
    rw [map_quatMatrixToAlbert_quaternionicMatrixDyadSampleLaw]
    exact ae_quaternionicTwoColumnSampleLaw_isAtom
  have hH : ∀ᵐ M ∂quaternionicMatrixDyadSampleLaw, IsSelfAdjoint M := by
    let f := fun Z : Matrix (Fin 3) (Fin 2) ℂ => normalizedQuaternionicMatrixDyad
      (fun i => quaternionOfComplexPair (Z i 0) (Z i 1))
    have hF : AEMeasurable f (standardComplexGaussianMatrix 2) :=
      measurable_quaternionicMatrixDyadSample.aemeasurable
    have hmeas : MeasurableSet {M : QuatMatrix3 | IsSelfAdjoint M} :=
      (isClosed_eq (continuous_id.matrix_conjTranspose : Continuous (fun A : QuatMatrix3 => star A))
        continuous_id).measurableSet
    change ∀ᵐ M ∂(standardComplexGaussianMatrix 2).map f, IsSelfAdjoint M
    rw [ae_map_iff hF hmeas]
    exact Eventually.of_forall fun _ => normalizedQuaternionicMatrixDyad_hermitian _
  exact hH.and hA

/-- Every invariant atom probability on the standard quaternionic carrier
pushes forward to the exact native normalized two-column sample. -/
theorem standardQuaternionicAmbient_eq_nativeSampleLaw (μ : Measure (H3Subalgebra .H).carrier)
    [IsProbabilityMeasure μ] (ha : ∀ᵐ p ∂μ, IsAtom p.val)
    (hi : ∀ g : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H), μ.map g.toLinearEquiv = μ) :
    μ.map (Subtype.val : (H3Subalgebra .H).carrier → Albert) = quaternionicTwoColumnSampleLaw := by
  let E : QuatHermitian3 ≃ₗ[ℝ] (H3Subalgebra .H).carrier := assocHermEquiv assocCD_H
  let f := fun p : (H3Subalgebra .H).carrier => (E.symm p).val
  have hf : Measurable f := by
    let inc : QuatHermitian3 →ₗ[ℝ] (Fin 3 → Fin 3 → Quaternion ℝ) :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact (inc.comp E.symm.toLinearMap).continuous_of_finiteDimensional.measurable
  have hP (p : (H3Subalgebra .H).carrier) : quatMatrixToAlbert quatEmbed1 (f p) = p.val :=
    congrArg Subtype.val (E.apply_symm_apply p)
  have hMap : (μ.map f) = quaternionicMatrixDyadSampleLaw := by
    have : IsProbabilityMeasure (μ.map f) :=
      (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 ‹IsProbabilityMeasure μ›
    have hAtom : ∀ᵐ M ∂μ.map f, M ∈ quatAtomMatrices := by
      change ∀ᵐ M ∂μ.map f, IsSelfAdjoint M ∧ IsAtom (quatMatrixToAlbert quatEmbed1 M)
      rw [ae_map_iff hf.aemeasurable measurableSet_quatAtomMatrices]
      filter_upwards [ha] with p hp
      exact ⟨(E.symm p).property, hP p ▸ hp⟩
    have hInv (U : unitary QuatMatrix3) :
        (μ.map f).map (fun M : QuatMatrix3 => U.val * M * star U.val) = μ.map f := by
      let C := fun M : QuatMatrix3 => U.val * M * star U.val
      let g := quaternionicUnitaryIso U
      have hg : Measurable g.toLinearEquiv := g.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
      have hC : Measurable C := measurable_quatConjugation measurable_const measurable_id
      have hcomm : C ∘ f = f ∘ g.toLinearEquiv := by
        funext p
        let M := E.symm p
        let N : QuatHermitian3 := ⟨C M.val, quatUnitaryConjugate_herm U M.property⟩
        have hE : E M = p := E.apply_symm_apply p
        have hN : E N = g.toLinearEquiv p := by
          apply Subtype.ext
          rw [← hE]
          exact (quatMatrixToAlbert_quaternionicUnitaryIso_apply U M).symm
        exact congrArg Subtype.val (E.symm_apply_eq.mpr hN.symm).symm
      rw [Measure.map_map hC hf, hcomm, ← Measure.map_map hf hg, hi g]
    exact (quatAtomicMatrix_meas_invariant_eq_haar (μ.map f) hAtom hInv).trans
      (quatAtomicMatrix_meas_invariant_eq_haar quaternionicMatrixDyadSampleLaw
        ae_quaternionicMatrixDyadSampleLaw_mem map_quaternionicUnitary_quaternionicMatrixDyadSampleLaw).symm
  have hc : (Subtype.val : (H3Subalgebra .H).carrier → Albert) = quatMatrixToAlbert quatEmbed1 ∘ f :=
    funext fun p => (hP p).symm
  rw [hc, ← Measure.map_map measurable_quatMatrixToAlbert hf, hMap,
    map_quatMatrixToAlbert_quaternionicMatrixDyadSampleLaw]

/-- The invariant native probability in the standard quaternionic ambient
projects to the exact two-column law on the standard complex window. -/
theorem standardQuaternionicAmbient_probability_law (μ : Measure (H3Subalgebra .H).carrier)
    [IsProbabilityMeasure μ] (ha : ∀ᵐ p ∂μ, IsAtom p.val)
    (hi : ∀ g : JordanSubalgebraIso (H3Subalgebra .H) (H3Subalgebra .H), μ.map g.toLinearEquiv = μ) :
    μ.map (fun p => projectedMatrix standardComplexWindow p.val) = inducedComplexStateLaw 2 := by
  rw [← projectedMatrix_quaternionicTwoColumnSampleLaw, ← standardQuaternionicAmbient_eq_nativeSampleLaw μ ha hi,
    Measure.map_map (measurable_projectedMatrix _) measurable_subtype_coe]
  rfl

end AlbertSequential.WindowProbability
