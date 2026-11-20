/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilitySphere
public import WindowProbabilityTransport
public import ComplexWindowDeterminantAndMax
public import SubalgebraCoordsAndLine

/-! Invariant pure-state probability on the complex rank-three ambient
algebra in companion Proposition 5.1. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory Set
open scoped Matrix AlbertSequential.WindowProbability

private def pureProjectionMatrix (v : Fin 3 → ℂ) : ComplexMatrix3 :=
  Matrix.vecMulVec v (star v)

private theorem sum_star_mul_of_unit {v : Fin 3 → ℂ} (hv : complexDirectionEnergy v = 1) :
    ∑ i, star (v i) * v i = 1 := by
  have h (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
  simp only [h, ← Complex.ofReal_sum]
  change (complexDirectionEnergy v : ℂ) = 1
  rw [hv, Complex.ofReal_one]

private theorem energy_of_sum_star_mul {v : Fin 3 → ℂ} (hv : ∑ i, star (v i) * v i = 1) :
    complexDirectionEnergy v = 1 := by
  have h (z : ℂ) : (star z * z).re = Complex.normSq z := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  simpa only [Complex.re_sum, h, Complex.one_re, complexDirectionEnergy] using congrArg Complex.re hv

private theorem pureProjectionMatrix_rankOne {v : Fin 3 → ℂ} (hv : complexDirectionEnergy v = 1) :
    IsComplexRankOneProjection (pureProjectionMatrix v) :=
  ⟨v, sum_star_mul_of_unit hv, fun _ _ => rfl⟩

private theorem isCompact_complexUnitSphere :
    IsCompact {v : Fin 3 → ℂ | complexDirectionEnergy v = 1} := by
  have hclosed : IsClosed {v : Fin 3 → ℂ | complexDirectionEnergy v = 1} := by
    apply isClosed_eq _ continuous_const
    unfold complexDirectionEnergy
    fun_prop
  have hbound : IsCompact {v : Fin 3 → ℂ | ∀ i, v i ∈ Metric.closedBall (0 : ℂ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_closedBall (0 : ℂ) 1
  apply hbound.of_isClosed_subset hclosed
  intro v hv i
  have hs : ‖v i‖^2 ≤ 1 := by
    rw [Complex.sq_norm, ← (show complexDirectionEnergy v = 1 from hv)]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg (v i)]

private theorem measurableSet_complexRankOne :
    MeasurableSet {P : ComplexMatrix3 | IsComplexRankOneProjection P} := by
  have hP : Continuous pureProjectionMatrix := by
    apply continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous (fun v : Fin 3 → ℂ => v i * star (v j))
    fun_prop
  have h : pureProjectionMatrix '' {v : Fin 3 → ℂ | complexDirectionEnergy v = 1} =
      {P : ComplexMatrix3 | IsComplexRankOneProjection P} := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact pureProjectionMatrix_rankOne hv
    · rintro ⟨v, hv, hP⟩
      exact ⟨v, energy_of_sum_star_mul hv, Matrix.ext fun i j => (hP i j).symm⟩
  rw [← h]
  exact (isCompact_complexUnitSphere.image hP).isClosed.measurableSet

/-- Matrix conjugation by an actual complex unitary. -/
def complexUnitaryConjugate (U : Matrix.unitaryGroup (Fin 3) ℂ) (P : ComplexMatrix3) : ComplexMatrix3 :=
  (U : ComplexMatrix3) * P * star (U : ComplexMatrix3)

private theorem complexUnitaryConjugate_pureProjection (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (v : Fin 3 → ℂ) :
    complexUnitaryConjugate U (pureProjectionMatrix v) =
      pureProjectionMatrix ((U : ComplexMatrix3) *ᵥ v) := by
  unfold complexUnitaryConjugate pureProjectionMatrix
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec, ← Matrix.star_eq_conjTranspose]

private theorem complexUnitaryConjugate_rankOne (U : Matrix.unitaryGroup (Fin 3) ℂ)
    {P : ComplexMatrix3} (hp : IsComplexRankOneProjection P) :
    IsComplexRankOneProjection (complexUnitaryConjugate U P) := by
  obtain ⟨v, hv, hp⟩ := hp
  have he : pureProjectionMatrix v = P := Matrix.ext fun i j => (hp i j).symm
  rw [← he, complexUnitaryConjugate_pureProjection]
  exact pureProjectionMatrix_rankOne
    ((complexDirectionEnergy_unitary U v).trans (energy_of_sum_star_mul hv))

private abbrev ComplexRankOneSpace := {P : ComplexMatrix3 // IsComplexRankOneProjection P}

private instance : MulAction (Matrix.unitaryGroup (Fin 3) ℂ) ComplexRankOneSpace where
  smul U P := ⟨complexUnitaryConjugate U P.val, complexUnitaryConjugate_rankOne U P.property⟩
  one_smul P := by
    apply Subtype.ext
    change (1 : ComplexMatrix3) * P.val * star (1 : ComplexMatrix3) = P.val
    simp
  mul_smul U V P := by
    apply Subtype.ext
    change (U : ComplexMatrix3) * (V : ComplexMatrix3) * P.val *
      star ((U : ComplexMatrix3) * (V : ComplexMatrix3)) =
      (U : ComplexMatrix3) * ((V : ComplexMatrix3) * P.val * star (V : ComplexMatrix3)) *
        star (U : ComplexMatrix3)
    simp only [star_mul, mul_assoc]

private theorem measurable_complexMatrix_mul {α : Type*} [MeasurableSpace α]
    {f g : α → ComplexMatrix3} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x * g x) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun x => ∑ k, f x i k * g x k j)
  have ev (a b : Fin 3) : Measurable (fun M : ComplexMatrix3 => M a b) :=
    (measurable_pi_apply b).comp (measurable_pi_apply a)
  exact Finset.measurable_fun_sum _ fun k _ => ((ev i k).comp hf).mul ((ev k j).comp hg)

private theorem measurable_complexUnitaryConjugate_apply {α : Type*} [MeasurableSpace α]
    {U : α → Matrix.unitaryGroup (Fin 3) ℂ} {P : α → ComplexMatrix3}
    (hU : Measurable (fun x => (U x : ComplexMatrix3))) (hP : Measurable P) :
    Measurable (fun x => complexUnitaryConjugate (U x) (P x)) := by
  have hs : Measurable (fun x => star (U x : ComplexMatrix3)) := by
    apply Measurable.of_eval_matrix
    intro i j
    have ev : Measurable (fun M : ComplexMatrix3 => M j i) :=
      (measurable_pi_apply i).comp (measurable_pi_apply j)
    exact Complex.conjLIE.continuous.measurable.comp (ev.comp hU)
  exact measurable_complexMatrix_mul (measurable_complexMatrix_mul hU hP) hs

private theorem measurable_complexUnitaryConjugate (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    Measurable (complexUnitaryConjugate U) :=
  measurable_complexUnitaryConjugate_apply (U := fun _ : ComplexMatrix3 => U)
    (P := id) measurable_const measurable_id

set_option maxHeartbeats 2000000 in
private theorem projective_orbit_invariant_probability
    (μ : Measure ComplexMatrix3) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ P ∂μ, IsComplexRankOneProjection P)
    (hInv : ∀ U : Matrix.unitaryGroup (Fin 3) ℂ, μ.map (complexUnitaryConjugate U) = μ) :
    μ = (complexUnitaryHaarProbability (Fin 3)).map
      (fun U => complexUnitaryConjugate U (pureProjectionMatrix (Pi.single 0 1))) := by
  let P₀ : ComplexRankOneSpace := ⟨pureProjectionMatrix (Pi.single 0 1),
    pureProjectionMatrix_rankOne (by simp [complexDirectionEnergy, Pi.single_apply])⟩
  let val : ComplexRankOneSpace → ComplexMatrix3 := Subtype.val
  let μA := μ.comap val
  have hv : MeasurableEmbedding val := MeasurableEmbedding.subtype_coe measurableSet_complexRankOne
  have hmap : μA.map val = μ :=
    (map_comap_subtype_coe measurableSet_complexRankOne μ).trans (Measure.restrict_eq_self_of_ae_mem hμ)
  have : IsProbabilityMeasure μA :=
    (Measure.isProbabilityMeasure_map_iff hv.measurable.aemeasurable).mp (hmap ▸ ‹IsProbabilityMeasure μ›)
  have hmA : Measurable (fun p : Matrix.unitaryGroup (Fin 3) ℂ × ComplexRankOneSpace => p.1 • p.2) := by
    have hU : Measurable (fun p : Matrix.unitaryGroup (Fin 3) ℂ × ComplexRankOneSpace =>
        (p.1 : ComplexMatrix3)) := measurable_subtype_coe.comp measurable_fst
    have hP : Measurable (fun p : Matrix.unitaryGroup (Fin 3) ℂ × ComplexRankOneSpace =>
        p.2.val) := hv.measurable.comp measurable_snd
    have hm : Measurable (fun p : Matrix.unitaryGroup (Fin 3) ℂ × ComplexRankOneSpace =>
        complexUnitaryConjugate p.1 p.2.val) :=
      measurable_complexUnitaryConjugate_apply (U := Prod.fst) hU hP
    change Measurable (fun p : Matrix.unitaryGroup (Fin 3) ℂ × ComplexRankOneSpace =>
      (⟨complexUnitaryConjugate p.1 p.2.val, complexUnitaryConjugate_rankOne p.1 p.2.property⟩ :
        ComplexRankOneSpace))
    exact hm.subtype_mk
  have htrans (P : ComplexRankOneSpace) : ∃ U : Matrix.unitaryGroup (Fin 3) ℂ, U • P₀ = P := by
    obtain ⟨v, hv, hp⟩ := P.property
    obtain ⟨U, hU⟩ := complexUnitaryOrbit_contains_unitVector 0 v (energy_of_sum_star_mul hv)
    use U
    apply Subtype.ext
    change complexUnitaryConjugate U (pureProjectionMatrix (Pi.single 0 1)) = P.val
    rw [complexUnitaryConjugate_pureProjection, hU]
    exact Matrix.ext (fun i j => (hp i j).symm)
  have hi (U : Matrix.unitaryGroup (Fin 3) ℂ) : MeasurePreserving (fun P : ComplexRankOneSpace => U • P) μA μA := by
    have hm : Measurable (fun P : ComplexRankOneSpace => U • P) :=
      hmA.comp measurable_prodMk_left
    have hM := measurable_complexUnitaryConjugate U
    refine ⟨hm, hv.map_injective ?_⟩
    rw [Measure.map_map hv.measurable hm]
    change μA.map (complexUnitaryConjugate U ∘ val) = _
    rw [← Measure.map_map hM hv.measurable, hmap, hInv U]
  have he := invariantProbability_eq_orbitMap hmA P₀ htrans (complexUnitaryHaarProbability (Fin 3)) μA hi
  have horbit : Measurable (fun U : Matrix.unitaryGroup (Fin 3) ℂ => U • P₀) :=
    hmA.comp measurable_prodMk_right
  rw [← hmap, he, Measure.map_map hv.measurable horbit]
  rfl

theorem map_complexUnitaryConjugate_inducedComplexStateLaw (k : ℕ)
    (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    (inducedComplexStateLaw k).map (complexUnitaryConjugate U) = inducedComplexStateLaw k := by
  have hU := measurePreserving_standardComplexGaussianMatrix_unitary k U
  have hC := measurable_complexUnitaryConjugate U
  have hN := measurable_normalizedComplexGram k
  have hcomm : complexUnitaryConjugate U ∘ normalizedComplexGram k =
      normalizedComplexGram k ∘ (fun Z : Matrix (Fin 3) (Fin k) ℂ => (U : ComplexMatrix3) * Z) := by
    funext Z
    have hgram : ((U : ComplexMatrix3) * Z) * ((U : ComplexMatrix3) * Z).conjTranspose =
        complexUnitaryConjugate U (Z * Z.conjTranspose) := by
      rw [Matrix.conjTranspose_mul]
      simp only [complexUnitaryConjugate, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    have htr (P : ComplexMatrix3) : (complexUnitaryConjugate U P).trace = P.trace := by
      rw [complexUnitaryConjugate, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
    change complexUnitaryConjugate U (normalizedComplexGram k Z) = normalizedComplexGram k ((U : ComplexMatrix3) * Z)
    unfold normalizedComplexGram
    rw [hgram, htr]
    simp [complexUnitaryConjugate]
  unfold inducedComplexStateLaw normalizedGramPushforward
  rw [Measure.map_map hC hN, hcomm, ← Measure.map_map hN hU.measurable, hU.map_eq]

theorem ae_inducedComplexStateLaw_one_rankOne :
    ∀ᵐ P ∂inducedComplexStateLaw 1, IsComplexRankOneProjection P := by
  unfold inducedComplexStateLaw normalizedGramPushforward
  rw [ae_map_iff (measurable_normalizedComplexGram 1).aemeasurable measurableSet_complexRankOne]
  filter_upwards [ae_normSq_normalizedComplexPureVector 1 (by decide)] with Z hZ
  let v := fun i : Fin 3 => normalizedComplexPureVector 1 Z (i, 0)
  have hv : complexDirectionEnergy v = 1 := by
    rw [Fintype.sum_prod_type] at hZ
    simpa [complexDirectionEnergy, v, Fin.sum_univ_one] using hZ
  rw [← partialTrace_normalizedComplexPureVector]
  have h : partialTraceComplexPureVector 1 (normalizedComplexPureVector 1 Z) = pureProjectionMatrix v := by
    ext i j
    simp [partialTraceComplexPureVector, pureProjectionMatrix, Matrix.vecMulVec, v]
  rw [h]
  exact pureProjectionMatrix_rankOne hv

/-- The exact one-column law is the unique unitary-invariant probability
on rank-one complex projections. -/
theorem complex_rankOne_invariantProbability_eq_induced
    (μ : Measure ComplexMatrix3) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ P ∂μ, IsComplexRankOneProjection P)
    (hInv : ∀ U : Matrix.unitaryGroup (Fin 3) ℂ, μ.map (complexUnitaryConjugate U) = μ) :
    μ = inducedComplexStateLaw 1 :=
  (projective_orbit_invariant_probability μ hμ hInv).trans
    (projective_orbit_invariant_probability (inducedComplexStateLaw 1)
      ae_inducedComplexStateLaw_one_rankOne (map_complexUnitaryConjugate_inducedComplexStateLaw 1)).symm

/-- Unitary conjugation restricted to the real vector space of
Hermitian complex matrices. -/
def hermitianUnitaryConjugate (U : Matrix.unitaryGroup (Fin 3) ℂ) : Hermitian3 ≃ₗ[ℝ] Hermitian3 := by
  let C := Unitary.conjStarAlgAut ℂ ComplexMatrix3 U
  have hC (M : ComplexMatrix3) (hM : IsSelfAdjoint M) : IsSelfAdjoint (C M) := by
    change star (C M) = C M
    rw [← map_star, hM.star_eq]
  have hCi (M : ComplexMatrix3) (hM : IsSelfAdjoint M) : IsSelfAdjoint (C.symm M) := by
    change star (C.symm M) = C.symm M
    rw [← map_star, hM.star_eq]
  refine
    { toFun := fun M => ⟨C M.val, hC _ M.property⟩
      invFun := fun M => ⟨C.symm M.val, hCi _ M.property⟩
      left_inv := fun M => Subtype.ext (C.symm_apply_apply M.val)
      right_inv := fun M => Subtype.ext (C.apply_symm_apply M.val)
      map_add' := fun M N => Subtype.ext (map_add C M.val N.val)
      map_smul' := ?_ }
  intro r M
  apply Subtype.ext
  have hr (N : ComplexMatrix3) : r • N = (r : ℂ) • N := by ext i j; simp [Complex.real_smul]
  change C (r • M.val) = r • C M.val
  simp only [hr, map_smul]

theorem hermitianUnitaryConjugate_apply (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (M : Hermitian3) :
    (hermitianUnitaryConjugate U M : ComplexMatrix3) =
      complexUnitaryConjugate U M.val := rfl

/-- Each actual complex unitary induces a unital Jordan automorphism of
the native complex window's carrier. -/
def complexWindowUnitaryIso (W : ComplexWindow) (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    JordanSubalgebraIso W.toSubalgebra W.toSubalgebra := by
  let E : Hermitian3 ≃ₗ[ℝ] W.toSubalgebra.carrier :=
    LinearEquiv.ofInjective W.embedding W.injective
  let T := hermitianUnitaryConjugate U
  refine ⟨(E.symm.trans T).trans E, ?_, ?_⟩
  · have h1 : E (1 : Hermitian3) = ⟨albertUnit, W.toSubalgebra.unit_mem⟩ :=
      Subtype.ext W.unit
    have ht : T 1 = 1 := by
      apply Subtype.ext
      exact map_one (Unitary.conjStarAlgAut ℂ _ U)
    rw [← h1]
    change E (T (E.symm (E 1))) = E 1
    rw [LinearEquiv.symm_apply_apply, ht]
  · intro p q
    let A := E.symm p
    let B := E.symm q
    obtain ⟨D, hD⟩ := W.product_closed A B
    have hp : W.embedding A = p.val := congrArg Subtype.val (E.apply_symm_apply p)
    have hq : W.embedding B = q.val := congrArg Subtype.val (E.apply_symm_apply q)
    have hAB : E D = ⟨jordanMul p.val q.val, W.toSubalgebra.product_mem p.val p.property q.val q.property⟩ := by
      apply Subtype.ext
      change W.embedding D = jordanMul p.val q.val
      rw [W.preserves_product A B D hD, hp, hq]
    rw [← hAB]
    apply Subtype.ext
    change W.embedding (T (E.symm (E D))) = jordanMul (W.embedding (T A)) (W.embedding (T B))
    rw [LinearEquiv.symm_apply_apply]
    apply W.preserves_product
    let C := Unitary.conjStarAlgAut ℂ ComplexMatrix3 U
    have hr (N : ComplexMatrix3) : (1/2 : ℝ) • N = (1/2 : ℂ) • N := by
      ext i j
      simp [Complex.real_smul]
    change C D.val = (1/2 : ℝ) • (C A.val * C B.val + C B.val * C A.val)
    rw [hD, hr, map_smul, map_add, map_mul, map_mul, ← hr]

theorem projectedMatrix_complexWindowUnitaryIso (W : ComplexWindow)
    (U : Matrix.unitaryGroup (Fin 3) ℂ) (p : W.toSubalgebra.carrier) :
    projectedMatrix W ((complexWindowUnitaryIso W U).toLinearEquiv p).val =
      complexUnitaryConjugate U (projectedMatrix W p.val) := by
  let E : Hermitian3 ≃ₗ[ℝ] W.toSubalgebra.carrier :=
    LinearEquiv.ofInjective W.embedding W.injective
  let T := hermitianUnitaryConjugate U
  have hp : W.embedding (E.symm p) = p.val := congrArg Subtype.val (E.apply_symm_apply p)
  change (windowProj W (W.embedding (T (E.symm p))) : ComplexMatrix3) =
    complexUnitaryConjugate U (windowProj W p.val : ComplexMatrix3)
  rw [← hp, windowProj_embedding, windowProj_embedding]
  exact hermitianUnitaryConjugate_apply U _

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

/-- The one-column window law for the complex ambient algebra, on the
actual carrier of the supplied window. -/
theorem complexAmbientWindow_probability_law (W : ComplexWindow)
    (μ : Measure W.toSubalgebra.carrier) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ p ∂μ, IsAtom p.val)
    (hInv : ∀ g : JordanSubalgebraIso W.toSubalgebra W.toSubalgebra, μ.map g.toLinearEquiv = μ) :
    μ.map (fun p : W.toSubalgebra.carrier => projectedMatrix W p.val) = inducedComplexStateLaw 1 := by
  let f := fun p : W.toSubalgebra.carrier => projectedMatrix W p.val
  have hf : Measurable f := (measurable_projectedMatrix W).comp measurable_subtype_coe
  change μ.map f = _
  apply complex_rankOne_invariantProbability_eq_induced
  · rw [ae_map_iff hf.aemeasurable measurableSet_complexRankOne]
    filter_upwards [hμ] with p hp
    exact (projectedMatrix_atom_rankOne_iff W hp).mpr p.property
  · intro U
    let g := complexWindowUnitaryIso W U
    have hg : Measurable g.toLinearEquiv :=
      g.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
    have hC := measurable_complexUnitaryConjugate U
    have hc : complexUnitaryConjugate U ∘ f = f ∘ g.toLinearEquiv :=
      funext fun p => (projectedMatrix_complexWindowUnitaryIso W U p).symm
    rw [Measure.map_map hC hf, hc, ← Measure.map_map hf hg, hInv g]

/-- Any native complex ambient algebra containing the supplied
complex window has the same carrier as that window. -/
theorem complexAmbient_eq_window (V : NativeJordanSubalgebra) (W : ComplexWindow)
    (hW : W.toSubalgebra.carrier ≤ V.carrier)
    (iso : JordanSubalgebraIso V standardComplexWindow.toSubalgebra) :
    V = W.toSubalgebra := by
  have hWdim : Module.finrank ℝ W.toSubalgebra.carrier = Module.finrank ℝ Hermitian3 :=
    (LinearEquiv.ofInjective W.embedding W.injective).finrank_eq.symm
  have hVdim : Module.finrank ℝ V.carrier = Module.finrank ℝ Hermitian3 :=
    iso.toLinearEquiv.finrank_eq.trans
      (LinearEquiv.ofInjective standardComplexWindow.embedding standardComplexWindow.injective).finrank_eq.symm
  have h := (Submodule.eq_of_le_of_finrank_eq hW (hWdim.trans hVdim.symm)).symm
  generalize hB : W.toSubalgebra = B at h ⊢
  cases V
  cases B
  cases h
  rfl

/-- The invariant atom law projects to one complex Gaussian column for
any complex rank-three ambient containing the supplied window. -/
theorem complexAmbientWindow_probability_law_of_iso (V : NativeJordanSubalgebra) (W : ComplexWindow)
    (hW : W.toSubalgebra.carrier ≤ V.carrier)
    (iso : JordanSubalgebraIso V standardComplexWindow.toSubalgebra)
    (μ : Measure V.carrier) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ p ∂μ, IsAtom p.val)
    (hInv : ∀ g : JordanSubalgebraIso V V, μ.map g.toLinearEquiv = μ) :
    μ.map (fun p : V.carrier => projectedMatrix W p.val) = inducedComplexStateLaw 1 := by
  have h := complexAmbient_eq_window V W hW iso
  subst V
  exact complexAmbientWindow_probability_law W μ hμ hInv

theorem complexRankOneProjection_rank {P : ComplexMatrix3} (hP : IsComplexRankOneProjection P) :
    P.rank = 1 := by
  obtain ⟨v, hv, hP⟩ := hP
  have he : P = pureProjectionMatrix v := Matrix.ext hP
  have hv' : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra! h
    simp [h] at hv
  obtain ⟨i, hi⟩ := hv'
  let row : Fin 1 → Fin 3 := fun _ => i
  have hd : (P.submatrix row row).det ≠ 0 := by
    rw [Matrix.det_unique]
    change P i i ≠ 0
    rw [hP]
    exact mul_ne_zero hi (star_ne_zero.mpr hi)
  have hbound := Matrix.rank_submatrix_le P row row
  rw [Matrix.rank_of_det_ne_zero hd] at hbound
  have hlo : 1 ≤ P.rank := by simpa using hbound
  have hhi : P.rank ≤ 1 := by
    rw [he]
    exact Matrix.rank_vecMulVec_le v (star v)
  exact le_antisymm hhi hlo

/-- In the complex ambient case the exact projected law has rank one
almost surely. -/
theorem ae_inducedComplexStateLaw_one_rank :
    ∀ᵐ P ∂inducedComplexStateLaw 1, P.rank = 1 :=
  ae_inducedComplexStateLaw_one_rankOne.mono fun _ hp => complexRankOneProjection_rank hp

end AlbertSequential.WindowProbability
