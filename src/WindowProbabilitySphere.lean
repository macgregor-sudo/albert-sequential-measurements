/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityGaussianUnitary
public import WindowProbabilityPureState
public import WindowProbabilityInvariant
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Isotropic complex Gaussian directions on the finite-dimensional unit sphere. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open Filter MeasureTheory Real Set WithLp
open scoped Matrix BigOperators

/-- The squared Euclidean norm in finite complex coordinates. -/
def complexDirectionEnergy {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

theorem complexDirectionEnergy_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    0 ≤ complexDirectionEnergy v := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem complexDirectionEnergy_eq_zero {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    complexDirectionEnergy v = 0 ↔ v = 0 := by
  rw [complexDirectionEnergy, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)]
  simp [funext_iff]

private theorem re_star_mul_self (z : ℂ) : (star z * z).re = Complex.normSq z := by
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem complexDirectionEnergy_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    complexDirectionEnergy ((U : Matrix ι ι ℂ) *ᵥ v) = complexDirectionEnergy v := by
  have h : star ((U : Matrix ι ι ℂ) *ᵥ v) ⬝ᵥ ((U : Matrix ι ι ℂ) *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose,
      Unitary.coe_star_mul_self, Matrix.vecMul_one]
  have hre := congrArg Complex.re h
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, re_star_mul_self,
    complexDirectionEnergy] at hre ⊢
  exact hre

/-- Euclidean direction with the usual trace-independent zero convention. -/
def normalizedComplexDirection {ι : Type*} [Fintype ι] (v : ι → ℂ) : ι → ℂ :=
  (((√(complexDirectionEnergy v))⁻¹ : ℝ) : ℂ) • v

theorem measurable_complexDirectionEnergy {ι : Type*} [Fintype ι] :
    Measurable (complexDirectionEnergy (ι := ι)) := by
  unfold complexDirectionEnergy
  fun_prop

theorem measurable_normalizedComplexDirection {ι : Type*} [Fintype ι] :
    Measurable (normalizedComplexDirection (ι := ι)) := by
  unfold normalizedComplexDirection
  exact (Complex.continuous_ofReal.measurable.comp
    (continuous_sqrt.measurable.comp measurable_complexDirectionEnergy).inv).smul measurable_id

theorem complexDirectionEnergy_normalized {ι : Type*} [Fintype ι] {v : ι → ℂ}
    (hv : v ≠ 0) : complexDirectionEnergy (normalizedComplexDirection v) = 1 := by
  have h : complexDirectionEnergy v ≠ 0 := (complexDirectionEnergy_eq_zero v).not.mpr hv
  have hscale : ((√(complexDirectionEnergy v))⁻¹)^2 = (complexDirectionEnergy v)⁻¹ := by
    rw [inv_pow, sq_sqrt (complexDirectionEnergy_nonneg v)]
  unfold complexDirectionEnergy
  simp only [normalizedComplexDirection, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Finset.mul_sum, ← pow_two]
  change ((√(complexDirectionEnergy v))⁻¹)^2 * complexDirectionEnergy v = 1
  rw [hscale]
  exact inv_mul_cancel₀ h

/-- The distribution of the normalized direction of the exact isotropic
complex Gaussian vector. -/
def complexGaussianSphereLaw (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  (Measure.pi fun _ : ι => standardComplexGaussian).map normalizedComplexDirection

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (complexGaussianSphereLaw ι) := by
  unfold complexGaussianSphereLaw
  infer_instance

theorem ae_complexGaussianSphereLaw_unit {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∀ᵐ v ∂complexGaussianSphereLaw ι, complexDirectionEnergy v = 1 := by
  unfold complexGaussianSphereLaw
  rw [ae_map_iff measurable_normalizedComplexDirection.aemeasurable
    (measurableSet_eq_fun measurable_complexDirectionEnergy measurable_const)]
  have h0 : ∀ᵐ v ∂(Measure.pi fun _ : ι => standardComplexGaussian), v ≠ 0 := by
    have hset : {v : ι → ℂ | ¬v ≠ 0} = {0} := by ext; simp
    rw [ae_iff, hset]
    simp
  exact h0.mono fun _ h => complexDirectionEnergy_normalized h

theorem map_unitary_complexGaussianSphereLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    (complexGaussianSphereLaw ι).map ((U : Matrix ι ι ℂ).mulVec) = complexGaussianSphereLaw ι := by
  have hU := measurePreserving_standardComplexGaussianColumn_unitary U
  have hcomm : (U : Matrix ι ι ℂ).mulVec ∘ normalizedComplexDirection =
      normalizedComplexDirection ∘ (U : Matrix ι ι ℂ).mulVec := by
    funext v
    change (U : Matrix ι ι ℂ) *ᵥ ((((√(complexDirectionEnergy v))⁻¹ : ℝ) : ℂ) • v) =
      (((√(complexDirectionEnergy ((U : Matrix ι ι ℂ) *ᵥ v)))⁻¹ : ℝ) : ℂ) •
        ((U : Matrix ι ι ℂ) *ᵥ v)
    rw [complexDirectionEnergy_unitary, Matrix.mulVec_smul]
  unfold complexGaussianSphereLaw
  rw [Measure.map_map hU.measurable measurable_normalizedComplexDirection, hcomm,
    ← Measure.map_map measurable_normalizedComplexDirection hU.measurable, hU.map_eq]

/-- The finite complex matrix unitary group is compact in the
entrywise topology. -/
theorem isCompact_complexUnitaryGroup (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsCompact (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  have hp : IsCompact {U : Matrix ι ι ℂ | ∀ i j, U i j ∈ Metric.closedBall (0 : ℂ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ =>
      isCompact_closedBall (0 : ℂ) 1
  apply hp.of_isClosed_subset isClosed_unitary
  intro U hU i j
  have hcol : ∑ i', Complex.normSq (U i' j) = 1 := by
    have hup : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
    have h := congrArg (fun M : Matrix ι ι ℂ => (M j j).re) hup
    simpa [Matrix.mul_apply, Matrix.star_apply, Complex.normSq_apply, pow_two] using h
  have hsq : ‖U i j‖^2 ≤ 1 := by
    rw [Complex.sq_norm, ← hcol]
    exact Finset.single_le_sum (fun i' _ => Complex.normSq_nonneg (U i' j)) (Finset.mem_univ i)
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg (U i j)]

theorem complexUnitaryOrbit_contains_unitVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (v : ι → ℂ) (hv : complexDirectionEnergy v = 1) :
    ∃ U : Matrix.unitaryGroup ι ℂ, (U : Matrix ι ι ℂ) *ᵥ Pi.single i₀ 1 = v := by
  let x : EuclideanSpace ℂ ι := toLp 2 v
  have hnorm : ‖x‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg x) zero_le_one).mp
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖v i‖^2) = (1 : ℝ)^2
    simp only [Complex.sq_norm, one_pow]
    exact hv
  have ho : Orthonormal ℂ (({i₀} : Set ι).domRestrict (fun _ : ι => x)) :=
    orthonormal_subsingleton_iff.mpr (fun _ => hnorm)
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace ho
  let a := EuclideanSpace.basisFun ι ℂ
  use ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b⟩
  change (a.toBasis.toMatrix b) *ᵥ Pi.single i₀ 1 = v
  rw [Matrix.mulVec_single_one]
  funext i
  change a.toBasis.repr (b i₀) i = v i
  rw [hb i₀ (mem_singleton i₀)]
  rfl

def allComplexUnitaries (ι : Type*) [Fintype ι] [DecidableEq ι] :
    TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup ι ℂ) := by
  let : CompactSpace (Matrix.unitaryGroup ι ℂ) :=
    isCompact_iff_compactSpace.mp (isCompact_complexUnitaryGroup ι)
  exact ⟨⟨univ, isCompact_univ⟩, by simp⟩

/-- Right Haar probability on the finite complex matrix unitary group. -/
def complexUnitaryHaarProbability (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Measure (Matrix.unitaryGroup ι ℂ) :=
  (Measure.haarMeasure (allComplexUnitaries ι)).inv

instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsProbabilityMeasure (complexUnitaryHaarProbability ι) := by
  have : IsProbabilityMeasure (Measure.haarMeasure (allComplexUnitaries ι)) :=
    ⟨Measure.haarMeasure_self⟩
  unfold complexUnitaryHaarProbability Measure.inv
  infer_instance

instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (complexUnitaryHaarProbability ι).IsMulRightInvariant := by
  unfold complexUnitaryHaarProbability
  infer_instance

private abbrev ComplexUnitSphere (ι : Type*) [Fintype ι] :=
  {v : ι → ℂ // complexDirectionEnergy v = 1}

private instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    MulAction (Matrix.unitaryGroup ι ℂ) (ComplexUnitSphere ι) where
  smul U v := ⟨(U : Matrix ι ι ℂ) *ᵥ v.val, (complexDirectionEnergy_unitary U v.val).trans v.property⟩
  one_smul v := Subtype.ext (Matrix.one_mulVec v.val)
  mul_smul U V v := Subtype.ext (Matrix.mulVec_mulVec v.val (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)).symm

private theorem measurable_unitary_mulVec_action {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun p : (Matrix.unitaryGroup ι ℂ) × (ι → ℂ) =>
      (p.1 : Matrix ι ι ℂ) *ᵥ p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun p : (Matrix.unitaryGroup ι ℂ) × (ι → ℂ) =>
    ∑ j, (p.1 : Matrix ι ι ℂ) i j * p.2 j)
  have h (j : ι) : Measurable (fun p : (Matrix.unitaryGroup ι ℂ) × (ι → ℂ) =>
      (p.1 : Matrix ι ι ℂ) i j) := by
    have hm : Measurable (fun M : Matrix ι ι ℂ => M i j) :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    exact hm.comp ((measurable_subtype_coe : Measurable
      ((↑) : Matrix.unitaryGroup ι ℂ → Matrix ι ι ℂ)).comp measurable_fst)
  have h' (j : ι) : Measurable (fun p : (Matrix.unitaryGroup ι ℂ) × (ι → ℂ) => p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact Finset.measurable_sum _ (fun j _ => (h j).mul (h' j))

/-- Any unitary-invariant Borel probability carried by the unit sphere
equals the Haar orbit of a coordinate unit vector. -/
theorem unitaryInvariantSphereProbability_eq_HaarOrbit
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    (μ : Measure (ι → ℂ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, complexDirectionEnergy v = 1)
    (hinv : ∀ U : Matrix.unitaryGroup ι ℂ, μ.map ((U : Matrix ι ι ℂ).mulVec) = μ) :
    μ = (complexUnitaryHaarProbability ι).map (fun U : Matrix.unitaryGroup ι ℂ =>
      (U : Matrix ι ι ℂ) *ᵥ Pi.single i₀ 1) := by
  let u₀ : ComplexUnitSphere ι := ⟨Pi.single i₀ 1, by
    simp [complexDirectionEnergy, Pi.single_apply]⟩
  let val : ComplexUnitSphere ι → ι → ℂ := Subtype.val
  let μA := μ.comap val
  have hset : MeasurableSet {v : ι → ℂ | complexDirectionEnergy v = 1} :=
    measurableSet_eq_fun measurable_complexDirectionEnergy measurable_const
  have hv : MeasurableEmbedding val := MeasurableEmbedding.subtype_coe hset
  have hmap : μA.map val = μ :=
    (map_comap_subtype_coe hset μ).trans (Measure.restrict_eq_self_of_ae_mem hμ)
  have : IsProbabilityMeasure μA :=
    (Measure.isProbabilityMeasure_map_iff hv.measurable.aemeasurable).mp (hmap ▸ ‹IsProbabilityMeasure μ›)
  have hm := measurable_unitary_mulVec_action (ι := ι)
  have hmA : Measurable (fun p : (Matrix.unitaryGroup ι ℂ) × ComplexUnitSphere ι =>
      p.1 • p.2) := by
    have hA : Measurable (fun p : (Matrix.unitaryGroup ι ℂ) × ComplexUnitSphere ι =>
        (p.1 : Matrix ι ι ℂ) *ᵥ p.2.val) :=
      hm.comp (measurable_fst.prodMk (hv.measurable.comp measurable_snd))
    change Measurable (fun p : (Matrix.unitaryGroup ι ℂ) × ComplexUnitSphere ι =>
      (⟨(p.1 : Matrix ι ι ℂ) *ᵥ p.2.val, (complexDirectionEnergy_unitary p.1 p.2.val).trans
        p.2.property⟩ : ComplexUnitSphere ι))
    exact hA.subtype_mk
  have ht (v : ComplexUnitSphere ι) : ∃ U : Matrix.unitaryGroup ι ℂ, U • u₀ = v := by
    obtain ⟨U, hU⟩ := complexUnitaryOrbit_contains_unitVector i₀ v.val v.property
    exact ⟨U, Subtype.ext hU⟩
  have hI (U : Matrix.unitaryGroup ι ℂ) : MeasurePreserving (fun v : ComplexUnitSphere ι => U • v) μA μA := by
    have hA : Measurable (fun v : ComplexUnitSphere ι => U • v) :=
      hmA.comp measurable_prodMk_left
    have hV : Measurable (fun v : ι → ℂ => (U : Matrix ι ι ℂ) *ᵥ v) :=
      hm.comp measurable_prodMk_left
    refine ⟨hA, hv.map_injective ?_⟩
    rw [Measure.map_map hv.measurable hA]
    change μA.map ((fun v : ι → ℂ => (U : Matrix ι ι ℂ) *ᵥ v) ∘ val) = _
    rw [← Measure.map_map hV hv.measurable, hmap, hinv U]
  have he := invariantProbability_eq_orbitMap hmA u₀ ht (complexUnitaryHaarProbability ι) μA hI
  have horbit : Measurable (fun U : Matrix.unitaryGroup ι ℂ => U • u₀) :=
    hmA.comp measurable_prodMk_right
  rw [← hmap, he, Measure.map_map hv.measurable horbit]
  rfl

/-- The Gaussian direction is the uniform pure-state vector obtained
by Haar action on a coordinate unit vector. -/
theorem complexGaussianSphereLaw_eq_HaarOrbit
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) :
    complexGaussianSphereLaw ι = (complexUnitaryHaarProbability ι).map
      (fun U : Matrix.unitaryGroup ι ℂ => (U : Matrix ι ι ℂ) *ᵥ Pi.single i₀ 1) := by
  have : Nonempty ι := ⟨i₀⟩
  exact unitaryInvariantSphereProbability_eq_HaarOrbit i₀ _ ae_complexGaussianSphereLaw_unit
    map_unitary_complexGaussianSphereLaw

private theorem measurePreserving_gaussianMatrixVectorization (k : ℕ) :
    MeasurePreserving (fun Z : Matrix (Fin 3) (Fin k) ℂ => fun p : Fin 3 × Fin k => Z p.1 p.2)
      (standardComplexGaussianMatrix k) (Measure.pi fun _ : Fin 3 × Fin k => standardComplexGaussian) := by
  let vec := fun Z : Matrix (Fin 3) (Fin k) ℂ => fun p : Fin 3 × Fin k => Z p.1 p.2
  have hm : Measurable vec := by
    apply measurable_pi_iff.mpr
    intro p
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hm, (Measure.pi_eq (μ := fun _ : Fin 3 × Fin k => standardComplexGaussian)
    (fun s hs => ?_)).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hset : vec ⁻¹' (univ.pi s) = univ.pi (fun i : Fin 3 => univ.pi (fun j : Fin k => s (i,j))) := by
    ext Z
    constructor
    · intro hz
      apply Set.mem_pi.mpr
      intro i _
      apply Set.mem_pi.mpr
      intro j _
      exact Set.mem_pi.mp hz (i,j) (mem_univ _)
    · intro hz
      apply Set.mem_pi.mpr
      intro p _
      exact Set.mem_pi.mp (Set.mem_pi.mp hz p.1 (mem_univ _)) p.2 (mem_univ _)
  rw [hset]
  change (Measure.pi fun _ : Fin 3 => Measure.pi fun _ : Fin k => standardComplexGaussian)
    (univ.pi (fun i : Fin 3 => univ.pi (fun j : Fin k => s (i,j)))) = _
  rw [Measure.pi_pi, ← Finset.univ_product_univ, Finset.prod_product]
  simp_rw [Measure.pi_pi]

/-- The exact Gaussian induced law is the partial trace pushforward of
its isotropic Gaussian direction on the product-basis unit sphere. -/
theorem inducedComplexStateLaw_eq_partialTrace_gaussianDirection (k : ℕ) :
    inducedComplexStateLaw k = (complexGaussianSphereLaw (Fin 3 × Fin k)).map
      (partialTraceComplexPureVector k) := by
  let vec := fun Z : Matrix (Fin 3) (Fin k) ℂ => fun p : Fin 3 × Fin k => Z p.1 p.2
  have hm := measurePreserving_gaussianMatrixVectorization k
  have hp : Measurable (partialTraceComplexPureVector k) := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun u : Fin 3 × Fin k → ℂ => ∑ a, u (i, a) * star (u (j, a)))
    fun_prop
  have hn (Z : Matrix (Fin 3) (Fin k) ℂ) :
      normalizedComplexDirection (vec Z) = normalizedComplexPureVector k Z := by
    have hn' : complexDirectionEnergy (vec Z) = complexMatrixEnergy Z := by
      unfold complexDirectionEnergy complexMatrixEnergy
      rw [Fintype.sum_prod_type]
    funext p
    change (((√(complexDirectionEnergy (vec Z)))⁻¹ : ℝ) : ℂ) * Z p.1 p.2 =
      (((√(complexMatrixEnergy Z))⁻¹ : ℝ) : ℂ) * Z p.1 p.2
    rw [hn']
  have he : partialTraceComplexPureVector k ∘ (normalizedComplexDirection ∘ vec) =
      normalizedComplexGram k := by
    funext Z
    exact (congrArg (partialTraceComplexPureVector k) (hn Z)).trans
      (partialTrace_normalizedComplexPureVector Z)
  unfold inducedComplexStateLaw normalizedGramPushforward complexGaussianSphereLaw
  change _ = ((Measure.pi fun _ : Fin 3 × Fin k => standardComplexGaussian).map
    normalizedComplexDirection).map (partialTraceComplexPureVector k)
  rw [← hm.map_eq, Measure.map_map measurable_normalizedComplexDirection hm.measurable,
    Measure.map_map hp (measurable_normalizedComplexDirection.comp hm.measurable), he]

/-- The companion's induced state law is the partial trace of a
Haar-uniform pure state on the tensor product, in the canonical product basis. -/
theorem inducedComplexStateLaw_eq_partialTrace_Haar (k : ℕ) (hk : 0 < k) :
    inducedComplexStateLaw k =
      ((complexUnitaryHaarProbability (Fin 3 × Fin k)).map
        (fun U : Matrix.unitaryGroup (Fin 3 × Fin k) ℂ =>
          (U : Matrix (Fin 3 × Fin k) (Fin 3 × Fin k) ℂ) *ᵥ Pi.single (0, ⟨0, hk⟩) 1)).map
        (partialTraceComplexPureVector k) := by
  rw [inducedComplexStateLaw_eq_partialTrace_gaussianDirection,
    complexGaussianSphereLaw_eq_HaarOrbit (0, (⟨0, hk⟩ : Fin k))]

end AlbertSequential.WindowProbability
