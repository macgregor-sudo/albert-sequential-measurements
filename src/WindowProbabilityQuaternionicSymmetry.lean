/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityQuaternionicSample
public import WindowProbabilitySphere
public import SubalgebraCoordsAndLine

/-! The scalar-coordinate representation of quaternionic unitary samples. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory Set
open scoped Matrix ENNReal

scoped instance quaternionMeasurableSpace : MeasurableSpace (Quaternion ℝ) := borel _
scoped instance quaternionBorelSpace : BorelSpace (Quaternion ℝ) := ⟨rfl⟩

/-- The actual quaternionic unitary matrix acting on the six complex coordinates. -/
def symplecticQuaternionicUnitary (U : unitary QuatMatrix3) :
    Matrix.unitaryGroup (Fin 6) ℂ := by
  refine ⟨symplecticQuatMat6 U.val, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  rw [Matrix.star_eq_conjTranspose, ← symplecticQuatMat6_star, ← symplecticQuatMat6_mul,
    Unitary.coe_star_mul_self, symplecticQuatMat6_one]

/-- The first column of the quaternion scalar representation identifies
three quaternionic coordinates with six complex coordinates. -/
def symplecticQuaternionicVector (v : Fin 3 → Quaternion ℝ) : Fin 6 → ℂ :=
  fun r => quatMat2 (v (fin3ProdFin2Equiv6.symm r).1) (fin3ProdFin2Equiv6.symm r).2 0

theorem symplecticQuaternionicVector_injective : Function.Injective symplecticQuaternionicVector := by
  intro v w h
  funext i
  have h0 := congrFun h (fin3ProdFin2Equiv6 (i, 0))
  have h1 := congrFun h (fin3ProdFin2Equiv6 (i, 1))
  simp only [symplecticQuaternionicVector, Equiv.symm_apply_apply, quatMat2,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Quaternion.ext _ _ (congrArg Complex.re h0) (congrArg Complex.im h0)
    (neg_injective (congrArg Complex.re h1)) (congrArg Complex.im h1)

/-- The symplectic first-column coordinates intertwine literal matrix-vector multiplication. -/
theorem symplecticQuaternionicVector_mulVec (A : QuatMatrix3) (v : Fin 3 → Quaternion ℝ) :
    symplecticQuaternionicVector (A *ᵥ v) = symplecticQuatMat6 A *ᵥ symplecticQuaternionicVector v := by
  let M : QuatMatrix3 := fun i _ => v i
  let j₀ := fin3ProdFin2Equiv6 (0, 0)
  have hcol (B : QuatMatrix3) : (symplecticQuatMat6 B).col j₀ =
      symplecticQuaternionicVector (B.col 0) := by
    funext r
    simp [symplecticQuatMat6, symplecticQuaternionicVector, j₀, Matrix.col]
  have hM : M.col 0 = v := rfl
  have hAM : (A * M).col 0 = A *ᵥ v := by
    funext i
    rfl
  rw [← hAM, ← hcol, symplecticQuatMat6_mul, ← hM, ← hcol]
  rfl

/-- Norm equality in the literal symplectic coordinates. -/
theorem complexDirectionEnergy_symplecticQuaternionicVector (v : Fin 3 → Quaternion ℝ) :
    complexDirectionEnergy (symplecticQuaternionicVector v) = ∑ i, quatNormSq (v i) := by
  unfold complexDirectionEnergy symplecticQuaternionicVector
  rw [Fintype.sum_equiv fin3ProdFin2Equiv6.symm _
    (fun p : Fin 3 × Fin 2 => Complex.normSq (quatMat2 (v p.1) p.2 0)) (fun _ => rfl),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp [quatMat2, Complex.normSq_apply, quatNormSq]
  ring

theorem quatNormSq_sum_unitary_mulVec (U : unitary QuatMatrix3)
    (v : Fin 3 → Quaternion ℝ) :
    (∑ i, quatNormSq ((U.val *ᵥ v) i)) = ∑ i, quatNormSq (v i) := by
  rw [← complexDirectionEnergy_symplecticQuaternionicVector, symplecticQuaternionicVector_mulVec,
    ← complexDirectionEnergy_symplecticQuaternionicVector]
  exact complexDirectionEnergy_unitary (symplecticQuaternionicUnitary U) _

def negativeConjugation : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)

private theorem measurePreserving_negativeConjugation :
    MeasurePreserving negativeConjugation standardComplexGaussian standardComplexGaussian := by
  let g := fun z : ℂ => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-Complex.normSq z))
  have hg : Measurable g := by dsimp [g]; fun_prop
  have h := negativeConjugation.measurePreserving
  refine ⟨h.measurable, ?_⟩
  rw [standardComplexGaussian_eq_withDensity]
  change (volume.withDensity g).map negativeConjugation = volume.withDensity g
  ext s hs
  rw [Measure.map_apply h.measurable hs, withDensity_apply _ (h.measurable hs),
    withDensity_apply _ hs]
  have he (z : ℂ) : g (negativeConjugation z) = g z := by
    unfold g
    rw [← Complex.sq_norm, negativeConjugation.norm_map, Complex.sq_norm]
  calc
    _ = ∫⁻ z in negativeConjugation ⁻¹' s, g (negativeConjugation z) :=
      setLIntegral_congr_fun (h.measurable hs) (fun z _ => (he z).symm)
    _ = _ := by rw [← setLIntegral_map hs hg h.measurable, h.map_eq]

def flattenQuaternionicInput : Matrix (Fin 3) (Fin 2) ℂ ≃ᵐ (Fin 3 × Fin 2 → ℂ) where
  toFun z p := z p.1 p.2
  invFun w i j := w (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  measurable_invFun := measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => measurable_pi_apply (i, j)

private theorem measurePreserving_flattenQuaternionicInput :
    MeasurePreserving flattenQuaternionicInput (standardComplexGaussianMatrix 2)
      (Measure.pi fun _ => standardComplexGaussian) := by
  refine ⟨flattenQuaternionicInput.measurable, (Measure.pi_eq
    (μ := fun _ : Fin 3 × Fin 2 => standardComplexGaussian) (fun s hs => ?_)).symm⟩
  rw [Measure.map_apply flattenQuaternionicInput.measurable (MeasurableSet.univ_pi hs)]
  have hset : flattenQuaternionicInput ⁻¹' univ.pi s =
      univ.pi (fun i : Fin 3 => univ.pi (fun j : Fin 2 => s (i,j))) := by
    ext x
    constructor
    · intro hx
      apply Set.mem_pi.mpr
      intro i _
      apply Set.mem_pi.mpr
      intro j _
      exact Set.mem_pi.mp hx (i, j) (mem_univ _)
    · intro hx
      apply Set.mem_pi.mpr
      intro p _
      exact Set.mem_pi.mp (Set.mem_pi.mp hx p.1 (mem_univ _)) p.2 (mem_univ _)
  rw [hset]
  change (Measure.pi fun _ : Fin 3 => Measure.pi fun _ : Fin 2 => standardComplexGaussian)
    (univ.pi (fun i : Fin 3 => univ.pi (fun j : Fin 2 => s (i,j)))) = _
  rw [Measure.pi_pi, ← Finset.univ_product_univ, Finset.prod_product]
  simp_rw [Measure.pi_pi]

def orientQuaternionicInput (p : Fin 3 × Fin 2) : ℂ ≃ᵐ ℂ :=
  if p.2 = 0 then MeasurableEquiv.refl ℂ else negativeConjugation.toHomeomorph.toMeasurableEquiv

/-- Gaussian samples are transported to the actual six complex symplectic coordinates. -/
def symplecticQuaternionicGaussianCoordinates : Matrix (Fin 3) (Fin 2) ℂ ≃ᵐ (Fin 6 → ℂ) :=
  MeasurableEquiv.trans
    (MeasurableEquiv.trans flattenQuaternionicInput (MeasurableEquiv.piCongrRight orientQuaternionicInput))
    (MeasurableEquiv.piCongrLeft (fun _ : Fin 6 => ℂ) fin3ProdFin2Equiv6)

private theorem symplecticQuaternionicGaussianCoordinates_apply (Z : Matrix (Fin 3) (Fin 2) ℂ) :
    symplecticQuaternionicGaussianCoordinates Z =
      symplecticQuaternionicVector (fun i => quaternionOfComplexPair (Z i 0) (Z i 1)) := by
  funext r
  obtain ⟨p, rfl⟩ := fin3ProdFin2Equiv6.surjective r
  obtain ⟨i, j⟩ := p
  rw [symplecticQuaternionicGaussianCoordinates, MeasurableEquiv.trans_apply,
    MeasurableEquiv.piCongrLeft_apply_apply]
  change orientQuaternionicInput (i, j) (Z i j) = _
  simp only [symplecticQuaternionicVector, Equiv.symm_apply_apply]
  fin_cases j <;>
    simp [orientQuaternionicInput, quaternionOfComplexPair, quatMat2, negativeConjugation]
  apply Complex.ext <;> simp

/-- Exact transport of the six independent standard complex Gaussian coordinates. -/
theorem measurePreserving_symplecticQuaternionicGaussianCoordinates :
    MeasurePreserving symplecticQuaternionicGaussianCoordinates (standardComplexGaussianMatrix 2)
      (Measure.pi fun _ : Fin 6 => standardComplexGaussian) := by
  have h (p : Fin 3 × Fin 2) : MeasurePreserving (orientQuaternionicInput p)
      standardComplexGaussian standardComplexGaussian := by
    unfold orientQuaternionicInput
    split
    · exact MeasurePreserving.id _
    · exact measurePreserving_negativeConjugation
  have hp := measurePreserving_pi (fun _ => standardComplexGaussian)
    (fun _ => standardComplexGaussian) h
  have hr := measurePreserving_piCongrLeft (fun _ : Fin 6 => standardComplexGaussian) fin3ProdFin2Equiv6
  exact hr.comp (hp.comp measurePreserving_flattenQuaternionicInput)

/-- The rotation of the raw two-column sample associated to a quaternionic unitary. -/
def rotateQuaternionicGaussianInput (U : unitary QuatMatrix3) :
    Matrix (Fin 3) (Fin 2) ℂ → Matrix (Fin 3) (Fin 2) ℂ :=
  symplecticQuaternionicGaussianCoordinates.symm ∘
    (symplecticQuaternionicUnitary U).val.mulVec ∘ symplecticQuaternionicGaussianCoordinates

/-- Quaternionic unitary rotation preserves the exact Gaussian input measure. -/
theorem measurePreserving_rotateQuaternionicGaussianInput (U : unitary QuatMatrix3) :
    MeasurePreserving (rotateQuaternionicGaussianInput U) (standardComplexGaussianMatrix 2)
      (standardComplexGaussianMatrix 2) := by
  have he := measurePreserving_symplecticQuaternionicGaussianCoordinates
  have hU := measurePreserving_standardComplexGaussianColumn_unitary (symplecticQuaternionicUnitary U)
  exact (he.symm symplecticQuaternionicGaussianCoordinates).comp (hU.comp he)

/-- After decoding the two complex columns, rotation is literal quaternionic multiplication. -/
theorem quaternionOfComplexPair_rotateQuaternionicGaussianInput (U : unitary QuatMatrix3)
    (Z : Matrix (Fin 3) (Fin 2) ℂ) :
    (fun i => quaternionOfComplexPair (rotateQuaternionicGaussianInput U Z i 0)
      (rotateQuaternionicGaussianInput U Z i 1)) =
      U.val *ᵥ (fun i => quaternionOfComplexPair (Z i 0) (Z i 1)) := by
  apply symplecticQuaternionicVector_injective
  rw [← symplecticQuaternionicGaussianCoordinates_apply, symplecticQuaternionicVector_mulVec,
    ← symplecticQuaternionicGaussianCoordinates_apply]
  unfold rotateQuaternionicGaussianInput
  simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
  rfl

/-- The literal normalized rank-one quaternionic matrix dyad. -/
def normalizedQuaternionicMatrixDyad (v : Fin 3 → Quaternion ℝ) : QuatMatrix3 :=
  (∑ i, quatNormSq (v i))⁻¹ • Matrix.vecMulVec v (star v)

/-- The decoded normalized Gaussian dyad intertwines quaternionic unitary conjugation. -/
theorem normalizedQuaternionicMatrixDyad_mulVec (U : unitary QuatMatrix3)
    (v : Fin 3 → Quaternion ℝ) :
    normalizedQuaternionicMatrixDyad (U.val *ᵥ v) =
      U.val * normalizedQuaternionicMatrixDyad v * star U.val := by
  unfold normalizedQuaternionicMatrixDyad
  rw [quatNormSq_sum_unitary_mulVec]
  have h : Matrix.vecMulVec (U.val *ᵥ v) (star (U.val *ᵥ v)) =
      U.val * Matrix.vecMulVec v (star v) * star U.val := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec, ← Matrix.star_eq_conjTranspose]
  rw [h]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The quaternionic matrix dyad agrees with the native Albert normalization. -/
theorem quatMatrixToAlbert_normalizedQuaternionicMatrixDyad
    (v : Fin 3 → Quaternion ℝ) :
    quatMatrixToAlbert quatEmbed1 (normalizedQuaternionicMatrixDyad v) =
      normalizeAlbert (quatDyad quatEmbed1 v 1) := by
  have hRe (i : Fin 3) : (v i * star (v i)).re = quatNormSq (v i) := by
    simp [quatNormSq]
    ring
  have hT : albertTrace (quatDyad quatEmbed1 v 1) = ∑ i, quatNormSq (v i) := by
    rw [quatDyad, div_one, one_smul]
    change (∑ i, (v i * star (v i)).re) = ∑ i, quatNormSq (v i)
    exact Finset.sum_congr rfl (fun i _ => hRe i)
  unfold normalizeAlbert
  rw [hT, quatDyad, div_one, one_smul]
  unfold quatMatrixToAlbert normalizedQuaternionicMatrixDyad
  apply Prod.ext
  · funext i
    rfl
  · funext i
    fin_cases i <;> apply quatEmbed1.map_smul

private theorem measurable_quaternionOfComplexPair :
    Measurable (fun p : ℂ × ℂ => quaternionOfComplexPair p.1 p.2) := by
  let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm
  have h : Continuous (fun p : ℂ × ℂ => quaternionOfComplexPair p.1 p.2) := by
    change Continuous (fun p : ℂ × ℂ => e ![p.1.re, p.1.im, p.2.re, p.2.im])
    exact e.toLinearMap.continuous_of_finiteDimensional.comp (by fun_prop)
  exact h.measurable

private theorem measurable_normalizedQuaternionicMatrixDyad :
    Measurable normalizedQuaternionicMatrixDyad := by
  have he : quatNormSq = (Quaternion.normSq : Quaternion ℝ → ℝ) := by
    funext q
    exact (Quaternion.normSq_def' (a := q)).symm
  have hNorm : Continuous quatNormSq := he ▸ Quaternion.continuous_normSq
  have hN : Measurable (fun v : Fin 3 → Quaternion ℝ => (∑ i, quatNormSq (v i))⁻¹) :=
    (Finset.measurable_fun_sum _ fun i _ => hNorm.measurable.comp (measurable_pi_apply i)).inv
  apply Measurable.of_eval_matrix
  intro i j
  have hs : Continuous (fun v : Fin 3 → Quaternion ℝ => v i * star (v j)) :=
    (continuous_apply i).mul (continuous_apply j).star
  change Measurable (fun v : Fin 3 → Quaternion ℝ => (∑ i, quatNormSq (v i))⁻¹ • (v i * star (v j)))
  exact hN.smul hs.measurable

theorem measurable_quaternionicMatrixDyadSample :
    Measurable (fun Z : Matrix (Fin 3) (Fin 2) ℂ => normalizedQuaternionicMatrixDyad
      (fun i => quaternionOfComplexPair (Z i 0) (Z i 1))) := by
  apply measurable_normalizedQuaternionicMatrixDyad.comp
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun Z : Matrix (Fin 3) (Fin 2) ℂ => quaternionOfComplexPair (Z i 0) (Z i 1))
  have hi : Measurable (fun Z : Fin 3 → Fin 2 → ℂ => Z i) := measurable_pi_apply i
  have hcols : Measurable (fun Z : Fin 3 → Fin 2 → ℂ => (Z i 0, Z i 1)) :=
    ((measurable_pi_apply 0).comp hi).prodMk ((measurable_pi_apply 1).comp hi)
  exact measurable_quaternionOfComplexPair.comp hcols

/-- Probability law of the actual normalized quaternionic matrix sample. -/
def quaternionicMatrixDyadSampleLaw : Measure QuatMatrix3 :=
  (standardComplexGaussianMatrix 2).map (fun Z => normalizedQuaternionicMatrixDyad
    (fun i => quaternionOfComplexPair (Z i 0) (Z i 1)))

instance : IsProbabilityMeasure quaternionicMatrixDyadSampleLaw :=
  (Measure.isProbabilityMeasure_map_iff measurable_quaternionicMatrixDyadSample.aemeasurable).2
    (inferInstance : IsProbabilityMeasure (standardComplexGaussianMatrix 2))

/-- The normalized quaternionic sample is invariant under each actual quaternionic unitary. -/
theorem map_quaternionicUnitary_quaternionicMatrixDyadSampleLaw (U : unitary QuatMatrix3) :
    quaternionicMatrixDyadSampleLaw.map (fun A : QuatMatrix3 => U.val * A * star U.val) =
      quaternionicMatrixDyadSampleLaw := by
  let f := fun Z : Matrix (Fin 3) (Fin 2) ℂ => normalizedQuaternionicMatrixDyad
    (fun i => quaternionOfComplexPair (Z i 0) (Z i 1))
  have hf : Measurable f := measurable_quaternionicMatrixDyadSample
  let A := fun M : QuatMatrix3 => U.val * M * star U.val
  have hA : Measurable A := by
    have h : Continuous A := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h.measurable
  have hcomm : A ∘ f = f ∘ rotateQuaternionicGaussianInput U := by
    funext Z
    change _ = normalizedQuaternionicMatrixDyad (fun i => quaternionOfComplexPair
      (rotateQuaternionicGaussianInput U Z i 0) (rotateQuaternionicGaussianInput U Z i 1))
    rw [quaternionOfComplexPair_rotateQuaternionicGaussianInput, normalizedQuaternionicMatrixDyad_mulVec]
    rfl
  have hU := measurePreserving_rotateQuaternionicGaussianInput U
  change ((standardComplexGaussianMatrix 2).map f).map A = (standardComplexGaussianMatrix 2).map f
  rw [Measure.map_map hA hf, hcomm, ← Measure.map_map hf hU.measurable, hU.map_eq]

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))

theorem measurable_quatMatrixToAlbert : Measurable (quatMatrixToAlbert quatEmbed1) := by
  have hev (i j : Fin 3) : Continuous (fun A : QuatMatrix3 => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  apply Continuous.measurable
  unfold quatMatrixToAlbert
  apply Continuous.prodMk
  · exact continuous_pi fun i => Quaternion.continuous_re.comp (hev i i)
  · apply continuous_pi
    intro i
    fin_cases i <;> exact quatEmbed1.continuous_of_finiteDimensional.comp (hev _ _)

/-- The matrix sampling probability has the exact native two-column probability as its pushforward. -/
theorem map_quatMatrixToAlbert_quaternionicMatrixDyadSampleLaw :
    quaternionicMatrixDyadSampleLaw.map (quatMatrixToAlbert quatEmbed1) = quaternionicTwoColumnSampleLaw := by
  unfold quaternionicMatrixDyadSampleLaw quaternionicTwoColumnSampleLaw
  rw [Measure.map_map measurable_quatMatrixToAlbert measurable_quaternionicMatrixDyadSample]
  congr 1
  funext Z
  exact quatMatrixToAlbert_normalizedQuaternionicMatrixDyad _

end AlbertSequential.WindowProbability
