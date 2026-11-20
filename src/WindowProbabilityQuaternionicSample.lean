/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityPureState
public import WindowProbabilityTransport
public import BlockA.GlennieDefect

/-! The actual two-complex-coordinate coupling for a quaternionic
rank-one sample on the standard associative window. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory
open scoped AlbertSequential.WindowProbability Matrix ComplexOrder

/-- Ordinary quaternion with complex coordinates `z + w j`. -/
def quaternionOfComplexPair (z w : ℂ) : Quaternion ℝ :=
  ⟨z.re, z.im, w.re, w.im⟩

theorem quaternionOfComplexPair_product_complexPart (z w z' w' : ℂ) :
    (⟨(quaternionOfComplexPair z w * star (quaternionOfComplexPair z' w')).re,
      (quaternionOfComplexPair z w * star (quaternionOfComplexPair z' w')).imI⟩ : ℂ) =
      z * star z' + w * star w' := by
  apply Complex.ext <;>
    simp [quaternionOfComplexPair, Complex.mul_re, Complex.mul_im] <;> ring

/-- The literal quaternionic dyad built from two columns of complex
Gaussian coordinates in the standard quaternionic embedding. -/
def quaternionicDyadFromTwoColumns (Z : Matrix (Fin 3) (Fin 2) ℂ) : Albert :=
  quatDyad quatEmbed1 (fun i => quaternionOfComplexPair (Z i 0) (Z i 1)) 1

/-- Orthogonal projection onto the standard complex window takes the
native quaternionic dyad to the exact unnormalized two-column Gram matrix. -/
theorem projectedMatrix_quaternionicDyadFromTwoColumns (Z : Matrix (Fin 3) (Fin 2) ℂ) :
    projectedMatrix standardComplexWindow (quaternionicDyadFromTwoColumns Z) = Z * Z.conjTranspose := by
  let G : Hermitian3 := ⟨Z * Z.conjTranspose, Matrix.isHermitian_mul_conjTranspose_self Z⟩
  have hG (i j : Fin 3) :
      (G : ComplexMatrix3) i j =
        (⟨(quaternionOfComplexPair (Z i 0) (Z i 1) * star (quaternionOfComplexPair (Z j 0) (Z j 1))).re,
          (quaternionOfComplexPair (Z i 0) (Z i 1) * star (quaternionOfComplexPair (Z j 0) (Z j 1))).imI⟩ : ℂ) := by
    rw [quaternionOfComplexPair_product_complexPart]
    simp [G, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  change (windowProj standardComplexWindow (quaternionicDyadFromTwoColumns Z) : ComplexMatrix3) =
    (G : ComplexMatrix3)
  apply congrArg (fun M : Hermitian3 => (M : ComplexMatrix3))
  apply standardComplexWindow.injective
  rw [AppF.standardComplexWindow_embedding_windowProj, standardComplexWindow_apply]
  apply Prod.ext
  · funext i
    rw [quaternionicDyadFromTwoColumns, quatDyad, one_div, inv_one, one_smul]
    change _ = ((G : ComplexMatrix3) i i).re
    rw [hG]
  · funext i
    rw [quaternionicDyadFromTwoColumns, quatDyad, one_div, inv_one, one_smul]
    fin_cases i <;>
      simp [complexHermToAlbert, hG, AppF.projC, quatEmbed1_apply, complexToOctonion_apply] <;> rfl

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

theorem measurable_quaternionicDyadFromTwoColumns :
    Measurable quaternionicDyadFromTwoColumns := by
  have hpair : Continuous (fun p : ℂ × ℂ => quaternionOfComplexPair p.1 p.2) := by
    let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm
    change Continuous (fun p : ℂ × ℂ => e ![p.1.re, p.1.im, p.2.re, p.2.im])
    exact e.toLinearMap.continuous_of_finiteDimensional.comp (by fun_prop)
  let u : (Fin 3 → Fin 2 → ℂ) → Fin 3 → Quaternion ℝ :=
    fun Z i => quaternionOfComplexPair (Z i 0) (Z i 1)
  have h (i : Fin 3) : Continuous (fun Z => u Z i) := by
    have hi : Continuous (fun Z : Fin 3 → Fin 2 → ℂ => Z i) := continuous_apply i
    have hcols : Continuous (fun Z : Fin 3 → Fin 2 → ℂ => (Z i 0, Z i 1)) :=
      ((continuous_apply 0).comp hi).prodMk ((continuous_apply 1).comp hi)
    exact hpair.comp hcols
  apply Continuous.measurable
  let raw : (Fin 3 → Fin 2 → ℂ) → Albert := fun Z =>
    (fun i => (u Z i * star (u Z i)).re,
      ![quatEmbed1 (u Z 0 * star (u Z 1)), quatEmbed1 (u Z 0 * star (u Z 2)),
        quatEmbed1 (u Z 1 * star (u Z 2))])
  have he (Z : Matrix (Fin 3) (Fin 2) ℂ) : quaternionicDyadFromTwoColumns Z = raw Z := by
    change (1 / 1 : ℝ) • raw Z = raw Z
    rw [div_one, one_smul]
  rw [show quaternionicDyadFromTwoColumns = raw from funext he]
  unfold raw
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact Quaternion.continuous_re.comp ((h i).mul ((h i).star))
  · apply continuous_pi
    intro i
    fin_cases i <;>
      exact quatEmbed1.continuous_of_finiteDimensional.comp ((h _).mul ((h _).star))

/-- Probability on normalized native quaternionic dyads produced by
the exact two-column complex Gaussian matrix. -/
def quaternionicTwoColumnSampleLaw : Measure Albert :=
  (standardComplexGaussianMatrix 2).map (normalizeAlbert ∘ quaternionicDyadFromTwoColumns)

instance : IsProbabilityMeasure quaternionicTwoColumnSampleLaw := by
  unfold quaternionicTwoColumnSampleLaw
  infer_instance

/-- The actual quaternionic sample probability projects to the exact
two-column induced complex law on the standard complex window. -/
theorem projectedMatrix_quaternionicTwoColumnSampleLaw :
    quaternionicTwoColumnSampleLaw.map (projectedMatrix standardComplexWindow) =
      inducedComplexStateLaw 2 := by
  unfold quaternionicTwoColumnSampleLaw inducedComplexStateLaw normalizedGramPushforward
  rw [Measure.map_map (measurable_projectedMatrix _) (measurable_normalizeAlbert.comp
    measurable_quaternionicDyadFromTwoColumns)]
  congr 1
  funext Z
  change projectedMatrix standardComplexWindow (normalizeAlbert (quaternionicDyadFromTwoColumns Z)) =
    normalizedComplexGram 2 Z
  rw [projectedMatrix_normalizeAlbert, projectedMatrix_quaternionicDyadFromTwoColumns]
  rfl

/-- The coupled quaternionic samples are genuine native atoms almost
surely after normalizing their trace. -/
theorem ae_quaternionicTwoColumnSampleLaw_isAtom :
    ∀ᵐ p ∂quaternionicTwoColumnSampleLaw, IsAtom p := by
  unfold quaternionicTwoColumnSampleLaw
  rw [ae_map_iff (measurable_normalizeAlbert.comp measurable_quaternionicDyadFromTwoColumns).aemeasurable
    measurableSet_atomSet]
  filter_upwards [ae_gaussianMatrix_ne_zero 2 (by decide)] with Z hZ
  let u := fun i : Fin 3 => quaternionOfComplexPair (Z i 0) (Z i 1)
  have hn : ∑ i, quatNormSq (u i) = complexMatrixEnergy Z := by
    unfold complexMatrixEnergy
    apply Finset.sum_congr rfl
    intro i _
    simp [u, quatNormSq, quaternionOfComplexPair, Fin.sum_univ_two, Complex.normSq_apply]
    ring
  have hT : albertTrace (quaternionicDyadFromTwoColumns Z) = complexMatrixEnergy Z := by
    apply Complex.ofReal_injective
    rw [← trace_projectedMatrix standardComplexWindow,
      projectedMatrix_quaternionicDyadFromTwoColumns, trace_complexGaussianGram_eq_energy]
  have hN : complexMatrixEnergy Z ≠ 0 := by
    intro hzero
    apply hZ
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    rw [trace_complexGaussianGram_eq_energy, hzero, Complex.ofReal_zero]
  change IsAtom (normalizeAlbert (quaternionicDyadFromTwoColumns Z))
  have he : normalizeAlbert (quaternionicDyadFromTwoColumns Z) =
      quatDyad quatEmbed1 u (complexMatrixEnergy Z) := by
    unfold normalizeAlbert
    rw [hT]
    unfold quaternionicDyadFromTwoColumns quatDyad
    simp only [one_div, inv_one, one_smul]
    rfl
  rw [he]
  exact quatDyad_isAtom quatEmbed1 quatEmbed1_isQuatEmbedding u _ hN hn

theorem normalizedQuaternionicDyadFromTwoColumns_mem
    (Z : Matrix (Fin 3) (Fin 2) ℂ) :
    normalizeAlbert (quaternionicDyadFromTwoColumns Z) ∈
      standardQuaternionicWindow.subalgebra.carrier := by
  let u := fun i : Fin 3 => quaternionOfComplexPair (Z i 0) (Z i 1)
  let A : QuatMatrix3 := fun i j => u i * star (u j)
  let H : QuatHermitian3 := ⟨A, by
    apply Matrix.ext
    intro i j
    change star (u j * star (u i)) = _
    rw [star_mul, star_star]⟩
  have h : quaternionicDyadFromTwoColumns Z ∈ standardQuaternionicWindow.subalgebra.carrier := by
    change quaternionicDyadFromTwoColumns Z ∈ LinearMap.range standardQuaternionicWindow.embedding
    refine ⟨H, ?_⟩
    rw [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding_apply]
    unfold quaternionicDyadFromTwoColumns quatDyad
    rw [one_div, inv_one, one_smul]
    rfl
  unfold normalizeAlbert
  exact standardQuaternionicWindow.subalgebra.carrier.smul_mem _ h

end AlbertSequential.WindowProbability
