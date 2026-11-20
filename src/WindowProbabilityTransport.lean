/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ComplexWindowDeterminantAndMax
public import Interfaces.MeasuresAndRobustness
public import NativeDensityCompactness
public import NativeWordDuality

/-! Measurable projection and trace normalization for the exact native complex window.
These are the deterministic and measure-transport steps of companion Proposition 5.1. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.WindowProbability

open MeasureTheory
open NativeAnalysis

scoped instance : MeasurableSpace Albert := borel Albert
scoped instance : BorelSpace Albert := ⟨rfl⟩

local instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
local instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

/-- The atom locus in the native coordinate topology. -/
theorem isClosed_atomSet : IsClosed {x : Albert | IsAtom x} :=
  (isClosed_eq continuous_nativeSquare continuous_id).inter
    (isClosed_eq continuous_albertTrace continuous_const)

theorem isCompact_atomSet : IsCompact {x : Albert | IsAtom x} :=
  isCompact_density_set.of_isClosed_subset isClosed_atomSet fun x hx =>
    ⟨⟨x, hx.1.symm⟩, hx.2⟩

theorem measurableSet_atomSet : MeasurableSet {x : Albert | IsAtom x} :=
  isClosed_atomSet.measurableSet

/-- Matrix coordinates of `ψ ∘ P_W`, for an arbitrary native complex window. -/
def projectedMatrix (W : ComplexWindow) (x : Albert) : ComplexMatrix3 := windowProj W x

theorem continuous_projectedMatrix (W : ComplexWindow) : Continuous (projectedMatrix W) := by
  have hpair (y : Albert) : Continuous (fun x : Albert => tracePairing x y) := by
    have h : Continuous (fun x : Albert => (x, y)) :=
      (continuous_id : Continuous (id : Albert → Albert)).prodMk continuous_const
    exact (NativeAnalysis.continuous_tracePairing.comp h).congr (fun _ => rfl)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun x : Albert => mkHerm3Matrix
    (fun i => tracePairing x (W.embedding (hermE i)))
    (fun k => ⟨(1 / 2 : ℝ) * tracePairing x (W.embedding (hermRe k)),
      (1 / 2 : ℝ) * tracePairing x (W.embedding (hermIm k))⟩) i j)
  have hdiag (k : Fin 3) : Continuous (fun x : Albert =>
      (⟨tracePairing x (W.embedding (hermE k)), 0⟩ : ℂ)) :=
    Complex.continuous_ofReal.comp (hpair (W.embedding (hermE k)))
  have hoff (k : Fin 3) : Continuous (fun x : Albert =>
      (⟨(1/2 : ℝ) * tracePairing x (W.embedding (hermRe k)),
        (1/2 : ℝ) * tracePairing x (W.embedding (hermIm k))⟩ : ℂ)) := by
    let r := fun x : Albert => (1/2 : ℝ) * tracePairing x (W.embedding (hermRe k))
    let s := fun x : Albert => (1/2 : ℝ) * tracePairing x (W.embedding (hermIm k))
    have hr : Continuous r := continuous_const.mul (hpair (W.embedding (hermRe k)))
    have hs : Continuous s := continuous_const.mul (hpair (W.embedding (hermIm k)))
    exact ((Complex.continuous_ofReal.comp hr).add
      ((Complex.continuous_ofReal.comp hs).mul continuous_const)).congr
      (fun x => Complex.re_add_im (⟨r x, s x⟩ : ℂ))
  fin_cases i <;> fin_cases j <;> simp only [mkHerm3Matrix, Fin.isValue] <;>
    first | exact hdiag _ | exact hoff _ | exact continuous_star.comp (hoff _)

theorem measurable_projectedMatrix (W : ComplexWindow) : Measurable (projectedMatrix W) :=
  (continuous_projectedMatrix W).measurable

theorem trace_projectedMatrix (W : ComplexWindow) (x : Albert) :
    Matrix.trace (projectedMatrix W x) = (albertTrace x : ℂ) := by
  have hre := windowProj_tracePairing W x 1
  change (Matrix.trace (projectedMatrix W x * 1)).re = tracePairing x (W.embedding 1) at hre
  rw [mul_one, W.unit, tracePairing_unit_right] at hre
  apply Complex.ext
  · simpa using hre
  · have him (i : Fin 3) : ((projectedMatrix W x) i i).im = 0 := by
      have hstar := (windowProj W x).prop
      have h := congrArg (fun M : ComplexMatrix3 => (M i i).im) hstar
      simp only [Matrix.star_apply, Complex.star_def, Complex.conj_im] at h
      change -((projectedMatrix W x) i i).im = ((projectedMatrix W x) i i).im at h
      linarith
    simp [Matrix.trace, Matrix.diag, him]

/-- Normalization using the real native trace, extended by zero at trace zero. -/
def normalizeAlbert (x : Albert) : Albert := (albertTrace x)⁻¹ • x

/-- The trace normalization in the accompanying `normalizedComplexGram`. -/
def normalizeMatrix (M : ComplexMatrix3) : ComplexMatrix3 := (Matrix.trace M)⁻¹ • M

theorem measurable_normalizeAlbert : Measurable normalizeAlbert := by
  have h : Measurable albertTrace := continuous_albertTrace.measurable
  exact h.inv.smul measurable_id

theorem measurable_normalizeMatrix : Measurable normalizeMatrix := by
  unfold normalizeMatrix Matrix.trace Matrix.diag
  fun_prop

theorem projectedMatrix_normalizeAlbert (W : ComplexWindow) (x : Albert) :
    projectedMatrix W (normalizeAlbert x) = normalizeMatrix (projectedMatrix W x) := by
  unfold normalizeAlbert normalizeMatrix
  rw [trace_projectedMatrix]
  change ((windowProj W ((albertTrace x)⁻¹ • x)) : ComplexMatrix3) =
    ((albertTrace x : ℂ)⁻¹) • projectedMatrix W x
  rw [map_smul]
  ext i j
  simp [projectedMatrix, Matrix.smul_apply, Complex.real_smul]

theorem map_projectedMatrix_normalizeAlbert (W : ComplexWindow) (μ : Measure Albert) :
    (μ.map normalizeAlbert).map (projectedMatrix W) =
      (μ.map (projectedMatrix W)).map normalizeMatrix := by
  rw [Measure.map_map (measurable_projectedMatrix W) measurable_normalizeAlbert,
    Measure.map_map measurable_normalizeMatrix (measurable_projectedMatrix W)]
  have h : projectedMatrix W ∘ normalizeAlbert = normalizeMatrix ∘ projectedMatrix W :=
    funext (projectedMatrix_normalizeAlbert W)
  rw [h]

theorem projectedMatrix_atom_density (W : ComplexWindow) {p : Albert} (hp : IsAtom p) :
    IsComplexDensity3 (projectedMatrix W p) := windowProj_atom_isDensity W hp

theorem projectedMatrix_atom_rankOne_iff (W : ComplexWindow) {p : Albert} (hp : IsAtom p) :
    IsComplexRankOneProjection (projectedMatrix W p) ↔ W.Contains p :=
  windowProj_atom_rankOne_iff_contains W hp

end AlbertSequential.WindowProbability
