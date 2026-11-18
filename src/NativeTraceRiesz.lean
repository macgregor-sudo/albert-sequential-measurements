module

public import NativeSquareCone
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! Exact real trace-Riesz representation on the current compact native model.
The proof representation has its existing recovered Hilbert structure, while
no norm is exported on the sealed current native carriers. Positivity below
tests every actual native square. -/

@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace AlbertSequential.NativeAnalysis

def tracePairingFunctional (ρ : Albert) : Albert →ₗ[ℝ] ℝ where
  toFun := tracePairing ρ
  map_add' := tracePairing_add_right ρ
  map_smul' r x := tracePairing_smul_right r ρ x

@[simp] theorem tracePairingFunctional_apply (ρ x : Albert) :
    tracePairingFunctional ρ x = tracePairing ρ x := rfl

/-- The transported functional on the separate finite real Hilbert carrier. -/
def recoveredFunctional (φ : Albert →ₗ[ℝ] ℝ) : Glennie.Albert →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (φ.comp recoveredCoordinateEquiv.symm.toLinearMap)

def traceRepresentative (φ : Albert →ₗ[ℝ] ℝ) : Albert :=
  recoveredCoordinateEquiv.symm
    ((InnerProductSpace.toDual ℝ Glennie.Albert).symm (recoveredFunctional φ))

theorem traceRepresentative_pairing (φ : Albert →ₗ[ℝ] ℝ) (x : Albert) :
    tracePairing (traceRepresentative φ) x = φ x := by
  rw [← recoveredCoordinateEquiv_tracePairing, traceRepresentative,
    LinearEquiv.apply_symm_apply]
  have hr := (InnerProductSpace.toDual_symm_apply
    (x := recoveredCoordinateEquiv x) (y := recoveredFunctional φ))
  change Glennie.inner
      ((InnerProductSpace.toDual ℝ Glennie.Albert).symm (recoveredFunctional φ))
      (recoveredCoordinateEquiv x) = φ x
  calc
    _ = recoveredFunctional φ (recoveredCoordinateEquiv x) := hr
    _ = φ x := by
      change φ (recoveredCoordinateEquiv.symm (recoveredCoordinateEquiv x)) = φ x
      rw [LinearEquiv.symm_apply_apply]

theorem traceRepresentative_unique (φ : Albert →ₗ[ℝ] ℝ) (ρ : Albert)
    (h : ∀ x, tracePairing ρ x = φ x) : ρ = traceRepresentative φ := by
  have hz : tracePairing (ρ - traceRepresentative φ) (ρ - traceRepresentative φ) = 0 := by
    rw [tracePairing_sub_left, h, traceRepresentative_pairing, sub_self]
  exact sub_eq_zero.mp ((tracePairing_self_eq_zero _).mp hz)

theorem traceRepresentative_positive_iff (φ : Albert →ₗ[ℝ] ℝ) :
    IsPositive (traceRepresentative φ) ↔ ∀ y, 0 ≤ φ (jordanMul y y) := by
  rw [isPositive_iff_dual_squares]
  simp only [traceRepresentative_pairing]

theorem traceRepresentative_trace (φ : Albert →ₗ[ℝ] ℝ) :
    albertTrace (traceRepresentative φ) = φ albertUnit := by
  rw [← tracePairing_unit_right, traceRepresentative_pairing]

theorem traceRepresentative_add (φ ψ : Albert →ₗ[ℝ] ℝ) :
    traceRepresentative (φ + ψ) = traceRepresentative φ + traceRepresentative ψ := by
  symm
  apply traceRepresentative_unique
  intro x
  rw [tracePairing_add_left, traceRepresentative_pairing, traceRepresentative_pairing]
  rfl

theorem traceRepresentative_smul (r : ℝ) (φ : Albert →ₗ[ℝ] ℝ) :
    traceRepresentative (r • φ) = r • traceRepresentative φ := by
  symm
  apply traceRepresentative_unique
  intro x
  rw [tracePairing_smul_left, traceRepresentative_pairing]
  rfl

def traceRepresentativeLinear : (Albert →ₗ[ℝ] ℝ) →ₗ[ℝ] Albert where
  toFun := traceRepresentative
  map_add' := traceRepresentative_add
  map_smul' := traceRepresentative_smul

theorem positiveFunctional_unit_zero (φ : Albert →ₗ[ℝ] ℝ)
    (hpos : ∀ y, 0 ≤ φ (jordanMul y y)) (hzero : φ albertUnit = 0) : φ = 0 := by
  have hp := (traceRepresentative_positive_iff φ).mpr hpos
  have ht : albertTrace (traceRepresentative φ) = 0 := by
    rw [traceRepresentative_trace, hzero]
  have hz := (isPositive_trace_eq_zero _ hp).mp ht
  ext x
  change φ x = 0
  rw [← traceRepresentative_pairing φ x, hz]
  unfold tracePairing
  rw [jordanMul_zero_left, albertTrace_zero]

theorem normalized_positiveFunctional_density (φ : Albert →ₗ[ℝ] ℝ)
    (hpos : ∀ y, 0 ≤ φ (jordanMul y y)) (hnorm : φ albertUnit = 1) :
    IsDensity (traceRepresentative φ) := by
  constructor
  · exact (traceRepresentative_positive_iff φ).mpr hpos
  · rw [← tracePairing_unit_right, traceRepresentative_pairing, hnorm]

theorem exists_unique_density_representative (φ : Albert →ₗ[ℝ] ℝ)
    (hpos : ∀ y, 0 ≤ φ (jordanMul y y)) (hnorm : φ albertUnit = 1) :
    ∃! ρ : Albert, IsDensity ρ ∧ ∀ x, tracePairing ρ x = φ x := by
  refine ⟨traceRepresentative φ, ⟨normalized_positiveFunctional_density φ hpos hnorm,
    traceRepresentative_pairing φ⟩, ?_⟩
  intro ρ hρ
  exact traceRepresentative_unique φ ρ hρ.2

theorem traceRepresentative_tracePairing (ρ : Albert) :
    traceRepresentative (tracePairingFunctional ρ) = ρ :=
  (traceRepresentative_unique _ _ (fun _ => rfl)).symm

end AlbertSequential.NativeAnalysis
