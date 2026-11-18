module

public import NativeRecoveredCoordinates
public import Glennie.NativeSquareConeR01
public import Glennie.NativeQuadraticPositiveR01
public import Mathlib.Analysis.Convex.Basic

/-! Square-cone properties transported through the literal compact-coordinate
equivalence. The pruned recovered closure supplies actual diagonalization and
U-positivity; no spectral/cone proposition is added as an assumption. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem isPositive_iff_recovered (x : Albert) :
    IsPositive x ↔ Glennie.NativeSquareConeR01.Positive (recoveredCoordinateEquiv x) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨recoveredCoordinateEquiv y, ?_⟩
    rw [← recoveredCoordinateEquiv_jordanMul]
    exact congrArg recoveredCoordinateEquiv hy.symm
  · rintro ⟨y, hy⟩
    refine ⟨recoveredCoordinateEquiv.symm y, ?_⟩
    apply recoveredCoordinateEquiv.injective
    rw [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply]
    exact hy.symm

theorem isPositive_iff_dual_squares (x : Albert) :
    IsPositive x ↔ ∀ y : Albert, 0 ≤ tracePairing x (jordanMul y y) := by
  rw [isPositive_iff_recovered, Glennie.NativeSquareConeR01.positive_iff_dual_squares]
  constructor
  · intro h y
    have hy := h (recoveredCoordinateEquiv y)
    rwa [← recoveredCoordinateEquiv_jordanMul, recoveredCoordinateEquiv_tracePairing] at hy
  · intro h y
    obtain ⟨z, rfl⟩ := recoveredCoordinateEquiv.surjective y
    rw [← recoveredCoordinateEquiv_jordanMul, recoveredCoordinateEquiv_tracePairing]
    exact h z

theorem isPositive_square (x : Albert) : IsPositive (jordanMul x x) := ⟨x, rfl⟩

theorem isPositive_zero : IsPositive (0 : Albert) := by
  refine ⟨0, ?_⟩
  exact (jordanMul_zero_left 0).symm

theorem isPositive_idempotent (x : Albert) (hx : jordanMul x x = x) : IsPositive x :=
  ⟨x, hx.symm⟩

theorem isPositive_add (x y : Albert) (hx : IsPositive x) (hy : IsPositive y) :
    IsPositive (x + y) := by
  apply (isPositive_iff_recovered _).mpr
  rw [map_add]
  exact Glennie.NativeSquareConeR01.positive_add _ _
    ((isPositive_iff_recovered x).mp hx) ((isPositive_iff_recovered y).mp hy)

theorem isPositive_smul (r : ℝ) (x : Albert) (hr : 0 ≤ r) (hx : IsPositive x) :
    IsPositive (r • x) := by
  apply (isPositive_iff_recovered _).mpr
  rw [map_smul]
  exact Glennie.NativeSquareConeR01.positive_smul _ _ hr ((isPositive_iff_recovered x).mp hx)

theorem tracePairing_positive_nonnegative (x y : Albert)
    (hx : IsPositive x) (hy : IsPositive y) : 0 ≤ tracePairing x y := by
  obtain ⟨z, rfl⟩ := hy
  exact (isPositive_iff_dual_squares x).mp hx z

theorem isPositive_and_negative_eq_zero (x : Albert)
    (hx : IsPositive x) (hnx : IsPositive (-x)) : x = 0 := by
  have h := tracePairing_positive_nonnegative x (-x) hx hnx
  have hn : tracePairing x (-x) = -tracePairing x x := by
    have hs := tracePairing_smul_right (-1 : ℝ) x x
    simpa only [neg_one_smul, neg_one_mul] using hs
  rw [hn] at h
  exact (tracePairing_self_eq_zero x).mp (le_antisymm (by linarith) (tracePairing_self_nonneg x))

theorem isPositive_trace_nonnegative (x : Albert) (hx : IsPositive x) :
    0 ≤ albertTrace x := by
  obtain ⟨y, rfl⟩ := hx
  exact tracePairing_self_nonneg y

theorem albertTrace_zero : albertTrace (0 : Albert) = 0 := by
  have h := albertTrace_smul (0 : ℝ) (0 : Albert)
  simpa only [zero_smul, zero_mul] using h

theorem isPositive_trace_eq_zero (x : Albert) (hx : IsPositive x) :
    albertTrace x = 0 ↔ x = 0 := by
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := hx
    have hy : tracePairing y y = 0 := h
    rw [(tracePairing_self_eq_zero y).mp hy, jordanMul_zero_left]
  · rintro rfl
    exact albertTrace_zero

theorem isPositive_quadraticMap (a x : Albert) (hx : IsPositive x) :
    IsPositive (quadraticMap a x) := by
  apply (isPositive_iff_recovered _).mpr
  rw [recoveredCoordinateEquiv_quadraticMap]
  exact Glennie.NativeQuadraticPositiveR01.U_positive _ _ ((isPositive_iff_recovered x).mp hx)

theorem convex_positive_set : Convex ℝ {x : Albert | IsPositive x} := by
  intro x hx y hy a b ha hb _
  exact isPositive_add _ _ (isPositive_smul a x ha hx) (isPositive_smul b y hb hy)

theorem convex_density_set : Convex ℝ {ρ : Albert | IsDensity ρ} := by
  intro x hx y hy a b ha hb hab
  refine ⟨isPositive_add _ _ (isPositive_smul a x ha hx.1) (isPositive_smul b y hb hy.1), ?_⟩
  rw [albertTrace_add, albertTrace_smul, albertTrace_smul, hx.2, hy.2]
  simpa only [mul_one] using hab

end AlbertSequential.NativeAnalysis
