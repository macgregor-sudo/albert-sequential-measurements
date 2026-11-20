/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PaperFixedDimensionCompactness
public import ReducedSharpFrameCoordinates
public import ReducedSharpDilationChannels
public import ChoiCompletePositivity
import Mathlib.Tactic.Abel

/-! Block padding of stationary instruments with arbitrary finite outcome sets. -/
@[expose] public section
noncomputable section

namespace AlbertSequential
open Matrix
open scoped BigOperators

/-- Put the old Kraus operators on the occupied block. The chosen outcome also
acts by the identity channel on the unused block, as a separate Kraus operator. -/
def paddedInstrumentKraus {d D : ℕ} {B : Type*} [DecidableEq B]
    (V : Matrix (Fin D) (Fin d) ℂ) (fallback : B) (K : B → List (ComplexMatrix d))
    (a : B) : List (ComplexMatrix D) :=
  isometricLiftKraus (K a) V V ++ (if a = fallback then [1 - V * Vᴴ] else [])

/-- The two compressions in this formula discard cross-block coherences for every input. -/
theorem paddedInstrumentKraus_action {d D : ℕ} {B : Type*} [DecidableEq B]
    (V : Matrix (Fin D) (Fin d) ℂ) (fallback : B) (K : B → List (ComplexMatrix d))
    (a : B) (Z : ComplexMatrix D) :
    krausAction (paddedInstrumentKraus V fallback K a) Z =
      sharpFrameEmbed V (krausAction (K a) (Vᴴ * Z * V)) +
      (if a = fallback then (1 - V * Vᴴ) * Z * (1 - V * Vᴴ) else 0) := by
  rw [paddedInstrumentKraus, krausAction_append, isometricLiftKraus_action, sharpFrameEmbed]
  by_cases ha : a = fallback
  · simp [ha, krausAction]
  · simp [ha, krausAction]

theorem paddedInstrumentKraus_completelyPositive {d D : ℕ} {B : Type*} [DecidableEq B]
    (V : Matrix (Fin D) (Fin d) ℂ) (fallback : B) (K : B → List (ComplexMatrix d))
    (a : B) : IsCompletelyPositiveMatrixMap (krausAction (paddedInstrumentKraus V fallback K a)) :=
  krausAction_completelyPositive _

theorem paddedInstrumentKraus_normalized {d D : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (V : Matrix (Fin D) (Fin d) ℂ) (hV : Vᴴ * V = 1) (fallback : B)
    (K : B → List (ComplexMatrix d)) (hK : ∑ a, krausEffect (K a) = 1) :
    ∑ a, krausEffect (paddedInstrumentKraus V fallback K a) = 1 := by
  have he (a : B) : krausEffect (paddedInstrumentKraus V fallback K a) =
      V * krausEffect (K a) * Vᴴ + (if a = fallback then 1 - V * Vᴴ else 0) := by
    rw [paddedInstrumentKraus, krausEffect_append, isometricLiftKraus_effect _ _ _ hV]
    by_cases ha : a = fallback
    · simp [ha, krausEffect, isometry_range_complement_idempotent V hV]
    · simp [ha, krausEffect]
  simp only [he, Finset.sum_add_distrib, ← Matrix.sum_mul, ← Matrix.mul_sum, hK, Matrix.mul_one]
  simp

theorem paddedInstrumentKraus_action_on_occupied {d D : ℕ} {B : Type*} [DecidableEq B]
    (V : Matrix (Fin D) (Fin d) ℂ) (hV : Vᴴ * V = 1) (fallback : B)
    (K : B → List (ComplexMatrix d)) (a : B) (Y : ComplexMatrix d) :
    krausAction (paddedInstrumentKraus V fallback K a) (sharpFrameEmbed V Y) =
      sharpFrameEmbed V (krausAction (K a) Y) := by
  have hc : Vᴴ * sharpFrameEmbed V Y * V = Y := by
    calc
      _ = (Vᴴ * V) * Y * (Vᴴ * V) := by simp only [sharpFrameEmbed, Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  have hv0 : (1 - V * Vᴴ) * V = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]
  have hq0 : (1 - V * Vᴴ) * sharpFrameEmbed V Y * (1 - V * Vᴴ) = 0 := by
    calc
      _ = ((1 - V * Vᴴ) * V) * Y * Vᴴ * (1 - V * Vᴴ) := by
        simp only [sharpFrameEmbed, Matrix.mul_assoc]
      _ = _ := by simp [hv0]
  rw [paddedInstrumentKraus_action, hc, hq0, ite_self, add_zero]

theorem paddedStationaryWordState {d D : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, DecidableEq (A x)] (V : Matrix (Fin D) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (fallback : ∀ x, A x) (rho : P → ComplexMatrix d)
    (K : ∀ x, A x → List (ComplexMatrix d)) (p : P) (w : InstrumentWord A) :
    finiteKrausWordState (fun p => sharpFrameEmbed V (rho p))
      (fun x => paddedInstrumentKraus V (fallback x) (K x)) p w =
      sharpFrameEmbed V (finiteKrausWordState rho K p w) := by
  change w.foldl (fun Y a => krausAction (paddedInstrumentKraus V (fallback a.1) (K a.1) a.2) Y)
      (sharpFrameEmbed V (rho p)) = sharpFrameEmbed V
      (w.foldl (fun Y a => krausAction (K a.1 a.2) Y) (rho p))
  generalize rho p = Y
  induction w generalizing Y with
  | nil => rfl
  | cons a w ih =>
    simp only [List.foldl_cons, paddedInstrumentKraus_action_on_occupied V hV]
    exact ih _

theorem paddedStationaryWordProbability {d D : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, DecidableEq (A x)] (V : Matrix (Fin D) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (fallback : ∀ x, A x) (rho : P → ComplexMatrix d)
    (K : ∀ x, A x → List (ComplexMatrix d)) (p : P) (w : InstrumentWord A) :
    finiteKrausWordProbability (fun p => sharpFrameEmbed V (rho p))
      (fun x => paddedInstrumentKraus V (fallback x) (K x)) p w =
      finiteKrausWordProbability rho K p w := by
  simp only [finiteKrausWordProbability, paddedStationaryWordState V hV, sharpFrameEmbed_trace V hV]

/-- A single common occupied block works for every preparation and test label. -/
theorem HasStationaryKrausRealization.of_le_dim {d D : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)] {t : P → InstrumentWord A → ℝ}
    (h : HasStationaryKrausRealization d t) (hle : d ≤ D) :
    HasStationaryKrausRealization D t := by
  classical
  have e := Nat.add_sub_of_le hle
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin D) (Fin d) ℂ, Vᴴ * V = 1 := by
    rw [← e]
    exact ⟨optimalCornerInclusion d (D - d), optimalCornerInclusion_isometry d (D - d)⟩
  obtain ⟨rho, K, hrho, hK, ht⟩ := h
  let fallback (x : X) : A x := Classical.choice inferInstance
  refine ⟨fun p => sharpFrameEmbed V (rho p),
    fun x => paddedInstrumentKraus V (fallback x) (K x),
    fun p => sharpFrameEmbed_density V hV (hrho p),
    fun x => paddedInstrumentKraus_normalized V hV (fallback x) (K x) (hK x), fun p w => ?_⟩
  exact (paddedStationaryWordProbability V hV fallback rho K p w).trans (ht p w)

/-- The printed upper-bound form of the finite-menu compactness theorem. -/
theorem stationaryKraus_global_iff_local_finite_menus_dim_le (D : ℕ) (hD : 0 < D)
    {P X : Type*} {A : X → Type*} [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (t : P → InstrumentWord A → ℝ) :
    HasStationaryKrausRealization D t ↔
      ∀ (ps : Finset P) (xs : Finset X), ∃ d ≤ D,
        HasStationaryKrausRealization d
          (fun (p : {p // p ∈ ps}) (w : InstrumentWord (fun x : {x // x ∈ xs} => A x.val)) =>
            t p.val (includeMenuWord xs w)) := by
  rw [stationaryKraus_global_iff_local_finite_menus D hD t]
  constructor
  · exact fun h ps xs => ⟨D, le_rfl, h ps xs⟩
  · intro h ps xs
    obtain ⟨d, hd, hr⟩ := h ps xs
    exact hr.of_le_dim hd

end AlbertSequential
