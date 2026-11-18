module

public import NativeMatrixTrace
public import NativeDensityCompactness

/-! Chronological native state/effect duality and continuity. These identities
hold for every native element and every menu, independently of atom or density
hypotheses; they do not establish that arbitrary words remain positive. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

local instance : IsTopologicalAddGroup Octonion :=
  inferInstanceAs (IsTopologicalAddGroup (Quaternion ℝ × Quaternion ℝ))
local instance : IsTopologicalAddGroup Albert :=
  inferInstanceAs (IsTopologicalAddGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

theorem nativeBranchState_cons {ι : Type*} (p : ι → Albert) (ρ : Albert)
    (a : Outcome ι) (w : Word ι) :
    nativeBranchState p ρ (a :: w) =
      nativeBranchState p (quadraticMap (nativeOutcome p a) ρ) w := rfl

theorem nativeBranchState_append {ι : Type*} (p : ι → Albert) (ρ : Albert)
    (u v : Word ι) :
    nativeBranchState p ρ (u ++ v) = nativeBranchState p (nativeBranchState p ρ u) v := by
  exact List.foldl_append

theorem tracePairing_unit_right (x : Albert) : tracePairing x albertUnit = albertTrace x := by
  unfold tracePairing
  rw [jordanMul_albertUnit_right]

/-- First outcome remains the outermost effect update, matching the chronological
state fold. No reversal or scalar traciality is used. -/
theorem nativeWordProbability_eq_pairing {ι : Type*} (p : ι → Albert) (ρ : Albert)
    (w : Word ι) :
    nativeWordProbability p ρ w = tracePairing ρ (nativeWordEffect p w) := by
  induction w generalizing ρ with
  | nil => exact (tracePairing_unit_right ρ).symm
  | cons a w ih =>
    change nativeWordProbability p (quadraticMap (nativeOutcome p a) ρ) w =
      tracePairing ρ (quadraticMap (nativeOutcome p a) (nativeWordEffect p w))
    rw [ih]
    exact quadraticMap_self_adjoint _ _ _

theorem nativeWordProbability_add {ι : Type*} (p : ι → Albert) (ρ σ : Albert)
    (w : Word ι) :
    nativeWordProbability p (ρ + σ) w =
      nativeWordProbability p ρ w + nativeWordProbability p σ w := by
  simp only [nativeWordProbability_eq_pairing, tracePairing_add_left]

theorem nativeWordProbability_smul {ι : Type*} (p : ι → Albert) (r : ℝ)
    (ρ : Albert) (w : Word ι) :
    nativeWordProbability p (r • ρ) w = r * nativeWordProbability p ρ w := by
  simp only [nativeWordProbability_eq_pairing, tracePairing_smul_left]

theorem continuous_nativeOutcome {ι : Type*} (a : Outcome ι) :
    Continuous (fun p : ι → Albert => nativeOutcome p a) := by
  cases a with
  | mk i b =>
    cases b
    · change Continuous (fun p : ι → Albert => albertUnit - p i)
      exact continuous_const.fun_sub (continuous_apply i)
    · exact continuous_apply i

theorem continuous_nativeBranchState_joint {ι : Type*} (w : Word ι) :
    Continuous (fun t : (ι → Albert) × Albert => nativeBranchState t.1 t.2 w) := by
  induction w with
  | nil => exact continuous_snd
  | cons a w ih =>
    have ho := (continuous_nativeOutcome a).comp
      (continuous_fst : Continuous (fun t : (ι → Albert) × Albert => t.1))
    have hu := continuous_quadraticMap.comp (ho.prodMk continuous_snd)
    have hc := ih.comp (continuous_fst.prodMk hu)
    exact hc.congr (fun _ => rfl)

theorem continuous_nativeWordProbability_joint {ι : Type*} (w : Word ι) :
    Continuous (fun t : (ι → Albert) × Albert => nativeWordProbability t.1 t.2 w) := by
  have hc := continuous_albertTrace.comp (continuous_nativeBranchState_joint w)
  exact hc.congr (fun _ => rfl)

theorem continuous_nativeWordProbability {ι : Type*} (p : ι → Albert) (w : Word ι) :
    Continuous (fun ρ : Albert => nativeWordProbability p ρ w) := by
  have hc := (continuous_nativeWordProbability_joint w).comp
    ((continuous_const : Continuous (fun _ : Albert => p)).prodMk
      (continuous_id : Continuous (id : Albert → Albert)))
  exact hc.congr (fun _ => rfl)

theorem continuous_nativeWordEffect {ι : Type*} (w : Word ι) :
    Continuous (fun p : ι → Albert => nativeWordEffect p w) := by
  induction w with
  | nil => exact continuous_const
  | cons a w ih =>
    have hc := continuous_quadraticMap.comp ((continuous_nativeOutcome a).prodMk ih)
    exact hc.congr (fun _ => rfl)

/-- The entire table of finite-word probabilities is a compact image for each
fixed menu. This is compactness only; no density-cone convexity is asserted. -/
theorem isCompact_nativeWordProbability_image {ι : Type*} (p : ι → Albert) :
    IsCompact ((fun ρ : Albert => fun w : Word ι => nativeWordProbability p ρ w) ''
      {ρ : Albert | IsDensity ρ}) := by
  exact isCompact_density_set.image (continuous_pi fun w => continuous_nativeWordProbability p w)

end AlbertSequential.NativeAnalysis
