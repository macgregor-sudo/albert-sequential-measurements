module

public import NativeAlbertLaws
public import NativeTopology
public import Interfaces.WordsAndCertificates
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.FunProp

/-!+# Trace geometry and topology of the literal compact Albert coordinates

The elementary algebra is in NativeAlbertLaws.
This analytic module installs no global norm or multiplication on the native
carriers. The continuous image proof of density compactness uses the definition
of positivity as a square, without cone convexity or a spectral theorem.
-/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

local instance : IsTopologicalAddGroup Octonion :=
  inferInstanceAs (IsTopologicalAddGroup (Quaternion ℝ × Quaternion ℝ))
local instance : ContinuousSMul ℝ Octonion :=
  inferInstanceAs (ContinuousSMul ℝ (Quaternion ℝ × Quaternion ℝ))
local instance : IsTopologicalAddGroup Albert :=
  inferInstanceAs (IsTopologicalAddGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
local instance : ContinuousSMul ℝ Albert :=
  inferInstanceAs (ContinuousSMul ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

theorem continuous_octonionMul :
    Continuous (fun xy : Octonion × Octonion => octonionMul xy.1 xy.2) := by
  change Continuous (fun xy : (Quaternion ℝ × Quaternion ℝ) ×
    (Quaternion ℝ × Quaternion ℝ) =>
      (xy.1.1 * xy.2.1 - star xy.2.2 * xy.1.2,
       xy.2.2 * xy.1.1 + xy.1.2 * star xy.2.1))
  fun_prop

theorem continuous_octonionConj : Continuous octonionConj := by
  change Continuous (fun x : Quaternion ℝ × Quaternion ℝ => (star x.1, -x.2))
  fun_prop

theorem continuous_octonionScalar : Continuous octonionScalar := by
  change Continuous (fun r : ℝ => ((r : Quaternion ℝ), (0 : Quaternion ℝ)))
  exact Quaternion.continuous_coe.prodMk continuous_const

theorem continuous_octonionReal : Continuous octonionReal := by
  exact Quaternion.continuous_re.comp continuous_fst

theorem continuous_albertMatrix (i j : Fin 3) :
    Continuous (fun x : Albert => albertMatrix x i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [albertMatrix] <;>
    first
    | exact continuous_octonionScalar.comp ((continuous_apply _).comp continuous_fst)
    | exact (continuous_apply _).comp continuous_snd
    | exact continuous_octonionConj.comp ((continuous_apply _).comp continuous_snd)

theorem continuous_albertCoordinates : Continuous albertCoordinates := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact continuous_octonionReal.comp ((continuous_apply i).comp (continuous_apply i))
  · apply continuous_pi
    intro i
    fin_cases i
    all_goals change Continuous (fun m : Fin 3 → Fin 3 → Octonion => m _ _)
    all_goals exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_octonionMatrixMul :
    Continuous (fun xy : (Fin 3 → Fin 3 → Octonion) ×
      (Fin 3 → Fin 3 → Octonion) => octonionMatrixMul xy.1 xy.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_finsetSum
  intro k _
  have hl : Continuous (fun xy : (Fin 3 → Fin 3 → Octonion) ×
      (Fin 3 → Fin 3 → Octonion) => xy.1 i k) := by fun_prop
  have hr : Continuous (fun xy : (Fin 3 → Fin 3 → Octonion) ×
      (Fin 3 → Fin 3 → Octonion) => xy.2 k j) := by fun_prop
  exact continuous_octonionMul.comp (hl.prodMk hr)

theorem continuous_albertMatrix_map : Continuous albertMatrix :=
  continuous_pi fun i => continuous_pi fun j => continuous_albertMatrix i j

theorem continuous_jordanMul :
    Continuous (fun xy : Albert × Albert => jordanMul xy.1 xy.2) := by
  have hm := continuous_albertMatrix_map
  have h1 := continuous_octonionMatrixMul.comp
    ((hm.comp continuous_fst).prodMk (hm.comp continuous_snd))
  have h2 := continuous_octonionMatrixMul.comp
    ((hm.comp continuous_snd).prodMk (hm.comp continuous_fst))
  simpa only [jordanMul, Function.comp_apply] using
    (continuous_albertCoordinates.comp (h1.fun_add h2)).fun_const_smul (1 / 2 : ℝ)

theorem continuous_albertTrace : Continuous albertTrace := by
  unfold albertTrace
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).comp continuous_fst

theorem continuous_tracePairing :
    Continuous (fun xy : Albert × Albert => tracePairing xy.1 xy.2) :=
  continuous_albertTrace.comp continuous_jordanMul

theorem continuous_quadraticMap :
    Continuous (fun xy : Albert × Albert => quadraticMap xy.1 xy.2) := by
  unfold quadraticMap
  have h1 := continuous_jordanMul.comp (continuous_fst.prodMk continuous_jordanMul)
  have h2 := continuous_jordanMul.comp
    ((continuous_jordanMul.comp (continuous_fst.prodMk continuous_fst)).prodMk continuous_snd)
  simpa only [two_smul, Function.comp_apply] using (h1.fun_add h1).fun_sub h2

theorem octDot_self_eq_normSq (z : Octonion) :
    octDot z z = Quaternion.normSq z.1 + Quaternion.normSq z.2 := by
  rw [octDot_eq_coords, Quaternion.normSq_def', Quaternion.normSq_def']
  ring

theorem trace_square_coordinates (y : Albert) :
    albertTrace (jordanMul y y) = (∑ i : Fin 3, (y.1 i)^2) +
      2 * (∑ i : Fin 3, (Quaternion.normSq (y.2 i).1 + Quaternion.normSq (y.2 i).2)) := by
  change tracePairing y y = _
  rw [tracePairing_eq_coords]
  simp only [octDot_self_eq_normSq, Fin.sum_univ_three]
  ring

end AlbertSequential.NativeAnalysis
