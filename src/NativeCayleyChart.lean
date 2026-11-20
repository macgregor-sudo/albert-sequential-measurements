/- SPDX-License-Identifier: Apache-2.0 -/
module
public import WindowProbabilityAlbertGroup
public import WindowProbabilityChart
public import OctonionRealCoordinates
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.Star

/-! The normalized rank-one dyad and its positive-pivot inverse. -/
@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.NativeCayley

open WindowProbability
open scoped Matrix ContDiff

scoped instance : NormedAddCommGroup Octonion :=
  inferInstanceAs (NormedAddCommGroup (Quaternion ℝ × Quaternion ℝ))
scoped instance : NormedSpace ℝ Octonion :=
  inferInstanceAs (NormedSpace ℝ (Quaternion ℝ × Quaternion ℝ))
scoped instance : FiniteDimensional ℝ Octonion := octonionChartCoordinates.finiteDimensional
scoped instance : NormedAddCommGroup Albert :=
  inferInstanceAs (NormedAddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
scoped instance : NormedSpace ℝ Albert :=
  inferInstanceAs (NormedSpace ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
scoped instance : FiniteDimensional ℝ Albert := NativeAnalysis.recoveredCoordinateEquiv.symm.finiteDimensional

abbrev AffineCoordinates := Octonion × Octonion

/-- The ambient rank-one embedding, based at the first positive diagonal pivot. -/
def affineAtomEmbedding (q : AffineCoordinates) : Albert :=
  (albertTrace (chartDyad q.1 q.2))⁻¹ • chartDyad q.1 q.2

/-- Recover the two affine octonions by dividing the first column by the real pivot. -/
def firstPivotCoordinates (p : Albert) : AffineCoordinates :=
  ((p.1 0)⁻¹ • octonionConj (p.2 0), (p.1 0)⁻¹ • octonionConj (p.2 1))

theorem isAtom_affineAtomEmbedding (q : AffineCoordinates) : IsAtom (affineAtomEmbedding q) :=
  chartDyad_normalize_isAtom q.1 q.2

theorem affineAtomEmbedding_pivot (q : AffineCoordinates) :
    (affineAtomEmbedding q).1 0 = (albertTrace (chartDyad q.1 q.2))⁻¹ := by
  change (albertTrace (chartDyad q.1 q.2))⁻¹ * octNormSq octOne = _
  rw [octNormSq_one, mul_one]

theorem firstPivotCoordinates_affineAtomEmbedding (q : AffineCoordinates) :
    firstPivotCoordinates (affineAtomEmbedding q) = q := by
  let d := albertTrace (chartDyad q.1 q.2)
  have hd : d ≠ 0 := (chartDyad_trace_pos q.1 q.2).ne'
  have h0 : (affineAtomEmbedding q).2 0 = d⁻¹ • octonionConj q.1 := by
    change d⁻¹ • octonionMul octOne (octonionConj q.1) = _
    rw [octonionMul_one_left]
  have h1 : (affineAtomEmbedding q).2 1 = d⁻¹ • octonionConj q.2 := by
    change d⁻¹ • octonionMul octOne (octonionConj q.2) = _
    rw [octonionMul_one_left]
  unfold firstPivotCoordinates
  rw [affineAtomEmbedding_pivot, h0, h1]
  change (d⁻¹⁻¹ • octonionConj (d⁻¹ • octonionConj q.1),
    d⁻¹⁻¹ • octonionConj (d⁻¹ • octonionConj q.2)) = q
  simp only [inv_inv, octonionConj_smul, octonionConj_conj, smul_smul, mul_inv_cancel₀ hd,
    one_smul, Prod.eta]

private theorem octDyad_homogeneous (r : ℝ) (v : Fin 3 → Octonion) :
    octDyad (fun i => r • v i) = r ^ 2 • octDyad v := by
  have hsnd (A : Albert) : (r ^ 2 • A).2 = r ^ 2 • A.2 := rfl
  apply Prod.ext <;> funext i
  · exact octNormSq_smul r (v i)
  · rw [hsnd]
    fin_cases i <;> simp [octDyad, Pi.smul_apply, octonionConj_smul, octonionMul_smul_left,
      octonionMul_smul_right, smul_smul, pow_two]

theorem affineAtomEmbedding_firstPivotCoordinates {p : Albert} (hp : IsAtom p) (ha : 0 < p.1 0) :
    affineAtomEmbedding (firstPivotCoordinates p) = p := by
  let a := p.1 0
  let r := Real.sqrt a
  let q := firstPivotCoordinates p
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha.le
  have hscale : 1 / r = r * a⁻¹ := by
    rw [← hr2]
    field_simp
  have hv : (![octonionScalar r, (1 / r) • octonionConj (p.2 0),
      (1 / r) • octonionConj (p.2 1)] : Fin 3 → Octonion) =
      fun i => r • (![octOne, q.1, q.2] : Fin 3 → Octonion) i := by
    funext i
    fin_cases i
    · exact octonionScalar_eq_smul r
    · change (1 / r) • octonionConj (p.2 0) = r • (a⁻¹ • octonionConj (p.2 0))
      rw [smul_smul, hscale]
    · change (1 / r) • octonionConj (p.2 1) = r • (a⁻¹ • octonionConj (p.2 1))
      rw [smul_smul, hscale]
  have hd : p = a • chartDyad q.1 q.2 := by
    have h := (isAtom_eq_octDyad hp ha).1
    change p = octDyad ![octonionScalar r, (1 / r) • octonionConj (p.2 0),
      (1 / r) • octonionConj (p.2 1)] at h
    rw [hv, octDyad_homogeneous, hr2] at h
    exact h
  have ht : a * albertTrace (chartDyad q.1 q.2) = 1 := by
    rw [← albertTrace_smul, ← hd]
    exact hp.2
  change (albertTrace (chartDyad q.1 q.2))⁻¹ • chartDyad q.1 q.2 = p
  rw [eq_inv_of_mul_eq_one_left ht |>.symm, ← hd]

/-- Slot swaps let the three charts share a single affine formula. -/
def pivotAutomorphism (i : Fin 3) : NativeAlbertAutomorphism :=
  ![NativeAlbertAutomorphism.refl, swap01AlbertAuto, swap02AlbertAuto] i

theorem pivotAutomorphism_first (i : Fin 3) (p : Albert) :
    ((pivotAutomorphism i).linearEquiv p).1 0 = p.1 i := by
  fin_cases i
  · rfl
  · exact congrArg (fun x : Albert => x.1 0) (swap01AlbertAuto_apply p)
  · exact congrArg (fun x : Albert => x.1 0) (swap02AlbertAuto_apply p)

theorem exists_positive_pivot (p : AlbertAtomSpace) : ∃ i : Fin 3, 0 < p.val.1 i := by
  have ht : p.val.1 0 + p.val.1 1 + p.val.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three] using p.property.2
  by_contra! h
  linarith [h 0, h 1, h 2]

private theorem contDiff_quaternionStar {n : ℕ∞ω} :
    ContDiff ℝ n (star : Quaternion ℝ → Quaternion ℝ) :=
  (starL' ℝ : Quaternion ℝ ≃L[ℝ] Quaternion ℝ).toContinuousLinearMap.contDiff

private theorem contDiff_octonionConj {n : ℕ∞ω} : ContDiff ℝ n octonionConj := by
  change ContDiff ℝ n (fun x : Quaternion ℝ × Quaternion ℝ => (star x.1, -x.2))
  exact (contDiff_quaternionStar.comp contDiff_fst).prodMk contDiff_snd.neg

private theorem contDiff_octonionMul {n : ℕ∞ω} :
    ContDiff ℝ n (fun p : Octonion × Octonion => octonionMul p.1 p.2) := by
  change ContDiff ℝ n (fun p : (Quaternion ℝ × Quaternion ℝ) × (Quaternion ℝ × Quaternion ℝ) =>
    (p.1.1 * p.2.1 - star p.2.2 * p.1.2, p.2.2 * p.1.1 + p.1.2 * star p.2.1))
  exact (((contDiff_fst.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd)).sub
    ((contDiff_quaternionStar.comp (contDiff_snd.comp contDiff_snd)).mul
      (contDiff_snd.comp contDiff_fst))).prodMk
    (((contDiff_snd.comp contDiff_snd).mul (contDiff_fst.comp contDiff_fst)).add
      ((contDiff_snd.comp contDiff_fst).mul
        (contDiff_quaternionStar.comp (contDiff_fst.comp contDiff_snd))))

private theorem contDiff_octNormSq {n : ℕ∞ω} : ContDiff ℝ n octNormSq := by
  have hRe : ContDiff ℝ n (fun x : Quaternion ℝ => x.re) :=
    (QuaternionAlgebra.reₗ (-1) 0 (-1) : Quaternion ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap.contDiff
  have hQ : ContDiff ℝ n (fun x : Quaternion ℝ => Quaternion.normSq x) :=
    hRe.comp (contDiff_id.mul contDiff_quaternionStar)
  have h : octNormSq = fun x => Quaternion.normSq x.1 + Quaternion.normSq x.2 := by
    funext x
    rw [octNormSq_eq_coords, Quaternion.normSq_def', Quaternion.normSq_def']
    ring
  rw [h]
  exact (hQ.comp contDiff_fst).add (hQ.comp contDiff_snd)

private theorem contDiff_chartDyad {n : ℕ∞ω} :
    ContDiff ℝ n (fun q : AffineCoordinates => chartDyad q.1 q.2) := by
  refine (contDiff_pi.mpr ?_).prodMk (contDiff_pi.mpr ?_)
  · intro i
    fin_cases i
    · change ContDiff ℝ n (fun _ : AffineCoordinates => octNormSq octOne)
      exact contDiff_const
    · change ContDiff ℝ n (fun q : AffineCoordinates => octNormSq q.1)
      exact contDiff_octNormSq.comp contDiff_fst
    · change ContDiff ℝ n (fun q : AffineCoordinates => octNormSq q.2)
      exact contDiff_octNormSq.comp contDiff_snd
  · intro i
    fin_cases i
    · change ContDiff ℝ n (fun q : AffineCoordinates => octonionMul octOne (octonionConj q.1))
      simp_rw [octonionMul_one_left]
      exact contDiff_octonionConj.comp contDiff_fst
    · change ContDiff ℝ n (fun q : AffineCoordinates => octonionMul octOne (octonionConj q.2))
      simp_rw [octonionMul_one_left]
      exact contDiff_octonionConj.comp contDiff_snd
    · exact contDiff_octonionMul.comp (contDiff_fst.prodMk (contDiff_octonionConj.comp contDiff_snd))

theorem contDiff_affineAtomEmbedding {n : ℕ∞ω} : ContDiff ℝ n affineAtomEmbedding := by
  have hd : ContDiff ℝ n (fun q : AffineCoordinates => 1 + octNormSq q.1 + octNormSq q.2) :=
    (contDiff_const.add (contDiff_octNormSq.comp contDiff_fst)).add
      (contDiff_octNormSq.comp contDiff_snd)
  have hi := hd.inv fun q => by rw [← chartDyad_trace]; exact (chartDyad_trace_pos q.1 q.2).ne'
  unfold affineAtomEmbedding
  simp_rw [chartDyad_trace]
  exact hi.smul contDiff_chartDyad

theorem contDiffOn_firstPivotCoordinates {n : ℕ∞ω} :
    ContDiffOn ℝ n firstPivotCoordinates {p : Albert | 0 < p.1 0} := by
  have h0 : ContDiff ℝ n (fun p : Albert => p.1 0) :=
    (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 0).comp contDiff_fst
  have hi := h0.contDiffOn.inv (s := {p : Albert | 0 < p.1 0}) fun p hp => (show 0 < p.1 0 from hp).ne'
  have hSlot (j : Fin 3) : ContDiff ℝ n (fun p : Albert => octonionConj (p.2 j)) :=
    contDiff_octonionConj.comp ((contDiff_apply ℝ (fun _ : Fin 3 => Octonion) j).comp contDiff_snd)
  exact (hi.smul (hSlot 0).contDiffOn).prodMk (hi.smul (hSlot 1).contDiffOn)

end AlbertSequential.NativeCayley
