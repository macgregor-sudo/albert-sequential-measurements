/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeCayleyManifold
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-! The locus of native atoms orthogonal to an atom is the ordinary eight-sphere. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.NativeCayley

open Metric NativeAnalysis Set WindowProbability
open scoped ContDiff Matrix Manifold

/-- Orthogonality in the actual native trace form, on the actual atom space. -/
def orthogonalAtomLocus (p : AlbertAtomSpace) : Set AlbertAtomSpace :=
  {q | tracePairing p.val q.val = 0}

/-- The scalar coordinate and the eight octonion coordinates have the usual Euclidean norm. -/
abbrev OrthogonalSphereAmbient := EuclideanSpace ℝ (Fin 9)

abbrev OrthogonalSphere := Metric.sphere (0 : OrthogonalSphereAmbient) 1

def firstDiagonalAtom : AlbertAtomSpace := ⟨diagAtom 0, diagAtom_isAtom 0⟩

/-- On the 1,2 block take the diagonal difference and twice its upper off-diagonal entry. -/
def orthogonalSphereCoordinates (q : Albert) : OrthogonalSphereAmbient :=
  WithLp.toLp 2 (Fin.cases (q.1 1 - q.1 2) (octonionChartCoordinates.symm ((2 : ℝ) • q.2 2)))

/-- Inverse affine map, writing the normalized rank-one candidate in the actual 1,2 block. -/
def orthogonalSphereEmbedding (x : OrthogonalSphereAmbient) : Albert :=
  (![0, (1 + x 0) / 2, (1 - x 0) / 2],
    ![0, 0, (1 / 2 : ℝ) • octonionChartCoordinates (fun i : Fin 8 => x i.succ)])

theorem isClosed_orthogonalAtomLocus (p : AlbertAtomSpace) : IsClosed (orthogonalAtomLocus p) := by
  have h : Continuous (fun q : AlbertAtomSpace => (p.val, q.val)) :=
    continuous_const.prodMk continuous_subtype_val
  have hc : Continuous (fun q : AlbertAtomSpace => tracePairing p.val q.val) :=
    (continuous_tracePairing.comp h).congr (fun _ => rfl)
  exact (isClosed_singleton : IsClosed ({0} : Set ℝ)).preimage hc

set_option maxHeartbeats 900000 in
theorem contDiff_orthogonalSphereCoordinates {n : ℕ∞ω} :
    ContDiff ℝ n orthogonalSphereCoordinates := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin 9 → ℝ)).symm.toContinuousLinearEquiv
  have hs : ContDiff ℝ n (fun q : Albert => q.1 1 - q.1 2) :=
    ((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 1).comp contDiff_fst).sub
      ((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 2).comp contDiff_fst)
  have hz : ContDiff ℝ n (fun q : Albert => q.2 2) :=
    (contDiff_apply ℝ (fun _ : Fin 3 => Octonion) 2).comp contDiff_snd
  have ho : ContDiff ℝ n (fun q : Albert => octonionChartCoordinates.symm ((2 : ℝ) • q.2 2)) :=
    octonionChartCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
      (hz.const_smul (2 : ℝ))
  have h : ContDiff ℝ n (fun (q : Albert) =>
      (Fin.cases (q.1 1 - q.1 2) (octonionChartCoordinates.symm ((2 : ℝ) • q.2 2)) : Fin 9 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hs
    · exact (contDiff_apply ℝ (fun _ : Fin 8 => ℝ) j).comp ho
  exact e.toContinuousLinearMap.contDiff.comp h

theorem contDiff_orthogonalSphereEmbedding {n : ℕ∞ω} :
    ContDiff ℝ n orthogonalSphereEmbedding := by
  have hx (i : Fin 9) : ContDiff ℝ n (fun x : OrthogonalSphereAmbient => x i) :=
    (PiLp.projₗ (𝕜 := ℝ) 2 (β := fun _ : Fin 9 => ℝ) i).toContinuousLinearMap.contDiff
  refine (contDiff_pi.mpr ?_).prodMk (contDiff_pi.mpr ?_)
  · intro i
    fin_cases i
    · exact contDiff_const
    · exact (contDiff_const.add (hx 0)).div_const 2
    · exact (contDiff_const.sub (hx 0)).div_const 2
  · intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_const
    · have h : ContDiff ℝ n (fun x : OrthogonalSphereAmbient =>
          octonionChartCoordinates (fun j : Fin 8 => x j.succ)) :=
        octonionChartCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
          (contDiff_pi.mpr fun j => hx j.succ)
      exact h.const_smul (1 / 2 : ℝ)

private theorem orthogonalSphereCoordinates_norm_sq (q : Albert) :
    ‖orthogonalSphereCoordinates q‖ ^ 2 = (q.1 1 - q.1 2)^2 + 4 * octNormSq (q.2 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  change (q.1 1 - q.1 2)^2 +
    (∑ i : Fin 8, octonionChartCoordinates.symm ((2 : ℝ) • q.2 2) i ^ 2) = _
  rw [← octNormSq_octonionChartCoordinates, LinearEquiv.apply_symm_apply, octNormSq_smul]
  norm_num

theorem orthogonalSphereCoordinates_mem {q : AlbertAtomSpace} (hq : q ∈ orthogonalAtomLocus firstDiagonalAtom) :
    orthogonalSphereCoordinates q.val ∈ OrthogonalSphere := by
  change tracePairing (diagAtom 0) q.val = 0 at hq
  rw [tracePairing_diagAtom] at hq
  have hrow := isAtom_zero_row0 q.property hq
  have htr : q.val.1 1 + q.val.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three, hq] using q.property.2
  have hn : octNormSq (q.val.2 2) = q.val.1 1 - q.val.1 1 * q.val.1 1 := by
    have h := congrArg (fun a : Albert => a.1 1) q.property.1
    rw [jordanMul_diag_1, hrow.1, octDot_zero_left, octDot_self, add_zero] at h
    linarith
  apply mem_sphere_zero_iff_norm.mpr
  have he : ‖orthogonalSphereCoordinates q.val‖ ^ 2 = 1 := by
    rw [orthogonalSphereCoordinates_norm_sq, hn]
    nlinarith [sq_nonneg (q.val.1 1 - q.val.1 2),
      congrArg (fun u : ℝ => u * (q.val.1 2 - q.val.1 1 + 1)) htr]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa only [one_pow] using he

theorem orthogonalSphereEmbedding_isAtom {x : OrthogonalSphereAmbient} (hx : x ∈ OrthogonalSphere) :
    IsAtom (orthogonalSphereEmbedding x) := by
  let q := orthogonalSphereEmbedding x
  have ha : q.1 0 = 0 := rfl
  have hl : q.2 0 = 0 := rfl
  have hr : q.2 1 = 0 := rfl
  have hc : q.1 1 + q.1 2 = 1 := by
    change (1 + x 0) / 2 + (1 - x 0) / 2 = 1
    ring
  have hxₛ : x 0 ^ 2 + (∑ i : Fin 8, (x i.succ)^2) = 1 := by
    have h := mem_sphere_zero_iff_norm.mp hx
    have h' := congrArg (fun a : ℝ => a^2) h
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, one_pow] at h'
    exact h'
  have hn : octNormSq (q.2 2) = q.1 1 * q.1 2 := by
    change octNormSq ((1 / 2 : ℝ) • octonionChartCoordinates (fun i : Fin 8 => x i.succ)) =
      ((1 + x 0) / 2) * ((1 - x 0) / 2)
    rw [octNormSq_smul, octNormSq_octonionChartCoordinates]
    nlinarith
  have h₁ : q.1 1 * q.1 1 + q.1 1 * q.1 2 = q.1 1 := by
    rw [← mul_add, hc, mul_one]
  have h₂ : q.1 2 * q.1 2 + q.1 1 * q.1 2 = q.1 2 := by
    rw [mul_comm (q.1 1) (q.1 2), ← mul_add, add_comm, hc, mul_one]
  refine ⟨?_, ?_⟩
  · change jordanMul q q = q
    apply Prod.ext <;> funext i
    · fin_cases i
      · change (jordanMul q q).1 0 = q.1 0
        simp [jordanMul_diag_0, ha, hl, hr, octDot_zero_left]
      · change (jordanMul q q).1 1 = q.1 1
        simpa only [jordanMul_diag_1, hl, octDot_zero_left, octDot_self, (octNormSq_eq_zero 0).mpr rfl, add_zero, hn] using h₁
      · change (jordanMul q q).1 2 = q.1 2
        simpa only [jordanMul_diag_2, hr, octDot_zero_left, octDot_self, (octNormSq_eq_zero 0).mpr rfl, add_zero, hn] using h₂
    · fin_cases i
      · change (jordanMul q q).2 0 = q.2 0
        simp [jordanMul_off_0, hl, hr, octonionMul_zero_left]
      · change (jordanMul q q).2 1 = q.2 1
        simp [jordanMul_off_1, hl, hr, octonionMul_zero_left]
      · change (jordanMul q q).2 2 = q.2 2
        rw [jordanMul_off_2, hc, one_smul, hl, hr]
        simp only [octonionMul_zero_right, add_zero, ← two_smul ℝ, smul_smul]
        norm_num
  · change albertTrace q = 1
    rw [albertTrace, Fin.sum_univ_three, ha, zero_add, hc]

theorem orthogonalSphereCoordinates_embedding (x : OrthogonalSphereAmbient) :
    orthogonalSphereCoordinates (orthogonalSphereEmbedding x) = x := by
  apply WithLp.ofLp_injective
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (1 + x 0) / 2 - (1 - x 0) / 2 = x 0
    ring
  · change octonionChartCoordinates.symm
      ((2 : ℝ) • ((1 / 2 : ℝ) • octonionChartCoordinates (fun j : Fin 8 => x j.succ))) j = x j.succ
    rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul, LinearEquiv.symm_apply_apply]

theorem orthogonalSphereEmbedding_coordinates {q : AlbertAtomSpace} (hq : q ∈ orthogonalAtomLocus firstDiagonalAtom) :
    orthogonalSphereEmbedding (orthogonalSphereCoordinates q.val) = q.val := by
  change tracePairing (diagAtom 0) q.val = 0 at hq
  rw [tracePairing_diagAtom] at hq
  have hrow := isAtom_zero_row0 q.property hq
  have htr : q.val.1 1 + q.val.1 2 = 1 := by
    simpa [albertTrace, Fin.sum_univ_three, hq] using q.property.2
  apply Prod.ext <;> funext i
  · fin_cases i
    · exact hq.symm
    · change (1 + (q.val.1 1 - q.val.1 2)) / 2 = q.val.1 1
      linarith
    · change (1 - (q.val.1 1 - q.val.1 2)) / 2 = q.val.1 2
      linarith
  · fin_cases i
    · exact hrow.1.symm
    · exact hrow.2.symm
    · change (1 / 2 : ℝ) • octonionChartCoordinates
        (octonionChartCoordinates.symm ((2 : ℝ) • q.val.2 2)) = q.val.2 2
      rw [LinearEquiv.apply_symm_apply, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

theorem orthogonalSphereEmbedding_pairing (x : OrthogonalSphereAmbient) :
    tracePairing (diagAtom 0) (orthogonalSphereEmbedding x) = 0 := by
  rw [tracePairing_diagAtom]
  rfl

/-- The explicit normalized Hermitian two-by-two identification at the first atom. -/
def firstOrthogonalAtomSphere : (orthogonalAtomLocus firstDiagonalAtom : Type) ≃ₜ (OrthogonalSphere : Type) where
  toFun q := ⟨orthogonalSphereCoordinates q.val.val, orthogonalSphereCoordinates_mem q.property⟩
  invFun x := ⟨⟨orthogonalSphereEmbedding x.val, orthogonalSphereEmbedding_isAtom x.property⟩,
    orthogonalSphereEmbedding_pairing x.val⟩
  left_inv q := Subtype.ext (Subtype.ext (orthogonalSphereEmbedding_coordinates q.property))
  right_inv x := Subtype.ext (orthogonalSphereCoordinates_embedding x.val)
  continuous_toFun :=
    (contDiff_orthogonalSphereCoordinates (n := 1)).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val) |>.subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun x : OrthogonalSphere => orthogonalSphereEmbedding x.val) :=
      (contDiff_orthogonalSphereEmbedding (n := 1)).continuous.comp continuous_subtype_val
    exact (hc.subtype_mk (fun x => orthogonalSphereEmbedding_isAtom x.property)).subtype_mk
      (fun x => orthogonalSphereEmbedding_pairing x.val)

/-- Restrict a genuine native automorphism to the orthogonal atom loci. -/
def orthogonalAtomLocusHomeomorph (g : NativeAlbertAutomorphism) (p p' : AlbertAtomSpace)
    (hg : g.linearEquiv p.val = p'.val) :
    (orthogonalAtomLocus p : Type) ≃ₜ (orthogonalAtomLocus p' : Type) where
  toFun q := ⟨⟨g.linearEquiv q.val.val, g.map_isAtom q.val.property⟩, by
    change tracePairing p'.val (g.linearEquiv q.val.val) = 0
    rw [← hg, nativeAutomorphism_pairing]
    exact q.property⟩
  invFun q := ⟨⟨g.linearEquiv.symm q.val.val, g.symm.map_isAtom q.val.property⟩, by
    change tracePairing p.val (g.linearEquiv.symm q.val.val) = 0
    rw [← nativeAutomorphism_pairing g, LinearEquiv.apply_symm_apply, hg]
    exact q.property⟩
  left_inv q := Subtype.ext (Subtype.ext (g.linearEquiv.symm_apply_apply q.val.val))
  right_inv q := Subtype.ext (Subtype.ext (g.linearEquiv.apply_symm_apply q.val.val))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact g.linearEquiv.toContinuousLinearEquiv.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact g.linearEquiv.symm.toContinuousLinearEquiv.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)

/-- The actual trace-orthogonal atom locus at any atom is a standard unit eight-sphere. -/
def orthogonalAtomSphere (p : AlbertAtomSpace) :
    (orthogonalAtomLocus p : Type) ≃ₜ (OrthogonalSphere : Type) :=
  (orthogonalAtomLocusHomeomorph (chosenAtomNormalizer p.val p.property) p firstDiagonalAtom
    (Classical.choose_spec (nativeAtomNormalizer_first p.val p.property))).trans firstOrthogonalAtomSphere

end AlbertSequential.NativeCayley
