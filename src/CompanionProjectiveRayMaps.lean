/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionQuadrangleGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
noncomputable section

namespace AlbertSequential.ProjectiveMetricInvariant

open NativeAnalysis WindowProbability

def IsPositiveAtomRay (x : Albert) : Prop :=
  ∃ (r : ℝ) (p : AlbertAtomSpace), 0 < r ∧ x = r • p.val

structure CubicRayEquiv where
  linearEquiv : Albert ≃ₗ[ℝ] Albert
  scale : ℝ
  scale_pos : 0 < scale
  map_norm : ∀ x, albertCubicNorm (linearEquiv x) = scale * albertCubicNorm x
  map_ray : ∀ x, IsPositiveAtomRay (linearEquiv x) ↔ IsPositiveAtomRay x

namespace CubicRayEquiv

theorem ray_of_atom (p : AlbertAtomSpace) : IsPositiveAtomRay p.val :=
  ⟨1, p, zero_lt_one, (one_smul ℝ _).symm⟩

theorem trace_pos (g : CubicRayEquiv) (p : AlbertAtomSpace) :
    0 < albertTrace (g.linearEquiv p.val) := by
  obtain ⟨r, a, hr, ha⟩ := (g.map_ray p.val).mpr (ray_of_atom p)
  rwa [ha, albertTrace_smul, a.property.2, mul_one]

def pointMap (g : CubicRayEquiv) (p : AlbertAtomSpace) : AlbertAtomSpace :=
  ⟨(albertTrace (g.linearEquiv p.val))⁻¹ • g.linearEquiv p.val, by
    obtain ⟨r, a, hr, ha⟩ := (g.map_ray p.val).mpr (ray_of_atom p)
    rw [ha, albertTrace_smul, a.property.2, mul_one, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact a.property⟩

theorem raw_pointMap (g : CubicRayEquiv) (p : AlbertAtomSpace) :
    g.linearEquiv p.val = albertTrace (g.linearEquiv p.val) • (g.pointMap p).val := by
  change g.linearEquiv p.val =
    albertTrace (g.linearEquiv p.val) • (albertTrace (g.linearEquiv p.val))⁻¹ • g.linearEquiv p.val
  rw [smul_smul, mul_inv_cancel₀ (g.trace_pos p).ne', one_smul]

theorem pointMap_eq_of_raw (g : CubicRayEquiv) {p q : AlbertAtomSpace} {r : ℝ}
    (hr : r ≠ 0) (h : g.linearEquiv p.val = r • q.val) : g.pointMap p = q := by
  apply Subtype.ext
  change (albertTrace (g.linearEquiv p.val))⁻¹ • g.linearEquiv p.val = q.val
  rw [h, albertTrace_smul, q.property.2, mul_one, smul_smul, inv_mul_cancel₀ hr, one_smul]

def ofAutomorphism (g : NativeAlbertAutomorphism) : CubicRayEquiv where
  linearEquiv := g.linearEquiv
  scale := 1
  scale_pos := zero_lt_one
  map_norm x := by rw [g.map_cubicNorm, one_mul]
  map_ray x := by
    constructor
    · rintro ⟨r, p, hr, hp⟩
      refine ⟨r, ⟨g.symm.linearEquiv p.val, g.symm.map_isAtom p.property⟩, hr, ?_⟩
      have h := congrArg g.linearEquiv.symm hp
      simpa only [show g.symm.linearEquiv = g.linearEquiv.symm from rfl,
        LinearEquiv.symm_apply_apply, map_smul] using h
    · rintro ⟨r, p, hr, rfl⟩
      exact ⟨r, ⟨g.linearEquiv p.val, g.map_isAtom p.property⟩, hr, map_smul _ _ _⟩

@[simp] theorem pointMap_ofAutomorphism_val (g : NativeAlbertAutomorphism) (p : AlbertAtomSpace) :
    ((ofAutomorphism g).pointMap p).val = g.linearEquiv p.val := by
  change (albertTrace (g.linearEquiv p.val))⁻¹ • g.linearEquiv p.val = _
  rw [g.preserves_trace, p.property.2, inv_one, one_smul]

def trans (g h : CubicRayEquiv) : CubicRayEquiv where
  linearEquiv := g.linearEquiv.trans h.linearEquiv
  scale := h.scale * g.scale
  scale_pos := mul_pos h.scale_pos g.scale_pos
  map_norm x := by
    rw [LinearEquiv.trans_apply, h.map_norm, g.map_norm, mul_assoc]
  map_ray x := by rw [LinearEquiv.trans_apply, h.map_ray, g.map_ray]

theorem pointMap_trans (g h : CubicRayEquiv) (p : AlbertAtomSpace) :
    (g.trans h).pointMap p = h.pointMap (g.pointMap p) := by
  apply pointMap_eq_of_raw _ (mul_pos (g.trace_pos p) (h.trace_pos (g.pointMap p))).ne'
  change h.linearEquiv (g.linearEquiv p.val) = _
  conv_lhs => rw [g.raw_pointMap p]
  rw [map_smul]
  conv_lhs => rw [h.raw_pointMap (g.pointMap p), smul_smul]

def symm (g : CubicRayEquiv) : CubicRayEquiv where
  linearEquiv := g.linearEquiv.symm
  scale := g.scale⁻¹
  scale_pos := inv_pos.mpr g.scale_pos
  map_norm x := by
    conv_rhs => rw [← g.linearEquiv.apply_symm_apply x, g.map_norm, ← mul_assoc,
      inv_mul_cancel₀ g.scale_pos.ne', one_mul]
  map_ray x := by
    have h := (g.map_ray (g.linearEquiv.symm x)).symm
    rwa [LinearEquiv.apply_symm_apply] at h

theorem symm_pointMap (g : CubicRayEquiv) (p : AlbertAtomSpace) :
    g.symm.pointMap (g.pointMap p) = p := by
  apply pointMap_eq_of_raw _ (inv_ne_zero (g.trace_pos p).ne')
  change g.linearEquiv.symm ((albertTrace (g.linearEquiv p.val))⁻¹ • g.linearEquiv p.val) = _
  rw [map_smul, LinearEquiv.symm_apply_apply]

theorem positive_smul_ray_iff {a : ℝ} (ha : 0 < a) (x : Albert) :
    IsPositiveAtomRay (a • x) ↔ IsPositiveAtomRay x := by
  constructor
  · rintro ⟨r, p, hr, he⟩
    refine ⟨a⁻¹ * r, p, mul_pos (inv_pos.mpr ha) hr, ?_⟩
    have hh := congrArg (fun y : Albert => a⁻¹ • y) he
    change a⁻¹ • (a • x) = a⁻¹ • (r • p.val) at hh
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at hh
  · rintro ⟨r, p, hr, rfl⟩
    exact ⟨a * r, p, mul_pos ha hr, smul_smul a r _⟩

def normalizeNorm (g : CubicRayEquiv) : CubicRayEquiv := by
  let a : ℝ := (g.scale⁻¹) ^ (1 / 3 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos (inv_pos.mpr g.scale_pos) _
  have hcube : a ^ (3 : ℕ) = g.scale⁻¹ := by
    dsimp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr g.scale_pos.le)]
    norm_num
  refine ⟨g.linearEquiv.trans (LinearEquiv.smulOfNeZero ℝ Albert a ha.ne'), 1, zero_lt_one, ?_, ?_⟩
  · intro x
    change albertCubicNorm (a • g.linearEquiv x) = 1 * _
    rw [albertCubicNorm_smul, hcube, g.map_norm, ← mul_assoc,
      inv_mul_cancel₀ g.scale_pos.ne']
  · intro x
    change IsPositiveAtomRay (a • g.linearEquiv x) ↔ _
    rw [positive_smul_ray_iff ha, g.map_ray]

@[simp] theorem normalizeNorm_scale (g : CubicRayEquiv) : g.normalizeNorm.scale = 1 := rfl

@[simp] theorem pointMap_normalizeNorm (g : CubicRayEquiv) (p : AlbertAtomSpace) :
    g.normalizeNorm.pointMap p = g.pointMap p := by
  let a : ℝ := (g.scale⁻¹) ^ (1 / 3 : ℝ)
  have ha : 0 < a := Real.rpow_pos_of_pos (inv_pos.mpr g.scale_pos) _
  apply pointMap_eq_of_raw _ (mul_pos ha (g.trace_pos p)).ne'
  change a • g.linearEquiv p.val = _
  conv_lhs => rw [g.raw_pointMap p]
  rw [smul_smul]

end CubicRayEquiv

private theorem diagScale_sharp (u v : ℝ) (x : Albert) :
    albertSharp (diagScale u v x) =
      (![(u*v)^2 * (albertSharp x).1 0, v^2 * (albertSharp x).1 1, u^2 * (albertSharp x).1 2],
       ![(u*v^2) • (albertSharp x).2 0, (u^2*v) • (albertSharp x).2 1,
          (u*v) • (albertSharp x).2 2]) := by
  apply Prod.ext <;> funext i <;> fin_cases i
  all_goals simp [albertSharp, diagScale, octNormSq_smul, octonionConj_smul,
    octonionMul_smul_left, octonionMul_smul_right, smul_smul, smul_sub]
  · ring
  · ring
  · ring
  · module
  · module
  · module

private theorem diagScale_trace_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (p : AlbertAtomSpace) : 0 < albertTrace (diagScale u v p.val) := by
  have ht := p.property.2
  rw [albertTrace, Fin.sum_univ_three] at ht
  have h0 := isAtom_diag_nonneg p.property 0
  have h1 := isAtom_diag_nonneg p.property 1
  have h2 := isAtom_diag_nonneg p.property 2
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  simp [albertTrace, Fin.sum_univ_three, diagScale]
  by_contra! hz
  have hp0 : p.val.1 0 = 0 := by nlinarith [mul_nonneg hu2.le h1, mul_nonneg hv2.le h2]
  have hp1 : p.val.1 1 = 0 := by
    by_contra h
    nlinarith [mul_pos hu2 (lt_of_le_of_ne h1 (Ne.symm h)), mul_nonneg hv2.le h2]
  have hp2 : p.val.1 2 = 0 := by
    by_contra h
    nlinarith [mul_pos hv2 (lt_of_le_of_ne h2 (Ne.symm h)), mul_nonneg hu2.le h1]
  rw [hp0, hp1, hp2] at ht
  norm_num at ht

private theorem isAtom_of_sharp_zero_trace_one {p : Albert} (hs : albertSharp p = 0)
    (ht : albertTrace p = 1) : IsAtom p := by
  let s := (1 / 2 : ℝ) * (1 - albertTrace (jordanMul p p))
  have he : (0 : Albert) = jordanMul p p - p + s • albertUnit := by
    simpa [tracePairing, s, ht, hs] using albertSharp_eq_jordanMul p
  have h := congrArg albertTrace he
  have hu : albertTrace albertUnit = 3 := by norm_num [albertTrace, Fin.sum_univ_three, albertUnit]
  rw [albertTrace_add, albertTrace_sub, albertTrace_smul, ht, hu] at h
  have hz : albertTrace (0 : Albert) = 0 := by simp [albertTrace, show ((0 : Albert).1) = 0 from rfl]
  rw [hz] at h
  have hs0 : s = 0 := by linarith [show s = (1 / 2 : ℝ) * (1 - albertTrace (jordanMul p p)) from rfl]
  rw [hs0, zero_smul, add_zero] at he
  exact ⟨sub_eq_zero.mp he.symm, ht⟩

private theorem diagonalCongruence_maps_ray {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    {x : Albert} (hx : IsPositiveAtomRay x) :
    IsPositiveAtomRay (diagonalCongruence u v hu.ne' hv.ne' x) := by
  obtain ⟨r, p, hr, rfl⟩ := hx
  let z := diagScale u v p.val
  let t := albertTrace z
  have ht : 0 < t := diagScale_trace_pos hu hv p
  have hs : albertSharp z = 0 := by
    dsimp only [z]
    rw [diagScale_sharp, albertSharp_atom_eq_zero _ p.property]
    apply Prod.ext <;> funext i <;> fin_cases i
    all_goals simp [show (0 : Albert).1 = 0 from rfl, show (0 : Albert).2 = 0 from rfl]
  let q : AlbertAtomSpace :=
    ⟨t⁻¹ • z, isAtom_of_sharp_zero_trace_one
      (by rw [albertSharp_smul, hs, smul_zero])
      (by rw [albertTrace_smul, inv_mul_cancel₀ ht.ne'])⟩
  refine ⟨r * t, q, mul_pos hr ht, ?_⟩
  rw [map_smul]
  change r • z = (r*t) • t⁻¹ • z
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ ht.ne', mul_one]

def positiveDiagonalCongruence (u v : ℝ) (hu : 0 < u) (hv : 0 < v) : CubicRayEquiv where
  linearEquiv := diagonalCongruence u v hu.ne' hv.ne'
  scale := (u*v)^2
  scale_pos := sq_pos_of_pos (mul_pos hu hv)
  map_norm x := by
    change albertCubicNorm (diagScale u v x) = _
    simp [albertCubicNorm, diagScale, octNormSq_smul, octonionMul_smul_left,
      octonionMul_smul_right, octDot_smul_left, octDot_smul_right]
    ring
  map_ray x := by
    refine ⟨?_, diagonalCongruence_maps_ray hu hv⟩
    intro h
    have hh := diagonalCongruence_maps_ray (inv_pos.mpr hu) (inv_pos.mpr hv) h
    change IsPositiveAtomRay ((diagonalCongruence u v hu.ne' hv.ne').symm
      (diagonalCongruence u v hu.ne' hv.ne' x)) at hh
    rwa [LinearEquiv.symm_apply_apply] at hh

end AlbertSequential.ProjectiveMetricInvariant
