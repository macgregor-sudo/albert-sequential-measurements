/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionProjectiveIncidence

@[expose] public section
noncomputable section

namespace AlbertSequential.ProjectiveMetricInvariant

open NativeAnalysis WindowProbability

private theorem diagonal_ne_zero_for_fourth (p : Fin 4 → AlbertAtomSpace)
    (hp : p ∈ quadrangleLocus) (ha : ∀ i : Fin 3, p i.castSucc = quadrangleAxis i)
    (i : Fin 3) : (p 3).val.1 i ≠ 0 := by
  intro h
  have haxis (j : Fin 3) (hj : i ≠ j) :
      tracePairing (p j.castSucc).val (diagAtom i) = 0 := by
    rw [ha, tracePairing_comm, tracePairing_diagAtom]
    change (if i = j then (1 : ℝ) else 0) = 0
    exact ite_eq_right hj
  have hlast : tracePairing (p 3).val (diagAtom i) = 0 := by
    rw [tracePairing_comm, tracePairing_diagAtom]
    exact h
  let q := quadrangleAxis i
  fin_cases i
  · let t : Fin 3 ↪ Fin 4 := ⟨![1, 2, 3], by decide⟩
    exact hp t ⟨q, fun j => by
      fin_cases j
      · exact haxis 1 (by decide)
      · exact haxis 2 (by decide)
      · exact hlast⟩
  · let t : Fin 3 ↪ Fin 4 := ⟨![0, 2, 3], by decide⟩
    exact hp t ⟨q, fun j => by
      fin_cases j
      · exact haxis 0 (by decide)
      · exact haxis 2 (by decide)
      · exact hlast⟩
  · let t : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by decide⟩
    exact hp t ⟨q, fun j => by
      fin_cases j
      · exact haxis 0 (by decide)
      · exact haxis 1 (by decide)
      · exact hlast⟩

private theorem positiveDiagonalCongruence_fixes_axes (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (i : Fin 3) : (positiveDiagonalCongruence u v hu hv).pointMap (quadrangleAxis i) =
      quadrangleAxis i := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero _ hu.ne'
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero _ hv.ne'
  have hdiag (c : ℝ) (a j : Fin 3) : (c • diagAtom a).1 j = c * (diagAtom a).1 j := rfl
  have hoff (c : ℝ) (a j : Fin 3) : (c • diagAtom a).2 j = c • (diagAtom a).2 j := rfl
  fin_cases i
  · apply CubicRayEquiv.pointMap_eq_of_raw _ one_ne_zero
    change diagScale u v (diagAtom 0) = (1 : ℝ) • diagAtom 0
    apply Prod.ext <;> funext j <;> fin_cases j
    all_goals simp only [hdiag, hoff]
    all_goals simp [diagScale, diagAtom]
  · apply CubicRayEquiv.pointMap_eq_of_raw _ hu2
    change diagScale u v (diagAtom 1) = (u ^ 2 : ℝ) • diagAtom 1
    apply Prod.ext <;> funext j <;> fin_cases j
    all_goals simp only [hdiag, hoff]
    all_goals simp [diagScale, diagAtom]
  · apply CubicRayEquiv.pointMap_eq_of_raw _ hv2
    change diagScale u v (diagAtom 2) = (v ^ 2 : ℝ) • diagAtom 2
    apply Prod.ext <;> funext j <;> fin_cases j
    all_goals simp only [hdiag, hoff]
    all_goals simp [diagScale, diagAtom]

private theorem balance_atom_diagonal (x : AlbertAtomSpace) (hx : ∀ i, 0 < x.val.1 i) :
    ∃ g : CubicRayEquiv, (∀ i, g.pointMap (quadrangleAxis i) = quadrangleAxis i) ∧
      ∀ i, (g.pointMap x).val.1 i = 1/3 := by
  let d := x.val.1
  let u := Real.sqrt (d 0 / d 1)
  let v := Real.sqrt (d 0 / d 2)
  have hu := Real.sqrt_pos.mpr (div_pos (hx 0) (hx 1))
  have hv := Real.sqrt_pos.mpr (div_pos (hx 0) (hx 2))
  let g := positiveDiagonalCongruence u v hu hv
  have h1 : u ^ 2 * d 1 = d 0 := by
    dsimp [u]
    rw [Real.sq_sqrt (div_nonneg (hx 0).le (hx 1).le), div_mul_cancel₀ _ (hx 1).ne']
  have h2 : v ^ 2 * d 2 = d 0 := by
    dsimp [v]
    rw [Real.sq_sqrt (div_nonneg (hx 0).le (hx 2).le), div_mul_cancel₀ _ (hx 2).ne']
  have hcoord (i : Fin 3) : (diagScale u v x.val).1 i = d 0 := by
    fin_cases i
    · rfl
    · exact h1
    · exact h2
  have htrace : albertTrace (diagScale u v x.val) = 3 * d 0 := by
    simp only [albertTrace, Fin.sum_univ_three, hcoord]
    ring
  refine ⟨g, positiveDiagonalCongruence_fixes_axes u v hu hv, fun i => ?_⟩
  change (albertTrace (diagScale u v x.val))⁻¹ * (diagScale u v x.val).1 i = 1/3
  rw [htrace, hcoord]
  field_simp [show d 0 ≠ 0 from (hx 0).ne']

private theorem fixed_axes_preserves_diagonal (g : NativeAlbertAutomorphism)
    (hg : ∀ i, g.linearEquiv (diagAtom i) = diagAtom i) (x : Albert) (i : Fin 3) :
    (g.linearEquiv x).1 i = x.1 i := by
  rw [← tracePairing_diagAtom, ← hg i, g.map_tracePairing, tracePairing_diagAtom]

private theorem octNormSq_scalar_eq (r : ℝ) : octNormSq (octonionScalar r) = r^2 := by
  rw [show octonionScalar r = r • octOne by
      change octonionScalar r = r • octonionScalar 1
      rw [← octonionScalar_smul, mul_one],
    octNormSq_smul, octNormSq_one, mul_one]

private theorem octNormSq_first_balanced_slot (x : AlbertAtomSpace)
    (hx : ∀ i, x.val.1 i = 1/3) : octNormSq (x.val.2 0) = (1/3 : ℝ)^2 := by
  have h := congrArg (fun a : Albert => a.1 2) (albertSharp_atom_eq_zero _ x.property)
  change x.val.1 0 * x.val.1 1 - octNormSq (x.val.2 0) = 0 at h
  rw [hx, hx] at h
  linarith

private theorem octNormSq_second_balanced_slot (x : AlbertAtomSpace)
    (hx : ∀ i, x.val.1 i = 1/3) : octNormSq (x.val.2 1) = (1/3 : ℝ)^2 := by
  have h := congrArg (fun a : Albert => a.1 1) (albertSharp_atom_eq_zero _ x.property)
  change x.val.1 0 * x.val.1 2 - octNormSq (x.val.2 1) = 0 at h
  rw [hx, hx] at h
  linarith

private theorem eq_third_of_sq {r : ℝ} (hr : 0 ≤ r) (hs : r^2 = (1/3 : ℝ)^2) :
    r = 1/3 := by
  have h : (r - 1/3) * (r + 1/3) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (by positivity))

private theorem pairing_slot01_one (x : Albert) :
    tracePairing (slotElem01 octOne) x = 2 * octonionReal (x.2 0) := by
  rw [tracePairing_eq_coords]
  change (0 * x.1 0 + 0 * x.1 1 + 0 * x.1 2) +
    2 * (octDot (octonionScalar 1) (x.2 0) + octDot 0 (x.2 1) + octDot 0 (x.2 2)) = _
  simp [octDot_scalar_left, octDot_zero_left]

private theorem balancedRealAtom_offdiag (i : Fin 3) :
    balancedRealAtom.val.2 i = octonionScalar (1/3) := by
  have htr : albertTrace (chartDyad octOne octOne) = 3 := by
    rw [chartDyad_trace, octNormSq_one]
    norm_num
  change (albertTrace (chartDyad octOne octOne))⁻¹ • (chartDyad octOne octOne).2 i = _
  rw [htr]
  have hcoord : (chartDyad octOne octOne).2 i = octOne := by
    fin_cases i <;> exact (by
      change octonionMul (octonionScalar 1) (octonionConj (octonionScalar 1)) = octOne
      rw [octonionConj_scalar, octonionMul_scalar_left, one_smul]
      rfl)
  rw [hcoord, show octOne = octonionScalar 1 from rfl, ← octonionScalar_smul, mul_one, one_div]

private theorem balancedRealAtom_diag (i : Fin 3) :
    balancedRealAtom.val.1 i = 1/3 := by
  have htr : albertTrace (chartDyad octOne octOne) = 3 := by
    rw [chartDyad_trace, octNormSq_one]
    norm_num
  change (albertTrace (chartDyad octOne octOne))⁻¹ * (chartDyad octOne octOne).1 i = _
  have hi : (chartDyad octOne octOne).1 i = 1 := by
    fin_cases i <;> exact octNormSq_one
  rw [htr, hi, mul_one, one_div]

private theorem balanced_atom_to_real (x : AlbertAtomSpace)
    (hx : ∀ i, x.val.1 i = 1/3) :
    ∃ g : NativeAlbertAutomorphism, (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      g.linearEquiv x.val = balancedRealAtom.val := by
  obtain ⟨g, hg, r, hr, hr0⟩ := exists_frameStab_slot01_real x.val
  let y : AlbertAtomSpace := ⟨g.linearEquiv x.val, g.map_isAtom x.property⟩
  have hy (i : Fin 3) : y.val.1 i = 1/3 :=
    (fixed_axes_preserves_diagonal g hg x.val i).trans (hx i)
  change y.val.2 0 = octonionScalar r at hr0
  have hr1 := octNormSq_first_balanced_slot y hy
  rw [hr0, octNormSq_scalar_eq] at hr1
  rw [eq_third_of_sq hr hr1] at hr0
  obtain ⟨k, hk, hk01, s, hs, hs1⟩ := exists_frameAnd01OneStab_slot02_real y.val
  let z : AlbertAtomSpace := ⟨k.linearEquiv y.val, k.map_isAtom y.property⟩
  have hz (i : Fin 3) : z.val.1 i = 1/3 :=
    (fixed_axes_preserves_diagonal k hk y.val i).trans (hy i)
  change z.val.2 1 = octonionScalar s at hs1
  have hs2 := octNormSq_second_balanced_slot z hz
  rw [hs1, octNormSq_scalar_eq] at hs2
  rw [eq_third_of_sq hs hs2] at hs1
  have hre : octonionReal (z.val.2 0) = 1/3 := by
    have h := k.map_tracePairing (slotElem01 octOne) y.val
    rw [hk01] at h
    change tracePairing (slotElem01 octOne) z.val = tracePairing (slotElem01 octOne) y.val at h
    rw [pairing_slot01_one, pairing_slot01_one, hr0, octonionReal_scalar] at h
    linarith
  have hz0 : z.val.2 0 = octonionScalar (1/3) := by
    apply sub_eq_zero.mp
    apply (octNormSq_eq_zero _).mp
    rw [octNormSq_sub, octNormSq_first_balanced_slot z hz, octNormSq_scalar_eq,
      octDot_comm, octDot_scalar_left, hre]
    norm_num
  have hz2 : z.val.2 2 = octonionScalar (1/3) := by
    have h := congrArg (fun a : Albert => a.2 2) (albertSharp_atom_eq_zero _ z.property)
    change octonionMul (octonionConj (z.val.2 0)) (z.val.2 1) - z.val.1 0 • z.val.2 2 = 0 at h
    rw [hz0, hs1, hz, octonionConj_scalar, octonionMul_scalar_left] at h
    exact ((smul_right_inj (by norm_num : (1/3 : ℝ) ≠ 0)).mp (sub_eq_zero.mp h)).symm
  refine ⟨k.comp g, fun i => ?_, ?_⟩
  · change k.linearEquiv (g.linearEquiv (diagAtom i)) = diagAtom i
    rw [hg, hk]
  · change z.val = balancedRealAtom.val
    apply Prod.ext
    · funext i
      rw [hz, balancedRealAtom_diag]
    · funext i
      rw [balancedRealAtom_offdiag]
      fin_cases i
      · exact hz0
      · exact hs1
      · exact hz2

/-- A norm-preserving projective change sends a labelled quadrangle to the real normal form. -/
theorem quadrangle_projective_normal_form (p : Fin 4 → AlbertAtomSpace)
    (hp : p ∈ quadrangleLocus) :
    ∃ g : CubicRayEquiv, g.scale = 1 ∧
      ∀ i, g.pointMap (p i) = standardRealQuadrangle i := by
  obtain ⟨g, hg⟩ := quadrangle_first_three_axes p hp
  let q (i : Fin 4) := g.pointMap (p i)
  have hq : q ∈ quadrangleLocus := g.pointMap_quadrangle hp
  have hlast (i : Fin 3) : 0 < (q 3).val.1 i :=
    lt_of_le_of_ne (isAtom_diag_nonneg (q 3).property i)
      (diagonal_ne_zero_for_fourth q hq hg i).symm
  obtain ⟨h, hh, hb⟩ := balance_atom_diagonal (q 3) hlast
  obtain ⟨k, hk, hkb⟩ := balanced_atom_to_real (h.pointMap (q 3)) hb
  let e := (g.trans h).trans (CubicRayEquiv.ofAutomorphism k)
  refine ⟨e.normalizeNorm, e.normalizeNorm_scale, fun i => ?_⟩
  rw [CubicRayEquiv.pointMap_normalizeNorm]
  change ((g.trans h).trans (CubicRayEquiv.ofAutomorphism k)).pointMap _ = _
  rw [CubicRayEquiv.pointMap_trans, CubicRayEquiv.pointMap_trans]
  apply Subtype.ext
  rw [CubicRayEquiv.pointMap_ofAutomorphism_val]
  have haxes (j : Fin 3) :
      k.linearEquiv (h.pointMap (g.pointMap (p j.castSucc))).val = (diagAtom j) := by
    rw [hg, hh]
    exact hk j
  fin_cases i
  · exact haxes 0
  · exact haxes 1
  · exact haxes 2
  · exact hkb

/-- The cubic-norm-preserving projective action is transitive on ordered quadrangles. -/
theorem quadrangle_projective_transitive (p q : Fin 4 → AlbertAtomSpace)
    (hp : p ∈ quadrangleLocus) (hq : q ∈ quadrangleLocus) :
    ∃ g : CubicRayEquiv, g.scale = 1 ∧ ∀ i, g.pointMap (p i) = q i := by
  obtain ⟨g, _, hg⟩ := quadrangle_projective_normal_form p hp
  obtain ⟨h, _, hh⟩ := quadrangle_projective_normal_form q hq
  refine ⟨(g.trans h.symm).normalizeNorm, CubicRayEquiv.normalizeNorm_scale _, fun i => ?_⟩
  rw [CubicRayEquiv.pointMap_normalizeNorm, CubicRayEquiv.pointMap_trans, hg, ← hh]
  exact h.symm_pointMap (q i)

/-- Every continuous projective invariant of ordered four-point configurations is constant. -/
theorem continuous_projective_four_point_invariant_constant
    (f : (Fin 4 → AlbertAtomSpace) → ℝ) (hf : Continuous f)
    (hi : ∀ (g : CubicRayEquiv), g.scale = 1 →
      ∀ p, f (fun i => g.pointMap (p i)) = f p) :
    ∀ p, f p = f standardRealQuadrangle := by
  apply constant_of_dense_locus _ quadrangleLocus_dense f hf _
  intro p hp
  obtain ⟨g, hg, he⟩ := quadrangle_projective_normal_form p hp
  rw [← hi g hg p, funext he]

end AlbertSequential.ProjectiveMetricInvariant
