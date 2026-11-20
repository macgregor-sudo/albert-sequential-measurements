/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfBoost
import NativeIdempotentClassification
import DiagPeirceAnchor
import Mathlib.Tactic.Module
import Mathlib.Analysis.Matrix.PosDef

/-! The two exact spectral coordinates and the forward cone of the atomic corner. -/
@[expose] public section
noncomputable section

open scoped Matrix BigOperators
open Polynomial

namespace AlbertSequential.NativeAnalysis

private theorem trace_cornerUnit (p : Albert) (hp : IsAtom p) :
    albertTrace (nativeCornerUnit p hp.1) = 2 := by
  change albertTrace (albertUnit - p) = _
  rw [albertTrace_sub, albertTrace_unit, hp.2]
  norm_num

private theorem cornerUnit_mul (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    jordanMul (nativeCornerUnit p hp.1) x = x := by
  change jordanMul (albertUnit - p) x = x
  rw [jordanMul_sub_left, jordanMul_albertUnit_left,
    (mem_nativePeirceZero _ _).mp x.property, sub_zero]

/-- The time coordinate of a spin factor is half the native trace. -/
def nativeCornerTime (x : Albert) : ℝ := albertTrace x / 2

/-- The spatial component in the actual corner, centered at its own unit. -/
def nativeCornerCentered (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    nativePeirceZero p := x - nativeCornerTime x • nativeCornerUnit p hp.1

/-- The Euclidean length of the spatial component in the paper's normalization. -/
def nativeCornerRadius (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) : ℝ :=
  let v := nativeCornerCentered p hp x
  Real.sqrt (tracePairing v v / 2)

private theorem nativeCornerCentered_trace (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    albertTrace (nativeCornerCentered p hp x) = 0 := by
  change albertTrace ((x : Albert) - nativeCornerTime x • (nativeCornerUnit p hp.1 : Albert)) = _
  rw [albertTrace_sub, albertTrace_smul, trace_cornerUnit p hp]
  unfold nativeCornerTime
  ring

/-- Every traceless vector in the actual atomic corner squares to its spin
norm squared times the corner unit. -/
theorem nativeCorner_traceless_square (p : Albert) (hp : IsAtom p) (v : nativePeirceZero p)
    (hv : albertTrace v = 0) :
    jordanMul v v = (tracePairing v v / 2) • (nativeCornerUnit p hp.1 : Albert) := by
  have hs := albertSharp_nativeCorner p hp v
  rw [albertSharp_eq_jordanMul, hv, zero_smul, sub_zero] at hs
  unfold nativeCornerLorentz at hs
  simp only [hv, zero_pow (by decide : (2:ℕ) ≠ 0), zero_sub] at hs
  change jordanMul v v = (tracePairing v v / 2) • (albertUnit - p)
  rw [smul_sub]
  calc
    jordanMul v v = jordanMul v v + ((1 / 2 : ℝ) * -tracePairing v v) • albertUnit -
        ((1 / 2 : ℝ) * -tracePairing v v) • albertUnit := by abel
    _ = _ := by rw [hs]; module

private theorem tracePairing_cornerUnit (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    tracePairing (nativeCornerUnit p hp.1) x = albertTrace x := by
  unfold tracePairing
  rw [cornerUnit_mul p hp x]

/-- In the normalized octonionic chart the squared radius is the printed
sum of the squared diagonal difference and octonionic norm squared. -/
theorem nativeCorner_time_radius_coordinates (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    let z := (chosenAtomNormalizer p hp).linearEquiv (x : Albert)
    nativeCornerTime x = (z.1 1 + z.1 2) / 2 ∧
      nativeCornerRadius p hp x ^ 2 = ((z.1 1 - z.1 2) / 2) ^ 2 + octNormSq (z.2 2) := by
  intro z
  have htr := (chosenAtomNormalizer p hp).preserves_trace (x : Albert)
  change albertTrace z = albertTrace x at htr
  change (∑ i : Fin 3, z.1 i) = albertTrace x at htr
  rw [Fin.sum_univ_three, native_normalized_corner_first_zero p hp x, zero_add] at htr
  have ht : nativeCornerTime x = (z.1 1 + z.1 2) / 2 := by rw [htr]; rfl
  refine ⟨ht, ?_⟩
  let a := nativeCornerTime x
  let u := nativeCornerUnit p hp.1
  let v := nativeCornerCentered p hp x
  have hr : nativeCornerRadius p hp x ^ 2 = tracePairing v v / 2 :=
    Real.sq_sqrt (div_nonneg (tracePairing_self_nonneg _) (by norm_num))
  have hvv : tracePairing v v / 2 = tracePairing x x / 2 - a^2 := by
    change tracePairing ((x : Albert) - a • (u : Albert)) ((x : Albert) - a • (u : Albert)) / 2 = _
    have hxu := tracePairing_cornerUnit p hp x
    change tracePairing (u : Albert) (x : Albert) = _ at hxu
    have huu := tracePairing_cornerUnit p hp u
    change tracePairing (u : Albert) (u : Albert) = _ at huu
    rw [trace_cornerUnit p hp] at huu
    rw [tracePairing_sub_left, tracePairing_sub_right, tracePairing_sub_right,
      tracePairing_smul_left, tracePairing_smul_left, tracePairing_smul_right, tracePairing_smul_right,
      tracePairing_comm (x : Albert) (u : Albert), hxu, huu]
    unfold a nativeCornerTime
    ring
  have hq := nativeCornerLorentz_eq_Minkowski p hp x
  change nativeCornerLorentz x = ((z.1 1 + z.1 2) / 2) ^ 2 - _ at hq
  unfold nativeCornerLorentz at hq
  rw [← ht] at hq
  rw [hr, hvv]
  unfold a nativeCornerTime at *
  linarith

private theorem corner_complementary_atoms (p : Albert) (hp : IsAtom p) :
    ∃ a b : nativePeirceZero p, IsAtom a ∧ IsAtom b ∧
      a + b = nativeCornerUnit p hp.1 := by
  let g := nativeAutomorphismInverse (chosenAtomNormalizer p hp)
  have hgp : g.linearEquiv (diagAtom 0) = p := by
    change (chosenAtomNormalizer p hp).linearEquiv.symm (diagAtom 0) = p
    rw [← atomNormalizer_first p hp, LinearEquiv.symm_apply_apply]
  have hmem (i : Fin 3) (hi : 0 ≠ i) : g.linearEquiv (diagAtom i) ∈ nativePeirceZero p := by
    rw [mem_nativePeirceZero, ← hgp, ← g.preserves_product, diagAtom_orthogonal hi, map_zero]
  let a : nativePeirceZero p := ⟨g.linearEquiv (diagAtom 1), hmem 1 (by decide)⟩
  let b : nativePeirceZero p := ⟨g.linearEquiv (diagAtom 2), hmem 2 (by decide)⟩
  refine ⟨a,b, nativeAutomorphism_isAtom g _ (diagAtom_isAtom _),
    nativeAutomorphism_isAtom g _ (diagAtom_isAtom _), Subtype.ext ?_⟩
  change g.linearEquiv (diagAtom 1) + g.linearEquiv (diagAtom 2) = albertUnit - p
  have hu := congrArg g.linearEquiv diagAtom_sum_eq_unit
  rw [Fin.sum_univ_three, map_add, map_add, g.preserves_unit, hgp] at hu
  apply eq_sub_of_add_eq'
  simpa only [add_assoc] using hu

/-- Two orthogonal atoms in the corner resolve its unit, and the native
spectral coefficients are the printed time plus and minus the radius. -/
theorem nativeCorner_spectralAtoms (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    ∃ a b : nativePeirceZero p, IsAtom a ∧ IsAtom b ∧ jordanMul a b = 0 ∧
      a + b = nativeCornerUnit p hp.1 ∧
      x = (nativeCornerTime x + nativeCornerRadius p hp x) • a +
        (nativeCornerTime x - nativeCornerRadius p hp x) • b := by
  let t := nativeCornerTime x
  let r := nativeCornerRadius p hp x
  let v := nativeCornerCentered p hp x
  let u := nativeCornerUnit p hp.1
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = tracePairing v v / 2 := Real.sq_sqrt
    (div_nonneg (tracePairing_self_nonneg _) (by norm_num))
  have hvt := nativeCornerCentered_trace p hp x
  have hv : jordanMul (v : Albert) v = (r ^ 2) • (u : Albert) := by
    rw [hrsq]
    exact nativeCorner_traceless_square p hp v hvt
  have hpair (a b : nativePeirceZero p) (ha : IsAtom a) (hs : a+b = u) : jordanMul a b = 0 := by
    have hab : (b : Albert) = (u : Albert) - (a : Albert) :=
      (eq_sub_of_add_eq' (congrArg Subtype.val hs : (a : Albert) + (b : Albert) = (u : Albert)))
    rw [hab, jordanMul_sub_right, jordanMul_comm (a : Albert) (u : Albert), cornerUnit_mul p hp a,
      ha.1, sub_self]
  by_cases hz : r = 0
  · have hv0 : v = 0 := Subtype.ext ((tracePairing_self_eq_zero (v : Albert)).mp (by
      rw [hz] at hrsq
      linarith))
    obtain ⟨a,b,ha,hb,hs⟩ := corner_complementary_atoms p hp
    refine ⟨a,b,ha,hb,hpair a b ha hs,hs,?_⟩
    change x = (t + r) • a + (t - r) • b
    rw [hz, add_zero, sub_zero, ← smul_add, hs]
    exact sub_eq_zero.mp hv0
  · let d := r⁻¹ • v
    let a := (1/2 : ℝ) • (u + d)
    let b := (1/2 : ℝ) • (u - d)
    have hsum : a + b = u := by dsimp only [a,b]; module
    have hdx : (d : Albert) = r⁻¹ • (v : Albert) := rfl
    have hdd : jordanMul (d : Albert) d = (u : Albert) := by
      rw [hdx, jordanMul_smul_left, jordanMul_smul_right, hv, smul_smul, smul_smul]
      rw [show r⁻¹ * r⁻¹ * r^2 = 1 by field_simp [hz], one_smul]
    have hdt : albertTrace (d : Albert) = 0 := by rw [hdx, albertTrace_smul, hvt, mul_zero]
    have huu := cornerUnit_mul p hp u
    have hud := cornerUnit_mul p hp d
    change jordanMul (u : Albert) u = (u : Albert) at huu
    change jordanMul (u : Albert) d = (d : Albert) at hud
    have hdu := (jordanMul_comm (d : Albert) (u : Albert)).trans hud
    have huc := trace_cornerUnit p hp
    have ha : IsAtom a := by
      constructor
      · change jordanMul ((1/2 : ℝ) • ((u : Albert) + (d : Albert)))
          ((1/2 : ℝ) • ((u : Albert) + (d : Albert))) = _
        simp only [jordanMul_smul_left, jordanMul_smul_right, jordanMul_add_left,
          jordanMul_add_right, huu, hud, hdu, hdd]
        change _ = (1/2 : ℝ) • ((u : Albert) + (d : Albert))
        module
      · change albertTrace ((1/2 : ℝ) • ((u : Albert) + (d : Albert))) = _
        rw [albertTrace_smul, albertTrace_add, huc, hdt]
        norm_num
    have hb : IsAtom b := by
      constructor
      · change jordanMul ((1/2 : ℝ) • ((u : Albert) - (d : Albert)))
          ((1/2 : ℝ) • ((u : Albert) - (d : Albert))) = _
        simp only [jordanMul_smul_left, jordanMul_smul_right, jordanMul_sub_left,
          jordanMul_sub_right, huu, hud, hdu, hdd]
        change _ = (1/2 : ℝ) • ((u : Albert) - (d : Albert))
        module
      · change albertTrace ((1/2 : ℝ) • ((u : Albert) - (d : Albert))) = _
        rw [albertTrace_smul, albertTrace_sub, huc, hdt]
        norm_num
    refine ⟨a,b,ha,hb,hpair a b ha hsum,hsum,?_⟩
    have hrd : r • d = v := by rw [show d = _ from rfl, smul_smul, mul_inv_cancel₀ hz, one_smul]
    calc
      x = t • u + v := by dsimp only [v, nativeCornerCentered]; module
      _ = t • u + r • d := by rw [hrd]
      _ = (t+r) • a + (t-r) • b := by dsimp only [a,b]; module

/-- Positivity in the actual Albert corner is exactly the forward-cone
inequality in the paper's spectral coordinates. -/
theorem nativeCorner_positive_iff_forwardCone (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) : IsPositive (x : Albert) ↔ nativeCornerRadius p hp x ≤ nativeCornerTime x := by
  obtain ⟨a,b,ha,hb,hab,_,he⟩ := nativeCorner_spectralAtoms p hp x
  let t := nativeCornerTime x
  let r := nativeCornerRadius p hp x
  change IsPositive (x : Albert) ↔ r ≤ t
  have hcoe : (x : Albert) = (t+r) • (a : Albert) + (t-r) • (b : Albert) := congrArg Subtype.val he
  have ha' : IsPositive (a : Albert) := isPositive_idempotent _ ha.1
  have hb' : IsPositive (b : Albert) := isPositive_idempotent _ hb.1
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  constructor
  · intro hx
    have h := tracePairing_positive_nonnegative (x : Albert) (b : Albert) hx hb'
    rw [hcoe, tracePairing_add_left, tracePairing_smul_left, tracePairing_smul_left] at h
    have hab' : tracePairing (a : Albert) b = 0 := by
      rw [tracePairing, hab, albertTrace_zero]
    have hbb : tracePairing (b : Albert) b = 1 := by rw [tracePairing, hb.1, hb.2]
    rw [hab', hbb, mul_zero, zero_add, mul_one] at h
    linarith
  · intro h
    rw [hcoe]
    exact isPositive_add _ _ (isPositive_smul _ _ (by linarith) ha')
      (isPositive_smul _ _ (sub_nonneg.mpr h) hb')

theorem nativeCorner_positive_iff_chartForwardCone (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p) :
    let z := (chosenAtomNormalizer p hp).linearEquiv (x : Albert)
    IsPositive (x : Albert) ↔
      Real.sqrt (((z.1 1 - z.1 2) / 2) ^ 2 + octNormSq (z.2 2)) ≤ (z.1 1 + z.1 2) / 2 := by
  intro z
  obtain ⟨ht, hr⟩ := nativeCorner_time_radius_coordinates p hp x
  change nativeCornerTime x = (z.1 1 + z.1 2) / 2 at ht
  change nativeCornerRadius p hp x ^ 2 = ((z.1 1 - z.1 2) / 2) ^ 2 + octNormSq (z.2 2) at hr
  rw [nativeCorner_positive_iff_forwardCone p hp x, ← ht, ← hr,
    Real.sqrt_sq (show 0 ≤ nativeCornerRadius p hp x from Real.sqrt_nonneg _)]

/-- The real sixteen-dimensional Clifford matrix has the two printed
corner eigenvalues with eight copies apiece, including coincident roots. -/
theorem nativeHalfMatrix_corner_charpoly (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    let t := nativeCornerTime x
    let r := nativeCornerRadius p hp x
    (nativeHalfMatrix p hp x).charpoly = (X - C (t+r))^8 * (X - C (t-r))^8 := by
  classical
  intro t r
  obtain ⟨a,b,ha,_,_,hs,he⟩ := nativeCorner_spectralAtoms p hp x
  let A := nativeHalfMatrix p hp x
  let P := nativeHalfMatrix p hp a
  let M := nativeHalfMatrix p hp
  have hP : Matrix.IsHermitian P := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      nativeHalfMatrix_symmetric p hp a
  have hP2 : P * P = P := by
    change M a * M a = M a
    rw [← nativeHalfMatrix_square]
    exact congrArg M (Subtype.ext ha.1)
  have hPt : Matrix.trace P = 8 := by
    change Matrix.trace (nativeHalfMatrix p hp a) = _
    rw [nativeHalfMatrix_trace, ha.2, mul_one]
  have hMb : M b = 1 - P := by
    have h := congrArg M hs
    rw [map_add, nativeHalfMatrix_unit] at h
    exact eq_sub_of_add_eq' h
  let F := Unitary.conjStarAlgAut ℝ (Matrix SpinorCoordinate SpinorCoordinate ℝ)
    (star hP.eigenvectorUnitary)
  have hdiag : F P = Matrix.diagonal hP.eigenvalues := by
    simpa only [F, RCLike.ofReal_real_eq_id, Function.id_comp] using
      hP.conjStarAlgAut_star_eigenvectorUnitary
  have hdiagSq := congrArg F hP2
  rw [map_mul, hdiag, Matrix.diagonal_mul_diagonal] at hdiagSq
  have hvals (i : SpinorCoordinate) : hP.eigenvalues i = 1 ∨ hP.eigenvalues i = 0 := by
    have hi := congrArg (fun M : NativeSpinorMatrix => M i i) hdiagSq
    simp only [Matrix.diagonal_apply_eq] at hi
    have hprod : hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 := by linear_combination hi
    exact ((mul_eq_zero.mp hprod).imp id sub_eq_zero.mp).symm
  let s := Finset.univ.filter (fun i => hP.eigenvalues i = 1)
  let u := Finset.univ.filter (fun i => hP.eigenvalues i ≠ 1)
  have htrace : ∑ i, hP.eigenvalues i = 8 := by
    simpa only [hP.trace_eq_sum_eigenvalues, RCLike.ofReal_real_eq_id, id_eq] using hPt
  have hsum : ∑ i, hP.eigenvalues i = (s.card : ℝ) := by
    calc
      _ = ∑ i, if hP.eigenvalues i = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : hP.eigenvalues i = 1
        · simp [h]
        · simp [(hvals i).resolve_left h]
      _ = _ := by rw [← Finset.sum_filter]; simp [s]
  have hs8 : s.card = 8 := by exact_mod_cast hsum.symm.trans htrace
  have hcard : s.card + u.card = 16 := by
    simpa only [s, u, Finset.card_univ, spinorCoordinate_card] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset SpinorCoordinate))
        (fun i => hP.eigenvalues i = 1)
  have hu8 : u.card = 8 := by omega
  let w := fun i : SpinorCoordinate => (t+r) * hP.eigenvalues i + (t-r) * (1 - hP.eigenvalues i)
  have hdiagA : F A = Matrix.diagonal w := by
    have h := congrArg M he
    change A = M ((t+r) • a + (t-r) • b) at h
    rw [map_add, map_smul, map_smul, hMb] at h
    rw [h, map_add, map_smul, map_smul, map_sub, map_one, hdiag, ← Matrix.diagonal_one,
      Matrix.diagonal_sub, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    rfl
  have hchar : (F A).charpoly = A.charpoly := by
    let Q := Unitary.toUnits (star hP.eigenvectorUnitary)
    change (Q.val * A * (↑Q⁻¹ : NativeSpinorMatrix)).charpoly = _
    rw [Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj Q A
  rw [← hchar, hdiagA, Matrix.charpoly_diagonal,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => hP.eigenvalues i = 1)]
  change (∏ i ∈ s, (X - C (w i))) * (∏ i ∈ u, (X - C (w i))) = _
  congr 1
  · rw [← hs8, ← Finset.prod_const (s := s)]
    apply Finset.prod_congr rfl
    intro i hi
    simp [w, (Finset.mem_filter.mp hi).2]
  · rw [← hu8, ← Finset.prod_const (s := u)]
    apply Finset.prod_congr rfl
    intro i hi
    simp [w, (hvals i).resolve_left (Finset.mem_filter.mp hi).2]

end AlbertSequential.NativeAnalysis
