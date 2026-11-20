/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeHalfExchangeMatrix
public import FrameSlotNormalizers
public import NativeDensityCompactness
public import NativeWordDuality
import NativeIdempotentClassification
import AppF.ExactModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! The Lorentz quadratic and bilinear similitude of the actual native corner transition. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.NativeAnalysis
open AppF

def nativeCornerLorentz (x : Albert) : ℝ :=
  (albertTrace x ^ 2 - tracePairing x x) / 2

def nativeCornerLorentzForm (x y : Albert) : ℝ :=
  (albertTrace x * albertTrace y - tracePairing x y) / 2

private theorem firstNo_coordinate_projection (x : Albert) :
    quadraticMap (albertUnit - diagAtom 0) x =
      ((![0, x.1 1, x.1 2], ![0, 0, x.2 2]) : Albert) := by
  rw [quadraticMap_complement, first_atom_mul, quadraticMap_atom _ _ (diagAtom_isAtom 0),
    tracePairing_diagAtom]
  apply albert_ext'
  · change x.1 0 - 2 * x.1 0 + x.1 0 * 1 = 0
    ring
  · change x.1 1 - 2 * 0 + x.1 0 * 0 = x.1 1
    ring
  · change x.1 2 - 2 * 0 + x.1 0 * 0 = x.1 2
    ring
  · change x.2 0 - (2 : ℝ) • ((1 / 2 : ℝ) • x.2 0) + x.1 0 • (0 : Octonion) = 0
    module
  · change x.2 1 - (2 : ℝ) • ((1 / 2 : ℝ) • x.2 1) + x.1 0 • (0 : Octonion) = 0
    module
  · change x.2 2 - (2 : ℝ) • (0 : Octonion) + x.1 0 • (0 : Octonion) = x.2 2
    module

private theorem firstCorner_coordinates (x : nativePeirceZero (diagAtom 0)) :
    x.val.1 0 = 0 ∧ x.val.2 0 = 0 ∧ x.val.2 1 = 0 := by
  have he := native_complement_quadratic_fixed_zero (diagAtom 0) x (diagAtom_isAtom 0).1 x.property
  rw [firstNo_coordinate_projection] at he
  exact ⟨(congrArg (fun y : Albert => y.1 0) he).symm,
    (congrArg (fun y : Albert => y.2 0) he).symm, (congrArg (fun y : Albert => y.2 1) he).symm⟩

private theorem firstCornerLorentz_eq (x : nativePeirceZero (diagAtom 0)) :
    nativeCornerLorentz x = x.val.1 1 * x.val.1 2 - octNormSq (x.val.2 2) := by
  obtain ⟨h0, h1, h2⟩ := firstCorner_coordinates x
  unfold nativeCornerLorentz
  rw [tracePairing_eq_coords]
  have ht : albertTrace x = x.val.1 1 + x.val.1 2 := by
    unfold albertTrace
    rw [Fin.sum_univ_three, h0, zero_add]
  rw [ht, h0, h1, h2, octDot_zero_left]
  unfold octNormSq
  ring

private theorem nativeCornerLorentz_automorphism (g : NativeAlbertAutomorphism) (x : Albert) :
    nativeCornerLorentz (g.linearEquiv x) = nativeCornerLorentz x := by
  unfold nativeCornerLorentz
  rw [g.preserves_trace, g.map_tracePairing]

private def firstCornerImage (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    nativePeirceZero (diagAtom 0) :=
  ⟨(chosenAtomNormalizer p hp).linearEquiv x, by
    let g := chosenAtomNormalizer p hp
    change jordanMul (diagAtom 0) (g.linearEquiv x) = 0
    rw [← atomNormalizer_first p hp, ← g.preserves_product,
      (mem_nativePeirceZero p x).mp x.property, map_zero]⟩

/-- The actual trace form is the printed Minkowski quadratic form in the native
diagonal and octonionic spatial coordinates. -/
theorem nativeCornerLorentz_eq_Minkowski (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    let z := (chosenAtomNormalizer p hp).linearEquiv (x : Albert)
    nativeCornerLorentz x =
      ((z.1 1 + z.1 2) / 2) ^ 2 - (((z.1 1 - z.1 2) / 2) ^ 2 + octNormSq (z.2 2)) := by
  intro z
  rw [← nativeCornerLorentz_automorphism (chosenAtomNormalizer p hp) (x : Albert)]
  change nativeCornerLorentz (firstCornerImage p hp x) = _
  rw [firstCornerLorentz_eq]
  change z.1 1 * z.1 2 - octNormSq (z.2 2) = _
  ring

private theorem albertSharp_firstCorner (x : nativePeirceZero (diagAtom 0)) :
    albertSharp x = nativeCornerLorentz x • diagAtom 0 := by
  obtain ⟨h0, h1, h2⟩ := firstCorner_coordinates x
  rw [firstCornerLorentz_eq]
  apply albert_ext' <;>
    simp only [albert_smul_fst', albert_smul_snd'] <;>
    simp [albertSharp, diagAtom,
      h0, h1, h2, octNormSq, octDot_zero_left, octonionMul_zero_left, octonionMul_zero_right,
      octonionConj_zero]

/-- The rank-two corner's Freudenthal adjoint points along its missing atom. -/
theorem albertSharp_nativeCorner (p : Albert) (hp : IsAtom p) (x : nativePeirceZero p) :
    albertSharp x = nativeCornerLorentz x • p := by
  let g := chosenAtomNormalizer p hp
  apply g.linearEquiv.injective
  rw [g.map_sharp, map_smul, atomNormalizer_first p hp]
  change albertSharp (firstCornerImage p hp x) = nativeCornerLorentz x • diagAtom 0
  rw [albertSharp_firstCorner]
  exact congrArg (fun t : ℝ => t • diagAtom 0) (nativeCornerLorentz_automorphism g (x : Albert))

private theorem firstNo_sharp_compression (x : Albert) :
    albertSharp (quadraticMap (albertUnit - diagAtom 0) x) =
      tracePairing (diagAtom 0) (albertSharp x) • diagAtom 0 := by
  have h := albertSharp_firstCorner
    ⟨quadraticMap (albertUnit - diagAtom 0) x,
      native_complement_quadratic_mem_zero _ _ (diagAtom_isAtom 0).1⟩
  rw [firstCornerLorentz_eq] at h
  change albertSharp (quadraticMap (albertUnit - diagAtom 0) x) =
    (((quadraticMap (albertUnit - diagAtom 0) x).1 1) *
      ((quadraticMap (albertUnit - diagAtom 0) x).1 2) -
      octNormSq ((quadraticMap (albertUnit - diagAtom 0) x).2 2)) • diagAtom 0 at h
  rw [firstNo_coordinate_projection] at h
  rw [tracePairing_diagAtom, firstNo_coordinate_projection]
  exact h

/-- The Freudenthal composition identity in the exact atomic complement case
used in Appendix D, for an arbitrary native input. -/
theorem albertSharp_atomComplementQuadratic (q : Albert) (hq : IsAtom q) (x : Albert) :
    albertSharp (quadraticMap (albertUnit - q) x) = quadraticMap q (albertSharp x) := by
  let g := chosenAtomNormalizer q hq
  rw [quadraticMap_atom q _ hq]
  apply g.linearEquiv.injective
  rw [g.map_sharp, g.map_quadraticMap, map_sub, g.preserves_unit, map_smul,
    atomNormalizer_first q hq]
  rw [firstNo_sharp_compression]
  have h := g.map_tracePairing q (albertSharp x)
  rw [atomNormalizer_first q hq, g.map_sharp] at h
  rw [h]

theorem nativeCornerLorentz_no_similitude (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (x : nativePeirceZero p) :
    nativeCornerLorentz (nativeCornerNoUpdate p q hq x) =
      tracePairing p q * nativeCornerLorentz x := by
  have h := albertSharp_nativeCorner q hq (nativeCornerNoUpdate p q hq x)
  change albertSharp (quadraticMap (albertUnit - q) x) =
    nativeCornerLorentz (nativeCornerNoUpdate p q hq x) • q at h
  rw [albertSharp_atomComplementQuadratic _ hq, albertSharp_nativeCorner p hp x,
    quadraticMap_smul_right, quadraticMap_atom q p hq, tracePairing_comm q p, smul_smul,
    mul_comm (nativeCornerLorentz x) (tracePairing p q)] at h
  have ht := congrArg albertTrace h
  simpa only [albertTrace_smul, hq.2, mul_one] using ht.symm

private theorem nativeCornerLorentz_polarize (x y : Albert) :
    nativeCornerLorentz (x + y) =
      nativeCornerLorentz x + nativeCornerLorentz y + 2 * nativeCornerLorentzForm x y := by
  unfold nativeCornerLorentz nativeCornerLorentzForm
  simp only [albertTrace_add, tracePairing_add_left, tracePairing_add_right, tracePairing_comm y x]
  ring

/-- The polarized identity is the coordinate equation `Mᵀ η M = o η`. -/
theorem nativeCornerLorentzForm_no_similitude (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (x y : nativePeirceZero p) :
    nativeCornerLorentzForm (nativeCornerNoUpdate p q hq x) (nativeCornerNoUpdate p q hq y) =
      tracePairing p q * nativeCornerLorentzForm x y := by
  have h := nativeCornerLorentz_no_similitude p q hp hq (x + y)
  rw [map_add] at h
  change nativeCornerLorentz
      ((nativeCornerNoUpdate p q hq x : Albert) + (nativeCornerNoUpdate p q hq y : Albert)) = _ at h
  change _ = tracePairing p q * nativeCornerLorentz ((x : Albert) + (y : Albert)) at h
  rw [nativeCornerLorentz_polarize, nativeCornerLorentz_polarize,
    nativeCornerLorentz_no_similitude p q hp hq x,
    nativeCornerLorentz_no_similitude p q hp hq y] at h
  linarith

private def firstCornerEquiv (p : Albert) (hp : IsAtom p) :
    nativePeirceZero p ≃ₗ[ℝ] nativePeirceZero (diagAtom 0) where
  toFun := firstCornerImage p hp
  invFun y := ⟨(chosenAtomNormalizer p hp).linearEquiv.symm y, by
    let g := chosenAtomNormalizer p hp
    change jordanMul p (g.linearEquiv.symm y) = 0
    apply g.linearEquiv.injective
    rw [g.preserves_product, atomNormalizer_first p hp, LinearEquiv.apply_symm_apply,
      (mem_nativePeirceZero _ _).mp y.property, map_zero]⟩
  left_inv x := Subtype.ext ((chosenAtomNormalizer p hp).linearEquiv.symm_apply_apply x)
  right_inv y := Subtype.ext ((chosenAtomNormalizer p hp).linearEquiv.apply_symm_apply y)
  map_add' x y := Subtype.ext ((chosenAtomNormalizer p hp).linearEquiv.map_add x y)
  map_smul' r x := Subtype.ext ((chosenAtomNormalizer p hp).linearEquiv.map_smul r x)

theorem nativeCornerLorentzForm_nondegenerate (p : Albert) (hp : IsAtom p)
    (x : nativePeirceZero p)
    (hx : ∀ y : nativePeirceZero p, nativeCornerLorentzForm (x : Albert) y = 0) : x = 0 := by
  have ht : albertTrace (albertUnit - p) = 2 := by
    rw [albertTrace_sub, albertTrace_unit, hp.2]
    norm_num
  have hxp : tracePairing (x : Albert) p = 0 := by
    rw [tracePairing_comm, tracePairing, (mem_nativePeirceZero p x).mp x.property, albertTrace_zero]
  have hunit : tracePairing (x : Albert) (albertUnit - p) = albertTrace x := by
    rw [tracePairing_sub_right, tracePairing_unit_right, hxp, sub_zero]
  have hy := hx (nativeCornerUnit p hp.1)
  change (albertTrace x * albertTrace (albertUnit - p) -
      tracePairing (x : Albert) (albertUnit - p)) / 2 = 0 at hy
  rw [ht, hunit] at hy
  have htx : albertTrace x = 0 := by linarith
  have hxx := hx x
  unfold nativeCornerLorentzForm at hxx
  rw [htx] at hxx
  exact Subtype.ext ((tracePairing_self_eq_zero _).mp (by linarith))

/-- Positive overlap gives an actual linear bijection of the two corners. -/
theorem nativeCornerNoUpdate_bijective_of_overlap (p q : Albert) (hp : IsAtom p) (hq : IsAtom q)
    (ho : 0 < tracePairing p q) : Function.Bijective (nativeCornerNoUpdate p q hq) := by
  let T := nativeCornerNoUpdate p q hq
  have hi : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x h
    apply nativeCornerLorentzForm_nondegenerate p hp x
    intro y
    have hsim := nativeCornerLorentzForm_no_similitude p q hp hq x y
    change nativeCornerLorentzForm (T x : Albert) (T y : Albert) =
      tracePairing p q * nativeCornerLorentzForm (x : Albert) (y : Albert) at hsim
    rw [h] at hsim
    change nativeCornerLorentzForm 0 (T y : Albert) = _ at hsim
    have hz : tracePairing (0 : Albert) (T y : Albert) = 0 := by
      change albertTrace (jordanMul 0 (T y : Albert)) = 0
      rw [jordanMul_zero_left, albertTrace_zero]
    simp only [nativeCornerLorentzForm, albertTrace_zero, zero_mul, hz, sub_zero, zero_div] at hsim
    exact (mul_eq_zero.mp hsim.symm).resolve_left ho.ne'
  let e := (firstCornerEquiv p hp).trans (firstCornerEquiv q hq).symm
  let _ : FiniteDimensional ℝ Octonion := octonionRealCoordinates.symm.finiteDimensional
  let _ : FiniteDimensional ℝ Albert :=
    inferInstanceAs (FiniteDimensional ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
  have hs : Function.Surjective (e.symm.toLinearMap.comp T) :=
    LinearMap.surjective_of_injective (e.symm.injective.comp hi)
  refine ⟨hi, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hs (e.symm y)
  exact ⟨x, e.symm.injective hx⟩

theorem nativeCornerNoUpdate_preserves_positive (p q : Albert) (hq : IsAtom q)
    (x : nativePeirceZero p) (hx : IsPositive x) : IsPositive (nativeCornerNoUpdate p q hq x) :=
  isPositive_quadraticMap _ _ hx

end AlbertSequential.NativeAnalysis
