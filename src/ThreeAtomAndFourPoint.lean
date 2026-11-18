/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Defs
public import NativeAlbertLaws
public import DiagPeirceAnchor
public import NativeMatrixTrace
public import NativeDensityCompactness
public import NativeWordDuality
public import NativeSquareCone
public import NativeWordPositivity
public import ComplexPositiveFactor
public import Interfaces.WordsAndCertificates
public import Interfaces.Geometry
public import Interfaces.SeparationAndConverse
public import OctonionGeometry
public import FrameSlotNormalizers
public import AcceptedRootAtomAdapter
public import ThirteenTracesAndAform
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Three-Atom Complex Containment, Four-Point Criterion, and Conditional No-Go

Formalizes:
- Overlap/orthogonality trichotomy, dyad extraction, strong `lemma_A_three`,
  orthogonal complex-window projection `windowProj`, `complexRestrictionContract_holds`
  (`lem:A:restrict`), and `complexTripleContract_holds` (`prop:three`, unconditional for all
  triples including coincident and orthogonal atoms, single `σ` chosen before test families).
- `lemma_A_normal` (`lem:A:normal`), `lemma_A_degenerate` (`lem:A:degenerate`),
  `lemma_A_zero_of_quat` & `lemma_A_zero_of_factor` (`lem:A:zero`),
  `lemma_A_generate_three` & `lemma_A_generate_four` (`lem:A:generate`),
  full `thm_fourpoint` (i)–(iv), conditional `cor:fp:noideal`, and the explicit `ℂ^6`
  symplectic rank-2 model `fourPoint_zero_c6_representation` for `fourPointInvariant p = 0`.

No `Mul`, `One`, `Star`, or `Norm` instance is installed on `Octonion` or `Albert`.
-/

@[expose] public section
noncomputable section

open scoped ComplexOrder

namespace AlbertSequential

open NativeAnalysis

/-! ## Section 1: Basic Coordinate Helpers and Atom Overlap/Orthogonality Trichotomy -/

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

private theorem oct_ext {x y : Octonion}
    (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
    (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK)
    (h5 : x.2.re = y.2.re) (h6 : x.2.imI = y.2.imI)
    (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

private theorem albert_zero_fst (j : Fin 3) : (0 : Albert).1 j = 0 := rfl
private theorem albert_zero_snd (k : Fin 3) : (0 : Albert).2 k = 0 := rfl
private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem albert_neg_fst (x : Albert) (j : Fin 3) : (-x).1 j = -x.1 j := rfl
private theorem albert_neg_snd (x : Albert) (k : Fin 3) : (-x).2 k = -x.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl
private theorem albert_mk_add_fst (a c : Fin 3 → ℝ) (b d : Fin 3 → Octonion) :
    (((a, b) + (c, d) : Albert)).1 = a + c := rfl
private theorem albert_mk_add_snd (a c : Fin 3 → ℝ) (b d : Fin 3 → Octonion) :
    (((a, b) + (c, d) : Albert)).2 = b + d := rfl
private theorem diagAtom_fst (i j : Fin 3) : (diagAtom i).1 j = if j = i then 1 else 0 := rfl
private theorem diagAtom_snd (i k : Fin 3) : (diagAtom i).2 k = 0 := rfl

private theorem oct_fst_zero : (0 : Octonion).1 = 0 := rfl
private theorem oct_snd_zero : (0 : Octonion).2 = 0 := rfl
private theorem oct_fst_add (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem oct_snd_add (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem oct_fst_sub (x y : Octonion) : (x - y).1 = x.1 - y.1 := rfl
private theorem oct_snd_sub (x y : Octonion) : (x - y).2 = x.2 - y.2 := rfl
private theorem oct_fst_smul (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem oct_snd_smul (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl
private theorem oct_neg_apply (a : Octonion) :
    (-a : Octonion) = ({ re := -a.1.re, imI := -a.1.imI, imJ := -a.1.imJ, imK := -a.1.imK },
      { re := -a.2.re, imI := -a.2.imI, imJ := -a.2.imJ, imK := -a.2.imK }) := rfl

private theorem octNormSq_zero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl

private theorem octNormSq_scalar (r : ℝ) : octNormSq (octonionScalar r) = r ^ 2 := by
  rw [octNormSq_eq_coords]
  simp [octonionScalar]

private theorem octonionScalar_re (r : ℝ) : (octonionScalar r).1.re = r := rfl
private theorem octonionScalar_coord (r : ℝ) :
    octonionScalar r = ({ re := r, imI := 0, imJ := 0, imK := 0 }, 0) := rfl
private theorem quat_add_imI (a b : Quaternion ℝ) : (a + b).imI = a.imI + b.imI := rfl
private theorem quat_smul_imI (r : ℝ) (a : Quaternion ℝ) : (r • a).imI = r * a.imI := rfl
private theorem quat_star_re (a : Quaternion ℝ) : (star a).re = a.re := by simp
private theorem quat_star_imI (a : Quaternion ℝ) : (star a).imI = -a.imI := by simp
private theorem quat_star_imJ (a : Quaternion ℝ) : (star a).imJ = -a.imJ := by simp
private theorem quat_star_imK (a : Quaternion ℝ) : (star a).imK = -a.imK := by simp
private theorem octConj_re (o : Octonion) : (octonionConj o).1.re = o.1.re := by simp [octonionConj]
private theorem octConj_imI (o : Octonion) : (octonionConj o).1.imI = -o.1.imI := by simp [octonionConj]
private theorem octConj_imJ (o : Octonion) : (octonionConj o).1.imJ = -o.1.imJ := by simp [octonionConj]
private theorem octConj_imK (o : Octonion) : (octonionConj o).1.imK = -o.1.imK := by simp [octonionConj]
private theorem octConj_snd (o : Octonion) : (octonionConj o).2 = -o.2 := rfl
private theorem octConj_s_re (o : Octonion) : (octonionConj o).2.re = -o.2.re := rfl
private theorem octConj_s_imI (o : Octonion) : (octonionConj o).2.imI = -o.2.imI := rfl
private theorem octConj_s_imJ (o : Octonion) : (octonionConj o).2.imJ = -o.2.imJ := rfl
private theorem octConj_s_imK (o : Octonion) : (octonionConj o).2.imK = -o.2.imK := rfl
private theorem oct_smul_re (r : ℝ) (x : Octonion) : (r • x).1.re = r * x.1.re := rfl
private theorem oct_smul_imI (r : ℝ) (x : Octonion) : (r • x).1.imI = r * x.1.imI := rfl
private theorem oct_smul_imJ (r : ℝ) (x : Octonion) : (r • x).1.imJ = r * x.1.imJ := rfl
private theorem oct_smul_imK (r : ℝ) (x : Octonion) : (r • x).1.imK = r * x.1.imK := rfl
private theorem oct_smul_s_re (r : ℝ) (x : Octonion) : (r • x).2.re = r * x.2.re := rfl
private theorem oct_smul_s_imI (r : ℝ) (x : Octonion) : (r • x).2.imI = r * x.2.imI := rfl
private theorem oct_smul_s_imJ (r : ℝ) (x : Octonion) : (r • x).2.imJ = r * x.2.imJ := rfl
private theorem oct_smul_s_imK (r : ℝ) (x : Octonion) : (r • x).2.imK = r * x.2.imK := rfl
private theorem oct_add_re (x y : Octonion) : (x + y).1.re = x.1.re + y.1.re := rfl
private theorem oct_add_imI (x y : Octonion) : (x + y).1.imI = x.1.imI + y.1.imI := rfl
private theorem oct_add_imJ (x y : Octonion) : (x + y).1.imJ = x.1.imJ + y.1.imJ := rfl
private theorem oct_add_imK (x y : Octonion) : (x + y).1.imK = x.1.imK + y.1.imK := rfl
private theorem oct_add_s_re (x y : Octonion) : (x + y).2.re = x.2.re + y.2.re := rfl
private theorem oct_add_s_imI (x y : Octonion) : (x + y).2.imI = x.2.imI + y.2.imI := rfl
private theorem oct_add_s_imJ (x y : Octonion) : (x + y).2.imJ = x.2.imJ + y.2.imJ := rfl
private theorem oct_add_s_imK (x y : Octonion) : (x + y).2.imK = x.2.imK + y.2.imK := rfl
private theorem oct_neg_re (x : Octonion) : (-x).1.re = -x.1.re := rfl
private theorem oct_neg_imI (x : Octonion) : (-x).1.imI = -x.1.imI := rfl
private theorem oct_neg_imJ (x : Octonion) : (-x).1.imJ = -x.1.imJ := rfl
private theorem oct_neg_imK (x : Octonion) : (-x).1.imK = -x.1.imK := rfl
private theorem oct_neg_s_re (x : Octonion) : (-x).2.re = -x.2.re := rfl
private theorem oct_neg_s_imI (x : Octonion) : (-x).2.imI = -x.2.imI := rfl
private theorem oct_neg_s_imJ (x : Octonion) : (-x).2.imJ = -x.2.imJ := rfl
private theorem oct_neg_s_imK (x : Octonion) : (-x).2.imK = -x.2.imK := rfl
private theorem oct_smul_fst (r : ℝ) (o : Octonion) : (r • o).1 = r • o.1 := rfl
private theorem oct_smul_snd (r : ℝ) (o : Octonion) : (r • o).2 = r • o.2 := rfl
private theorem oct_add_fst (a b : Octonion) : (a + b).1 = a.1 + b.1 := rfl
private theorem oct_add_snd (a b : Octonion) : (a + b).2 = a.2 + b.2 := rfl
private theorem quat_smul_re (r : ℝ) (a : Quaternion ℝ) : (r • a).re = r * a.re := rfl
private theorem quat_smul_imJ (r : ℝ) (a : Quaternion ℝ) : (r • a).imJ = r * a.imJ := rfl
private theorem quat_smul_imK (r : ℝ) (a : Quaternion ℝ) : (r • a).imK = r * a.imK := rfl
private theorem quat_add_re (a b : Quaternion ℝ) : (a + b).re = a.re + b.re := rfl
private theorem quat_add_imJ (a b : Quaternion ℝ) : (a + b).imJ = a.imJ + b.imJ := rfl
private theorem quat_add_imK (a b : Quaternion ℝ) : (a + b).imK = a.imK + b.imK := rfl
private theorem quat_neg_re (a : Quaternion ℝ) : (-a).re = -a.re := rfl
private theorem quat_neg_imI (a : Quaternion ℝ) : (-a).imI = -a.imI := rfl
private theorem quat_neg_imJ (a : Quaternion ℝ) : (-a).imJ = -a.imJ := rfl
private theorem quat_neg_imK (a : Quaternion ℝ) : (-a).imK = -a.imK := rfl
private theorem quat_zero_re : (0 : Quaternion ℝ).re = 0 := rfl
private theorem quat_zero_imI : (0 : Quaternion ℝ).imI = 0 := rfl
private theorem quat_zero_imJ : (0 : Quaternion ℝ).imJ = 0 := rfl
private theorem quat_zero_imK : (0 : Quaternion ℝ).imK = 0 := rfl

private theorem vec3_eq {α : Type*} {a0 a1 a2 b0 b1 b2 : α}
    (h0 : a0 = b0) (h1 : a1 = b1) (h2 : a2 = b2) :
    ![a0, a1, a2] = ![b0, b1, b2] := by
  subst h0 h1 h2; rfl

private theorem octConj_I : octonionConj octI = -octI := by
  rw [eq_neg_iff_add_eq_zero]
  apply Prod.ext
  · change (octonionConj octI).1 + octI.1 = 0
    apply Quaternion.ext <;> simp [octonionConj, octI]
  · change (octonionConj octI).2 + octI.2 = 0
    apply Quaternion.ext <;> simp [octonionConj, octI]

private theorem octConj_J : octonionConj octJ = -octJ := by
  rw [eq_neg_iff_add_eq_zero]
  apply Prod.ext
  · change (octonionConj octJ).1 + octJ.1 = 0
    apply Quaternion.ext <;> simp [octonionConj, octJ]
  · change (octonionConj octJ).2 + octJ.2 = 0
    apply Quaternion.ext <;> simp [octonionConj, octJ]

private theorem octConj_K : octonionConj octK = -octK := by
  rw [eq_neg_iff_add_eq_zero]
  apply Prod.ext
  · change (octonionConj octK).1 + octK.1 = 0
    apply Quaternion.ext <;> simp [octonionConj, octK]
  · change (octonionConj octK).2 + octK.2 = 0
    apply Quaternion.ext <;> simp [octonionConj, octK]

private theorem octConj_L : octonionConj octL = -octL := by
  rw [eq_neg_iff_add_eq_zero]
  apply Prod.ext
  · change (octonionConj octL).1 + octL.1 = 0
    apply Quaternion.ext <;> simp [octonionConj, octL]
  · change (octonionConj octL).2 + octL.2 = 0
    apply Quaternion.ext <;> simp [octonionConj, octL]

private theorem oct_eq_complex {o : Octonion} (hj : o.1.imJ = 0) (hk : o.1.imK = 0)
    (hs : o.2 = 0) : o = o.1.re • octOne + o.1.imI • octI := by
  apply Prod.ext
  · change o.1 = o.1.re • octOne.1 + o.1.imI • octI.1
    apply Quaternion.ext <;> simp [octOne, octI, octonionScalar_coord, hj, hk]
  · change o.2 = o.1.re • octOne.2 + o.1.imI • octI.2
    rw [hs]
    apply Quaternion.ext <;> simp [octOne, octI, octonionScalar_coord]

private theorem complex_oct_coord_eq (r s : ℝ) (z : ℂ) (hr : z.re = r) (hs : z.im = s) :
    complexToOctonion z = octonionScalar r + s • octI := by
  apply Prod.ext
  · change (complexToOctonion z).1 = (octonionScalar r).1 + s • octI.1
    apply Quaternion.ext <;> simp [complexToOctonion_apply, octonionScalar, octI, hr, hs]
  · change (complexToOctonion z).2 = (octonionScalar r).2 + s • octI.2
    apply Quaternion.ext <;> simp [complexToOctonion_apply, octonionScalar, octI]

private theorem conjI_complex_oct (r s : ℝ) :
    conjIAutomorphism.equiv (r • octOne + s • octI) = r • octOne + (-s) • octI := by
  rw [map_add, map_smul, map_smul, conjIAutomorphism.map_one, conjIAutomorphism_I, smul_neg, ← neg_smul]

private theorem slotElem01_fst (a : Octonion) (j : Fin 3) : (slotElem01 a).1 j = 0 := rfl
private theorem slotElem01_snd_0 (a : Octonion) : (slotElem01 a).2 0 = a := rfl
private theorem slotElem01_snd_1 (a : Octonion) : (slotElem01 a).2 1 = 0 := rfl
private theorem slotElem01_snd_2 (a : Octonion) : (slotElem01 a).2 2 = 0 := rfl
private theorem slotElem02_fst (a : Octonion) (j : Fin 3) : (slotElem02 a).1 j = 0 := rfl
private theorem slotElem02_snd_0 (a : Octonion) : (slotElem02 a).2 0 = 0 := rfl
private theorem slotElem02_snd_1 (a : Octonion) : (slotElem02 a).2 1 = a := rfl
private theorem slotElem02_snd_2 (a : Octonion) : (slotElem02 a).2 2 = 0 := rfl
private theorem slotElem12_fst (a : Octonion) (j : Fin 3) : (slotElem12 a).1 j = 0 := rfl
private theorem slotElem12_snd_0 (a : Octonion) : (slotElem12 a).2 0 = 0 := rfl
private theorem slotElem12_snd_1 (a : Octonion) : (slotElem12 a).2 1 = 0 := rfl
private theorem slotElem12_snd_2 (a : Octonion) : (slotElem12 a).2 2 = a := rfl

private theorem octDyad_fst (v : Fin 3 → Octonion) (i : Fin 3) :
    (octDyad v).1 i = octNormSq (v i) := rfl
private theorem octDyad_snd_0 (v : Fin 3 → Octonion) :
    (octDyad v).2 0 = octonionMul (v 0) (octonionConj (v 1)) := rfl
private theorem octDyad_snd_1 (v : Fin 3 → Octonion) :
    (octDyad v).2 1 = octonionMul (v 0) (octonionConj (v 2)) := rfl
private theorem octDyad_snd_2 (v : Fin 3 → Octonion) :
    (octDyad v).2 2 = octonionMul (v 1) (octonionConj (v 2)) := rfl

private theorem albertTrace_eq_sum (x : Albert) :
    albertTrace x = x.1 0 + x.1 1 + x.1 2 := by
  unfold albertTrace
  exact Fin.sum_univ_three _

private theorem octAuto_map_scalar (α : OctonionAutomorphism) (r : ℝ) :
    α.equiv (octonionScalar r) = octonionScalar r := by
  rw [octonionScalar_eq_smul, map_smul, ← octOne, α.map_one]

private theorem octAuto_map_conj (α : OctonionAutomorphism) (x : Octonion) :
    α.equiv (octonionConj x) = octonionConj (α.equiv x) := by
  rw [octConj_eq_two_real_sub, octConj_eq_two_real_sub, map_sub, map_smul,
    α.map_one, α.map_real]

private theorem octAuto_octDyad (α : OctonionAutomorphism) (v : Fin 3 → Octonion) :
    (octAutoToAlbertAuto α).linearEquiv (octDyad v) = octDyad (fun i => α.equiv (v i)) := by
  apply albert_ext
  · change (octDyad v).1 0 = octNormSq (α.equiv (v 0))
    rw [octDyad_fst, α.map_normSq]
  · change (octDyad v).1 1 = octNormSq (α.equiv (v 1))
    rw [octDyad_fst, α.map_normSq]
  · change (octDyad v).1 2 = octNormSq (α.equiv (v 2))
    rw [octDyad_fst, α.map_normSq]
  · change α.equiv ((octDyad v).2 0) = _
    rw [octDyad_snd_0, octDyad_snd_0, α.map_mul, octAuto_map_conj]
  · change α.equiv ((octDyad v).2 1) = _
    rw [octDyad_snd_1, octDyad_snd_1, α.map_mul, octAuto_map_conj]
  · change α.equiv ((octDyad v).2 2) = _
    rw [octDyad_snd_2, octDyad_snd_2, α.map_mul, octAuto_map_conj]

theorem atom_tracePairing_bounds (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    0 ≤ tracePairing p q ∧ tracePairing p q ≤ 1 := by
  have hp_pos : IsPositive p := ⟨p, hp.1.symm⟩
  have hq_pos : IsPositive q := ⟨q, hq.1.symm⟩
  have hqc : jordanMul (albertUnit - q) (albertUnit - q) = albertUnit - q := by
    simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
      jordanMul_albertUnit_right, hq.1]
    abel
  have hqc_pos : IsPositive (albertUnit - q) := ⟨albertUnit - q, hqc.symm⟩
  have h0 : 0 ≤ tracePairing p q := tracePairing_positive_nonnegative p q hp_pos hq_pos
  have h1 : 0 ≤ tracePairing p (albertUnit - q) :=
    tracePairing_positive_nonnegative p (albertUnit - q) hp_pos hqc_pos
  have hsum : tracePairing p q + tracePairing p (albertUnit - q) = 1 := by
    rw [← tracePairing_add_right]
    simp only [add_sub_cancel, tracePairing_unit_right, hp.2]
  exact ⟨h0, by linarith⟩

theorem atom_tracePairing_eq_one_iff (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    tracePairing p q = 1 ↔ p = q := by
  constructor
  · intro h
    have hself : tracePairing (p - q) (p - q) = 0 := by
      rw [tracePairing_sub_left, tracePairing_sub_right, tracePairing_sub_right,
        tracePairing_comm q p]
      have hpp : tracePairing p p = 1 := by unfold tracePairing; rw [hp.1, hp.2]
      have hqq : tracePairing q q = 1 := by unfold tracePairing; rw [hq.1, hq.2]
      linarith
    exact sub_eq_zero.mp ((tracePairing_self_eq_zero (p - q)).mp hself)
  · rintro rfl
    unfold tracePairing
    rw [hp.1, hp.2]

theorem atom_tracePairing_eq_zero_iff (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    tracePairing p q = 0 ↔ jordanMul p q = 0 := by
  constructor
  · intro h
    have hq_pos : IsPositive q := ⟨q, hq.1.symm⟩
    exact (idempotent_support_lemma hp.1 hq_pos h).1
  · intro h
    unfold tracePairing
    rw [h, albertTrace_zero]

def atomDyadVec (p : Albert) : Fin 3 → Octonion :=
  let s := Real.sqrt (p.1 0)
  ![octonionScalar s, (1 / s) • octonionConj (p.2 0), (1 / s) • octonionConj (p.2 1)]

theorem eq_octDyad_of_isAtom_diag0_pos (p : Albert) (hp : IsAtom p) (h0 : 0 < p.1 0) :
    p = octDyad (atomDyadVec p) :=
  (isAtom_eq_octDyad hp h0).1

/-! ## Section 2: Strong Three-Atom Normal Form (`lem:A:three`) -/

private theorem atom_diag1_zero_or_diag2_zero_of_slot12_zero {p : Albert} (hp : IsAtom p)
    (h12 : p.2 2 = 0) : p.1 1 = 0 ∨ p.1 2 = 0 := by
  have hsharp := albertSharp_atom_eq_zero p hp
  have hf := congrArg (fun a : Albert => a.1 0) hsharp
  simp [albertSharp, h12, octNormSq_zero, albert_zero_fst] at hf
  exact hf

theorem lemma_A_three (p : Fin 3 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ g : NativeAlbertAutomorphism,
      g.linearEquiv (p 0) = diagAtom 0 ∧
      (∃ ξ₀ ξ₁ c : ℝ, 0 ≤ ξ₀ ∧ 0 ≤ ξ₁ ∧ 0 ≤ c ∧ ξ₀ + ξ₁ = 1 ∧ ξ₀ * ξ₁ = c ^ 2 ∧
        g.linearEquiv (p 1) = ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c)) ∧
      standardComplexWindow.Contains (g.linearEquiv (p 2)) ∧
      (∃ s : ℝ, 0 ≤ s ∧ (g.linearEquiv (p 2)).2 1 = octonionScalar s) ∧
      ((g.linearEquiv (p 2)).2 0).1.imI ≤ 0 ∧
      ((g.linearEquiv (p 2)).1 0 = 0 →
        ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv (p 2)).2 2 = octonionScalar r) := by
  obtain ⟨g0, hg0⟩ := atom_to_diagAtom0 (p 0) (hp 0)
  have hq1_atom : IsAtom (g0.linearEquiv (p 1)) := g0.map_isAtom (hp 1)
  have hq2_atom : IsAtom (g0.linearEquiv (p 2)) := g0.map_isAtom (hp 2)
  obtain ⟨g1, hg1_diag0, hg1_12⟩ := corner12_zero_fixing_diagAtom0 (g0.linearEquiv (p 1))
  let r1 := g1.linearEquiv (g0.linearEquiv (p 1))
  let r2 := g1.linearEquiv (g0.linearEquiv (p 2))
  have hr1_atom : IsAtom r1 := g1.map_isAtom hq1_atom
  have hr2_atom : IsAtom r2 := g1.map_isAtom hq2_atom
  have hr1_alt : r1.1 1 = 0 ∨ r1.1 2 = 0 :=
    atom_diag1_zero_or_diag2_zero_of_slot12_zero hr1_atom hg1_12
  have hstep2 : ∃ g2 : NativeAlbertAutomorphism,
      g2.linearEquiv (diagAtom 0) = diagAtom 0 ∧
      IsAtom (g2.linearEquiv r1) ∧
      (g2.linearEquiv r1).1 2 = 0 := by
    rcases hr1_alt with h1z | h2z
    · refine ⟨swap12AlbertAuto, ?_, swap12AlbertAuto.map_isAtom hr1_atom, ?_⟩
      · rw [swap12AlbertAuto_diagAtom]; rfl
      · rw [swap12AlbertAuto_apply]; exact h1z
    · exact ⟨NativeAlbertAutomorphism.refl, rfl, hr1_atom, h2z⟩
  obtain ⟨g2, hg2_diag0, hs1_atom, hs1_d2⟩ := hstep2
  let s1 := g2.linearEquiv r1
  let s2 := g2.linearEquiv r2
  have hs2_atom : IsAtom s2 := g2.map_isAtom hr2_atom
  obtain ⟨h12_z1, h12_z2⟩ := isAtom_zero_row2 hs1_atom hs1_d2
  obtain ⟨g3, hg3_diag, c, hc_nn, hg3_01⟩ := exists_frameStab_slot01_real s1
  let t1 := g3.linearEquiv s1
  let t2 := g3.linearEquiv s2
  have ht1_atom : IsAtom t1 := g3.map_isAtom hs1_atom
  have ht2_atom : IsAtom t2 := g3.map_isAtom hs2_atom
  have ht1_diag : ∀ k : Fin 3, t1.1 k = s1.1 k := fun k => by
    have htr := g3.map_tracePairing (diagAtom k) s1
    rw [hg3_diag k, tracePairing_diagAtom, tracePairing_diagAtom] at htr
    exact htr
  have ht1_d2 : t1.1 2 = 0 := by rw [ht1_diag 2, hs1_d2]
  obtain ⟨ht1_s02, ht1_s12⟩ := isAtom_zero_row2 ht1_atom ht1_d2
  let ξ₀ := t1.1 0
  let ξ₁ := t1.1 1
  have hξ₀_nn : 0 ≤ ξ₀ := isAtom_diag_nonneg ht1_atom 0
  have hξ₁_nn : 0 ≤ ξ₁ := isAtom_diag_nonneg ht1_atom 1
  have hξ_sum : ξ₀ + ξ₁ = 1 := by
    have htr := ht1_atom.2
    rw [albertTrace_eq_sum] at htr
    change ξ₀ + ξ₁ + t1.1 2 = 1 at htr
    linarith [ht1_d2]
  have hξ_prod : ξ₀ * ξ₁ = c ^ 2 := by
    have hsharp := albertSharp_atom_eq_zero t1 ht1_atom
    have hf2 := congrArg (fun a : Albert => a.1 2) hsharp
    change t1.1 0 * t1.1 1 - octNormSq (t1.2 0) = 0 at hf2
    dsimp only [t1, ξ₀, ξ₁] at *
    rw [hg3_01, octNormSq_scalar] at hf2
    linarith
  have ht1_eq : t1 = ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c) := by
    apply albert_ext
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem01_fst]; ring
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem01_fst]; ring
    · simp [albert_add_fst, albert_smul_fst, diagAtom_fst, slotElem01_fst, ht1_d2]
    · simp only [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem01_snd_0, smul_zero, add_zero, zero_add]
      exact hg3_01
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem01_snd_1, ht1_s02]
    · simp [albert_add_snd, albert_smul_snd, diagAtom_snd, slotElem01_snd_2, ht1_s12]
  have hfix_t1 : ∀ h : NativeAlbertAutomorphism,
      (∀ i, h.linearEquiv (diagAtom i) = diagAtom i) →
      h.linearEquiv (slotElem01 octOne) = slotElem01 octOne →
      h.linearEquiv t1 = t1 := fun h hd h01 => by
    rw [ht1_eq]
    simp only [map_add, map_smul, hd 0, hd 1]
    have hsc : slotElem01 (octonionScalar c) = c • slotElem01 octOne := by
      rw [octonionScalar_eq_smul, ← octOne, map_smul]
    rw [hsc, map_smul, h01]
  have hstep4 : ∃ g4 : NativeAlbertAutomorphism,
      (∀ i, g4.linearEquiv (diagAtom i) = diagAtom i) ∧
      g4.linearEquiv (slotElem01 octOne) = slotElem01 octOne ∧
      (∃ s : ℝ, 0 ≤ s ∧ (g4.linearEquiv t2).2 1 = octonionScalar s) ∧
      ((g4.linearEquiv t2).1 0 = 0 →
        ∃ r : ℝ, 0 ≤ r ∧ (g4.linearEquiv t2).2 2 = octonionScalar r) := by
    by_cases ht2_d0 : t2.1 0 = 0
    · obtain ⟨g4, hd, h01, r, hr, hr12⟩ := exists_frameAnd01OneStab_slot12_real t2
      refine ⟨g4, hd, h01, ?_, fun _ => ⟨r, hr, hr12⟩⟩
      have hu2_atom : IsAtom (g4.linearEquiv t2) := g4.map_isAtom ht2_atom
      have hu2_d0 : (g4.linearEquiv t2).1 0 = 0 := by
        have htr := g4.map_tracePairing (diagAtom 0) t2
        rw [hd 0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
        rw [htr, ht2_d0]
      have hu2_02 := (isAtom_zero_row0 hu2_atom hu2_d0).2
      exact ⟨0, le_rfl, by rw [hu2_02, octonionScalar_zero]⟩
    · obtain ⟨g4, hd, h01, s, hs, hs02⟩ := exists_frameAnd01OneStab_slot02_real t2
      refine ⟨g4, hd, h01, ⟨s, hs, hs02⟩, fun h0 => False.elim ?_⟩
      have htr := g4.map_tracePairing (diagAtom 0) t2
      rw [hd 0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
      exact ht2_d0 (by rw [← htr, h0])
  obtain ⟨g4, hg4_diag, hg4_01, ⟨s, hs_nn, hu2_02⟩, hu2_d0_zero⟩ := hstep4
  let u2 := g4.linearEquiv t2
  have hu2_atom : IsAtom u2 := g4.map_isAtom ht2_atom
  have hstep5 : ∃ α : OctonionAutomorphism,
      ((octAutoToAlbertAuto α).linearEquiv u2).2 0 ∈ Set.range complexToOctonion ∧
      ((octAutoToAlbertAuto α).linearEquiv u2).2 2 ∈ Set.range complexToOctonion := by
    by_cases hd2 : u2.1 2 = 0
    · obtain ⟨_hs0, hz12⟩ := isAtom_zero_row2 hu2_atom hd2
      obtain ⟨α, r, _hr, hα⟩ := exists_octAuto_imag_to_I (octIm (u2.2 0)) (octonionReal_octIm _)
      refine ⟨α, ?_, ?_⟩
      · have hsplit : u2.2 0 = octonionScalar (octonionReal (u2.2 0)) + octIm (u2.2 0) := by
          rw [octIm, add_sub_cancel]
        have hmap : α.equiv (u2.2 0) =
            octonionScalar (octonionReal (u2.2 0)) + r • octI := by
          conv_lhs => rw [hsplit]
          rw [map_add, octAuto_map_scalar, hα]
        change α.equiv (u2.2 0) ∈ Set.range complexToOctonion
        rw [hmap]
        refine ⟨⟨octonionReal (u2.2 0), r⟩, ?_⟩
        exact complex_oct_coord_eq (octonionReal (u2.2 0)) r _ rfl rfl
      · change α.equiv (u2.2 2) ∈ Set.range complexToOctonion
        rw [hz12, map_zero]
        exact ⟨0, map_zero complexToOctonion⟩
    · obtain ⟨α, r, _hr, hα⟩ := exists_octAuto_imag_to_I (octIm (u2.2 2)) (octonionReal_octIm _)
      have hsplit12 : u2.2 2 = octonionScalar (octonionReal (u2.2 2)) + octIm (u2.2 2) := by
        rw [octIm, add_sub_cancel]
      have h12_img : α.equiv (u2.2 2) ∈ Set.range complexToOctonion := by
        have hmap : α.equiv (u2.2 2) =
            octonionScalar (octonionReal (u2.2 2)) + r • octI := by
          conv_lhs => rw [hsplit12]
          rw [map_add, octAuto_map_scalar, hα]
        rw [hmap]
        refine ⟨⟨octonionReal (u2.2 2), r⟩, ?_⟩
        exact complex_oct_coord_eq (octonionReal (u2.2 2)) r _ rfl rfl
      have hrel01 : u2.1 2 • u2.2 0 = octonionMul (u2.2 1) (octonionConj (u2.2 2)) := by
        have hf0 := congrArg (fun a : Albert => a.2 0) (albertSharp_atom_eq_zero u2 hu2_atom)
        simp only [albertSharp, albert_zero_snd, Matrix.cons_val_zero, sub_eq_zero] at hf0
        exact hf0.symm
      have h01_eq : u2.2 0 = (s / u2.1 2) • octonionConj (u2.2 2) := by
        have h1 : u2.1 2 • u2.2 0 = s • octonionConj (u2.2 2) := by
          rw [hrel01, hu2_02, octonionMul_scalar_left]
        calc
          u2.2 0 = (1 / u2.1 2) • (u2.1 2 • u2.2 0) := by
            rw [smul_smul, one_div, inv_mul_cancel₀ hd2, one_smul]
          _ = (s / u2.1 2) • octonionConj (u2.2 2) := by
            rw [h1, smul_smul]; ring_nf
      rcases h12_img with ⟨z12, hz12⟩
      refine ⟨α, ?_, ⟨z12, hz12⟩⟩
      change α.equiv (u2.2 0) ∈ Set.range complexToOctonion
      rw [h01_eq, map_smul, octAuto_map_conj, ← hz12]
      refine ⟨(s / u2.1 2 : ℝ) • star z12, ?_⟩
      apply oct_ext <;>
        (simp only [oct_smul_re, oct_smul_imI, oct_smul_imJ, oct_smul_imK,
          oct_smul_s_re, oct_smul_s_imI, oct_smul_s_imJ, oct_smul_s_imK,
          octConj_re, octConj_imI, octConj_imJ, octConj_imK,
          octConj_s_re, octConj_s_imI, octConj_s_imJ, octConj_s_imK];
         simp [complexToOctonion_apply, Complex.real_smul]; try ring)
  obtain ⟨α, hα01, hα12⟩ := hstep5
  let g5 := octAutoToAlbertAuto α
  let v2 := g5.linearEquiv u2
  have hv2_in : standardComplexWindow.Contains v2 := by
    rcases hα01 with ⟨z01, hz01⟩
    rcases hα12 with ⟨z12, hz12⟩
    have hv2_01 : v2.2 0 = complexToOctonion z01 := hz01.symm
    have hv2_02 : v2.2 1 = octonionScalar s := by
      change α.equiv (u2.2 1) = octonionScalar s
      rw [hu2_02, octAuto_map_scalar]
    have hv2_12 : v2.2 2 = complexToOctonion z12 := hz12.symm
    rw [standardComplexWindow_contains_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hv2_01, hv2_02, hv2_12, complexToOctonion_apply, octonionScalar]
  let g6 : NativeAlbertAutomorphism :=
    if 0 < (v2.2 0).1.imI then complexTransposeAuto else NativeAlbertAutomorphism.refl
  have hg6_fix_complex : ∀ x : Albert,
      x.2 0 = octonionScalar (x.2 0).1.re →
      x.2 1 = octonionScalar (x.2 1).1.re →
      x.2 2 = octonionScalar (x.2 2).1.re →
      g6.linearEquiv x = x := by
    intro x h0 h1 h2
    dsimp only [g6]
    split_ifs
    · apply albert_ext
      · rfl
      · rfl
      · rfl
      · change conjIAutomorphism.equiv (x.2 0) = x.2 0
        rw [h0, octAuto_map_scalar, ← h0]
      · change conjIAutomorphism.equiv (x.2 1) = x.2 1
        rw [h1, octAuto_map_scalar, ← h1]
      · change conjIAutomorphism.equiv (x.2 2) = x.2 2
        rw [h2, octAuto_map_scalar, ← h2]
    · rfl
  let w2 := g6.linearEquiv v2
  have hw2_in : standardComplexWindow.Contains w2 := by
    rw [standardComplexWindow_contains_iff]
    have hv2c := (standardComplexWindow_contains_iff v2).mp hv2_in
    dsimp only [w2, g6]
    split_ifs
    · obtain ⟨h0j, h0k, h0s, h1j, h1k, h1s, h2j, h2k, h2s⟩ := hv2c
      have hconj_c : ∀ o : Octonion, o.1.imJ = 0 → o.1.imK = 0 → o.2 = 0 →
          (conjIAutomorphism.equiv o).1.imJ = 0 ∧
          (conjIAutomorphism.equiv o).1.imK = 0 ∧
          (conjIAutomorphism.equiv o).2 = 0 := fun o hj hk hs => by
        have hdecomp := oct_eq_complex hj hk hs
        rw [hdecomp, conjI_complex_oct]
        refine ⟨?_, ?_, ?_⟩
        · change (o.1.re • octOne.1 + (-o.1.imI) • octI.1).imJ = 0
          simp [octOne, octI, octonionScalar_coord]
        · change (o.1.re • octOne.1 + (-o.1.imI) • octI.1).imK = 0
          simp [octOne, octI, octonionScalar_coord]
        · change (o.1.re • octOne.2 + (-o.1.imI) • octI.2) = 0
          rw [show octOne.2 = 0 from rfl, show octI.2 = 0 from rfl, smul_zero, smul_zero, add_zero]
      have c0 := hconj_c _ h0j h0k h0s
      have c1 := hconj_c _ h1j h1k h1s
      have c2 := hconj_c _ h2j h2k h2s
      exact ⟨c0.1, c0.2.1, c0.2.2, c1.1, c1.2.1, c1.2.2, c2.1, c2.2.1, c2.2.2⟩
    · exact hv2c
  have hw2_02 : w2.2 1 = octonionScalar s := by
    have hv2_02 : v2.2 1 = octonionScalar s := by
      change α.equiv (u2.2 1) = octonionScalar s
      rw [hu2_02, octAuto_map_scalar]
    dsimp only [w2, g6]
    split_ifs
    · change conjIAutomorphism.equiv (v2.2 1) = octonionScalar s
      rw [hv2_02, octAuto_map_scalar]
    · exact hv2_02
  have hw2_01_imI : (w2.2 0).1.imI ≤ 0 := by
    dsimp only [w2, g6]
    split_ifs with hpos
    · have hv2c := (standardComplexWindow_contains_iff v2).mp hv2_in
      have hdecomp := oct_eq_complex hv2c.1 hv2c.2.1 hv2c.2.2.1
      change (conjIAutomorphism.equiv (v2.2 0)).1.imI ≤ 0
      rw [hdecomp, conjI_complex_oct]
      change ((v2.2 0).1.re • octOne.1 + (-(v2.2 0).1.imI) • octI.1).imI ≤ 0
      simp only [octOne, octI, octonionScalar_coord, quat_add_imI, quat_smul_imI]
      norm_num
      linarith
    · change (v2.2 0).1.imI ≤ 0
      exact not_lt.mp hpos
  have hw2_d0_zero : w2.1 0 = 0 → ∃ r : ℝ, 0 ≤ r ∧ w2.2 2 = octonionScalar r := by
    intro hw0
    have hu0 : u2.1 0 = 0 := by
      have hvw : w2.1 0 = v2.1 0 := by
        dsimp only [w2, g6]; split_ifs <;> rfl
      rw [hvw] at hw0
      exact hw0
    obtain ⟨r, hr, hr12⟩ := hu2_d0_zero hu0
    refine ⟨r, hr, ?_⟩
    have hv12 : v2.2 2 = octonionScalar r := by
      change α.equiv (u2.2 2) = octonionScalar r
      rw [hr12, octAuto_map_scalar]
    dsimp only [w2, g6]
    split_ifs
    · change conjIAutomorphism.equiv (v2.2 2) = octonionScalar r
      rw [hv12, octAuto_map_scalar]
    · exact hv12
  let g := g6.comp (g5.comp (g4.comp (g3.comp (g2.comp (g1.comp g0)))))
  have hz0 : (0 : Octonion) = octonionScalar (0 : Octonion).1.re := by
    rw [show (0 : Octonion).1.re = 0 from rfl, octonionScalar_zero]
  have hg_p0 : g.linearEquiv (p 0) = diagAtom 0 := by
    change g6.linearEquiv (g5.linearEquiv (g4.linearEquiv (g3.linearEquiv
      (g2.linearEquiv (g1.linearEquiv (g0.linearEquiv (p 0))))))) = diagAtom 0
    rw [hg0, hg1_diag0, hg2_diag0, hg3_diag 0, hg4_diag 0]
    have hg5_0 : g5.linearEquiv (diagAtom 0) = diagAtom 0 := octAutoToAlbertAuto_diagAtom α 0
    rw [hg5_0]
    exact hg6_fix_complex (diagAtom 0) hz0 hz0 hz0
  have hg_p1 : g.linearEquiv (p 1) =
      ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c) := by
    change g6.linearEquiv (g5.linearEquiv (g4.linearEquiv t1)) = _
    rw [hfix_t1 g4 hg4_diag hg4_01]
    have hg5_t1 : g5.linearEquiv t1 = t1 := by
      dsimp only [g5]
      rw [ht1_eq]
      simp only [map_add, map_smul, octAutoToAlbertAuto_diagAtom, octAutoToAlbertAuto_slotElem01,
        octAuto_map_scalar]
    rw [hg5_t1, ← ht1_eq]
    dsimp only [t1]
    exact hg6_fix_complex (g3.linearEquiv s1)
      (by rw [hg3_01, octonionScalar_re])
      (by change t1.2 1 = octonionScalar (t1.2 1).1.re; rw [ht1_s02]; exact hz0)
      (by change t1.2 2 = octonionScalar (t1.2 2).1.re; rw [ht1_s12]; exact hz0)
  refine ⟨g, hg_p0, ⟨ξ₀, ξ₁, c, hξ₀_nn, hξ₁_nn, hc_nn, hξ_sum, hξ_prod, hg_p1⟩,
    hw2_in, ⟨s, hs_nn, hw2_02⟩, hw2_01_imI, hw2_d0_zero⟩

/-! ## Section 3: Complex-Window Orthogonal Projection (`windowProj`) & Restriction (`lem:A:restrict`, `prop:three`) -/

def hermE (k : Fin 3) : Hermitian3 :=
  hermitian3Equiv.symm (fun i => if i = k then 1 else 0, 0)

def hermRe (k : Fin 3) : Hermitian3 :=
  hermitian3Equiv.symm (0, fun i => if i = k then 1 else 0)

def hermIm (k : Fin 3) : Hermitian3 :=
  hermitian3Equiv.symm (0, fun i => if i = k then Complex.I else 0)

private theorem herm_decompose (x : Hermitian3) :
    x = (∑ i : Fin 3, ((x : ComplexMatrix3) i i).re • hermE i) +
      (∑ k : Fin 3, ((hermitian3Equiv x).2 k).re • hermRe k) +
      (∑ k : Fin 3, ((hermitian3Equiv x).2 k).im • hermIm k) := by
  apply hermitian3Equiv.injective
  have he : ∀ i : Fin 3, hermitian3Equiv (hermE i) = (fun j => if j = i then 1 else 0, 0) :=
    fun i => hermitian3Equiv.apply_symm_apply _
  have hr : ∀ k : Fin 3, hermitian3Equiv (hermRe k) = (0, fun j => if j = k then 1 else 0) :=
    fun k => hermitian3Equiv.apply_symm_apply _
  have hi : ∀ k : Fin 3, hermitian3Equiv (hermIm k) = (0, fun j => if j = k then Complex.I else 0) :=
    fun k => hermitian3Equiv.apply_symm_apply _
  simp only [map_add, map_sum, map_smul, he, hr, hi]
  apply Prod.ext
  · funext j
    fin_cases j <;> simp [Fin.sum_univ_three, hermitian3Equiv]
  · funext j
    fin_cases j <;> simp [Fin.sum_univ_three, hermitian3Equiv]

def windowProj (W : ComplexWindow) : Albert →ₗ[ℝ] Hermitian3 where
  toFun y :=
    hermitian3Equiv.symm
      (fun i => tracePairing y (W.embedding (hermE i)),
       fun k => ⟨(1 / 2 : ℝ) * tracePairing y (W.embedding (hermRe k)),
                  (1 / 2 : ℝ) * tracePairing y (W.embedding (hermIm k))⟩)
  map_add' y z := by
    rw [← map_add]
    congr 1
    apply Prod.ext
    · funext i; exact tracePairing_add_left y z _
    · funext k
      apply Complex.ext <;> simp [tracePairing_add_left] <;> ring
  map_smul' r y := by
    rw [← map_smul]
    congr 1
    apply Prod.ext
    · funext i; simp [tracePairing_smul_left]
    · funext k
      apply Complex.ext <;> simp [Complex.real_smul, tracePairing_smul_left] <;> ring

private theorem complexHerm_trace_mul_re (M N : Hermitian3) :
    (Matrix.trace ((M : ComplexMatrix3) * (N : ComplexMatrix3))).re =
      ∑ i : Fin 3, ((M : ComplexMatrix3) i i).re * ((N : ComplexMatrix3) i i).re +
      2 * ∑ k : Fin 3, (((hermitian3Equiv M).2 k).re * ((hermitian3Equiv N).2 k).re +
        ((hermitian3Equiv M).2 k).im * ((hermitian3Equiv N).2 k).im) := by
  have hM := M.prop
  have hN := N.prop
  have hMd : ∀ i : Fin 3, ((M : ComplexMatrix3) i i).im = 0 := fun i => by
    have h := congrArg (fun A : ComplexMatrix3 => (A i i).im) hM
    simp only [Matrix.star_apply, Complex.star_def, Complex.conj_im] at h
    linarith
  have hNd : ∀ i : Fin 3, ((N : ComplexMatrix3) i i).im = 0 := fun i => by
    have h := congrArg (fun A : ComplexMatrix3 => (A i i).im) hN
    simp only [Matrix.star_apply, Complex.star_def, Complex.conj_im] at h
    linarith
  have hMs : ∀ i j : Fin 3, (M : ComplexMatrix3) j i = star ((M : ComplexMatrix3) i j) := fun i j => by
    have h := congrArg (fun A : ComplexMatrix3 => A j i) hM
    simpa [Matrix.star_apply] using h.symm
  have hNs : ∀ i j : Fin 3, (N : ComplexMatrix3) j i = star ((N : ComplexMatrix3) i j) := fun i j => by
    have h := congrArg (fun A : ComplexMatrix3 => A j i) hN
    simpa [Matrix.star_apply] using h.symm
  unfold Matrix.trace Matrix.diag
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hMs 0 1, hMs 0 2, hMs 1 2,
    hNs 0 1, hNs 0 2, hNs 1 2, Complex.add_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im, hMd 0, hMd 1, hMd 2, hNd 0, hNd 1, hNd 2,
    hermitian3Equiv, LinearEquiv.coe_mk]
  dsimp
  ring

theorem windowProj_tracePairing (W : ComplexWindow) (y : Albert) (x : Hermitian3) :
    (Matrix.trace ((windowProj W y : ComplexMatrix3) * (x : ComplexMatrix3))).re =
      tracePairing y (W.embedding x) := by
  rw [complexHerm_trace_mul_re]
  have hpw := hermitian3Equiv.apply_symm_apply
    (fun i => tracePairing y (W.embedding (hermE i)),
     fun k => ⟨(1 / 2 : ℝ) * tracePairing y (W.embedding (hermRe k)),
                (1 / 2 : ℝ) * tracePairing y (W.embedding (hermIm k))⟩)
  have hpd : ∀ i : Fin 3, ((windowProj W y : ComplexMatrix3) i i).re =
      tracePairing y (W.embedding (hermE i)) := fun i =>
    congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → ℂ) => p.1 i) hpw
  have hpo : ∀ k : Fin 3, (hermitian3Equiv (windowProj W y)).2 k =
      ⟨(1 / 2 : ℝ) * tracePairing y (W.embedding (hermRe k)),
       (1 / 2 : ℝ) * tracePairing y (W.embedding (hermIm k))⟩ := fun k =>
    congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → ℂ) => p.2 k) hpw
  have hL : ∑ i : Fin 3, ((windowProj W y : ComplexMatrix3) i i).re *
        ((x : ComplexMatrix3) i i).re +
      2 * ∑ k : Fin 3, (((hermitian3Equiv (windowProj W y)).2 k).re * ((hermitian3Equiv x).2 k).re +
        ((hermitian3Equiv (windowProj W y)).2 k).im * ((hermitian3Equiv x).2 k).im) =
      ∑ i : Fin 3, ((x : ComplexMatrix3) i i).re * tracePairing y (W.embedding (hermE i)) +
      ∑ k : Fin 3, ((hermitian3Equiv x).2 k).re * tracePairing y (W.embedding (hermRe k)) +
      ∑ k : Fin 3, ((hermitian3Equiv x).2 k).im * tracePairing y (W.embedding (hermIm k)) := by
    simp_rw [hpd, hpo]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
      Fin.sum_univ_three, Fin.sum_univ_three]
    ring
  rw [hL]
  conv_rhs =>
    rw [herm_decompose x, map_add, map_add, map_sum, map_sum, map_sum,
      tracePairing_add_right, tracePairing_add_right]
  simp only [LinearMap.map_smul, tracePairing_smul_right,
    show ∀ f : Fin 3 → Albert, tracePairing y (∑ i, f i) = ∑ i, tracePairing y (f i) from fun f => by
      rw [Fin.sum_univ_three, Fin.sum_univ_three, tracePairing_add_right, tracePairing_add_right]]

theorem windowProj_embedding (W : ComplexWindow) (x : Hermitian3) :
    windowProj W (W.embedding x) = x := by
  have hz : windowProj W (W.embedding x) - x = 0 := by
    let d := windowProj W (W.embedding x) - x
    have htr0 : (Matrix.trace ((d : ComplexMatrix3) * (d : ComplexMatrix3))).re = 0 := by
      have h1 : (Matrix.trace ((windowProj W (W.embedding x) : ComplexMatrix3) *
          (d : ComplexMatrix3))).re = tracePairing (W.embedding x) (W.embedding d) :=
        windowProj_tracePairing W (W.embedding x) d
      have h2 : tracePairing (W.embedding x) (W.embedding d) =
          (Matrix.trace ((x : ComplexMatrix3) * (d : ComplexMatrix3))).re := by
        obtain ⟨z, hz⟩ := W.product_closed x d
        have hp : jordanMul (W.embedding x) (W.embedding d) = W.embedding z :=
          (W.preserves_product x d z hz).symm
        unfold tracePairing
        rw [hp, W.preserves_trace, hz]
        have hcd : Matrix.trace ((d : ComplexMatrix3) * (x : ComplexMatrix3)) =
            Matrix.trace ((x : ComplexMatrix3) * (d : ComplexMatrix3)) :=
          Matrix.trace_mul_comm _ _
        rw [Matrix.trace_smul, Matrix.trace_add, hcd, ← two_smul ℝ, smul_smul]
        norm_num
      have hd_eq : (d : ComplexMatrix3) * (d : ComplexMatrix3) =
          ((windowProj W (W.embedding x) : ComplexMatrix3) - (x : ComplexMatrix3)) *
            (d : ComplexMatrix3) := rfl
      rw [hd_eq, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, h1, h2, sub_self]
    rw [complexHerm_trace_mul_re] at htr0
    have hd0 : ∀ i : Fin 3, ((d : ComplexMatrix3) i i).re = 0 := fun i => by
      have hsum : ((d : ComplexMatrix3) 0 0).re ^ 2 + ((d : ComplexMatrix3) 1 1).re ^ 2 +
          ((d : ComplexMatrix3) 2 2).re ^ 2 + 2 * ∑ k : Fin 3,
            (((hermitian3Equiv d).2 k).re ^ 2 + ((hermitian3Equiv d).2 k).im ^ 2) = 0 := by
        rw [← htr0, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
        ring
      have hnn : 0 ≤ ∑ k : Fin 3, (((hermitian3Equiv d).2 k).re ^ 2 + ((hermitian3Equiv d).2 k).im ^ 2) :=
        Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
      fin_cases i <;>
        (dsimp; nlinarith [sq_nonneg ((d : ComplexMatrix3) 0 0).re, sq_nonneg ((d : ComplexMatrix3) 1 1).re,
          sq_nonneg ((d : ComplexMatrix3) 2 2).re, hnn])
    have ho0 : ∀ k : Fin 3, (hermitian3Equiv d).2 k = 0 := fun k => by
      have hsum := htr0
      simp only [hd0, zero_mul, Finset.sum_const_zero, zero_add] at hsum
      rw [Fin.sum_univ_three] at hsum
      apply Complex.ext <;>
        fin_cases k <;> simp <;>
        nlinarith [sq_nonneg ((hermitian3Equiv d).2 0).re, sq_nonneg ((hermitian3Equiv d).2 0).im,
          sq_nonneg ((hermitian3Equiv d).2 1).re, sq_nonneg ((hermitian3Equiv d).2 1).im,
          sq_nonneg ((hermitian3Equiv d).2 2).re, sq_nonneg ((hermitian3Equiv d).2 2).im]
    apply hermitian3Equiv.injective
    rw [map_zero]
    apply Prod.ext
    · funext i; exact hd0 i
    · funext k; exact ho0 k
  exact sub_eq_zero.mp hz

private def rankOneHerm (v : Fin 3 → ℂ) : Hermitian3 :=
  ⟨Matrix.of (fun i j => v i * star (v j)), by
    rw [selfAdjoint.mem_iff]
    funext i j
    simp [Matrix.star_apply, mul_comm]⟩

theorem complexWindow_isPositive_of_posSemidef (W : ComplexWindow) (M : Hermitian3)
    (hM : (M : ComplexMatrix3).PosSemidef) : IsPositive (W.embedding M) := by
  let U : ComplexMatrix3 := hM.isHermitian.eigenvectorUnitary
  let ev := hM.isHermitian.eigenvalues
  let D : ComplexMatrix3 := Matrix.diagonal (fun i => (Real.sqrt (ev i) : ℂ))
  have hD_herm : D.conjTranspose = D := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [D, Matrix.diagonal]
    · simp [D, Matrix.diagonal, hij, Ne.symm hij]
  let S : Hermitian3 :=
    ⟨U * D * U.conjTranspose, by
      rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD_herm, Matrix.mul_assoc]⟩
  have hSsq : (M : ComplexMatrix3) =
      (1 / 2 : ℝ) • ((S : ComplexMatrix3) * (S : ComplexMatrix3) +
        (S : ComplexMatrix3) * (S : ComplexMatrix3)) := by
    have hUU : U.conjTranspose * U = 1 := by
      simpa [U, Matrix.star_eq_conjTranspose] using
        Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary
    have hD2 : D * D = Matrix.diagonal (fun i => (ev i : ℂ)) := by
      dsimp only [D]
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact_mod_cast Real.mul_self_sqrt (hM.eigenvalues_nonneg i)
    have hspec : (M : ComplexMatrix3) =
        U * Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose := by
      simpa [U, ev, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
        hM.isHermitian.spectral_theorem
    have hSS : (S : ComplexMatrix3) * (S : ComplexMatrix3) = (M : ComplexMatrix3) := by
      dsimp only [S]
      calc
        U * D * U.conjTranspose * (U * D * U.conjTranspose)
          = U * D * (U.conjTranspose * U) * D * U.conjTranspose := by
              simp only [Matrix.mul_assoc]
        _ = U * (D * D) * U.conjTranspose := by
              rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = (M : ComplexMatrix3) := by rw [hD2, ← hspec]
    rw [hSS, ← two_smul ℝ (M : ComplexMatrix3), smul_smul]
    norm_num
  exact ⟨W.embedding S, W.preserves_product S S M hSsq⟩

private theorem rankOneHerm_posSemidef (v : Fin 3 → ℂ) :
    ((rankOneHerm v : Hermitian3) : ComplexMatrix3).PosSemidef := by
  have hH : ((rankOneHerm v : Hermitian3) : ComplexMatrix3).IsHermitian := (rankOneHerm v).prop
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hH, fun x => ?_⟩
  have hval : star x ⬝ᵥ Matrix.mulVec ((rankOneHerm v : Hermitian3) : ComplexMatrix3) x =
      (∑ i : Fin 3, star (v i) * x i) * star (∑ i : Fin 3, star (v i) * x i) := by
    simp only [dotProduct, Matrix.mulVec, rankOneHerm, Matrix.of_apply,
      Finset.sum_mul, Finset.mul_sum, Pi.star_apply, star_sum, star_mul, star_star]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hval]
  let z := ∑ i : Fin 3, star (v i) * x i
  change 0 ≤ z * star z
  have hz : z * star z = ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> (simp [sq, Complex.mul_re, Complex.mul_im]; try ring)
  rw [hz]
  exact_mod_cast add_nonneg (sq_nonneg z.re) (sq_nonneg z.im)

theorem windowProj_isComplexDensity3 (W : ComplexWindow) (ρ : Albert) (hρ : IsDensity ρ) :
    IsComplexDensity3 (windowProj W ρ : ComplexMatrix3) := by
  let σ := (windowProj W ρ : ComplexMatrix3)
  have hHerm : σ.IsHermitian := (windowProj W ρ).prop
  have htr_re : (Matrix.trace σ).re = 1 := by
    have h1 := windowProj_tracePairing W ρ 1
    have hmul : σ * ((1 : Hermitian3) : ComplexMatrix3) = σ := Matrix.mul_one σ
    rw [hmul, W.unit, tracePairing_unit_right, hρ.2] at h1
    exact h1
  have htr_im : (Matrix.trace σ).im = 0 := by
    have hs := congrArg (fun A : ComplexMatrix3 => (Matrix.trace A).im) (windowProj W ρ).prop
    simp only [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def,
      Complex.conj_im] at hs
    linarith
  have htr : Matrix.trace σ = 1 := Complex.ext htr_re htr_im
  refine ⟨?_, htr⟩
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hHerm, fun v => ?_⟩
  have hpair : star v ⬝ᵥ Matrix.mulVec σ v = Matrix.trace (σ * (rankOneHerm v : ComplexMatrix3)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      rankOneHerm, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hconj_tr : star (Matrix.trace (σ * (rankOneHerm v : ComplexMatrix3))) =
      Matrix.trace (σ * (rankOneHerm v : ComplexMatrix3)) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
    have hs1 : σ.conjTranspose = σ := hHerm.eq
    have hs2 : ((rankOneHerm v : Hermitian3) : ComplexMatrix3).conjTranspose =
        (rankOneHerm v : ComplexMatrix3) := (rankOneHerm v).prop
    rw [hs1, hs2, Matrix.trace_mul_comm]
  have him : (star v ⬝ᵥ Matrix.mulVec σ v).im = 0 := by
    rw [hpair]
    have hc := congrArg Complex.im hconj_tr
    simp only [Complex.star_def, Complex.conj_im] at hc
    linarith
  have hre : 0 ≤ (star v ⬝ᵥ Matrix.mulVec σ v).re := by
    rw [hpair, windowProj_tracePairing]
    exact tracePairing_positive_nonnegative ρ _ hρ.1
      (complexWindow_isPositive_of_posSemidef W (rankOneHerm v) (rankOneHerm_posSemidef v))
  have hceq : star v ⬝ᵥ Matrix.mulVec σ v = (((star v ⬝ᵥ Matrix.mulVec σ v).re : ℝ) : ℂ) :=
    Complex.ext rfl him
  rw [hceq]
  exact_mod_cast hre

theorem complexWindow_rankOne_of_atom (W : ComplexWindow) (P : Hermitian3)
    (hP : IsAtom (W.embedding P)) : IsComplexRankOneProjection (P : ComplexMatrix3) := by
  have hsq : (P : ComplexMatrix3) * (P : ComplexMatrix3) = (P : ComplexMatrix3) := by
    obtain ⟨Q, hQ⟩ := W.product_closed P P
    have hPQ : W.embedding Q = jordanMul (W.embedding P) (W.embedding P) :=
      W.preserves_product P P Q hQ
    rw [hP.1] at hPQ
    have hQp := W.injective hPQ
    have hmat : (Q : ComplexMatrix3) = (P : ComplexMatrix3) := congrArg Subtype.val hQp
    rw [hQ, ← two_smul ℝ ((P : ComplexMatrix3) * (P : ComplexMatrix3)), smul_smul] at hmat
    norm_num at hmat
    exact hmat
  have htr : Matrix.trace (P : ComplexMatrix3) = 1 := by
    have hre : (Matrix.trace (P : ComplexMatrix3)).re = 1 := by
      rw [← W.preserves_trace, hP.2]
    have him : (Matrix.trace (P : ComplexMatrix3)).im = 0 := by
      have hs := congrArg (fun A : ComplexMatrix3 => (Matrix.trace A).im) P.prop
      simp only [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def,
        Complex.conj_im] at hs
      linarith
    exact Complex.ext hre him
  have hHerm : (P : ComplexMatrix3).IsHermitian := P.prop
  let U : ComplexMatrix3 := hHerm.eigenvectorUnitary
  let ev := hHerm.eigenvalues
  have hUU : U.conjTranspose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hHerm.eigenvectorUnitary
  have hspec : (P : ComplexMatrix3) =
      U * Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose := by
    simpa [U, ev, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hHerm.spectral_theorem
  have hev_sq : ∀ k : Fin 3, ev k * ev k = ev k := by
    intro k
    have hD2 : Matrix.diagonal (fun i => ((ev i * ev i : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => (ev i : ℂ)) := by
      have h1 : U * Matrix.diagonal (fun i => ((ev i * ev i : ℝ) : ℂ)) * U.conjTranspose =
          U * Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose := by
        calc
          U * Matrix.diagonal (fun i => ((ev i * ev i : ℝ) : ℂ)) * U.conjTranspose
            = (U * Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose) *
                (U * Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose) := by
                  have hd : Matrix.diagonal (fun i => (ev i : ℂ)) *
                      Matrix.diagonal (fun i => (ev i : ℂ)) =
                      Matrix.diagonal (fun i => ((ev i * ev i : ℝ) : ℂ)) := by
                    rw [Matrix.diagonal_mul_diagonal]
                    congr 1; funext i; push_cast; rfl
                  rw [← hd]
                  calc
                    U * (Matrix.diagonal (fun i => (ev i : ℂ)) *
                        Matrix.diagonal (fun i => (ev i : ℂ))) * U.conjTranspose
                      = U * Matrix.diagonal (fun i => (ev i : ℂ)) * (U.conjTranspose * U) *
                          Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose := by
                            rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
                    _ = (U * Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose) *
                          (U * Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose) := by
                            simp only [Matrix.mul_assoc]
          _ = (P : ComplexMatrix3) * (P : ComplexMatrix3) := by rw [← hspec]
          _ = (P : ComplexMatrix3) := hsq
          _ = U * Matrix.diagonal (fun i => (ev i : ℂ)) * U.conjTranspose := hspec
      have h2 := congrArg (fun M : ComplexMatrix3 => U.conjTranspose * M * U) h1
      simp only [Matrix.mul_assoc] at h2
      have h3 : U.conjTranspose * (U * (Matrix.diagonal (fun i => ((ev i * ev i : ℝ) : ℂ)) *
          (U.conjTranspose * U))) = Matrix.diagonal (fun i => ((ev i * ev i : ℝ) : ℂ)) := by
        rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
      have h4 : U.conjTranspose * (U * (Matrix.diagonal (fun i => (ev i : ℂ)) *
          (U.conjTranspose * U))) = Matrix.diagonal (fun i => (ev i : ℂ)) := by
        rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
      rw [h3, h4] at h2
      exact h2
    have hk := congrArg (fun M : ComplexMatrix3 => (M k k).re) hD2
    simpa [Matrix.diagonal] using hk
  have hev_sum : ev 0 + ev 1 + ev 2 = 1 := by
    have htr_diag : Matrix.trace (P : ComplexMatrix3) = ∑ i : Fin 3, (ev i : ℂ) := by
      rw [hspec, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal]
    rw [htr] at htr_diag
    have hre := congrArg Complex.re htr_diag
    rw [Fin.sum_univ_three] at hre
    simpa using hre.symm
  have hev_bin : ∀ k : Fin 3, ev k = 0 ∨ ev k = 1 := fun k => by
    have h := hev_sq k
    have hm : ev k * (ev k - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hm with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hex : ∃ k₀ : Fin 3, ev k₀ = 1 ∧ ∀ k : Fin 3, k ≠ k₀ → ev k = 0 := by
    rcases hev_bin 0 with h0 | h0 <;> rcases hev_bin 1 with h1 | h1 <;> rcases hev_bin 2 with h2 | h2
    all_goals try (exfalso; linarith)
    · refine ⟨2, h2, fun k hk => ?_⟩; fin_cases k <;> [exact h0; exact h1; exact False.elim (hk rfl)]
    · refine ⟨1, h1, fun k hk => ?_⟩; fin_cases k <;> [exact h0; exact False.elim (hk rfl); exact h2]
    · refine ⟨0, h0, fun k hk => ?_⟩; fin_cases k <;> [exact False.elim (hk rfl); exact h1; exact h2]
  obtain ⟨k₀, hk₀_one, hk₀_other⟩ := hex
  refine ⟨fun i => U i k₀, ?_, ?_⟩
  · have hnorm : (U.conjTranspose * U) k₀ k₀ = 1 := by rw [hUU, Matrix.one_apply_eq]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, mul_comm] using hnorm
  · intro i j
    rw [hspec]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Matrix.conjTranspose_apply, RCLike.star_def]
    rw [Fin.sum_univ_three]
    fin_cases k₀ <;> dsimp at hk₀_one hk₀_other ⊢
    · rw [hk₀_one, hk₀_other 1 (by decide), hk₀_other 2 (by decide)]; simp
    · rw [hk₀_one, hk₀_other 0 (by decide), hk₀_other 2 (by decide)]; simp
    · rw [hk₀_one, hk₀_other 0 (by decide), hk₀_other 1 (by decide)]; simp

private theorem complexWindow_quadraticMap (W : ComplexWindow) (Q M : Hermitian3) :
    ∃ R : Hermitian3,
      (R : ComplexMatrix3) = (Q : ComplexMatrix3) * (M : ComplexMatrix3) * (Q : ComplexMatrix3) ∧
      W.embedding R = quadraticMap (W.embedding Q) (W.embedding M) := by
  obtain ⟨QM, hQM⟩ := W.product_closed Q M
  obtain ⟨QQM, hQQM⟩ := W.product_closed Q QM
  obtain ⟨QQ, hQQ⟩ := W.product_closed Q Q
  obtain ⟨QQ_M, hQQ_M⟩ := W.product_closed QQ M
  refine ⟨(2 : ℝ) • QQM - QQ_M, ?_, ?_⟩
  · ext i j
    change ((2 : ℝ) • (QQM : ComplexMatrix3) - (QQ_M : ComplexMatrix3)) i j =
      ((Q : ComplexMatrix3) * (M : ComplexMatrix3) * (Q : ComplexMatrix3)) i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
    rw [hQQM, hQM, hQQ_M, hQQ]
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Matrix.mul_apply,
      Fin.sum_univ_three]
    push_cast
    ring
  · unfold quadraticMap
    rw [map_sub, map_smul, W.preserves_product Q QM QQM hQQM,
      W.preserves_product Q M QM hQM, W.preserves_product QQ M QQ_M hQQ_M,
      W.preserves_product Q Q QQ hQQ]
    rw [two_smul ℝ, two_smul ℕ]

private def hermOutcome {ι : Type*} (P : ι → Hermitian3) (a : Outcome ι) : Hermitian3 :=
  if a.2 then P a.1 else 1 - P a.1

private theorem hermOutcome_val {ι : Type*} (P : ι → Hermitian3) (a : Outcome ι) :
    (hermOutcome P a : ComplexMatrix3) = algebraicOutcome (fun i => (P i : ComplexMatrix3)) a := by
  cases a with
  | mk i b => cases b <;> rfl

private theorem hermOutcome_embedding {ι : Type*} (W : ComplexWindow)
    (P : ι → Hermitian3) (a : Outcome ι) :
    W.embedding (hermOutcome P a) = nativeOutcome (fun i => W.embedding (P i)) a := by
  cases a with
  | mk i b =>
    cases b
    · change W.embedding (1 - P i) = albertUnit - W.embedding (P i)
      rw [map_sub, W.unit]
    · rfl

private theorem wordAmplitude_cons {ι A : Type*} [Ring A] (P : ι → A)
    (a : Outcome ι) (w : Word ι) :
    wordAmplitude P (a :: w) = wordAmplitude P w * algebraicOutcome P a := by
  unfold wordAmplitude
  rw [List.foldl_cons, mul_one]
  suffices h : ∀ (w' : Word ι) (z : A),
      w'.foldl (fun x b => algebraicOutcome P b * x) z =
        w'.foldl (fun x b => algebraicOutcome P b * x) 1 * z from h w (algebraicOutcome P a)
  intro w'
  induction w' with
  | nil => intro z; simp
  | cons b ws ih =>
    intro z
    rw [List.foldl_cons, List.foldl_cons, mul_one, ih (algebraicOutcome P b * z),
      ih (algebraicOutcome P b), mul_assoc]

private theorem wordOperator_cons_herm {ι : Type*} (P : ι → Hermitian3)
    (a : Outcome ι) (w : Word ι) :
    wordOperator (fun i => (P i : ComplexMatrix3)) (a :: w) =
      (hermOutcome P a : ComplexMatrix3) *
        wordOperator (fun i => (P i : ComplexMatrix3)) w *
        (hermOutcome P a : ComplexMatrix3) := by
  unfold wordOperator
  rw [wordAmplitude_cons, star_mul, hermOutcome_val]
  have hst : star (hermOutcome P a : ComplexMatrix3) = (hermOutcome P a : ComplexMatrix3) :=
    (hermOutcome P a).prop
  rw [hermOutcome_val] at hst
  rw [hst]
  simp only [Matrix.mul_assoc]

private theorem complexWindow_wordEffect_eq {ι : Type*} (W : ComplexWindow)
    (P : ι → Hermitian3) (w : Word ι) :
    ∃ R : Hermitian3,
      (R : ComplexMatrix3) = wordOperator (fun i => (P i : ComplexMatrix3)) w ∧
      W.embedding R = nativeWordEffect (fun i => W.embedding (P i)) w := by
  induction w with
  | nil =>
    refine ⟨1, ?_, W.unit⟩
    simp [wordOperator, wordAmplitude]
  | cons a ws ih =>
    obtain ⟨Rw, hRw_val, hRw_emb⟩ := ih
    obtain ⟨R', hR'_val, hR'_emb⟩ := complexWindow_quadraticMap W (hermOutcome P a) Rw
    refine ⟨R', ?_, ?_⟩
    · rw [hR'_val, hRw_val, wordOperator_cons_herm]
    · rw [hR'_emb, hermOutcome_embedding, hRw_emb]
      rfl

theorem complexRestrictionContract_holds : ComplexRestrictionContract where
  common_density_transport W ρ hρ := by
    let σ : ComplexMatrix3 := windowProj W ρ
    refine ⟨σ, windowProj_isComplexDensity3 W ρ hρ, fun x => windowProj_tracePairing W ρ x, ?_⟩
    intro ι p P hp hPp
    refine ⟨fun i => complexWindow_rankOne_of_atom W (P i) (by rw [hPp i]; exact hp i), fun w => ?_⟩
    obtain ⟨Rw, hRw_val, hRw_emb⟩ := complexWindow_wordEffect_eq W P w
    have hpeq : (fun i => W.embedding (P i)) = p := funext hPp
    rw [hpeq] at hRw_emb
    unfold complexWordProbability3
    rw [← hRw_val, windowProj_tracePairing, hRw_emb, nativeWordProbability_eq_pairing]

private theorem standardComplexWindow_contains_diag0 :
    standardComplexWindow.Contains (diagAtom 0) := by
  rw [standardComplexWindow_contains_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private theorem standardComplexWindow_contains_xi_slot01 (ξ₀ ξ₁ c : ℝ) :
    standardComplexWindow.Contains
      (ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c)) := by
  let x := ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c)
  have hx0 : x.2 0 = octonionScalar c := by
    rw [albert_add_snd, albert_add_snd, albert_smul_snd, albert_smul_snd,
      diagAtom_snd, diagAtom_snd, smul_zero, smul_zero, add_zero, zero_add, slotElem01_snd_0]
  have hx1 : x.2 1 = 0 := by
    rw [albert_add_snd, albert_add_snd, albert_smul_snd, albert_smul_snd,
      diagAtom_snd, diagAtom_snd, smul_zero, smul_zero, add_zero, zero_add, slotElem01_snd_1]
  have hx2 : x.2 2 = 0 := by
    rw [albert_add_snd, albert_add_snd, albert_smul_snd, albert_smul_snd,
      diagAtom_snd, diagAtom_snd, smul_zero, smul_zero, add_zero, zero_add, slotElem01_snd_2]
  change standardComplexWindow.Contains x
  rw [standardComplexWindow_contains_iff, hx0, hx1, hx2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem complexTripleContract_holds : ComplexTripleContract where
  common_window p hp := by
    obtain ⟨g, hg0, ⟨ξ₀, ξ₁, c, _hξ₀, _hξ₁, _hc, _hsum, _hprod, hg1⟩, hg2, _⟩ :=
      lemma_A_three p hp
    refine ⟨standardComplexWindow.transport g.symm, fun i => ?_⟩
    rw [ComplexWindow.contains_transport_iff]
    have hinv : g.symm.linearEquiv.symm = g.linearEquiv := rfl
    rw [hinv]
    fin_cases i
    · dsimp; rw [hg0]; exact standardComplexWindow_contains_diag0
    · dsimp; rw [hg1]; exact standardComplexWindow_contains_xi_slot01 ξ₀ ξ₁ c
    · exact hg2
  rank_one_statistics p ρ hp hρ := by
    obtain ⟨g, hg0, ⟨ξ₀, ξ₁, c, _hξ₀, _hξ₁, _hc, _hsum, _hprod, hg1⟩, hg2, _⟩ :=
      lemma_A_three p hp
    let W := standardComplexWindow.transport g.symm
    have hW : ∀ i : Fin 3, W.Contains (p i) := fun i => by
      rw [ComplexWindow.contains_transport_iff]
      have hinv : g.symm.linearEquiv.symm = g.linearEquiv := rfl
      rw [hinv]
      fin_cases i
      · dsimp; rw [hg0]; exact standardComplexWindow_contains_diag0
      · dsimp; rw [hg1]; exact standardComplexWindow_contains_xi_slot01 ξ₀ ξ₁ c
      · exact hg2
    choose P hP using hW
    obtain ⟨σ, hσ_dens, _, hstats⟩ :=
      complexRestrictionContract_holds.common_density_transport W ρ hρ
    obtain ⟨hP_rk1, hw⟩ := hstats (Fin 3) p P hp hP
    exact ⟨fun i => (P i : ComplexMatrix3), σ, hP_rk1, hσ_dens, hw⟩

/-! ## Section 4: Four-Point Normal Form (`lem:A:normal`) and Degenerate Lemma (`lem:A:degenerate`) -/

private theorem atom_diag1_eq_octDyad {p : Albert} (hp : IsAtom p) (h0 : p.1 0 = 0)
    (h1 : 0 < p.1 1) (hr : ∃ r : ℝ, 0 ≤ r ∧ p.2 2 = octonionScalar r) :
    let C₁ := Real.sqrt (p.1 1)
    let C₃ := Real.sqrt (p.1 2)
    0 < C₁ ∧ 0 ≤ C₃ ∧ C₁ ^ 2 + C₃ ^ 2 = 1 ∧
    p = octDyad ![0, octonionScalar C₁, octonionScalar C₃] := by
  intro C₁ C₃
  obtain ⟨r, hr_nn, hr_eq⟩ := hr
  obtain ⟨hz01, hz02⟩ := isAtom_zero_row0 hp h0
  have hsharp := albertSharp_atom_eq_zero p hp
  have hf0 := congrArg (fun a : Albert => a.1 0) hsharp
  simp [albertSharp, hr_eq, octNormSq_scalar, albert_zero_fst] at hf0
  have hC1_pos : 0 < C₁ := Real.sqrt_pos.mpr h1
  have hC3_nn : 0 ≤ C₃ := Real.sqrt_nonneg _
  have hp2_nn : 0 ≤ p.1 2 := isAtom_diag_nonneg hp 2
  have hsum : C₁ ^ 2 + C₃ ^ 2 = 1 := by
    rw [Real.sq_sqrt h1.le, Real.sq_sqrt hp2_nn]
    have htr := hp.2
    rw [albertTrace_eq_sum, h0] at htr
    linarith
  have hr_prod : r = C₁ * C₃ := by
    have hsq : r ^ 2 = (C₁ * C₃) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h1.le, Real.sq_sqrt hp2_nn]
      linarith
    nlinarith [mul_nonneg hC1_pos.le hC3_nn]
  refine ⟨hC1_pos, hC3_nn, hsum, ?_⟩
  apply albert_ext
  · simp [octDyad_fst, h0, octNormSq_zero]
  · dsimp only [C₁]; simp [octDyad_fst, octNormSq_scalar, Real.sq_sqrt h1.le]
  · dsimp only [C₃]; simp [octDyad_fst, octNormSq_scalar, Real.sq_sqrt hp2_nn]
  · simp [octDyad_snd_0, hz01, octonionMul_zero_left]
  · simp [octDyad_snd_1, hz02, octonionMul_zero_left]
  · simp [octDyad_snd_2, hr_eq, hr_prod, octonionMul_scalar_left, octonionConj_scalar,
      octonionScalar_smul]

private theorem atom_diag2_eq_octDyad {p : Albert} (hp : IsAtom p) (h0 : p.1 0 = 0)
    (h1 : p.1 1 = 0) : p = octDyad ![0, 0, octonionScalar 1] := by
  obtain ⟨hz01, hz02⟩ := isAtom_zero_row0 hp h0
  obtain ⟨_, hz12⟩ := isAtom_zero_row1 hp h1
  have h2 : p.1 2 = 1 := by
    have htr := hp.2
    rw [albertTrace_eq_sum, h0, h1] at htr
    linarith
  apply albert_ext
  · simp [octDyad_fst, h0, octNormSq_zero]
  · simp [octDyad_fst, h1, octNormSq_zero]
  · simp [octDyad_fst, h2, octNormSq_scalar]
  · simp [octDyad_snd_0, hz01, octonionMul_zero_left]
  · simp [octDyad_snd_1, hz02, octonionMul_zero_left]
  · simp [octDyad_snd_2, hz12, octonionMul_zero_left]

theorem lemma_A_normal_general (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ (g : NativeAlbertAutomorphism)
      (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : ℝ) (X Y : Octonion)
      (x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄ : ℝ),
      0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ C₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 ≤ D₀ ∧ 0 ≤ x₂ ∧ 0 ≤ y₄ ∧
      B₀ ^ 2 + B₁ ^ 2 = 1 ∧ C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1 ∧
      D₀ ^ 2 + x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 = 1 ∧
      X = x₀ • octOne + x₁ • octI + x₂ • octJ ∧
      Y = y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL ∧
      (fun i => g.linearEquiv (p i)) = sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y ∧
      (D₀ = 0 → x₁ = 0 ∧ x₂ = 0) := by
  obtain ⟨g0, hg0, ⟨ξ₀, ξ₁, c, hξ₀, hξ₁, hc_nn, hξ_sum, hξ_prod, hg1⟩,
    hg2_in, ⟨s, hs_nn, hg2_02⟩, hg2_imI, hg2_d0_zero⟩ :=
    lemma_A_three (fun i : Fin 3 => p i.castSucc) (fun i => hp i.castSucc)
  let q0 := g0.linearEquiv (p 0)
  let q1 := g0.linearEquiv (p 1)
  let q2 := g0.linearEquiv (p 2)
  let q3 := g0.linearEquiv (p 3)
  have hq2_02 : q2.2 1 = octonionScalar s := hg2_02
  have hq2_imI : (q2.2 0).1.imI ≤ 0 := hg2_imI
  have hq2_d0_zero : q2.1 0 = 0 → ∃ r : ℝ, 0 ≤ r ∧ q2.2 2 = octonionScalar r := hg2_d0_zero
  have hq2_atom : IsAtom q2 := g0.map_isAtom (hp 2)
  have hq3_atom : IsAtom q3 := g0.map_isAtom (hp 3)
  let B₀ := Real.sqrt ξ₀
  let B₁ := Real.sqrt ξ₁
  have hB0_nn : 0 ≤ B₀ := Real.sqrt_nonneg _
  have hB1_nn : 0 ≤ B₁ := Real.sqrt_nonneg _
  have hB_sum : B₀ ^ 2 + B₁ ^ 2 = 1 := by
    dsimp only [B₀, B₁]
    rw [Real.sq_sqrt hξ₀, Real.sq_sqrt hξ₁, hξ_sum]
  have hB_prod : B₀ * B₁ = c := by
    have hsq : (B₀ * B₁) ^ 2 = c ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hξ₀, Real.sq_sqrt hξ₁, hξ_prod]
    nlinarith [mul_nonneg hB0_nn hB1_nn]
  have hq0_dyad : q0 = octDyad ![octonionScalar 1, 0, 0] := by
    change g0.linearEquiv (p (Fin.castSucc 0)) = _
    rw [hg0]
    apply albert_ext <;> simp [diagAtom, octDyad, octNormSq_scalar, octNormSq_zero,
      octonionConj_zero, octonionMul_zero_right]
  have hq1_dyad : q1 = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] := by
    change g0.linearEquiv (p (Fin.castSucc 1)) = _
    rw [hg1]
    dsimp only [B₀, B₁]
    apply albert_ext <;>
      simp [octDyad_fst, octDyad_snd_0, octDyad_snd_1, octDyad_snd_2,
        albert_add_fst, albert_add_snd, albert_smul_fst, albert_smul_snd,
        diagAtom_fst, diagAtom_snd, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1,
        slotElem01_snd_2, octNormSq_scalar, octNormSq_zero, octonionConj_zero,
        octonionConj_scalar, octonionMul_zero_right, octonionMul_scalar_left,
        Real.sq_sqrt hξ₀, Real.sq_sqrt hξ₁]
    dsimp only [B₀, B₁] at hB_prod
    rw [← octonionScalar_smul, hB_prod]
  have hq2_data : ∃ C₀ C₁ C₂ C₃ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
      C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1 ∧
      q2 = octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] := by
    by_cases h2d0 : 0 < q2.1 0
    · let C₀ := Real.sqrt (q2.1 0)
      have hC0_pos : 0 < C₀ := Real.sqrt_pos.mpr h2d0
      obtain ⟨hdyad, hnorm⟩ := isAtom_eq_octDyad hq2_atom h2d0
      have hC_in := (standardComplexWindow_contains_iff q2).mp hg2_in
      let C₁ := (1 / C₀) * (q2.2 0).1.re
      let C₂ := -(1 / C₀) * (q2.2 0).1.imI
      let C₃ := (1 / C₀) * s
      have hv1_eq : (1 / Real.sqrt (q2.1 0)) • octonionConj (q2.2 0) =
          octonionScalar C₁ + C₂ • octI := by
        have hs1 : (q2.2 0).2.re = 0 := by rw [hC_in.2.2.1]; rfl
        have hs2 : (q2.2 0).2.imI = 0 := by rw [hC_in.2.2.1]; rfl
        have hs3 : (q2.2 0).2.imJ = 0 := by rw [hC_in.2.2.1]; rfl
        have hs4 : (q2.2 0).2.imK = 0 := by rw [hC_in.2.2.1]; rfl
        apply oct_ext <;>
          (simp only [oct_smul_re, oct_smul_imI, oct_smul_imJ, oct_smul_imK,
            oct_smul_s_re, oct_smul_s_imI, oct_smul_s_imJ, oct_smul_s_imK,
            oct_add_re, oct_add_imI, oct_add_imJ, oct_add_imK,
            oct_add_s_re, oct_add_s_imI, oct_add_s_imJ, oct_add_s_imK,
            octConj_re, octConj_imI, octConj_imJ, octConj_imK,
            octConj_s_re, octConj_s_imI, octConj_s_imJ, octConj_s_imK];
           dsimp only [C₀, C₁, C₂];
           simp [octonionScalar_coord, octI, hC_in.1, hC_in.2.1, hs1, hs2, hs3, hs4]; try ring)
      have hv2_eq : (1 / Real.sqrt (q2.1 0)) • octonionConj (q2.2 1) = octonionScalar C₃ := by
        change (1 / C₀) • octonionConj (q2.2 1) = octonionScalar C₃
        dsimp only [C₃]
        rw [hq2_02, octonionConj_scalar, ← octonionScalar_smul]
      have hC2_nn : 0 ≤ C₂ := by
        have h1 : 0 ≤ -(q2.2 0).1.imI := by linarith [hq2_imI]
        have h2 : 0 ≤ 1 / C₀ := one_div_nonneg.mpr hC0_pos.le
        have h3 : C₂ = (1 / C₀) * (-(q2.2 0).1.imI) := by dsimp only [C₂]; ring
        rw [h3]
        exact mul_nonneg h2 h1
      have hC3_nn : 0 ≤ C₃ := mul_nonneg (one_div_nonneg.mpr hC0_pos.le) hs_nn
      have hv0_norm : octNormSq (octonionScalar (Real.sqrt (q2.1 0))) = C₀ ^ 2 := by
        simp [C₀, octNormSq_scalar]
      have hv1_norm : octNormSq ((1 / Real.sqrt (q2.1 0)) • octonionConj (q2.2 0)) = C₁ ^ 2 + C₂ ^ 2 := by
        rw [hv1_eq, octNormSq_eq_coords]
        have hr1 : (octonionScalar C₁ + C₂ • octI).1 =
            (octonionScalar C₁).1 + C₂ • octI.1 := rfl
        have hr2 : (octonionScalar C₁ + C₂ • octI).2 = 0 := by
          change (octonionScalar C₁).2 + C₂ • octI.2 = 0
          rw [show octI.2 = 0 from rfl, smul_zero, add_zero]; rfl
        rw [hr1, hr2]
        simp [octonionScalar_coord, octI, quat_add_re, quat_add_imI, quat_add_imJ, quat_add_imK,
          quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK]
      have hv2_norm : octNormSq ((1 / Real.sqrt (q2.1 0)) • octonionConj (q2.2 1)) = C₃ ^ 2 := by
        rw [hv2_eq, octNormSq_scalar]
      have hsum : C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1 := by
        rw [Fin.sum_univ_three] at hnorm
        change octNormSq (octonionScalar (Real.sqrt (q2.1 0))) +
          octNormSq ((1 / Real.sqrt (q2.1 0)) • octonionConj (q2.2 0)) +
          octNormSq ((1 / Real.sqrt (q2.1 0)) • octonionConj (q2.2 1)) = 1 at hnorm
        linarith [hv0_norm, hv1_norm, hv2_norm]
      refine ⟨C₀, C₁, C₂, C₃, hC0_pos.le, hC2_nn, hC3_nn, hsum, ?_⟩
      rw [hdyad]
      exact congrArg octDyad (vec3_eq rfl hv1_eq hv2_eq)
    · have h2d0z : q2.1 0 = 0 := le_antisymm (not_lt.mp h2d0) (isAtom_diag_nonneg hq2_atom 0)
      by_cases h2d1 : 0 < q2.1 1
      · obtain ⟨_hC1_pos, hC3_nn, hsum, hdyad⟩ :=
          atom_diag1_eq_octDyad hq2_atom h2d0z h2d1 (hq2_d0_zero h2d0z)
        refine ⟨0, Real.sqrt (q2.1 1), 0, Real.sqrt (q2.1 2), le_rfl, le_rfl, hC3_nn, by linarith [hsum], ?_⟩
        nth_rw 1 [hdyad]
        exact congrArg octDyad (vec3_eq octonionScalar_zero.symm (by rw [zero_smul, add_zero]) rfl)
      · have h2d1z : q2.1 1 = 0 := le_antisymm (not_lt.mp h2d1) (isAtom_diag_nonneg hq2_atom 1)
        have hdyad := atom_diag2_eq_octDyad hq2_atom h2d0z h2d1z
        refine ⟨0, 0, 0, 1, le_rfl, le_rfl, zero_le_one, by norm_num, ?_⟩
        rw [hdyad]
        exact congrArg octDyad (vec3_eq octonionScalar_zero.symm (by simp [octonionScalar_zero]) rfl)
  obtain ⟨C₀, C₁, C₂, C₃, hC0_nn, hC2_nn, hC3_nn, hC_sum, hq2_dyad⟩ := hq2_data
  have hq3_data : ∃ (D₀ : ℝ) (X' Y' : Octonion), 0 ≤ D₀ ∧
      D₀ ^ 2 + octNormSq X' + octNormSq Y' = 1 ∧
      q3 = octDyad ![octonionScalar D₀, X', Y'] ∧
      (D₀ = 0 → ∃ x₀ : ℝ, X' = octonionScalar x₀) := by
    by_cases h3d0 : 0 < q3.1 0
    · let D₀ := Real.sqrt (q3.1 0)
      obtain ⟨hdyad, hnorm⟩ := isAtom_eq_octDyad hq3_atom h3d0
      have hD0_pos : 0 < D₀ := Real.sqrt_pos.mpr h3d0
      rw [Fin.sum_univ_three] at hnorm
      dsimp at hnorm
      have hd0 : octNormSq (octonionScalar D₀) = D₀ ^ 2 := octNormSq_scalar D₀
      refine ⟨D₀, (1 / D₀) • octonionConj (q3.2 0), (1 / D₀) • octonionConj (q3.2 1),
        hD0_pos.le, by linarith, hdyad, fun h => False.elim (hD0_pos.ne' h)⟩
    · have h3d0z : q3.1 0 = 0 := le_antisymm (not_lt.mp h3d0) (isAtom_diag_nonneg hq3_atom 0)
      by_cases h3d1 : 0 < q3.1 1
      · let x₀ := Real.sqrt (q3.1 1)
        have hx0_pos : 0 < x₀ := Real.sqrt_pos.mpr h3d1
        let Y' := (1 / x₀) • octonionConj (q3.2 2)
        have hsharp := albertSharp_atom_eq_zero q3 hq3_atom
        have hf0 := congrArg (fun a : Albert => a.1 0) hsharp
        simp [albertSharp, albert_zero_fst] at hf0
        have hny : octNormSq Y' = q3.1 2 := by
          dsimp only [Y', x₀]
          rw [octNormSq_smul, octNormSq_conj, one_div, inv_pow, Real.sq_sqrt h3d1.le]
          have hf0' : q3.1 1 * q3.1 2 = octNormSq (q3.2 2) := by linarith
          rw [← hf0']
          field_simp [h3d1.ne']
        have hsum : 0 ^ 2 + octNormSq (octonionScalar x₀) + octNormSq Y' = 1 := by
          dsimp only [x₀]
          rw [octNormSq_scalar, Real.sq_sqrt h3d1.le, hny]
          have htr := hq3_atom.2
          rw [albertTrace_eq_sum, h3d0z] at htr
          linarith
        obtain ⟨hz01, hz02⟩ := isAtom_zero_row0 hq3_atom h3d0z
        have hdyad : q3 = octDyad ![octonionScalar 0, octonionScalar x₀, Y'] := by
          apply albert_ext
          · simp [octDyad_fst, h3d0z, octNormSq_scalar]
          · dsimp only [x₀]; simp [octDyad_fst, octNormSq_scalar, Real.sq_sqrt h3d1.le]
          · simp [octDyad_fst, hny]
          · simp [octDyad_snd_0, hz01, octonionScalar_zero, octonionMul_zero_left]
          · simp [octDyad_snd_1, hz02, octonionScalar_zero, octonionMul_zero_left]
          · dsimp only [Y']
            rw [octDyad_snd_2,
              show (![octonionScalar 0, octonionScalar x₀, (1 / x₀) • octonionConj (q3.2 2)] : Fin 3 → Octonion) 1 =
                octonionScalar x₀ from rfl,
              show (![octonionScalar 0, octonionScalar x₀, (1 / x₀) • octonionConj (q3.2 2)] : Fin 3 → Octonion) 2 =
                (1 / x₀) • octonionConj (q3.2 2) from rfl,
              octonionConj_smul, octonionConj_conj, octonionMul_smul_right,
              octonionMul_scalar_left, smul_smul, one_div_mul_cancel hx0_pos.ne', one_smul]
        exact ⟨0, octonionScalar x₀, Y', le_rfl, hsum, hdyad, fun _ => ⟨x₀, rfl⟩⟩
      · have h3d1z : q3.1 1 = 0 := le_antisymm (not_lt.mp h3d1) (isAtom_diag_nonneg hq3_atom 1)
        have hdyad := atom_diag2_eq_octDyad hq3_atom h3d0z h3d1z
        refine ⟨0, 0, octonionScalar 1, le_rfl, by simp [octNormSq_scalar, octNormSq_zero], ?_,
          fun _ => ⟨0, by simp [octonionScalar_zero]⟩⟩
        rw [hdyad]
        exact congrArg octDyad (vec3_eq octonionScalar_zero.symm rfl rfl)
  obtain ⟨D₀, X', Y', hD0_nn, hD_norm, hq3_dyad, hD0_real⟩ := hq3_data
  obtain ⟨α1, hα1_I, x₀, x₁, x₂, hx2_nn, hα1_X⟩ := exists_octAuto_fix_I_to_IJ X'
  obtain ⟨α2, hα2_I, hα2_J, hα2_K, y₀, y₁, y₂, y₃, y₄, hy4_nn, hα2_Y⟩ :=
    exists_octAuto_fix_IJ_to_IJL (α1.equiv Y')
  let α := α2.comp α1
  have hα_I : α.equiv octI = octI := by
    change α2.equiv (α1.equiv octI) = octI; rw [hα1_I, hα2_I]
  let X := x₀ • octOne + x₁ • octI + x₂ • octJ
  let Y := y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL
  have hα_X : α.equiv X' = X := by
    change α2.equiv (α1.equiv X') = X
    dsimp only [X]
    rw [hα1_X]
    simp only [map_add, map_smul, α2.map_one, hα2_I, hα2_J]
  have hα_Y : α.equiv Y' = Y := hα2_Y
  have hfix_q0 : (octAutoToAlbertAuto α).linearEquiv q0 = octDyad ![octonionScalar 1, 0, 0] := by
    rw [hq0_dyad, octAuto_octDyad]
    congr 1; funext i; fin_cases i <;> simp [octAuto_map_scalar]
  have hfix_q1 : (octAutoToAlbertAuto α).linearEquiv q1 =
      octDyad ![octonionScalar B₀, octonionScalar B₁, 0] := by
    rw [hq1_dyad, octAuto_octDyad]
    congr 1; funext i; fin_cases i <;> simp [octAuto_map_scalar]
  have hfix_q2 : (octAutoToAlbertAuto α).linearEquiv q2 =
      octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] := by
    rw [hq2_dyad, octAuto_octDyad]
    congr 1; funext i; fin_cases i
    · simp [octAuto_map_scalar]
    · simp [map_add, map_smul, octAuto_map_scalar, hα_I]
    · simp [octAuto_map_scalar]
  have hmap_q3 : (octAutoToAlbertAuto α).linearEquiv q3 =
      octDyad ![octonionScalar D₀, X, Y] := by
    rw [hq3_dyad, octAuto_octDyad]
    congr 1; funext i; fin_cases i
    · simp [octAuto_map_scalar]
    · exact hα_X
    · exact hα_Y
  have hX_norm : octNormSq X = x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 := by
    change octNormSq (x₀ • octOne + x₁ • octI + x₂ • octJ) = _
    have hX1 : (x₀ • octOne + x₁ • octI + x₂ • octJ).1 =
        x₀ • octOne.1 + x₁ • octI.1 + x₂ • octJ.1 := rfl
    have hX2 : (x₀ • octOne + x₁ • octI + x₂ • octJ).2 = 0 := by
      change x₀ • octOne.2 + x₁ • octI.2 + x₂ • octJ.2 = 0
      rw [show octOne.2 = 0 from rfl, show octI.2 = 0 from rfl, show octJ.2 = 0 from rfl,
        smul_zero, smul_zero, smul_zero, add_zero, add_zero]
    rw [octNormSq_eq_coords, hX1, hX2]
    simp [octOne, octI, octJ, octonionScalar_coord, quat_add_re, quat_add_imI, quat_add_imJ,
      quat_add_imK, quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK]
  have hY_norm : octNormSq Y = y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 := by
    change octNormSq (y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL) = _
    have hY1 : (y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL).1 =
        y₀ • octOne.1 + y₁ • octI.1 + y₂ • octJ.1 + y₃ • octK.1 := by
      change y₀ • octOne.1 + y₁ • octI.1 + y₂ • octJ.1 + y₃ • octK.1 + y₄ • octL.1 = _
      rw [show octL.1 = 0 from rfl, smul_zero, add_zero]
    have hY2 : (y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL).2 = y₄ • octL.2 := by
      change y₀ • octOne.2 + y₁ • octI.2 + y₂ • octJ.2 + y₃ • octK.2 + y₄ • octL.2 = _
      rw [show octOne.2 = 0 from rfl, show octI.2 = 0 from rfl, show octJ.2 = 0 from rfl,
        show octK.2 = 0 from rfl, smul_zero, smul_zero, smul_zero, smul_zero,
        add_zero, add_zero, add_zero, zero_add]
    rw [octNormSq_eq_coords, hY1, hY2]
    simp [octOne, octI, octJ, octK, octL, octonionScalar_coord, quat_add_re, quat_add_imI,
      quat_add_imJ, quat_add_imK, quat_smul_re, quat_smul_imI, quat_smul_imJ, quat_smul_imK]
  have hD_sum : D₀ ^ 2 + x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 = 1 := by
    have h1 : octNormSq X = octNormSq X' := by rw [← hα_X, α.map_normSq]
    have h2 : octNormSq Y = octNormSq Y' := by rw [← hα_Y, α.map_normSq]
    linarith [hD_norm, hX_norm, hY_norm]
  have hD0_check : D₀ = 0 → x₁ = 0 ∧ x₂ = 0 := by
    intro h0
    obtain ⟨rx, hrx⟩ := hD0_real h0
    have hX_rx : X = rx • octOne := by
      rw [← hα_X, hrx, octAuto_map_scalar, octonionScalar_eq_smul, octOne_eq_scalar]
    have hi1 := congrArg (fun o : Octonion => o.1.imI) hX_rx
    have hi2 := congrArg (fun o : Octonion => o.1.imJ) hX_rx
    change (x₀ • octOne.1 + x₁ • octI.1 + x₂ • octJ.1).imI = (rx • octOne.1).imI at hi1
    change (x₀ • octOne.1 + x₁ • octI.1 + x₂ • octJ.1).imJ = (rx • octOne.1).imJ at hi2
    simp [octOne, octI, octJ, octonionScalar_coord] at hi1 hi2
    exact ⟨hi1, hi2⟩
  refine ⟨(octAutoToAlbertAuto α).comp g0, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y,
    x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
    hB0_nn, hB1_nn, hC0_nn, hC2_nn, hC3_nn, hD0_nn, hx2_nn, hy4_nn,
    hB_sum, hC_sum, hD_sum, rfl, rfl, ?_, hD0_check⟩
  funext i
  fin_cases i
  · exact hfix_q0
  · exact hfix_q1
  · exact hfix_q2
  · exact hmap_q3

theorem lemma_A_normal (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (h01 : 0 < tracePairing (p 0) (p 1)) (h01' : tracePairing (p 0) (p 1) < 1)
    (h02 : 0 < tracePairing (p 0) (p 2)) (h03 : 0 < tracePairing (p 0) (p 3)) :
    ∃ (g : NativeAlbertAutomorphism)
      (B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄ : ℝ),
      0 < B₀ ∧ 0 < B₁ ∧ 0 < C₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 < D₀ ∧ 0 ≤ x₂ ∧ 0 ≤ y₄ ∧
      B₀ ^ 2 + B₁ ^ 2 = 1 ∧ C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1 ∧
      D₀ ^ 2 + x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 = 1 ∧
      (fun i => g.linearEquiv (p i)) =
        sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂
          (y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL) := by
  obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
    hB0, hB1, hC0, hC2, hC3, hD0, hx2, hy4, hBs, hCs, hDs, hX, hY, hcfg, _⟩ :=
    lemma_A_normal_general p hp
  have htr : ∀ i : Fin 4, fpOverlap (fun j => g.linearEquiv (p j)) 0 i = tracePairing (p 0) (p i) :=
    fun i => g.map_tracePairing (p 0) (p i)
  have h1 : B₀ ^ 2 = tracePairing (p 0) (p 1) := by
    have := (sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y).1
    rw [← hcfg, htr 1] at this
    exact this.symm
  have h2 : C₀ ^ 2 = tracePairing (p 0) (p 2) := by
    have := (sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y).2.1
    rw [← hcfg, htr 2] at this
    exact this.symm
  have h3 : D₀ ^ 2 = tracePairing (p 0) (p 3) := by
    have := (sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y).2.2.1
    rw [← hcfg, htr 3] at this
    exact this.symm
  have hB0p : 0 < B₀ := lt_of_le_of_ne hB0 (fun h => by rw [← h] at h1; linarith)
  have hB1p : 0 < B₁ := lt_of_le_of_ne hB1 (fun h => by rw [← h, h1] at hBs; linarith)
  have hC0p : 0 < C₀ := lt_of_le_of_ne hC0 (fun h => by rw [← h] at h2; linarith)
  have hD0p : 0 < D₀ := lt_of_le_of_ne hD0 (fun h => by rw [← h] at h3; linarith)
  refine ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
    hB0p, hB1p, hC0p, hC2, hC3, hD0p, hx2, hy4, hBs, hCs, hDs, ?_⟩
  rw [hcfg, hX, hY]
  have hxsc : x₀ • octOne = octonionScalar x₀ := (octonionScalar_eq_smul x₀).symm
  rw [hxsc]
  unfold sparseFourConfig
  rfl

theorem lemma_A_normal_nondegenerate (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hnd : ∀ i j, i ≠ j → p i ≠ p j ∧ jordanMul (p i) (p j) ≠ 0) :
    ∃ (g : NativeAlbertAutomorphism)
      (B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄ : ℝ),
      0 < B₀ ∧ 0 < B₁ ∧ 0 < C₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 < D₀ ∧ 0 ≤ x₂ ∧ 0 ≤ y₄ ∧
      B₀ ^ 2 + B₁ ^ 2 = 1 ∧ C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1 ∧
      D₀ ^ 2 + x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 = 1 ∧
      (fun i => g.linearEquiv (p i)) =
        sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂
          (y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL) := by
  have htr : ∀ i : Fin 4, i ≠ 0 →
      0 < tracePairing (p 0) (p i) ∧ tracePairing (p 0) (p i) < 1 := fun i hi => by
    obtain ⟨hne, hmul⟩ := hnd 0 i hi.symm
    obtain ⟨h0, h1⟩ := atom_tracePairing_bounds (p 0) (p i) (hp 0) (hp i)
    refine ⟨lt_of_le_of_ne h0 (fun h => hmul ((atom_tracePairing_eq_zero_iff (p 0) (p i)
      (hp 0) (hp i)).mp h.symm)),
      lt_of_le_of_ne h1 (fun h => hne ((atom_tracePairing_eq_one_iff (p 0) (p i)
        (hp 0) (hp i)).mp h))⟩
  exact lemma_A_normal p hp (htr 1 (by decide)).1 (htr 1 (by decide)).2
    (htr 2 (by decide)).1 (htr 3 (by decide)).1

private theorem standardComplexWindow_le_standardQuat (x : Albert)
    (hx : standardComplexWindow.Contains x) :
    x ∈ standardQuaternionicWindow.subalgebra.carrier := by
  obtain ⟨M, rfl⟩ := hx
  rw [← standardQuaternionicWindow.range_eq]
  let Q : QuatMatrix3 := fun i j =>
    ⟨((M : ComplexMatrix3) i j).re, ((M : ComplexMatrix3) i j).im, 0, 0⟩
  have hQ : Q ∈ selfAdjoint QuatMatrix3 := by
    rw [selfAdjoint.mem_iff]
    funext i j
    have hM := congrArg (fun A : ComplexMatrix3 => A i j) M.prop
    simp only [Matrix.star_apply, Complex.star_def] at hM
    have hre := congrArg Complex.re hM
    have him := congrArg Complex.im hM
    simp only [Complex.conj_re, Complex.conj_im] at hre him
    apply Quaternion.ext
    · change (star (Q j i)).re = (Q i j).re
      simp [Q, quat_star_re, hre]
    · change (star (Q j i)).imI = (Q i j).imI
      simp [Q, quat_star_imI, him]
    · change (star (Q j i)).imJ = (Q i j).imJ
      simp [Q, quat_star_imJ]
    · change (star (Q j i)).imK = (Q i j).imK
      simp [Q, quat_star_imK]
  refine ⟨⟨Q, hQ⟩, ?_⟩
  apply albert_ext <;>
    (simp [Q, standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding_apply,
      quatMatrixToAlbert, standardComplexWindow, complexHermToAlbert, complexToOctonion_apply,
      quatEmbed1_apply]; try rfl)

theorem lemma_A_degenerate (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hdeg : ∃ i j, i ≠ j ∧ (p i = p j ∨ jordanMul (p i) (p j) = 0)) :
    ∃ Q : QuaternionicWindow, ∀ i, p i ∈ Q.subalgebra.carrier := by
  rcases hdeg with ⟨i0, j0, hij, hco | horth⟩
  · have h3 : ∃ f : Fin 3 → Fin 4, ∀ k : Fin 4, ∃ m : Fin 3, p k = p (f m) := by
      fin_cases j0
      · refine ⟨![1, 2, 3], fun k => ?_⟩
        fin_cases k
        · fin_cases i0 <;> dsimp at hij hco ⊢
          · exact absurd rfl hij
          · exact ⟨0, hco.symm⟩
          · exact ⟨1, hco.symm⟩
          · exact ⟨2, hco.symm⟩
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
      · refine ⟨![0, 2, 3], fun k => ?_⟩
        fin_cases k
        · exact ⟨0, rfl⟩
        · fin_cases i0 <;> dsimp at hij hco ⊢
          · exact ⟨0, hco.symm⟩
          · exact absurd rfl hij
          · exact ⟨1, hco.symm⟩
          · exact ⟨2, hco.symm⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
      · refine ⟨![0, 1, 3], fun k => ?_⟩
        fin_cases k
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · fin_cases i0 <;> dsimp at hij hco ⊢
          · exact ⟨0, hco.symm⟩
          · exact ⟨1, hco.symm⟩
          · exact absurd rfl hij
          · exact ⟨2, hco.symm⟩
        · exact ⟨2, rfl⟩
      · refine ⟨![0, 1, 2], fun k => ?_⟩
        fin_cases k
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · fin_cases i0 <;> dsimp at hij hco ⊢
          · exact ⟨0, hco.symm⟩
          · exact ⟨1, hco.symm⟩
          · exact ⟨2, hco.symm⟩
          · exact absurd rfl hij
    obtain ⟨f, hf⟩ := h3
    obtain ⟨W, hW⟩ := complexTripleContract_holds.common_window (p ∘ f) (fun m => hp (f m))
    obtain ⟨g, hg⟩ := native_complexWindow_conjugate_standard W
    refine ⟨standardQuaternionicWindow.transport g.symm, fun k => ?_⟩
    obtain ⟨m, hm⟩ := hf k
    obtain ⟨M, hM⟩ := hW m
    rw [hm]
    change (p ∘ f) m ∈ (standardQuaternionicWindow.transport g.symm).subalgebra.carrier
    rw [← hM]
    refine ⟨g.linearEquiv (W.embedding M), ?_, ?_⟩
    · rw [hg M]
      exact standardComplexWindow_le_standardQuat _ ⟨M, rfl⟩
    · exact g.linearEquiv.symm_apply_apply (W.embedding M)
  · have hperm : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i0 ∧ σ 1 = j0 := by
      let σ0 : Equiv.Perm (Fin 4) := Equiv.swap 0 i0
      let j1 := σ0.symm j0
      have hj1 : j1 ≠ 0 := by
        intro h
        apply hij
        have h' := congrArg σ0 h
        rw [Equiv.apply_symm_apply] at h'
        simpa [σ0] using h'.symm
      let σ1 : Equiv.Perm (Fin 4) := Equiv.swap 1 j1
      refine ⟨σ1.trans σ0, ?_, ?_⟩
      · simp only [Equiv.trans_apply, σ1, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) hj1.symm,
          σ0, Equiv.swap_apply_left]
      · simp only [Equiv.trans_apply, σ1, Equiv.swap_apply_left, j1, Equiv.apply_symm_apply]
    obtain ⟨σ, hσ0, hσ1⟩ := hperm
    let q := p ∘ σ
    have hq_atom : ∀ k, IsAtom (q k) := fun k => hp (σ k)
    have hq01_orth : jordanMul (q 0) (q 1) = 0 := by
      change jordanMul (p (σ 0)) (p (σ 1)) = 0
      rw [hσ0, hσ1]; exact horth
    obtain ⟨g0, hg0, ⟨ξ₀, ξ₁, c, _hξ0, _hξ1, _hc, hξsum, hξprod, hg1⟩, _⟩ :=
      lemma_A_three (fun k : Fin 3 => q k.castSucc) (fun k => hq_atom k.castSucc)
    have hg0' : g0.linearEquiv (q 0) = diagAtom 0 := hg0
    have hg1' : g0.linearEquiv (q 1) = ξ₀ • diagAtom 0 + ξ₁ • diagAtom 1 + slotElem01 (octonionScalar c) := hg1
    have hq1_diag : g0.linearEquiv (q 1) = diagAtom 1 := by
      have htr : tracePairing (diagAtom 0) (g0.linearEquiv (q 1)) = 0 := by
        rw [← hg0', g0.map_tracePairing, (atom_tracePairing_eq_zero_iff (q 0) (q 1)
          (hq_atom 0) (hq_atom 1)).mpr hq01_orth]
      rw [hg1', tracePairing_add_right, tracePairing_add_right, tracePairing_smul_right,
        tracePairing_smul_right, tracePairing_diagAtom, diagAtom_fst,
        tracePairing_diagAtom, diagAtom_fst] at htr
      have hsp : tracePairing (diagAtom 0) (slotElem01 (octonionScalar c)) = 0 := by
        rw [tracePairing_diagAtom, slotElem01_fst]
      rw [hsp] at htr
      have hξ0z : ξ₀ = 0 := by simpa using htr
      have hξ1o : ξ₁ = 1 := by linarith
      have hcz : c = 0 := by
        have hsq : c ^ 2 = 0 := by rw [← hξprod, hξ0z, zero_mul]
        exact mul_self_eq_zero.mp (by rw [sq] at hsq; exact hsq)
      rw [hg1', hξ0z, hξ1o, hcz, zero_smul, one_smul, zero_add, octonionScalar_zero,
        map_zero, add_zero]
    let r2 := g0.linearEquiv (q 2)
    have hr2_atom : IsAtom r2 := g0.map_isAtom (hq_atom 2)
    obtain ⟨g1, hg1_diag, c01, _hc01, hg1_01⟩ := exists_frameStab_slot01_real r2
    let s2 := g1.linearEquiv r2
    have hs2_atom : IsAtom s2 := g1.map_isAtom hr2_atom
    have hs2_step : ∃ g2 : NativeAlbertAutomorphism,
        (∀ k, g2.linearEquiv (diagAtom k) = diagAtom k) ∧
        (g2.linearEquiv s2).2 0 = octonionScalar ((g2.linearEquiv s2).2 0).1.re ∧
        (g2.linearEquiv s2).2 1 = octonionScalar ((g2.linearEquiv s2).2 1).1.re ∧
        (g2.linearEquiv s2).2 2 = octonionScalar ((g2.linearEquiv s2).2 2).1.re := by
      by_cases hs2d0 : s2.1 0 = 0
      · obtain ⟨g2, hd, _h01, r12, _hr12, hg2_12⟩ := exists_frameAnd01OneStab_slot12_real s2
        have ht2_atom : IsAtom (g2.linearEquiv s2) := g2.map_isAtom hs2_atom
        have ht2d0 : (g2.linearEquiv s2).1 0 = 0 := by
          have htr := g2.map_tracePairing (diagAtom 0) s2
          rw [hd 0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
          exact htr.trans hs2d0
        obtain ⟨hz01, hz02⟩ := isAtom_zero_row0 ht2_atom ht2d0
        have hz0 : (0 : Octonion) = octonionScalar (0 : Octonion).1.re := by
          rw [show (0 : Octonion).1.re = 0 from rfl, octonionScalar_zero]
        refine ⟨g2, hd, ?_, ?_, ?_⟩
        · rw [hz01]; exact hz0
        · rw [hz02]; exact hz0
        · rw [hg2_12, octonionScalar_re]
      · obtain ⟨g2, hd, h01, r02, _hr02, hg2_02⟩ := exists_frameAnd01OneStab_slot02_real s2
        have ht2_atom : IsAtom (g2.linearEquiv s2) := g2.map_isAtom hs2_atom
        have ht2_01 : (g2.linearEquiv s2).2 0 = octonionScalar c01 := by
          have hsc : slotElem01 (octonionScalar c01) = c01 • slotElem01 octOne := by
            rw [octonionScalar_eq_smul, ← octOne, map_smul]
          have hp01 := congrArg g2.linearEquiv (peirce01_extract s2)
          rw [map_smul, g2.preserves_product, g2.preserves_product, hd 0, hd 1,
            peirce01_extract, hg1_01, hsc, map_smul, h01, ← hsc] at hp01
          have heq := congrArg (fun a : Albert => a.2 0) hp01
          simp [albert_smul_snd, slotElem01_snd_0] at heq
          exact heq
        have ht2d0 : (g2.linearEquiv s2).1 0 = s2.1 0 := by
          have htr := g2.map_tracePairing (diagAtom 0) s2
          rw [hd 0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
          exact htr
        have ht2d0_pos : (g2.linearEquiv s2).1 0 ≠ 0 := by rw [ht2d0]; exact hs2d0
        have ht2_12_eq : (g2.linearEquiv s2).1 0 • (g2.linearEquiv s2).2 2 =
            octonionMul (octonionConj ((g2.linearEquiv s2).2 0)) ((g2.linearEquiv s2).2 1) := by
          have hsharp := albertSharp_atom_eq_zero _ ht2_atom
          have hf := congrArg (fun a : Albert => a.2 2) hsharp
          exact (sub_eq_zero.mp hf).symm
        have ht2_12 : (g2.linearEquiv s2).2 2 =
            octonionScalar ((c01 * r02) / (g2.linearEquiv s2).1 0) := by
          rw [ht2_01, hg2_02, octonionConj_scalar, octonionMul_scalar_left,
            ← octonionScalar_smul] at ht2_12_eq
          calc
            (g2.linearEquiv s2).2 2 =
                (1 / (g2.linearEquiv s2).1 0) • ((g2.linearEquiv s2).1 0 • (g2.linearEquiv s2).2 2) := by
                  rw [smul_smul, one_div, inv_mul_cancel₀ ht2d0_pos, one_smul]
            _ = octonionScalar ((c01 * r02) / (g2.linearEquiv s2).1 0) := by
                  rw [ht2_12_eq, ← octonionScalar_smul]; congr 1; ring
        refine ⟨g2, hd, ?_, ?_, ?_⟩
        · rw [ht2_01, octonionScalar_re]
        · rw [hg2_02, octonionScalar_re]
        · rw [ht2_12, octonionScalar_re]
    obtain ⟨g2, hg2_diag, ht2_01, ht2_02, ht2_12⟩ := hs2_step
    let g := g2.comp (g1.comp g0)
    have hq0_g : g.linearEquiv (q 0) = diagAtom 0 := by
      change g2.linearEquiv (g1.linearEquiv (g0.linearEquiv (q (Fin.castSucc 0)))) = diagAtom 0
      rw [hg0, hg1_diag 0, hg2_diag 0]
    have hq1_g : g.linearEquiv (q 1) = diagAtom 1 := by
      change g2.linearEquiv (g1.linearEquiv (g0.linearEquiv (q 1))) = diagAtom 1
      rw [hq1_diag, hg1_diag 1, hg2_diag 1]
    let u3 := g.linearEquiv (q 3)
    have hu3_atom : IsAtom u3 := g.map_isAtom (hq_atom 3)
    have hquat : ∃ (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ),
        u3.2 0 ∈ Set.range φ ∧ u3.2 1 ∈ Set.range φ ∧ u3.2 2 ∈ Set.range φ := by
      by_cases hu3d0 : u3.1 0 = 0
      · obtain ⟨hz01, hz02⟩ := isAtom_zero_row0 hu3_atom hu3d0
        obtain ⟨φ, hφ, h12, _⟩ := exists_quatEmbedding_containing_pair (u3.2 2) octOne
        exact ⟨φ, hφ, by rw [hz01]; exact ⟨0, map_zero φ⟩,
          by rw [hz02]; exact ⟨0, map_zero φ⟩, h12⟩
      · obtain ⟨φ, hφ, h01, h02⟩ := exists_quatEmbedding_containing_pair (u3.2 0) (u3.2 1)
        rcases h01 with ⟨a01, ha01⟩
        rcases h02 with ⟨a02, ha02⟩
        have hsharp := albertSharp_atom_eq_zero u3 hu3_atom
        have hf := congrArg (fun a : Albert => a.2 2) hsharp
        have heq : u3.1 0 • u3.2 2 = octonionMul (octonionConj (u3.2 0)) (u3.2 1) :=
          (sub_eq_zero.mp hf).symm
        have h12 : u3.2 2 ∈ Set.range φ := by
          refine ⟨(1 / u3.1 0 : ℝ) • (star a01 * a02), ?_⟩
          rw [map_smul, hφ.map_mul, hφ.map_star, ha01, ha02, ← heq, smul_smul, one_div,
            inv_mul_cancel₀ hu3d0, one_smul]
        exact ⟨φ, hφ, ⟨a01, ha01⟩, ⟨a02, ha02⟩, h12⟩
    obtain ⟨φ, hφ, h3_01, h3_02, h3_12⟩ := hquat
    let Q0 := quaternionicWindowOfQuatEmbedding φ hφ
    have hscalar_mem : ∀ r : ℝ, octonionScalar r ∈ Set.range φ := fun r =>
      ⟨r • (1 : Quaternion ℝ), by
        rw [map_smul, hφ.map_one]
        exact (octonionScalar_eq_smul r).symm⟩
    have hmem_Q0 : ∀ x : Albert, x.2 0 ∈ Set.range φ → x.2 1 ∈ Set.range φ →
        x.2 2 ∈ Set.range φ → x ∈ Q0.subalgebra.carrier := by
      intro x hx0 hx1 hx2
      rcases hx0 with ⟨a0, ha0⟩
      rcases hx1 with ⟨a1, ha1⟩
      rcases hx2 with ⟨a2, ha2⟩
      rw [← Q0.range_eq]
      refine ⟨quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]), ?_⟩
      change quatMatrixToAlbert φ ((quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]) : QuatHermitian3) : QuatMatrix3) = x
      have hp' := quatHermitian3Equiv.apply_symm_apply (x.1, ![a0, a1, a2])
      apply albert_ext
      · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 0) hp'
      · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 1) hp'
      · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 2) hp'
      · change φ _ = x.2 0
        have h := congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 0) hp'
        change ((quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]) : QuatMatrix3) 0 1) = a0 at h
        rw [h, ha0]
      · change φ _ = x.2 1
        have h := congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 1) hp'
        change ((quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]) : QuatMatrix3) 0 2) = a1 at h
        rw [h, ha1]
      · change φ _ = x.2 2
        have h := congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 2) hp'
        change ((quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]) : QuatMatrix3) 1 2) = a2 at h
        rw [h, ha2]
    refine ⟨Q0.transport g.symm, fun k => ?_⟩
    have hk_eq : p k = q (σ.symm k) := by simp [q]
    rw [hk_eq]
    refine ⟨g.linearEquiv (q (σ.symm k)), ?_, g.linearEquiv.symm_apply_apply _⟩
    match hidx : σ.symm k with
    | 0 =>
      rw [hq0_g]
      exact hmem_Q0 _ ⟨0, map_zero φ⟩ ⟨0, map_zero φ⟩ ⟨0, map_zero φ⟩
    | 1 =>
      rw [hq1_g]
      exact hmem_Q0 _ ⟨0, map_zero φ⟩ ⟨0, map_zero φ⟩ ⟨0, map_zero φ⟩
    | 2 =>
      exact hmem_Q0 _
        (by change (g2.linearEquiv s2).2 0 ∈ Set.range φ; rw [ht2_01]; exact hscalar_mem _)
        (by change (g2.linearEquiv s2).2 1 ∈ Set.range φ; rw [ht2_02]; exact hscalar_mem _)
        (by change (g2.linearEquiv s2).2 2 ∈ Set.range φ; rw [ht2_12]; exact hscalar_mem _)
    | 3 =>
      exact hmem_Q0 _ h3_01 h3_02 h3_12

/-! ## Section 5: The Zero Set (`lem:A:zero`) -/

private def inStandardQuat (x : Albert) : Prop :=
  (x.2 0).2 = 0 ∧ (x.2 1).2 = 0 ∧ (x.2 2).2 = 0

private theorem mem_standardQuat_iff (x : Albert) :
    x ∈ standardQuaternionicWindow.subalgebra.carrier ↔ inStandardQuat x := by
  constructor
  · intro hx
    rw [← standardQuaternionicWindow.range_eq] at hx
    rcases hx with ⟨M, hM⟩
    rw [← hM]
    change (quatEmbed1 _).2 = 0 ∧ (quatEmbed1 _).2 = 0 ∧ (quatEmbed1 _).2 = 0
    simp [quatEmbed1_apply]
  · intro hx
    rw [← standardQuaternionicWindow.range_eq]
    refine ⟨quatHermitian3Equiv.symm (x.1, ![((x.2 0).1), ((x.2 1).1), ((x.2 2).1)]), ?_⟩
    change quatMatrixToAlbert quatEmbed1
      ((quatHermitian3Equiv.symm (x.1, ![((x.2 0).1), ((x.2 1).1), ((x.2 2).1)]) : QuatHermitian3) : QuatMatrix3) = x
    have hp' := quatHermitian3Equiv.apply_symm_apply (x.1, ![((x.2 0).1), ((x.2 1).1), ((x.2 2).1)])
    apply albert_ext
    · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 0) hp'
    · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 1) hp'
    · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 2) hp'
    · change quatEmbed1 ((quatHermitian3Equiv.symm (x.1, ![((x.2 0).1), ((x.2 1).1), ((x.2 2).1)]) : QuatMatrix3) 0 1) = x.2 0
      change quatEmbed1 (x.2 0).1 = x.2 0
      exact Prod.ext rfl hx.1.symm
    · change quatEmbed1 ((quatHermitian3Equiv.symm (x.1, ![((x.2 0).1), ((x.2 1).1), ((x.2 2).1)]) : QuatMatrix3) 0 2) = x.2 1
      change quatEmbed1 (x.2 1).1 = x.2 1
      exact Prod.ext rfl hx.2.1.symm
    · change quatEmbed1 ((quatHermitian3Equiv.symm (x.1, ![((x.2 0).1), ((x.2 1).1), ((x.2 2).1)]) : QuatMatrix3) 1 2) = x.2 2
      change quatEmbed1 (x.2 2).1 = x.2 2
      exact Prod.ext rfl hx.2.2.symm

private theorem octMul_quat_snd_zero {a b : Octonion} (ha : a.2 = 0) (hb : b.2 = 0) :
    (octonionMul a b).2 = 0 := by
  have h1 : a = quatEmbed1 a.1 := Prod.ext rfl ha
  have h2 : b = quatEmbed1 b.1 := Prod.ext rfl hb
  rw [h1, h2, ← quatEmbed1_isQuatEmbedding.map_mul]
  rfl

private theorem octConj_quat_snd_zero {a : Octonion} (ha : a.2 = 0) :
    (octonionConj a).2 = 0 := by
  have h1 : a = quatEmbed1 a.1 := Prod.ext rfl ha
  rw [h1, ← quatEmbed1_isQuatEmbedding.map_star]
  rfl

private theorem middleMoufang_preserves_quat {u : Octonion} (hu : octNormSq u = 1) (huq : u.2 = 0)
    {x : Albert} (hx : inStandardQuat x) :
    inStandardQuat ((middleMoufangAlbertAuto u hu).linearEquiv x) := by
  rw [middleMoufangAlbertAuto_apply]
  exact ⟨octMul_quat_snd_zero huq hx.1,
    octMul_quat_snd_zero (octMul_quat_snd_zero huq hx.2.1) huq,
    octMul_quat_snd_zero hx.2.2 huq⟩

private theorem familyCMoufang_preserves_quat {u : Octonion} (hu : octNormSq u = 1) (huq : u.2 = 0)
    {x : Albert} (hx : inStandardQuat x) :
    inStandardQuat ((familyCMoufangAlbertAuto u hu).linearEquiv x) := by
  rw [familyCMoufangAlbertAuto_apply]
  exact ⟨octMul_quat_snd_zero (octMul_quat_snd_zero huq hx.1) huq,
    octMul_quat_snd_zero huq hx.2.1,
    octMul_quat_snd_zero (octConj_quat_snd_zero huq) hx.2.2⟩

private theorem swap01_preserves_quat {x : Albert} (hx : inStandardQuat x) :
    inStandardQuat (swap01AlbertAuto.linearEquiv x) := by
  rw [swap01AlbertAuto_apply]
  exact ⟨octConj_quat_snd_zero hx.1, hx.2.2, hx.2.1⟩

private theorem swap02_preserves_quat {x : Albert} (hx : inStandardQuat x) :
    inStandardQuat (swap02AlbertAuto.linearEquiv x) := by
  rw [swap02AlbertAuto_apply]
  exact ⟨octConj_quat_snd_zero hx.2.2, octConj_quat_snd_zero hx.2.1, octConj_quat_snd_zero hx.1⟩

private theorem swap12_preserves_quat {x : Albert} (hx : inStandardQuat x) :
    inStandardQuat (swap12AlbertAuto.linearEquiv x) := by
  rw [swap12AlbertAuto_apply]
  exact ⟨hx.2.1, hx.1, octConj_quat_snd_zero hx.2.2⟩

private theorem realRotation12_preserves_quat (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1)
    {x : Albert} (hx : inStandardQuat x) :
    inStandardQuat ((realRotation12AlbertAuto c s h).linearEquiv x) := by
  have hentry : ∀ i j : Fin 3, (realConjMatrix (realRotation12 c s) (albertMatrix x) i j).2 = 0 := by
    intro i j
    have hM : ∀ k l : Fin 3, (albertMatrix x k l).2 = 0 := fun k l => by
      fin_cases k <;> fin_cases l
      · rfl
      · exact hx.1
      · exact hx.2.1
      · exact octConj_quat_snd_zero hx.1
      · rfl
      · exact hx.2.2
      · exact octConj_quat_snd_zero hx.2.1
      · exact octConj_quat_snd_zero hx.2.2
      · rfl
    rw [realConjMatrix, Fin.sum_univ_three]
    have hrow : ∀ k : Fin 3,
        (∑ l : Fin 3, (realRotation12 c s i k * realRotation12 c s j l) • albertMatrix x k l).2 = 0 :=
      fun k => by
        rw [Fin.sum_univ_three]
        simp only [oct_snd_add, oct_snd_smul, hM, smul_zero, add_zero]
    simp only [oct_snd_add, hrow, add_zero]
  change ((albertCoordinates (realConjMatrix (realRotation12 c s) (albertMatrix x))).2 0).2 = 0 ∧
    ((albertCoordinates (realConjMatrix (realRotation12 c s) (albertMatrix x))).2 1).2 = 0 ∧
    ((albertCoordinates (realConjMatrix (realRotation12 c s) (albertMatrix x))).2 2).2 = 0
  exact ⟨hentry 0 1, hentry 0 2, hentry 1 2⟩

private theorem realRotation12_diagAtom0 (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (realRotation12AlbertAuto c s h).linearEquiv (diagAtom 0) = diagAtom 0 := by
  change realConjAlbert (realRotation12 c s) (diagAtom 0) = diagAtom 0
  have hM0 : ∀ k l : Fin 3, albertMatrix (diagAtom 0) k l =
      if k = 0 ∧ l = 0 then octonionScalar 1 else 0 := fun k l => by
    fin_cases k <;> fin_cases l <;>
      simp [albertMatrix, diagAtom_fst, diagAtom_snd, octonionConj_zero, octonionScalar_zero]
  have hent : ∀ i j : Fin 3,
      realConjMatrix (realRotation12 c s) (albertMatrix (diagAtom 0)) i j =
        if i = 0 ∧ j = 0 then octonionScalar 1 else 0 := fun i j => by
    rw [realConjMatrix, Fin.sum_univ_three]
    simp only [Fin.sum_univ_three, hM0]
    fin_cases i <;> fin_cases j <;> simp [realRotation12, octonionScalar_zero]
  apply albert_ext <;>
    simp [realConjAlbert, albertCoordinates, hent, diagAtom_fst, diagAtom_snd,
      octonionReal_scalar, octonionReal_zero]

private theorem realRotation12_octDyad_real (b0 b1 b2 : ℝ) :
    let r := Real.sqrt (b1 ^ 2 + b2 ^ 2)
    ∃ c s : ℝ, ∃ h : c ^ 2 + s ^ 2 = 1,
      (realRotation12AlbertAuto c s h).linearEquiv
        (octDyad ![octonionScalar b0, octonionScalar b1, octonionScalar b2]) =
      octDyad ![octonionScalar b0, octonionScalar r, 0] := by
  intro r
  by_cases hr : r = 0
  · have hb1 : b1 = 0 := by
      have hsq : b1 ^ 2 + b2 ^ 2 = 0 := by
        nlinarith [Real.sq_sqrt (add_nonneg (sq_nonneg b1) (sq_nonneg b2)), hr]
      nlinarith [sq_nonneg b1, sq_nonneg b2]
    have hb2 : b2 = 0 := by
      have hsq : b1 ^ 2 + b2 ^ 2 = 0 := by
        nlinarith [Real.sq_sqrt (add_nonneg (sq_nonneg b1) (sq_nonneg b2)), hr]
      nlinarith [sq_nonneg b1, sq_nonneg b2]
    refine ⟨1, 0, by norm_num, ?_⟩
    have hmat : realRotation12 1 0 = 1 := by
      funext i j; fin_cases i <;> fin_cases j <;> simp [realRotation12]
    have hent1 : ∀ (x : Albert) (i j : Fin 3),
        realConjMatrix (1 : Matrix (Fin 3) (Fin 3) ℝ) (albertMatrix x) i j = albertMatrix x i j := by
      intro x i j
      rw [realConjMatrix]
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Fin.sum_univ_three]
    have hid : (realRotation12AlbertAuto 1 0 (by norm_num)).linearEquiv
        (octDyad ![octonionScalar b0, octonionScalar b1, octonionScalar b2]) =
        octDyad ![octonionScalar b0, octonionScalar b1, octonionScalar b2] := by
      change realConjAlbert (realRotation12 1 0) _ = _
      unfold realConjAlbert
      rw [hmat]
      apply albert_ext <;> simp [albertCoordinates, hent1, albertMatrix, octonionReal_scalar]
    rw [hid, hr, hb1, hb2]
    simp [octonionScalar_zero]
  · have hr2 : r ^ 2 = b1 ^ 2 + b2 ^ 2 := Real.sq_sqrt (add_nonneg (sq_nonneg b1) (sq_nonneg b2))
    let c := b1 / r
    let s := b2 / r
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      dsimp only [c, s]; rw [div_pow, div_pow, ← add_div, ← hr2, div_self (pow_ne_zero 2 hr)]
    have hcs1 : c * b1 + s * b2 = r := by
      dsimp only [c, s]; field_simp [hr]; nlinarith [hr2]
    have hcs2 : -s * b1 + c * b2 = 0 := by
      dsimp only [c, s]; field_simp [hr]; ring
    refine ⟨c, s, hcs, ?_⟩
    let x := octDyad ![octonionScalar b0, octonionScalar b1, octonionScalar b2]
    change realConjAlbert (realRotation12 c s) x =
      octDyad ![octonionScalar b0, octonionScalar r, 0]
    have hrow_vec : ∀ i : Fin 3,
        (∑ k : Fin 3, realRotation12 c s i k * ![b0, b1, b2] k) = ![b0, r, 0] i := fun i => by
      fin_cases i <;> simp [Fin.sum_univ_three, realRotation12]
      · exact hcs1
      · simpa [neg_mul] using hcs2
    have hent : ∀ i j : Fin 3,
        realConjMatrix (realRotation12 c s) (albertMatrix x) i j =
          octonionScalar (![b0, r, 0] i * ![b0, r, 0] j) := by
      intro i j
      have hM : ∀ k l : Fin 3,
          albertMatrix x k l = octonionScalar (![b0, b1, b2] k * ![b0, b1, b2] l) := by
        intro k l
        fin_cases k <;> fin_cases l <;>
          (dsimp [x, albertMatrix, octDyad_fst, octDyad_snd_0, octDyad_snd_1, octDyad_snd_2];
            simp [octNormSq_scalar, octonionConj_scalar, octonionMul_scalar_left, ← octonionScalar_smul];
            try (congr 1; ring))
      unfold realConjMatrix
      simp only [hM, ← octonionScalar_smul, Fin.sum_univ_three, ← octonionScalar_add]
      congr 1
      rw [← hrow_vec i, ← hrow_vec j, Fin.sum_univ_three, Fin.sum_univ_three]
      ring
    apply albert_ext
    · change octonionReal (realConjMatrix (realRotation12 c s) (albertMatrix x) 0 0) = _
      rw [hent 0 0, octonionReal_scalar, octDyad_fst]; simp [octNormSq_scalar]; ring
    · change octonionReal (realConjMatrix (realRotation12 c s) (albertMatrix x) 1 1) = _
      rw [hent 1 1, octonionReal_scalar, octDyad_fst]; simp [octNormSq_scalar]; ring
    · change octonionReal (realConjMatrix (realRotation12 c s) (albertMatrix x) 2 2) = _
      rw [hent 2 2, octonionReal_scalar, octDyad_fst]; simp [octNormSq_zero]
    · change realConjMatrix (realRotation12 c s) (albertMatrix x) 0 1 = _
      rw [hent 0 1, octDyad_snd_0]; simp [octonionMul_scalar_left, octonionConj_scalar, ← octonionScalar_smul]
    · change realConjMatrix (realRotation12 c s) (albertMatrix x) 0 2 = _
      rw [hent 0 2, octDyad_snd_1]; simp [octonionConj_zero, octonionMul_zero_right, octonionScalar_zero]
    · change realConjMatrix (realRotation12 c s) (albertMatrix x) 1 2 = _
      rw [hent 1 2, octDyad_snd_2]; simp [octonionConj_zero, octonionMul_zero_right, octonionScalar_zero]

private theorem exists_quat_frameStab_slot01_real (x : Albert) (hx : inStandardQuat x) :
    ∃ g : NativeAlbertAutomorphism, (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      (∀ y, inStandardQuat y → inStandardQuat (g.linearEquiv y)) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 0 = octonionScalar r := by
  by_cases h0 : x.2 0 = 0
  · exact ⟨NativeAlbertAutomorphism.refl, fun _ => rfl, fun _ hy => hy, 0, le_rfl,
      by simp [NativeAlbertAutomorphism.refl, h0, octonionScalar_zero]⟩
  · have hpos : 0 < octNormSq (x.2 0) :=
      lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => h0 ((octNormSq_eq_zero _).mp h))
    let r := Real.sqrt (octNormSq (x.2 0))
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : octNormSq (x.2 0) = r ^ 2 := (Real.sq_sqrt hpos.le).symm
    let u := (1 / r) • octonionConj (x.2 0)
    have hu : octNormSq u = 1 := by
      dsimp only [u]
      rw [octNormSq_smul, octNormSq_conj, hr2, one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
    have huq : u.2 = 0 := by
      dsimp only [u]
      change (1 / r) • (octonionConj (x.2 0)).2 = 0
      rw [octConj_quat_snd_zero hx.1, smul_zero]
    refine ⟨middleMoufangAlbertAuto u hu, middleMoufangAlbertAuto_diagAtom u hu,
      fun y hy => middleMoufang_preserves_quat hu huq hy, r, hr.le, ?_⟩
    rw [middleMoufangAlbertAuto_apply]
    change octonionMul u (x.2 0) = octonionScalar r
    dsimp only [u]
    rw [octonionMul_smul_left, octMul_conj_self, hr2, ← octonionScalar_smul]
    congr 1; field_simp [hr.ne']

private theorem exists_quat_unit_imag_ortho (a : Octonion) (ha : a.2 = 0) :
    ∃ u : Octonion, octonionReal u = 0 ∧ octNormSq u = 1 ∧
      octDot u (octIm a) = 0 ∧ u.2 = 0 := by
  let p1 := octDot octI (octIm a)
  let p2 := octDot octJ (octIm a)
  by_cases h1 : p1 = 0
  · exact ⟨octI, rfl, by rw [octNormSq_eq_coords]; simp [octI], h1, rfl⟩
  · by_cases h2 : p2 = 0
    · exact ⟨octJ, rfl, by rw [octNormSq_eq_coords]; simp [octJ], h2, rfl⟩
    · let v := p2 • octI - p1 • octJ
      have hv_re : octonionReal v = 0 := by
        dsimp only [v]
        rw [octonionReal_sub, octonionReal_smul, octonionReal_smul]
        simp [octI, octJ, octonionReal]
      have hv_ns : octNormSq v = p2 ^ 2 + p1 ^ 2 := by
        rw [octNormSq_sub, octNormSq_smul, octNormSq_smul,
          show octNormSq octI = 1 from by rw [octNormSq_eq_coords]; simp [octI],
          show octNormSq octJ = 1 from by rw [octNormSq_eq_coords]; simp [octJ],
          octDot_smul_left, octDot_smul_right,
          show octDot octI octJ = 0 from by rw [octDot_eq_coords]; simp [octI, octJ]]
        ring
      have hv_pos : 0 < octNormSq v := by rw [hv_ns]; positivity
      let n := Real.sqrt (octNormSq v)
      refine ⟨(1 / n) • v, by simp [octonionReal_smul, hv_re], ?_, ?_, ?_⟩
      · rw [octNormSq_smul, one_div, inv_pow, Real.sq_sqrt hv_pos.le]; field_simp [hv_pos.ne']
      · rw [octDot_smul_left, octDot_sub_left, octDot_smul_left, octDot_smul_left]
        change (1 / n) * (p2 * p1 - p1 * p2) = 0; ring
      · change (1 / n) • (p2 • octI.2 - p1 • octJ.2) = 0
        rw [show octI.2 = 0 from rfl, show octJ.2 = 0 from rfl, smul_zero, smul_zero, sub_zero, smul_zero]

private theorem familyCMoufang_imag_slot01_one_local {u : Octonion}
    (hre : octonionReal u = 0) (hu : octNormSq u = 1) :
    (familyCMoufangAlbertAuto u hu).linearEquiv (slotElem01 octOne) = -slotElem01 octOne := by
  have hsq : octonionMul (octonionMul u octOne) u = -octOne := by
    rw [octonionMul_one_right, octonionMul_imag_sq hre, hu, neg_smul, one_smul]
  rw [familyCMoufangAlbertAuto_apply]
  apply albert_ext <;>
    simp [slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2,
      albert_neg_fst, albert_neg_snd, hsq, octonionMul_zero_right]

private theorem exists_quat_frameAnd01OneStab_slot02_real (x : Albert) (hx : inStandardQuat x) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      g.linearEquiv (slotElem01 octOne) = slotElem01 octOne ∧
      (∀ y, inStandardQuat y → inStandardQuat (g.linearEquiv y)) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 1 = octonionScalar r := by
  by_cases h1 : x.2 1 = 0
  · exact ⟨NativeAlbertAutomorphism.refl, fun _ => rfl, rfl, fun _ hy => hy, 0, le_rfl,
      by simp [NativeAlbertAutomorphism.refl, h1, octonionScalar_zero]⟩
  · have hpos : 0 < octNormSq (x.2 1) :=
      lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => h1 ((octNormSq_eq_zero _).mp h))
    let r := Real.sqrt (octNormSq (x.2 1))
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : octNormSq (x.2 1) = r ^ 2 := (Real.sq_sqrt hpos.le).symm
    let a := (1 / r) • x.2 1
    have haq : a.2 = 0 := by
      dsimp only [a]; change (1 / r) • (x.2 1).2 = 0; rw [hx.2.1, smul_zero]
    have ha_ns : octNormSq a = 1 := by
      dsimp only [a]
      rw [octNormSq_smul, hr2, one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
    obtain ⟨u1, hu1_re, hu1_ns, hu1_ortho, hu1q⟩ := exists_quat_unit_imag_ortho a haq
    let u2 := -octonionMul u1 a
    have hu2_re : octonionReal u2 = 0 := by
      simp only [u2, octonionReal_neg]
      have hre : octonionReal (octonionMul u1 a) = octDot u1 (octonionConj a) := by
        rw [octDot, octonionConj_conj]
      rw [hre, octConj_eq_two_real_sub a, octDot_sub_right, octDot_smul_right, octDot_comm u1 octOne,
        show octOne = octonionScalar 1 from rfl, octDot_scalar_left, hu1_re, mul_zero, mul_zero,
        zero_sub]
      have him : octDot u1 a = octDot u1 (octIm a) := by
        conv_lhs => rw [oct_eq_scalar_add_octIm a, octDot_add_right, octDot_comm u1 (octonionScalar _),
          octDot_scalar_left, hu1_re, mul_zero, zero_add]
      linarith
    have hu2_ns : octNormSq u2 = 1 := by simp [u2, octNormSq_neg, octNormSq_mul, hu1_ns, ha_ns]
    have hu2q : u2.2 = 0 := by
      dsimp only [u2]; change -(octonionMul u1 a).2 = 0
      rw [octMul_quat_snd_zero hu1q haq, neg_zero]
    let g1 := familyCMoufangAlbertAuto u1 hu1_ns
    let g2 := familyCMoufangAlbertAuto u2 hu2_ns
    have hq_pres : ∀ y, inStandardQuat y → inStandardQuat ((g2.comp g1).linearEquiv y) := fun y hy => by
      change inStandardQuat (g2.linearEquiv (g1.linearEquiv y))
      exact familyCMoufang_preserves_quat hu2_ns hu2q (familyCMoufang_preserves_quat hu1_ns hu1q hy)
    refine ⟨g2.comp g1, fun i => ?_, ?_, hq_pres, r, hr.le, ?_⟩
    · change g2.linearEquiv (g1.linearEquiv (diagAtom i)) = diagAtom i
      rw [familyCMoufangAlbertAuto_diagAtom, familyCMoufangAlbertAuto_diagAtom]
    · change g2.linearEquiv (g1.linearEquiv (slotElem01 octOne)) = slotElem01 octOne
      rw [familyCMoufang_imag_slot01_one_local hu1_re hu1_ns, map_neg,
        familyCMoufang_imag_slot01_one_local hu2_re hu2_ns, neg_neg]
    · change (g2.linearEquiv (g1.linearEquiv x)).2 1 = octonionScalar r
      rw [familyCMoufangAlbertAuto_apply, familyCMoufangAlbertAuto_apply]
      dsimp
      have hxa : x.2 1 = r • a := by
        dsimp only [a]; rw [smul_smul, mul_one_div_cancel hr.ne', one_smul]
      rw [hxa, octonionMul_smul_right, octonionMul_smul_right]
      have hprod : octonionMul u2 (octonionMul u1 a) = octOne := by
        have hc : octonionConj (octonionMul u1 a) = u2 :=
          octonionConj_eq_neg_of_real_zero (by simpa [u2, octonionReal_neg] using hu2_re)
        rw [← hc, octMul_conj_self, octNormSq_mul, hu1_ns, ha_ns, mul_one]; rfl
      rw [hprod, octonionScalar_eq_smul]; rfl

private theorem exists_quat_frameAnd01OneStab_slot12_real (x : Albert) (hx : inStandardQuat x) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ i, g.linearEquiv (diagAtom i) = diagAtom i) ∧
      g.linearEquiv (slotElem01 octOne) = slotElem01 octOne ∧
      (∀ y, inStandardQuat y → inStandardQuat (g.linearEquiv y)) ∧
      ∃ r : ℝ, 0 ≤ r ∧ (g.linearEquiv x).2 2 = octonionScalar r := by
  obtain ⟨h, hd, h01, hq, r, hr, hslot⟩ :=
    exists_quat_frameAnd01OneStab_slot02_real (swap01AlbertAuto.linearEquiv x) (swap01_preserves_quat hx)
  let g := (swap01AlbertAuto.comp h).comp swap01AlbertAuto
  refine ⟨g, ?_, ?_, fun y hy => swap01_preserves_quat (hq _ (swap01_preserves_quat hy)), r, hr, ?_⟩
  · intro i
    change swap01AlbertAuto.linearEquiv (h.linearEquiv (swap01AlbertAuto.linearEquiv (diagAtom i))) = diagAtom i
    rw [swap01AlbertAuto_diagAtom, hd, swap01AlbertAuto_diagAtom]; simp
  · have hswap : swap01AlbertAuto.linearEquiv (slotElem01 octOne) = slotElem01 octOne := by
      apply albert_ext <;>
        simp [swap01AlbertAuto_apply, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1,
          slotElem01_snd_2, octOne, octonionConj_scalar]
    change swap01AlbertAuto.linearEquiv (h.linearEquiv (swap01AlbertAuto.linearEquiv (slotElem01 octOne))) =
      slotElem01 octOne
    rw [hswap, h01, hswap]
  · change (swap01AlbertAuto.linearEquiv (h.linearEquiv (swap01AlbertAuto.linearEquiv x))).2 2 =
      octonionScalar r
    rw [swap01AlbertAuto_apply]
    exact hslot

private theorem exists_quatAuto_atom_to_diagAtom0 (p : Albert) (hp : IsAtom p)
    (hpq : inStandardQuat p) :
    ∃ g : NativeAlbertAutomorphism,
      (∀ y, inStandardQuat y → inStandardQuat (g.linearEquiv y)) ∧
      g.linearEquiv p = diagAtom 0 := by
  have hmax : ∃ σ : NativeAlbertAutomorphism,
      (∀ y, inStandardQuat y → inStandardQuat (σ.linearEquiv y)) ∧
      0 < (σ.linearEquiv p).1 0 := by
    by_cases h0 : 0 < p.1 0
    · exact ⟨NativeAlbertAutomorphism.refl, fun _ hy => hy, h0⟩
    · by_cases h1 : 0 < p.1 1
      · exact ⟨swap01AlbertAuto, fun _ hy => swap01_preserves_quat hy, by
          rw [swap01AlbertAuto_apply]; exact h1⟩
      · have h2 : 0 < p.1 2 := by
          have htr := hp.2; rw [albertTrace_eq_sum] at htr
          linarith [not_lt.mp h0, not_lt.mp h1]
        exact ⟨swap02AlbertAuto, fun _ hy => swap02_preserves_quat hy, by
          rw [swap02AlbertAuto_apply]; exact h2⟩
  obtain ⟨g0, hg0q, h0_pos⟩ := hmax
  let p1 := g0.linearEquiv p
  have hp1_atom : IsAtom p1 := g0.map_isAtom hp
  have hp1_q : inStandardQuat p1 := hg0q p hpq
  obtain ⟨g1, hg1_diag, hg1_q, r01, hr01, hg1_01⟩ := exists_quat_frameStab_slot01_real p1 hp1_q
  let p2 := g1.linearEquiv p1
  have hp2_atom : IsAtom p2 := g1.map_isAtom hp1_atom
  have hp2_q : inStandardQuat p2 := hg1_q p1 hp1_q
  obtain ⟨g2, hg2_diag, hg2_01, hg2_q, r02, hr02, hg2_02⟩ :=
    exists_quat_frameAnd01OneStab_slot02_real p2 hp2_q
  let p3 := g2.linearEquiv p2
  have hp3_atom : IsAtom p3 := g2.map_isAtom hp2_atom
  have hp3_d0 : 0 < p3.1 0 := by
    have htr := (g2.comp g1).map_tracePairing (diagAtom 0) p1
    have hf0 : (g2.comp g1).linearEquiv (diagAtom 0) = diagAtom 0 := by
      change g2.linearEquiv (g1.linearEquiv (diagAtom 0)) = diagAtom 0
      rw [hg1_diag 0, hg2_diag 0]
    rw [hf0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
    change p3.1 0 = p1.1 0 at htr
    linarith
  have hp3_01 : p3.2 0 = octonionScalar r01 := by
    have h01_eq : (g2.linearEquiv (slotElem01 (p2.2 0))).2 0 = p3.2 0 := by
      have hx := congrArg g2.linearEquiv (peirce01_extract p2)
      rw [map_smul, g2.preserves_product, g2.preserves_product, hg2_diag 0, hg2_diag 1,
        peirce01_extract] at hx
      have heq := congrArg (fun a : Albert => a.2 0) hx
      simp [albert_smul_snd, slotElem01_snd_0] at heq
      exact heq.symm
    have hsc : slotElem01 (p2.2 0) = r01 • slotElem01 octOne := by
      rw [hg1_01, octonionScalar_eq_smul, ← octOne, map_smul]
    rw [← h01_eq, hsc, map_smul, hg2_01, albert_smul_snd, slotElem01_snd_0]
    exact (octonionScalar_eq_smul r01).symm
  let b0 := Real.sqrt (p3.1 0)
  let b1 := r01 / b0
  let b2 := r02 / b0
  have hp3_eq : p3 = octDyad ![octonionScalar b0, octonionScalar b1, octonionScalar b2] := by
    obtain ⟨hdy, _⟩ := isAtom_eq_octDyad hp3_atom hp3_d0
    rw [hdy]
    refine congrArg octDyad (vec3_eq rfl ?_ ?_)
    · dsimp only [atomDyadVec, b0, b1]
      rw [hp3_01, octonionConj_scalar, ← octonionScalar_smul]
      congr 1; ring
    · dsimp only [atomDyadVec, b0, b2]
      rw [hg2_02, octonionConj_scalar, ← octonionScalar_smul]
      congr 1; ring
  obtain ⟨c1, s1, hcs1, hr1⟩ := realRotation12_octDyad_real b0 b1 b2
  let r1 := Real.sqrt (b1 ^ 2 + b2 ^ 2)
  let g3 := realRotation12AlbertAuto c1 s1 hcs1
  let p4 := g3.linearEquiv p3
  have hp4_atom : IsAtom p4 := g3.map_isAtom hp3_atom
  have hp4_eq : p4 = octDyad ![octonionScalar b0, octonionScalar r1, 0] := by
    change g3.linearEquiv p3 = _
    rw [hp3_eq]; exact hr1
  have hb0r1 : b0 ^ 2 + r1 ^ 2 = 1 := by
    have htr := hp4_atom.2
    rw [albertTrace_eq_sum, hp4_eq] at htr
    simp [octDyad_fst, octNormSq_scalar, octNormSq_zero] at htr
    exact htr
  let g4 := swap02AlbertAuto
  have hp5_eq : g4.linearEquiv p4 = octDyad ![0, octonionScalar r1, octonionScalar b0] := by
    dsimp only [g4]
    rw [hp4_eq]
    apply albert_ext <;>
      (simp [swap02AlbertAuto_apply, octDyad_fst, octDyad_snd_0, octDyad_snd_1, octDyad_snd_2,
        octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionConj_scalar,
        octonionMul_zero_left, octonionMul_zero_right, octonionMul_scalar_left,
        ← octonionScalar_smul]; try (congr 1; ring))
  obtain ⟨c2, s2, hcs2, hr2⟩ := realRotation12_octDyad_real 0 r1 b0
  let g5 := realRotation12AlbertAuto c2 s2 hcs2
  have hr2_one : Real.sqrt (r1 ^ 2 + b0 ^ 2) = 1 := by
    rw [add_comm, hb0r1, Real.sqrt_one]
  have hp6_eq : g5.linearEquiv (g4.linearEquiv p4) = diagAtom 1 := by
    dsimp only [g5]
    rw [hp5_eq,
      show ![0, octonionScalar r1, octonionScalar b0] =
          ![octonionScalar 0, octonionScalar r1, octonionScalar b0] from
        vec3_eq octonionScalar_zero.symm rfl rfl,
      hr2, hr2_one]
    apply albert_ext <;>
      simp [octDyad_fst, octDyad_snd_0, octDyad_snd_1, octDyad_snd_2, diagAtom_fst, diagAtom_snd,
        octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionConj_scalar, octonionScalar_zero,
        octonionMul_zero_left, octonionMul_zero_right]
  let g6 := swap01AlbertAuto
  have hp7_eq : g6.linearEquiv (g5.linearEquiv (g4.linearEquiv p4)) = diagAtom 0 := by
    rw [hp6_eq, swap01AlbertAuto_diagAtom]; rfl
  let g := g6.comp (g5.comp (g4.comp (g3.comp (g2.comp (g1.comp g0)))))
  refine ⟨g, fun y hy => ?_, ?_⟩
  · exact swap01_preserves_quat (realRotation12_preserves_quat c2 s2 hcs2
      (swap02_preserves_quat (realRotation12_preserves_quat c1 s1 hcs1
        (hg2_q _ (hg1_q _ (hg0q _ hy))))))
  · exact hp7_eq

private theorem octAuto_quat_preserves_snd_zero (e1 e2 : Octonion)
    (he1_im : octonionReal e1 = 0) (he2_im : octonionReal e2 = 0)
    (he1_n : octNormSq e1 = 1) (he2_n : octNormSq e2 = 1)
    (h12 : octDot e1 e2 = 0) (he1q : e1.2 = 0) (he2q : e2.2 = 0) :
    let h13 : octDot e1 octL = 0 := by rw [octDot_eq_coords]; simp [octL, he1q]
    let h23 : octDot e2 octL = 0 := by rw [octDot_eq_coords]; simp [octL, he2q]
    let h3_12 : octDot octL (octonionMul e1 e2) = 0 := by
      rw [octDot_eq_coords]; simp [octL, octMul_quat_snd_zero he1q he2q]
    let α := octAutoOfBasicTriple e1 e2 octL he1_im he2_im rfl he1_n he2_n
      (by rw [octNormSq_eq_coords]; simp [octL]) h12 h13 h23 h3_12
    ∀ z : Octonion, z.2 = 0 → (α.symm.equiv z).2 = 0 := by
  intro h13 h23 h3_12 α z hz
  let T : Quaternion ℝ →ₗ[ℝ] Quaternion ℝ :=
    { toFun := fun q => (α.equiv (quatEmbed1 q)).1
      map_add' := fun a b => by
        have h := congrArg Prod.fst (α.equiv.map_add (quatEmbed1 a) (quatEmbed1 b))
        rw [← quatEmbed1.map_add] at h
        exact h
      map_smul' := fun r a => by
        have h := congrArg Prod.fst (α.equiv.map_smul r (quatEmbed1 a))
        rw [← quatEmbed1.map_smul] at h
        exact h }
  have hmemH : ∀ q : Quaternion ℝ, (α.equiv (quatEmbed1 q)).2 = 0 := fun q => by
    have hqdec : quatEmbed1 q = q.re • octOne + q.imI • octI + q.imJ • octJ + q.imK • octK := by
      apply oct_ext <;>
        simp only [oct_add_re, oct_add_imI, oct_add_imJ, oct_add_imK,
          oct_add_s_re, oct_add_s_imI, oct_add_s_imJ, oct_add_s_imK,
          oct_smul_re, oct_smul_imI, oct_smul_imJ, oct_smul_imK,
          oct_smul_s_re, oct_smul_s_imI, oct_smul_s_imJ, oct_smul_s_imK] <;>
        (simp [quatEmbed1_apply, octOne, octonionScalar_coord, octI, octJ, octK]; try ring)
    have hαI : α.equiv octI = e1 :=
      octAutoOfBasicTriple_I e1 e2 octL he1_im he2_im rfl he1_n he2_n
        (by rw [octNormSq_eq_coords]; simp [octL]) h12 h13 h23 h3_12
    have hαJ : α.equiv octJ = e2 :=
      octAutoOfBasicTriple_J e1 e2 octL he1_im he2_im rfl he1_n he2_n
        (by rw [octNormSq_eq_coords]; simp [octL]) h12 h13 h23 h3_12
    have hK : α.equiv octK = octonionMul e1 e2 := by
      rw [← octK_eq_mul, α.map_mul, hαI, hαJ]
    rw [hqdec]
    simp only [map_add, map_smul, α.map_one, hαI, hαJ, hK]
    change (q.re • octOne.2 + q.imI • e1.2 + q.imJ • e2.2 + q.imK • (octonionMul e1 e2).2) = 0
    rw [show octOne.2 = 0 from rfl, he1q, he2q, octMul_quat_snd_zero he1q he2q,
      smul_zero, smul_zero, smul_zero, smul_zero, add_zero, add_zero, add_zero]
  have hT_inj : Function.Injective T := (injective_iff_map_eq_zero T).mpr fun q hq => by
    have h0 : α.equiv (quatEmbed1 q) = 0 := Prod.ext hq (hmemH q)
    have h1 : quatEmbed1 q = 0 := α.equiv.injective (h0.trans (map_zero α.equiv).symm)
    exact quatEmbed1_isQuatEmbedding.injective (h1.trans (map_zero quatEmbed1).symm)
  have hT_surj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT_inj
  obtain ⟨q, hq⟩ := hT_surj z.1
  have hzeq : α.equiv (quatEmbed1 q) = z := Prod.ext hq (by rw [hmemH q, hz])
  have hsymm : α.symm.equiv z = quatEmbed1 q := by
    apply α.equiv.injective
    simpa [OctonionAutomorphism.symm_apply] using hzeq.symm
  rw [hsymm]
  rfl

private theorem exists_quatAuto_to_sparseFourConfigOct (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hpq : ∀ i, inStandardQuat (p i)) :
    ∃ (g : NativeAlbertAutomorphism)
      (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : ℝ) (X Y : Octonion),
      (∀ i, inStandardQuat (g.linearEquiv (p i))) ∧
      (fun i => g.linearEquiv (p i)) = sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y := by
  obtain ⟨g0, hg0q, hg0_p0⟩ := exists_quatAuto_atom_to_diagAtom0 (p 0) (hp 0) (hpq 0)
  let q1 := g0.linearEquiv (p 1)
  let q2 := g0.linearEquiv (p 2)
  let q3 := g0.linearEquiv (p 3)
  have hq1_atom : IsAtom q1 := g0.map_isAtom (hp 1)
  have hq2_atom : IsAtom q2 := g0.map_isAtom (hp 2)
  have hq3_atom : IsAtom q3 := g0.map_isAtom (hp 3)
  have hq1_q : inStandardQuat q1 := hg0q (p 1) (hpq 1)
  have hq2_q : inStandardQuat q2 := hg0q (p 2) (hpq 2)
  have hq3_q : inStandardQuat q3 := hg0q (p 3) (hpq 3)
  obtain ⟨g1, hg1_diag, hg1_q, r01, hr01, hg1_01⟩ := exists_quat_frameStab_slot01_real q1 hq1_q
  let s1 := g1.linearEquiv q1
  have hs1_atom : IsAtom s1 := g1.map_isAtom hq1_atom
  have hs1_q : inStandardQuat s1 := hg1_q q1 hq1_q
  have hs1_step : ∃ g2 : NativeAlbertAutomorphism,
      g2.linearEquiv (diagAtom 0) = diagAtom 0 ∧
      (∀ y, inStandardQuat y → inStandardQuat (g2.linearEquiv y)) ∧
      ∃ B₀ B₁ : ℝ, g2.linearEquiv s1 = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] := by
    by_cases hs1d0 : s1.1 0 = 0
    · by_cases hs1d1 : 0 < s1.1 1
      · obtain ⟨g2, hd, _h01, hq, r12, hr12, hg2_12⟩ :=
          exists_quat_frameAnd01OneStab_slot12_real s1 hs1_q
        have hs1'_atom : IsAtom (g2.linearEquiv s1) := g2.map_isAtom hs1_atom
        have hs1'_d0 : (g2.linearEquiv s1).1 0 = 0 := by
          have htr := g2.map_tracePairing (diagAtom 0) s1
          rw [hd 0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
          exact htr.trans hs1d0
        have hs1'_d1 : 0 < (g2.linearEquiv s1).1 1 := by
          have htr := g2.map_tracePairing (diagAtom 1) s1
          rw [hd 1, tracePairing_diagAtom, tracePairing_diagAtom] at htr
          rw [htr]; exact hs1d1
        obtain ⟨_, _, _, hdy⟩ :=
          atom_diag1_eq_octDyad hs1'_atom hs1'_d0 hs1'_d1 ⟨r12, hr12, hg2_12⟩
        let s1' := g2.linearEquiv s1
        let b1 := Real.sqrt (s1'.1 1)
        let b2 := Real.sqrt (s1'.1 2)
        obtain ⟨c, s, hcs, hrot⟩ := realRotation12_octDyad_real 0 b1 b2
        let g3 := realRotation12AlbertAuto c s hcs
        refine ⟨g3.comp g2, ?_, fun y hy => realRotation12_preserves_quat c s hcs (hq y hy),
          0, Real.sqrt (b1 ^ 2 + b2 ^ 2), ?_⟩
        · change g3.linearEquiv (g2.linearEquiv (diagAtom 0)) = diagAtom 0
          rw [hd 0]
          exact realRotation12_diagAtom0 c s hcs
        · change g3.linearEquiv (g2.linearEquiv s1) = _
          rw [hdy]
          rw [show ![0, octonionScalar (Real.sqrt ((g2.linearEquiv s1).1 1)),
              octonionScalar (Real.sqrt ((g2.linearEquiv s1).1 2))] =
              ![octonionScalar 0, octonionScalar b1, octonionScalar b2] from
            vec3_eq octonionScalar_zero.symm rfl rfl]
          exact hrot
      · have hs1d1z : s1.1 1 = 0 := le_antisymm (not_lt.mp hs1d1) (isAtom_diag_nonneg hs1_atom 1)
        have hdy := atom_diag2_eq_octDyad hs1_atom hs1d0 hs1d1z
        refine ⟨swap12AlbertAuto, by rw [swap12AlbertAuto_diagAtom]; rfl,
          fun _ hy => swap12_preserves_quat hy, 0, 1, ?_⟩
        rw [hdy]
        apply albert_ext <;>
          simp [swap12AlbertAuto_apply, octDyad_fst, octDyad_snd_0, octDyad_snd_1, octDyad_snd_2,
            octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionScalar_zero,
            octonionMul_zero_left, octonionMul_zero_right]
    · have hs1d0_pos : 0 < s1.1 0 := lt_of_le_of_ne (isAtom_diag_nonneg hs1_atom 0) (Ne.symm hs1d0)
      obtain ⟨g2, hd, h01, hq, r02, hr02, hg2_02⟩ :=
        exists_quat_frameAnd01OneStab_slot02_real s1 hs1_q
      let t1 := g2.linearEquiv s1
      have ht1_atom : IsAtom t1 := g2.map_isAtom hs1_atom
      have ht1_d0 : 0 < t1.1 0 := by
        have htr := g2.map_tracePairing (diagAtom 0) s1
        rw [hd 0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
        change t1.1 0 = s1.1 0 at htr; linarith
      have ht1_01 : t1.2 0 = octonionScalar r01 := by
        have hx := congrArg g2.linearEquiv (peirce01_extract s1)
        rw [map_smul, g2.preserves_product, g2.preserves_product, hd 0, hd 1,
          peirce01_extract] at hx
        have hsc : slotElem01 (s1.2 0) = r01 • slotElem01 octOne := by
          rw [hg1_01, octonionScalar_eq_smul, ← octOne, map_smul]
        rw [hsc, map_smul, h01] at hx
        have heq := congrArg (fun a : Albert => a.2 0) hx
        rw [albert_smul_snd, slotElem01_snd_0, slotElem01_snd_0, octOne_eq_scalar] at heq
        change t1.2 0 = octonionScalar r01
        rw [heq, ← octonionScalar_eq_smul r01]
      let b0 := Real.sqrt (t1.1 0)
      let b1 := r01 / b0
      let b2 := r02 / b0
      have ht1_eq : t1 = octDyad ![octonionScalar b0, octonionScalar b1, octonionScalar b2] := by
        obtain ⟨hdy, _⟩ := isAtom_eq_octDyad ht1_atom ht1_d0
        rw [hdy]
        refine congrArg octDyad (vec3_eq rfl ?_ ?_)
        · dsimp only [atomDyadVec, b0, b1, t1]
          rw [ht1_01, octonionConj_scalar, ← octonionScalar_smul]
          congr 1; ring
        · dsimp only [atomDyadVec, b0, b2, t1]
          rw [hg2_02, octonionConj_scalar, ← octonionScalar_smul]
          congr 1; ring
      obtain ⟨c, s, hcs, hrot⟩ := realRotation12_octDyad_real b0 b1 b2
      let g3 := realRotation12AlbertAuto c s hcs
      refine ⟨g3.comp g2, ?_, fun y hy => realRotation12_preserves_quat c s hcs (hq y hy),
        b0, Real.sqrt (b1 ^ 2 + b2 ^ 2), ?_⟩
      · change g3.linearEquiv (g2.linearEquiv (diagAtom 0)) = diagAtom 0
        rw [hd 0]
        exact realRotation12_diagAtom0 c s hcs
      · change g3.linearEquiv t1 = _
        rw [ht1_eq]; exact hrot
  obtain ⟨g2, hg2_d0, hg2_q, B₀, B₁, hg2_s1⟩ := hs1_step
  let t1 := g2.linearEquiv s1
  let t2 := g2.linearEquiv (g1.linearEquiv q2)
  let t3 := g2.linearEquiv (g1.linearEquiv q3)
  have ht2_atom : IsAtom t2 := g2.map_isAtom (g1.map_isAtom hq2_atom)
  have ht2_q : inStandardQuat t2 := hg2_q _ (hg1_q q2 hq2_q)
  have ht3_q : inStandardQuat t3 := hg2_q _ (hg1_q q3 hq3_q)
  have ht2_step : ∃ g3 : NativeAlbertAutomorphism,
      (∀ i, g3.linearEquiv (diagAtom i) = diagAtom i) ∧
      g3.linearEquiv (slotElem01 octOne) = slotElem01 octOne ∧
      (∀ y, inStandardQuat y → inStandardQuat (g3.linearEquiv y)) ∧
      ∃ C₀ C₁ C₂ C₃ : ℝ,
        g3.linearEquiv t2 =
          octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃] := by
    by_cases ht2d0 : t2.1 0 = 0
    · obtain ⟨g3, hd, h01, hq, r12, hr12, hg3_12⟩ :=
        exists_quat_frameAnd01OneStab_slot12_real t2 ht2_q
      let u2 := g3.linearEquiv t2
      have hu2_atom : IsAtom u2 := g3.map_isAtom ht2_atom
      have hu2_d0 : u2.1 0 = 0 := by
        have htr := g3.map_tracePairing (diagAtom 0) t2
        rw [hd 0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
        exact htr.trans ht2d0
      by_cases hu2d1 : 0 < u2.1 1
      · obtain ⟨_, _, _, hdy⟩ :=
          atom_diag1_eq_octDyad hu2_atom hu2_d0 hu2d1 ⟨r12, hr12, hg3_12⟩
        refine ⟨g3, hd, h01, hq, 0, Real.sqrt (u2.1 1), 0, Real.sqrt (u2.1 2), ?_⟩
        change u2 = octDyad ![octonionScalar 0, octonionScalar (Real.sqrt (u2.1 1)) + 0 • octI,
          octonionScalar (Real.sqrt (u2.1 2))]
        conv_lhs => rw [hdy]
        apply congrArg octDyad
        apply vec3_eq
        · exact octonionScalar_zero.symm
        · rw [zero_smul, add_zero]
        · rfl
      · have hu2_d1z : u2.1 1 = 0 := le_antisymm (not_lt.mp hu2d1) (isAtom_diag_nonneg hu2_atom 1)
        have hdy := atom_diag2_eq_octDyad hu2_atom hu2_d0 hu2_d1z
        refine ⟨g3, hd, h01, hq, 0, 0, 0, 1, ?_⟩
        change u2 = _
        rw [hdy]
        exact congrArg octDyad (vec3_eq octonionScalar_zero.symm
          (by simp [octonionScalar_zero]) rfl)
    · have ht2d0_pos : 0 < t2.1 0 := lt_of_le_of_ne (isAtom_diag_nonneg ht2_atom 0) (Ne.symm ht2d0)
      obtain ⟨g3, hd, h01, hq, r02, hr02, hg3_02⟩ :=
        exists_quat_frameAnd01OneStab_slot02_real t2 ht2_q
      let u2 := g3.linearEquiv t2
      have hu2_atom : IsAtom u2 := g3.map_isAtom ht2_atom
      have hu2_q : inStandardQuat u2 := hq t2 ht2_q
      have hu2_d0 : 0 < u2.1 0 := by
        have htr := g3.map_tracePairing (diagAtom 0) t2
        rw [hd 0, tracePairing_diagAtom, tracePairing_diagAtom] at htr
        change u2.1 0 = t2.1 0 at htr; linarith
      let C₀ := Real.sqrt (u2.1 0)
      let z := (1 / C₀) • octonionConj (u2.2 0)
      have hzq : z.2 = 0 := by
        dsimp only [z]; change (1 / C₀) • (octonionConj (u2.2 0)).2 = 0
        rw [octConj_quat_snd_zero hu2_q.1, smul_zero]
      let C₃ := r02 / C₀
      let C₁ := octonionReal z
      let w := octIm z
      have hwq : w.2 = 0 := by
        dsimp only [w, octIm]
        change (z - octonionScalar (octonionReal z)).2 = 0
        rw [show (z - octonionScalar (octonionReal z)).2 = z.2 - (octonionScalar (octonionReal z)).2 from rfl,
          hzq, show (octonionScalar (octonionReal z)).2 = 0 from rfl, sub_zero]
      have hu2_eq : u2 = octDyad ![octonionScalar C₀, z, octonionScalar C₃] := by
        obtain ⟨hdy, _⟩ := isAtom_eq_octDyad hu2_atom hu2_d0
        rw [hdy]
        refine congrArg octDyad (vec3_eq rfl rfl ?_)
        dsimp only [atomDyadVec, C₀, C₃, u2]
        rw [hg3_02, octonionConj_scalar, ← octonionScalar_smul]
        congr 1; ring
      by_cases hw0 : w = 0
      · have hz_sc : z = octonionScalar C₁ := by
          rw [oct_eq_scalar_add_octIm z]; change octonionScalar C₁ + w = _; rw [hw0, add_zero]
        refine ⟨g3, hd, h01, hq, C₀, C₁, 0, C₃, ?_⟩
        rw [hz_sc] at hu2_eq
        simpa using hu2_eq
      · have hw_pos : 0 < octNormSq w :=
          lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => hw0 ((octNormSq_eq_zero _).mp h))
        let C₂ := Real.sqrt (octNormSq w)
        have hC2_pos : 0 < C₂ := Real.sqrt_pos.mpr hw_pos
        let e1 := (1 / C₂) • w
        have he1_im : octonionReal e1 = 0 := by simp [e1, octonionReal_smul, w, octonionReal_octIm]
        have he1_n : octNormSq e1 = 1 := by
          dsimp only [e1, C₂]
          rw [octNormSq_smul, one_div, inv_pow, Real.sq_sqrt hw_pos.le]
          field_simp [hw_pos.ne']
        have he1_q : e1.2 = 0 := by
          dsimp only [e1]; change (1 / C₂) • w.2 = 0; rw [hwq, smul_zero]
        let v1 := octI - octDot octI e1 • e1
        let v2 := octJ - octDot octJ e1 • e1
        have hv12 : v1 ≠ 0 ∨ v2 ≠ 0 := by
          by_contra h
          push Not at h
          have hi := sub_eq_zero.mp h.1
          have hj := sub_eq_zero.mp h.2
          have h0 : octDot octI octJ = 0 := by rw [octDot_eq_coords]; simp [octI, octJ]
          conv_lhs at h0 => rw [hi, hj]
          rw [octDot_smul_left (octDot octI e1), octDot_comm e1 (octDot octJ e1 • e1),
            octDot_smul_left (octDot octJ e1), octDot_self, he1_n, mul_one] at h0
          have hi_n : octNormSq octI = 1 := by rw [octNormSq_eq_coords]; simp [octI]
          have hj_n : octNormSq octJ = 1 := by rw [octNormSq_eq_coords]; simp [octJ]
          rw [hi, octNormSq_smul, he1_n, mul_one] at hi_n
          rw [hj, octNormSq_smul, he1_n, mul_one] at hj_n
          nlinarith [sq_nonneg (octDot octI e1), sq_nonneg (octDot octJ e1)]
        have hex_e2 : ∃ e2 : Octonion, octonionReal e2 = 0 ∧ octNormSq e2 = 1 ∧
            octDot e1 e2 = 0 ∧ e2.2 = 0 := by
          rcases hv12 with hv1 | hv2
          · have hnv1 : 0 < octNormSq v1 :=
              lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => hv1 ((octNormSq_eq_zero _).mp h))
            let s := Real.sqrt (octNormSq v1)
            refine ⟨(1 / s) • v1, ?_, ?_, ?_, ?_⟩
            · simp [v1, octonionReal_smul, octonionReal_sub, he1_im, show octonionReal octI = 0 from rfl]
            · rw [octNormSq_smul, one_div, inv_pow, Real.sq_sqrt hnv1.le]; field_simp [hnv1.ne']
            · rw [octDot_smul_right, octDot_comm]; dsimp only [v1]
              rw [octDot_sub_left, octDot_smul_left, octDot_self, he1_n, mul_one, sub_self, mul_zero]
            · change (1 / s) • (octI.2 - octDot octI e1 • e1.2) = 0
              rw [show octI.2 = 0 from rfl, he1_q, smul_zero, sub_zero, smul_zero]
          · have hnv2 : 0 < octNormSq v2 :=
              lt_of_le_of_ne (octNormSq_nonneg _) (Ne.symm fun h => hv2 ((octNormSq_eq_zero _).mp h))
            let s := Real.sqrt (octNormSq v2)
            refine ⟨(1 / s) • v2, ?_, ?_, ?_, ?_⟩
            · simp [v2, octonionReal_smul, octonionReal_sub, he1_im, show octonionReal octJ = 0 from rfl]
            · rw [octNormSq_smul, one_div, inv_pow, Real.sq_sqrt hnv2.le]; field_simp [hnv2.ne']
            · rw [octDot_smul_right, octDot_comm]; dsimp only [v2]
              rw [octDot_sub_left, octDot_smul_left, octDot_self, he1_n, mul_one, sub_self, mul_zero]
            · change (1 / s) • (octJ.2 - octDot octJ e1 • e1.2) = 0
              rw [show octJ.2 = 0 from rfl, he1_q, smul_zero, sub_zero, smul_zero]
        obtain ⟨e2, he2_im, he2_n, h12, he2_q⟩ := hex_e2
        let h13 : octDot e1 octL = 0 := by rw [octDot_eq_coords]; simp [octL, he1_q]
        let h23 : octDot e2 octL = 0 := by rw [octDot_eq_coords]; simp [octL, he2_q]
        let h3_12 : octDot octL (octonionMul e1 e2) = 0 := by
          rw [octDot_eq_coords]; simp [octL, octMul_quat_snd_zero he1_q he2_q]
        let α := octAutoOfBasicTriple e1 e2 octL he1_im he2_im rfl he1_n he2_n
          (by rw [octNormSq_eq_coords]; simp [octL]) h12 h13 h23 h3_12
        let g4 := octAutoToAlbertAuto α.symm
        have hαI : α.equiv octI = e1 :=
          octAutoOfBasicTriple_I e1 e2 octL he1_im he2_im rfl he1_n he2_n
            (by rw [octNormSq_eq_coords]; simp [octL]) h12 h13 h23 h3_12
        have hα_w : α.symm.equiv w = C₂ • octI := by
          apply α.equiv.injective
          change α.equiv (α.symm.equiv w) = α.equiv (C₂ • octI)
          rw [show α.equiv (α.symm.equiv w) = w from α.equiv.apply_symm_apply w, map_smul, hαI]
          dsimp only [e1]; rw [smul_smul, mul_one_div_cancel hC2_pos.ne', one_smul]
        have hg4_q : ∀ y, inStandardQuat y → inStandardQuat (g4.linearEquiv y) := fun y hy => by
          have hpres := octAuto_quat_preserves_snd_zero e1 e2 he1_im he2_im he1_n he2_n h12 he1_q he2_q
          exact ⟨hpres _ hy.1, hpres _ hy.2.1, hpres _ hy.2.2⟩
        refine ⟨g4.comp g3, fun i => by
          change g4.linearEquiv (g3.linearEquiv (diagAtom i)) = diagAtom i
          rw [hd i, octAutoToAlbertAuto_diagAtom], ?_, fun y hy => hg4_q _ (hq y hy), C₀, C₁, C₂, C₃, ?_⟩
        · change g4.linearEquiv (g3.linearEquiv (slotElem01 octOne)) = slotElem01 octOne
          rw [h01, octAutoToAlbertAuto_slotElem01, α.symm.map_one]
        · change g4.linearEquiv u2 = _
          rw [hu2_eq, octAuto_octDyad]
          refine congrArg octDyad (funext fun k => ?_)
          fin_cases k <;> dsimp
          · exact octAuto_map_scalar α.symm C₀
          · conv_lhs => rw [oct_eq_scalar_add_octIm z]
            change α.symm.equiv (octonionScalar C₁ + w) = _
            rw [map_add, octAuto_map_scalar, hα_w]
          · exact octAuto_map_scalar α.symm C₃
  obtain ⟨g3, hg3_diag, hg3_01, hg3_q, C₀, C₁, C₂, C₃, hg3_t2⟩ := ht2_step
  let u3 := g3.linearEquiv t3
  have hu3_atom : IsAtom u3 := g3.map_isAtom (g2.map_isAtom (g1.map_isAtom hq3_atom))
  have hu3_q : inStandardQuat u3 := hg3_q t3 ht3_q
  have hu3_dyad : ∃ (D₀ : ℝ) (X Y : Octonion),
      u3 = octDyad ![octonionScalar D₀, X, Y] ∧ X.2 = 0 ∧ Y.2 = 0 := by
    by_cases hu3d0 : 0 < u3.1 0
    · obtain ⟨hdy, _⟩ := isAtom_eq_octDyad hu3_atom hu3d0
      refine ⟨Real.sqrt (u3.1 0), (1 / Real.sqrt (u3.1 0)) • octonionConj (u3.2 0),
        (1 / Real.sqrt (u3.1 0)) • octonionConj (u3.2 1), hdy, ?_, ?_⟩
      · change (1 / Real.sqrt (u3.1 0)) • (octonionConj (u3.2 0)).2 = 0
        rw [octConj_quat_snd_zero hu3_q.1, smul_zero]
      · change (1 / Real.sqrt (u3.1 0)) • (octonionConj (u3.2 1)).2 = 0
        rw [octConj_quat_snd_zero hu3_q.2.1, smul_zero]
    · have hu3d0z : u3.1 0 = 0 := le_antisymm (not_lt.mp hu3d0) (isAtom_diag_nonneg hu3_atom 0)
      by_cases hu3d1 : 0 < u3.1 1
      · let x0 := Real.sqrt (u3.1 1)
        have hx0 : 0 < x0 := Real.sqrt_pos.mpr hu3d1
        let Y := (1 / x0) • octonionConj (u3.2 2)
        have hsharp := albertSharp_atom_eq_zero u3 hu3_atom
        have hf0 := congrArg (fun a : Albert => a.1 0) hsharp
        simp [albertSharp, albert_zero_fst] at hf0
        have hny : octNormSq Y = u3.1 2 := by
          dsimp only [Y, x0]
          rw [octNormSq_smul, octNormSq_conj, one_div, inv_pow, Real.sq_sqrt hu3d1.le]
          have hf0' : u3.1 1 * u3.1 2 = octNormSq (u3.2 2) := by linarith
          rw [← hf0']; field_simp [hu3d1.ne']
        obtain ⟨hz01, hz02⟩ := isAtom_zero_row0 hu3_atom hu3d0z
        refine ⟨0, octonionScalar x0, Y, ?_, rfl, ?_⟩
        · apply albert_ext
          · simp [octDyad_fst, hu3d0z, octNormSq_scalar]
          · dsimp only [x0]; simp [octDyad_fst, octNormSq_scalar, Real.sq_sqrt hu3d1.le]
          · simp [octDyad_fst, hny]
          · simp [octDyad_snd_0, hz01, octonionScalar_zero, octonionMul_zero_left]
          · simp [octDyad_snd_1, hz02, octonionScalar_zero, octonionMul_zero_left]
          · dsimp only [Y]
            rw [octDyad_snd_2,
              show (![octonionScalar 0, octonionScalar x0, (1 / x0) • octonionConj (u3.2 2)] : Fin 3 → Octonion) 1 =
                octonionScalar x0 from rfl,
              show (![octonionScalar 0, octonionScalar x0, (1 / x0) • octonionConj (u3.2 2)] : Fin 3 → Octonion) 2 =
                (1 / x0) • octonionConj (u3.2 2) from rfl,
              octonionConj_smul, octonionConj_conj, octonionMul_smul_right,
              octonionMul_scalar_left, smul_smul, one_div_mul_cancel hx0.ne', one_smul]
        · change (1 / x0) • (octonionConj (u3.2 2)).2 = 0
          rw [octConj_quat_snd_zero hu3_q.2.2, smul_zero]
      · have hu3d1z : u3.1 1 = 0 := le_antisymm (not_lt.mp hu3d1) (isAtom_diag_nonneg hu3_atom 1)
        have hdy := atom_diag2_eq_octDyad hu3_atom hu3d0z hu3d1z
        refine ⟨0, 0, octonionScalar 1, ?_, rfl, rfl⟩
        rw [hdy]
        exact congrArg octDyad (vec3_eq octonionScalar_zero.symm rfl rfl)
  obtain ⟨D₀, X, Y, hu3_eq, hXq, hYq⟩ := hu3_dyad
  let g := g3.comp (g2.comp (g1.comp g0))
  have hg_p0 : g.linearEquiv (p 0) = octDyad ![octonionScalar 1, 0, 0] := by
    change g3.linearEquiv (g2.linearEquiv (g1.linearEquiv (g0.linearEquiv (p 0)))) = _
    rw [hg0_p0, hg1_diag 0, hg2_d0, hg3_diag 0]
    apply albert_ext <;>
      simp [diagAtom_fst, diagAtom_snd, octDyad_fst, octDyad_snd_0, octDyad_snd_1, octDyad_snd_2,
        octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
  have hg_p1 : g.linearEquiv (p 1) = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] := by
    change g3.linearEquiv (g2.linearEquiv s1) = _
    rw [hg2_s1]
    have ht1_eq : octDyad ![octonionScalar B₀, octonionScalar B₁, 0] =
        B₀ ^ 2 • diagAtom 0 + B₁ ^ 2 • diagAtom 1 + (B₀ * B₁) • slotElem01 octOne := by
      apply albert_ext <;>
        simp [octDyad_fst, octDyad_snd_0, octDyad_snd_1, octDyad_snd_2,
          albert_add_fst, albert_add_snd, albert_smul_fst, albert_smul_snd,
          diagAtom_fst, diagAtom_snd, slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1,
          slotElem01_snd_2, octNormSq_scalar, octNormSq_zero, octonionConj_zero,
          octonionConj_scalar, octonionMul_zero_right, octonionMul_scalar_left]
      exact (octonionScalar_smul B₀ B₁).symm.trans
        (by rw [octonionScalar_eq_smul (B₀ * B₁), ← octOne_eq_scalar])
    rw [ht1_eq]
    simp only [map_add, map_smul, hg3_diag 0, hg3_diag 1, hg3_01]
  refine ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, fun i => ?_, ?_⟩
  · fin_cases i <;> dsimp
    · rw [hg_p0]
      exact ⟨octMul_quat_snd_zero rfl (octConj_quat_snd_zero rfl),
        octMul_quat_snd_zero rfl (octConj_quat_snd_zero rfl),
        octMul_quat_snd_zero rfl (octConj_quat_snd_zero rfl)⟩
    · rw [hg_p1]
      exact ⟨octMul_quat_snd_zero rfl (octConj_quat_snd_zero rfl),
        octMul_quat_snd_zero rfl (octConj_quat_snd_zero rfl),
        octMul_quat_snd_zero rfl (octConj_quat_snd_zero rfl)⟩
    · have hc12 : (octonionScalar C₁ + C₂ • octI).2 = 0 := by
        change (octonionScalar C₁).2 + C₂ • octI.2 = 0
        rw [show octI.2 = 0 from rfl, smul_zero, add_zero]; rfl
      change inStandardQuat (g3.linearEquiv t2)
      rw [hg3_t2]
      exact ⟨octMul_quat_snd_zero rfl (octConj_quat_snd_zero hc12),
        octMul_quat_snd_zero rfl (octConj_quat_snd_zero rfl),
        octMul_quat_snd_zero hc12 (octConj_quat_snd_zero rfl)⟩
    · change inStandardQuat u3
      rw [hu3_eq]
      exact ⟨octMul_quat_snd_zero rfl (octConj_quat_snd_zero hXq),
        octMul_quat_snd_zero rfl (octConj_quat_snd_zero hYq),
        octMul_quat_snd_zero hXq (octConj_quat_snd_zero hYq)⟩
  · funext i
    fin_cases i
    · exact hg_p0
    · exact hg_p1
    · exact hg3_t2
    · exact hu3_eq

theorem lemma_A_zero_of_quat (Q : QuaternionicWindow) (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, p i ∈ Q.subalgebra.carrier) :
    fourPointInvariant p = 0 := by
  obtain ⟨g0, hg0⟩ := native_quaternionicWindow_conjugate_standard Q
  let q := fun i => g0.linearEquiv (p i)
  have hq_atom : ∀ i, IsAtom (q i) := fun i => g0.map_isAtom (hp i)
  have hq_std : ∀ i, inStandardQuat (q i) := fun i =>
    (mem_standardQuat_iff _).mp ((hg0 (p i)).mp (hq i))
  obtain ⟨g1, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, hq_std1, hcfg⟩ :=
    exists_quatAuto_to_sparseFourConfigOct q hq_atom hq_std
  have hq3_in : inStandardQuat (g1.linearEquiv (q 3)) := hq_std1 3
  have hinv0 : fourPointInvariant p = fourPointInvariant q :=
    (fourPointInvariant_automorphism_invariant g0 p).symm
  have hinv1 : fourPointInvariant q = fourPointInvariant (fun i => g1.linearEquiv (q i)) :=
    (fourPointInvariant_automorphism_invariant g1 q).symm
  rw [hinv0, hinv1, hcfg, sparseFourConfigOct_fourPointInvariant]
  by_cases hD0 : D₀ = 0
  · simp [hD0]
  · have hI : octI ∈ Set.range quatEmbed1 := ⟨⟨0, 1, 0, 0⟩, by apply oct_ext <;> simp [quatEmbed1_apply, octI]⟩
    have hX : X ∈ Set.range quatEmbed1 := by
      have h01 : (g1.linearEquiv (q 3)).2 0 = D₀ • octonionConj X := by
        rw [congrFun hcfg 3]; simp [sparseFourConfigOct, octDyad, octonionMul_scalar_left]
      have hsm : D₀ • (octonionConj X).2 = 0 := by
        change (D₀ • octonionConj X).2 = 0
        rw [← h01]; exact hq3_in.1
      have hconj_snd : (octonionConj X).2 = 0 := (smul_eq_zero.mp hsm).resolve_left hD0
      have hX_snd : X.2 = 0 := by
        have h := octConj_quat_snd_zero hconj_snd
        rw [octonionConj_conj] at h
        exact h
      exact ⟨X.1, Prod.ext rfl hX_snd.symm⟩
    have hY : Y ∈ Set.range quatEmbed1 := by
      have h02 : (g1.linearEquiv (q 3)).2 1 = D₀ • octonionConj Y := by
        rw [congrFun hcfg 3]; simp [sparseFourConfigOct, octDyad, octonionMul_scalar_left]
      have hsm : D₀ • (octonionConj Y).2 = 0 := by
        change (D₀ • octonionConj Y).2 = 0
        rw [← h02]; exact hq3_in.2.1
      have hconj_snd : (octonionConj Y).2 = 0 := (smul_eq_zero.mp hsm).resolve_left hD0
      have hY_snd : Y.2 = 0 := by
        have h := octConj_quat_snd_zero hconj_snd
        rw [octonionConj_conj] at h
        exact h
      exact ⟨Y.1, Prod.ext rfl hY_snd.symm⟩
    rw [octAssociator_eq_zero_of_quatEmbedding quatEmbed1 quatEmbed1_isQuatEmbedding hI hX hY,
      octNormSq_zero, mul_zero]

private theorem mem_quatWindowOfEmbedding_of_slots {φ : Quaternion ℝ →ₗ[ℝ] Octonion}
    (hφ : IsQuatEmbedding φ) {x : Albert}
    (h0 : x.2 0 ∈ Set.range φ) (h1 : x.2 1 ∈ Set.range φ) (h2 : x.2 2 ∈ Set.range φ) :
    x ∈ (quaternionicWindowOfQuatEmbedding φ hφ).subalgebra.carrier := by
  rcases h0 with ⟨a0, ha0⟩
  rcases h1 with ⟨a1, ha1⟩
  rcases h2 with ⟨a2, ha2⟩
  rw [← (quaternionicWindowOfQuatEmbedding φ hφ).range_eq]
  refine ⟨quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]), ?_⟩
  change quatMatrixToAlbert φ ((quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]) : QuatHermitian3) : QuatMatrix3) = x
  have hp' := quatHermitian3Equiv.apply_symm_apply (x.1, ![a0, a1, a2])
  apply albert_ext
  · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 0) hp'
  · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 1) hp'
  · exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 2) hp'
  · change φ _ = x.2 0
    have h := congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 0) hp'
    change ((quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]) : QuatMatrix3) 0 1) = a0 at h
    rw [h, ha0]
  · change φ _ = x.2 1
    have h := congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 1) hp'
    change ((quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]) : QuatMatrix3) 0 2) = a1 at h
    rw [h, ha1]
  · change φ _ = x.2 2
    have h := congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.2 2) hp'
    change ((quatHermitian3Equiv.symm (x.1, ![a0, a1, a2]) : QuatMatrix3) 1 2) = a2 at h
    rw [h, ha2]

private theorem octDyad_mem_quatWindow {φ : Quaternion ℝ →ₗ[ℝ] Octonion}
    (hφ : IsQuatEmbedding φ) (v : Fin 3 → Octonion) (hv : ∀ i, v i ∈ Set.range φ) :
    octDyad v ∈ (quaternionicWindowOfQuatEmbedding φ hφ).subalgebra.carrier := by
  have hmul : ∀ a b : Octonion, a ∈ Set.range φ → b ∈ Set.range φ →
      octonionMul a (octonionConj b) ∈ Set.range φ := by
    rintro _ _ ⟨qa, rfl⟩ ⟨qb, rfl⟩
    exact ⟨qa * star qb, by rw [hφ.map_mul, hφ.map_star]⟩
  exact mem_quatWindowOfEmbedding_of_slots hφ
    (hmul _ _ (hv 0) (hv 1)) (hmul _ _ (hv 0) (hv 2)) (hmul _ _ (hv 1) (hv 2))

theorem lemma_A_zero_of_factor (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (g : NativeAlbertAutomorphism)
    (B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄ : ℝ)
    (hB0 : 0 < B₀) (hB1 : 0 < B₁) (hC0 : 0 < C₀) (hD0 : 0 < D₀)
    (hB_sum : B₀ ^ 2 + B₁ ^ 2 = 1)
    (hcfg : (fun i => g.linearEquiv (p i)) =
      sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂
        (y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL))
    (hvanish : C₂ * C₃ * x₂ * y₄ = 0) :
    ∃ Q : QuaternionicWindow, ∀ i, p i ∈ Q.subalgebra.carrier := by
  let X := octonionScalar x₀ + x₁ • octI + x₂ • octJ
  let Y := y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL
  have hscalar_mem : ∀ (φ : Quaternion ℝ →ₗ[ℝ] Octonion) (hφ : IsQuatEmbedding φ) (r : ℝ),
      octonionScalar r ∈ Set.range φ := fun φ hφ r =>
    ⟨r • 1, by rw [map_smul, hφ.map_one, ← octonionScalar_eq_smul]⟩
  have hC₂_or : C₂ = 0 ∨ C₃ = 0 ∨ x₂ = 0 ∨ y₄ = 0 := by
    rcases mul_eq_zero.mp hvanish with h1 | hy4
    · rcases mul_eq_zero.mp h1 with h2 | hx2
      · rcases mul_eq_zero.mp h2 with hc2 | hc3
        · exact Or.inl hc2
        · exact Or.inr (Or.inl hc3)
      · exact Or.inr (Or.inr (Or.inl hx2))
    · exact Or.inr (Or.inr (Or.inr hy4))
  rcases hC₂_or with hC2z | hC3z | hx2z | hy4z
  · obtain ⟨φ, hφ, hX, hY⟩ := exists_quatEmbedding_containing_pair X Y
    let Q0 := quaternionicWindowOfQuatEmbedding φ hφ
    refine ⟨Q0.transport g.symm, fun i => ?_⟩
    refine ⟨g.linearEquiv (p i), ?_, g.linearEquiv.symm_apply_apply _⟩
    rw [congrFun hcfg i]
    fin_cases i
    · exact octDyad_mem_quatWindow hφ _ (fun k => by
        fin_cases k <;> [exact hscalar_mem φ hφ 1; exact ⟨0, map_zero φ⟩; exact ⟨0, map_zero φ⟩])
    · exact octDyad_mem_quatWindow hφ _ (fun k => by
        fin_cases k <;> [exact hscalar_mem φ hφ B₀; exact hscalar_mem φ hφ B₁; exact ⟨0, map_zero φ⟩])
    · exact octDyad_mem_quatWindow hφ _ (fun k => by
        fin_cases k
        · exact hscalar_mem φ hφ C₀
        · rw [hC2z, zero_smul, add_zero]; exact hscalar_mem φ hφ C₁
        · exact hscalar_mem φ hφ C₃)
    · exact octDyad_mem_quatWindow hφ _ (fun k => by
        fin_cases k <;> [exact hscalar_mem φ hφ D₀; exact hX; exact hY])
  · let q := fun i => g.linearEquiv (p i)
    let c := diagAtom 0 + diagAtom 1
    have hq_atom : ∀ i, IsAtom (q i) := fun i => g.map_isAtom (hp i)
    have h01_zero : jordanMul (diagAtom 0) (diagAtom 1) = 0 := by
      rw [jordanMul_diagAtom0]
      apply albert_ext <;> simp [diagAtom, albert_zero_fst, albert_zero_snd]
    have hc_idem : jordanMul c c = c := by
      dsimp only [c]
      rw [jordanMul_add_left, jordanMul_add_right, jordanMul_add_right,
        (diagAtom_isAtom 0).1, (diagAtom_isAtom 1).1, h01_zero,
        jordanMul_comm (diagAtom 1), h01_zero, add_zero, zero_add]
    have h_d01_dyad : ∀ u v : Octonion, jordanMul c (octDyad ![u, v, 0]) = octDyad ![u, v, 0] := by
      intro u v
      dsimp only [c]
      rw [jordanMul_add_left]
      apply albert_ext
      · rw [albert_add_fst, jordanMul_diagAtom0, jordanMul_diagAtom1]
        change (octDyad ![u, v, 0]).1 0 + 0 = (octDyad ![u, v, 0]).1 0; ring
      · rw [albert_add_fst, jordanMul_diagAtom0, jordanMul_diagAtom1]
        change 0 + (octDyad ![u, v, 0]).1 1 = (octDyad ![u, v, 0]).1 1; ring
      · rw [albert_add_fst, jordanMul_diagAtom0, jordanMul_diagAtom1]
        change (0 : ℝ) + 0 = (octDyad ![u, v, 0]).1 2
        rw [octDyad_fst]; simp [octNormSq_zero]
      · rw [albert_add_snd, jordanMul_diagAtom0, jordanMul_diagAtom1]
        change (1 / 2 : ℝ) • (octDyad ![u, v, 0]).2 0 +
          (1 / 2 : ℝ) • (octDyad ![u, v, 0]).2 0 = (octDyad ![u, v, 0]).2 0; module
      · rw [albert_add_snd, jordanMul_diagAtom0, jordanMul_diagAtom1]
        change (1 / 2 : ℝ) • (octDyad ![u, v, 0]).2 1 + (0 : Octonion) =
          (octDyad ![u, v, 0]).2 1
        rw [octDyad_snd_1]; dsimp; simp [octonionConj_zero, octonionMul_zero_right]
      · rw [albert_add_snd, jordanMul_diagAtom0, jordanMul_diagAtom1]
        change (0 : Octonion) + (1 / 2 : ℝ) • (octDyad ![u, v, 0]).2 2 =
          (octDyad ![u, v, 0]).2 2
        rw [octDyad_snd_2]; dsimp; simp [octonionConj_zero, octonionMul_zero_right]
    have hq2_supp : jordanMul c (q 2) = q 2 := by
      have h02 : q 2 = octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, 0] := by
        dsimp only [q]
        rw [congrFun hcfg 2]
        simp [sparseFourConfig, sparseFourConfigOct, hC3z, octonionScalar_zero]
      rw [h02]
      exact h_d01_dyad _ _
    have hq0_supp : jordanMul c (q 0) = q 0 := by
      have h00 : q 0 = diagAtom 0 := by
        dsimp only [q]
        rw [congrFun hcfg 0]
        apply albert_ext <;> simp [sparseFourConfig, sparseFourConfigOct, octDyad, diagAtom,
          octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
      rw [h00]
      dsimp only [c]
      rw [jordanMul_add_left, (diagAtom_isAtom 0).1, jordanMul_comm (diagAtom 1), h01_zero, add_zero]
    have hq1_supp : jordanMul c (q 1) = q 1 := by
      have h01 : q 1 = octDyad ![octonionScalar B₀, octonionScalar B₁, 0] := by
        dsimp only [q]
        rw [congrFun hcfg 1]; rfl
      rw [h01]
      exact h_d01_dyad _ _
    let q' : Fin 4 → Albert := ![q 0, q 1, q 3, q 2]
    have hq'_atom : ∀ i, IsAtom (q' i) := fun i => by fin_cases i <;> exact hq_atom _
    have htr_all := sparseFourConfigOct_traces B₀ B₁ C₀ C₁ C₂ C₃ D₀
      (octonionScalar x₀ + x₁ • octI + x₂ • octJ) Y
    have htr_eq : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀
        (octonionScalar x₀ + x₁ • octI + x₂ • octJ) Y = q := by
      dsimp only [q]; rw [hcfg]; rfl
    rw [htr_eq] at htr_all
    have h01_pos : 0 < tracePairing (q' 0) (q' 1) := by
      have h01 : fpOverlap q 0 1 = B₀ ^ 2 := htr_all.1
      change 0 < tracePairing (q 0) (q 1)
      rw [show tracePairing (q 0) (q 1) = B₀ ^ 2 from h01]; positivity
    have h01_lt : tracePairing (q' 0) (q' 1) < 1 := by
      have h01 : fpOverlap q 0 1 = B₀ ^ 2 := htr_all.1
      change tracePairing (q 0) (q 1) < 1
      rw [show tracePairing (q 0) (q 1) = B₀ ^ 2 from h01]; nlinarith [sq_pos_iff.mpr hB1.ne']
    have h02_pos : 0 < tracePairing (q' 0) (q' 2) := by
      have h02 : fpOverlap q 0 3 = D₀ ^ 2 := htr_all.2.2.1
      change 0 < tracePairing (q 0) (q 3)
      rw [show tracePairing (q 0) (q 3) = D₀ ^ 2 from h02]; positivity
    have h03_pos : 0 < tracePairing (q' 0) (q' 3) := by
      have h03 : fpOverlap q 0 2 = C₀ ^ 2 := htr_all.2.1
      change 0 < tracePairing (q 0) (q 2)
      rw [show tracePairing (q 0) (q 2) = C₀ ^ 2 from h03]; positivity
    obtain ⟨g', B₀', B₁', C₀', C₁', C₂', C₃', D₀', x₀', x₁', x₂', y₀', y₁', y₂', y₃', y₄',
      _hB0', hB1', _hC0', _hC2', _hC3', _hD0', _hx2', _hy4', hB'_sum, _hC'_sum, _hD'_sum, hcfg'⟩ :=
      lemma_A_normal q' hq'_atom h01_pos h01_lt h02_pos h03_pos
    let c' := g'.linearEquiv c
    let r := c' - diagAtom 0
    have hc'_idem : jordanMul c' c' = c' := by
      rw [← g'.preserves_product, hc_idem]
    have hc'_tr : albertTrace c' = 2 := by
      rw [g'.preserves_trace, albertTrace_add, (diagAtom_isAtom 0).2, (diagAtom_isAtom 1).2]
      norm_num
    have hc'_d0 : jordanMul c' (diagAtom 0) = diagAtom 0 := by
      have h0 : g'.linearEquiv (q' 0) = diagAtom 0 := by
        rw [congrFun hcfg' 0]
        apply albert_ext <;> simp [sparseFourConfig, sparseFourConfigOct, octDyad, diagAtom,
          octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
      have h0' : q' 0 = q 0 := rfl
      rw [← h0, h0', ← g'.preserves_product]
      change g'.linearEquiv (jordanMul c (q 0)) = g'.linearEquiv (q 0)
      rw [hq0_supp]
    have hr_atom : IsAtom r := by
      refine ⟨?_, ?_⟩
      · dsimp only [r]
        rw [jordanMul_sub_left, jordanMul_sub_right, jordanMul_sub_right, hc'_idem, hc'_d0,
          jordanMul_comm (diagAtom 0) c', hc'_d0, (diagAtom_isAtom 0).1]
        abel
      · dsimp only [r]
        rw [albertTrace_sub, hc'_tr, (diagAtom_isAtom 0).2]
        norm_num
    have hr_d0 : r.1 0 = 0 := by
      have hjd : jordanMul (diagAtom 0) r = 0 := by
        dsimp only [r]
        rw [jordanMul_sub_right, jordanMul_comm (diagAtom 0) c', hc'_d0,
          (diagAtom_isAtom 0).1, sub_self]
      have htr : tracePairing (diagAtom 0) r = 0 := by
        unfold tracePairing; rw [hjd, albertTrace_zero]
      simpa [tracePairing_diagAtom] using htr
    obtain ⟨hr_01, hr_02⟩ := isAtom_zero_row0 hr_atom hr_d0
    have hr_d1 : r.1 1 = 1 := by
      have htr1 : tracePairing (g'.linearEquiv (q' 1)) c' = 1 := by
        rw [g'.map_tracePairing]
        change tracePairing (q 1) c = 1
        unfold tracePairing; rw [jordanMul_comm, hq1_supp, (hq_atom 1).2]
      have htr_d0 : tracePairing (g'.linearEquiv (q' 1)) (diagAtom 0) = B₀' ^ 2 := by
        rw [congrFun hcfg' 1, tracePairing_comm, tracePairing_diagAtom]
        simp [sparseFourConfig, sparseFourConfigOct, octDyad_fst, octNormSq_scalar]
      have htr_r1 : tracePairing (g'.linearEquiv (q' 1)) r = B₁' ^ 2 := by
        dsimp only [r]; rw [tracePairing_sub_right, htr1, htr_d0]; linarith [hB'_sum]
      have htr_r2 : tracePairing (g'.linearEquiv (q' 1)) r = B₁' ^ 2 * r.1 1 := by
        rw [congrFun hcfg' 1, tracePairing_eq_coords]
        simp [sparseFourConfig, sparseFourConfigOct, octDyad, octNormSq_scalar, octNormSq_zero,
          octonionConj_zero, octonionMul_zero_right, hr_d0, hr_01, hr_02,
          octDot_zero_left, octDot_zero_right]
      have hB1_sq_ne : B₁' ^ 2 ≠ 0 := pow_ne_zero 2 hB1'.ne'
      exact mul_left_cancel₀ hB1_sq_ne ((htr_r2.symm.trans htr_r1).trans (mul_one _).symm)
    have hr_eq : r = diagAtom 1 := by
      have hr_d2 : r.1 2 = 0 := by
        have htr := hr_atom.2; rw [albertTrace_eq_sum, hr_d0, hr_d1] at htr; linarith
      obtain ⟨_, hr_12⟩ := isAtom_zero_row2 hr_atom hr_d2
      apply albert_ext <;> simp [diagAtom, hr_d0, hr_d1, hr_d2, hr_01, hr_02, hr_12]
    have hc'_eq : c' = diagAtom 0 + diagAtom 1 := by
      have h : c' = diagAtom 0 + r := by dsimp only [r]; abel
      rw [h, hr_eq]
    have hq2_supp' : tracePairing (diagAtom 2) (g'.linearEquiv (q' 3)) = 0 := by
      have htr_c : tracePairing c' (g'.linearEquiv (q' 3)) = 1 := by
        rw [g'.map_tracePairing]
        change tracePairing c (q 2) = 1
        unfold tracePairing; rw [hq2_supp, (hq_atom 2).2]
      have hdiag2 : diagAtom 2 = albertUnit - c' := by
        rw [hc'_eq]
        have hds := diagAtom_sum_eq_unit; rw [Fin.sum_univ_three] at hds; rw [← hds]; abel
      rw [hdiag2, tracePairing_sub_left, tracePairing_comm, tracePairing_unit_right,
        (g'.map_isAtom (hq'_atom 3)).2, htr_c, sub_self]
    have hgq3_d2 : (g'.linearEquiv (q' 3)).1 2 = 0 := by
      simpa [tracePairing_diagAtom] using hq2_supp'
    obtain ⟨hgq3_02, hgq3_12⟩ := isAtom_zero_row2 (g'.map_isAtom (hq'_atom 3)) hgq3_d2
    obtain ⟨φ, hφ, hI_mem, hslot_mem⟩ :=
      exists_quatEmbedding_containing_pair octI ((g'.linearEquiv (q' 3)).2 0)
    let Q0 := quaternionicWindowOfQuatEmbedding φ hφ
    have hmem_c : ∀ i : Fin 3, (g'.linearEquiv (q' i.castSucc)) ∈ Q0.subalgebra.carrier := by
      intro i
      rw [congrFun hcfg' i.castSucc]
      fin_cases i
      · exact octDyad_mem_quatWindow hφ _ (fun k => by
          fin_cases k <;> [exact hscalar_mem φ hφ 1; exact ⟨0, map_zero φ⟩; exact ⟨0, map_zero φ⟩])
      · exact octDyad_mem_quatWindow hφ _ (fun k => by
          fin_cases k <;> [exact hscalar_mem φ hφ B₀'; exact hscalar_mem φ hφ B₁'; exact ⟨0, map_zero φ⟩])
      · refine octDyad_mem_quatWindow hφ _ (fun k => ?_)
        fin_cases k <;> dsimp
        · exact hscalar_mem φ hφ C₀'
        · have h1 := hscalar_mem φ hφ C₁'
          have h2 : C₂' • octI ∈ Set.range φ := by
            rcases hI_mem with ⟨qi, hqi⟩
            exact ⟨C₂' • qi, by rw [map_smul, hqi]⟩
          rcases h1 with ⟨a1, ha1⟩; rcases h2 with ⟨a2, ha2⟩
          exact ⟨a1 + a2, by rw [map_add, ha1, ha2]⟩
        · exact hscalar_mem φ hφ C₃'
    have hmem_3 : g'.linearEquiv (q' 3) ∈ Q0.subalgebra.carrier :=
      mem_quatWindowOfEmbedding_of_slots hφ hslot_mem
        (by rw [hgq3_02]; exact ⟨0, map_zero φ⟩) (by rw [hgq3_12]; exact ⟨0, map_zero φ⟩)
    refine ⟨Q0.transport (g'.comp g).symm, fun i => ?_⟩
    refine ⟨(g'.comp g).linearEquiv (p i), ?_, (g'.comp g).linearEquiv.symm_apply_apply _⟩
    change g'.linearEquiv (q i) ∈ Q0.subalgebra.carrier
    fin_cases i
    · exact hmem_c 0
    · exact hmem_c 1
    · exact hmem_3
    · exact hmem_c 2
  · obtain ⟨φ, hφ, hI_mem, hY_mem⟩ := exists_quatEmbedding_containing_pair octI Y
    let Q0 := quaternionicWindowOfQuatEmbedding φ hφ
    have hI_sc : ∀ a b : ℝ, octonionScalar a + b • octI ∈ Set.range φ := fun a b => by
      rcases hscalar_mem φ hφ a with ⟨qa, hqa⟩
      rcases hI_mem with ⟨qi, hqi⟩
      exact ⟨qa + b • qi, by rw [map_add, map_smul, hqa, hqi]⟩
    refine ⟨Q0.transport g.symm, fun i => ?_⟩
    refine ⟨g.linearEquiv (p i), ?_, g.linearEquiv.symm_apply_apply _⟩
    rw [congrFun hcfg i]
    fin_cases i
    · exact octDyad_mem_quatWindow hφ _ (fun k => by
        fin_cases k <;> [exact hscalar_mem φ hφ 1; exact ⟨0, map_zero φ⟩; exact ⟨0, map_zero φ⟩])
    · exact octDyad_mem_quatWindow hφ _ (fun k => by
        fin_cases k <;> [exact hscalar_mem φ hφ B₀; exact hscalar_mem φ hφ B₁; exact ⟨0, map_zero φ⟩])
    · exact octDyad_mem_quatWindow hφ _ (fun k => by
        fin_cases k <;> [exact hscalar_mem φ hφ C₀; exact hI_sc C₁ C₂; exact hscalar_mem φ hφ C₃])
    · exact octDyad_mem_quatWindow hφ _ (fun k => by
        fin_cases k
        · exact hscalar_mem φ hφ D₀
        · dsimp only [sparseFourConfig, sparseFourConfigOct]
          rw [hx2z, zero_smul, add_zero]
          exact hI_sc x₀ x₁
        · exact hY_mem)
  · refine ⟨standardQuaternionicWindow.transport g.symm, fun i => ?_⟩
    refine ⟨g.linearEquiv (p i), ?_, g.linearEquiv.symm_apply_apply _⟩
    rw [congrFun hcfg i]
    have hmem1 : ∀ x : Octonion, x.2 = 0 → x ∈ Set.range quatEmbed1 := fun x hx =>
      ⟨x.1, Prod.ext rfl hx.symm⟩
    fin_cases i
    · exact octDyad_mem_quatWindow quatEmbed1_isQuatEmbedding _ (fun k => by
        fin_cases k <;> exact hmem1 _ rfl)
    · exact octDyad_mem_quatWindow quatEmbed1_isQuatEmbedding _ (fun k => by
        fin_cases k <;> exact hmem1 _ rfl)
    · exact octDyad_mem_quatWindow quatEmbed1_isQuatEmbedding _ (fun k => by
        fin_cases k
        · exact hmem1 _ rfl
        · exact hmem1 _ (by
            dsimp
            rw [oct_snd_add, oct_snd_smul, show (octonionScalar C₁).2 = 0 from rfl,
              show octI.2 = 0 from rfl, smul_zero, add_zero])
        · exact hmem1 _ rfl)
    · exact octDyad_mem_quatWindow quatEmbed1_isQuatEmbedding _ (fun k => by
        fin_cases k <;> dsimp
        · exact hmem1 _ rfl
        · exact hmem1 _ (by
            rw [oct_snd_add, oct_snd_add, oct_snd_smul, oct_snd_smul,
              show (octonionScalar x₀).2 = 0 from rfl, show octI.2 = 0 from rfl,
              show octJ.2 = 0 from rfl, smul_zero, smul_zero, add_zero, add_zero])
        · exact hmem1 _ (by
            rw [hy4z, zero_smul, add_zero, oct_snd_add, oct_snd_add, oct_snd_add,
              oct_snd_smul, oct_snd_smul, oct_snd_smul, oct_snd_smul,
              show octOne.2 = 0 from rfl, show octI.2 = 0 from rfl,
              show octJ.2 = 0 from rfl, show octK.2 = 0 from rfl,
              smul_zero, smul_zero, smul_zero, smul_zero, add_zero, add_zero, add_zero]))

/-! ## Section 6: Subalgebra Generation (`lem:A:generate`) & Full `thm:fourpoint` -/

private theorem quadraticMap_compl_diag0 (x : Albert) :
    quadraticMap (albertUnit - diagAtom 0) x =
      ((fun k : Fin 3 => if k = 0 then 0 else x.1 k, ![0, 0, x.2 2]) : Albert) := by
  have hsub_idem : jordanMul (albertUnit - diagAtom 0) (albertUnit - diagAtom 0) =
      albertUnit - diagAtom 0 := by
    simp only [jordanMul_sub_left, jordanMul_sub_right,
      jordanMul_albertUnit_left, jordanMul_albertUnit_right, (diagAtom_isAtom 0).1]
    abel
  have hL : ∀ y : Albert, jordanMul (albertUnit - diagAtom 0) y =
      ((fun k : Fin 3 => if k = 0 then 0 else y.1 k,
        ![(1 / 2 : ℝ) • y.2 0, (1 / 2 : ℝ) • y.2 1, y.2 2]) : Albert) := by
    intro y
    rw [jordanMul_sub_left, jordanMul_albertUnit_left]
    apply albert_ext
    · rw [albert_sub_fst, jordanMul_diagAtom0]; change y.1 0 - y.1 0 = 0; ring
    · rw [albert_sub_fst, jordanMul_diagAtom0]; change y.1 1 - 0 = y.1 1; ring
    · rw [albert_sub_fst, jordanMul_diagAtom0]; change y.1 2 - 0 = y.1 2; ring
    · rw [albert_sub_snd, jordanMul_diagAtom0]
      change y.2 0 - (1 / 2 : ℝ) • y.2 0 = (1 / 2 : ℝ) • y.2 0; module
    · rw [albert_sub_snd, jordanMul_diagAtom0]
      change y.2 1 - (1 / 2 : ℝ) • y.2 1 = (1 / 2 : ℝ) • y.2 1; module
    · rw [albert_sub_snd, jordanMul_diagAtom0]; change y.2 2 - 0 = y.2 2; module
  unfold quadraticMap
  rw [hsub_idem, two_nsmul]
  apply albert_ext
  · rw [albert_sub_fst, albert_add_fst, hL, hL]; change (0 : ℝ) + 0 - 0 = 0; ring
  · rw [albert_sub_fst, albert_add_fst, hL, hL]; change x.1 1 + x.1 1 - x.1 1 = x.1 1; ring
  · rw [albert_sub_fst, albert_add_fst, hL, hL]; change x.1 2 + x.1 2 - x.1 2 = x.1 2; ring
  · rw [albert_sub_snd, albert_add_snd, hL, hL]
    change (1 / 2 : ℝ) • ((1 / 2 : ℝ) • x.2 0) + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • x.2 0) -
      (1 / 2 : ℝ) • x.2 0 = 0; module
  · rw [albert_sub_snd, albert_add_snd, hL, hL]
    change (1 / 2 : ℝ) • ((1 / 2 : ℝ) • x.2 1) + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • x.2 1) -
      (1 / 2 : ℝ) • x.2 1 = 0; module
  · rw [albert_sub_snd, albert_add_snd, hL, hL]; change x.2 2 + x.2 2 - x.2 2 = x.2 2; module

private theorem slot_decomposition (x : Albert) :
    x = x.1 0 • diagAtom 0 + x.1 1 • diagAtom 1 + x.1 2 • diagAtom 2 +
      slotElem01 (x.2 0) + slotElem02 (x.2 1) + slotElem12 (x.2 2) := by
  apply albert_ext <;>
    simp [albert_add_fst, albert_add_snd, albert_smul_fst, albert_smul_snd,
      diagAtom_fst, diagAtom_snd,
      slotElem01_fst, slotElem01_snd_0, slotElem01_snd_1, slotElem01_snd_2,
      slotElem02_fst, slotElem02_snd_0, slotElem02_snd_1, slotElem02_snd_2,
      slotElem12_fst, slotElem12_snd_0, slotElem12_snd_1, slotElem12_snd_2]

private theorem octConj_I_eq : octonionConj octI = -octI := by
  apply oct_ext <;>
    (simp only [octConj_re, octConj_imI, octConj_imJ, octConj_imK,
      octConj_s_re, octConj_s_imI, octConj_s_imJ, octConj_s_imK,
      oct_neg_re, oct_neg_imI, oct_neg_imJ, oct_neg_imK,
      oct_neg_s_re, oct_neg_s_imI, oct_neg_s_imJ, oct_neg_s_imK];
     try simp [octI])

private theorem octConj_J_eq : octonionConj octJ = -octJ := by
  apply oct_ext <;>
    (simp only [octConj_re, octConj_imI, octConj_imJ, octConj_imK,
      octConj_s_re, octConj_s_imI, octConj_s_imJ, octConj_s_imK,
      oct_neg_re, oct_neg_imI, oct_neg_imJ, oct_neg_imK,
      oct_neg_s_re, oct_neg_s_imI, oct_neg_s_imJ, oct_neg_s_imK];
     try simp [octJ])

private theorem octConj_K_eq : octonionConj octK = -octK := by
  apply oct_ext <;>
    (simp only [octConj_re, octConj_imI, octConj_imJ, octConj_imK,
      octConj_s_re, octConj_s_imI, octConj_s_imJ, octConj_s_imK,
      oct_neg_re, oct_neg_imI, oct_neg_imJ, oct_neg_imK,
      oct_neg_s_re, oct_neg_s_imI, oct_neg_s_imJ, oct_neg_s_imK];
     try simp [octK])

private theorem octConj_L_eq : octonionConj octL = -octL := by
  apply oct_ext <;>
    (simp only [octConj_re, octConj_imI, octConj_imJ, octConj_imK,
      octConj_s_re, octConj_s_imI, octConj_s_imJ, octConj_s_imK,
      oct_neg_re, oct_neg_imI, oct_neg_imJ, oct_neg_imK,
      oct_neg_s_re, oct_neg_s_imI, oct_neg_s_imJ, oct_neg_s_imK];
     try simp [octL])

private theorem subalgebra_triple_core (B : NativeJordanSubalgebra)
    (q0 q1 q2 : Albert) (hq0B : q0 ∈ B.carrier) (hq1B : q1 ∈ B.carrier) (hq2B : q2 ∈ B.carrier)
    (B₀ B₁ C₀ C₁ C₂ C₃ : ℝ)
    (hB0 : B₀ ≠ 0) (hB1 : B₁ ≠ 0) (hC0 : C₀ ≠ 0) (hC2 : C₂ ≠ 0) (hC3 : C₃ ≠ 0)
    (hq0 : q0 = diagAtom 0)
    (hq1 : q1 = octDyad ![octonionScalar B₀, octonionScalar B₁, 0])
    (hq2 : q2 = octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃]) :
    diagAtom 0 ∈ B.carrier ∧ diagAtom 1 ∈ B.carrier ∧ diagAtom 2 ∈ B.carrier ∧
    slotElem01 octOne ∈ B.carrier ∧ slotElem02 octOne ∈ B.carrier ∧
    slotElem12 octOne ∈ B.carrier ∧ slotElem01 octI ∈ B.carrier := by
  have hd0 : diagAtom 0 ∈ B.carrier := hq0 ▸ hq0B
  have hcomp := (peirce_components_mem_subalgebra B hd0 hq1B).2.2
  have hq1_e1 : quadraticMap (albertUnit - diagAtom 0) q1 = B₁ ^ 2 • diagAtom 1 := by
    rw [hq1, quadraticMap_compl_diag0]
    apply albert_ext <;>
      simp [octDyad, diagAtom_fst, diagAtom_snd, albert_smul_fst, albert_smul_snd,
        octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
  rw [hq1_e1] at hcomp
  have hd1 : diagAtom 1 ∈ B.carrier := by
    have hsm := B.carrier.smul_mem ((B₁ ^ 2)⁻¹) hcomp
    rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hB1), one_smul] at hsm
    exact hsm
  have hd2 : diagAtom 2 ∈ B.carrier := by
    have hds := diagAtom_sum_eq_unit; rw [Fin.sum_univ_three] at hds
    have heq : diagAtom 2 = albertUnit - diagAtom 0 - diagAtom 1 := by rw [← hds]; abel
    rw [heq]
    exact B.carrier.sub_mem (B.carrier.sub_mem B.unit_mem hd0) hd1
  have h01_B1 : slotElem01 (q1.2 0) ∈ B.carrier := by
    rw [← peirce01_extract q1]
    exact B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ hq1B))
  have hs01 : slotElem01 octOne ∈ B.carrier := by
    have hq10 : q1.2 0 = (B₀ * B₁) • octOne := by
      rw [hq1, octDyad_snd_0]; dsimp
      rw [octonionConj_scalar, octonionMul_scalar_left, ← octonionScalar_smul,
        octonionScalar_eq_smul, ← octOne_eq_scalar]
    rw [hq10, map_smul] at h01_B1
    have hsm := B.carrier.smul_mem ((B₀ * B₁)⁻¹) h01_B1
    rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hB0 hB1), one_smul] at hsm
    exact hsm
  have h02_C : slotElem02 (q2.2 1) ∈ B.carrier := by
    rw [← peirce02_extract q2]
    exact B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd2 _ hq2B))
  have hs02 : slotElem02 octOne ∈ B.carrier := by
    have hq21 : q2.2 1 = (C₀ * C₃) • octOne := by
      rw [hq2, octDyad_snd_1]; dsimp
      rw [octonionConj_scalar, octonionMul_scalar_left, ← octonionScalar_smul,
        octonionScalar_eq_smul, ← octOne_eq_scalar]
    rw [hq21, map_smul] at h02_C
    have hsm := B.carrier.smul_mem ((C₀ * C₃)⁻¹) h02_C
    rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hC0 hC3), one_smul] at hsm
    exact hsm
  have hs12 : slotElem12 octOne ∈ B.carrier := slotElem02_mem_12_of_mem hs01 hs02
  have h01_C : slotElem01 (q2.2 0) ∈ B.carrier := by
    rw [← peirce01_extract q2]
    exact B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ hq2B))
  have hq20 : q2.2 0 = (C₀ * C₁) • octOne - (C₀ * C₂) • octI := by
    rw [hq2, octDyad_snd_0]; dsimp
    rw [octonionConj_add, octonionConj_scalar, octonionConj_smul, octConj_I_eq,
      octonionMul_add_right, octonionMul_scalar_left, octonionMul_smul_right,
      octonionMul_neg_right, octonionMul_scalar_left, ← octonionScalar_smul,
      octonionScalar_eq_smul (C₀ * C₁), ← octOne_eq_scalar, smul_neg, smul_smul, mul_comm C₂ C₀]
    abel
  have hs01_I : slotElem01 octI ∈ B.carrier := by
    rw [hq20, map_sub, map_smul, map_smul] at h01_C
    have hdiff := B.carrier.sub_mem (B.carrier.smul_mem (C₀ * C₁) hs01) h01_C
    have hsub : (C₀ * C₁) • slotElem01 octOne - ((C₀ * C₁) • slotElem01 octOne -
        (C₀ * C₂) • slotElem01 octI) = (C₀ * C₂) • slotElem01 octI := by abel
    rw [hsub] at hdiff
    have hsm := B.carrier.smul_mem ((C₀ * C₂)⁻¹) hdiff
    rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hC0 hC2), one_smul] at hsm
    exact hsm
  exact ⟨hd0, hd1, hd2, hs01, hs02, hs12, hs01_I⟩

theorem lemma_A_generate_three
    (B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ : ℝ) (Y : Octonion)
    (hB0 : 0 < B₀) (hB1 : 0 < B₁) (hC0 : 0 < C₀) (hC2 : C₂ ≠ 0) (hC3 : C₃ ≠ 0) :
    let q := sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ Y
    ∀ x, InGeneratedAlgebra ![q 0, q 1, q 2] x ↔ standardComplexWindow.Contains x := by
  intro q x
  have hq0_in : standardComplexWindow.Contains (q 0) := by
    have h0 : q 0 = diagAtom 0 := by
      apply albert_ext <;> simp [q, sparseFourConfig, sparseFourConfigOct, octDyad, diagAtom,
        octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
    rw [h0]
    exact standardComplexWindow_contains_diag0
  have hq1_in : standardComplexWindow.Contains (q 1) := by
    have h10 : (q 1).2 0 = octonionScalar (B₀ * B₁) := by
      dsimp [q, sparseFourConfig, sparseFourConfigOct]
      rw [octDyad_snd_0]; dsimp; rw [octonionConj_scalar, octonionMul_scalar_left, ← octonionScalar_smul]
    have h11 : (q 1).2 1 = 0 := by
      dsimp [q, sparseFourConfig, sparseFourConfigOct]
      rw [octDyad_snd_1]; dsimp; rw [octonionConj_zero, octonionMul_zero_right]
    have h12 : (q 1).2 2 = 0 := by
      dsimp [q, sparseFourConfig, sparseFourConfigOct]
      rw [octDyad_snd_2]; dsimp; rw [octonionConj_zero, octonionMul_zero_right]
    rw [standardComplexWindow_contains_iff, h10, h11, h12]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  have hq2_in : standardComplexWindow.Contains (q 2) := by
    have h20 : (q 2).2 0 = (C₀ * C₁) • octOne + (-(C₀ * C₂)) • octI := by
      dsimp [q, sparseFourConfig, sparseFourConfigOct]
      rw [octDyad_snd_0]; dsimp
      rw [octonionConj_add, octonionConj_scalar, octonionConj_smul, octConj_I_eq,
        octonionMul_add_right, octonionMul_scalar_left, octonionMul_smul_right,
        octonionMul_neg_right, octonionMul_scalar_left, ← octonionScalar_smul,
        octonionScalar_eq_smul (C₀ * C₁), ← octOne_eq_scalar, smul_neg, neg_smul, smul_smul,
        mul_comm C₂ C₀]
    have h21 : (q 2).2 1 = octonionScalar (C₀ * C₃) := by
      dsimp [q, sparseFourConfig, sparseFourConfigOct]
      rw [octDyad_snd_1]; dsimp; rw [octonionConj_scalar, octonionMul_scalar_left, ← octonionScalar_smul]
    have h22 : (q 2).2 2 = C₃ • (octonionScalar C₁ + C₂ • octI) := by
      dsimp [q, sparseFourConfig, sparseFourConfigOct]
      rw [octDyad_snd_2]; dsimp; rw [octonionConj_scalar, octonionMul_scalar_right]
    rw [standardComplexWindow_contains_iff, h20, h21, h22]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [oct_fst_add, oct_snd_add, oct_fst_smul, oct_snd_smul,
        quat_add_imJ, quat_add_imK, quat_smul_imJ, quat_smul_imK]) <;>
      simp [octOne, octonionScalar_coord, octI]
  constructor
  · intro hx
    obtain ⟨M, hM⟩ := hx standardComplexWindow.toSubalgebra (fun i => by
      fin_cases i
      · exact hq0_in
      · exact hq1_in
      · exact hq2_in)
    exact ⟨M, hM⟩
  · intro hx B hB
    have h0 : q 0 = diagAtom 0 := by
      apply albert_ext <;> simp [q, sparseFourConfig, sparseFourConfigOct, octDyad, diagAtom,
        octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
    obtain ⟨hd0, hd1, hd2, hs01, hs02, hs12, hs01_I⟩ :=
      subalgebra_triple_core B (q 0) (q 1) (q 2) (hB 0) (hB 1) (hB 2) B₀ B₁ C₀ C₁ C₂ C₃
        hB0.ne' hB1.ne' hC0.ne' hC2 hC3 h0 rfl rfl
    have hs02_I : slotElem02 octI ∈ B.carrier := slotElem01_mem_02_of_mem hs12 hs01_I
    have hs12_I : slotElem12 octI ∈ B.carrier := slotElem02_mem_12_of_mem hs01 hs02_I
    have hxc := (standardComplexWindow_contains_iff x).mp hx
    have hslot : ∀ (a : Octonion), a.1.imJ = 0 → a.1.imK = 0 → a.2 = 0 →
        ∀ (S : Octonion →ₗ[ℝ] Albert), S octOne ∈ B.carrier → S octI ∈ B.carrier →
          S a ∈ B.carrier := fun a hj hk hs S hS1 hSI => by
      have ha := oct_eq_complex hj hk hs
      rw [ha, map_add, map_smul, map_smul]
      exact B.carrier.add_mem (B.carrier.smul_mem _ hS1) (B.carrier.smul_mem _ hSI)
    rw [slot_decomposition x]
    exact B.carrier.add_mem (B.carrier.add_mem (B.carrier.add_mem (B.carrier.add_mem
      (B.carrier.add_mem (B.carrier.smul_mem _ hd0) (B.carrier.smul_mem _ hd1))
      (B.carrier.smul_mem _ hd2))
      (hslot _ hxc.1 hxc.2.1 hxc.2.2.1 slotElem01 hs01 hs01_I))
      (hslot _ hxc.2.2.2.1 hxc.2.2.2.2.1 hxc.2.2.2.2.2.1 slotElem02 hs02 hs02_I))
      (hslot _ hxc.2.2.2.2.2.2.1 hxc.2.2.2.2.2.2.2.1 hxc.2.2.2.2.2.2.2.2 slotElem12 hs12 hs12_I)

theorem lemma_A_generate_four
    (B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄ : ℝ)
    (hB0 : 0 < B₀) (hB1 : 0 < B₁) (hC0 : 0 < C₀) (hD0 : 0 < D₀)
    (hC2 : C₂ ≠ 0) (hC3 : C₃ ≠ 0) (hx2 : x₂ ≠ 0) (hy4 : y₄ ≠ 0) :
    GeneratesAlbert (sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂
      (y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL)) := by
  let Y := y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL
  let q := sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ Y
  intro x B hB
  have h0 : q 0 = diagAtom 0 := by
    apply albert_ext <;> simp [q, sparseFourConfig, sparseFourConfigOct, octDyad, diagAtom,
      octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
  obtain ⟨hd0, hd1, hd2, hs01, hs02, hs12, hs01_I⟩ :=
    subalgebra_triple_core B (q 0) (q 1) (q 2) (hB 0) (hB 1) (hB 2) B₀ B₁ C₀ C₁ C₂ C₃
      hB0.ne' hB1.ne' hC0.ne' hC2 hC3 h0 rfl rfl
  let S := slotSubalgebraOfJordanSubalgebra B hd0 hd1 hd2 hs01 hs02 hs12
  have hS1 : octOne ∈ S.carrier := hs01
  have hSI : octI ∈ S.carrier := (mem_slotSubalgebra_iff_slotElem01 B hd0 hd1 hd2 hs01 hs02 hs12 _).mpr hs01_I
  have h01_q3 : (q 3).2 0 ∈ S.carrier := by
    rw [mem_slotSubalgebra_iff_slotElem01, ← peirce01_extract (q 3)]
    exact B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd1 _ (hB 3)))
  have hq3_0 : (q 3).2 0 = (D₀ * x₀) • octOne - (D₀ * x₁) • octI - (D₀ * x₂) • octJ := by
    change (octDyad ![octonionScalar D₀, octonionScalar x₀ + x₁ • octI + x₂ • octJ, Y]).2 0 = _
    rw [octDyad_snd_0]
    dsimp
    rw [octonionConj_add, octonionConj_add, octonionConj_scalar, octonionConj_smul,
      octonionConj_smul, octConj_I_eq, octConj_J_eq,
      octonionMul_add_right, octonionMul_add_right, octonionMul_scalar_left,
      octonionMul_smul_right, octonionMul_neg_right, octonionMul_scalar_left,
      octonionMul_smul_right, octonionMul_neg_right, octonionMul_scalar_left,
      ← octonionScalar_smul, octonionScalar_eq_smul (D₀ * x₀), ← octOne_eq_scalar,
      smul_neg, smul_neg, smul_smul, smul_smul, mul_comm x₁ D₀, mul_comm x₂ D₀]
    abel
  have hSJ : octJ ∈ S.carrier := by
    rw [hq3_0] at h01_q3
    have h1 := S.carrier.sub_mem (S.carrier.smul_mem (D₀ * x₀) hS1)
      (S.carrier.sub_mem h01_q3 (S.carrier.smul_mem (-D₀ * x₁) hSI))
    have hsub : (D₀ * x₀) • octOne - ((D₀ * x₀) • octOne - (D₀ * x₁) • octI -
        (D₀ * x₂) • octJ - (-D₀ * x₁) • octI) = (D₀ * x₂) • octJ := by module
    rw [hsub] at h1
    have hsm := S.carrier.smul_mem ((D₀ * x₂)⁻¹) h1
    rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hD0.ne' hx2), one_smul] at hsm
    exact hsm
  have hSK : octK ∈ S.carrier := by
    rw [← octK_eq_mul]
    exact S.mul_mem _ hSI _ hSJ
  have h02_q3 : (q 3).2 1 ∈ S.carrier := by
    rw [mem_slotSubalgebra_iff_slotElem02, ← peirce02_extract (q 3)]
    exact B.carrier.smul_mem (4 : ℝ) (B.product_mem _ hd0 _ (B.product_mem _ hd2 _ (hB 3)))
  have hq3_1 : (q 3).2 1 =
      (D₀ * y₀) • octOne - (D₀ * y₁) • octI - (D₀ * y₂) • octJ -
      (D₀ * y₃) • octK - (D₀ * y₄) • octL := by
    change (octDyad ![octonionScalar D₀, octonionScalar x₀ + x₁ • octI + x₂ • octJ, Y]).2 1 = _
    rw [octDyad_snd_1]
    dsimp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Y]
    dsimp
    rw [octonionConj_add, octonionConj_add, octonionConj_add, octonionConj_add,
      octonionConj_smul, octonionConj_smul, octonionConj_smul, octonionConj_smul,
      octonionConj_smul, octonionConj_one, octConj_I_eq, octConj_J_eq, octConj_K_eq, octConj_L_eq,
      octonionMul_add_right, octonionMul_add_right, octonionMul_add_right, octonionMul_add_right,
      octonionMul_smul_right, octonionMul_one_right,
      octonionMul_smul_right, octonionMul_neg_right, octonionMul_scalar_left,
      octonionMul_smul_right, octonionMul_neg_right, octonionMul_scalar_left,
      octonionMul_smul_right, octonionMul_neg_right, octonionMul_scalar_left,
      octonionMul_smul_right, octonionMul_neg_right, octonionMul_scalar_left,
      octonionScalar_eq_smul D₀, ← octOne_eq_scalar]
    module
  have hSL : octL ∈ S.carrier := by
    rw [hq3_1] at h02_q3
    let lin := (D₀ * y₀) • octOne - (D₀ * y₁) • octI - (D₀ * y₂) • octJ - (D₀ * y₃) • octK
    have hlin : lin ∈ S.carrier :=
      S.carrier.sub_mem (S.carrier.sub_mem (S.carrier.sub_mem
        (S.carrier.smul_mem _ hS1) (S.carrier.smul_mem _ hSI))
        (S.carrier.smul_mem _ hSJ)) (S.carrier.smul_mem _ hSK)
    have h1 := S.carrier.sub_mem hlin h02_q3
    have hsub : lin - (lin - (D₀ * y₄) • octL) = (D₀ * y₄) • octL := by abel
    rw [hsub] at h1
    have hsm := S.carrier.smul_mem ((D₀ * y₄)⁻¹) h1
    rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hD0.ne' hy4), one_smul] at hsm
    exact hsm
  have hS_top : ∀ a : Octonion, a ∈ S.carrier := fun a =>
    (OctSubalgebra.generated_le {octOne, octI, octJ, octL} S fun z hz => by
      rcases hz with rfl | rfl | rfl | rfl
      · exact hS1
      · exact hSI
      · exact hSJ
      · exact hSL) (by rw [octSubalgebra_generated_IJL_eq_top]; trivial)
  rw [slot_decomposition x]
  exact B.carrier.add_mem (B.carrier.add_mem (B.carrier.add_mem (B.carrier.add_mem
    (B.carrier.add_mem (B.carrier.smul_mem _ hd0) (B.carrier.smul_mem _ hd1))
    (B.carrier.smul_mem _ hd2))
    ((mem_slotSubalgebra_iff_slotElem01 B hd0 hd1 hd2 hs01 hs02 hs12 _).mp (hS_top _)))
    ((mem_slotSubalgebra_iff_slotElem02 B hd0 hd1 hd2 hs01 hs02 hs12 _).mp (hS_top _)))
    ((mem_slotSubalgebra_iff_slotElem12 B hd0 hd1 hd2 hs01 hs02 hs12 _).mp (hS_top _))

theorem fourPointInvariant_nonneg (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    0 ≤ fourPointInvariant p := by
  obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
    _, _, _, _, _, _, _, _, _, _, _, hX, hY, hcfg, _⟩ := lemma_A_normal_general p hp
  rw [← fourPointInvariant_automorphism_invariant g p, hcfg,
    show sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y =
      sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂
        (octonionScalar y₀ + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL) from by
      rw [hX, hY, octOne_eq_scalar, ← octonionScalar_eq_smul x₀, ← octonionScalar_eq_smul y₀]; rfl,
    sparseFourConfig_fourPointInvariant]
  positivity

theorem fourPointInvariant_eq_zero_iff (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    fourPointInvariant p = 0 ↔ ∃ Q : QuaternionicWindow, ∀ i, p i ∈ Q.subalgebra.carrier := by
  constructor
  · intro hz
    by_cases hdeg : ∃ i j, i ≠ j ∧ (p i = p j ∨ jordanMul (p i) (p j) = 0)
    · exact lemma_A_degenerate p hp hdeg
    · have hnd : ∀ i j, i ≠ j → p i ≠ p j ∧ jordanMul (p i) (p j) ≠ 0 := by
        intro i j hij; by_contra h
        exact hdeg ⟨i, j, hij, Or.imp not_not.mp not_not.mp (not_and_or.mp h)⟩
      obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
        hB0, hB1, hC0, _hC2, _hC3, hD0, _hx2, _hy4, hBs, _hCs, _hDs, hcfg⟩ :=
        lemma_A_normal_nondegenerate p hp hnd
      have hfp := fourPointInvariant_automorphism_invariant g p
      have hcfg' := hcfg
      rw [octOne_eq_scalar, ← octonionScalar_eq_smul y₀] at hcfg'
      rw [hcfg', sparseFourConfig_fourPointInvariant] at hfp
      rw [← hfp] at hz
      have hvan : C₂ * C₃ * x₂ * y₄ = 0 := by
        have hsq_van : (B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * D₀ ^ 2) * (C₂ * C₃ * x₂ * y₄) ^ 2 = 0 := by
          nlinarith [hz]
        have hpre : B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * D₀ ^ 2 ≠ 0 := by positivity
        exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hsq_van).resolve_left hpre)
      exact lemma_A_zero_of_factor p hp g B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄
        hB0 hB1 hC0 hD0 hBs hcfg hvan
  · rintro ⟨Q, hQ⟩
    exact lemma_A_zero_of_quat Q p hp hQ

private theorem albert_finrank : Module.finrank ℝ Albert = 27 := by
  have heq : Albert ≃ₗ[ℝ] ((Fin 3 → ℝ) × (Fin 3 → (Quaternion ℝ × Quaternion ℝ))) :=
    LinearEquiv.refl ℝ Albert
  have hquat : Module.finrank ℝ (Quaternion ℝ) = 4 := by
    let e : Quaternion ℝ ≃ₗ[ℝ] (Fin 4 → ℝ) :=
      { toFun := fun q => ![q.re, q.imI, q.imJ, q.imK]
        invFun := fun v => ⟨v 0, v 1, v 2, v 3⟩
        left_inv := fun q => by apply Quaternion.ext <;> rfl
        right_inv := fun v => by funext i; fin_cases i <;> rfl
        map_add' := fun a b => by funext i; fin_cases i <;> rfl
        map_smul' := fun r a => by funext i; fin_cases i <;> rfl }
    rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype]
    simp
  rw [LinearEquiv.finrank_eq heq, Module.finrank_prod, Module.finrank_pi_fintype,
    Module.finrank_pi_fintype, Module.finrank_self, Module.finrank_prod, hquat]
  norm_num

theorem fourPointInvariant_pos_iff (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    0 < fourPointInvariant p ↔ GeneratesAlbert p := by
  constructor
  · intro hpos
    have hnd : ∀ i j, i ≠ j → p i ≠ p j ∧ jordanMul (p i) (p j) ≠ 0 := by
      intro i j hij
      by_contra h
      obtain ⟨Q, hQ⟩ :=
        lemma_A_degenerate p hp ⟨i, j, hij, Or.imp not_not.mp not_not.mp (not_and_or.mp h)⟩
      have hz := lemma_A_zero_of_quat Q p hp hQ
      linarith
    obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
      hB0, hB1, hC0, _hC2, _hC3, hD0, _hx2, _hy4, _hBs, _hCs, _hDs, hcfg⟩ :=
      lemma_A_normal_nondegenerate p hp hnd
    have hfp : fourPointInvariant p =
        B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 := by
      have hcfg' := hcfg
      rw [octOne_eq_scalar, ← octonionScalar_eq_smul y₀] at hcfg'
      rw [← fourPointInvariant_automorphism_invariant g p, hcfg', sparseFourConfig_fourPointInvariant]
    rw [hfp] at hpos
    have hC2 : C₂ ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hC3 : C₃ ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hx2 : x₂ ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hy4 : y₄ ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hgen := lemma_A_generate_four B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄
      hB0 hB1 hC0 hD0 hC2 hC3 hx2 hy4
    rw [← hcfg] at hgen
    have hgen' := g.symm.map_generatesAlbert (fun i => g.linearEquiv (p i)) hgen
    have hp_eq : (fun i => g.symm.linearEquiv (g.linearEquiv (p i))) = p := funext fun i =>
      g.linearEquiv.symm_apply_apply (p i)
    rwa [hp_eq] at hgen'
  · intro hgen
    have hnn := fourPointInvariant_nonneg p hp
    refine lt_of_le_of_ne hnn (Ne.symm fun hz => ?_)
    obtain ⟨Q, hQ⟩ := (fourPointInvariant_eq_zero_iff p hp).mp hz
    have htop : Q.subalgebra.carrier = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hgen x Q.subalgebra hQ
    have hfr : Module.finrank ℝ Q.subalgebra.carrier = 27 := by
      rw [htop, finrank_top, albert_finrank]
    have h15 := Q.finrank_eq
    omega

theorem thm_fourpoint (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    (0 ≤ fourPointInvariant p) ∧
    (fourPointInvariant p = 0 ↔ ∃ Q : QuaternionicWindow, ∀ i, p i ∈ Q.subalgebra.carrier) ∧
    (0 < fourPointInvariant p ↔ GeneratesAlbert p) ∧
    (∃ (g : NativeAlbertAutomorphism)
        (B₀ B₁ C₀ C₁ C₂ C₃ D₀ : ℝ) (X Y : Octonion)
        (x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄ : ℝ),
      0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ C₀ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 ≤ D₀ ∧ 0 ≤ x₂ ∧ 0 ≤ y₄ ∧
      B₀ ^ 2 + B₁ ^ 2 = 1 ∧ C₀ ^ 2 + C₁ ^ 2 + C₂ ^ 2 + C₃ ^ 2 = 1 ∧
      D₀ ^ 2 + x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 = 1 ∧
      X = x₀ • octOne + x₁ • octI + x₂ • octJ ∧
      Y = y₀ • octOne + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL ∧
      (fun i => g.linearEquiv (p i)) =
        sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y ∧
      fourPointInvariant p =
        (1 / 4 : ℝ) * B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 *
          octNormSq (octAssociator octI X Y) ∧
      (1 / 4 : ℝ) * B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 *
          octNormSq (octAssociator octI X Y) =
        B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2) := by
  refine ⟨fourPointInvariant_nonneg p hp, fourPointInvariant_eq_zero_iff p hp,
    fourPointInvariant_pos_iff p hp, ?_⟩
  obtain ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
    hB0, hB1, hC0, hC2, hC3, hD0, hx2, hy4, hBs, hCs, hDs, hX, hY, hcfg, _⟩ :=
    lemma_A_normal_general p hp
  have h1 : fourPointInvariant p =
      (1 / 4 : ℝ) * B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 *
        octNormSq (octAssociator octI X Y) := by
    rw [← fourPointInvariant_automorphism_invariant g p, hcfg, sparseFourConfigOct_fourPointInvariant]
  have h2 : (1 / 4 : ℝ) * B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 *
      octNormSq (octAssociator octI X Y) =
      B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 := by
    have hX2 : X = octonionScalar x₀ + x₁ • octI + x₂ • octJ := by
      rw [hX, octOne_eq_scalar, ← octonionScalar_eq_smul x₀]
    have hY2 : Y = octonionScalar y₀ + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL := by
      rw [hY, octOne_eq_scalar, ← octonionScalar_eq_smul y₀]
    have h_eq : sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y =
        sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂
          (octonionScalar y₀ + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL) := by
      rw [hX2, hY2]; rfl
    calc
      (1 / 4 : ℝ) * B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 *
          octNormSq (octAssociator octI X Y)
        = fourPointInvariant (sparseFourConfigOct B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y) :=
            (sparseFourConfigOct_fourPointInvariant B₀ B₁ C₀ C₁ C₂ C₃ D₀ X Y).symm
      _ = fourPointInvariant (sparseFourConfig B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂
            (octonionScalar y₀ + y₁ • octI + y₂ • octJ + y₃ • octK + y₄ • octL)) := by
            rw [h_eq]
      _ = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 * D₀ ^ 2 * x₂ ^ 2 * y₄ ^ 2 :=
            sparseFourConfig_fourPointInvariant B₀ B₁ C₀ C₁ C₂ C₃ D₀ x₀ x₁ x₂ y₀ y₁ y₂ y₃ y₄
  exact ⟨g, B₀, B₁, C₀, C₁, C₂, C₃, D₀, X, Y, x₀, x₁, x₂, y₀, y₁, y₂, y₃, y₄,
    hB0, hB1, hC0, hC2, hC3, hD0, hx2, hy4, hBs, hCs, hDs, hX, hY, hcfg, h1, h2⟩

/-! ## Section 7: Conditional No-Go (`cor:fp:noideal`) and `ℂ^6` Symplectic Model -/

theorem maximallyMixed_isDensity : IsDensity ((1 / 3 : ℝ) • albertUnit) := by
  refine ⟨⟨((1 / Real.sqrt 3 : ℝ) • albertUnit), ?_⟩, ?_⟩
  · rw [jordanMul_smul_left, jordanMul_smul_right, jordanMul_albertUnit_left, smul_smul,
      div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  · rw [albertTrace_smul, show albertTrace albertUnit = 3 from by simp [albertTrace, albertUnit]]
    norm_num

theorem fourPoint_no_ideal_separator (hsep : AlbertUniformSeparationContract 4)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hpos : 0 < fourPointInvariant p) :
    UniformMomentSeparator p nativeDensitySet :=
  hsep.all_states p hp ((fourPointInvariant_pos_iff p hp).mp hpos)

theorem fourPoint_no_moment_match (hsep : AlbertUniformSeparationContract 4)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hpos : 0 < fourPointInvariant p) :
    NoMomentMatch p nativeDensitySet := by
  obtain ⟨L, c, γ, hγ, _hL, hm_nn, hρ_neg⟩ := fourPoint_no_ideal_separator hsep p hp hpos
  intro m hm ρ hρ
  by_contra hall
  push Not at hall
  have hev : c.evaluate (momentWordProbability m) = c.evaluate (nativeWordProbability p ρ) := by
    unfold FiniteRealWordFunctional.evaluate
    congr 1
    refine List.map_congr_left fun t _ => ?_
    rw [hall t.2]
  have h0 := hm_nn m hm
  have h1 := hρ_neg ρ hρ
  linarith

theorem fourPoint_no_ideal_maximally_mixed (hsep : AlbertUniformSeparationContract 4)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hpos : 0 < fourPointInvariant p) :
    ∀ m : ProjectionMoments 4, AdmissibleProjectionMoments 4 m →
      ∃ w : Word (Fin 4), momentWordProbability m w ≠
        nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := fun m hm =>
  fourPoint_no_moment_match hsep p hp hpos m hm _ maximallyMixed_isDensity

theorem fourPoint_no_ideal_algebraic_binding (hsep : AlbertUniformSeparationContract 4)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hpos : 0 < fourPointInvariant p)
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin 4) A) (hM : AlgebraicMomentBinding M) :
    ∀ ρ ∈ nativeDensitySet, ¬ M.Matches p ρ := by
  intro ρ hρ hmatch
  obtain ⟨w, hw⟩ :=
    fourPoint_no_moment_match hsep p hp hpos (momentsOfProjectiveData M) hM.admissible ρ hρ
  exact hw ((hM.probabilities w).trans (hmatch w))

private def quatToMat2 (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩], ![-⟨q.imJ, -q.imK⟩, ⟨q.re, -q.imI⟩]]

private theorem quatToMat2_one : quatToMat2 (1 : Quaternion ℝ) = 1 := by
  funext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatToMat2]

private theorem quatToMat2_add (a b : Quaternion ℝ) :
    quatToMat2 (a + b) = quatToMat2 a + quatToMat2 b := by
  funext i j
  rw [Matrix.add_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatToMat2] <;> ring

private theorem quatToMat2_smul (r : ℝ) (a : Quaternion ℝ) :
    quatToMat2 (r • a) = r • quatToMat2 a := by
  funext i j
  rw [Matrix.smul_apply, Complex.real_smul]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatToMat2]

private theorem quatToMat2_mul (a b : Quaternion ℝ) :
    quatToMat2 (a * b) = quatToMat2 a * quatToMat2 b := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.mul_apply, Fin.sum_univ_two]; apply Complex.ext <;> simp [quatToMat2] <;> ring)

private theorem quatToMat2_star (a : Quaternion ℝ) :
    quatToMat2 (star a) = (quatToMat2 a).conjTranspose := by
  funext i j
  rw [Matrix.conjTranspose_apply, RCLike.star_def]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quatToMat2]

private def fin3ProdFin2Equiv : Fin 3 × Fin 2 ≃ Fin 6 where
  toFun p := ⟨2 * p.1.1 + p.2.1, by omega⟩
  invFun k := (⟨k.1 / 2, by omega⟩, ⟨k.1 % 2, by omega⟩)
  left_inv p := by
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> decide
  right_inv k := by
    fin_cases k <;> decide

private def symplecticQuatMat (M : QuatMatrix3) : HermitianEmbeddingMatrix 6 :=
  Matrix.of fun r c =>
    let rp := fin3ProdFin2Equiv.symm r
    let cp := fin3ProdFin2Equiv.symm c
    quatToMat2 (M rp.1 cp.1) rp.2 cp.2

private theorem symplecticQuatMat_one : symplecticQuatMat 1 = 1 := by
  funext r c
  simp only [symplecticQuatMat, Matrix.of_apply, Matrix.one_apply]
  by_cases hrc : r = c
  · subst c
    simp [quatToMat2_one]
  · have hpair : fin3ProdFin2Equiv.symm r ≠ fin3ProdFin2Equiv.symm c := fun h =>
      hrc (fin3ProdFin2Equiv.symm.injective h)
    by_cases h1 : (fin3ProdFin2Equiv.symm r).1 = (fin3ProdFin2Equiv.symm c).1
    · have h2 : (fin3ProdFin2Equiv.symm r).2 ≠ (fin3ProdFin2Equiv.symm c).2 := fun h =>
        hpair (Prod.ext h1 h)
      simp [h1, hrc, quatToMat2_one, h2]
    · simp only [h1, ite_false, hrc]
      rcases (fin3ProdFin2Equiv.symm r).2 with ⟨_ | _, _⟩ <;>
        rcases (fin3ProdFin2Equiv.symm c).2 with ⟨_ | _, _⟩ <;> simp [quatToMat2] <;> rfl

private theorem symplecticQuatMat_add (M N : QuatMatrix3) :
    symplecticQuatMat (M + N) = symplecticQuatMat M + symplecticQuatMat N := by
  funext r c
  simp [symplecticQuatMat, quatToMat2_add]

private theorem symplecticQuatMat_smul (r : ℝ) (M : QuatMatrix3) :
    symplecticQuatMat (r • M) = r • symplecticQuatMat M := by
  funext a b
  simp [symplecticQuatMat, quatToMat2_smul, Complex.real_smul]

private theorem symplecticQuatMat_mul (M N : QuatMatrix3) :
    symplecticQuatMat (M * N) = symplecticQuatMat M * symplecticQuatMat N := by
  funext r c
  let rp := fin3ProdFin2Equiv.symm r
  let cp := fin3ProdFin2Equiv.symm c
  change quatToMat2 ((M * N) rp.1 cp.1) rp.2 cp.2 =
    ∑ k : Fin 6, quatToMat2 (M rp.1 (fin3ProdFin2Equiv.symm k).1) rp.2 (fin3ProdFin2Equiv.symm k).2 *
      quatToMat2 (N (fin3ProdFin2Equiv.symm k).1 cp.1) (fin3ProdFin2Equiv.symm k).2 cp.2
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp only [quatToMat2_add, Matrix.add_apply, quatToMat2_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hsum := Fintype.sum_equiv fin3ProdFin2Equiv.symm
    (fun k : Fin 6 =>
      quatToMat2 (M rp.1 (fin3ProdFin2Equiv.symm k).1) rp.2 (fin3ProdFin2Equiv.symm k).2 *
        quatToMat2 (N (fin3ProdFin2Equiv.symm k).1 cp.1) (fin3ProdFin2Equiv.symm k).2 cp.2)
    (fun p : Fin 3 × Fin 2 =>
      quatToMat2 (M rp.1 p.1) rp.2 p.2 * quatToMat2 (N p.1 cp.1) p.2 cp.2)
    (fun _ => rfl)
  rw [hsum, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp_rw [Fin.sum_univ_two]

private theorem symplecticQuatMat_star (M : QuatMatrix3) :
    symplecticQuatMat (star M) = (symplecticQuatMat M).conjTranspose := by
  funext r c
  simp only [symplecticQuatMat, Matrix.of_apply, Matrix.star_apply, Matrix.conjTranspose_apply,
    quatToMat2_star]

private theorem symplecticQuatMat_trace (M : QuatMatrix3) :
    Matrix.trace (symplecticQuatMat M) =
      2 * ((M 0 0).re + (M 1 1).re + (M 2 2).re : ℂ) := by
  unfold Matrix.trace Matrix.diag
  have hsum := Fintype.sum_equiv fin3ProdFin2Equiv.symm
    (fun k : Fin 6 => symplecticQuatMat M k k)
    (fun p : Fin 3 × Fin 2 => quatToMat2 (M p.1 p.1) p.2 p.2)
    (fun _ => rfl)
  rw [hsum, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp_rw [Fin.sum_univ_two]
  simp [quatToMat2]
  apply Complex.ext
  · simp; ring
  · simp

private def evalQuatFactors : List ℝ → QuatHermitian3 → QuatHermitian3
  | [], _ => 1
  | r :: rs, Z =>
    let P := evalQuatFactors rs Z
    let A : QuatMatrix3 := (Z : QuatMatrix3) - r • 1
    ⟨(1 / 2 : ℝ) • (A * (P : QuatMatrix3) + (P : QuatMatrix3) * A), by
      rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_sub, star_smul,
        star_one, Z.prop, P.prop, star_trivial, star_trivial, add_comm]⟩

private theorem evalQuatFactors_comm (L : List ℝ) (Z : QuatHermitian3) :
    (Z : QuatMatrix3) * (evalQuatFactors L Z : QuatMatrix3) =
      (evalQuatFactors L Z : QuatMatrix3) * (Z : QuatMatrix3) ∧
    ∀ r : ℝ, ((Z : QuatMatrix3) - r • 1) * (evalQuatFactors L Z : QuatMatrix3) =
      (evalQuatFactors L Z : QuatMatrix3) * ((Z : QuatMatrix3) - r • 1) := by
  induction L with
  | nil =>
    refine ⟨by simp [evalQuatFactors], fun r => by simp [evalQuatFactors]⟩
  | cons a rs ih =>
    have hcomm := ih.2 a
    have hval : (evalQuatFactors (a :: rs) Z : QuatMatrix3) =
        ((Z : QuatMatrix3) - a • 1) * (evalQuatFactors rs Z : QuatMatrix3) := by
      change (1 / 2 : ℝ) • (((Z : QuatMatrix3) - a • 1) * (evalQuatFactors rs Z : QuatMatrix3) +
        (evalQuatFactors rs Z : QuatMatrix3) * ((Z : QuatMatrix3) - a • 1)) = _
      rw [← hcomm, ← two_smul ℝ, smul_smul]
      norm_num
    have hZ : (Z : QuatMatrix3) * (evalQuatFactors (a :: rs) Z : QuatMatrix3) =
        (evalQuatFactors (a :: rs) Z : QuatMatrix3) * (Z : QuatMatrix3) := by
      rw [hval]
      calc
        (Z : QuatMatrix3) * (((Z : QuatMatrix3) - a • 1) * (evalQuatFactors rs Z : QuatMatrix3))
          = (Z : QuatMatrix3) * ((Z : QuatMatrix3) * (evalQuatFactors rs Z : QuatMatrix3) -
              a • (evalQuatFactors rs Z : QuatMatrix3)) := by
              rw [sub_mul, smul_mul_assoc, Matrix.one_mul]
        _ = (Z : QuatMatrix3) * ((Z : QuatMatrix3) * (evalQuatFactors rs Z : QuatMatrix3)) -
              a • ((Z : QuatMatrix3) * (evalQuatFactors rs Z : QuatMatrix3)) := by
              rw [mul_sub, mul_smul_comm]
        _ = ((Z : QuatMatrix3) * (evalQuatFactors rs Z : QuatMatrix3)) * (Z : QuatMatrix3) -
              a • ((evalQuatFactors rs Z : QuatMatrix3) * (Z : QuatMatrix3)) := by
              conv_lhs => rw [ih.1, ← Matrix.mul_assoc (Z : QuatMatrix3)]
        _ = ((Z : QuatMatrix3) * (evalQuatFactors rs Z : QuatMatrix3) -
              a • (evalQuatFactors rs Z : QuatMatrix3)) * (Z : QuatMatrix3) := by
              rw [sub_mul, smul_mul_assoc]
        _ = (((Z : QuatMatrix3) - a • 1) * (evalQuatFactors rs Z : QuatMatrix3)) * (Z : QuatMatrix3) := by
              conv_rhs => rw [sub_mul, smul_mul_assoc, Matrix.one_mul]
    refine ⟨hZ, fun r => ?_⟩
    rw [sub_mul, smul_mul_assoc, Matrix.one_mul, mul_sub, mul_smul_comm, Matrix.mul_one, hZ]

private theorem evalQuatFactors_mat_spec (L : List ℝ) (Z : QuatHermitian3)
    (U : HermitianEmbeddingMatrix 6) (μ : Fin 6 → ℝ)
    (hspec : symplecticQuatMat (Z : QuatMatrix3) =
      U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose)
    (hUU : U.conjTranspose * U = 1) (hUUt : U * U.conjTranspose = 1) :
    symplecticQuatMat (evalQuatFactors L Z : QuatMatrix3) =
      U * Matrix.diagonal (fun i => ((L.map (fun r => μ i - r)).prod : ℂ)) * U.conjTranspose := by
  induction L with
  | nil =>
    simp [evalQuatFactors, symplecticQuatMat_one, Matrix.diagonal_one, hUUt]
  | cons a rs ih =>
    have hcomm := (evalQuatFactors_comm rs Z).2 a
    have hval : (evalQuatFactors (a :: rs) Z : QuatMatrix3) =
        ((Z : QuatMatrix3) - a • 1) * (evalQuatFactors rs Z : QuatMatrix3) := by
      change (1 / 2 : ℝ) • (((Z : QuatMatrix3) - a • 1) * (evalQuatFactors rs Z : QuatMatrix3) +
        (evalQuatFactors rs Z : QuatMatrix3) * ((Z : QuatMatrix3) - a • 1)) = _
      rw [← hcomm, ← two_smul ℝ, smul_smul]
      norm_num
    rw [hval, symplecticQuatMat_mul]
    have hsub : symplecticQuatMat ((Z : QuatMatrix3) - a • 1) =
        U * Matrix.diagonal (fun i => ((μ i - a : ℝ) : ℂ)) * U.conjTranspose := by
      rw [sub_eq_add_neg, ← neg_one_smul ℝ (a • (1 : QuatMatrix3)), smul_smul,
        symplecticQuatMat_add, symplecticQuatMat_smul, symplecticQuatMat_one, hspec]
      have hdiag : U * Matrix.diagonal (fun i => ((μ i - a : ℝ) : ℂ)) * U.conjTranspose =
          U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose +
          ((-1 * a) • (1 : HermitianEmbeddingMatrix 6)) := by
        have h1 : Matrix.diagonal (fun i => ((μ i - a : ℝ) : ℂ)) =
            Matrix.diagonal (fun i => (μ i : ℂ)) + (-1 * a) • (1 : HermitianEmbeddingMatrix 6) := by
          ext i j
          by_cases hij : i = j
          · subst j; simp [Complex.real_smul]; ring
          · simp [hij]
        rw [h1, Matrix.mul_add, Matrix.add_mul, mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hUUt]
      exact hdiag.symm
    rw [hsub, ih]
    calc
      (U * Matrix.diagonal (fun i => ((μ i - a : ℝ) : ℂ)) * U.conjTranspose) *
          (U * Matrix.diagonal (fun i => ((rs.map (fun r => μ i - r)).prod : ℂ)) * U.conjTranspose)
        = U * Matrix.diagonal (fun i => ((μ i - a : ℝ) : ℂ)) * (U.conjTranspose * U) *
            Matrix.diagonal (fun i => ((rs.map (fun r => μ i - r)).prod : ℂ)) * U.conjTranspose := by
              simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal (fun i => ((μ i - a : ℝ) : ℂ)) *
            Matrix.diagonal (fun i => ((rs.map (fun r => μ i - r)).prod : ℂ))) * U.conjTranspose := by
              rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun i => (((a :: rs).map (fun r => μ i - r)).prod : ℂ)) *
            U.conjTranspose := by
              rw [Matrix.diagonal_mul_diagonal]
              congr 1; congr 1; ext i; simp [List.prod_cons, Complex.ofReal_mul]

private theorem nativeWordProbability_automorphism {ι : Type*} (g : NativeAlbertAutomorphism)
    (p : ι → Albert) (ρ : Albert) (w : Word ι) :
    nativeWordProbability (fun i => g.linearEquiv (p i)) (g.linearEquiv ρ) w =
      nativeWordProbability p ρ w := by
  have heff : nativeWordEffect (fun i => g.linearEquiv (p i)) w =
      g.linearEquiv (nativeWordEffect p w) := by
    induction w with
    | nil => exact g.preserves_unit.symm
    | cons a ws ih =>
      have hout : nativeOutcome (fun i => g.linearEquiv (p i)) a =
          g.linearEquiv (nativeOutcome p a) := by
        cases a with
        | mk i b =>
          cases b
          · change albertUnit - g.linearEquiv (p i) = g.linearEquiv (albertUnit - p i)
            rw [map_sub, g.preserves_unit]
          · rfl
      change quadraticMap (nativeOutcome (fun i => g.linearEquiv (p i)) a)
        (nativeWordEffect (fun i => g.linearEquiv (p i)) ws) =
        g.linearEquiv (quadraticMap (nativeOutcome p a) (nativeWordEffect p ws))
      rw [hout, ih, g.map_quadraticMap]
  rw [nativeWordProbability_eq_pairing, nativeWordProbability_eq_pairing, heff, g.map_tracePairing]

private theorem stdQuat_wordEffect_eq {ι : Type*} (q : ι → QuatHermitian3) (w : Word ι) :
    ∃ R : QuatHermitian3,
      (R : QuatMatrix3) = wordOperator (fun i => (q i : QuatMatrix3)) w ∧
      standardQuaternionicWindow.embedding R =
        nativeWordEffect (fun i => standardQuaternionicWindow.embedding (q i)) w := by
  have hquad : ∀ A B : QuatHermitian3, ∃ R : QuatHermitian3,
      (R : QuatMatrix3) = (A : QuatMatrix3) * (B : QuatMatrix3) * (A : QuatMatrix3) ∧
      standardQuaternionicWindow.embedding R =
        quadraticMap (standardQuaternionicWindow.embedding A)
          (standardQuaternionicWindow.embedding B) := by
    intro A B
    let prod : QuatHermitian3 → QuatHermitian3 → QuatHermitian3 := fun X Y =>
      ⟨(1 / 2 : ℝ) • ((X : QuatMatrix3) * (Y : QuatMatrix3) + (Y : QuatMatrix3) * (X : QuatMatrix3)), by
        rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial,
          X.prop, Y.prop, add_comm]⟩
    have hprod : ∀ X Y : QuatHermitian3,
        standardQuaternionicWindow.embedding (prod X Y) =
          jordanMul (standardQuaternionicWindow.embedding X)
            (standardQuaternionicWindow.embedding Y) := fun X Y =>
      standardQuaternionicWindow.preserves_product X Y (prod X Y) rfl
    refine ⟨(2 : ℝ) • prod A (prod A B) - prod (prod A A) B, ?_, ?_⟩
    · change (2 : ℝ) • (prod A (prod A B) : QuatMatrix3) - (prod (prod A A) B : QuatMatrix3) = _
      dsimp only [prod]
      simp only [smul_add, Matrix.mul_add, Matrix.add_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
        Matrix.mul_assoc]
      module
    · rw [map_sub, map_smul, hprod, hprod, hprod, hprod]
      unfold quadraticMap
      rw [two_smul ℝ, two_smul ℕ]
  let qOut : Outcome ι → QuatHermitian3 := fun a => if a.2 then q a.1 else 1 - q a.1
  have hOut_val : ∀ a, (qOut a : QuatMatrix3) = algebraicOutcome (fun i => (q i : QuatMatrix3)) a :=
    fun a => by cases a with | mk i b => cases b <;> rfl
  have hOut_emb : ∀ a, standardQuaternionicWindow.embedding (qOut a) =
      nativeOutcome (fun i => standardQuaternionicWindow.embedding (q i)) a := fun a => by
    cases a with
    | mk i b =>
      cases b
      · change standardQuaternionicWindow.embedding (1 - q i) =
          albertUnit - standardQuaternionicWindow.embedding (q i)
        rw [map_sub, standardQuaternionicWindow.unit]
      · rfl
  induction w with
  | nil => exact ⟨1, by simp [wordOperator, wordAmplitude], standardQuaternionicWindow.unit⟩
  | cons a ws ih =>
    obtain ⟨Rw, hRw_val, hRw_emb⟩ := ih
    obtain ⟨R', hR'_val, hR'_emb⟩ := hquad (qOut a) Rw
    refine ⟨R', ?_, ?_⟩
    · rw [hR'_val, hRw_val, hOut_val]
      unfold wordOperator
      rw [wordAmplitude_cons, star_mul]
      have hst : star (algebraicOutcome (fun i => (q i : QuatMatrix3)) a) =
          algebraicOutcome (fun i => (q i : QuatMatrix3)) a := by
        rw [← hOut_val a]; exact (qOut a).prop
      rw [hst]
      simp only [Matrix.mul_assoc]
    · rw [hR'_emb, hOut_emb, hRw_emb]; rfl

private theorem symplectic_trace_mul_eq_pairing (A B : QuatHermitian3) :
    (Matrix.trace (symplecticQuatMat (A : QuatMatrix3) *
      symplecticQuatMat (B : QuatMatrix3))).re =
      2 * tracePairing (standardQuaternionicWindow.embedding A)
        (standardQuaternionicWindow.embedding B) := by
  let prodAB : QuatHermitian3 :=
    ⟨(1 / 2 : ℝ) • ((A : QuatMatrix3) * (B : QuatMatrix3) + (B : QuatMatrix3) * (A : QuatMatrix3)), by
      rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial,
        A.prop, B.prop, add_comm]⟩
  have hjm := standardQuaternionicWindow.preserves_product A B prodAB rfl
  have htr : tracePairing (standardQuaternionicWindow.embedding A)
      (standardQuaternionicWindow.embedding B) =
      albertTrace (standardQuaternionicWindow.embedding prodAB) := by
    unfold tracePairing; rw [hjm]
  rw [htr, standardQuaternionicWindow.preserves_trace]
  have hs : Matrix.trace (symplecticQuatMat (prodAB : QuatMatrix3)) =
      2 * (((prodAB : QuatMatrix3) 0 0).re + ((prodAB : QuatMatrix3) 1 1).re +
        ((prodAB : QuatMatrix3) 2 2).re : ℂ) := symplecticQuatMat_trace _
  have hre : (Matrix.trace (symplecticQuatMat (prodAB : QuatMatrix3))).re =
      2 * (((prodAB : QuatMatrix3) 0 0).re + ((prodAB : QuatMatrix3) 1 1).re +
        ((prodAB : QuatMatrix3) 2 2).re) := by
    have h := congrArg Complex.re hs; simpa using h
  have hAB : (Matrix.trace (symplecticQuatMat (prodAB : QuatMatrix3))).re =
      (Matrix.trace (symplecticQuatMat (A : QuatMatrix3) *
        symplecticQuatMat (B : QuatMatrix3))).re := by
    change (Matrix.trace (symplecticQuatMat ((1 / 2 : ℝ) • ((A : QuatMatrix3) * (B : QuatMatrix3) +
      (B : QuatMatrix3) * (A : QuatMatrix3))))).re = _
    rw [symplecticQuatMat_smul, symplecticQuatMat_add, symplecticQuatMat_mul, symplecticQuatMat_mul,
      Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_comm (symplecticQuatMat (B : QuatMatrix3)),
      ← two_smul ℝ, smul_smul]
    norm_num
  rw [← hAB, hre]

theorem fourPoint_zero_c6_representation (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hzero : fourPointInvariant p = 0) :
    ∃ P : Fin 4 → HermitianEmbeddingMatrix 6,
      (∀ i, (P i).IsHermitian ∧ P i * P i = P i ∧ Matrix.trace (P i) = 2) ∧
      ∀ ρ : Albert, IsDensity ρ →
        ∃ σ : HermitianEmbeddingMatrix 6, IsEmbeddingDensity 6 σ ∧
          ∀ w : Word (Fin 4),
            (Matrix.trace (σ * wordOperator P w)).re = nativeWordProbability p ρ w := by
  obtain ⟨Q, hQ⟩ := (fourPointInvariant_eq_zero_iff p hp).mp hzero
  obtain ⟨g, hg⟩ := native_quaternionicWindow_conjugate_standard Q
  have hq_mem : ∀ i : Fin 4, g.linearEquiv (p i) ∈ LinearMap.range standardQuaternionicWindow.embedding :=
    fun i => by rw [standardQuaternionicWindow.range_eq]; exact (hg (p i)).mp (hQ i)
  choose q hq using hq_mem
  let P : Fin 4 → HermitianEmbeddingMatrix 6 := fun i => symplecticQuatMat (q i : QuatMatrix3)
  have hP_props : ∀ i : Fin 4, (P i).IsHermitian ∧ P i * P i = P i ∧ Matrix.trace (P i) = 2 := by
    intro i
    have hPi_atom : IsAtom (standardQuaternionicWindow.embedding (q i)) := by
      rw [hq i]; exact g.map_isAtom (hp i)
    have hqi_sq : (q i : QuatMatrix3) * (q i : QuatMatrix3) = (q i : QuatMatrix3) := by
      let q2 : QuatHermitian3 := ⟨(1 / 2 : ℝ) • ((q i : QuatMatrix3) * (q i : QuatMatrix3) +
        (q i : QuatMatrix3) * (q i : QuatMatrix3)), by
        rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_trivial, (q i).prop]⟩
      have he := standardQuaternionicWindow.preserves_product (q i) (q i) q2 rfl
      rw [hPi_atom.1] at he
      have hinj := congrArg Subtype.val (standardQuaternionicWindow.injective he)
      dsimp only [q2] at hinj
      rw [← two_smul ℝ, smul_smul] at hinj
      norm_num at hinj
      exact hinj
    have hqi_tr : (((q i : QuatMatrix3) 0 0).re + ((q i : QuatMatrix3) 1 1).re +
        ((q i : QuatMatrix3) 2 2).re) = 1 := by
      have ht := standardQuaternionicWindow.preserves_trace (q i)
      rw [hPi_atom.2] at ht
      exact ht.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.IsHermitian, ← symplecticQuatMat_star, (q i).prop]
    · dsimp only [P]; rw [← symplecticQuatMat_mul, hqi_sq]
    · dsimp only [P]; rw [symplecticQuatMat_trace]
      have hre : (((q i : QuatMatrix3) 0 0).re + ((q i : QuatMatrix3) 1 1).re +
          ((q i : QuatMatrix3) 2 2).re : ℂ) =
          ((((q i : QuatMatrix3) 0 0).re + ((q i : QuatMatrix3) 1 1).re +
            ((q i : QuatMatrix3) 2 2).re : ℝ) : ℂ) := by push_cast; rfl
      rw [hre, hqi_tr]; norm_num
  refine ⟨P, hP_props, fun ρ hρ => ?_⟩
  let ρ' := g.linearEquiv ρ
  have hρ' : IsDensity ρ' := g.map_isDensity hρ
  let ρQ : QuatHermitian3 :=
    quatHermitian3Equiv.symm (ρ'.1, ![((ρ'.2 0).1), ((ρ'.2 1).1), ((ρ'.2 2).1)])
  have hρQ_pair : ∀ M : QuatHermitian3,
      tracePairing (standardQuaternionicWindow.embedding ρQ)
        (standardQuaternionicWindow.embedding M) =
        tracePairing ρ' (standardQuaternionicWindow.embedding M) := by
    intro M
    have hρQ_eq : (standardQuaternionicWindow.embedding ρQ).1 = ρ'.1 ∧
        ((standardQuaternionicWindow.embedding ρQ).2 0 = quatEmbed1 ((ρ'.2 0).1)) ∧
        ((standardQuaternionicWindow.embedding ρQ).2 1 = quatEmbed1 ((ρ'.2 1).1)) ∧
        ((standardQuaternionicWindow.embedding ρQ).2 2 = quatEmbed1 ((ρ'.2 2).1)) := by
      have hp' := quatHermitian3Equiv.apply_symm_apply
        (ρ'.1, ![((ρ'.2 0).1), ((ρ'.2 1).1), ((ρ'.2 2).1)])
      refine ⟨?_, rfl, rfl, rfl⟩
      funext i
      exact congrArg (fun p : (Fin 3 → ℝ) × (Fin 3 → Quaternion ℝ) => p.1 i) hp'
    rw [tracePairing_eq_coords, tracePairing_eq_coords, hρQ_eq.1, hρQ_eq.2.1, hρQ_eq.2.2.1,
      hρQ_eq.2.2.2]
    have hdot : ∀ (o : Octonion) (q : Quaternion ℝ),
        octDot (quatEmbed1 o.1) (quatEmbed1 q) = octDot o (quatEmbed1 q) := fun o q => by
      rw [octDot_eq_coords, octDot_eq_coords]
      simp [quatEmbed1_apply]
    dsimp [standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding_apply, quatMatrixToAlbert]
    rw [hdot (ρ'.2 0), hdot (ρ'.2 1), hdot (ρ'.2 2)]
  let A : HermitianEmbeddingMatrix 6 := symplecticQuatMat (ρQ : QuatMatrix3)
  have hA_herm : A.IsHermitian := by
    rw [Matrix.IsHermitian, ← symplecticQuatMat_star, ρQ.prop]
  let U : HermitianEmbeddingMatrix 6 := hA_herm.eigenvectorUnitary
  let μ : Fin 6 → ℝ := hA_herm.eigenvalues
  have hUU : U.conjTranspose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA_herm.eigenvectorUnitary
  have hUUt : U * U.conjTranspose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hA_herm.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose := by
    simpa [U, μ, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hA_herm.spectral_theorem
  have hμ_nonneg : ∀ k : Fin 6, 0 ≤ μ k := by
    intro k
    let L : List ℝ := (List.finRange 6).filterMap (fun j => if μ j = μ k then none else some (μ j))
    let qF := evalQuatFactors L ρQ
    let qSq : QuatHermitian3 := ⟨(1 / 2 : ℝ) • ((qF : QuatMatrix3) * (qF : QuatMatrix3) +
      (qF : QuatMatrix3) * (qF : QuatMatrix3)), by
      rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_trivial, qF.prop]⟩
    have hqSq_emb : standardQuaternionicWindow.embedding qSq =
        jordanMul (standardQuaternionicWindow.embedding qF)
          (standardQuaternionicWindow.embedding qF) :=
      standardQuaternionicWindow.preserves_product qF qF qSq rfl
    have hnonneg_pair : 0 ≤ (Matrix.trace (A * symplecticQuatMat (qSq : QuatMatrix3))).re := by
      rw [symplectic_trace_mul_eq_pairing ρQ qSq, hρQ_pair, hqSq_emb]
      exact mul_nonneg (by norm_num) (tracePairing_positive_nonnegative ρ' _ hρ'.1
        ⟨standardQuaternionicWindow.embedding qF, rfl⟩)
    let val : Fin 6 → ℝ := fun i => (L.map (fun r => μ i - r)).prod
    have hqF_spec := evalQuatFactors_mat_spec L ρQ U μ hspec hUU hUUt
    have hqSq_spec : symplecticQuatMat (qSq : QuatMatrix3) =
        U * Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
      have hmat : (qSq : QuatMatrix3) = (qF : QuatMatrix3) * (qF : QuatMatrix3) := by
        dsimp only [qSq]; rw [← two_smul ℝ, smul_smul]; norm_num
      rw [hmat, symplecticQuatMat_mul, hqF_spec]
      calc
        (U * Matrix.diagonal (fun i => (val i : ℂ)) * U.conjTranspose) *
            (U * Matrix.diagonal (fun i => (val i : ℂ)) * U.conjTranspose)
          = U * Matrix.diagonal (fun i => (val i : ℂ)) * (U.conjTranspose * U) *
              Matrix.diagonal (fun i => (val i : ℂ)) * U.conjTranspose := by
                simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal (fun i => (val i : ℂ)) *
              Matrix.diagonal (fun i => (val i : ℂ))) * U.conjTranspose := by
                rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = U * Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
              rw [Matrix.diagonal_mul_diagonal]
              congr 1; congr 1; ext i; push_cast; ring
    have htr_eval : (Matrix.trace (A * symplecticQuatMat (qSq : QuatMatrix3))).re =
        ∑ i : Fin 6, μ i * val i ^ 2 := by
      have hmul : A * symplecticQuatMat (qSq : QuatMatrix3) =
          U * Matrix.diagonal (fun i => ((μ i * val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
        rw [hspec, hqSq_spec]
        calc
          (U * Matrix.diagonal (fun i => (μ i : ℂ)) * U.conjTranspose) *
              (U * Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose)
            = U * Matrix.diagonal (fun i => (μ i : ℂ)) * (U.conjTranspose * U) *
                Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
                  simp only [Matrix.mul_assoc]
          _ = U * (Matrix.diagonal (fun i => (μ i : ℂ)) *
                Matrix.diagonal (fun i => ((val i ^ 2 : ℝ) : ℂ))) * U.conjTranspose := by
                  rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = U * Matrix.diagonal (fun i => ((μ i * val i ^ 2 : ℝ) : ℂ)) * U.conjTranspose := by
                rw [Matrix.diagonal_mul_diagonal]
                congr 1; congr 1; ext i; push_cast; ring
      rw [hmul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal,
        Complex.re_sum]
      simp_rw [Complex.ofReal_re]
    have hzero_other : ∀ i : Fin 6, μ i ≠ μ k → val i = 0 := by
      intro i hne
      dsimp only [val]
      rw [List.prod_eq_zero_iff, List.mem_map]
      refine ⟨μ i, ?_, sub_self _⟩
      rw [List.mem_filterMap]
      exact ⟨i, List.mem_finRange i, by simp [hne]⟩
    have hprod_eq : ∀ i : Fin 6, μ i * val i ^ 2 = μ k * val i ^ 2 := fun i => by
      by_cases heq : μ i = μ k
      · rw [heq]
      · rw [hzero_other i heq]; ring
    have hvalk_ne : val k ≠ 0 := by
      intro h0
      dsimp only [val] at h0
      rw [List.prod_eq_zero_iff, List.mem_map] at h0
      rcases h0 with ⟨r, hr, hx0⟩
      rw [List.mem_filterMap] at hr
      rcases hr with ⟨j, _hj, hif⟩
      by_cases hjk : μ j = μ k
      · simp [hjk] at hif
      · simp [hjk] at hif
        rw [← hif] at hx0
        exact sub_ne_zero.mpr (Ne.symm hjk) hx0
    have hsum_pos : 0 < ∑ i : Fin 6, val i ^ 2 := by
      have hk_pos : 0 < val k ^ 2 := sq_pos_iff.mpr hvalk_ne
      have hle : val k ^ 2 ≤ ∑ i : Fin 6, val i ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (val i)) (Finset.mem_univ k)
      linarith
    have hfinal : 0 ≤ μ k * ∑ i : Fin 6, val i ^ 2 := by
      rw [Finset.mul_sum]
      calc
        0 ≤ (Matrix.trace (A * symplecticQuatMat (qSq : QuatMatrix3))).re := hnonneg_pair
        _ = ∑ i : Fin 6, μ i * val i ^ 2 := htr_eval
        _ = ∑ i : Fin 6, μ k * val i ^ 2 := Finset.sum_congr rfl fun i _ => hprod_eq i
    exact nonneg_of_mul_nonneg_left hfinal hsum_pos
  have hA_psd : A.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hA_herm, fun v => ?_⟩
    let D := Matrix.diagonal (fun i => (Real.sqrt (μ i) : ℂ))
    have hD2 : D * D = Matrix.diagonal (fun i => (μ i : ℂ)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; ext i; exact_mod_cast Real.mul_self_sqrt (hμ_nonneg i)
    have hD_herm : D.conjTranspose = D := by
      ext i j
      by_cases hij : i = j
      · subst j; simp [D]
      · simp [D, hij, Ne.symm hij]
    have hAA : A = (U * D) * (U * D).conjTranspose := by
      rw [Matrix.conjTranspose_mul, hD_herm, hspec, ← hD2]
      simp only [Matrix.mul_assoc]
    rw [hAA]
    let w := Matrix.mulVec (U * D).conjTranspose v
    have hval : star v ⬝ᵥ Matrix.mulVec ((U * D) * (U * D).conjTranspose) v =
        ∑ i : Fin 6, star (w i) * w i := by
      have hw : star w = Matrix.vecMul (star v) (U * D) := by
        dsimp only [w]
        rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← hw]
      refine Finset.sum_congr rfl fun i _ => by rw [Pi.star_apply, mul_comm]
    rw [hval]
    refine Finset.sum_nonneg fun i _ => ?_
    have hz : star (w i) * w i = (((w i).re ^ 2 + (w i).im ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re]; ring
      · simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]; ring
    rw [hz]
    exact_mod_cast add_nonneg (sq_nonneg (w i).re) (sq_nonneg (w i).im)
  let σ : HermitianEmbeddingMatrix 6 := (1 / 2 : ℝ) • A
  have hσ_psd : σ.PosSemidef := hA_psd.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hσ_tr : Matrix.trace σ = 1 := by
    have htr1 : Matrix.trace A = 2 := by
      rw [symplecticQuatMat_trace]
      have hρQ_tr : (((ρQ : QuatMatrix3) 0 0).re + ((ρQ : QuatMatrix3) 1 1).re +
          ((ρQ : QuatMatrix3) 2 2).re) = 1 := by
        have ht := standardQuaternionicWindow.preserves_trace ρQ
        have ht2 : albertTrace (standardQuaternionicWindow.embedding ρQ) = 1 := by
          rw [← tracePairing_unit_right, ← standardQuaternionicWindow.unit, hρQ_pair 1,
            standardQuaternionicWindow.unit, tracePairing_unit_right, hρ'.2]
        rw [ht2] at ht
        exact ht.symm
      have hre : (((ρQ : QuatMatrix3) 0 0).re + ((ρQ : QuatMatrix3) 1 1).re +
          ((ρQ : QuatMatrix3) 2 2).re : ℂ) =
          ((((ρQ : QuatMatrix3) 0 0).re + ((ρQ : QuatMatrix3) 1 1).re +
            ((ρQ : QuatMatrix3) 2 2).re : ℝ) : ℂ) := by push_cast; rfl
      rw [hre, hρQ_tr]; norm_num
    dsimp only [σ]
    rw [Matrix.trace_smul, htr1, Complex.real_smul]
    norm_num
  refine ⟨σ, ⟨hσ_psd, hσ_tr⟩, fun w => ?_⟩
  obtain ⟨Rw, hRw_val, hRw_emb⟩ := stdQuat_wordEffect_eq q w
  have hsym_op : ∀ ws : Word (Fin 4),
      wordOperator P ws = symplecticQuatMat (wordOperator (fun i => (q i : QuatMatrix3)) ws) := by
    intro ws
    induction ws with
    | nil => simp [wordOperator, wordAmplitude, symplecticQuatMat_one]
    | cons a ws ih =>
      unfold wordOperator at ih ⊢
      rw [wordAmplitude_cons, wordAmplitude_cons, star_mul, star_mul]
      have hout : algebraicOutcome P a = symplecticQuatMat (algebraicOutcome (fun i => (q i : QuatMatrix3)) a) := by
        cases a with
        | mk i b =>
          cases b
          · change 1 - P i = symplecticQuatMat (1 - (q i : QuatMatrix3))
            rw [sub_eq_add_neg, sub_eq_add_neg, symplecticQuatMat_add, symplecticQuatMat_one,
              show -((q i : QuatMatrix3)) = (-1 : ℝ) • (q i : QuatMatrix3) from (neg_one_smul ℝ _).symm,
              symplecticQuatMat_smul, neg_one_smul]
          · rfl
      have hstP : star (algebraicOutcome P a) = algebraicOutcome P a := by
        cases a with
        | mk i b =>
          cases b
          · simp [algebraicOutcome, Matrix.star_eq_conjTranspose, (hP_props i).1.eq]
          · simp [algebraicOutcome, Matrix.star_eq_conjTranspose, (hP_props i).1.eq]
      have hstq : star (algebraicOutcome (fun i => (q i : QuatMatrix3)) a) =
          algebraicOutcome (fun i => (q i : QuatMatrix3)) a := by
        cases a with
        | mk i b =>
          cases b
          · simp [algebraicOutcome]
          · simp [algebraicOutcome]
      calc
        star (algebraicOutcome P a) * star (wordAmplitude P ws) * (wordAmplitude P ws * algebraicOutcome P a)
          = algebraicOutcome P a * (star (wordAmplitude P ws) * wordAmplitude P ws) * algebraicOutcome P a := by
              rw [hstP]; simp only [Matrix.mul_assoc]
        _ = symplecticQuatMat (algebraicOutcome (fun i => (q i : QuatMatrix3)) a) *
              symplecticQuatMat (star (wordAmplitude (fun i => (q i : QuatMatrix3)) ws) *
                wordAmplitude (fun i => (q i : QuatMatrix3)) ws) *
              symplecticQuatMat (algebraicOutcome (fun i => (q i : QuatMatrix3)) a) := by
              rw [ih, hout]
        _ = symplecticQuatMat (star (algebraicOutcome (fun i => (q i : QuatMatrix3)) a) *
              star (wordAmplitude (fun i => (q i : QuatMatrix3)) ws) *
              (wordAmplitude (fun i => (q i : QuatMatrix3)) ws *
                algebraicOutcome (fun i => (q i : QuatMatrix3)) a)) := by
              rw [hstq, ← symplecticQuatMat_mul, ← symplecticQuatMat_mul]; simp only [Matrix.mul_assoc]
  have hsym : wordOperator P w = symplecticQuatMat (Rw : QuatMatrix3) :=
    (hsym_op w).trans (congrArg symplecticQuatMat hRw_val.symm)
  rw [hsym]
  dsimp only [σ]
  rw [Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [symplectic_trace_mul_eq_pairing ρQ Rw, hρQ_pair, hRw_emb]
  have hpeq : (fun i => standardQuaternionicWindow.embedding (q i)) =
      fun i => g.linearEquiv (p i) := funext hq
  rw [hpeq, ← nativeWordProbability_eq_pairing, nativeWordProbability_automorphism]
  ring

end AlbertSequential
