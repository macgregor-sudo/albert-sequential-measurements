/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FrameSlotNormalizers
public import NativeRecoveredCoordinates
public import Glennie.Diagonalization
public import Glennie.NativeQuadraticPositiveR01

@[expose] public section

namespace AlbertSequential

noncomputable section

open NativeAnalysis

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl
private theorem diagAtom_fst (i j : Fin 3) : (diagAtom i).1 j = if j = i then 1 else 0 := rfl
private theorem diagAtom_snd (i k : Fin 3) : (diagAtom i).2 k = 0 := rfl

private theorem albertTrace_albertUnit : albertTrace albertUnit = 3 := by
  simp [albertTrace, albertUnit]

private theorem albertTrace_jordanMul_self (y : Albert) :
    albertTrace (jordanMul y y) =
      (y.1 0) ^ 2 + (y.1 1) ^ 2 + (y.1 2) ^ 2 +
        2 * (octNormSq (y.2 0) + octNormSq (y.2 1) + octNormSq (y.2 2)) := by
  simp only [albertTrace, Fin.sum_univ_three, jordanMul_diag_0, jordanMul_diag_1,
    jordanMul_diag_2, octDot_self]
  ring

def compactAutoToNativeAuto (g : Glennie.CompactAutomorphism) : NativeAlbertAutomorphism where
  linearEquiv := (recoveredCoordinateEquiv.trans g.equiv).trans recoveredCoordinateEquiv.symm
  preserves_product x y := by
    apply recoveredCoordinateEquiv.injective
    simp only [LinearEquiv.trans_apply]
    rw [recoveredCoordinateEquiv_jordanMul, g.map_jordan, LinearEquiv.apply_symm_apply,
      recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  preserves_unit := by
    apply recoveredCoordinateEquiv.injective
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [recoveredCoordinateEquiv_unit, g.map_unit]
  preserves_trace x := by
    simp only [LinearEquiv.trans_apply]
    rw [← recoveredCoordinateEquiv_trace, LinearEquiv.apply_symm_apply, g.map_trace,
      recoveredCoordinateEquiv_trace]

def nativeAutoToCompactAuto (g : NativeAlbertAutomorphism) : Glennie.CompactAutomorphism where
  equiv := (recoveredCoordinateEquiv.symm.trans g.linearEquiv).trans recoveredCoordinateEquiv
  map_jordan x y := by
    simp only [LinearEquiv.trans_apply]
    have hxy : Glennie.jordan x y = recoveredCoordinateEquiv
        (jordanMul (recoveredCoordinateEquiv.symm x) (recoveredCoordinateEquiv.symm y)) := by
      rw [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    rw [hxy, LinearEquiv.symm_apply_apply, g.preserves_product, recoveredCoordinateEquiv_jordanMul]
  map_trace x := by
    simp only [LinearEquiv.trans_apply]
    rw [recoveredCoordinateEquiv_trace, g.preserves_trace, ← recoveredCoordinateEquiv_trace,
      LinearEquiv.apply_symm_apply]

@[simp] theorem compactAutoToNativeAuto_apply (g : Glennie.CompactAutomorphism) (x : Albert) :
    (compactAutoToNativeAuto g).linearEquiv x =
      recoveredCoordinateEquiv.symm (g.equiv (recoveredCoordinateEquiv x)) :=
  rfl

@[simp] theorem nativeAutoToCompactAuto_apply (g : NativeAlbertAutomorphism) (x : Glennie.Albert) :
    (nativeAutoToCompactAuto g).equiv x =
      recoveredCoordinateEquiv (g.linearEquiv (recoveredCoordinateEquiv.symm x)) :=
  rfl

private theorem recoveredCoordinateEquiv_diagAtom0 :
    recoveredCoordinateEquiv (diagAtom 0) = Glennie.standardFrame 0 := by
  apply Glennie.Albert.ext <;> rfl

private theorem recoveredCoordinateEquiv_diagAtom1 :
    recoveredCoordinateEquiv (diagAtom 1) = Glennie.standardFrame 1 := by
  apply Glennie.Albert.ext <;> rfl

private theorem recoveredCoordinateEquiv_diagAtom2 :
    recoveredCoordinateEquiv (diagAtom 2) = Glennie.standardFrame 2 := by
  apply Glennie.Albert.ext <;> rfl

private theorem glennie_diagonal_idempotent_cases (d : Glennie.Albert)
    (hd : Glennie.IsDiagonal d) (hid : Glennie.jordan d d = d) :
    (d.d0 = 0 ∨ d.d0 = 1) ∧ (d.d1 = 0 ∨ d.d1 = 1) ∧ (d.d2 = 0 ∨ d.d2 = 1) := by
  have h0 : d.d0 * d.d0 = d.d0 := by
    have h := congrArg Glennie.Albert.d0 hid
    simpa [Glennie.jordan_d0, hd.1, hd.2.1, Glennie.octDot_coordinates, Glennie.octNormSq,
      Quaternion.normSq_def'] using h
  have h1 : d.d1 * d.d1 = d.d1 := by
    have h := congrArg Glennie.Albert.d1 hid
    simpa [Glennie.jordan_d1, hd.1, hd.2.2, Glennie.octDot_coordinates, Glennie.octNormSq,
      Quaternion.normSq_def'] using h
  have h2 : d.d2 * d.d2 = d.d2 := by
    have h := congrArg Glennie.Albert.d2 hid
    simpa [Glennie.jordan_d2, hd.2.1, hd.2.2, Glennie.octDot_coordinates, Glennie.octNormSq,
      Quaternion.normSq_def'] using h
  have split : ∀ t : ℝ, t * t = t → t = 0 ∨ t = 1 := fun t ht => by
    have hfac : t * (t - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with ht0 | ht1
    · exact Or.inl ht0
    · exact Or.inr (sub_eq_zero.mp ht1)
  exact ⟨split d.d0 h0, split d.d1 h1, split d.d2 h2⟩

theorem accepted_atom_to_diagAtom0 (p : Albert) (hp : IsAtom p) :
    ∃ g : NativeAlbertAutomorphism, g.linearEquiv p = diagAtom 0 := by
  obtain ⟨g', hg'⟩ := Glennie.native_diagonalization (recoveredCoordinateEquiv p)
  let g0 := compactAutoToNativeAuto g'
  let q := g0.linearEquiv p
  let d := g'.equiv (recoveredCoordinateEquiv p)
  have hd_diag : Glennie.IsDiagonal d := hg'
  have hd_id : Glennie.jordan d d = d := by
    dsimp [d]
    rw [← g'.map_jordan, ← recoveredCoordinateEquiv_jordanMul, hp.1]
  have hd_tr : Glennie.trace d = 1 := by
    dsimp [d]
    rw [g'.map_trace, recoveredCoordinateEquiv_trace, hp.2]
  have hcases := glennie_diagonal_idempotent_cases d hd_diag hd_id
  have hsum : d.d0 + d.d1 + d.d2 = 1 := by
    simpa [Glennie.trace] using hd_tr
  have hq_eq : ∀ i j k : ℝ, d.d0 = i → d.d1 = j → d.d2 = k →
      d = i • Glennie.standardFrame 0 + j • Glennie.standardFrame 1 + k • Glennie.standardFrame 2 := by
    intro i j k hi hj hk
    apply Glennie.Albert.ext
    · simp [Glennie.standardFrame, hi]
    · simp [Glennie.standardFrame, hj]
    · simp [Glennie.standardFrame, hk]
    · simp [Glennie.standardFrame]; exact hd_diag.1
    · simp [Glennie.standardFrame]; exact hd_diag.2.1
    · simp [Glennie.standardFrame]; exact hd_diag.2.2
  rcases hcases with ⟨h0 | h0, h1 | h1, h2 | h2⟩
  · exfalso; linarith
  · have hdq : q = diagAtom 2 := by
      apply recoveredCoordinateEquiv.injective
      change d = recoveredCoordinateEquiv (diagAtom 2)
      rw [hq_eq 0 0 1 h0 h1 h2, recoveredCoordinateEquiv_diagAtom2]
      simp [Glennie.standardFrame]
    refine ⟨swap02AlbertAuto.comp g0, ?_⟩
    change swap02AlbertAuto.linearEquiv q = diagAtom 0
    rw [hdq, swap02AlbertAuto_diagAtom]
    rfl
  · have hdq : q = diagAtom 1 := by
      apply recoveredCoordinateEquiv.injective
      change d = recoveredCoordinateEquiv (diagAtom 1)
      rw [hq_eq 0 1 0 h0 h1 h2, recoveredCoordinateEquiv_diagAtom1]
      simp [Glennie.standardFrame]
    refine ⟨swap01AlbertAuto.comp g0, ?_⟩
    change swap01AlbertAuto.linearEquiv q = diagAtom 0
    rw [hdq, swap01AlbertAuto_diagAtom]
    rfl
  · exfalso; linarith
  · have hdq : q = diagAtom 0 := by
      apply recoveredCoordinateEquiv.injective
      change d = recoveredCoordinateEquiv (diagAtom 0)
      rw [hq_eq 1 0 0 h0 h1 h2, recoveredCoordinateEquiv_diagAtom0]
      simp [Glennie.standardFrame]
    exact ⟨g0, hdq⟩
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith

private theorem glennie_realRotation12_fix_diagAtom0 (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (compactAutoToNativeAuto (Glennie.realRotation12Automorphism c s h)).linearEquiv (diagAtom 0) =
      diagAtom 0 := by
  apply recoveredCoordinateEquiv.injective
  simp only [compactAutoToNativeAuto_apply, LinearEquiv.apply_symm_apply,
    recoveredCoordinateEquiv_diagAtom0]
  let z := (Glennie.realRotation12Automorphism c s h).equiv (Glennie.standardFrame 0)
  have hz0 : z.d0 = 1 := Glennie.realRotation12_d0 c s (Glennie.standardFrame 0)
  have hz1 : z.d1 = 0 := by
    change (Glennie.realConjugateAlbert (Glennie.realRotation12 c s) (Glennie.standardFrame 0)).d1 = 0
    rw [Glennie.realRotation12_d1]
    simp [Glennie.standardFrame, Glennie.octRe]
  have hz2 : z.d2 = 0 := by
    change (Glennie.realConjugateAlbert (Glennie.realRotation12 c s) (Glennie.standardFrame 0)).d2 = 0
    rw [Glennie.realRotation12_d2]
    simp [Glennie.standardFrame, Glennie.octRe]
  have hn : Glennie.inner z z = 1 := by
    dsimp [z]
    rw [(Glennie.realRotation12Automorphism c s h).inner_map]
    simp [Glennie.inner_self_coordinates, Glennie.standardFrame,
      Glennie.octNormSq, Quaternion.normSq_def']
  rw [Glennie.inner_self_coordinates, hz0, hz1, hz2] at hn
  have h01 := Glennie.octNormSq_nonneg z.o01
  have h02 := Glennie.octNormSq_nonneg z.o02
  have h12 := Glennie.octNormSq_nonneg z.o12
  have hz01 : z.o01 = 0 := (Glennie.octNormSq_eq_zero _).mp (by nlinarith)
  have hz02 : z.o02 = 0 := (Glennie.octNormSq_eq_zero _).mp (by nlinarith)
  have hz12 : z.o12 = 0 := (Glennie.octNormSq_eq_zero _).mp (by nlinarith)
  apply Glennie.Albert.ext
  · exact hz0
  · exact hz1
  · exact hz2
  · exact hz01
  · exact hz02
  · exact hz12

private theorem glennie_realRotation12_o01_o02_normSq (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1)
    (y : Glennie.Albert) :
    Glennie.octNormSq ((Glennie.realRotation12Automorphism c s h).equiv y).o01 +
      Glennie.octNormSq ((Glennie.realRotation12Automorphism c s h).equiv y).o02 =
    Glennie.octNormSq y.o01 + Glennie.octNormSq y.o02 := by
  change Glennie.octNormSq (Glennie.realConjugateAlbert (Glennie.realRotation12 c s) y).o01 +
      Glennie.octNormSq (Glennie.realConjugateAlbert (Glennie.realRotation12 c s) y).o02 = _
  simp only [Glennie.realConjugateAlbert, Glennie.fromMatrix, Glennie.matrixConjugateReal,
    Glennie.matrixRowMix, Glennie.matrixColMix, Glennie.toMatrix, Glennie.realRotation12,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  simp only [one_smul, zero_smul, add_zero, zero_add]
  have hdot : ∀ (a b : ℝ) (u v : Glennie.Octonion),
      Glennie.octDot (a • u) (b • v) = a * b * Glennie.octDot u v := fun a b u v => by
    rw [Glennie.octDot_smul_left, Glennie.octDot_comm, Glennie.octDot_smul_left,
      Glennie.octDot_comm]
    ring
  have hadd : ∀ u v : Glennie.Octonion,
      Glennie.octNormSq (c • u + s • v) + Glennie.octNormSq ((-s) • u + c • v) =
        (c ^ 2 + s ^ 2) * (Glennie.octNormSq u + Glennie.octNormSq v) := fun u v => by
    rw [Glennie.octNormSq_add, Glennie.octNormSq_add, Glennie.octNormSq_smul,
      Glennie.octNormSq_smul, Glennie.octNormSq_smul, Glennie.octNormSq_smul, hdot, hdot]
    ring
  have heq := hadd y.o01 y.o02
  rw [h, one_mul] at heq
  simpa [neg_smul] using heq

theorem accepted_corner12_zero_fixing_diagAtom0 (x : Albert) :
    ∃ g : NativeAlbertAutomorphism,
      g.linearEquiv (diagAtom 0) = diagAtom 0 ∧ (g.linearEquiv x).2 2 = 0 := by
  obtain ⟨g1, hg1_diag, r1, hr1_nn, hr1_slot⟩ := exists_frameStab_slot12_real x
  let y := g1.linearEquiv x
  by_cases hr1 : r1 = 0
  · refine ⟨g1, hg1_diag 0, ?_⟩
    change y.2 2 = 0
    rw [hr1_slot, hr1, octonionScalar_zero]
  · have hr1_pos : 0 < r1 := lt_of_le_of_ne hr1_nn (Ne.symm hr1)
    let y' := recoveredCoordinateEquiv y
    have hy'_o12 : y'.o12 = Glennie.octScalar r1 := by
      change (y.2 2 : Octonion) = Glennie.octScalar r1
      rw [hr1_slot]
      apply Prod.ext <;> apply Quaternion.ext <;> rfl
    have hy'_re : Glennie.octRe y'.o12 = r1 := by
      rw [hy'_o12, Glennie.octRe_scalar]
    have hy'_ns : Glennie.octNormSq y'.o12 = r1 ^ 2 := by
      rw [hy'_o12, Glennie.octNormSq, Quaternion.normSq_def']
      simp [Glennie.octScalar]
    obtain ⟨c, s, hcs, hmax⟩ := Glennie.exists_rotation_improving_energy y'.d1 y'.d2 r1 hr1_pos
    let g2' := Glennie.realRotation12Automorphism c s hcs
    let z' := g2'.equiv y'
    have hz0 : z'.d0 = y'.d0 := Glennie.realRotation12_d0 c s y'
    have hz1 : z'.d1 = c ^ 2 * y'.d1 + s ^ 2 * y'.d2 + 2 * c * s * r1 := by
      change (Glennie.realConjugateAlbert (Glennie.realRotation12 c s) y').d1 = _
      rw [Glennie.realRotation12_d1, hy'_re]
    have hz2 : z'.d2 = s ^ 2 * y'.d1 + c ^ 2 * y'.d2 - 2 * c * s * r1 := by
      change (Glennie.realConjugateAlbert (Glennie.realRotation12 c s) y').d2 = _
      rw [Glennie.realRotation12_d2, hy'_re]
    have hdiag_sum : z'.d1 ^ 2 + z'.d2 ^ 2 = y'.d1 ^ 2 + y'.d2 ^ 2 + 2 * r1 ^ 2 := by
      rw [hz1, hz2]
      exact hmax
    have hinner : z'.d0 ^ 2 + z'.d1 ^ 2 + z'.d2 ^ 2 +
        2 * (Glennie.octNormSq z'.o01 + Glennie.octNormSq z'.o02 + Glennie.octNormSq z'.o12) =
        y'.d0 ^ 2 + y'.d1 ^ 2 + y'.d2 ^ 2 +
          2 * (Glennie.octNormSq y'.o01 + Glennie.octNormSq y'.o02 + Glennie.octNormSq y'.o12) := by
      simpa [Glennie.inner_self_coordinates] using g2'.inner_map y' y'
    have ho01_02 : Glennie.octNormSq z'.o01 + Glennie.octNormSq z'.o02 =
        Glennie.octNormSq y'.o01 + Glennie.octNormSq y'.o02 :=
      glennie_realRotation12_o01_o02_normSq c s hcs y'
    have hz0_sq : z'.d0 ^ 2 = y'.d0 ^ 2 := congrArg (· ^ 2) hz0
    have hz12_nn : 0 ≤ Glennie.octNormSq z'.o12 := Glennie.octNormSq_nonneg z'.o12
    have hz12_ns : Glennie.octNormSq z'.o12 = 0 := by
      linarith [hz0_sq, hdiag_sum, hinner, ho01_02, hy'_ns, hz12_nn]
    have hz12 : z'.o12 = 0 := (Glennie.octNormSq_eq_zero _).mp hz12_ns
    let g2 := compactAutoToNativeAuto g2'
    refine ⟨g2.comp g1, ?_, ?_⟩
    · change g2.linearEquiv (g1.linearEquiv (diagAtom 0)) = diagAtom 0
      rw [hg1_diag 0]
      exact glennie_realRotation12_fix_diagAtom0 c s hcs
    · change (recoveredCoordinateEquiv (recoveredCoordinateEquiv.symm z')).o12 = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hz12

private theorem quadraticMap_diagAtom0 (x : Albert) :
    quadraticMap (diagAtom 0) x = tracePairing (diagAtom 0) x • diagAtom 0 := by
  rw [tracePairing_diagAtom]
  unfold quadraticMap
  rw [(diagAtom_isAtom 0).1, two_nsmul, jordanMul_diagAtom0, jordanMul_diagAtom0]
  apply albert_ext
  · change x.1 0 + x.1 0 - x.1 0 = x.1 0 * 1; ring
  · change (0 : ℝ) + 0 - 0 = x.1 0 * 0; ring
  · change (0 : ℝ) + 0 - 0 = x.1 0 * 0; ring
  · change ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • x.2 0) + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • x.2 0) -
      (1 / 2 : ℝ) • x.2 0) = x.1 0 • (0 : Octonion); module
  · change ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • x.2 1) + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • x.2 1) -
      (1 / 2 : ℝ) • x.2 1) = x.1 0 • (0 : Octonion); module
  · change (0 : Octonion) + 0 - 0 = x.1 0 • (0 : Octonion); module

theorem accepted_quadraticMap_diagAtom0_right (a : Albert) :
    IsPositive (quadraticMap a (diagAtom 0)) := by
  have h := Glennie.NativeQuadraticPositiveR01.U_standardFrame_zero_positive (recoveredCoordinateEquiv a)
  rcases h with ⟨y', hy'⟩
  refine ⟨recoveredCoordinateEquiv.symm y', ?_⟩
  apply recoveredCoordinateEquiv.injective
  rw [recoveredCoordinateEquiv_jordanMul, LinearEquiv.apply_symm_apply, hy',
    recoveredCoordinateEquiv_quadraticMap, recoveredCoordinateEquiv_diagAtom0]

theorem accepted_quadraticMap_atom (p x : Albert) (hp : IsAtom p) :
    quadraticMap p x = tracePairing p x • p := by
  obtain ⟨g, hg⟩ := accepted_atom_to_diagAtom0 p hp
  apply g.linearEquiv.injective
  rw [g.map_quadraticMap, hg, map_smul, quadraticMap_diagAtom0, ← hg, g.map_tracePairing]

theorem accepted_albertSharp_atom_eq_zero (p : Albert) (hp : IsAtom p) :
    albertSharp p = 0 :=
  albertSharp_of_isAtom hp

theorem acceptedAtomAndRankOneBridge : AtomAndRankOneBridge where
  atom_to_diagAtom0 := accepted_atom_to_diagAtom0
  corner12_zero_fixing_diagAtom0 := accepted_corner12_zero_fixing_diagAtom0
  quadraticMap_atom := accepted_quadraticMap_atom
  albertSharp_atom_eq_zero := accepted_albertSharp_atom_eq_zero

theorem atom_to_diagAtom0 (p : Albert) (hp : IsAtom p) :
    ∃ g : NativeAlbertAutomorphism, g.linearEquiv p = diagAtom 0 :=
  accepted_atom_to_diagAtom0 p hp

theorem corner12_zero_fixing_diagAtom0 (x : Albert) :
    ∃ g : NativeAlbertAutomorphism,
      g.linearEquiv (diagAtom 0) = diagAtom 0 ∧ (g.linearEquiv x).2 2 = 0 :=
  accepted_corner12_zero_fixing_diagAtom0 x

theorem quadraticMap_atom (p x : Albert) (hp : IsAtom p) :
    quadraticMap p x = tracePairing p x • p :=
  accepted_quadraticMap_atom p x hp

theorem albertSharp_atom_eq_zero (p : Albert) (hp : IsAtom p) :
    albertSharp p = 0 :=
  accepted_albertSharp_atom_eq_zero p hp

theorem native_frame_to_standardFrame (F : NativeJordanFrame) :
    ∃ g : NativeAlbertAutomorphism, ∀ i : Fin 3, g.linearEquiv (F.atom i) = diagAtom i :=
  frame_to_standardFrame acceptedAtomAndRankOneBridge F

theorem native_complexWindow_conjugate_standard (W : ComplexWindow) :
    ∃ g : NativeAlbertAutomorphism, ∀ M : Hermitian3,
      g.linearEquiv (W.embedding M) = standardComplexWindow.embedding M :=
  complexWindow_conjugate_standard acceptedAtomAndRankOneBridge W

theorem native_quaternionicWindow_conjugate_standard_embedding (Q : QuaternionicWindow) :
    ∃ g : NativeAlbertAutomorphism, ∀ M : QuatHermitian3,
      g.linearEquiv (Q.embedding M) = standardQuaternionicWindow.embedding M :=
  quaternionicWindow_conjugate_standard_embedding acceptedAtomAndRankOneBridge Q

theorem native_quaternionicWindow_conjugate_standard (Q : QuaternionicWindow) :
    ∃ g : NativeAlbertAutomorphism, ∀ x,
      x ∈ Q.subalgebra.carrier ↔ g.linearEquiv x ∈ standardQuaternionicWindow.subalgebra.carrier :=
  quaternionicWindow_conjugate_standard acceptedAtomAndRankOneBridge Q

theorem idempotent_dichotomy (c : Albert) (hc : jordanMul c c = c) :
    (c = 0 ∧ albertTrace c = 0) ∨
    (IsAtom c ∧ albertTrace c = 1) ∨
    ((∃ q : Albert, IsAtom q ∧ c = albertUnit - q) ∧ albertTrace c = 2) ∨
    (c = albertUnit ∧ albertTrace c = 3) := by
  obtain ⟨g', hg'⟩ := Glennie.native_diagonalization (recoveredCoordinateEquiv c)
  let d := g'.equiv (recoveredCoordinateEquiv c)
  have hd_id : Glennie.jordan d d = d := by
    dsimp [d]
    rw [← g'.map_jordan, ← recoveredCoordinateEquiv_jordanMul, hc]
  have hcases := glennie_diagonal_idempotent_cases d hg' hd_id
  let g := compactAutoToNativeAuto g'
  have hge : g.linearEquiv c = recoveredCoordinateEquiv.symm d := by
    simp [g, d]
  have hd_eq : ∀ i j k : ℝ, d.d0 = i → d.d1 = j → d.d2 = k →
      d = i • Glennie.standardFrame 0 + j • Glennie.standardFrame 1 + k • Glennie.standardFrame 2 := by
    intro i j k hi hj hk
    apply Glennie.Albert.ext
    · simp [Glennie.standardFrame, hi]
    · simp [Glennie.standardFrame, hj]
    · simp [Glennie.standardFrame, hk]
    · simp [Glennie.standardFrame]; exact hg'.1
    · simp [Glennie.standardFrame]; exact hg'.2.1
    · simp [Glennie.standardFrame]; exact hg'.2.2
  have hid_comp : jordanMul (albertUnit - c) (albertUnit - c) = albertUnit - c := by
    simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
      jordanMul_albertUnit_right, hc]
    abel
  have htrace_d : albertTrace c = d.d0 + d.d1 + d.d2 := by
    rw [← recoveredCoordinateEquiv_trace, ← g'.map_trace]
    rfl
  have hco : ∀ (htr : albertTrace c = 2),
      (∃ q : Albert, IsAtom q ∧ c = albertUnit - q) ∧ albertTrace c = 2 := fun htr => by
    refine ⟨⟨albertUnit - c, ⟨hid_comp, ?_⟩, by abel⟩, htr⟩
    rw [albertTrace_sub, albertTrace_albertUnit, htr]
    norm_num
  rcases hcases with ⟨h0 | h0, h1 | h1, h2 | h2⟩
  · left
    have hc0 : c = 0 := by
      apply g.linearEquiv.injective
      apply recoveredCoordinateEquiv.injective
      rw [map_zero, map_zero, hge, LinearEquiv.apply_symm_apply, hd_eq 0 0 0 h0 h1 h2]
      simp
    exact ⟨hc0, by rw [htrace_d, h0, h1, h2]; norm_num⟩
  · right; left
    have htr : albertTrace c = 1 := by rw [htrace_d, h0, h1, h2]; norm_num
    exact ⟨⟨hc, htr⟩, htr⟩
  · right; left
    have htr : albertTrace c = 1 := by rw [htrace_d, h0, h1, h2]; norm_num
    exact ⟨⟨hc, htr⟩, htr⟩
  · right; right; left
    exact hco (by rw [htrace_d, h0, h1, h2]; norm_num)
  · right; left
    have htr : albertTrace c = 1 := by rw [htrace_d, h0, h1, h2]; norm_num
    exact ⟨⟨hc, htr⟩, htr⟩
  · right; right; left
    exact hco (by rw [htrace_d, h0, h1, h2]; norm_num)
  · right; right; left
    exact hco (by rw [htrace_d, h0, h1, h2]; norm_num)
  · right; right; right
    have hc1 : c = albertUnit := by
      apply g.linearEquiv.injective
      apply recoveredCoordinateEquiv.injective
      rw [g.preserves_unit, recoveredCoordinateEquiv_unit, hge, LinearEquiv.apply_symm_apply,
        hd_eq 1 1 1 h0 h1 h2]
      apply Glennie.Albert.ext <;> simp [Glennie.standardFrame]
    exact ⟨hc1, by rw [htrace_d, h0, h1, h2]; norm_num⟩

theorem idempotent_support_lemma {c x : Albert} (hc : jordanMul c c = c)
    (hx : IsPositive x) (hcx : tracePairing c x = 0) :
    jordanMul c x = 0 ∧ quadraticMap c x = 0 ∧ quadraticMap (albertUnit - c) x = x := by
  rcases idempotent_dichotomy c hc with ⟨rfl, _⟩ | ⟨hAtom, _⟩ | ⟨⟨q, hq, rfl⟩, _⟩ | ⟨rfl, _⟩
  · refine ⟨jordanMul_zero_left x, ?_, ?_⟩
    · simp [quadraticMap, jordanMul_zero_left, jordanMul_zero_right]
    · simp [quadraticMap, jordanMul_albertUnit_left, jordanMul_albertUnit_right, two_smul]
  · exact support_of_atom_zero_pairing acceptedAtomAndRankOneBridge hAtom hx hcx
  · simpa [sub_sub_cancel] using
      support_of_corankOne_zero_pairing acceptedAtomAndRankOneBridge hq hx hcx
  · obtain ⟨y, rfl⟩ := hx
    have htr : albertTrace (jordanMul y y) = 0 := by
      simpa [tracePairing, jordanMul_albertUnit_left] using hcx
    rw [albertTrace_jordanMul_self] at htr
    have hs1 : 0 ≤ (y.1 0) ^ 2 + (y.1 1) ^ 2 + (y.1 2) ^ 2 :=
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
    have hs2 : 0 ≤ 2 * (octNormSq (y.2 0) + octNormSq (y.2 1) + octNormSq (y.2 2)) :=
      mul_nonneg (by norm_num) (add_nonneg (add_nonneg (octNormSq_nonneg _) (octNormSq_nonneg _))
        (octNormSq_nonneg _))
    have hsplit := (add_eq_zero_iff_of_nonneg hs1 hs2).mp htr
    have hs1a := (add_eq_zero_iff_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)).mp hsplit.1
    have hs1b := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hs1a.1
    have h0 : y.1 0 = 0 := sq_eq_zero_iff.mp hs1b.1
    have h1 : y.1 1 = 0 := sq_eq_zero_iff.mp hs1b.2
    have h2 : y.1 2 = 0 := sq_eq_zero_iff.mp hs1a.2
    have hn_sum : octNormSq (y.2 0) + octNormSq (y.2 1) + octNormSq (y.2 2) = 0 := by
      linarith [hsplit.2]
    have hs2a := (add_eq_zero_iff_of_nonneg (add_nonneg (octNormSq_nonneg _) (octNormSq_nonneg _))
      (octNormSq_nonneg _)).mp hn_sum
    have hs2b := (add_eq_zero_iff_of_nonneg (octNormSq_nonneg _) (octNormSq_nonneg _)).mp hs2a.1
    have h01 : y.2 0 = 0 := (octNormSq_eq_zero _).mp hs2b.1
    have h02 : y.2 1 = 0 := (octNormSq_eq_zero _).mp hs2b.2
    have h12 : y.2 2 = 0 := (octNormSq_eq_zero _).mp hs2a.2
    have hy0 : y = 0 := by
      apply albert_ext <;> simp [h0, h1, h2, h01, h02, h12] <;> rfl
    subst hy0
    simp [quadraticMap, jordanMul_zero_right]

private theorem peirce_decomposition_diagAtom0 (y : Albert) :
    quadraticMap (diagAtom 0) y +
      (2 : ℝ) • (jordanMul (diagAtom 0) y - quadraticMap (diagAtom 0) y) +
      quadraticMap (albertUnit - diagAtom 0) y = y ∧
    jordanMul (diagAtom 0) (quadraticMap (diagAtom 0) y) = quadraticMap (diagAtom 0) y ∧
    jordanMul (diagAtom 0) ((2 : ℝ) • (jordanMul (diagAtom 0) y - quadraticMap (diagAtom 0) y)) =
      (1 / 2 : ℝ) • ((2 : ℝ) • (jordanMul (diagAtom 0) y - quadraticMap (diagAtom 0) y)) ∧
    jordanMul (diagAtom 0) (quadraticMap (albertUnit - diagAtom 0) y) = 0 := by
  have hq0 : quadraticMap (diagAtom 0) y = y.1 0 • diagAtom 0 := by
    rw [quadraticMap_diagAtom0, tracePairing_diagAtom]
  have h1c : albertUnit - diagAtom 0 = diagAtom 1 + diagAtom 2 := by
    have h := diagAtom_sum_eq_unit
    rw [Fin.sum_univ_three] at h
    rw [← h]
    abel
  let v0 : Albert := (fun _ => 0, ![0, 0, y.2 2])
  have hj12 : ∀ z : Albert, jordanMul (diagAtom 1 + diagAtom 2) z =
      (![0, z.1 1, z.1 2], ![(1 / 2 : ℝ) • z.2 0, (1 / 2 : ℝ) • z.2 1, z.2 2]) := fun z => by
    rw [jordanMul_add_left, jordanMul_diagAtom1, jordanMul_diagAtom2]
    apply albert_ext
    · change 0 + 0 = (0 : ℝ); ring
    · change z.1 1 + 0 = z.1 1; ring
    · change (0 : ℝ) + z.1 2 = z.1 2; ring
    · change (1 / 2 : ℝ) • z.2 0 + 0 = (1 / 2 : ℝ) • z.2 0; module
    · change (0 : Octonion) + (1 / 2 : ℝ) • z.2 1 = (1 / 2 : ℝ) • z.2 1; module
    · change (1 / 2 : ℝ) • z.2 2 + (1 / 2 : ℝ) • z.2 2 = z.2 2; module
  have hq0c : quadraticMap (albertUnit - diagAtom 0) y =
      v0 + (y.1 1 • diagAtom 1 + y.1 2 • diagAtom 2) := by
    unfold quadraticMap
    have hsq : jordanMul (albertUnit - diagAtom 0) (albertUnit - diagAtom 0) =
        albertUnit - diagAtom 0 := by
      simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
        jordanMul_albertUnit_right, (diagAtom_isAtom 0).1]
      abel
    rw [hsq, h1c, two_nsmul, hj12, hj12]
    apply albert_ext
    · change (0 : ℝ) + 0 - 0 = 0 + (y.1 1 * (if (0 : Fin 3) = 1 then 1 else 0) +
        y.1 2 * (if (0 : Fin 3) = 2 then 1 else 0)); norm_num
    · change y.1 1 + y.1 1 - y.1 1 = 0 + (y.1 1 * (if (1 : Fin 3) = 1 then 1 else 0) +
        y.1 2 * (if (1 : Fin 3) = 2 then 1 else 0)); norm_num
    · change y.1 2 + y.1 2 - y.1 2 = 0 + (y.1 1 * (if (2 : Fin 3) = 1 then 1 else 0) +
        y.1 2 * (if (2 : Fin 3) = 2 then 1 else 0)); norm_num
    · change (1 / 2 : ℝ) • ((1 / 2 : ℝ) • y.2 0) + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • y.2 0) -
        (1 / 2 : ℝ) • y.2 0 = (0 : Octonion) + (y.1 1 • 0 + y.1 2 • 0); module
    · change (1 / 2 : ℝ) • ((1 / 2 : ℝ) • y.2 1) + (1 / 2 : ℝ) • ((1 / 2 : ℝ) • y.2 1) -
        (1 / 2 : ℝ) • y.2 1 = (0 : Octonion) + (y.1 1 • 0 + y.1 2 • 0); module
    · change y.2 2 + y.2 2 - y.2 2 = y.2 2 + (y.1 1 • (0 : Octonion) + y.1 2 • 0); module
  have hj0_sub : jordanMul (diagAtom 0) y - y.1 0 • diagAtom 0 =
      ((fun _ => (0 : ℝ), ![(1 / 2 : ℝ) • y.2 0, (1 / 2 : ℝ) • y.2 1, 0]) : Albert) := by
    rw [jordanMul_diagAtom0]
    apply albert_ext
    · change y.1 0 - y.1 0 * 1 = 0; ring
    · change (0 : ℝ) - y.1 0 * 0 = 0; ring
    · change (0 : ℝ) - y.1 0 * 0 = 0; ring
    · change (1 / 2 : ℝ) • y.2 0 - y.1 0 • 0 = (1 / 2 : ℝ) • y.2 0; module
    · change (1 / 2 : ℝ) • y.2 1 - y.1 0 • 0 = (1 / 2 : ℝ) • y.2 1; module
    · change (0 : Octonion) - y.1 0 • 0 = 0; module
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq0, hj0_sub, hq0c]
    apply albert_ext
    · change y.1 0 * 1 + 2 * 0 + (0 + (y.1 1 * (if (0 : Fin 3) = 1 then 1 else 0) +
        y.1 2 * (if (0 : Fin 3) = 2 then 1 else 0))) = y.1 0; simp
    · change y.1 0 * 0 + 2 * 0 + (0 + (y.1 1 * (if (1 : Fin 3) = 1 then 1 else 0) +
        y.1 2 * (if (1 : Fin 3) = 2 then 1 else 0))) = y.1 1; simp
    · change y.1 0 * 0 + 2 * 0 + (0 + (y.1 1 * (if (2 : Fin 3) = 1 then 1 else 0) +
        y.1 2 * (if (2 : Fin 3) = 2 then 1 else 0))) = y.1 2; simp
    · change y.1 0 • (0 : Octonion) + (2 : ℝ) • ((1 / 2 : ℝ) • y.2 0) +
        ((0 : Octonion) + (y.1 1 • 0 + y.1 2 • 0)) = y.2 0; module
    · change y.1 0 • (0 : Octonion) + (2 : ℝ) • ((1 / 2 : ℝ) • y.2 1) +
        ((0 : Octonion) + (y.1 1 • 0 + y.1 2 • 0)) = y.2 1; module
    · change y.1 0 • (0 : Octonion) + (2 : ℝ) • (0 : Octonion) +
        (y.2 2 + (y.1 1 • (0 : Octonion) + y.1 2 • 0)) = y.2 2; module
  · rw [hq0, jordanMul_smul_right, (diagAtom_isAtom 0).1]
  · rw [hq0, hj0_sub, jordanMul_diagAtom0]
    apply albert_ext
    · change (2 : ℝ) * (0 : ℝ) = (1 / 2 : ℝ) * (2 * 0); ring
    · change (0 : ℝ) = (1 / 2 : ℝ) * (2 * 0); ring
    · change (0 : ℝ) = (1 / 2 : ℝ) * (2 * 0); ring
    · change (1 / 2 : ℝ) • ((2 : ℝ) • ((1 / 2 : ℝ) • y.2 0)) =
        (1 / 2 : ℝ) • ((2 : ℝ) • ((1 / 2 : ℝ) • y.2 0)); rfl
    · change (1 / 2 : ℝ) • ((2 : ℝ) • ((1 / 2 : ℝ) • y.2 1)) =
        (1 / 2 : ℝ) • ((2 : ℝ) • ((1 / 2 : ℝ) • y.2 1)); rfl
    · change (0 : Octonion) = (1 / 2 : ℝ) • ((2 : ℝ) • (0 : Octonion)); module
  · rw [hq0c, jordanMul_add_right, jordanMul_add_right, jordanMul_smul_right, jordanMul_smul_right,
      diagAtom_orthogonal (i := 0) (j := 1) (by decide),
      diagAtom_orthogonal (i := 0) (j := 2) (by decide), smul_zero, smul_zero,
      add_zero, add_zero, jordanMul_diagAtom0]
    apply albert_ext <;> simp [v0] <;> rfl

private theorem peirce_xhalf_eq {c : Albert} (hc : jordanMul c c = c) (x : Albert) :
    (4 : ℝ) • (jordanMul c x - jordanMul c (jordanMul c x)) =
      (2 : ℝ) • (jordanMul c x - quadraticMap c x) := by
  unfold quadraticMap
  rw [hc]
  module

theorem peirce_decomposition {c : Albert} (hc : jordanMul c c = c) (x : Albert) :
    let x1 := quadraticMap c x
    let xhalf := (4 : ℝ) • (jordanMul c x - jordanMul c (jordanMul c x))
    let x0 := quadraticMap (albertUnit - c) x
    x1 + xhalf + x0 = x ∧ jordanMul c x1 = x1 ∧ jordanMul c xhalf = (1 / 2 : ℝ) • xhalf ∧
      jordanMul c x0 = 0 := by
  dsimp only
  rw [peirce_xhalf_eq hc x]
  rcases idempotent_dichotomy c hc with ⟨rfl, _⟩ | ⟨hAtom, _⟩ | ⟨⟨q, hq, rfl⟩, _⟩ | ⟨rfl, _⟩
  · simp [quadraticMap, jordanMul_zero_left, jordanMul_zero_right,
      jordanMul_albertUnit_left, jordanMul_albertUnit_right, two_smul]
  · obtain ⟨g, hg⟩ := atom_to_diagAtom0 c hAtom
    have hd := peirce_decomposition_diagAtom0 (g.linearEquiv x)
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply g.linearEquiv.injective
      rw [map_add, map_add, map_smul, map_sub, g.preserves_product, g.map_quadraticMap,
        g.map_quadraticMap, map_sub, g.preserves_unit, hg]
      exact hd.1
    · apply g.linearEquiv.injective
      rw [g.preserves_product, g.map_quadraticMap, hg]
      exact hd.2.1
    · apply g.linearEquiv.injective
      rw [g.preserves_product, map_smul, map_smul, map_smul, map_sub, g.preserves_product,
        g.map_quadraticMap, hg]
      exact hd.2.2.1
    · apply g.linearEquiv.injective
      rw [g.preserves_product, map_zero, g.map_quadraticMap, map_sub, g.preserves_unit, hg]
      exact hd.2.2.2
  · obtain ⟨g, hg⟩ := atom_to_diagAtom0 q hq
    set y := g.linearEquiv x
    have hd := peirce_decomposition_diagAtom0 y
    have hge : g.linearEquiv (albertUnit - q) = albertUnit - diagAtom 0 := by
      rw [map_sub, g.preserves_unit, hg]
    have hid_sub_q : albertUnit - (albertUnit - q) = q := by abel
    have hmid : (2 : ℝ) • (jordanMul (albertUnit - diagAtom 0) y -
        quadraticMap (albertUnit - diagAtom 0) y) =
        (2 : ℝ) • (jordanMul (diagAtom 0) y - quadraticMap (diagAtom 0) y) := by
      have hs := hd.1
      rw [jordanMul_sub_left, jordanMul_albertUnit_left]
      have h1 : (y - jordanMul (diagAtom 0) y) - quadraticMap (albertUnit - diagAtom 0) y =
          jordanMul (diagAtom 0) y - quadraticMap (diagAtom 0) y := by
        calc
          (y - jordanMul (diagAtom 0) y) - quadraticMap (albertUnit - diagAtom 0) y
            = (quadraticMap (diagAtom 0) y + (2 : ℝ) • (jordanMul (diagAtom 0) y -
                quadraticMap (diagAtom 0) y) + quadraticMap (albertUnit - diagAtom 0) y) -
                jordanMul (diagAtom 0) y - quadraticMap (albertUnit - diagAtom 0) y := by
              rw [hs]
          _ = jordanMul (diagAtom 0) y - quadraticMap (diagAtom 0) y := by
              rw [two_smul]; abel
      rw [h1]
    have hx1_map : g.linearEquiv (quadraticMap (albertUnit - q) x) =
        quadraticMap (albertUnit - diagAtom 0) y := by
      rw [g.map_quadraticMap, hge]
    have hxhalf_map : g.linearEquiv ((2 : ℝ) • (jordanMul (albertUnit - q) x -
        quadraticMap (albertUnit - q) x)) =
        (2 : ℝ) • (jordanMul (diagAtom 0) y - quadraticMap (diagAtom 0) y) := by
      rw [map_smul, map_sub, g.preserves_product, hge, hx1_map, hmid]
    have hx0_map : g.linearEquiv (quadraticMap (albertUnit - (albertUnit - q)) x) =
        quadraticMap (diagAtom 0) y := by
      rw [hid_sub_q, g.map_quadraticMap, hg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply g.linearEquiv.injective
      rw [map_add, map_add, hx1_map, hxhalf_map, hx0_map]
      conv_rhs => change y; rw [← hd.1]
      abel
    · apply g.linearEquiv.injective
      rw [g.preserves_product, hge, hx1_map, jordanMul_sub_left,
        jordanMul_albertUnit_left, hd.2.2.2, sub_zero]
    · apply g.linearEquiv.injective
      rw [g.preserves_product, hge, hxhalf_map]
      conv_rhs => rw [map_smul, hxhalf_map]
      rw [jordanMul_sub_left, jordanMul_albertUnit_left, hd.2.2.1]
      module
    · apply g.linearEquiv.injective
      rw [g.preserves_product, map_zero, hge, hx0_map, jordanMul_sub_left,
        jordanMul_albertUnit_left, hd.2.1, sub_self]
  · simp [quadraticMap, jordanMul_albertUnit_left, jordanMul_albertUnit_right,
      jordanMul_zero_left, jordanMul_zero_right]
    refine ⟨by module, by module⟩

theorem peirce_components_mem_subalgebra (B : NativeJordanSubalgebra) {c x : Albert}
    (hcB : c ∈ B.carrier) (hxB : x ∈ B.carrier) :
    quadraticMap c x ∈ B.carrier ∧
    (4 : ℝ) • (jordanMul c x - jordanMul c (jordanMul c x)) ∈ B.carrier ∧
    quadraticMap (albertUnit - c) x ∈ B.carrier := by
  have hmul_c_x : jordanMul c x ∈ B.carrier := B.product_mem c hcB x hxB
  have hmul_c_c : jordanMul c c ∈ B.carrier := B.product_mem c hcB c hcB
  have hq : quadraticMap c x ∈ B.carrier := by
    unfold quadraticMap
    rw [two_nsmul]
    have hcx2 : jordanMul c (jordanMul c x) ∈ B.carrier := B.product_mem c hcB _ hmul_c_x
    exact B.carrier.sub_mem (B.carrier.add_mem hcx2 hcx2) (B.product_mem _ hmul_c_c x hxB)
  have hhalf : (4 : ℝ) • (jordanMul c x - jordanMul c (jordanMul c x)) ∈ B.carrier :=
    B.carrier.smul_mem (4 : ℝ) (B.carrier.sub_mem hmul_c_x (B.product_mem c hcB _ hmul_c_x))
  have hcc : albertUnit - c ∈ B.carrier := B.carrier.sub_mem B.unit_mem hcB
  have hq0 : quadraticMap (albertUnit - c) x ∈ B.carrier := by
    unfold quadraticMap
    rw [two_nsmul]
    have hccx2 : jordanMul (albertUnit - c) (jordanMul (albertUnit - c) x) ∈ B.carrier :=
      B.product_mem _ hcc _ (B.product_mem _ hcc x hxB)
    exact B.carrier.sub_mem (B.carrier.add_mem hccx2 hccx2)
      (B.product_mem _ (B.product_mem _ hcc _ hcc) x hxB)
  exact ⟨hq, hhalf, hq0⟩

end

end AlbertSequential
