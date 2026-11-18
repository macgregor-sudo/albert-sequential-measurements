/-
SPDX-License-Identifier: Apache-2.0
-/
module

public import Defs
public import NativeAlbertLaws
public import NativeMatrixTrace
public import NativeWordDuality
public import FrameSlotNormalizers
public import AcceptedRootAtomAdapter
public import ThirteenTracesAndAform
public import ThreeAtomAndFourPoint
public import ComplexWindowDeterminantAndMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Universal Six-Step Affinity in Double-Pair Traces (`app:cert:universalsix`)

Formalizes the algebraic core of `prop:cer:universalsix` (`app:cert:universalsix`,
paragraphs "Traces with one occurrence of an atom" and "Expansion and counting"):
for any four Albert atoms `p` with `0 < fourPointInvariant p` and any two atom
quadruples `pPlus, pMinus : Fin 4 → Albert` sharing all pairwise overlaps and
triple triangles with `p` and satisfying the `lam`-affine double-pair relation
`t_r(p) = lam * t_r(pPlus) + (1 - lam) * t_r(pMinus)` (`r = 1, 2, 3`),
every sequential word probability from `(1 / 3 : ℝ) • albertUnit` of length at
most six satisfies the same `lam`-affine relation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace AlbertSequential.MatchingModels

open AlbertSequential
open AlbertSequential.NativeAnalysis

/-! ## Section 1: Elementary Jordan, Trace, and Quadratic-Update Helpers -/

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

private theorem albertTrace_albertUnit : albertTrace albertUnit = 3 := by
  unfold albertTrace albertUnit
  rw [Fin.sum_univ_three]
  norm_num

private theorem tracePairing_atom_self {p : Albert} (hp : IsAtom p) :
    tracePairing p p = 1 := by
  unfold tracePairing
  rw [hp.1, hp.2]

private theorem tracePairing_atom_unit {p : Albert} (hp : IsAtom p) :
    tracePairing p albertUnit = 1 := by
  rw [tracePairing_unit_right, hp.2]

private theorem quadraticMap_compl_atom {p : Albert} (hp : IsAtom p) (x : Albert) :
    quadraticMap (albertUnit - p) x =
      x + (-2 : ℝ) • jordanMul p x + tracePairing p x • p := by
  have hqa : (2 : ℝ) • jordanMul p (jordanMul p x) - jordanMul p x =
      tracePairing p x • p := by
    have h := quadraticMap_atom p x hp
    unfold quadraticMap at h
    rw [hp.1, two_smul] at h
    simpa [two_smul] using h
  unfold quadraticMap
  simp only [two_smul, jordanMul_sub_left, jordanMul_sub_right,
    jordanMul_albertUnit_left, jordanMul_albertUnit_right, hp.1]
  rw [← hqa]
  module

/-! ## Section 2: Cubic Norm Formula, `tripleDelta`, and Non-degeneracy -/

theorem albertCubicNorm_three_atoms {p1 p2 p3 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) :
    albertCubicNorm (p1 + p2 + p3) =
      1 - tracePairing p1 p2 - tracePairing p1 p3 - tracePairing p2 p3 +
        2 * tracePairing p1 (jordanMul p2 p3) := by
  let x := p1 + p2 + p3
  have htr : albertTrace x = 3 := by
    dsimp [x]
    rw [albertTrace_add, albertTrace_add, hp1.2, hp2.2, hp3.2]
    norm_num
  have h11 : tracePairing p1 p1 = 1 := tracePairing_atom_self hp1
  have h22 : tracePairing p2 p2 = 1 := tracePairing_atom_self hp2
  have h33 : tracePairing p3 p3 = 1 := tracePairing_atom_self hp3
  have hxx : tracePairing x x =
      3 + 2 * (tracePairing p1 p2 + tracePairing p1 p3 + tracePairing p2 p3) := by
    dsimp [x]
    simp only [tracePairing_add_left, tracePairing_add_right, h11, h22, h33,
      tracePairing_comm p2 p1, tracePairing_comm p3 p1, tracePairing_comm p3 p2]
    ring
  have hx2 : jordanMul x x =
      x + (2 : ℝ) • jordanMul p1 p2 + (2 : ℝ) • jordanMul p1 p3 +
        (2 : ℝ) • jordanMul p2 p3 := by
    dsimp [x]
    simp only [jordanMul_add_left, jordanMul_add_right, hp1.1, hp2.1, hp3.1,
      jordanMul_comm p2 p1, jordanMul_comm p3 p1, jordanMul_comm p3 p2]
    module
  have hr12_1 : tracePairing p1 (jordanMul p1 p2) = tracePairing p1 p2 := by
    rw [← tracePairing_associative, hp1.1]
  have hr12_2 : tracePairing p2 (jordanMul p1 p2) = tracePairing p1 p2 := by
    rw [jordanMul_comm p1 p2, ← tracePairing_associative, hp2.1, tracePairing_comm]
  have hr13_1 : tracePairing p1 (jordanMul p1 p3) = tracePairing p1 p3 := by
    rw [← tracePairing_associative, hp1.1]
  have hr13_3 : tracePairing p3 (jordanMul p1 p3) = tracePairing p1 p3 := by
    rw [jordanMul_comm p1 p3, ← tracePairing_associative, hp3.1, tracePairing_comm]
  have hr23_2 : tracePairing p2 (jordanMul p2 p3) = tracePairing p2 p3 := by
    rw [← tracePairing_associative, hp2.1]
  have hr23_3 : tracePairing p3 (jordanMul p2 p3) = tracePairing p2 p3 := by
    rw [jordanMul_comm p2 p3, ← tracePairing_associative, hp3.1, tracePairing_comm]
  have hr_213 : tracePairing p2 (jordanMul p1 p3) = tracePairing p1 (jordanMul p2 p3) := by
    rw [← tracePairing_associative, jordanMul_comm p2 p1, tracePairing_associative]
  have hr_312 : tracePairing p3 (jordanMul p1 p2) = tracePairing p1 (jordanMul p2 p3) := by
    rw [tracePairing_comm, tracePairing_associative]
  have hxxx : tracePairing x (jordanMul x x) =
      3 + 6 * (tracePairing p1 p2 + tracePairing p1 p3 + tracePairing p2 p3) +
        6 * tracePairing p1 (jordanMul p2 p3) := by
    rw [hx2]
    dsimp [x]
    simp only [tracePairing_add_right, tracePairing_smul_right,
      tracePairing_add_left, h11, h22, h33,
      tracePairing_comm p2 p1, tracePairing_comm p3 p1, tracePairing_comm p3 p2,
      hr12_1, hr12_2, hr13_1, hr13_3, hr23_2, hr23_3, hr_213, hr_312]
    ring
  rw [albertCubicNorm_eq_tracePairing, albertSharp_eq_jordanMul]
  change (1 / 3 : ℝ) * tracePairing x (jordanMul x x - albertTrace x • x +
    ((1 / 2 : ℝ) * ((albertTrace x) ^ 2 - tracePairing x x)) • albertUnit) = _
  rw [tracePairing_add_right, tracePairing_sub_right, tracePairing_smul_right,
    tracePairing_smul_right, tracePairing_unit_right, htr, hxx, hxxx]
  ring

theorem tripleDelta_eq_poly {p1 p2 p3 : Albert}
    (hp1 : IsAtom p1) (hp2 : IsAtom p2) (hp3 : IsAtom p3) :
    tripleDelta p1 p2 p3 =
      (1 - tracePairing p1 p2 - tracePairing p1 p3 - tracePairing p2 p3 +
        2 * tracePairing p1 (jordanMul p2 p3)) *
      (tracePairing p1 p2 * tracePairing p2 p3 * tracePairing p1 p3 -
        (tracePairing p1 (jordanMul p2 p3)) ^ 2) := by
  unfold tripleDelta
  rw [albertCubicNorm_three_atoms hp1 hp2 hp3]

theorem tripleDelta_eq_of_traces_eq {p q : Fin 4 → Albert}
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i))
    (ho : ∀ i j, fpOverlap p i j = fpOverlap q i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle q i j k)
    (a b c : Fin 4) :
    tripleDelta (q a) (q b) (q c) = tripleDelta (p a) (p b) (p c) := by
  have hab : tracePairing (q a) (q b) = tracePairing (p a) (p b) := (ho a b).symm
  have hac : tracePairing (q a) (q c) = tracePairing (p a) (p c) := (ho a c).symm
  have hbc : tracePairing (q b) (q c) = tracePairing (p b) (p c) := (ho b c).symm
  have habc : tracePairing (q a) (jordanMul (q b) (q c)) =
      tracePairing (p a) (jordanMul (p b) (p c)) := by
    have h := (hR b c a).symm
    unfold fpTriangle at h
    simpa only [tracePairing_comm] using h
  rw [tripleDelta_eq_poly (hq a) (hq b) (hq c),
    tripleDelta_eq_poly (hp a) (hp b) (hp c), hab, hac, hbc, habc]

private theorem exists_fourth_index (a b c : Fin 4) :
    ∃ d : Fin 4, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  have hcard : ({a, b, c} : Finset (Fin 4)).card ≤ 3 := by
    have h1 := Finset.card_insert_le a ({b, c} : Finset (Fin 4))
    have h2 := Finset.card_insert_le b ({c} : Finset (Fin 4))
    have h3 : ({c} : Finset (Fin 4)).card = 1 := Finset.card_singleton c
    omega
  have hne : (Finset.univ \ ({a, b, c} : Finset (Fin 4))).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff]
    have hsub : ({a, b, c} : Finset (Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
    rw [Finset.inter_eq_left.mpr hsub, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨d, hd⟩ := hne
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
    Finset.mem_singleton, true_and, not_or] at hd
  exact ⟨d, hd.1, hd.2.1, hd.2.2⟩

theorem tripleDelta_ne_zero_of_fourPointInvariant_pos {p : Fin 4 → Albert}
    (hp : ∀ i, IsAtom (p i)) (hpos : 0 < fourPointInvariant p)
    {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tripleDelta (p a) (p b) (p c) ≠ 0 := by
  obtain ⟨d, hda, hdb, hdc⟩ := exists_fourth_index a b c
  let f : Fin 4 → Fin 4 := ![a, b, c, d]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
    all_goals first | rfl | exact absurd hij hab | exact absurd hij hac |
      exact absurd hij hda.symm | exact absurd hij hab.symm | exact absurd hij hbc |
      exact absurd hij hdb.symm | exact absurd hij hac.symm | exact absurd hij hbc.symm |
      exact absurd hij hdc.symm | exact absurd hij hda | exact absurd hij hdb |
      exact absurd hij hdc
  let σ : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩)
  have hperm : (fun i => p (σ i)) = ![p a, p b, p c, p d] := by
    funext i
    fin_cases i <;> rfl
  have hfp_ne : fourPointInvariant ![p a, p b, p c, p d] ≠ 0 := by
    rw [← hperm, fourPointInvariant_perm_invariant σ p]
    exact hpos.ne'
  intro hz
  exact hfp_ne (prop_windowdet_zero (hp a) (hp b) (hp c) (hp d) hz)

/-! ## Section 3: Explicit 9-Element Jordan Basis of `Hermitian3` -/

private def mkHermDyad (v : Fin 3 → ℂ) : Hermitian3 :=
  ⟨Matrix.of (fun i j => v i * star (v j)), by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    ext i j
    simp [Matrix.conjTranspose_apply, mul_comm]⟩

private def hermJordanMul (A B : Hermitian3) : Hermitian3 :=
  ⟨(1 / 2 : ℝ) • ((A : ComplexMatrix3) * (B : ComplexMatrix3) +
      (B : ComplexMatrix3) * (A : ComplexMatrix3)), by
    rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial]
    have hA : star (A : ComplexMatrix3) = A := A.prop
    have hB : star (B : ComplexMatrix3) = B := B.prop
    rw [hA, hB, add_comm]⟩

private theorem standardComplexWindow_hermJordanMul (A B : Hermitian3) :
    standardComplexWindow.embedding (hermJordanMul A B) =
      jordanMul (standardComplexWindow.embedding A) (standardComplexWindow.embedding B) :=
  standardComplexWindow.preserves_product A B (hermJordanMul A B) rfl

private def cInner (u w : Fin 3 → ℂ) : ℂ := ∑ k : Fin 3, star (u k) * w k

private theorem cInner_conj (u w : Fin 3 → ℂ) : star (cInner u w) = cInner w u := by
  unfold cInner
  rw [Fin.sum_univ_three, Fin.sum_univ_three, star_add, star_add,
    star_mul, star_mul, star_mul, star_star, star_star, star_star]

private def Hmat (u w : Fin 3 → ℂ) : ComplexMatrix3 :=
  Matrix.of (fun a b => cInner u w * (u a * star (w b)) + cInner w u * (w a * star (u b)))

private def Kmat (u w : Fin 3 → ℂ) : ComplexMatrix3 :=
  Matrix.of (fun a b => Complex.I * (cInner u w * (u a * star (w b)) - cInner w u * (w a * star (u b))))

private theorem hermJordanMul_mkHermDyad (u w : Fin 3 → ℂ) :
    ((hermJordanMul (mkHermDyad u) (mkHermDyad w) : Hermitian3) : ComplexMatrix3) =
      (1 / 2 : ℝ) • Hmat u w := by
  ext a b
  change (1 / 2 : ℝ) • ((∑ k : Fin 3, (u a * star (u k)) * (w k * star (w b))) +
      (∑ k : Fin 3, (w a * star (w k)) * (u k * star (u b)))) =
    (1 / 2 : ℝ) • (cInner u w * (u a * star (w b)) + cInner w u * (w a * star (u b)))
  congr 1
  unfold cInner
  simp only [Fin.sum_univ_three]
  ring

private theorem hermJordanMul_triple_entry (u₁ u₂ u₃ : Fin 3 → ℂ) (a c : Fin 3) :
    (4 : ℝ) • (((hermJordanMul (hermJordanMul (mkHermDyad u₁) (mkHermDyad u₂))
        (mkHermDyad u₃) : Hermitian3) : ComplexMatrix3) a c) =
      cInner u₁ u₂ * cInner u₂ u₃ * (u₁ a * star (u₃ c)) +
      cInner u₂ u₁ * cInner u₁ u₃ * (u₂ a * star (u₃ c)) +
      cInner u₁ u₂ * cInner u₃ u₁ * (u₃ a * star (u₂ c)) +
      cInner u₂ u₁ * cInner u₃ u₂ * (u₃ a * star (u₁ c)) := by
  change (4 : ℝ) • ((1 / 2 : ℝ) • ((∑ k : Fin 3,
      ((hermJordanMul (mkHermDyad u₁) (mkHermDyad u₂) : Hermitian3) : ComplexMatrix3) a k *
        (u₃ k * star (u₃ c))) +
      (∑ k : Fin 3, (u₃ a * star (u₃ k)) *
        ((hermJordanMul (mkHermDyad u₁) (mkHermDyad u₂) : Hermitian3) : ComplexMatrix3) k c))) = _
  simp_rw [hermJordanMul_mkHermDyad]
  simp only [Hmat, Matrix.smul_apply, Matrix.of_apply, Complex.real_smul,
    cInner, Fin.sum_univ_three]
  push_cast
  ring

private theorem complex_re_mul_two (z : ℂ) : (2 : ℂ) * (z.re : ℂ) = z + star z := by
  apply Complex.ext
  · simp; ring
  · simp

private theorem complex_im_mul_two_I (z : ℂ) :
    (2 : ℂ) * Complex.I * (z.im : ℂ) = z - star z := by
  apply Complex.ext
  · simp
  · simp; ring

private theorem complex_mul_star_self_re (z : ℂ) : ((z * star z).re : ℂ) = z * star z := by
  apply Complex.ext <;> simp [Complex.mul_im, mul_comm]

private theorem triple_jordan_formula (u₁ u₂ u₃ : Fin 3 → ℂ) :
    let b := cInner u₁ u₂ * cInner u₂ u₃ * cInner u₃ u₁
    let n₁₃ := (cInner u₁ u₃ * cInner u₃ u₁).re
    let n₂₃ := (cInner u₂ u₃ * cInner u₃ u₂).re
    (n₁₃ * n₂₃ * 4 : ℝ) •
        (((hermJordanMul (hermJordanMul (mkHermDyad u₁) (mkHermDyad u₂))
          (mkHermDyad u₃) : Hermitian3) : ComplexMatrix3)) =
      (n₂₃ * b.re) • Hmat u₁ u₃ + (n₁₃ * b.re) • Hmat u₂ u₃ -
        (n₂₃ * b.im) • Kmat u₃ u₁ - (n₁₃ * b.im) • Kmat u₂ u₃ := by
  intro b n₁₃ n₂₃
  ext a c
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  rw [show ((n₁₃ * n₂₃ * 4 : ℝ) : ℂ) * _ =
      ((n₁₃ : ℂ) * (n₂₃ : ℂ)) * (((4 : ℝ) • (((hermJordanMul
        (hermJordanMul (mkHermDyad u₁) (mkHermDyad u₂))
          (mkHermDyad u₃) : Hermitian3) : ComplexMatrix3) a c))) by
    simp [Complex.real_smul]; ring]
  rw [hermJordanMul_triple_entry]
  have hn13 : (n₁₃ : ℂ) = cInner u₁ u₃ * cInner u₃ u₁ := by
    dsimp only [n₁₃]
    rw [← cInner_conj u₁ u₃]
    exact complex_mul_star_self_re _
  have hn23 : (n₂₃ : ℂ) = cInner u₂ u₃ * cInner u₃ u₂ := by
    dsimp only [n₂₃]
    rw [← cInner_conj u₂ u₃]
    exact complex_mul_star_self_re _
  have hbr : (b.re : ℂ) = (b + star b) / 2 := by
    rw [← complex_re_mul_two b]; ring
  have hbi : (b.im : ℂ) = (b - star b) / (2 * Complex.I) := by
    rw [← complex_im_mul_two_I b]
    have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
    field_simp [hI]
  have hsb : star b = cInner u₂ u₁ * cInner u₃ u₂ * cInner u₁ u₃ := by
    dsimp only [b]
    rw [star_mul, star_mul, cInner_conj, cInner_conj, cInner_conj]
    ring
  simp only [Hmat, Kmat, Matrix.of_apply]
  push_cast
  rw [hn13, hn23, hbr, hbi, hsb]
  dsimp only [b]
  field_simp [Complex.I_ne_zero]
  ring

private def stdBasisHerm (B₀ B₁ C₀ C₁ C₂ C₃ : ℝ) (k : Fin 9) : Hermitian3 :=
  let v₁ : Fin 3 → ℂ := ![1, 0, 0]
  let v₂ : Fin 3 → ℂ := ![B₀, B₁, 0]
  let v₃ : Fin 3 → ℂ := ![C₀, ⟨C₁, C₂⟩, C₃]
  let X := mkHermDyad v₁
  let Y := mkHermDyad v₂
  let Z := mkHermDyad v₃
  match k.val with
  | 0 => X
  | 1 => Y
  | 2 => Z
  | 3 => hermJordanMul X Y
  | 4 => hermJordanMul X Z
  | 5 => hermJordanMul Y Z
  | 6 => hermJordanMul (hermJordanMul X Y) Z
  | 7 => hermJordanMul (hermJordanMul Y Z) X
  | _ => hermJordanMul (hermJordanMul Z X) Y

private theorem complex_pair_decomp (w g : ℂ) (hg : g ≠ 0) (A B : ComplexMatrix3) :
    ((w / g).re : ℝ) • (g • A + star g • B) +
      ((w / g).im : ℝ) • (Complex.I • (g • A - star g • B)) =
    w • A + star w • B := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  have hq : ((w / g).re : ℂ) + Complex.I * ((w / g).im : ℂ) = w / g := by
    rw [mul_comm Complex.I]; exact Complex.re_add_im _
  have hqs : ((w / g).re : ℂ) - Complex.I * ((w / g).im : ℂ) = star (w / g) := by
    calc
      ((w / g).re : ℂ) - Complex.I * ((w / g).im : ℂ)
        = star (((w / g).re : ℂ) + Complex.I * ((w / g).im : ℂ)) := by
            apply Complex.ext
            · simp
            · simp
      _ = star (w / g) := by rw [hq]
  have hstar : star (w / g) * star g = star w := by
    rw [← star_mul, mul_div_cancel₀ w hg]
  have hdiv : (w / g) * g = w := div_mul_cancel₀ w hg
  calc
    ((w / g).re : ℂ) * (g * A i j + star g * B i j) +
        ((w / g).im : ℂ) * (Complex.I * (g * A i j - star g * B i j))
      = (((w / g).re : ℂ) + Complex.I * ((w / g).im : ℂ)) * g * A i j +
          (((w / g).re : ℂ) - Complex.I * ((w / g).im : ℂ)) * star g * B i j := by ring
    _ = (w / g) * g * A i j + star (w / g) * star g * B i j := by rw [hq, hqs]
    _ = w * A i j + star w * B i j := by rw [hdiv, hstar]

private theorem fin_sum_univ_nine {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
    (∑ k : Fin 9, f k) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + f 8))))))) = _
  abel

private theorem hermitian3_span_stdBasis (B₀ B₁ C₀ C₁ C₂ C₃ : ℝ)
    (hB0 : B₀ ≠ 0) (hB1 : B₁ ≠ 0) (hC0 : C₀ ≠ 0) (hC2 : C₂ ≠ 0) (hC3 : C₃ ≠ 0)
    (M : Hermitian3) :
    ∃ c : Fin 9 → ℝ, M = ∑ k : Fin 9, c k • stdBasisHerm B₀ B₁ C₀ C₁ C₂ C₃ k := by
  let z : ℂ := ⟨C₁, C₂⟩
  let v₁ : Fin 3 → ℂ := ![1, 0, 0]
  let v₂ : Fin 3 → ℂ := ![B₀, B₁, 0]
  let v₃ : Fin 3 → ℂ := ![C₀, z, C₃]
  let v : Fin 3 → (Fin 3 → ℂ) := ![v₁, v₂, v₃]
  let T : ComplexMatrix3 := Matrix.of (fun i j => v j i)
  let Tinv : ComplexMatrix3 :=
    Matrix.of ![![1, -(B₀ / B₁ : ℂ), (B₀ * z / B₁ - C₀) / C₃],
                ![0, (1 / B₁ : ℂ), -(z / (B₁ * C₃))],
                ![0, 0, (1 / C₃ : ℂ)]]
  have hB1C : (B₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB1
  have hC3C : (C₃ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC3
  have hTTinv : T * Tinv = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Tinv, v, v₁, v₂, v₃, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp [hB1C, hC3C] <;> ring
  let N : ComplexMatrix3 := Tinv * (M : ComplexMatrix3) * Tinv.conjTranspose
  have hM_ct : (M : ComplexMatrix3).conjTranspose = (M : ComplexMatrix3) := M.prop
  have hN_herm : N.IsHermitian := by
    simp only [N, Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hM_ct, Matrix.mul_assoc]
  have hM_rec : (M : ComplexMatrix3) = T * N * T.conjTranspose := by
    have h1 : T * Tinv * (M : ComplexMatrix3) * (T * Tinv).conjTranspose = (M : ComplexMatrix3) := by
      rw [hTTinv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    rw [← h1]
    simp only [N, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hN_diag : ∀ i : Fin 3, N i i = ((N i i).re : ℂ) := fun i => by
    have h := congrArg Complex.im (congrFun (congrFun hN_herm.eq i) i)
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at h
    apply Complex.ext
    · rfl
    · simp; linarith
  have hN_sym : ∀ i j : Fin 3, N j i = star (N i j) := fun i j => by
    have h := congrFun (congrFun hN_herm.eq j) i
    simpa [Matrix.conjTranspose_apply] using h.symm
  let outer : (Fin 3 → ℂ) → (Fin 3 → ℂ) → ComplexMatrix3 :=
    fun u w => Matrix.of (fun a b => u a * star (w b))
  have hM_sum : (M : ComplexMatrix3) =
      ((N 0 0).re : ℝ) • ((mkHermDyad v₁ : Hermitian3) : ComplexMatrix3) +
      ((N 1 1).re : ℝ) • ((mkHermDyad v₂ : Hermitian3) : ComplexMatrix3) +
      ((N 2 2).re : ℝ) • ((mkHermDyad v₃ : Hermitian3) : ComplexMatrix3) +
      (N 0 1 • outer v₁ v₂ + star (N 0 1) • outer v₂ v₁) +
      (N 0 2 • outer v₁ v₃ + star (N 0 2) • outer v₃ v₁) +
      (N 1 2 • outer v₂ v₃ + star (N 1 2) • outer v₃ v₂) := by
    rw [hM_rec]
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, mkHermDyad, outer, Matrix.of_apply, Fin.sum_univ_three, T, v]
    rw [hN_diag 0, hN_diag 1, hN_diag 2, hN_sym 0 1, hN_sym 0 2, hN_sym 1 2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_re]
    ring
  have hg12_val : cInner v₁ v₂ = (B₀ : ℂ) := by
    simp [cInner, v₁, v₂, Fin.sum_univ_three]
  have hg13_val : cInner v₁ v₃ = (C₀ : ℂ) := by
    simp [cInner, v₁, v₃, Fin.sum_univ_three]
  have hg23_val : cInner v₂ v₃ = (B₀ * C₀ : ℂ) + (B₁ : ℂ) * z := by
    simp [cInner, v₂, v₃, Fin.sum_univ_three]
  have hg12_ne : cInner v₁ v₂ ≠ 0 := by rw [hg12_val]; exact Complex.ofReal_ne_zero.mpr hB0
  have hg13_ne : cInner v₁ v₃ ≠ 0 := by rw [hg13_val]; exact Complex.ofReal_ne_zero.mpr hC0
  have hg23_ne : cInner v₂ v₃ ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [hg23_val] at him
    simp [z] at him
    rcases him with h1 | h2
    · exact hB1 h1
    · exact hC2 h2
  have H_eq : ∀ u w : Fin 3 → ℂ, Hmat u w = cInner u w • outer u w + star (cInner u w) • outer w u := by
    intro u w
    ext a b
    simp [Hmat, outer, cInner_conj]
  have K_eq : ∀ u w : Fin 3 → ℂ,
      Kmat u w = Complex.I • (cInner u w • outer u w - star (cInner u w) • outer w u) := by
    intro u w
    ext a b
    simp [Kmat, outer, cInner_conj]
  have hp01 := complex_pair_decomp (N 0 1) (cInner v₁ v₂) hg12_ne (outer v₁ v₂) (outer v₂ v₁)
  have hp02 := complex_pair_decomp (N 0 2) (cInner v₁ v₃) hg13_ne (outer v₁ v₃) (outer v₃ v₁)
  have hp12 := complex_pair_decomp (N 1 2) (cInner v₂ v₃) hg23_ne (outer v₂ v₃) (outer v₃ v₂)
  rw [← H_eq v₁ v₂, ← K_eq v₁ v₂] at hp01
  rw [← H_eq v₁ v₃, ← K_eq v₁ v₃] at hp02
  rw [← H_eq v₂ v₃, ← K_eq v₂ v₃] at hp12
  rw [← hp01, ← hp02, ← hp12] at hM_sum
  have hH_span : ∀ u w : Fin 3 → ℂ,
      Hmat u w = (2 : ℝ) • ((hermJordanMul (mkHermDyad u) (mkHermDyad w) : Hermitian3) : ComplexMatrix3) := by
    intro u w
    rw [hermJordanMul_mkHermDyad, smul_smul]
    norm_num
  let b := cInner v₁ v₂ * cInner v₂ v₃ * cInner v₃ v₁
  have hb_val : b = (B₀ : ℂ) * ((B₀ * C₀ : ℂ) + (B₁ : ℂ) * z) * (C₀ : ℂ) := by
    dsimp only [b]
    rw [hg12_val, hg23_val, ← cInner_conj v₁ v₃, hg13_val]
    simp
  have hbim_ne : b.im ≠ 0 := by
    rw [hb_val]
    have him : ((B₀ : ℂ) * ((B₀ * C₀ : ℂ) + (B₁ : ℂ) * z) * (C₀ : ℂ)).im = B₀ * B₁ * C₀ * C₂ := by
      simp [z, Complex.mul_im]; ring
    rw [him]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hB0 hB1) hC0) hC2
  let n₁₂ := (cInner v₁ v₂ * cInner v₂ v₁).re
  let n₁₃ := (cInner v₁ v₃ * cInner v₃ v₁).re
  let n₂₃ := (cInner v₂ v₃ * cInner v₃ v₂).re
  have hn12_pos : n₁₂ ≠ 0 := by
    dsimp only [n₁₂]; rw [hg12_val, ← cInner_conj v₁ v₂, hg12_val]; simp [hB0]
  have hn13_pos : n₁₃ ≠ 0 := by
    dsimp only [n₁₃]; rw [hg13_val, ← cInner_conj v₁ v₃, hg13_val]; simp [hC0]
  have hn23_pos : n₂₃ ≠ 0 := by
    dsimp only [n₂₃]; rw [← cInner_conj v₂ v₃, hg23_val]
    have hval : (((B₀ * C₀ : ℂ) + (B₁ : ℂ) * z) * star ((B₀ * C₀ : ℂ) + (B₁ : ℂ) * z)).re =
        (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 := by
      simp [z, Complex.mul_re]; ring
    rw [hval]
    intro h0
    have hbc2 : (B₁ * C₂) ^ 2 = 0 := by nlinarith [sq_nonneg (B₀ * C₀ + B₁ * C₁)]
    exact (mul_ne_zero hB1 hC2) (sq_eq_zero_iff.mp hbc2)
  have hK_opp : ∀ u w : Fin 3 → ℂ, Kmat w u = - Kmat u w := fun u w => by
    ext a b; simp [Kmat]; ring
  have hH_sym : ∀ u w : Fin 3 → ℂ, Hmat w u = Hmat u w := fun u w => by
    ext a b; simp [Hmat]; ring
  have ht3 : (n₁₃ * n₂₃ * 4 : ℝ) •
      (((hermJordanMul (hermJordanMul (mkHermDyad v₁) (mkHermDyad v₂))
        (mkHermDyad v₃) : Hermitian3) : ComplexMatrix3)) =
      (n₂₃ * b.re) • Hmat v₁ v₃ + (n₁₃ * b.re) • Hmat v₂ v₃ -
        (n₂₃ * b.im) • Kmat v₃ v₁ - (n₁₃ * b.im) • Kmat v₂ v₃ :=
    triple_jordan_formula v₁ v₂ v₃
  have ht1 : (n₁₂ * n₁₃ * 4 : ℝ) •
      (((hermJordanMul (hermJordanMul (mkHermDyad v₂) (mkHermDyad v₃))
        (mkHermDyad v₁) : Hermitian3) : ComplexMatrix3)) =
      (n₁₃ * b.re) • Hmat v₂ v₁ + (n₁₂ * b.re) • Hmat v₃ v₁ -
        (n₁₃ * b.im) • Kmat v₁ v₂ - (n₁₂ * b.im) • Kmat v₃ v₁ := by
    have h := triple_jordan_formula v₂ v₃ v₁
    have hbc : cInner v₂ v₃ * cInner v₃ v₁ * cInner v₁ v₂ = b := by dsimp [b]; ring
    have hn21 : (cInner v₂ v₁ * cInner v₁ v₂).re = n₁₂ := by dsimp [n₁₂]; rw [mul_comm]
    dsimp only at h
    rw [hbc, hn21, show (cInner v₃ v₁ * cInner v₁ v₃).re = n₁₃ by dsimp [n₁₃]; rw [mul_comm]] at h
    simpa [mul_comm n₁₂ n₁₃] using h
  have ht2 : (n₂₃ * n₁₂ * 4 : ℝ) •
      (((hermJordanMul (hermJordanMul (mkHermDyad v₃) (mkHermDyad v₁))
        (mkHermDyad v₂) : Hermitian3) : ComplexMatrix3)) =
      (n₁₂ * b.re) • Hmat v₃ v₂ + (n₂₃ * b.re) • Hmat v₁ v₂ -
        (n₁₂ * b.im) • Kmat v₂ v₃ - (n₂₃ * b.im) • Kmat v₁ v₂ := by
    have h := triple_jordan_formula v₃ v₁ v₂
    have hbc : cInner v₃ v₁ * cInner v₁ v₂ * cInner v₂ v₃ = b := by dsimp [b]; ring
    have hn32 : (cInner v₃ v₂ * cInner v₂ v₃).re = n₂₃ := by dsimp [n₂₃]; rw [mul_comm]
    dsimp only at h
    rw [hbc, hn32] at h
    exact h
  have hT3_eq : (b.im : ℝ) • (-n₁₃⁻¹ • Kmat v₁ v₃ + n₂₃⁻¹ • Kmat v₂ v₃) =
      (b.re * n₁₃⁻¹ : ℝ) • Hmat v₁ v₃ + (b.re * n₂₃⁻¹ : ℝ) • Hmat v₂ v₃ -
        (4 : ℝ) • (((hermJordanMul (hermJordanMul (mkHermDyad v₁) (mkHermDyad v₂))
          (mkHermDyad v₃) : Hermitian3) : ComplexMatrix3)) := by
    have hs := congrArg ((n₁₃ * n₂₃)⁻¹ • ·) ht3
    rw [smul_smul, show (n₁₃ * n₂₃)⁻¹ * (n₁₃ * n₂₃ * 4) = 4 by field_simp [hn13_pos, hn23_pos]] at hs
    rw [hs, hK_opp v₃ v₁]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
      Complex.real_smul]
    push_cast
    field_simp [hn13_pos, hn23_pos]
    ring
  have hT1_eq : (b.im : ℝ) • (n₁₂⁻¹ • Kmat v₁ v₂ - n₁₃⁻¹ • Kmat v₁ v₃) =
      (b.re * n₁₃⁻¹ : ℝ) • Hmat v₁ v₃ + (b.re * n₁₂⁻¹ : ℝ) • Hmat v₁ v₂ -
        (4 : ℝ) • (((hermJordanMul (hermJordanMul (mkHermDyad v₂) (mkHermDyad v₃))
          (mkHermDyad v₁) : Hermitian3) : ComplexMatrix3)) := by
    have hs := congrArg ((n₁₂ * n₁₃)⁻¹ • ·) ht1
    rw [smul_smul, show (n₁₂ * n₁₃)⁻¹ * (n₁₂ * n₁₃ * 4) = 4 by field_simp [hn12_pos, hn13_pos]] at hs
    rw [hs, hK_opp v₃ v₁, hH_sym v₂ v₁, hH_sym v₃ v₁]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
      Complex.real_smul]
    push_cast
    field_simp [hn12_pos, hn13_pos]
    ring
  have hT2_eq : (b.im : ℝ) • (n₁₂⁻¹ • Kmat v₁ v₂ + n₂₃⁻¹ • Kmat v₂ v₃) =
      (b.re * n₁₂⁻¹ : ℝ) • Hmat v₁ v₂ + (b.re * n₂₃⁻¹ : ℝ) • Hmat v₂ v₃ -
        (4 : ℝ) • (((hermJordanMul (hermJordanMul (mkHermDyad v₃) (mkHermDyad v₁))
          (mkHermDyad v₂) : Hermitian3) : ComplexMatrix3)) := by
    have hs := congrArg ((n₂₃ * n₁₂)⁻¹ • ·) ht2
    rw [smul_smul, show (n₂₃ * n₁₂)⁻¹ * (n₂₃ * n₁₂ * 4) = 4 by field_simp [hn12_pos, hn23_pos]] at hs
    rw [hs, hH_sym v₃ v₂]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul]
    push_cast
    field_simp [hn12_pos, hn23_pos]
    ring
  let S := stdBasisHerm B₀ B₁ C₀ C₁ C₂ C₃
  have hS6 : S 6 = hermJordanMul (hermJordanMul (mkHermDyad v₁) (mkHermDyad v₂)) (mkHermDyad v₃) := rfl
  have hS7 : S 7 = hermJordanMul (hermJordanMul (mkHermDyad v₂) (mkHermDyad v₃)) (mkHermDyad v₁) := rfl
  have hS8 : S 8 = hermJordanMul (hermJordanMul (mkHermDyad v₃) (mkHermDyad v₁)) (mkHermDyad v₂) := rfl
  let T3 : ComplexMatrix3 :=
    (b.re * n₁₃⁻¹ : ℝ) • Hmat v₁ v₃ + (b.re * n₂₃⁻¹ : ℝ) • Hmat v₂ v₃ - (4 : ℝ) • ((S 6 : Hermitian3) : ComplexMatrix3)
  let T1 : ComplexMatrix3 :=
    (b.re * n₁₃⁻¹ : ℝ) • Hmat v₁ v₃ + (b.re * n₁₂⁻¹ : ℝ) • Hmat v₁ v₂ - (4 : ℝ) • ((S 7 : Hermitian3) : ComplexMatrix3)
  let T2 : ComplexMatrix3 :=
    (b.re * n₁₂⁻¹ : ℝ) • Hmat v₁ v₂ + (b.re * n₂₃⁻¹ : ℝ) • Hmat v₂ v₃ - (4 : ℝ) • ((S 8 : Hermitian3) : ComplexMatrix3)
  have hK12 : Kmat v₁ v₂ = (n₁₂ / (2 * b.im) : ℝ) • (T1 + T2 - T3) := by
    have hT : T1 + T2 - T3 = (2 * b.im * n₁₂⁻¹ : ℝ) • Kmat v₁ v₂ := by
      dsimp only [T1, T2, T3]
      rw [hS6, hS7, hS8, ← hT1_eq, ← hT2_eq, ← hT3_eq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
      push_cast
      ring
    rw [hT, smul_smul]
    have hcoeff : (n₁₂ / (2 * b.im)) * (2 * b.im * n₁₂⁻¹) = 1 := by
      field_simp [hbim_ne, hn12_pos]
    rw [hcoeff, one_smul]
  have hK13 : Kmat v₁ v₃ = (n₁₃ / (2 * b.im) : ℝ) • (T2 - T1 - T3) := by
    have hT : T2 - T1 - T3 = (2 * b.im * n₁₃⁻¹ : ℝ) • Kmat v₁ v₃ := by
      dsimp only [T1, T2, T3]
      rw [hS6, hS7, hS8, ← hT1_eq, ← hT2_eq, ← hT3_eq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
      push_cast
      ring
    rw [hT, smul_smul]
    have hcoeff : (n₁₃ / (2 * b.im)) * (2 * b.im * n₁₃⁻¹) = 1 := by
      field_simp [hbim_ne, hn13_pos]
    rw [hcoeff, one_smul]
  have hK23 : Kmat v₂ v₃ = (n₂₃ / (2 * b.im) : ℝ) • (T2 + T3 - T1) := by
    have hT : T2 + T3 - T1 = (2 * b.im * n₂₃⁻¹ : ℝ) • Kmat v₂ v₃ := by
      dsimp only [T1, T2, T3]
      rw [hS6, hS7, hS8, ← hT1_eq, ← hT2_eq, ← hT3_eq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
      push_cast
      ring
    rw [hT, smul_smul]
    have hcoeff : (n₂₃ / (2 * b.im)) * (2 * b.im * n₂₃⁻¹) = 1 := by
      field_simp [hbim_ne, hn23_pos]
    rw [hcoeff, one_smul]
  let α12 := (N 0 1 / cInner v₁ v₂).re
  let β12 := (N 0 1 / cInner v₁ v₂).im
  let α13 := (N 0 2 / cInner v₁ v₃).re
  let β13 := (N 0 2 / cInner v₁ v₃).im
  let α23 := (N 1 2 / cInner v₂ v₃).re
  let β23 := (N 1 2 / cInner v₂ v₃).im
  let k12 := β12 * (n₁₂ / (2 * b.im))
  let k13 := β13 * (n₁₃ / (2 * b.im))
  let k23 := β23 * (n₂₃ / (2 * b.im))
  let c0 := (N 0 0).re
  let c1 := (N 1 1).re
  let c2 := (N 2 2).re
  let c3 := 2 * (α12 + 2 * k12 * (b.re * n₁₂⁻¹))
  let c4 := 2 * (α13 - 2 * k13 * (b.re * n₁₃⁻¹))
  let c5 := 2 * (α23 + 2 * k23 * (b.re * n₂₃⁻¹))
  let c6 := 4 * (k12 + k13 - k23)
  let c7 := 4 * (-k12 + k13 + k23)
  let c8 := -4 * (k12 + k13 + k23)
  refine ⟨fun k => match k.val with
    | 0 => c0
    | 1 => c1
    | 2 => c2
    | 3 => c3
    | 4 => c4
    | 5 => c5
    | 6 => c6
    | 7 => c7
    | _ => c8, ?_⟩
  apply Subtype.ext
  rw [hM_sum, hK12, hK13, hK23]
  have hS3 : Hmat v₁ v₂ = (2 : ℝ) • ((S 3 : Hermitian3) : ComplexMatrix3) := hH_span v₁ v₂
  have hS4 : Hmat v₁ v₃ = (2 : ℝ) • ((S 4 : Hermitian3) : ComplexMatrix3) := hH_span v₁ v₃
  have hS5 : Hmat v₂ v₃ = (2 : ℝ) • ((S 5 : Hermitian3) : ComplexMatrix3) := hH_span v₂ v₃
  rw [fin_sum_univ_nine]
  simp only [AddSubgroup.coe_add]
  change _ = c0 • ((mkHermDyad v₁ : Hermitian3) : ComplexMatrix3) +
    c1 • ((mkHermDyad v₂ : Hermitian3) : ComplexMatrix3) +
    c2 • ((mkHermDyad v₃ : Hermitian3) : ComplexMatrix3) +
    c3 • ((S 3 : Hermitian3) : ComplexMatrix3) +
    c4 • ((S 4 : Hermitian3) : ComplexMatrix3) +
    c5 • ((S 5 : Hermitian3) : ComplexMatrix3) +
    c6 • ((S 6 : Hermitian3) : ComplexMatrix3) +
    c7 • ((S 7 : Hermitian3) : ComplexMatrix3) +
    c8 • ((S 8 : Hermitian3) : ComplexMatrix3)
  dsimp only [T1, T2, T3]
  rw [hS3, hS4, hS5]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
  dsimp only [α12, β12, α13, β13, α23, β23, k12, k13, k23, c0, c1, c2, c3, c4, c5, c6, c7, c8]
  push_cast
  ring

/-! ## Section 4: Complex-Triple Canonicalization & Equivariant Trace Affinity -/

private theorem octNormSq_zero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl

private theorem octNormSq_scalar (r : ℝ) : octNormSq (octonionScalar r) = r ^ 2 := by
  rw [octNormSq_eq_coords]; simp [octonionScalar]

private theorem oct_fst_zero : (0 : Octonion).1 = 0 := rfl
private theorem oct_snd_zero : (0 : Octonion).2 = 0 := rfl

private theorem oct_add_re (x y : Octonion) : (x + y).1.re = x.1.re + y.1.re := rfl
private theorem oct_add_imI (x y : Octonion) : (x + y).1.imI = x.1.imI + y.1.imI := rfl
private theorem oct_add_imJ (x y : Octonion) : (x + y).1.imJ = x.1.imJ + y.1.imJ := rfl
private theorem oct_add_imK (x y : Octonion) : (x + y).1.imK = x.1.imK + y.1.imK := rfl
private theorem oct_add_s_re (x y : Octonion) : (x + y).2.re = x.2.re + y.2.re := rfl
private theorem oct_add_s_imI (x y : Octonion) : (x + y).2.imI = x.2.imI + y.2.imI := rfl
private theorem oct_add_s_imJ (x y : Octonion) : (x + y).2.imJ = x.2.imJ + y.2.imJ := rfl
private theorem oct_add_s_imK (x y : Octonion) : (x + y).2.imK = x.2.imK + y.2.imK := rfl
private theorem oct_smul_re (r : ℝ) (x : Octonion) : (r • x).1.re = r * x.1.re := rfl
private theorem oct_smul_imI (r : ℝ) (x : Octonion) : (r • x).1.imI = r * x.1.imI := rfl
private theorem oct_smul_imJ (r : ℝ) (x : Octonion) : (r • x).1.imJ = r * x.1.imJ := rfl
private theorem oct_smul_imK (r : ℝ) (x : Octonion) : (r • x).1.imK = r * x.1.imK := rfl
private theorem oct_smul_s_re (r : ℝ) (x : Octonion) : (r • x).2.re = r * x.2.re := rfl
private theorem oct_smul_s_imI (r : ℝ) (x : Octonion) : (r • x).2.imI = r * x.2.imI := rfl
private theorem oct_smul_s_imJ (r : ℝ) (x : Octonion) : (r • x).2.imJ = r * x.2.imJ := rfl
private theorem oct_smul_s_imK (r : ℝ) (x : Octonion) : (r • x).2.imK = r * x.2.imK := rfl

private theorem oct_scalar_add_smul_I (a b : ℝ) :
    octonionScalar a + b • octI = ({ re := a, imI := b, imJ := 0, imK := 0 }, 0) := by
  apply oct_ext <;>
    (simp only [oct_add_re, oct_add_imI, oct_add_imJ, oct_add_imK,
      oct_add_s_re, oct_add_s_imI, oct_add_s_imJ, oct_add_s_imK,
      oct_smul_re, oct_smul_imI, oct_smul_imJ, oct_smul_imK,
      oct_smul_s_re, oct_smul_s_imI, oct_smul_s_imJ, oct_smul_s_imK];
     simp [octonionScalar, octI])

private def stdAtom0 : Albert := diagAtom 0

private def stdAtom1 (B₀ B₁ : ℝ) : Albert :=
  octDyad ![octonionScalar B₀, octonionScalar B₁, 0]

private def stdAtom2 (C₀ C₁ C₂ C₃ : ℝ) : Albert :=
  octDyad ![octonionScalar C₀, octonionScalar C₁ + C₂ • octI, octonionScalar C₃]

private theorem standardComplexWindow_embedding_apply (M : Hermitian3) :
    standardComplexWindow.embedding M = complexHermToAlbert M := rfl

private theorem stdAtom0_eq_mkHermDyad :
    standardComplexWindow.embedding (mkHermDyad ![1, 0, 0]) = stdAtom0 := by
  rw [standardComplexWindow_embedding_apply]
  apply albert_ext
  · simp [complexHermToAlbert, mkHermDyad, stdAtom0, diagAtom]
  · simp [complexHermToAlbert, mkHermDyad, stdAtom0, diagAtom]
  · simp [complexHermToAlbert, mkHermDyad, stdAtom0, diagAtom]
  · apply oct_ext <;> simp [complexHermToAlbert, complexToOctonion_apply, mkHermDyad, stdAtom0,
      diagAtom, oct_fst_zero, oct_snd_zero]
  · apply oct_ext <;> simp [complexHermToAlbert, complexToOctonion_apply, mkHermDyad, stdAtom0,
      diagAtom, oct_fst_zero, oct_snd_zero]
  · apply oct_ext <;> simp [complexHermToAlbert, complexToOctonion_apply, mkHermDyad, stdAtom0,
      diagAtom, oct_fst_zero, oct_snd_zero]

private theorem stdAtom1_eq_mkHermDyad (B₀ B₁ : ℝ) :
    standardComplexWindow.embedding (mkHermDyad ![B₀, B₁, 0]) = stdAtom1 B₀ B₁ := by
  rw [standardComplexWindow_embedding_apply]
  apply albert_ext
  · simp [complexHermToAlbert, mkHermDyad, stdAtom1, octDyad, octNormSq_scalar]; ring
  · simp [complexHermToAlbert, mkHermDyad, stdAtom1, octDyad, octNormSq_scalar]; ring
  · simp [complexHermToAlbert, mkHermDyad, stdAtom1, octDyad, octNormSq_zero]
  · apply oct_ext <;> (simp [complexHermToAlbert, mkHermDyad, stdAtom1, octDyad,
      complexToOctonion_apply, octonionMul, octonionConj, octonionScalar,
      oct_fst_zero, oct_snd_zero]; try ring)
  · apply oct_ext <;> simp [complexHermToAlbert, mkHermDyad, stdAtom1, octDyad,
      complexToOctonion_apply, octonionConj_zero, octonionMul_zero_right,
      oct_fst_zero, oct_snd_zero]
  · apply oct_ext <;> simp [complexHermToAlbert, mkHermDyad, stdAtom1, octDyad,
      complexToOctonion_apply, octonionConj_zero, octonionMul_zero_right,
      oct_fst_zero, oct_snd_zero]

private theorem stdAtom2_eq_mkHermDyad (C₀ C₁ C₂ C₃ : ℝ) :
    standardComplexWindow.embedding (mkHermDyad ![C₀, ⟨C₁, C₂⟩, C₃]) =
      stdAtom2 C₀ C₁ C₂ C₃ := by
  rw [standardComplexWindow_embedding_apply]
  dsimp only [stdAtom2]
  rw [oct_scalar_add_smul_I]
  apply albert_ext
  · simp [complexHermToAlbert, mkHermDyad, octDyad, octNormSq_scalar]; ring
  · simp [complexHermToAlbert, mkHermDyad, octDyad, octNormSq_eq_coords, Complex.mul_re]; ring
  · simp [complexHermToAlbert, mkHermDyad, octDyad, octNormSq_scalar]; ring
  · apply oct_ext <;> (simp [complexHermToAlbert, mkHermDyad, octDyad, complexToOctonion_apply,
      octonionMul, octonionConj, octonionScalar, Complex.mul_re, Complex.mul_im]; try ring)
  · apply oct_ext <;> (simp [complexHermToAlbert, mkHermDyad, octDyad, complexToOctonion_apply,
      octonionMul, octonionConj, octonionScalar, Complex.mul_re, Complex.mul_im]; try ring)
  · apply oct_ext <;> (simp [complexHermToAlbert, mkHermDyad, octDyad, complexToOctonion_apply,
      octonionMul, octonionConj, octonionScalar, Complex.mul_re, Complex.mul_im]; try ring)

private def stdBasisAlbert (x y z : Albert) (k : Fin 9) : Albert :=
  match k.val with
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => jordanMul x y
  | 4 => jordanMul x z
  | 5 => jordanMul y z
  | 6 => jordanMul (jordanMul x y) z
  | 7 => jordanMul (jordanMul y z) x
  | _ => jordanMul (jordanMul z x) y

private theorem stdBasisAlbert_std (B₀ B₁ C₀ C₁ C₂ C₃ : ℝ) (k : Fin 9) :
    stdBasisAlbert stdAtom0 (stdAtom1 B₀ B₁) (stdAtom2 C₀ C₁ C₂ C₃) k =
      standardComplexWindow.embedding (stdBasisHerm B₀ B₁ C₀ C₁ C₂ C₃ k) := by
  fin_cases k <;>
    simp only [stdBasisAlbert, stdBasisHerm, standardComplexWindow_hermJordanMul,
      stdAtom0_eq_mkHermDyad, stdAtom1_eq_mkHermDyad, stdAtom2_eq_mkHermDyad]

private theorem stdBasisAlbert_map (g : NativeAlbertAutomorphism) (x y z : Albert) (k : Fin 9) :
    g.linearEquiv (stdBasisAlbert x y z k) =
      stdBasisAlbert (g.linearEquiv x) (g.linearEquiv y) (g.linearEquiv z) k := by
  fin_cases k <;>
    simp [stdBasisAlbert, g.preserves_product]

private theorem standardComplexWindow_tracePairing (M N : Hermitian3) :
    tracePairing (standardComplexWindow.embedding M) (standardComplexWindow.embedding N) =
      (Matrix.trace ((M : ComplexMatrix3) * (N : ComplexMatrix3))).re := by
  rw [← windowProj_embedding standardComplexWindow M, windowProj_tracePairing,
    windowProj_embedding]

private theorem trace_mkHermDyad (u w : Fin 3 → ℂ) :
    (Matrix.trace (((mkHermDyad u : Hermitian3) : ComplexMatrix3) *
      ((mkHermDyad w : Hermitian3) : ComplexMatrix3))).re =
      (cInner u w * cInner w u).re := by
  have h : Matrix.trace (((mkHermDyad u : Hermitian3) : ComplexMatrix3) *
      ((mkHermDyad w : Hermitian3) : ComplexMatrix3)) = cInner u w * cInner w u := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, mkHermDyad, Matrix.of_apply,
      cInner, Fin.sum_univ_three]
    ring
  rw [h]

private theorem trace_mkHermDyad_hermJordanMul (u₀ u₁ u₂ : Fin 3 → ℂ) :
    (Matrix.trace (((mkHermDyad u₀ : Hermitian3) : ComplexMatrix3) *
      ((hermJordanMul (mkHermDyad u₁) (mkHermDyad u₂) : Hermitian3) : ComplexMatrix3))).re =
      (cInner u₀ u₁ * cInner u₁ u₂ * cInner u₂ u₀).re := by
  have h : Matrix.trace (((mkHermDyad u₀ : Hermitian3) : ComplexMatrix3) *
      ((hermJordanMul (mkHermDyad u₁) (mkHermDyad u₂) : Hermitian3) : ComplexMatrix3)) =
      (1 / 2 : ℂ) * (cInner u₀ u₁ * cInner u₁ u₂ * cInner u₂ u₀ +
        cInner u₀ u₂ * cInner u₂ u₁ * cInner u₁ u₀) := by
    rw [hermJordanMul_mkHermDyad]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.smul_apply,
      Complex.real_smul, mkHermDyad, Hmat, Matrix.of_apply, cInner, Fin.sum_univ_three]
    push_cast
    ring
  have hconj : star (cInner u₀ u₁ * cInner u₁ u₂ * cInner u₂ u₀) =
      cInner u₀ u₂ * cInner u₂ u₁ * cInner u₁ u₀ := by
    rw [star_mul, star_mul, cInner_conj, cInner_conj, cInner_conj]
    ring
  rw [h, ← hconj, ← complex_re_mul_two]
  have hhalf : (1 / 2 : ℂ) * ((2 : ℂ) * ((cInner u₀ u₁ * cInner u₁ u₂ * cInner u₂ u₀).re : ℂ)) =
      ((cInner u₀ u₁ * cInner u₁ u₂ * cInner u₂ u₀).re : ℂ) := by ring
  rw [hhalf, Complex.ofReal_re]

private theorem stdAtoms_traces (B₀ B₁ C₀ C₁ C₂ C₃ : ℝ) :
    tracePairing stdAtom0 (stdAtom1 B₀ B₁) = B₀ ^ 2 ∧
    tracePairing stdAtom0 (stdAtom2 C₀ C₁ C₂ C₃) = C₀ ^ 2 ∧
    tracePairing (stdAtom1 B₀ B₁) (stdAtom2 C₀ C₁ C₂ C₃) =
      (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 ∧
    tracePairing stdAtom0 (jordanMul (stdAtom1 B₀ B₁) (stdAtom2 C₀ C₁ C₂ C₃)) =
      B₀ * C₀ * (B₀ * C₀ + B₁ * C₁) ∧
    tripleDelta stdAtom0 (stdAtom1 B₀ B₁) (stdAtom2 C₀ C₁ C₂ C₃) =
      B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by
  have ho01 : tracePairing stdAtom0 (stdAtom1 B₀ B₁) = B₀ ^ 2 := by
    rw [← stdAtom0_eq_mkHermDyad, ← stdAtom1_eq_mkHermDyad, standardComplexWindow_tracePairing,
      trace_mkHermDyad]
    simp [cInner, Fin.sum_univ_three, Complex.mul_re]
    ring
  have ho02 : tracePairing stdAtom0 (stdAtom2 C₀ C₁ C₂ C₃) = C₀ ^ 2 := by
    rw [← stdAtom0_eq_mkHermDyad, ← stdAtom2_eq_mkHermDyad, standardComplexWindow_tracePairing,
      trace_mkHermDyad]
    simp [cInner, Fin.sum_univ_three, Complex.mul_re]
    ring
  have ho12 : tracePairing (stdAtom1 B₀ B₁) (stdAtom2 C₀ C₁ C₂ C₃) =
      (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 := by
    rw [← stdAtom1_eq_mkHermDyad, ← stdAtom2_eq_mkHermDyad, standardComplexWindow_tracePairing,
      trace_mkHermDyad]
    simp [cInner, Fin.sum_univ_three, Complex.mul_re]
    ring
  have hR012 : tracePairing stdAtom0 (jordanMul (stdAtom1 B₀ B₁) (stdAtom2 C₀ C₁ C₂ C₃)) =
      B₀ * C₀ * (B₀ * C₀ + B₁ * C₁) := by
    rw [← stdAtom0_eq_mkHermDyad, ← stdAtom1_eq_mkHermDyad, ← stdAtom2_eq_mkHermDyad,
      ← standardComplexWindow_hermJordanMul, standardComplexWindow_tracePairing,
      trace_mkHermDyad_hermJordanMul]
    simp [cInner, Fin.sum_univ_three, Complex.mul_re]
    ring
  have hcub : albertCubicNorm (stdAtom0 + stdAtom1 B₀ B₁ + stdAtom2 C₀ C₁ C₂ C₃) =
      B₁ ^ 2 * C₃ ^ 2 := by
    rw [← stdAtom0_eq_mkHermDyad, ← stdAtom1_eq_mkHermDyad, ← stdAtom2_eq_mkHermDyad,
      ← map_add, ← map_add, (standardComplexWindow_albertCubicNorm_eq_det _).1]
    let T : ComplexMatrix3 :=
      Matrix.of ![![1, (B₀ : ℂ), (C₀ : ℂ)], ![0, (B₁ : ℂ), ⟨C₁, C₂⟩], ![0, 0, (C₃ : ℂ)]]
    have hsum_eq :
        ((mkHermDyad ![1, 0, 0] + mkHermDyad ![B₀, B₁, 0] +
            mkHermDyad ![C₀, ⟨C₁, C₂⟩, C₃] : Hermitian3) : ComplexMatrix3) =
          T * T.conjTranspose := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [T, mkHermDyad, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three]
    have hdetT : T.det = ((B₁ * C₃ : ℝ) : ℂ) := by
      rw [Matrix.det_fin_three]
      simp [T]
    change ((((mkHermDyad ![1, 0, 0] + mkHermDyad ![B₀, B₁, 0] +
        mkHermDyad ![C₀, ⟨C₁, C₂⟩, C₃] : Hermitian3) : ComplexMatrix3)).det).re = _
    rw [hsum_eq, Matrix.det_mul, Matrix.det_conjTranspose, hdetT]
    simp [Complex.mul_re]
    ring
  have hdel : tripleDelta stdAtom0 (stdAtom1 B₀ B₁) (stdAtom2 C₀ C₁ C₂ C₃) =
      B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by
    unfold tripleDelta
    rw [hcub, ho01, ho02, ho12, hR012]
    ring
  exact ⟨ho01, ho02, ho12, hR012, hdel⟩

private theorem triple_canonical_pair {p q : Fin 4 → Albert}
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i))
    (ho : ∀ i j, fpOverlap p i j = fpOverlap q i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle q i j k)
    {x y z : Fin 4} (hΔ : tripleDelta (p x) (p y) (p z) ≠ 0) :
    ∃ (B₀ B₁ C₀ C₁ C₂ C₃ : ℝ) (g_p g_q : NativeAlbertAutomorphism),
      0 < B₀ ∧ 0 < B₁ ∧ 0 < C₀ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      g_p.linearEquiv (p x) = stdAtom0 ∧
      g_p.linearEquiv (p y) = stdAtom1 B₀ B₁ ∧
      g_p.linearEquiv (p z) = stdAtom2 C₀ C₁ C₂ C₃ ∧
      g_q.linearEquiv (q x) = stdAtom0 ∧
      g_q.linearEquiv (q y) = stdAtom1 B₀ B₁ ∧
      g_q.linearEquiv (q z) = stdAtom2 C₀ C₁ C₂ C₃ := by
  have hΔq : tripleDelta (q x) (q y) (q z) ≠ 0 := by
    rw [tripleDelta_eq_of_traces_eq hp hq ho hR x y z]
    exact hΔ
  obtain ⟨_, hpxy, hpxz, _hpyz, _⟩ := lemma_A_window_generated (hp x) (hp y) (hp z) hΔ
  obtain ⟨_, hqxy, hqxz, _hqyz, _⟩ := lemma_A_window_generated (hq x) (hq y) (hq z) hΔq
  obtain ⟨gp, B₀, B₁, C₀, C₁, C₂, C₃, _D0p, _x0p, _x1p, _x2p, _y0p, _y1p, _y2p, _y3p, _y4p,
    hB0p, hB1p, hC0p, hC2p, hC3p, _hD0p, _hx2p, _hy4p, hBsp, hCsp, _hDsp, hcfgp⟩ :=
    lemma_A_normal ![p x, p y, p z, p x]
      (fun i => by fin_cases i <;> [exact hp x; exact hp y; exact hp z; exact hp x])
      hpxy.1 hpxy.2 hpxz.1 (by show 0 < tracePairing (p x) (p x); rw [tracePairing_atom_self (hp x)]; norm_num)
  obtain ⟨gq, B₀', B₁', C₀', C₁', C₂', C₃', _D0q, _x0q, _x1q, _x2q, _y0q, _y1q, _y2q, _y3q, _y4q,
    hB0q, hB1q, hC0q, hC2q, hC3q, _hD0q, _hx2q, _hy4q, hBsq, hCsq, _hDsq, hcfgq⟩ :=
    lemma_A_normal ![q x, q y, q z, q x]
      (fun i => by fin_cases i <;> [exact hq x; exact hq y; exact hq z; exact hq x])
      hqxy.1 hqxy.2 hqxz.1 (by show 0 < tracePairing (q x) (q x); rw [tracePairing_atom_self (hq x)]; norm_num)
  have hgp0 : gp.linearEquiv (p x) = stdAtom0 := by
    have h := congrFun hcfgp 0
    change gp.linearEquiv (p x) = sparseFourConfig _ _ _ _ _ _ _ _ _ _ _ 0 at h
    rw [h]
    apply albert_ext <;> simp [sparseFourConfig, sparseFourConfigOct, stdAtom0, diagAtom, octDyad,
      octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
  have hgp1 : gp.linearEquiv (p y) = stdAtom1 B₀ B₁ := congrFun hcfgp 1
  have hgp2 : gp.linearEquiv (p z) = stdAtom2 C₀ C₁ C₂ C₃ := congrFun hcfgp 2
  have hgq0 : gq.linearEquiv (q x) = stdAtom0 := by
    have h := congrFun hcfgq 0
    change gq.linearEquiv (q x) = sparseFourConfig _ _ _ _ _ _ _ _ _ _ _ 0 at h
    rw [h]
    apply albert_ext <;> simp [sparseFourConfig, sparseFourConfigOct, stdAtom0, diagAtom, octDyad,
      octNormSq_scalar, octNormSq_zero, octonionConj_zero, octonionMul_zero_right]
  have hgq1 : gq.linearEquiv (q y) = stdAtom1 B₀' B₁' := congrFun hcfgq 1
  have hgq2 : gq.linearEquiv (q z) = stdAtom2 C₀' C₁' C₂' C₃' := congrFun hcfgq 2
  have htp := stdAtoms_traces B₀ B₁ C₀ C₁ C₂ C₃
  have htq := stdAtoms_traces B₀' B₁' C₀' C₁' C₂' C₃'
  have hdel_p : tripleDelta (p x) (p y) (p z) = B₀ ^ 2 * B₁ ^ 4 * C₀ ^ 2 * C₂ ^ 2 * C₃ ^ 2 := by
    rw [← tripleDelta_automorphism gp (p x) (p y) (p z), hgp0, hgp1, hgp2]
    exact htp.2.2.2.2
  have hC2_pos : 0 < C₂ := by
    refine lt_of_le_of_ne hC2p (Ne.symm fun h => ?_)
    rw [h] at hdel_p; ring_nf at hdel_p; exact hΔ hdel_p
  have hC3_pos : 0 < C₃ := by
    refine lt_of_le_of_ne hC3p (Ne.symm fun h => ?_)
    rw [h] at hdel_p; ring_nf at hdel_p; exact hΔ hdel_p
  have ho01_eq : B₀' ^ 2 = B₀ ^ 2 := by
    have hp1 : tracePairing (p x) (p y) = B₀ ^ 2 := by
      rw [← gp.map_tracePairing, hgp0, hgp1]; exact htp.1
    have hq1 : tracePairing (q x) (q y) = B₀' ^ 2 := by
      rw [← gq.map_tracePairing, hgq0, hgq1]; exact htq.1
    have ho1 : tracePairing (p x) (p y) = tracePairing (q x) (q y) := ho x y
    linarith
  have hB0_eq : B₀' = B₀ := (sq_eq_sq₀ hB0q.le hB0p.le).mp ho01_eq
  have hB1_eq : B₁' = B₁ :=
    (sq_eq_sq₀ hB1q.le hB1p.le).mp (by linarith [hBsp, hBsq, ho01_eq])
  have ho02_eq : C₀' ^ 2 = C₀ ^ 2 := by
    have hp2 : tracePairing (p x) (p z) = C₀ ^ 2 := by
      rw [← gp.map_tracePairing, hgp0, hgp2]; exact htp.2.1
    have hq2 : tracePairing (q x) (q z) = C₀' ^ 2 := by
      rw [← gq.map_tracePairing, hgq0, hgq2]; exact htq.2.1
    have ho2 : tracePairing (p x) (p z) = tracePairing (q x) (q z) := ho x z
    linarith
  have hC0_eq : C₀' = C₀ := (sq_eq_sq₀ hC0q.le hC0p.le).mp ho02_eq
  have hR_eq : B₀ * C₀ * (B₀ * C₀ + B₁ * C₁') = B₀ * C₀ * (B₀ * C₀ + B₁ * C₁) := by
    have hpR : tracePairing (p x) (jordanMul (p y) (p z)) = B₀ * C₀ * (B₀ * C₀ + B₁ * C₁) := by
      rw [← gp.map_tracePairing, gp.preserves_product, hgp0, hgp1, hgp2]; exact htp.2.2.2.1
    have hqR : tracePairing (q x) (jordanMul (q y) (q z)) = B₀' * C₀' * (B₀' * C₀' + B₁' * C₁') := by
      rw [← gq.map_tracePairing, gq.preserves_product, hgq0, hgq1, hgq2]; exact htq.2.2.2.1
    have hRt : tracePairing (p x) (jordanMul (p y) (p z)) =
        tracePairing (q x) (jordanMul (q y) (q z)) := by
      have h := hR y z x
      unfold fpTriangle at h
      simpa only [tracePairing_comm] using h
    rw [hB0_eq, hB1_eq, hC0_eq] at hqR
    linarith
  have hC1_eq : C₁' = C₁ := by
    have hmul : (B₀ * C₀ * B₁) * (C₁' - C₁) = 0 := by linarith
    have hnz : B₀ * C₀ * B₁ ≠ 0 := mul_ne_zero (mul_ne_zero hB0p.ne' hC0p.ne') hB1p.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hnz)
  have ho12_eq : (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂') ^ 2 =
      (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 := by
    have hp12 : tracePairing (p y) (p z) = (B₀ * C₀ + B₁ * C₁) ^ 2 + (B₁ * C₂) ^ 2 := by
      rw [← gp.map_tracePairing, hgp1, hgp2]; exact htp.2.2.1
    have hq12 : tracePairing (q y) (q z) = (B₀' * C₀' + B₁' * C₁') ^ 2 + (B₁' * C₂') ^ 2 := by
      rw [← gq.map_tracePairing, hgq1, hgq2]; exact htq.2.2.1
    have ho12 : tracePairing (p y) (p z) = tracePairing (q y) (q z) := ho y z
    rw [hB0_eq, hB1_eq, hC0_eq, hC1_eq] at hq12
    linarith
  have hC2_eq : C₂' = C₂ := by
    have hsq : (B₁ * C₂') ^ 2 = (B₁ * C₂) ^ 2 := by linarith
    have hprod := (sq_eq_sq₀ (mul_nonneg hB1p.le hC2q) (mul_nonneg hB1p.le hC2p)).mp hsq
    exact mul_left_cancel₀ hB1p.ne' hprod
  have hC3_eq : C₃' = C₃ :=
    (sq_eq_sq₀ hC3q hC3p).mp (by rw [hC0_eq, hC1_eq, hC2_eq] at hCsq; linarith [hCsp, hCsq])
  rw [hB0_eq, hB1_eq] at hgq1
  rw [hC0_eq, hC1_eq, hC2_eq, hC3_eq] at hgq2
  exact ⟨B₀, B₁, C₀, C₁, C₂, C₃, gp, gq, hB0p, hB1p, hC0p, hC2_pos, hC3_pos,
    hgp0, hgp1, hgp2, hgq0, hgq1, hgq2⟩

private theorem triple_automorphism_of_traces_eq {p q : Fin 4 → Albert}
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i))
    (ho : ∀ i j, fpOverlap p i j = fpOverlap q i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle q i j k)
    {x y z : Fin 4} (hΔ : tripleDelta (p x) (p y) (p z) ≠ 0) :
    ∃ g : NativeAlbertAutomorphism,
      g.linearEquiv (p x) = q x ∧ g.linearEquiv (p y) = q y ∧ g.linearEquiv (p z) = q z := by
  obtain ⟨B₀, B₁, C₀, C₁, C₂, C₃, gp, gq, _, _, _, _, _,
    hpx, hpy, hpz, hqx, hqy, hqz⟩ := triple_canonical_pair hp hq ho hR hΔ
  refine ⟨gq.symm.comp gp, ?_, ?_, ?_⟩
  · change gq.linearEquiv.symm (gp.linearEquiv (p x)) = q x
    rw [hpx, ← hqx, gq.linearEquiv.symm_apply_apply]
  · change gq.linearEquiv.symm (gp.linearEquiv (p y)) = q y
    rw [hpy, ← hqy, gq.linearEquiv.symm_apply_apply]
  · change gq.linearEquiv.symm (gp.linearEquiv (p z)) = q z
    rw [hpz, ← hqz, gq.linearEquiv.symm_apply_apply]

private theorem unorderedPairClass_comm (a b : Fin 4) :
    unorderedPairClass a b = unorderedPairClass b a := by
  revert a b; decide

private theorem doublePair_of_distinct (q : Fin 4 → Albert) {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    tracePairing (jordanMul (q a) (q b)) (jordanMul (q c) (q d)) =
      match unorderedPairClass a b with
      | 0 => fpDoublePair1 q
      | 1 => fpDoublePair2 q
      | 2 => fpDoublePair3 q := by
  have hbase : ∀ a b c d : Fin 4, a < b → c < d → a < c → b ≠ c → b ≠ d →
      tracePairing (jordanMul (q a) (q b)) (jordanMul (q c) (q d)) =
        match unorderedPairClass a b with
        | 0 => fpDoublePair1 q
        | 1 => fpDoublePair2 q
        | 2 => fpDoublePair3 q := by
    intro a b c d hab' hcd' hac' hbc' hbd'
    have ha0 : a = 0 := Fin.ext (by
      have h1 : a.val < b.val := hab'
      have h2 : a.val < c.val := hac'
      have h3 : c.val < d.val := hcd'
      have h4 : b.val ≠ c.val := fun h => hbc' (Fin.ext h)
      have h5 : b.val ≠ d.val := fun h => hbd' (Fin.ext h)
      omega)
    subst ha0
    have hbv : b.val = 1 ∨ b.val = 2 ∨ b.val = 3 := by
      have h1 : (0 : ℕ) < b.val := hab'
      omega
    rcases hbv with hb1 | hb2 | hb3
    · have hb : b = 1 := Fin.ext hb1; subst hb
      have hc : c = 2 := Fin.ext (by
        have h1 : (0 : ℕ) < c.val := hac'
        have h2 : c.val < d.val := hcd'
        have h3 : (1 : ℕ) ≠ c.val := fun h => hbc' (Fin.ext h)
        have h4 : (1 : ℕ) ≠ d.val := fun h => hbd' (Fin.ext h)
        omega)
      subst hc
      have hd : d = 3 := Fin.ext (by
        have h1 : (2 : ℕ) < d.val := hcd'
        omega)
      subst hd
      rfl
    · have hb : b = 2 := Fin.ext hb2; subst hb
      have hc : c = 1 := Fin.ext (by
        have h1 : (0 : ℕ) < c.val := hac'
        have h2 : c.val < d.val := hcd'
        have h3 : (2 : ℕ) ≠ c.val := fun h => hbc' (Fin.ext h)
        have h4 : (2 : ℕ) ≠ d.val := fun h => hbd' (Fin.ext h)
        omega)
      subst hc
      have hd : d = 3 := Fin.ext (by
        have h1 : (1 : ℕ) < d.val := hcd'
        have h2 : (2 : ℕ) ≠ d.val := fun h => hbd' (Fin.ext h)
        omega)
      subst hd
      rfl
    · have hb : b = 3 := Fin.ext hb3; subst hb
      have hc : c = 1 := Fin.ext (by
        have h1 : (0 : ℕ) < c.val := hac'
        have h2 : c.val < d.val := hcd'
        have h3 : (3 : ℕ) ≠ c.val := fun h => hbc' (Fin.ext h)
        have h4 : (3 : ℕ) ≠ d.val := fun h => hbd' (Fin.ext h)
        omega)
      subst hc
      have hd : d = 2 := Fin.ext (by
        have h1 : (1 : ℕ) < d.val := hcd'
        have h2 : (3 : ℕ) ≠ d.val := fun h => hbd' (Fin.ext h)
        omega)
      subst hd
      rfl
  have hnorm_cd : ∀ a b c d : Fin 4, a < b → c < d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      tracePairing (jordanMul (q a) (q b)) (jordanMul (q c) (q d)) =
        match unorderedPairClass a b with
        | 0 => fpDoublePair1 q
        | 1 => fpDoublePair2 q
        | 2 => fpDoublePair3 q := by
    intro a b c d hab' hcd' hac' had' hbc' hbd'
    rcases lt_or_gt_of_ne hac' with hac1 | hca1
    · exact hbase a b c d hab' hcd' hac1 hbc' hbd'
    · have hc0 : c = 0 := Fin.ext (by
        have h1 : c.val < a.val := hca1
        have h2 : a.val < b.val := hab'
        have h3 : c.val < d.val := hcd'
        have h4 : a.val ≠ d.val := fun h => had' (Fin.ext h)
        have h5 : b.val ≠ d.val := fun h => hbd' (Fin.ext h)
        omega)
      subst hc0
      have hdv : d.val = 1 ∨ d.val = 2 ∨ d.val = 3 := by
        have h1 : (0 : ℕ) < d.val := hcd'
        omega
      rcases hdv with hd1 | hd2 | hd3
      · have hd : d = 1 := Fin.ext hd1; subst hd
        have ha : a = 2 := Fin.ext (by
          have h1 : (0 : ℕ) < a.val := hca1
          have h2 : a.val < b.val := hab'
          have h3 : a.val ≠ (1 : ℕ) := fun h => had' (Fin.ext h)
          have h4 : b.val ≠ (1 : ℕ) := fun h => hbd' (Fin.ext h)
          omega)
        subst ha
        have hb : b = 3 := Fin.ext (by
          have h1 : (2 : ℕ) < b.val := hab'
          omega)
        subst hb
        rw [tracePairing_comm]; rfl
      · have hd : d = 2 := Fin.ext hd2; subst hd
        have ha : a = 1 := Fin.ext (by
          have h1 : (0 : ℕ) < a.val := hca1
          have h2 : a.val < b.val := hab'
          have h3 : a.val ≠ (2 : ℕ) := fun h => had' (Fin.ext h)
          have h4 : b.val ≠ (2 : ℕ) := fun h => hbd' (Fin.ext h)
          omega)
        subst ha
        have hb : b = 3 := Fin.ext (by
          have h1 : (1 : ℕ) < b.val := hab'
          have h2 : b.val ≠ (2 : ℕ) := fun h => hbd' (Fin.ext h)
          omega)
        subst hb
        rw [tracePairing_comm]; rfl
      · have hd : d = 3 := Fin.ext hd3; subst hd
        have ha : a = 1 := Fin.ext (by
          have h1 : (0 : ℕ) < a.val := hca1
          have h2 : a.val < b.val := hab'
          have h3 : a.val ≠ (3 : ℕ) := fun h => had' (Fin.ext h)
          have h4 : b.val ≠ (3 : ℕ) := fun h => hbd' (Fin.ext h)
          omega)
        subst ha
        have hb : b = 2 := Fin.ext (by
          have h1 : (1 : ℕ) < b.val := hab'
          have h2 : b.val ≠ (3 : ℕ) := fun h => hbd' (Fin.ext h)
          omega)
        subst hb
        rw [tracePairing_comm]; rfl
  have hnorm_d : ∀ a b c d : Fin 4, a < b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      tracePairing (jordanMul (q a) (q b)) (jordanMul (q c) (q d)) =
        match unorderedPairClass a b with
        | 0 => fpDoublePair1 q
        | 1 => fpDoublePair2 q
        | 2 => fpDoublePair3 q := by
    intro a b c d hab' hcd' hac' had' hbc' hbd'
    rcases lt_or_gt_of_ne hcd' with hcd1 | hdc1
    · exact hnorm_cd a b c d hab' hcd1 hac' had' hbc' hbd'
    · rw [jordanMul_comm (q c) (q d)]
      exact hnorm_cd a b d c hab' hdc1 had' hac' hbd' hbc'
  rcases lt_or_gt_of_ne hab with hab1 | hba1
  · exact hnorm_d a b c d hab1 hcd hac had hbc hbd
  · rw [jordanMul_comm (q a) (q b), unorderedPairClass_comm a b]
    exact hnorm_d b a c d hba1 hcd hbc hbd hac had

private theorem stdBasis_pairing_affine {p pPlus pMinus : Fin 4 → Albert} {lam : ℝ}
    (ho : ∀ i j, fpOverlap p i j = fpOverlap pPlus i j ∧ fpOverlap p i j = fpOverlap pMinus i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle pPlus i j k ∧ fpTriangle p i j k = fpTriangle pMinus i j k)
    (ht1 : fpDoublePair1 p = lam * fpDoublePair1 pPlus + (1 - lam) * fpDoublePair1 pMinus)
    (ht2 : fpDoublePair2 p = lam * fpDoublePair2 pPlus + (1 - lam) * fpDoublePair2 pMinus)
    (ht3 : fpDoublePair3 p = lam * fpDoublePair3 pPlus + (1 - lam) * fpDoublePair3 pMinus)
    {x y z d : Fin 4} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z) (k : Fin 9) :
    tracePairing (p d) (stdBasisAlbert (p x) (p y) (p z) k) =
      lam * tracePairing (pPlus d) (stdBasisAlbert (pPlus x) (pPlus y) (pPlus z) k) +
        (1 - lam) * tracePairing (pMinus d) (stdBasisAlbert (pMinus x) (pMinus y) (pMinus z) k) := by
  have hc_const : ∀ (a b c : ℝ), a = b → a = c → a = lam * b + (1 - lam) * c := by
    intro a b c hab hac; subst hab hac; ring
  have hdp_eq : ∀ q : Fin 4 → Albert, ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      d ≠ a → d ≠ b → d ≠ c →
      tracePairing (q d) (jordanMul (jordanMul (q a) (q b)) (q c)) =
        match unorderedPairClass a b with
        | 0 => fpDoublePair1 q
        | 1 => fpDoublePair2 q
        | 2 => fpDoublePair3 q := by
    intro q a b c hab hac hbc hda hdb hdc
    rw [jordanMul_comm (jordanMul (q a) (q b)) (q c),
      ← tracePairing_associative (q d) (q c) (jordanMul (q a) (q b)),
      tracePairing_comm, jordanMul_comm (q d) (q c)]
    exact doublePair_of_distinct q hab hac hda.symm hbc hdb.symm hdc.symm
  fin_cases k <;> simp only [stdBasisAlbert]
  · exact hc_const _ _ _ (ho d x).1 (ho d x).2
  · exact hc_const _ _ _ (ho d y).1 (ho d y).2
  · exact hc_const _ _ _ (ho d z).1 (ho d z).2
  · rw [tracePairing_comm (p d), tracePairing_comm (pPlus d), tracePairing_comm (pMinus d)]
    exact hc_const _ _ _ (hR x y d).1 (hR x y d).2
  · rw [tracePairing_comm (p d), tracePairing_comm (pPlus d), tracePairing_comm (pMinus d)]
    exact hc_const _ _ _ (hR x z d).1 (hR x z d).2
  · rw [tracePairing_comm (p d), tracePairing_comm (pPlus d), tracePairing_comm (pMinus d)]
    exact hc_const _ _ _ (hR y z d).1 (hR y z d).2
  · rw [hdp_eq p x y z hxy hxz hyz hdx hdy hdz,
      hdp_eq pPlus x y z hxy hxz hyz hdx hdy hdz,
      hdp_eq pMinus x y z hxy hxz hyz hdx hdy hdz]
    generalize unorderedPairClass x y = u
    fin_cases u <;> [exact ht1; exact ht2; exact ht3]
  · rw [hdp_eq p y z x hyz hxy.symm hxz.symm hdy hdz hdx,
      hdp_eq pPlus y z x hyz hxy.symm hxz.symm hdy hdz hdx,
      hdp_eq pMinus y z x hyz hxy.symm hxz.symm hdy hdz hdx]
    generalize unorderedPairClass y z = u
    fin_cases u <;> [exact ht1; exact ht2; exact ht3]
  · rw [hdp_eq p z x y hxz.symm hyz.symm hxy hdz hdx hdy,
      hdp_eq pPlus z x y hxz.symm hyz.symm hxy hdz hdx hdy,
      hdp_eq pMinus z x y hxz.symm hyz.symm hxy hdz hdx hdy]
    generalize unorderedPairClass z x = u
    fin_cases u <;> [exact ht1; exact ht2; exact ht3]

private theorem subalgebra_equivariant_affine {p pPlus pMinus : Fin 4 → Albert} {lam : ℝ}
    (hp : ∀ i, IsAtom (p i)) (hpPlus : ∀ i, IsAtom (pPlus i)) (hpMinus : ∀ i, IsAtom (pMinus i))
    (hpos : 0 < fourPointInvariant p)
    (ho : ∀ i j, fpOverlap p i j = fpOverlap pPlus i j ∧ fpOverlap p i j = fpOverlap pMinus i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle pPlus i j k ∧ fpTriangle p i j k = fpTriangle pMinus i j k)
    (ht1 : fpDoublePair1 p = lam * fpDoublePair1 pPlus + (1 - lam) * fpDoublePair1 pMinus)
    (ht2 : fpDoublePair2 p = lam * fpDoublePair2 pPlus + (1 - lam) * fpDoublePair2 pMinus)
    (ht3 : fpDoublePair3 p = lam * fpDoublePair3 pPlus + (1 - lam) * fpDoublePair3 pMinus)
    {x y z d : Fin 4} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z)
    (Φ : (Fin 4 → Albert) → Albert)
    (hgen : InGeneratedAlgebra ![p x, p y, p z] (Φ p))
    (hmap_plus : ∀ g : NativeAlbertAutomorphism,
      g.linearEquiv (p x) = pPlus x → g.linearEquiv (p y) = pPlus y →
      g.linearEquiv (p z) = pPlus z → g.linearEquiv (Φ p) = Φ pPlus)
    (hmap_minus : ∀ g : NativeAlbertAutomorphism,
      g.linearEquiv (p x) = pMinus x → g.linearEquiv (p y) = pMinus y →
      g.linearEquiv (p z) = pMinus z → g.linearEquiv (Φ p) = Φ pMinus) :
    tracePairing (p d) (Φ p) =
      lam * tracePairing (pPlus d) (Φ pPlus) +
        (1 - lam) * tracePairing (pMinus d) (Φ pMinus) := by
  have hΔ : tripleDelta (p x) (p y) (p z) ≠ 0 :=
    tripleDelta_ne_zero_of_fourPointInvariant_pos hp hpos hxy hxz hyz
  obtain ⟨B₀, B₁, C₀, C₁, C₂, C₃, gp, gplus, hB0, hB1, hC0, hC2, hC3,
    hpx, hpy, hpz, hqx, hqy, hqz⟩ :=
    triple_canonical_pair hp hpPlus (fun i j => (ho i j).1) (fun i j k => (hR i j k).1) hΔ
  obtain ⟨g_to_minus, hm_x, hm_y, hm_z⟩ :=
    triple_automorphism_of_traces_eq hp hpMinus (fun i j => (ho i j).2) (fun i j k => (hR i j k).2) hΔ
  have g_to_plus_eq : ∀ g : NativeAlbertAutomorphism,
      g = gplus.symm.comp gp →
      g.linearEquiv (p x) = pPlus x ∧ g.linearEquiv (p y) = pPlus y ∧ g.linearEquiv (p z) = pPlus z := by
    rintro g rfl
    refine ⟨?_, ?_, ?_⟩ <;> simp only [NativeAlbertAutomorphism.comp, LinearEquiv.trans_apply]
    · change gplus.linearEquiv.symm (gp.linearEquiv (p x)) = pPlus x
      rw [hpx, ← hqx, gplus.linearEquiv.symm_apply_apply]
    · change gplus.linearEquiv.symm (gp.linearEquiv (p y)) = pPlus y
      rw [hpy, ← hqy, gplus.linearEquiv.symm_apply_apply]
    · change gplus.linearEquiv.symm (gp.linearEquiv (p z)) = pPlus z
      rw [hpz, ← hqz, gplus.linearEquiv.symm_apply_apply]
  have hmem_std : gp.linearEquiv (Φ p) ∈ standardComplexWindow.toSubalgebra.carrier := by
    have hgen' := gp.map_inGeneratedAlgebra ![p x, p y, p z] hgen
    have heq : (fun i => gp.linearEquiv (![p x, p y, p z] i)) =
        ![stdAtom0, stdAtom1 B₀ B₁, stdAtom2 C₀ C₁ C₂ C₃] := by
      funext i; fin_cases i <;> [exact hpx; exact hpy; exact hpz]
    rw [heq] at hgen'
    refine hgen' standardComplexWindow.toSubalgebra (fun i => ?_)
    fin_cases i
    · exact ⟨mkHermDyad ![1, 0, 0], stdAtom0_eq_mkHermDyad⟩
    · exact ⟨mkHermDyad ![B₀, B₁, 0], stdAtom1_eq_mkHermDyad B₀ B₁⟩
    · exact ⟨mkHermDyad ![C₀, ⟨C₁, C₂⟩, C₃], stdAtom2_eq_mkHermDyad C₀ C₁ C₂ C₃⟩
  obtain ⟨M, hM⟩ := hmem_std
  obtain ⟨c, hc⟩ := hermitian3_span_stdBasis B₀ B₁ C₀ C₁ C₂ C₃
    hB0.ne' hB1.ne' hC0.ne' hC2.ne' hC3.ne' M
  have hgp_phi : gp.linearEquiv (Φ p) =
      ∑ k : Fin 9, c k • stdBasisAlbert stdAtom0 (stdAtom1 B₀ B₁) (stdAtom2 C₀ C₁ C₂ C₃) k := by
    rw [← hM, hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, stdBasisAlbert_std]
  have hphi_p : Φ p = ∑ k : Fin 9, c k • stdBasisAlbert (p x) (p y) (p z) k := by
    apply gp.linearEquiv.injective
    rw [hgp_phi, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, stdBasisAlbert_map, hpx, hpy, hpz]
  have hphi_plus : Φ pPlus = ∑ k : Fin 9, c k • stdBasisAlbert (pPlus x) (pPlus y) (pPlus z) k := by
    obtain ⟨hx, hy, hz⟩ := g_to_plus_eq (gplus.symm.comp gp) rfl
    rw [← hmap_plus (gplus.symm.comp gp) hx hy hz]
    change gplus.linearEquiv.symm (gp.linearEquiv (Φ p)) = _
    rw [hgp_phi, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    congr 1
    change gplus.symm.linearEquiv (stdBasisAlbert _ _ _ k) = _
    rw [stdBasisAlbert_map]
    have hinv0 : gplus.symm.linearEquiv stdAtom0 = pPlus x := by
      change gplus.linearEquiv.symm stdAtom0 = pPlus x
      rw [← hqx, gplus.linearEquiv.symm_apply_apply]
    have hinv1 : gplus.symm.linearEquiv (stdAtom1 B₀ B₁) = pPlus y := by
      change gplus.linearEquiv.symm (stdAtom1 B₀ B₁) = pPlus y
      rw [← hqy, gplus.linearEquiv.symm_apply_apply]
    have hinv2 : gplus.symm.linearEquiv (stdAtom2 C₀ C₁ C₂ C₃) = pPlus z := by
      change gplus.linearEquiv.symm (stdAtom2 C₀ C₁ C₂ C₃) = pPlus z
      rw [← hqz, gplus.linearEquiv.symm_apply_apply]
    rw [hinv0, hinv1, hinv2]
  have hphi_minus : Φ pMinus = ∑ k : Fin 9, c k • stdBasisAlbert (pMinus x) (pMinus y) (pMinus z) k := by
    rw [← hmap_minus g_to_minus hm_x hm_y hm_z, hphi_p, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, stdBasisAlbert_map, hm_x, hm_y, hm_z]
  have htp0 : ∀ a : Albert, tracePairing a 0 = 0 := fun a => by
    rw [← zero_smul ℝ (0 : Albert), tracePairing_smul_right, zero_mul]
  have hsum_pair : ∀ (a : Albert) (v : Fin 9 → Albert),
      tracePairing a (∑ k : Fin 9, c k • v k) = ∑ k : Fin 9, c k * tracePairing a (v k) := by
    intro a v
    induction (Finset.univ : Finset (Fin 9)) using Finset.induction_on with
    | empty => simp [htp0]
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, tracePairing_add_right,
        tracePairing_smul_right, ih]
  rw [hphi_p, hphi_plus, hphi_minus, hsum_pair, hsum_pair, hsum_pair]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [stdBasis_pairing_affine ho hR ht1 ht2 ht3 hxy hxz hyz hdx hdy hdz k]
  ring

/-! ## Section 5: `PairFactor` Evaluation and Zero/One Occurrence Affinity -/

private def atomChainElem (q : Fin 4 → Albert) (base : Fin 4) (ops : List (Fin 4)) : Albert :=
  ops.foldr (fun i x => jordanMul (q i) x) (q base)

private structure PairFactor where
  head : Fin 4
  mid : List (Fin 4)
  tail : Fin 4

private def PairFactor.atoms (f : PairFactor) : List (Fin 4) :=
  f.head :: (f.mid ++ [f.tail])

private def PairFactor.eval (f : PairFactor) (q : Fin 4 → Albert) : ℝ :=
  tracePairing (q f.head) (atomChainElem q f.tail f.mid)

private def PairFactor.weight (f : PairFactor) : ℕ :=
  f.mid.length + 1

private theorem tracePairing_foldr_reverse (q : Fin 4 → Albert) (ops : List (Fin 4)) (x y : Albert) :
    tracePairing x (ops.foldr (fun i u => jordanMul (q i) u) y) =
      tracePairing y (ops.reverse.foldr (fun i u => jordanMul (q i) u) x) := by
  induction ops generalizing x with
  | nil => exact tracePairing_comm x y
  | cons c cs ih =>
    simp only [List.foldr_cons, List.reverse_cons, List.foldr_append, List.foldr_nil]
    rw [← tracePairing_associative x (q c) _, jordanMul_comm x (q c)]
    exact ih (jordanMul (q c) x)

private theorem pairFactor_split_at (q : Fin 4 → Albert)
    (b : Fin 4) (L₁ : List (Fin 4)) (d : Fin 4) (L₂ : List (Fin 4)) (a : Fin 4) :
    tracePairing (q b) (atomChainElem q a (L₁ ++ d :: L₂)) =
      tracePairing (q d) (jordanMul (atomChainElem q a L₂) (atomChainElem q b L₁.reverse)) := by
  unfold atomChainElem
  rw [List.foldr_append, List.foldr_cons, tracePairing_foldr_reverse, tracePairing_associative]

private theorem atomChainElem_mem_subalgebra (B : NativeJordanSubalgebra)
    (q : Fin 4 → Albert) {base : Fin 4} {ops : List (Fin 4)}
    (hbase : q base ∈ B.carrier) (hops : ∀ i ∈ ops, q i ∈ B.carrier) :
    atomChainElem q base ops ∈ B.carrier := by
  induction ops with
  | nil => exact hbase
  | cons i is ih =>
    simp only [atomChainElem, List.foldr_cons]
    exact B.product_mem _ (hops i (by simp)) _
      (ih fun j hj => hops j (by simp [hj]))

private theorem atomChainElem_inGenerated {q : Fin 4 → Albert} {x y z : Fin 4}
    {base : Fin 4} {ops : List (Fin 4)}
    (hbase : base = x ∨ base = y ∨ base = z)
    (hops : ∀ i ∈ ops, i = x ∨ i = y ∨ i = z) :
    InGeneratedAlgebra ![q x, q y, q z] (atomChainElem q base ops) := by
  intro B hB
  have hmem : ∀ i : Fin 4, i = x ∨ i = y ∨ i = z → q i ∈ B.carrier := by
    rintro i (rfl | rfl | rfl)
    · exact hB 0
    · exact hB 1
    · exact hB 2
  exact atomChainElem_mem_subalgebra B q (hmem base hbase) fun i hi => hmem i (hops i hi)

private theorem atomChainElem_cons (q : Fin 4 → Albert) (base : Fin 4) (i : Fin 4)
    (is : List (Fin 4)) :
    atomChainElem q base (i :: is) = jordanMul (q i) (atomChainElem q base is) := rfl

private theorem atomChainElem_map_auto (g : NativeAlbertAutomorphism)
    {q q' : Fin 4 → Albert} {base : Fin 4} {ops : List (Fin 4)}
    (hbase : g.linearEquiv (q base) = q' base)
    (hops : ∀ i ∈ ops, g.linearEquiv (q i) = q' i) :
    g.linearEquiv (atomChainElem q base ops) = atomChainElem q' base ops := by
  induction ops with
  | nil => exact hbase
  | cons i is ih =>
    rw [atomChainElem_cons, atomChainElem_cons, g.preserves_product,
      hops i (by simp), ih fun j hj => hops j (by simp [hj])]

private theorem three_complement_of_ne (d : Fin 4) :
    ∃ x y z : Fin 4, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ d ≠ x ∧ d ≠ y ∧ d ≠ z ∧
      ∀ i : Fin 4, i ≠ d → i = x ∨ i = y ∨ i = z := by
  fin_cases d
  · exact ⟨1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      fun i hi => by fin_cases i <;> simp at hi ⊢⟩
  · exact ⟨0, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      fun i hi => by fin_cases i <;> simp at hi ⊢⟩
  · exact ⟨0, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      fun i hi => by fin_cases i <;> simp at hi ⊢⟩
  · exact ⟨0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide,
      fun i hi => by fin_cases i <;> simp at hi ⊢⟩

private theorem pairFactor_eval_eq_of_missing {p q : Fin 4 → Albert}
    (hp : ∀ i, IsAtom (p i)) (hq : ∀ i, IsAtom (q i))
    (hpos : 0 < fourPointInvariant p)
    (ho : ∀ i j, fpOverlap p i j = fpOverlap q i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle q i j k)
    (f : PairFactor) (hd : ∃ d : Fin 4, d ∉ f.atoms) :
    f.eval q = f.eval p := by
  obtain ⟨d, hnd⟩ := hd
  obtain ⟨x, y, z, hxy, hxz, hyz, hdx, hdy, hdz, hcov⟩ := three_complement_of_ne d
  have hΔ : tripleDelta (p x) (p y) (p z) ≠ 0 :=
    tripleDelta_ne_zero_of_fourPointInvariant_pos hp hpos hxy hxz hyz
  obtain ⟨g, gx, gy, gz⟩ := triple_automorphism_of_traces_eq hp hq ho hR hΔ
  have hmap : ∀ i ∈ f.atoms, g.linearEquiv (p i) = q i := by
    intro i hi
    have hid : i ≠ d := fun h => hnd (h ▸ hi)
    rcases hcov i hid with rfl | rfl | rfl
    · exact gx
    · exact gy
    · exact gz
  unfold PairFactor.eval
  rw [← hmap f.head (by simp [PairFactor.atoms]),
    ← atomChainElem_map_auto g
      (hmap f.tail (by simp [PairFactor.atoms]))
      (fun i hi => hmap i (by simp [PairFactor.atoms, hi])),
    g.map_tracePairing]

private theorem count_eq_zero_iff_notMem {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    l.count a = 0 ↔ a ∉ l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, List.mem_cons, not_or, beq_iff_eq]
    split_ifs with h
    · subst h; simp
    · simpa [Ne.symm h] using ih

private theorem mem_split_unique {α : Type*} [DecidableEq α] {d : α} {l : List α}
    (hc : l.count d = 1) :
    ∃ l₁ l₂ : List α, l = l₁ ++ d :: l₂ ∧ d ∉ l₁ ∧ d ∉ l₂ := by
  induction l with
  | nil => simp at hc
  | cons x xs ih =>
    simp only [List.count_cons, beq_iff_eq] at hc
    split_ifs at hc with h
    · subst h
      have hxs0 : xs.count x = 0 := by omega
      exact ⟨[], xs, rfl, by simp, (count_eq_zero_iff_notMem x xs).mp hxs0⟩
    · have hxs1 : xs.count d = 1 := by omega
      obtain ⟨l₁, l₂, rfl, h1, h2⟩ := ih hxs1
      exact ⟨x :: l₁, l₂, rfl, by simp [Ne.symm h, h1], h2⟩

private theorem pairFactor_eval_affine_of_count_le_one
    {p pPlus pMinus : Fin 4 → Albert} {lam : ℝ}
    (hp : ∀ i, IsAtom (p i)) (hpPlus : ∀ i, IsAtom (pPlus i)) (hpMinus : ∀ i, IsAtom (pMinus i))
    (hpos : 0 < fourPointInvariant p)
    (ho : ∀ i j, fpOverlap p i j = fpOverlap pPlus i j ∧ fpOverlap p i j = fpOverlap pMinus i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle pPlus i j k ∧ fpTriangle p i j k = fpTriangle pMinus i j k)
    (ht1 : fpDoublePair1 p = lam * fpDoublePair1 pPlus + (1 - lam) * fpDoublePair1 pMinus)
    (ht2 : fpDoublePair2 p = lam * fpDoublePair2 pPlus + (1 - lam) * fpDoublePair2 pMinus)
    (ht3 : fpDoublePair3 p = lam * fpDoublePair3 pPlus + (1 - lam) * fpDoublePair3 pMinus)
    (f : PairFactor) (hc : ∃ d : Fin 4, f.atoms.count d ≤ 1) :
    f.eval p = lam * f.eval pPlus + (1 - lam) * f.eval pMinus := by
  obtain ⟨d, hd⟩ := hc
  by_cases hc0 : f.atoms.count d = 0
  · have hnd : d ∉ f.atoms := (count_eq_zero_iff_notMem d f.atoms).mp hc0
    have e1 := pairFactor_eval_eq_of_missing hp hpPlus hpos
      (fun i j => (ho i j).1) (fun i j k => (hR i j k).1) f ⟨d, hnd⟩
    have e2 := pairFactor_eval_eq_of_missing hp hpMinus hpos
      (fun i j => (ho i j).2) (fun i j k => (hR i j k).2) f ⟨d, hnd⟩
    rw [e1, e2]; ring
  · have hc1 : f.atoms.count d = 1 := by omega
    obtain ⟨x, y, z, hxy, hxz, hyz, hdx, hdy, hdz, hcov⟩ := three_complement_of_ne d
    have hcount_split : f.atoms.count d =
        (if f.head = d then 1 else 0) + f.mid.count d + (if f.tail = d then 1 else 0) := by
      simp [PairFactor.atoms, List.count_cons, List.count_append]
      split_ifs <;> omega
    rw [hcount_split] at hc1
    by_cases hhd : f.head = d
    · have hm0 : f.mid.count d = 0 := by simp [hhd] at hc1; omega
      have htd : f.tail ≠ d := by intro h; simp [hhd, h] at hc1
      have hmn : d ∉ f.mid := (count_eq_zero_iff_notMem d f.mid).mp hm0
      have hgen : InGeneratedAlgebra ![p x, p y, p z] (atomChainElem p f.tail f.mid) :=
        atomChainElem_inGenerated (hcov f.tail htd) (fun i hi => hcov i fun h => hmn (h ▸ hi))
      have haff := subalgebra_equivariant_affine hp hpPlus hpMinus hpos ho hR ht1 ht2 ht3
        hxy hxz hyz hdx hdy hdz (fun q => atomChainElem q f.tail f.mid) hgen
        (fun g gx gy gz => atomChainElem_map_auto g
          (by rcases hcov f.tail htd with rfl | rfl | rfl <;> assumption)
          (fun i hi => by rcases hcov i (fun h => hmn (h ▸ hi)) with rfl | rfl | rfl <;> assumption))
        (fun g gx gy gz => atomChainElem_map_auto g
          (by rcases hcov f.tail htd with rfl | rfl | rfl <;> assumption)
          (fun i hi => by rcases hcov i (fun h => hmn (h ▸ hi)) with rfl | rfl | rfl <;> assumption))
      simpa only [PairFactor.eval, hhd] using haff
    · by_cases htd : f.tail = d
      · have hm0 : f.mid.count d = 0 := by simp [hhd, htd] at hc1; omega
        have hmn : d ∉ f.mid := (count_eq_zero_iff_notMem d f.mid).mp hm0
        have hev : ∀ q : Fin 4 → Albert,
            f.eval q = tracePairing (q d) (atomChainElem q f.head f.mid.reverse) := fun q => by
          unfold PairFactor.eval atomChainElem
          rw [tracePairing_foldr_reverse, htd]
        have hgen : InGeneratedAlgebra ![p x, p y, p z] (atomChainElem p f.head f.mid.reverse) :=
          atomChainElem_inGenerated (hcov f.head hhd)
            (fun i hi => hcov i fun h => hmn (h ▸ List.mem_reverse.mp hi))
        have haff := subalgebra_equivariant_affine hp hpPlus hpMinus hpos ho hR ht1 ht2 ht3
          hxy hxz hyz hdx hdy hdz (fun q => atomChainElem q f.head f.mid.reverse) hgen
          (fun g gx gy gz => atomChainElem_map_auto g
            (by rcases hcov f.head hhd with rfl | rfl | rfl <;> assumption)
            (fun i hi => by
              rcases hcov i (fun h => hmn (h ▸ List.mem_reverse.mp hi)) with rfl | rfl | rfl <;> assumption))
          (fun g gx gy gz => atomChainElem_map_auto g
            (by rcases hcov f.head hhd with rfl | rfl | rfl <;> assumption)
            (fun i hi => by
              rcases hcov i (fun h => hmn (h ▸ List.mem_reverse.mp hi)) with rfl | rfl | rfl <;> assumption))
        rw [hev p, hev pPlus, hev pMinus]
        exact haff
      · have hm1 : f.mid.count d = 1 := by simp [hhd, htd] at hc1; omega
        obtain ⟨L₁, L₂, hmid, h1, h2⟩ := mem_split_unique hm1
        have hev : ∀ q : Fin 4 → Albert,
            f.eval q = tracePairing (q d)
              (jordanMul (atomChainElem q f.tail L₂) (atomChainElem q f.head L₁.reverse)) := fun q => by
          unfold PairFactor.eval
          rw [hmid]
          exact pairFactor_split_at q f.head L₁ d L₂ f.tail
        have hgen : InGeneratedAlgebra ![p x, p y, p z]
            (jordanMul (atomChainElem p f.tail L₂) (atomChainElem p f.head L₁.reverse)) := by
          intro B hB
          exact B.product_mem _ (atomChainElem_inGenerated (hcov f.tail htd)
              (fun i hi => hcov i fun h => h2 (h ▸ hi)) B hB)
            _ (atomChainElem_inGenerated (hcov f.head hhd)
              (fun i hi => hcov i fun h => h1 (h ▸ List.mem_reverse.mp hi)) B hB)
        have hmap : ∀ (q : Fin 4 → Albert) (g : NativeAlbertAutomorphism),
            g.linearEquiv (p x) = q x → g.linearEquiv (p y) = q y → g.linearEquiv (p z) = q z →
            g.linearEquiv (jordanMul (atomChainElem p f.tail L₂) (atomChainElem p f.head L₁.reverse)) =
              jordanMul (atomChainElem q f.tail L₂) (atomChainElem q f.head L₁.reverse) :=
          fun q g gx gy gz => by
            rw [g.preserves_product,
              atomChainElem_map_auto g
                (by rcases hcov f.tail htd with rfl | rfl | rfl <;> assumption)
                (fun i hi => by rcases hcov i (fun h => h2 (h ▸ hi)) with rfl | rfl | rfl <;> assumption),
              atomChainElem_map_auto g
                (by rcases hcov f.head hhd with rfl | rfl | rfl <;> assumption)
                (fun i hi => by
                  rcases hcov i (fun h => h1 (h ▸ List.mem_reverse.mp hi)) with rfl | rfl | rfl <;> assumption)]
        have haff := subalgebra_equivariant_affine hp hpPlus hpMinus hpos ho hR ht1 ht2 ht3
          hxy hxz hyz hdx hdy hdz
          (fun q => jordanMul (atomChainElem q f.tail L₂) (atomChainElem q f.head L₁.reverse))
          hgen (hmap pPlus) (hmap pMinus)
        rw [hev p, hev pPlus, hev pMinus]
        exact haff

private theorem sum_count_fin4 (l : List (Fin 4)) :
    (∑ d : Fin 4, l.count d) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib]
    have hdelta : (∑ d : Fin 4, (if a == d then 1 else 0)) = 1 := by
      fin_cases a <;> decide
    omega

private theorem exists_count_le_one_of_length_le_seven (l : List (Fin 4)) (hlen : l.length ≤ 7) :
    ∃ d : Fin 4, l.count d ≤ 1 := by
  by_contra h
  push Not at h
  have hsum : ∑ d : Fin 4, (2 : ℕ) ≤ ∑ d : Fin 4, l.count d :=
    Finset.sum_le_sum fun d _ => h d
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    sum_count_fin4] at hsum
  omega

/-! ## Section 6: Word Expansion, Counting, and `nativeWordProbability_e3_affine_le_six` -/

private def chainElem (q : Fin 4 → Albert) (ops : List (Fin 4)) : Albert :=
  ops.foldr (fun i x => jordanMul (q i) x) albertUnit

private theorem chainElem_append_singleton (q : Fin 4 → Albert) (mid : List (Fin 4)) (tail : Fin 4) :
    chainElem q (mid ++ [tail]) = atomChainElem q tail mid := by
  unfold chainElem atomChainElem
  rw [List.foldr_append, List.foldr_cons, List.foldr_nil, jordanMul_albertUnit_right]

private inductive EffectTerm where
  | openTerm (coeff : ℝ) (ops : List (Fin 4))
  | splitTerm (coeff : ℝ) (factors : List PairFactor) (base : Fin 4) (ops : List (Fin 4))

private def EffectTerm.eval (q : Fin 4 → Albert) : EffectTerm → Albert
  | .openTerm c ops => c • chainElem q ops
  | .splitTerm c fs base ops => (c * (fs.map (fun f => f.eval q)).prod) • atomChainElem q base ops

private def EffectTerm.weight : EffectTerm → ℕ
  | .openTerm _ ops => ops.length
  | .splitTerm _ fs _ ops => (fs.map PairFactor.weight).sum + (ops.length + 1)

private def splitLast? {α : Type*} : List α → Option (List α × α)
  | [] => none
  | [x] => some ([], x)
  | x :: xs =>
    match splitLast? xs with
    | none => none
    | some (mid, last) => some (x :: mid, last)

private theorem splitLast?_none_iff {α : Type*} (l : List α) :
    splitLast? l = none ↔ l = [] := by
  cases l with
  | nil => simp [splitLast?]
  | cons x xs =>
    cases xs with
    | nil => simp [splitLast?]
    | cons y ys =>
      simp only [splitLast?]
      cases h : splitLast? (y :: ys) with
      | none =>
        have : y :: ys = [] := (splitLast?_none_iff (y :: ys)).mp h
        simp at this
      | some p => simp

private theorem splitLast?_some {α : Type*} {l mid : List α} {last : α}
    (h : splitLast? l = some (mid, last)) :
    l = mid ++ [last] := by
  induction l generalizing mid with
  | nil => simp [splitLast?] at h
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [splitLast?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | cons y ys =>
      simp only [splitLast?] at h
      cases hs : splitLast? (y :: ys) with
      | none => rw [hs] at h; simp at h
      | some p =>
        rw [hs] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [ih hs]

private def stepU (i : Fin 4) : EffectTerm → EffectTerm
  | .openTerm c ops =>
    match splitLast? ops with
    | none => .splitTerm c [] i []
    | some (mid, tail) => .splitTerm c [⟨i, mid, tail⟩] i []
  | .splitTerm c fs base ops =>
    .splitTerm c (⟨i, ops, base⟩ :: fs) i []

private def stepNeg2L (i : Fin 4) : EffectTerm → EffectTerm
  | .openTerm c ops => .openTerm (-2 * c) (i :: ops)
  | .splitTerm c fs base ops => .splitTerm (-2 * c) fs base (i :: ops)

private def stepTerm (a : Outcome (Fin 4)) (t : EffectTerm) : List EffectTerm :=
  if a.2 then [stepU a.1 t] else [t, stepNeg2L a.1 t, stepU a.1 t]

private def expandWord : Word (Fin 4) → List EffectTerm
  | [] => [.openTerm 1 []]
  | a :: w => (expandWord w).flatMap (stepTerm a)

private theorem stepU_eval {q : Fin 4 → Albert} (hq : ∀ i, IsAtom (q i))
    (i : Fin 4) (t : EffectTerm) :
    (stepU i t).eval q = quadraticMap (q i) (t.eval q) := by
  cases t with
  | openTerm c ops =>
    dsimp only [stepU]
    cases hs : splitLast? ops with
    | none =>
      have hops : ops = [] := (splitLast?_none_iff ops).mp hs
      subst hops
      simp only [EffectTerm.eval, List.map_nil, List.prod_nil, mul_one,
        chainElem, List.foldr_nil, atomChainElem,
        quadraticMap_atom _ _ (hq i), tracePairing_smul_right,
        tracePairing_atom_unit (hq i)]
    | some p =>
      rcases p with ⟨mid, tail⟩
      have hops := splitLast?_some hs
      subst hops
      simp only [EffectTerm.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, chainElem_append_singleton, atomChainElem, List.foldr_nil,
        quadraticMap_atom _ _ (hq i), tracePairing_smul_right, PairFactor.eval]
  | splitTerm c fs base ops =>
    simp only [stepU, EffectTerm.eval, List.map_cons, List.prod_cons,
      quadraticMap_atom _ _ (hq i), tracePairing_smul_right,
      atomChainElem, List.foldr_nil, PairFactor.eval]
    congr 1
    ring

private theorem stepNeg2L_eval (q : Fin 4 → Albert) (i : Fin 4) (t : EffectTerm) :
    (stepNeg2L i t).eval q = (-2 : ℝ) • jordanMul (q i) (t.eval q) := by
  cases t with
  | openTerm c ops =>
    simp only [stepNeg2L, EffectTerm.eval, chainElem, List.foldr_cons,
      jordanMul_smul_right, smul_smul]
  | splitTerm c fs base ops =>
    simp only [stepNeg2L, EffectTerm.eval, atomChainElem, List.foldr_cons,
      jordanMul_smul_right, smul_smul, mul_assoc]

private theorem stepTerm_eval {q : Fin 4 → Albert} (hq : ∀ i, IsAtom (q i))
    (a : Outcome (Fin 4)) (t : EffectTerm) :
    ((stepTerm a t).map (EffectTerm.eval q)).sum =
      quadraticMap (nativeOutcome q a) (t.eval q) := by
  rcases a with ⟨i, b⟩
  cases b
  · simp only [stepTerm, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, stepNeg2L_eval, stepU_eval hq,
      nativeOutcome, quadraticMap_compl_atom (hq i), quadraticMap_atom _ _ (hq i)]
    abel
  · simp only [stepTerm, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, stepU_eval hq, nativeOutcome]

private theorem quadraticMap_list_sum (a : Albert) (l : List Albert) :
    quadraticMap a l.sum = (l.map (quadraticMap a)).sum := by
  induction l with
  | nil => simp [quadraticMap_zero_right]
  | cons x xs ih => simp [quadraticMap_add_right, ih]

private theorem expandWord_eval {q : Fin 4 → Albert} (hq : ∀ i, IsAtom (q i)) (w : Word (Fin 4)) :
    ((expandWord w).map (EffectTerm.eval q)).sum = nativeWordEffect q w := by
  induction w with
  | nil => simp [expandWord, EffectTerm.eval, chainElem, nativeWordEffect]
  | cons a w ih =>
    simp only [expandWord, nativeWordEffect, ← ih]
    clear ih
    induction expandWord w with
    | nil => simp [quadraticMap_zero_right]
    | cons t ts iht =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, quadraticMap_add_right, stepTerm_eval hq, iht]

private theorem stepU_weight (i : Fin 4) (t : EffectTerm) :
    (stepU i t).weight ≤ t.weight + 1 := by
  cases t with
  | openTerm c ops =>
    dsimp only [stepU]
    cases hs : splitLast? ops with
    | none => simp [EffectTerm.weight]
    | some p =>
      rcases p with ⟨mid, tail⟩
      have hops := splitLast?_some hs
      subst hops
      simp [EffectTerm.weight, PairFactor.weight]
  | splitTerm c fs base ops =>
    simp [stepU, EffectTerm.weight, PairFactor.weight]
    omega

private theorem stepNeg2L_weight (i : Fin 4) (t : EffectTerm) :
    (stepNeg2L i t).weight = t.weight + 1 := by
  cases t
  · simp [stepNeg2L, EffectTerm.weight]
  · simp [stepNeg2L, EffectTerm.weight]; omega

private theorem expandWord_weight (w : Word (Fin 4)) :
    ∀ t ∈ expandWord w, t.weight ≤ w.length := by
  induction w with
  | nil =>
    intro t ht
    simp only [expandWord, List.mem_singleton] at ht
    subst ht
    simp [EffectTerm.weight]
  | cons a w ih =>
    intro t ht
    simp only [expandWord, List.mem_flatMap] at ht
    rcases ht with ⟨s, hs, hts⟩
    have hsw := ih s hs
    rcases a with ⟨i, b⟩
    cases b <;> simp only [stepTerm, Bool.false_eq_true, ↓reduceIte,
        List.mem_cons, List.not_mem_nil, or_false] at hts
    · rcases hts with rfl | rfl | rfl
      · simp; omega
      · rw [stepNeg2L_weight]; simp; omega
      · have := stepU_weight i s; simp; omega
    · subst hts
      have := stepU_weight i s; simp; omega

private def closeTerm : EffectTerm → ℝ × List PairFactor
  | .openTerm c ops =>
    match ops with
    | [] => (3 * c, [])
    | [_b] => (c, [])
    | b :: rest =>
      match splitLast? rest with
      | none => (c, [])
      | some (mid, tail) => (c, [⟨b, mid, tail⟩])
  | .splitTerm c fs base ops =>
    match ops with
    | [] => (c, fs)
    | b :: mid => (c, ⟨b, mid, base⟩ :: fs)

private theorem closeTerm_eval {q : Fin 4 → Albert} (hq : ∀ i, IsAtom (q i)) (t : EffectTerm) :
    let cf := closeTerm t
    albertTrace (t.eval q) = cf.1 * (cf.2.map (fun f => f.eval q)).prod := by
  cases t with
  | openTerm c ops =>
    cases ops with
    | nil =>
      simp [closeTerm, EffectTerm.eval, chainElem, albertTrace_smul, albertTrace_albertUnit,
        mul_comm]
    | cons b rest =>
      cases rest with
      | nil =>
        simp [closeTerm, EffectTerm.eval, chainElem, albertTrace_smul,
          jordanMul_albertUnit_right, (hq b).2]
      | cons r rs =>
        simp only [closeTerm]
        cases hs : splitLast? (r :: rs) with
        | none =>
          have := (splitLast?_none_iff (r :: rs)).mp hs
          simp at this
        | some p =>
          rcases p with ⟨mid, tail⟩
          have hrest := splitLast?_some hs
          simp only [EffectTerm.eval, chainElem, List.foldr_cons, hrest]
          change albertTrace (c • jordanMul (q b) (chainElem q (mid ++ [tail]))) =
            c * (tracePairing (q b) (atomChainElem q tail mid) * 1)
          rw [albertTrace_smul, chainElem_append_singleton]
          simp [tracePairing]
  | splitTerm c fs base ops =>
    cases ops with
    | nil =>
      simp only [closeTerm, EffectTerm.eval, atomChainElem, List.foldr_nil,
        albertTrace_smul, (hq base).2, mul_one]
    | cons b mid =>
      dsimp only [closeTerm, EffectTerm.eval, List.map_cons, List.prod_cons, PairFactor.eval]
      rw [atomChainElem_cons, albertTrace_smul]
      change (c * (fs.map (fun f => f.eval q)).prod) *
          tracePairing (q b) (atomChainElem q base mid) =
        c * (tracePairing (q b) (atomChainElem q base mid) * (fs.map (fun f => f.eval q)).prod)
      ring

private theorem closeTerm_weight {t : EffectTerm} {k : ℕ} (hk : t.weight ≤ k) :
    ((closeTerm t).2.map PairFactor.weight).sum ≤ k - 1 := by
  cases t with
  | openTerm c ops =>
    cases ops with
    | nil => simp [closeTerm]
    | cons b rest =>
      cases rest with
      | nil => simp [closeTerm]
      | cons r rs =>
        simp only [closeTerm]
        cases hs : splitLast? (r :: rs) with
        | none => simp
        | some p =>
          rcases p with ⟨mid, tail⟩
          have hrest := splitLast?_some hs
          have hlen : (b :: (r :: rs)).length = mid.length + 2 := by
            rw [hrest]; simp
          simp only [EffectTerm.weight] at hk
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            PairFactor.weight]
          omega
  | splitTerm c fs base ops =>
    cases ops with
    | nil =>
      simp only [EffectTerm.weight, List.length_nil, zero_add] at hk
      simp only [closeTerm]
      omega
    | cons b mid =>
      simp only [EffectTerm.weight, List.length_cons] at hk
      simp only [closeTerm, List.map_cons, List.sum_cons, PairFactor.weight]
      omega

private theorem albertTrace_list_sum (l : List Albert) :
    albertTrace l.sum = (l.map albertTrace).sum := by
  induction l with
  | nil => simp [albertTrace_zero]
  | cons x xs ih => simp [albertTrace_add, ih]

private theorem nativeWordProbability_e3_eq_sum {q : Fin 4 → Albert} (hq : ∀ i, IsAtom (q i))
    (w : Word (Fin 4)) :
    nativeWordProbability q ((1 / 3 : ℝ) • albertUnit) w =
      (1 / 3 : ℝ) * (((expandWord w).map closeTerm).map
        (fun cf => cf.1 * (cf.2.map (fun f => f.eval q)).prod)).sum := by
  rw [nativeWordProbability_smul, nativeWordProbability_eq_pairing,
    tracePairing_comm, tracePairing_unit_right, ← expandWord_eval hq, albertTrace_list_sum]
  congr 1
  simp only [List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => closeTerm_eval hq t

private theorem prod_affine_of_weight_le_five
    {p pPlus pMinus : Fin 4 → Albert} {lam : ℝ}
    (hp : ∀ i, IsAtom (p i)) (hpPlus : ∀ i, IsAtom (pPlus i)) (hpMinus : ∀ i, IsAtom (pMinus i))
    (hpos : 0 < fourPointInvariant p)
    (ho : ∀ i j, fpOverlap p i j = fpOverlap pPlus i j ∧ fpOverlap p i j = fpOverlap pMinus i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle pPlus i j k ∧ fpTriangle p i j k = fpTriangle pMinus i j k)
    (ht1 : fpDoublePair1 p = lam * fpDoublePair1 pPlus + (1 - lam) * fpDoublePair1 pMinus)
    (ht2 : fpDoublePair2 p = lam * fpDoublePair2 pPlus + (1 - lam) * fpDoublePair2 pMinus)
    (ht3 : fpDoublePair3 p = lam * fpDoublePair3 pPlus + (1 - lam) * fpDoublePair3 pMinus)
    (fs : List PairFactor) (hwt : (fs.map PairFactor.weight).sum ≤ 5) :
    (fs.map (fun f => f.eval p)).prod =
      lam * (fs.map (fun f => f.eval pPlus)).prod +
        (1 - lam) * (fs.map (fun f => f.eval pMinus)).prod := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons] at hwt
    have hf_wt : f.weight ≤ 5 := by omega
    have hfs_wt : (fs.map PairFactor.weight).sum ≤ 5 := by omega
    have hf_len : f.atoms.length ≤ 7 := by
      simp only [PairFactor.atoms, List.length_cons, List.length_append, List.length_nil]
      simp only [PairFactor.weight] at hf_wt
      omega
    have hf_aff : f.eval p = lam * f.eval pPlus + (1 - lam) * f.eval pMinus :=
      pairFactor_eval_affine_of_count_le_one hp hpPlus hpMinus hpos ho hR ht1 ht2 ht3 f
        (exists_count_le_one_of_length_le_seven f.atoms hf_len)
    by_cases hmiss : ∃ d : Fin 4, d ∉ f.atoms
    · have h1 : f.eval pPlus = f.eval p :=
        pairFactor_eval_eq_of_missing hp hpPlus hpos
          (fun i j => (ho i j).1) (fun i j k => (hR i j k).1) f hmiss
      have h2 : f.eval pMinus = f.eval p :=
        pairFactor_eval_eq_of_missing hp hpMinus hpos
          (fun i j => (ho i j).2) (fun i j k => (hR i j k).2) f hmiss
      simp only [List.map_cons, List.prod_cons, ih hfs_wt, h1, h2]
      ring
    · push Not at hmiss
      have h4_le : 4 ≤ f.atoms.length := by
        have hsub : (Finset.univ : Finset (Fin 4)) ⊆ f.atoms.toFinset := by
          intro d _
          exact List.mem_toFinset.mpr (hmiss d)
        calc 4 = (Finset.univ : Finset (Fin 4)).card := by simp
          _ ≤ f.atoms.toFinset.card := Finset.card_le_card hsub
          _ ≤ f.atoms.length := List.toFinset_card_le _
      have hf_ge3 : 3 ≤ f.weight := by
        simp only [PairFactor.atoms, List.length_cons, List.length_append, List.length_nil] at h4_le
        simp only [PairFactor.weight]
        omega
      have hfs_le2 : (fs.map PairFactor.weight).sum ≤ 2 := by omega
      have hfs_const : ∀ g ∈ fs, g.eval pPlus = g.eval p ∧ g.eval pMinus = g.eval p := by
        intro g hg
        have hg_wt : g.weight ≤ 2 := by
          have := List.le_sum_of_mem (List.mem_map_of_mem (f := PairFactor.weight) hg)
          omega
        have hg_len : g.atoms.length ≤ 3 := by
          simp only [PairFactor.atoms, List.length_cons, List.length_append, List.length_nil]
          simp only [PairFactor.weight] at hg_wt
          omega
        have hg_miss : ∃ d : Fin 4, d ∉ g.atoms := by
          by_contra hall
          push Not at hall
          have hsub : (Finset.univ : Finset (Fin 4)) ⊆ g.atoms.toFinset := by
            intro d _
            exact List.mem_toFinset.mpr (hall d)
          have hle := calc 4 = (Finset.univ : Finset (Fin 4)).card := by simp
            _ ≤ g.atoms.toFinset.card := Finset.card_le_card hsub
            _ ≤ g.atoms.length := List.toFinset_card_le _
          omega
        exact ⟨pairFactor_eval_eq_of_missing hp hpPlus hpos
            (fun i j => (ho i j).1) (fun i j k => (hR i j k).1) g hg_miss,
          pairFactor_eval_eq_of_missing hp hpMinus hpos
            (fun i j => (ho i j).2) (fun i j k => (hR i j k).2) g hg_miss⟩
      have hp_plus_prod : (fs.map (fun g => g.eval pPlus)).prod = (fs.map (fun g => g.eval p)).prod := by
        congr 1
        exact List.map_congr_left fun g hg => (hfs_const g hg).1
      have hp_minus_prod : (fs.map (fun g => g.eval pMinus)).prod = (fs.map (fun g => g.eval p)).prod := by
        congr 1
        exact List.map_congr_left fun g hg => (hfs_const g hg).2
      simp only [List.map_cons, List.prod_cons, hp_plus_prod, hp_minus_prod, hf_aff]
      ring

/--
`app:cert:universalsix`: for any four atoms `p : Fin 4 → Albert` with `0 < fourPointInvariant p`
and any two atom quadruples `pPlus, pMinus : Fin 4 → Albert` sharing all pairwise overlaps and
triple triangles with `p` and satisfying `t_r(p) = lam * t_r(pPlus) + (1 - lam) * t_r(pMinus)`
(`r = 1, 2, 3`), every sequential word probability from `(1 / 3 : ℝ) • albertUnit` of length
at most `6` is given by the exact same `lam`-affine combination.
-/
theorem nativeWordProbability_e3_affine_le_six
    {p pPlus pMinus : Fin 4 → Albert} {lam : ℝ}
    (hp : ∀ i, IsAtom (p i)) (hpPlus : ∀ i, IsAtom (pPlus i)) (hpMinus : ∀ i, IsAtom (pMinus i))
    (hpos : 0 < fourPointInvariant p)
    (ho : ∀ i j, fpOverlap p i j = fpOverlap pPlus i j ∧ fpOverlap p i j = fpOverlap pMinus i j)
    (hR : ∀ i j k, fpTriangle p i j k = fpTriangle pPlus i j k ∧ fpTriangle p i j k = fpTriangle pMinus i j k)
    (ht1 : fpDoublePair1 p = lam * fpDoublePair1 pPlus + (1 - lam) * fpDoublePair1 pMinus)
    (ht2 : fpDoublePair2 p = lam * fpDoublePair2 pPlus + (1 - lam) * fpDoublePair2 pMinus)
    (ht3 : fpDoublePair3 p = lam * fpDoublePair3 pPlus + (1 - lam) * fpDoublePair3 pMinus)
    (w : Word (Fin 4)) (hw : w.length ≤ 6) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w =
      lam * nativeWordProbability pPlus ((1 / 3 : ℝ) • albertUnit) w +
        (1 - lam) * nativeWordProbability pMinus ((1 / 3 : ℝ) • albertUnit) w := by
  rw [nativeWordProbability_e3_eq_sum hp, nativeWordProbability_e3_eq_sum hpPlus,
    nativeWordProbability_e3_eq_sum hpMinus]
  have hsum_aff :
      ∀ ts : List EffectTerm,
        (∀ t ∈ ts, t.weight ≤ 6) →
        ((ts.map closeTerm).map (fun cf => cf.1 * (cf.2.map (fun f => f.eval p)).prod)).sum =
          lam * ((ts.map closeTerm).map (fun cf => cf.1 * (cf.2.map (fun f => f.eval pPlus)).prod)).sum +
          (1 - lam) * ((ts.map closeTerm).map (fun cf => cf.1 * (cf.2.map (fun f => f.eval pMinus)).prod)).sum := by
    intro ts hts
    induction ts with
    | nil => simp
    | cons t ts iht =>
      have ht6 : t.weight ≤ 6 := hts t (by simp)
      have hwt5 : ((closeTerm t).2.map PairFactor.weight).sum ≤ 5 :=
        (closeTerm_weight ht6).trans (by norm_num)
      have hprod := prod_affine_of_weight_le_five hp hpPlus hpMinus hpos ho hR ht1 ht2 ht3
        (closeTerm t).2 hwt5
      have iht' := iht fun s hs => hts s (by simp [hs])
      simp only [List.map_cons, List.sum_cons, hprod, iht']
      ring
  rw [hsum_aff (expandWord w) (fun t ht => (expandWord_weight w t ht).trans hw)]
  ring

end AlbertSequential.MatchingModels
