/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationNormalForm
public import MatchingModels.DfailsModel
import Mathlib.Tactic.LinearCombination

/-! Literal short-word agreement and first purity deviation of companion Proposition 2.7. -/
@[expose] public section
noncomputable section
open scoped Matrix
namespace AlbertSequential.NativeAnalysis
open MatchingModels

def leftModelNativeTraceVector (prob : Word (Fin 4) → ℝ) : Fin 13 → ℝ :=
  ![wordExtractOverlap prob 0 1, wordExtractOverlap prob 0 2, wordExtractOverlap prob 0 3,
    wordExtractOverlap prob 1 2, wordExtractOverlap prob 1 3, wordExtractOverlap prob 2 3,
    wordExtractTriangle prob 0 1 2, wordExtractTriangle prob 0 1 3, wordExtractTriangle prob 0 2 3,
    wordExtractDoublePair prob 0 1 2 3, wordExtractDoublePair prob 0 2 1 3,
    wordExtractDoublePair prob 0 3 1 2, wordExtractTriangle prob 1 2 3]

private theorem nativeYesFirst (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (i : Fin 4) (w : Word (Fin 4)) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) ((i, true) :: w) =
      (1 / 3) * nativeWordProbability p (p i) w := by
  change nativeWordProbability p (quadraticMap (p i) ((1 / 3 : ℝ) • albertUnit)) w = _
  rw [quadraticMap_smul_right, quadraticMap_unit_argument, (hp i).1, nativeWordProbability_smul]

private theorem nativeYesLast (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (x : Albert) (i : Fin 4) :
    nativeWordProbability p x [(i, true)] = tracePairing x (p i) := by
  rw [nativeWordProbability_eq_pairing]
  change tracePairing x (quadraticMap (p i) albertUnit) = _
  rw [quadraticMap_unit_argument, (hp i).1]

private theorem quadraticMap_middle_sum (p x : Albert) :
    x + quadraticMap p x - quadraticMap (albertUnit - p) x = (2 : ℝ) • jordanMul p x := by
  simp only [quadraticMap, jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
    jordanMul_albertUnit_right, two_smul]
  abel

private theorem nativeMiddleSum (p : Fin 4 → Albert) (x : Albert)
    (i : Fin 4) (w : Word (Fin 4)) :
    nativeWordProbability p x w + nativeWordProbability p x ((i, true) :: w) -
        nativeWordProbability p x ((i, false) :: w) =
      nativeWordProbability p ((2 : ℝ) • jordanMul (p i) x) w := by
  change nativeWordProbability p x w + nativeWordProbability p (quadraticMap (p i) x) w -
    nativeWordProbability p (quadraticMap (albertUnit - p i) x) w = _
  simp only [nativeWordProbability_eq_pairing]
  rw [← tracePairing_add_left, ← tracePairing_sub_left, quadraticMap_middle_sum]

theorem leftModelWordExtractOverlap_native (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (i j : Fin 4) :
    wordExtractOverlap (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) i j = fpOverlap p i j := by
  rw [wordExtractOverlap, nativeYesFirst p hp, nativeYesLast p hp, fpOverlap]
  ring

theorem leftModelWordExtractTriangle_native (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (i j k : Fin 4) :
    wordExtractTriangle (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) i j k = fpTriangle p i j k := by
  rw [wordExtractTriangle, nativeYesFirst p hp, nativeYesFirst p hp, nativeYesFirst p hp]
  calc
    _ = (1 / 2 : ℝ) * (nativeWordProbability p (p i) [(k, true)] +
          nativeWordProbability p (p i) [(j, true), (k, true)] -
          nativeWordProbability p (p i) [(j, false), (k, true)]) := by ring
    _ = _ := by
      rw [nativeMiddleSum, nativeYesLast p hp, tracePairing_smul_left, jordanMul_comm (p j), fpTriangle]
      ring

theorem leftModelWordExtractDoublePair_native (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (a b c d : Fin 4) :
    wordExtractDoublePair (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) a b c d =
      tracePairing (jordanMul (p a) (p b)) (jordanMul (p c) (p d)) := by
  unfold wordExtractDoublePair
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.cons_append,
    List.nil_append, nativeYesFirst p hp, one_mul, neg_one_mul, add_zero]
  let x := p a
  let y := (2 : ℝ) • jordanMul (p b) x
  have h0 := nativeMiddleSum p x b [(d, true)]
  have h1 := nativeMiddleSum p x b [(c, true), (d, true)]
  have h2 := nativeMiddleSum p x b [(c, false), (d, true)]
  have hc := nativeMiddleSum p y c [(d, true)]
  change _ = _
  calc
    _ = (1 / 4 : ℝ) * (nativeWordProbability p y [(d, true)] +
      nativeWordProbability p y [(c, true), (d, true)] - nativeWordProbability p y [(c, false), (d, true)]) := by
        linear_combination (h0 + h1 - h2) / 4
    _ = _ := by
      rw [hc, nativeYesLast p hp, tracePairing_smul_left]
      unfold y x
      rw [jordanMul_smul_right, tracePairing_smul_left, jordanMul_comm (p c),
        tracePairing_associative, jordanMul_comm (p b) (p a)]
      ring

theorem leftModelNativeTraceVector_native (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (i : Fin 13) :
    leftModelNativeTraceVector (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) i =
      fourPointTraceVec p i := by
  fin_cases i <;>
    simp only [leftModelNativeTraceVector, fourPointTraceVec, Matrix.cons_val_zero', Matrix.cons_val_succ',
      leftModelWordExtractOverlap_native p hp, leftModelWordExtractTriangle_native p hp,
      leftModelWordExtractDoublePair_native p hp, fpDoublePair1, fpDoublePair2, fpDoublePair3]

theorem leftModelNativeTraceVector_chord (a : ℝ) (p q : Word (Fin 4) → ℝ) (i : Fin 13) :
    leftModelNativeTraceVector (fun w => leftModelChord a (p w) (q w)) i =
      leftModelChord a (leftModelNativeTraceVector p i) (leftModelNativeTraceVector q i) := by
  fin_cases i <;>
    simp only [leftModelNativeTraceVector, Matrix.cons_val_zero', Matrix.cons_val_succ',
      wordExtractOverlap, wordExtractTriangle, wordExtractDoublePair, leftModelChord,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
    ring


private theorem LeftModelNormalForm.defectDenominator_pos (f : LeftModelNormalForm) (a b : ℝ)
    (hA : 0 < fourPointInvariant (f.atoms a b)) :
    0 < fpOverlap (f.atoms a b) 0 1 * (1 - fpOverlap (f.atoms a b) 0 1)^2 *
      fpOverlap (f.atoms a b) 0 2 * fpOverlap (f.atoms a b) 0 3 := by
  have hA' := hA
  rw [LeftModelNormalForm.atoms, leftModelSpan_eq_normalForm,
    sparseFourConfig_fourPointInvariant] at hA'
  have hne : f.B0 ^ 2 * (f.B1 ^ 2)^2 * f.C0 ^ 2 * f.D0 ^ 2 ≠ 0 := by
    intro hz
    apply hA'.ne'
    linear_combination f.C2 ^ 2 * f.C3 ^ 2 * f.x2 ^ 2 * (b * f.r)^2 * hz
  have hB : 1 - f.B0 ^ 2 = f.B1 ^ 2 := by linarith [f.normB]
  have ht := sparseFourConfigOct_traces f.B0 f.B1 f.C0 f.C1 f.C2 f.C3 f.D0
    (octonionScalar f.x0 + f.x1 • octI + f.x2 • octJ) (leftModelSpan a b f.y0 f.y1 f.y2 f.r)
  rw [show fpOverlap (f.atoms a b) 0 1 = f.B0 ^ 2 from ht.1,
    show fpOverlap (f.atoms a b) 0 2 = f.C0 ^ 2 from ht.2.1,
    show fpOverlap (f.atoms a b) 0 3 = f.D0 ^ 2 from ht.2.2.1, hB]
  exact lt_of_le_of_ne (by positivity) hne.symm

theorem LeftModelNormalForm.literalFirstDeviation (f : LeftModelNormalForm) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (hA : 0 < fourPointInvariant (f.atoms a b)) :
    ∃ c d : ℝ,
      let p := f.atoms a b
      let P := f.projections a b
      let VPlus := leftModelSectorFrame c d
      let VMinus := leftModelSectorFrame (-d) c
      let density := leftModelDensity a VPlus VMinus
      let prob := fun w => (density * wordOperator P w).trace
      let native := nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
      let base := [(2, true)]
      let middle := [(2, true), (3, true)]
      let overlap := fpOverlap p 2 3
      let defect := prob leftModelCDC - native leftModelCDC
      (∀ i, (P i).rank = 8) ∧
      (leftModelSectorProjection VPlus).rank = 12 ∧
      (leftModelSectorProjection VMinus).rank = 12 ∧
      VPlusᵀ * VMinus = 0 ∧
      leftModelSectorProjection VPlus + leftModelSectorProjection VMinus = 1 ∧
      (∀ i, P i * VPlus = VPlus * leftModelQuaternionProjection a b 1 (f.coefficients i) ∧
        P i * VMinus = VMinus * leftModelQuaternionProjection a b (-1) (f.coefficients i)) ∧
      density.PosSemidef ∧ density.trace = 1 ∧
      (∀ w, w.length ≤ 2 → prob w = native w) ∧
      (∀ i, leftModelNativeTraceVector prob i = fourPointTraceVec p i) ∧
      defect = (4 / 3) * fourPointInvariant p /
        (fpOverlap p 0 1 * (1 - fpOverlap p 0 1)^2 * fpOverlap p 0 2 * fpOverlap p 0 3) ∧
      0 < defect ∧
      prob leftModelCDC - 2 * overlap * prob middle + overlap^2 * prob base = defect ∧
      native leftModelCDC - 2 * overlap * native middle + overlap^2 * native base = 0 := by
  obtain ⟨c, d, h8, h12Plus, h12Minus, horth, hsplit, hinter, hpsd, htrace, hprob⟩ :=
    f.weightedProbability a b h hA
  refine ⟨c, d, h8, h12Plus, h12Minus, horth, hsplit, hinter, hpsd, htrace, ?_⟩
  let p := f.atoms a b
  let native := nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
  let body := leftModelDensity a (leftModelSectorFrame c d) (leftModelSectorFrame (-d) c)
  let prob := fun w => (body * wordOperator (f.projections a b) w).trace
  have hp := f.isAtom a b h
  have hShort (w : Word (Fin 4)) (hw : w.length ≤ 2) : prob w = native w :=
    (hprob w).trans (f.shortWordChord a b h w hw).symm
  have hTraces (i : Fin 13) : leftModelNativeTraceVector prob i = fourPointTraceVec p i := by
    rw [show prob = _ from funext hprob, leftModelNativeTraceVector_chord,
      leftModelNativeTraceVector_native _ (f.isAtom 1 0 (by norm_num)),
      leftModelNativeTraceVector_native _ (f.isAtom (-1) 0 (by norm_num))]
    exact (f.traceChord a b h i).symm
  have hDefect : prob leftModelCDC - native leftModelCDC =
      (4 / 3) * fourPointInvariant p /
        (fpOverlap p 0 1 * (1 - fpOverlap p 0 1)^2 * fpOverlap p 0 2 * fpOverlap p 0 3) := by
    change (body * wordOperator (f.projections a b) leftModelCDC).trace - native leftModelCDC = _
    rw [show (body * wordOperator (f.projections a b) leftModelCDC).trace = _ from hprob leftModelCDC]
    exact f.nativeChordDefect a b h hA
  have hPos : 0 < prob leftModelCDC - native leftModelCDC := by
    rw [hDefect]
    exact div_pos (mul_pos (by norm_num) hA) (f.defectDenominator_pos a b hA)
  have hBase : native [(2, true)] = 1 / 3 := by
    unfold native
    rw [nativeYesFirst p hp]
    change (1 / 3 : ℝ) * albertTrace (p 2) = _
    rw [(hp 2).2, mul_one]
  have hMiddle : native [(2, true), (3, true)] = fpOverlap p 2 3 / 3 := by
    unfold native
    rw [nativeTracialTwoOutcomes p hp]
    change (1 / 3 : ℝ) * fpOverlap p 2 3 = _
    ring
  have hLong : native leftModelCDC = (fpOverlap p 2 3)^2 / 3 :=
    nativeTracialRepeatedAtom p hp 2 3
  refine ⟨hShort, hTraces, hDefect, hPos, ?_, ?_⟩
  · change prob leftModelCDC - 2 * fpOverlap p 2 3 * prob [(2, true), (3, true)] +
        (fpOverlap p 2 3)^2 * prob [(2, true)] =
      prob leftModelCDC - native leftModelCDC
    rw [hShort [(2, true), (3, true)] (by decide), hShort [(2, true)] (by decide), hBase, hMiddle, hLong]
    ring
  · change native leftModelCDC - 2 * fpOverlap p 2 3 * native [(2, true), (3, true)] +
        (fpOverlap p 2 3)^2 * native [(2, true)] = 0
    rw [hBase, hMiddle, hLong]
    ring

end AlbertSequential.NativeAnalysis
