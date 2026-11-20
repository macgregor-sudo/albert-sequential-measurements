/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationChord
public import CompanionLeftMultiplicationQuaternionTrace
import Mathlib.Tactic.FinCases

/-! The actual sparse normal-form columns and their two quaternionic endpoints. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix
namespace AlbertSequential.NativeAnalysis

structure LeftModelNormalForm where
  B0 : ℝ
  B1 : ℝ
  C0 : ℝ
  C1 : ℝ
  C2 : ℝ
  C3 : ℝ
  D0 : ℝ
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  y0 : ℝ
  y1 : ℝ
  y2 : ℝ
  r : ℝ
  normB : B0 ^ 2 + B1 ^ 2 = 1
  normC : C0 ^ 2 + C1 ^ 2 + C2 ^ 2 + C3 ^ 2 = 1
  normD : D0 ^ 2 + x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + r ^ 2 = 1

def LeftModelNormalForm.coefficients (f : LeftModelNormalForm) : Fin 4 → Fin 3 → Fin 4 → ℝ :=
  ![![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![f.B0, 0, 0, 0], ![f.B1, 0, 0, 0], ![0, 0, 0, 0]],
    ![![f.C0, 0, 0, 0], ![f.C1, f.C2, 0, 0], ![f.C3, 0, 0, 0]],
    ![![f.D0, 0, 0, 0], ![f.x0, f.x1, f.x2, 0], ![f.y0, f.y1, f.y2, f.r]]]

def LeftModelNormalForm.atoms (f : LeftModelNormalForm) (a b : ℝ) : Fin 4 → Albert :=
  sparseFourConfig f.B0 f.B1 f.C0 f.C1 f.C2 f.C3 f.D0 f.x0 f.x1 f.x2
    (leftModelSpan a b f.y0 f.y1 f.y2 f.r)

private theorem leftModelSpan_normSq (a b u x y z : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    octNormSq (leftModelSpan a b u x y z) = u ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 := by
  rw [octNormSq_eq_coords]
  dsimp [leftModelSpan]
  linear_combination z ^ 2 * h

theorem LeftModelNormalForm.column_norm (f : LeftModelNormalForm) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (i : Fin 4) :
    octonionColumnNormSq (leftModelSpanColumn a b (f.coefficients i)) = 1 := by
  unfold octonionColumnNormSq
  simp only [leftModelSpanColumn, leftModelSpan_normSq _ _ _ _ _ _ h, Fin.sum_univ_three]
  fin_cases i <;> norm_num [LeftModelNormalForm.coefficients]
  · linarith [f.normB]
  · linarith [f.normC]
  · linarith [f.normD]

private theorem LeftModelNormalForm.column_first (f : LeftModelNormalForm) (a b : ℝ) (i : Fin 4) :
    leftModelSpanColumn a b (f.coefficients i) 0 =
      octonionScalar (f.coefficients i 0 0) := by
  fin_cases i <;>
    simp [LeftModelNormalForm.coefficients, leftModelSpanColumn, leftModelSpan_eq_normalForm]

theorem LeftModelNormalForm.atom_eq (f : LeftModelNormalForm) (a b : ℝ) (i : Fin 4) :
    f.atoms a b i = octDyad (leftModelSpanColumn a b (f.coefficients i)) := by
  fin_cases i <;>
    simp only [LeftModelNormalForm.atoms, sparseFourConfig, sparseFourConfigOct,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    apply congrArg octDyad <;> funext j <;> fin_cases j <;>
    simp [LeftModelNormalForm.coefficients, leftModelSpanColumn, leftModelSpan_eq_normalForm,
      show octonionScalar 0 = 0 from rfl]

theorem LeftModelNormalForm.isAtom (f : LeftModelNormalForm) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (i : Fin 4) : IsAtom (f.atoms a b i) := by
  let v := leftModelSpanColumn a b (f.coefficients i)
  let s := f.coefficients i 0 0
  have hcol : v = ![octonionScalar s, v 1, v 2] := by
    funext k
    fin_cases k
    · exact f.column_first a b i
    · rfl
    · rfl
  have hs : octNormSq (octonionScalar s) = s ^ 2 := by
    rw [octNormSq_eq_coords]
    simp [octonionScalar]
  have hn := f.column_norm a b h i
  change octonionColumnNormSq v = 1 at hn
  rw [f.atom_eq, show leftModelSpanColumn a b (f.coefficients i) = v from rfl, hcol]
  apply octDyad_real0_isAtom
  rw [octonionColumnNormSq, Fin.sum_univ_three,
    show v 0 = octonionScalar s from f.column_first a b i, hs] at hn
  exact hn

theorem LeftModelNormalForm.positiveInvariant_sine (f : LeftModelNormalForm) (a b : ℝ)
    (hA : 0 < fourPointInvariant (f.atoms a b)) : b ≠ 0 := by
  rintro rfl
  rw [LeftModelNormalForm.atoms, leftModelSpan_eq_normalForm, sparseFourConfig_fourPointInvariant] at hA
  norm_num at hA

private theorem leftModelSpan_axis (s u x y z : ℝ) :
    leftModelSpan s 0 u x y z = quatEmbed1 (leftModelQuaternion s u x y z) := by
  apply Prod.ext
  · rfl
  · simp [leftModelSpan, quatEmbed1_apply]; rfl

def LeftModelNormalForm.quaternionicDyad (f : LeftModelNormalForm) (s : ℝ)
    (i : Fin 4) : QuatHermitian3 :=
  ⟨quaternionColumnDyad (leftModelQuatColumn s (f.coefficients i)), by
    rw [selfAdjoint.mem_iff]
    apply Matrix.ext
    intro j k
    change star (leftModelQuatColumn s (f.coefficients i) k *
        star (leftModelQuatColumn s (f.coefficients i) j)) = _
    rw [star_mul, star_star]
    rfl⟩

theorem LeftModelNormalForm.quaternionicDyad_embedding (f : LeftModelNormalForm) (s : ℝ) (i : Fin 4) :
    standardQuaternionicWindow.embedding (f.quaternionicDyad s i) = f.atoms s 0 i := by
  rw [f.atom_eq, standardQuaternionicWindow, quaternionicWindowOfQuatEmbedding_apply]
  have hv (j : Fin 3) : leftModelSpanColumn s 0 (f.coefficients i) j =
      quatEmbed1 (leftModelQuatColumn s (f.coefficients i) j) := leftModelSpan_axis _ _ _ _ _
  apply Prod.ext
  · funext j
    change (leftModelQuatColumn s (f.coefficients i) j *
      star (leftModelQuatColumn s (f.coefficients i) j)).re = octNormSq _
    rw [hv, octNormSq, octDot, ← quatEmbed1_isQuatEmbedding.map_star, ← quatEmbed1_isQuatEmbedding.map_mul]
    rfl
  · funext j
    fin_cases j <;>
      simp [LeftModelNormalForm.quaternionicDyad, quaternionColumnDyad, octDyad,
        quatMatrixToAlbert, hv, quatEmbed1_isQuatEmbedding.map_mul, quatEmbed1_isQuatEmbedding.map_star]

theorem LeftModelNormalForm.quaternionicProjection_representation (f : LeftModelNormalForm)
    (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) (s : ℝ) (i : Fin 4) :
    leftModelQuaternionProjection a b s (f.coefficients i) =
      leftQuaternionMatrixRepresentation (f.quaternionicDyad s i : QuatMatrix3) := by
  rw [leftModelQuaternionProjection, f.column_norm a b h, inv_one, one_smul]
  have hm := leftQuaternionMatrixRepresentation_columnDyad (leftModelQuatColumn s (f.coefficients i)) 1
  simpa [LeftModelNormalForm.quaternionicDyad] using hm.symm


def LeftModelNormalForm.projections (f : LeftModelNormalForm) (a b : ℝ) :
    Fin 4 → Matrix AlbertColumnCoordinate AlbertColumnCoordinate ℝ :=
  fun i => octonionLeftProjection (leftModelSpanColumn a b (f.coefficients i))

theorem LeftModelNormalForm.weightedProbability (f : LeftModelNormalForm) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (hA : 0 < fourPointInvariant (f.atoms a b)) :
    ∃ c d : ℝ,
      let VPlus := leftModelSectorFrame c d
      let VMinus := leftModelSectorFrame (-d) c
      let D := leftModelDensity a VPlus VMinus
      (∀ i, (f.projections a b i).rank = 8) ∧
      (leftModelSectorProjection VPlus).rank = 12 ∧
      (leftModelSectorProjection VMinus).rank = 12 ∧
      VPlusᵀ * VMinus = 0 ∧
      leftModelSectorProjection VPlus + leftModelSectorProjection VMinus = 1 ∧
      (∀ i, f.projections a b i * VPlus = VPlus * leftModelQuaternionProjection a b 1 (f.coefficients i) ∧
        f.projections a b i * VMinus = VMinus * leftModelQuaternionProjection a b (-1) (f.coefficients i)) ∧
      D.PosSemidef ∧ D.trace = 1 ∧
      ∀ w : Word (Fin 4), (D * wordOperator (f.projections a b) w).trace =
        leftModelChord a (nativeWordProbability (f.atoms 1 0) ((1 / 3 : ℝ) • albertUnit) w)
          (nativeWordProbability (f.atoms (-1) 0) ((1 / 3 : ℝ) • albertUnit) w) := by
  have hv i : 0 < octonionColumnNormSq (leftModelSpanColumn a b (f.coefficients i)) := by
    rw [f.column_norm a b h]
    norm_num
  obtain ⟨c, d, h8, h12Plus, h12Minus, horth, hsplit, hinter, hpsd, htrace, hprob⟩ :=
    leftModelLiteralWeightedModel a b h (f.positiveInvariant_sine a b hA) f.coefficients hv
  refine ⟨c, d, h8, h12Plus, h12Minus, horth, hsplit, hinter, hpsd, htrace, ?_⟩
  intro w
  rw [show (leftModelDensity a (leftModelSectorFrame c d) (leftModelSectorFrame (-d) c) *
      wordOperator (f.projections a b) w).trace = _ from hprob w]
  have hbranch (s : ℝ) : (wordOperator (fun i => leftModelQuaternionProjection a b s (f.coefficients i)) w).trace / 12 =
      nativeWordProbability (f.atoms s 0) ((1 / 3 : ℝ) • albertUnit) w := by
    rw [show (fun i => leftModelQuaternionProjection a b s (f.coefficients i)) =
        (fun i => leftQuaternionMatrixRepresentation (f.quaternionicDyad s i : QuatMatrix3))
        from funext (f.quaternionicProjection_representation a b h s),
      leftQuaternionMatrixRepresentation_wordProbability standardQuaternionicWindow,
      show (fun i => standardQuaternionicWindow.embedding (f.quaternionicDyad s i)) = f.atoms s 0
        from funext (f.quaternionicDyad_embedding s)]
  rw [hbranch 1, hbranch (-1)]
  unfold leftModelWeight leftModelChord
  ring

theorem LeftModelNormalForm.traceChord (f : LeftModelNormalForm) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (i : Fin 13) :
    fourPointTraceVec (f.atoms a b) i =
      leftModelChord a (fourPointTraceVec (f.atoms 1 0) i) (fourPointTraceVec (f.atoms (-1) 0) i) :=
  leftModelSparseTraceChord a b h f.B0 f.B1 f.C0 f.C1 f.C2 f.C3 f.D0
    f.x0 f.x1 f.x2 f.y0 f.y1 f.y2 f.r i

set_option maxHeartbeats 800000 in
theorem LeftModelNormalForm.shortWordChord (f : LeftModelNormalForm) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (w : Word (Fin 4)) (hw : w.length ≤ 2) :
    nativeWordProbability (f.atoms a b) ((1 / 3 : ℝ) • albertUnit) w =
      leftModelChord a (nativeWordProbability (f.atoms 1 0) ((1 / 3 : ℝ) • albertUnit) w)
        (nativeWordProbability (f.atoms (-1) 0) ((1 / 3 : ℝ) • albertUnit) w) := by
  have hp := f.isAtom a b h
  have hPlus := f.isAtom 1 0 (by norm_num)
  have hMinus := f.isAtom (-1) 0 (by norm_num)
  apply nativeTracialShortWordChord _ _ _ _ hp hPlus hMinus _ w hw
  have hrefl (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (i : Fin 4) :
      tracePairing (p i) (p i) = 1 := by
    rw [tracePairing, (hp i).1, (hp i).2]
  have h01 := f.traceChord a b h 0
  have h02 := f.traceChord a b h 1
  have h03 := f.traceChord a b h 2
  have h12 := f.traceChord a b h 3
  have h13 := f.traceChord a b h 4
  have h23 := f.traceChord a b h 5
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | (rw [hrefl _ hp, hrefl _ hPlus, hrefl _ hMinus]; unfold leftModelChord; ring)
    | exact h01
    | exact h02
    | exact h03
    | exact h12
    | exact h13
    | exact h23
    | (rw [tracePairing_comm ((f.atoms a b) _) _, tracePairing_comm ((f.atoms 1 0) _) _,
        tracePairing_comm ((f.atoms (-1) 0) _) _]
       first
       | exact h01
       | exact h02
       | exact h03
       | exact h12
       | exact h13
       | exact h23)

def leftModelCDC : Word (Fin 4) := [(2, true), (3, true), (2, true)]

theorem LeftModelNormalForm.nativeChordDefect (f : LeftModelNormalForm) (a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (hA : 0 < fourPointInvariant (f.atoms a b)) :
    let p := f.atoms a b
    leftModelChord a (nativeWordProbability (f.atoms 1 0) ((1 / 3 : ℝ) • albertUnit) leftModelCDC)
        (nativeWordProbability (f.atoms (-1) 0) ((1 / 3 : ℝ) • albertUnit) leftModelCDC) -
        nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) leftModelCDC =
      (4 / 3) * fourPointInvariant p /
        (fpOverlap p 0 1 * (1 - fpOverlap p 0 1)^2 * fpOverlap p 0 2 * fpOverlap p 0 3) := by
  dsimp only
  rw [leftModelCDC, nativeTracialRepeatedAtom _ (f.isAtom 1 0 (by norm_num)),
    nativeTracialRepeatedAtom _ (f.isAtom (-1) 0 (by norm_num)),
    nativeTracialRepeatedAtom _ (f.isAtom a b h)]
  change leftModelChord a ((fpOverlap (f.atoms 1 0) 2 3)^2 / 3)
      ((fpOverlap (f.atoms (-1) 0) 2 3)^2 / 3) - (fpOverlap (f.atoms a b) 2 3)^2 / 3 = _
  unfold LeftModelNormalForm.atoms
  rw [leftModelSparseOverlapCD 1 0 (by norm_num), leftModelSparseOverlapCD (-1) 0 (by norm_num),
    leftModelSparseOverlapCD a b h, ← leftModelDefectCoefficient a b f.B0 f.B1 f.C0 f.C1 f.C2 f.C3 f.D0
      f.x0 f.x1 f.x2 f.y0 f.y1 f.y2 f.r f.normB hA]
  unfold leftModelChord
  ring_nf
  linear_combination -(4 * f.C2^2 * f.x2^2 * f.C3^2 * f.r^2 / 3) * h

end AlbertSequential.NativeAnalysis
