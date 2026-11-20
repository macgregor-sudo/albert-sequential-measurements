/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationSectors
public import ThirteenTracesAndAform
public import NativeWordPositivity
public import NativeAtomCompression
import Mathlib.Tactic.LinearCombination

/-! Sparse native coordinates for the repeated C,D,C word in companion Proposition 2.7. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

private theorem octonionAdd_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem octonionAdd_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem octonionSMul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem octonionSMul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl

private theorem octonionChord_ext {x y : Octonion}
    (h0 : x.1.re = y.1.re) (h1 : x.1.imI = y.1.imI)
    (h2 : x.1.imJ = y.1.imJ) (h3 : x.1.imK = y.1.imK)
    (h4 : x.2.re = y.2.re) (h5 : x.2.imI = y.2.imI)
    (h6 : x.2.imJ = y.2.imJ) (h7 : x.2.imK = y.2.imK) : x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

theorem leftModelSpan_eq_normalForm (a b u x y z : ℝ) :
    leftModelSpan a b u x y z =
      octonionScalar u + x • octI + y • octJ + (a * z) • octK + (b * z) • octL := by
  apply octonionChord_ext <;>
    simp only [octonionAdd_fst, octonionAdd_snd, octonionSMul_fst, octonionSMul_snd,
      QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
      QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul] <;>
    simp [leftModelSpan, octonionScalar, octI, octJ, octK, octL]

private theorem span_C_entry (C1 C2 : ℝ) :
    octonionScalar C1 + C2 • octI = leftModelSpan 0 0 C1 C2 0 0 := by
  rw [leftModelSpan_eq_normalForm]
  simp

private theorem span_D_middle (x0 x1 x2 : ℝ) :
    octonionScalar x0 + x1 • octI + x2 • octJ = leftModelSpan 0 0 x0 x1 x2 0 := by
  rw [leftModelSpan_eq_normalForm]
  simp

private def leftModelCDCoordinates
    (a b C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 r : ℝ) : Octonion :=
  (⟨C0 * D0 + C1 * x0 + C2 * x1 + C3 * y0, C1 * x1 - C2 * x0 + C3 * y1,
      C1 * x2 + C3 * y2, -C2 * x2 + C3 * a * r⟩, ⟨C3 * b * r, 0, 0, 0⟩)

private theorem leftModelCD_inner
    (a b C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 r : ℝ) :
    octonionScalar (C0 * D0) +
        octonionMul (octonionConj (octonionScalar C1 + C2 • octI))
          (octonionScalar x0 + x1 • octI + x2 • octJ) +
        C3 • leftModelSpan a b y0 y1 y2 r =
      leftModelCDCoordinates a b C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 r := by
  rw [span_C_entry, span_D_middle]
  apply octonionChord_ext <;>
    simp only [octonionAdd_fst, octonionAdd_snd, octonionSMul_fst, octonionSMul_snd,
      QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
      QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul] <;>
    simp [octonionScalar, leftModelSpan, leftModelCDCoordinates, octonionMul, octonionConj] <;> ring

theorem leftModelSparseOverlapCD (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1)
    (B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 r : ℝ) :
    fpOverlap (sparseFourConfig B0 B1 C0 C1 C2 C3 D0 x0 x1 x2
      (leftModelSpan a b y0 y1 y2 r)) 2 3 =
      (C0 * D0 + C1 * x0 + C2 * x1 + C3 * y0)^2 +
        (C1 * x1 - C2 * x0 + C3 * y1)^2 + (C1 * x2 + C3 * y2)^2 +
        (C2 * x2)^2 + (C3 * r)^2 - 2 * C2 * x2 * C3 * r * a := by
  have ht := sparseFourConfigOct_traces B0 B1 C0 C1 C2 C3 D0
    (octonionScalar x0 + x1 • octI + x2 • octJ) (leftModelSpan a b y0 y1 y2 r)
  have hCD := ht.2.2.2.2.2.1
  unfold sparseFourConfig
  rw [hCD, leftModelCD_inner, octNormSq_eq_coords]
  dsimp [leftModelCDCoordinates]
  linear_combination (C3 * r)^2 * h

theorem leftModelSquareChord (a b o0 o1 : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ((1 + a) / 2) * ((o0 + o1)^2 / 3) +
        ((1 - a) / 2) * ((o0 - o1)^2 / 3) - (o0 + o1 * a)^2 / 3 =
      b ^ 2 * o1 ^ 2 / 3 := by
  linear_combination -(o1 ^ 2 / 3) * h

theorem leftModelDefectCoefficient (a b : ℝ)
    (B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 r : ℝ)
    (hB : B0 ^ 2 + B1 ^ 2 = 1)
    (hA : 0 < fourPointInvariant
      (sparseFourConfig B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 (leftModelSpan a b y0 y1 y2 r))) :
    let p := sparseFourConfig B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 (leftModelSpan a b y0 y1 y2 r)
    b ^ 2 * (2 * C2 * x2 * C3 * r)^2 / 3 =
      (4 / 3) * fourPointInvariant p /
        (fpOverlap p 0 1 * (1 - fpOverlap p 0 1)^2 * fpOverlap p 0 2 * fpOverlap p 0 3) := by
  let X := octonionScalar x0 + x1 • octI + x2 • octJ
  let Y := leftModelSpan a b y0 y1 y2 r
  let p := sparseFourConfig B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 Y
  change 0 < fourPointInvariant p at hA
  change _ = (4 / 3) * fourPointInvariant p /
    (fpOverlap p 0 1 * (1 - fpOverlap p 0 1)^2 * fpOverlap p 0 2 * fpOverlap p 0 3)
  have ht := sparseFourConfigOct_traces B0 B1 C0 C1 C2 C3 D0 X Y
  have hinv : fourPointInvariant p =
      B0 ^ 2 * B1 ^ 4 * C0 ^ 2 * C2 ^ 2 * C3 ^ 2 * D0 ^ 2 * x2 ^ 2 * (b * r) ^ 2 := by
    dsimp only [p, Y]
    rw [leftModelSpan_eq_normalForm, sparseFourConfig_fourPointInvariant]
  have hB1 : 1 - B0 ^ 2 = B1 ^ 2 := by linarith
  rw [show fpOverlap p 0 1 = B0 ^ 2 from ht.1, show fpOverlap p 0 2 = C0 ^ 2 from ht.2.1,
    show fpOverlap p 0 3 = D0 ^ 2 from ht.2.2.1, hB1, hinv]
  have hden : B0 ^ 2 * (B1 ^ 2)^2 * C0 ^ 2 * D0 ^ 2 ≠ 0 := by
    intro hz
    rw [hinv] at hA
    have hzero : B0 ^ 2 * B1 ^ 4 * C0 ^ 2 * C2 ^ 2 * C3 ^ 2 * D0 ^ 2 * x2 ^ 2 * (b * r)^2 = 0 := by
      linear_combination C2 ^ 2 * C3 ^ 2 * x2 ^ 2 * (b * r)^2 * hz
    exact hA.ne' hzero
  apply (eq_div_iff hden).2
  ring


def leftModelChord (a x y : ℝ) : ℝ := ((1 + a) / 2) * x + ((1 - a) / 2) * y

theorem leftModelSparseTraceChord
    (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1)
    (B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 r : ℝ) :
    let p := fun s t => sparseFourConfig B0 B1 C0 C1 C2 C3 D0 x0 x1 x2
      (leftModelSpan s t y0 y1 y2 r)
    ∀ i, fourPointTraceVec (p a b) i =
      leftModelChord a (fourPointTraceVec (p 1 0) i) (fourPointTraceVec (p (-1) 0) i) := by
  let X := octonionScalar x0 + x1 • octI + x2 • octJ
  let z := octonionScalar C1 + C2 • octI
  let p := fun s t => sparseFourConfig B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 (leftModelSpan s t y0 y1 y2 r)
  let g1 := octonionScalar (B0 * C0) + B1 • z
  let g2 := octonionScalar (B0 * D0) + B1 • X
  let g3 := fun s t => octonionScalar (C0 * D0) + octonionMul (octonionConj z) X +
    C3 • leftModelSpan s t y0 y1 y2 r
  have htr (s t : ℝ) := sparseFourConfigOct_traces B0 B1 C0 C1 C2 C3 D0 X (leftModelSpan s t y0 y1 y2 r)
  have hg1 : g1.2 = 0 := by
    unfold g1 z
    rw [octonionAdd_snd, octonionSMul_snd, span_C_entry]
    simp [octonionScalar, leftModelSpan]; rfl
  have hg2 : g2.2 = 0 := by
    unfold g2 X
    rw [octonionAdd_snd, octonionSMul_snd, span_D_middle]
    simp [octonionScalar, leftModelSpan]; rfl
  have hG (s t : ℝ) : g3 s t = leftModelCDCoordinates s t C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 r :=
    leftModelCD_inner s t C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 r
  have hsplit : (g3 a b).1 = ((1 + a) / 2) • (g3 1 0).1 + ((1 - a) / 2) • (g3 (-1) 0).1 := by
    rw [hG a b, hG 1 0, hG (-1) 0]
    ext <;> simp only [leftModelCDCoordinates, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul] <;> ring
  have hreal (f : Quaternion ℝ →ₗ[ℝ] ℝ) :
      f (g3 a b).1 = leftModelChord a (f (g3 1 0).1) (f (g3 (-1) 0).1) := by
    rw [hsplit, map_add, map_smul, map_smul]
    rfl
  have hR (s t : ℝ) :
      octonionReal (octonionMul (octonionMul g1 (g3 s t)) (octonionConj g2)) =
        (g1.1 * (g3 s t).1 * star g2.1).re := by
    unfold octonionReal octonionConj octonionMul
    change ((g1.1 * (g3 s t).1 - star (g3 s t).2 * g1.2) * star g2.1 -
      star (-g2.2) * _).re = _
    rw [hg1, hg2]
    simp
  have hU (s t : ℝ) :
      octonionReal (octonionMul g1 (g3 s t)) = (g1.1 * (g3 s t).1).re := by
    change (g1.1 * (g3 s t).1 - star (g3 s t).2 * g1.2).re = _
    rw [hg1, mul_zero, sub_zero]
  have hV (s t : ℝ) :
      octonionReal (octonionMul g2 (octonionConj (g3 s t))) =
        (g2.1 * star (g3 s t).1).re := by
    change (g2.1 * star (g3 s t).1 - star (-(g3 s t).2) * g2.2).re = _
    rw [hg2, mul_zero, sub_zero]
  let f0 : Quaternion ℝ →ₗ[ℝ] ℝ := QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)
  let f1 : Quaternion ℝ →ₗ[ℝ] ℝ := (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).comp (LinearMap.mulLeft ℝ g1.1)
  let f2 : Quaternion ℝ →ₗ[ℝ] ℝ :=
    (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).comp ((LinearMap.mulRight ℝ (star g2.1)).comp (LinearMap.mulLeft ℝ g1.1))
  let f3 : Quaternion ℝ →ₗ[ℝ] ℝ :=
    (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).comp ((LinearMap.mulLeft ℝ g2.1).comp (starLinearEquiv ℝ).toLinearMap)
  have c0 := hreal f0
  have c1 := hreal f1
  have c2 := hreal f2
  have c3 := hreal f3
  change octonionReal (g3 a b) =
    leftModelChord a (octonionReal (g3 1 0)) (octonionReal (g3 (-1) 0)) at c0
  change (g1.1 * (g3 a b).1).re =
    leftModelChord a (g1.1 * (g3 1 0).1).re (g1.1 * (g3 (-1) 0).1).re at c1
  change (g1.1 * (g3 a b).1 * star g2.1).re =
    leftModelChord a (g1.1 * (g3 1 0).1 * star g2.1).re (g1.1 * (g3 (-1) 0).1 * star g2.1).re at c2
  change (g2.1 * star (g3 a b).1).re =
    leftModelChord a (g2.1 * star (g3 1 0).1).re (g2.1 * star (g3 (-1) 0).1).re at c3
  have om1 : fpOmega1 (p a b) = leftModelChord a (fpOmega1 (p 1 0)) (fpOmega1 (p (-1) 0)) := by
    unfold p sparseFourConfig
    rw [(htr a b).2.2.2.2.2.2.2.2.2.2.1, (htr 1 0).2.2.2.2.2.2.2.2.2.2.1,
      (htr (-1) 0).2.2.2.2.2.2.2.2.2.2.1]
    unfold leftModelChord
    ring
  have om2 : fpOmega2 (p a b) = leftModelChord a (fpOmega2 (p 1 0)) (fpOmega2 (p (-1) 0)) := by
    unfold p sparseFourConfig
    rw [(htr a b).2.2.2.2.2.2.2.2.2.2.2.1, (htr 1 0).2.2.2.2.2.2.2.2.2.2.2.1,
      (htr (-1) 0).2.2.2.2.2.2.2.2.2.2.2.1]
    change B0 * D0 * octonionReal (octonionMul g1 (g3 a b)) =
      leftModelChord a (B0 * D0 * octonionReal (octonionMul g1 (g3 1 0)))
        (B0 * D0 * octonionReal (octonionMul g1 (g3 (-1) 0)))
    rw [hU, hU, hU, c1]
    unfold leftModelChord
    ring
  have om3 : fpOmega3 (p a b) = leftModelChord a (fpOmega3 (p 1 0)) (fpOmega3 (p (-1) 0)) := by
    unfold p sparseFourConfig
    rw [(htr a b).2.2.2.2.2.2.2.2.2.2.2.2, (htr 1 0).2.2.2.2.2.2.2.2.2.2.2.2,
      (htr (-1) 0).2.2.2.2.2.2.2.2.2.2.2.2]
    change B0 * C0 * octonionReal (octonionMul g2 (octonionConj (g3 a b))) =
      leftModelChord a (B0 * C0 * octonionReal (octonionMul g2 (octonionConj (g3 1 0))))
        (B0 * C0 * octonionReal (octonionMul g2 (octonionConj (g3 (-1) 0))))
    rw [hV, hV, hV, c3]
    unfold leftModelChord
    ring
  -- The six overlaps, four triangles and three Omega identities use the source ordering.
  change ∀ i, fourPointTraceVec (p a b) i =
    leftModelChord a (fourPointTraceVec (p 1 0) i) (fourPointTraceVec (p (-1) 0) i)
  intro i
  fin_cases i <;> simp only [fourPointTraceVec, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
    | (unfold p sparseFourConfig; rw [(htr a b).1, (htr 1 0).1, (htr (-1) 0).1]; unfold leftModelChord; ring)
    | (unfold p sparseFourConfig; rw [(htr a b).2.1, (htr 1 0).2.1, (htr (-1) 0).2.1]; unfold leftModelChord; ring)
    | (unfold p sparseFourConfig; rw [(htr a b).2.2.1, (htr 1 0).2.2.1, (htr (-1) 0).2.2.1]; unfold leftModelChord; ring)
    | (unfold p sparseFourConfig; rw [(htr a b).2.2.2.1, (htr 1 0).2.2.2.1, (htr (-1) 0).2.2.2.1]; unfold leftModelChord; ring)
    | (unfold p sparseFourConfig; rw [(htr a b).2.2.2.2.1, (htr 1 0).2.2.2.2.1, (htr (-1) 0).2.2.2.2.1]; unfold leftModelChord; ring)
    | (unfold p; rw [leftModelSparseOverlapCD a b h, leftModelSparseOverlapCD 1 0 (by norm_num),
        leftModelSparseOverlapCD (-1) 0 (by norm_num)]; unfold leftModelChord; ring)
    | (unfold p sparseFourConfig; rw [(htr a b).2.2.2.2.2.2.1, (htr 1 0).2.2.2.2.2.2.1,
        (htr (-1) 0).2.2.2.2.2.2.1]; unfold leftModelChord; ring)
    | (unfold p sparseFourConfig; rw [(htr a b).2.2.2.2.2.2.2.1, (htr 1 0).2.2.2.2.2.2.2.1,
        (htr (-1) 0).2.2.2.2.2.2.2.1]; unfold leftModelChord; ring)
    | (unfold p sparseFourConfig; rw [(htr a b).2.2.2.2.2.2.2.2.1, (htr 1 0).2.2.2.2.2.2.2.2.1,
        (htr (-1) 0).2.2.2.2.2.2.2.2.1]
       change C0 * D0 * octonionReal (g3 a b) = leftModelChord a
         (C0 * D0 * octonionReal (g3 1 0)) (C0 * D0 * octonionReal (g3 (-1) 0))
       rw [c0]; unfold leftModelChord; ring)
    | (unfold p sparseFourConfig; rw [(htr a b).2.2.2.2.2.2.2.2.2.1, (htr 1 0).2.2.2.2.2.2.2.2.2.1,
        (htr (-1) 0).2.2.2.2.2.2.2.2.2.1]
       change octonionReal (octonionMul (octonionMul g1 (g3 a b)) (octonionConj g2)) = _
       rw [hR, hR, hR, c2])
    | (simp only [fpOmega1, fpOmega2, fpOmega3, leftModelChord] at om1 om2 om3 ⊢
       linarith only [om1, om2, om3])


theorem nativeTracialTwoOutcomes {ι : Type*} (p : ι → Albert) (hp : ∀ i, IsAtom (p i))
    (x y : Outcome ι) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) [x, y] =
      (1 / 3) * tracePairing (nativeOutcome p x) (nativeOutcome p y) := by
  rw [nativeWordProbability_eq_pairing, tracePairing_smul_left]
  change (1 / 3 : ℝ) * tracePairing albertUnit
      (quadraticMap (nativeOutcome p x) (quadraticMap (nativeOutcome p y) albertUnit)) = _
  rw [quadraticMap_unit_argument, nativeOutcome_idempotent p (fun i => (hp i).1),
    tracePairing_comm albertUnit, tracePairing_unit_right, albertTrace_quadraticMap,
    nativeOutcome_idempotent p (fun i => (hp i).1)]

theorem nativeTracialRepeatedAtom {ι : Type*} (p : ι → Albert) (hp : ∀ i, IsAtom (p i))
    (i j : ι) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, true), (i, true)] =
      tracePairing (p i) (p j) ^ 2 / 3 := by
  rw [nativeWordProbability_eq_pairing, tracePairing_smul_left]
  change (1 / 3 : ℝ) * tracePairing albertUnit
      (quadraticMap (p i) (quadraticMap (p j) (quadraticMap (p i) albertUnit))) = _
  rw [quadraticMap_unit_argument, (hp i).1, quadraticMap_atom (p j) (p i) (hp j),
    quadraticMap_smul_right, quadraticMap_atom (p i) (p j) (hp i),
    tracePairing_smul_right, tracePairing_smul_right,
    tracePairing_comm albertUnit, tracePairing_unit_right,
    (hp i).2, tracePairing_comm (p j) (p i)]
  ring

private theorem leftModelUnitTrace : albertTrace albertUnit = 3 := by
  unfold albertTrace albertUnit
  rw [Fin.sum_univ_three]
  norm_num

theorem nativeTracialShortWordChord {ι : Type*}
    (a : ℝ) (p pPlus pMinus : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (hPlus : ∀ i, IsAtom (pPlus i)) (hMinus : ∀ i, IsAtom (pMinus i))
    (hPair : ∀ i j, tracePairing (p i) (p j) =
      leftModelChord a (tracePairing (pPlus i) (pPlus j)) (tracePairing (pMinus i) (pMinus j)))
    (w : Word ι) (hw : w.length ≤ 2) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w =
      leftModelChord a
        (nativeWordProbability pPlus ((1 / 3 : ℝ) • albertUnit) w)
        (nativeWordProbability pMinus ((1 / 3 : ℝ) • albertUnit) w) := by
  have hnil (q : ι → Albert) :
      nativeWordProbability q ((1 / 3 : ℝ) • albertUnit) [] = 1 := by
    change albertTrace ((1 / 3 : ℝ) • albertUnit) = 1
    rw [albertTrace_smul, leftModelUnitTrace]
    norm_num
  have hone (q : ι → Albert) (hq : ∀ i, IsAtom (q i)) (x : Outcome ι) :
      nativeWordProbability q ((1 / 3 : ℝ) • albertUnit) [x] =
        if x.2 then 1 / 3 else 2 / 3 := by
    rw [nativeWordProbability_eq_pairing, tracePairing_smul_left]
    change (1 / 3 : ℝ) * tracePairing albertUnit (quadraticMap (nativeOutcome q x) albertUnit) = _
    rw [quadraticMap_unit_argument, nativeOutcome_idempotent q (fun i => (hq i).1),
      tracePairing_comm albertUnit, tracePairing_unit_right]
    rcases x with ⟨i,b⟩
    cases b
    · change (1 / 3 : ℝ) * albertTrace (albertUnit - q i) = 2 / 3
      rw [albertTrace_sub, leftModelUnitTrace, (hq i).2]
      norm_num
    · change (1 / 3 : ℝ) * albertTrace (q i) = 1 / 3
      rw [(hq i).2, mul_one]
  cases w with
  | nil => rw [hnil, hnil, hnil]; unfold leftModelChord; ring
  | cons x w =>
    cases w with
    | nil => rw [hone p hp, hone pPlus hPlus, hone pMinus hMinus]; unfold leftModelChord; ring
    | cons y w =>
      have hw' : w = [] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons] at hw
        omega)
      subst w
      rw [nativeTracialTwoOutcomes _ hp, nativeTracialTwoOutcomes _ hPlus, nativeTracialTwoOutcomes _ hMinus]
      obtain ⟨i,b⟩ := x
      obtain ⟨j,c⟩ := y
      have hleft (x : Albert) : tracePairing albertUnit x = albertTrace x := by
        rw [tracePairing_comm, tracePairing_unit_right]
      cases b <;> cases c <;>
        simp only [nativeOutcome, Bool.false_eq_true, ↓reduceIte,
          tracePairing_sub_left, tracePairing_sub_right, hleft, tracePairing_unit_right, albertTrace_sub,
          leftModelUnitTrace, (hp i).2, (hp j).2, (hPlus i).2, (hPlus j).2,
          (hMinus i).2, (hMinus j).2, hPair] <;>
        unfold leftModelChord <;> ring

end AlbertSequential.NativeAnalysis
