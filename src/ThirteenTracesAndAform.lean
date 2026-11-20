/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Defs
public import Interfaces.Geometry
public import Interfaces.AlgebraicReconstruction
public import NativeAlbertLaws
public import NativeMatrixTrace
public import NativeAnalysis
public import FixedSBinding
public import OctonionGeometry
public import FrameSlotNormalizers
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Thirteen Traces, Rank-Three Trace Relation, `Aform`, `Dacal`, and Principal Trace Ideal

Formalizes:
1. Definition `def:traces` (`fpOverlap`, `fpTriangle`, `fpDoublePair1/2/3`, `fpOmega1/2/3`) and the
   16-term / 52-monomial four-point invariant `fourPointInvariant` (`eq:A:Acal52`), with
   `NativeAlbertAutomorphism` invariance and `Equiv.Perm (Fin 4)` symmetry (`S_4` via adjacent swaps).
2. General rank-three cubic-Jordan polarization `rankThree_fourIdempotent_trace_relation` (`prop:fp:tracerel`),
   its specialization to `Defs.Albert` (`albert_fourAtom_trace_relation`), and the rank-four
   excess/counterexample (`rem:fp:tracerel-rank(b)`).
3. Unrestricted normal-form polynomial identity `lem:A:Aform` (`sparseFourConfigOct` & `sparseFourConfig`)
   for ALL real parameters including `B0 = 0`, `C0 = 0`, `D0 = 0` via sparse dyad contractions,
   the denominator-free 12-line scalar 3x3 determinant bridge `fourPointOmegaPoly_det_poly`,
   Harvey–Lawson, and associator reduction, plus `fourPointInvariant_fixedS : fourPointInvariant fixedS = 1 / 5832`
   and the maximizer value `4 / 19683`.
4. The tetrahedral determinant identity `prop:Dacal` (`fpTetraDtet`, `prop_Dacal_poly`,
   `fpTetraDtet_perm_invariant`) for arbitrary base/order permutations and positive overlaps, plus
   the exact link to `tetrahedronDiscriminant`.
5. The explicit continuous triangular local inverse around `fixedS` (`triangularLocalInverse`)
   and principal-ideal theorem `fourAtom_trace_ideal_principal` (`rem:fp:tracerel-rank(a)`) via
   monic division in `MvPolynomial (Fin 13) ℝ`.

No `Mul`, `One`, `Star`, or `Norm` instance is installed on `Octonion` or `Albert`.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

open scoped Matrix

/-! ## Internal Carrier, Octonion, and Albert Coordinate Helpers -/

private theorem oct_add_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
private theorem oct_add_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
private theorem oct_smul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
private theorem oct_smul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl
private theorem oct_mul_fst (x y : Octonion) :
    (octonionMul x y).1 = x.1 * y.1 - star y.2 * x.2 := rfl
private theorem oct_mul_snd (x y : Octonion) :
    (octonionMul x y).2 = y.2 * x.1 + x.2 * star y.1 := rfl
private theorem oct_conj_fst (x : Octonion) : (octonionConj x).1 = star x.1 := rfl
private theorem oct_conj_snd (x : Octonion) : (octonionConj x).2 = -x.2 := rfl

private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (hu0 : x.2 0 = y.2 0) (hu1 : x.2 1 = y.2 1) (hu2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext i <;> fin_cases i
  · exact hd0
  · exact hd1
  · exact hd2
  · exact hu0
  · exact hu1
  · exact hu2

private theorem octonionReal_mul_conj_left (a b : Octonion) :
    octonionReal (octonionMul (octonionConj a) b) = octDot a b := by
  rw [octonionReal_mul_comm]
  exact octDot_comm b a

private theorem octonionReal_mul_conj_right (a b : Octonion) :
    octonionReal (octonionMul a (octonionConj b)) = octDot a b := rfl

private theorem octDot_scalar_right (x : Octonion) (r : ℝ) :
    octDot x (octonionScalar r) = r * octonionReal x := by
  rw [octDot_comm, octDot_scalar_left]

private theorem octNormSq_scalar (r : ℝ) : octNormSq (octonionScalar r) = r ^ 2 := by
  rw [octNormSq_eq_coords]
  simp [octonionScalar]

private theorem octNormSq_zero : octNormSq 0 = 0 :=
  (octNormSq_eq_zero 0).mpr rfl

private theorem oct_ext {x y : Octonion}
    (h1re : x.1.re = y.1.re) (h1i : x.1.imI = y.1.imI) (h1j : x.1.imJ = y.1.imJ) (h1k : x.1.imK = y.1.imK)
    (h2re : x.2.re = y.2.re) (h2i : x.2.imI = y.2.imI) (h2j : x.2.imJ = y.2.imJ) (h2k : x.2.imK = y.2.imK) :
    x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

private theorem octonionReal_mul_split (x y : Octonion) :
    octonionReal (octonionMul x y) =
      octonionReal x * octonionReal y - octDot (octIm x) (octIm y) := by
  have hx : x = octonionScalar (octonionReal x) + octIm x := by
    simp [octIm]
  have hy : y = octonionScalar (octonionReal y) + octIm y := by
    simp [octIm]
  conv_lhs => rw [hx, hy]
  rw [octonionMul_add_left, octonionMul_add_right, octonionMul_add_right,
    octonionMul_scalar_left, octonionMul_scalar_left, octonionMul_scalar_right,
    octonionReal_add, octonionReal_add, octonionReal_add,
    octonionReal_smul, octonionReal_smul, octonionReal_smul,
    octonionReal_scalar, octonionReal_octIm, octonionReal_octIm,
    octonionReal_mul_imag_eq (octonionReal_octIm x) (octonionReal_octIm y)]
  ring

private theorem octMul_right_conj_cancel' (a b : Octonion) :
    octonionMul (octonionMul a (octonionConj b)) b = octNormSq b • a :=
  octMul_right_conj_cancel b a

/-! ## Section 1: Thirteen Traces (`def:traces`) and `fourPointInvariant` (`eq:A:Acal52`) -/

def fpOverlap (p : Fin 4 → Albert) (i j : Fin 4) : ℝ :=
  tracePairing (p i) (p j)

def fpTriangle (p : Fin 4 → Albert) (i j k : Fin 4) : ℝ :=
  tracePairing (jordanMul (p i) (p j)) (p k)

def fpDoublePair1 (p : Fin 4 → Albert) : ℝ :=
  tracePairing (jordanMul (p 0) (p 1)) (jordanMul (p 2) (p 3))

def fpDoublePair2 (p : Fin 4 → Albert) : ℝ :=
  tracePairing (jordanMul (p 0) (p 2)) (jordanMul (p 1) (p 3))

def fpDoublePair3 (p : Fin 4 → Albert) : ℝ :=
  tracePairing (jordanMul (p 0) (p 3)) (jordanMul (p 1) (p 2))

def fpOmega1 (p : Fin 4 → Albert) : ℝ :=
  fpDoublePair2 p + fpDoublePair3 p - fpDoublePair1 p

def fpOmega2 (p : Fin 4 → Albert) : ℝ :=
  fpDoublePair1 p + fpDoublePair3 p - fpDoublePair2 p

def fpOmega3 (p : Fin 4 → Albert) : ℝ :=
  fpDoublePair1 p + fpDoublePair2 p - fpDoublePair3 p

theorem fpOverlap_symm (p : Fin 4 → Albert) (i j : Fin 4) :
    fpOverlap p i j = fpOverlap p j i :=
  tracePairing_comm (p i) (p j)

theorem fpTriangle_swap12 (p : Fin 4 → Albert) (i j k : Fin 4) :
    fpTriangle p i j k = fpTriangle p j i k := by
  unfold fpTriangle
  rw [jordanMul_comm]

theorem fpTriangle_swap23 (p : Fin 4 → Albert) (i j k : Fin 4) :
    fpTriangle p i j k = fpTriangle p i k j := by
  unfold fpTriangle
  rw [NativeAnalysis.tracePairing_associative, jordanMul_comm (p j) (p k),
    ← NativeAnalysis.tracePairing_associative]

theorem fpTriangle_eq_nativeTriangles (p : Fin 4 → Albert) (i j k : Fin 4) :
    fpTriangle p i j k = nativeTriangles p i j k := by
  unfold fpTriangle nativeTriangles
  exact NativeAnalysis.tracePairing_associative (p i) (p j) (p k)

private theorem tracePairing_jordanTriple_eq (a b c d : Albert) :
    tracePairing a (jordanTriple b c d) =
      tracePairing (jordanMul a b) (jordanMul c d) +
      tracePairing (jordanMul a d) (jordanMul b c) -
      tracePairing (jordanMul a c) (jordanMul b d) := by
  have hstep : ∀ x y z : Albert,
      tracePairing a (jordanMul (jordanMul x y) z) =
        tracePairing (jordanMul a z) (jordanMul x y) := fun x y z => by
    rw [jordanMul_comm (jordanMul x y) z, ← NativeAnalysis.tracePairing_associative]
  unfold jordanTriple
  rw [tracePairing_sub_right, tracePairing_add_right, hstep b c d, hstep d c b, hstep b d c,
    jordanMul_comm d c]
  ring

theorem nativeCornerQ_eq_fpOmega (p : Fin 4 → Albert) :
    nativeCornerQ p = ![fpOmega2 p, fpOmega3 p, fpOmega1 p] := by
  have h0 : nativeCornerQ p 0 = fpOmega2 p := by
    unfold nativeCornerQ fpOmega2 fpDoublePair1 fpDoublePair2 fpDoublePair3
    rw [Matrix.cons_val_zero, tracePairing_jordanTriple_eq]
  have h1 : nativeCornerQ p 1 = fpOmega3 p := by
    unfold nativeCornerQ fpOmega3 fpDoublePair1 fpDoublePair2 fpDoublePair3
    rw [Matrix.cons_val_one, Matrix.cons_val_zero, tracePairing_jordanTriple_eq,
      jordanMul_comm (p 3) (p 1), jordanMul_comm (p 2) (p 1),
      tracePairing_comm (jordanMul (p 0) (p 1)) (jordanMul (p 2) (p 3)),
      tracePairing_comm (jordanMul (p 0) (p 3)) (jordanMul (p 1) (p 2))]
    ring
  have h2 : nativeCornerQ p 2 = fpOmega1 p := by
    unfold nativeCornerQ fpOmega1 fpDoublePair1 fpDoublePair2 fpDoublePair3
    change tracePairing (p 0) (jordanTriple (p 3) (p 1) (p 2)) = _
    rw [tracePairing_jordanTriple_eq, jordanMul_comm (p 3) (p 1), jordanMul_comm (p 3) (p 2)]
    ring
  funext idx
  fin_cases idx
  · exact h0
  · exact h1
  · exact h2

def fourPointOmegaPoly
    (oAB oAC oAD oBC oBD oCD RABC RABD RACD RBCD ω1 ω2 ω3 : ℝ) : ℝ :=
  oAB * oAC * oAD * oBC * oBD * oCD
    - (RABC ^ 2 * oAD * oBD * oCD + RABD ^ 2 * oAC * oBC * oCD
        + RACD ^ 2 * oAB * oBC * oBD + RBCD ^ 2 * oAB * oAC * oAD)
    - 4 * RABC * RABD * RACD * RBCD
    - (oAB * oCD * ω1 ^ 2 + oAC * oBD * ω2 ^ 2 + oAD * oBC * ω3 ^ 2)
    + 2 * ω1 * (RABC * RABD * oCD + RACD * RBCD * oAB)
    + 2 * ω2 * (RABC * RACD * oBD + RABD * RBCD * oAC)
    + 2 * ω3 * (RABC * RBCD * oAD + RABD * RACD * oBC)
    - 2 * ω1 * ω2 * ω3

def fourPointTracePoly
    (oAB oAC oAD oBC oBD oCD RABC RABD RACD RBCD t1 t2 t3 : ℝ) : ℝ :=
  fourPointOmegaPoly oAB oAC oAD oBC oBD oCD RABC RABD RACD RBCD
    (t2 + t3 - t1) (t1 + t3 - t2) (t1 + t2 - t3)

def fourPointInvariant (p : Fin 4 → Albert) : ℝ :=
  fourPointOmegaPoly
    (fpOverlap p 0 1) (fpOverlap p 0 2) (fpOverlap p 0 3)
    (fpOverlap p 1 2) (fpOverlap p 1 3) (fpOverlap p 2 3)
    (fpTriangle p 0 1 2) (fpTriangle p 0 1 3)
    (fpTriangle p 0 2 3) (fpTriangle p 1 2 3)
    (fpOmega1 p) (fpOmega2 p) (fpOmega3 p)

def unorderedPairClass (a b : Fin 4) : Fin 3 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 0
  else if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then 1
  else 2

def pairTraceSelector (t : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 4)) (k : Fin 3) : ℝ :=
  match k with
  | 0 => t (unorderedPairClass (σ 0) (σ 1))
  | 1 => t (unorderedPairClass (σ 0) (σ 2))
  | 2 => t (unorderedPairClass (σ 0) (σ 3))

private def SamePartition (a b c d : Fin 4) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d)

private theorem samePartition_perm (σ : Equiv.Perm (Fin 4)) (a b c d : Fin 4) :
    SamePartition (σ a) (σ b) (σ c) (σ d) ↔ SamePartition a b c d := by
  simp [SamePartition, σ.injective.eq_iff]

private def pairRep1 : Fin 3 → Fin 4 := ![0, 0, 0]
private def pairRep2 : Fin 3 → Fin 4 := ![1, 2, 3]

private theorem samePartition_pairRep (a b : Fin 4) (hab : a ≠ b) :
    SamePartition a b (pairRep1 (unorderedPairClass a b)) (pairRep2 (unorderedPairClass a b)) := by
  fin_cases a <;> fin_cases b <;> simp_all [SamePartition, unorderedPairClass, pairRep1, pairRep2]

private theorem unorderedPairClass_eq_of_samePartition {a b c d : Fin 4}
    (hab : a ≠ b) (hcd : c ≠ d) (hsp : SamePartition a b c d) :
    unorderedPairClass a b = unorderedPairClass c d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [SamePartition, unorderedPairClass]

private theorem pairTraceSelector_mul (t : Fin 3 → ℝ) (σ τ : Equiv.Perm (Fin 4)) :
    pairTraceSelector (pairTraceSelector t σ) τ = pairTraceSelector t (σ * τ) := by
  funext k
  have step : ∀ a b : Fin 4, a ≠ b →
      unorderedPairClass (σ (pairRep1 (unorderedPairClass a b)))
        (σ (pairRep2 (unorderedPairClass a b))) =
      unorderedPairClass (σ a) (σ b) := by
    intro a b hab
    apply unorderedPairClass_eq_of_samePartition
    · intro h
      have heq := σ.injective h
      have hsp := samePartition_pairRep a b hab
      fin_cases a <;> fin_cases b <;> simp_all [unorderedPairClass, pairRep1, pairRep2]
    · exact fun h => hab (σ.injective h)
    · rw [samePartition_perm]
      exact samePartition_pairRep a b hab |>.symm |> fun _ => by
        have h := samePartition_pairRep a b hab
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr (Or.inl ⟨h2.symm, h1.symm⟩)
        · exact Or.inr (Or.inr ⟨h1.symm, h3.symm, h2.symm, h4.symm⟩)
  fin_cases k
  · simp only [pairTraceSelector, Equiv.Perm.mul_apply]
    have h01 : τ 0 ≠ τ 1 := fun h => by have := τ.injective h; contradiction
    generalize h : unorderedPairClass (τ 0) (τ 1) = c
    fin_cases c <;>
      simp [← step (τ 0) (τ 1) h01, h, pairRep1, pairRep2]
  · simp only [pairTraceSelector, Equiv.Perm.mul_apply]
    have h02 : τ 0 ≠ τ 2 := fun h => by have := τ.injective h; contradiction
    generalize h : unorderedPairClass (τ 0) (τ 2) = c
    fin_cases c <;>
      simp [← step (τ 0) (τ 2) h02, h, pairRep1, pairRep2]
  · simp only [pairTraceSelector, Equiv.Perm.mul_apply]
    have h03 : τ 0 ≠ τ 3 := fun h => by have := τ.injective h; contradiction
    generalize h : unorderedPairClass (τ 0) (τ 3) = c
    fin_cases c <;>
      simp [← step (τ 0) (τ 3) h03, h, pairRep1, pairRep2]

private theorem swap01_0 : Equiv.swap (0 : Fin 4) 1 0 = 1 := by decide
private theorem swap01_1 : Equiv.swap (0 : Fin 4) 1 1 = 0 := by decide
private theorem swap01_2 : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
private theorem swap01_3 : Equiv.swap (0 : Fin 4) 1 3 = 3 := by decide
private theorem swap12_0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
private theorem swap12_1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
private theorem swap12_2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
private theorem swap12_3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
private theorem swap23_0 : Equiv.swap (2 : Fin 4) 3 0 = 0 := by decide
private theorem swap23_1 : Equiv.swap (2 : Fin 4) 3 1 = 1 := by decide
private theorem swap23_2 : Equiv.swap (2 : Fin 4) 3 2 = 3 := by decide
private theorem swap23_3 : Equiv.swap (2 : Fin 4) 3 3 = 2 := by decide

private def permTraceEval
    (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ)
    (σ : Equiv.Perm (Fin 4)) : ℝ :=
  fourPointTracePoly
    (o (σ 0) (σ 1)) (o (σ 0) (σ 2)) (o (σ 0) (σ 3))
    (o (σ 1) (σ 2)) (o (σ 1) (σ 3)) (o (σ 2) (σ 3))
    (R (σ 0) (σ 1) (σ 2)) (R (σ 0) (σ 1) (σ 3))
    (R (σ 0) (σ 2) (σ 3)) (R (σ 1) (σ 2) (σ 3))
    (pairTraceSelector t σ 0) (pairTraceSelector t σ 1) (pairTraceSelector t σ 2)

private theorem permTraceEval_swap01
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR12 : ∀ i j k, R i j k = R j i k) (_hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ) :
    permTraceEval o R t (Equiv.swap 0 1) = permTraceEval o R t 1 := by
  unfold permTraceEval pairTraceSelector unorderedPairClass fourPointTracePoly fourPointOmegaPoly
  simp only [Equiv.Perm.one_apply, swap01_0, swap01_1, swap01_2, swap01_3]
  norm_num
  rw [ho 1 0, hR12 1 0 2, hR12 1 0 3]
  ring

private theorem permTraceEval_swap12
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR12 : ∀ i j k, R i j k = R j i k) (hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ) :
    permTraceEval o R t (Equiv.swap 1 2) = permTraceEval o R t 1 := by
  unfold permTraceEval pairTraceSelector unorderedPairClass fourPointTracePoly fourPointOmegaPoly
  simp only [Equiv.Perm.one_apply, swap12_0, swap12_1, swap12_2, swap12_3]
  norm_num
  rw [ho 2 1, hR23 0 2 1, hR12 2 1 3]
  ring

private theorem permTraceEval_swap23
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (_hR12 : ∀ i j k, R i j k = R j i k) (hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ) :
    permTraceEval o R t (Equiv.swap 2 3) = permTraceEval o R t 1 := by
  unfold permTraceEval pairTraceSelector unorderedPairClass fourPointTracePoly fourPointOmegaPoly
  simp only [Equiv.Perm.one_apply, swap23_0, swap23_1, swap23_2, swap23_3]
  norm_num
  rw [ho 3 2, hR23 0 3 2, hR23 1 3 2]
  ring

private theorem permTraceEval_mul_right (σ τ : Equiv.Perm (Fin 4))
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR12 : ∀ i j k, R i j k = R j i k) (hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ)
    (hτ : ∀ o' : Fin 4 → Fin 4 → ℝ, (∀ i j, o' i j = o' j i) →
      ∀ R' : Fin 4 → Fin 4 → Fin 4 → ℝ,
      (∀ i j k, R' i j k = R' j i k) → (∀ i j k, R' i j k = R' i k j) →
      ∀ t' : Fin 3 → ℝ, permTraceEval o' R' t' τ = permTraceEval o' R' t' 1) :
    permTraceEval o R t (σ * τ) = permTraceEval o R t σ := by
  have h1 := hτ (fun i j => o (σ i) (σ j)) (fun i j => ho (σ i) (σ j))
    (fun i j k => R (σ i) (σ j) (σ k))
    (fun i j k => hR12 (σ i) (σ j) (σ k))
    (fun i j k => hR23 (σ i) (σ j) (σ k))
    (pairTraceSelector t σ)
  have hl : permTraceEval (fun i j => o (σ i) (σ j)) (fun i j k => R (σ i) (σ j) (σ k))
      (pairTraceSelector t σ) τ = permTraceEval o R t (σ * τ) := by
    unfold permTraceEval
    simp only [Equiv.Perm.mul_apply]
    rw [pairTraceSelector_mul]
  have hr : permTraceEval (fun i j => o (σ i) (σ j)) (fun i j k => R (σ i) (σ j) (σ k))
      (pairTraceSelector t σ) 1 = permTraceEval o R t σ := by
    unfold permTraceEval
    simp only [Equiv.Perm.one_apply]
    have hp := pairTraceSelector_mul t σ 1
    rw [mul_one] at hp
    simp [hp]
  rw [← hl, ← hr]
  exact h1

private theorem permTraceEval_swap_all (i j : Fin 4) :
    ∀ (o : Fin 4 → Fin 4 → ℝ), (∀ a b, o a b = o b a) →
    ∀ (R : Fin 4 → Fin 4 → Fin 4 → ℝ),
    (∀ a b c, R a b c = R b a c) → (∀ a b c, R a b c = R a c b) →
    ∀ (t : Fin 3 → ℝ), permTraceEval o R t (Equiv.swap i j) = permTraceEval o R t 1 := by
  have h01 : ∀ (o : Fin 4 → Fin 4 → ℝ), (∀ a b, o a b = o b a) →
      ∀ (R : Fin 4 → Fin 4 → Fin 4 → ℝ),
      (∀ a b c, R a b c = R b a c) → (∀ a b c, R a b c = R a c b) →
      ∀ (t : Fin 3 → ℝ), permTraceEval o R t (Equiv.swap 0 1) = permTraceEval o R t 1 :=
    permTraceEval_swap01
  have h12 : ∀ (o : Fin 4 → Fin 4 → ℝ), (∀ a b, o a b = o b a) →
      ∀ (R : Fin 4 → Fin 4 → Fin 4 → ℝ),
      (∀ a b c, R a b c = R b a c) → (∀ a b c, R a b c = R a c b) →
      ∀ (t : Fin 3 → ℝ), permTraceEval o R t (Equiv.swap 1 2) = permTraceEval o R t 1 :=
    permTraceEval_swap12
  have h23 : ∀ (o : Fin 4 → Fin 4 → ℝ), (∀ a b, o a b = o b a) →
      ∀ (R : Fin 4 → Fin 4 → Fin 4 → ℝ),
      (∀ a b c, R a b c = R b a c) → (∀ a b c, R a b c = R a c b) →
      ∀ (t : Fin 3 → ℝ), permTraceEval o R t (Equiv.swap 2 3) = permTraceEval o R t 1 :=
    permTraceEval_swap23
  have h02 : ∀ (o : Fin 4 → Fin 4 → ℝ), (∀ a b, o a b = o b a) →
      ∀ (R : Fin 4 → Fin 4 → Fin 4 → ℝ),
      (∀ a b c, R a b c = R b a c) → (∀ a b c, R a b c = R a c b) →
      ∀ (t : Fin 3 → ℝ), permTraceEval o R t (Equiv.swap 0 2) = permTraceEval o R t 1 := by
    intro o ho R hR12 hR23 t
    have hsw : Equiv.swap (0 : Fin 4) 2 = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
      ext x; fin_cases x <;> decide
    rw [hsw, permTraceEval_mul_right _ _ o ho R hR12 hR23 t h01,
      permTraceEval_mul_right _ _ o ho R hR12 hR23 t h12, h01 o ho R hR12 hR23 t]
  have h13 : ∀ (o : Fin 4 → Fin 4 → ℝ), (∀ a b, o a b = o b a) →
      ∀ (R : Fin 4 → Fin 4 → Fin 4 → ℝ),
      (∀ a b c, R a b c = R b a c) → (∀ a b c, R a b c = R a c b) →
      ∀ (t : Fin 3 → ℝ), permTraceEval o R t (Equiv.swap 1 3) = permTraceEval o R t 1 := by
    intro o ho R hR12 hR23 t
    have hsw : Equiv.swap (1 : Fin 4) 3 = Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 1 2 := by
      ext x; fin_cases x <;> decide
    rw [hsw, permTraceEval_mul_right _ _ o ho R hR12 hR23 t h12,
      permTraceEval_mul_right _ _ o ho R hR12 hR23 t h23, h12 o ho R hR12 hR23 t]
  have h03 : ∀ (o : Fin 4 → Fin 4 → ℝ), (∀ a b, o a b = o b a) →
      ∀ (R : Fin 4 → Fin 4 → Fin 4 → ℝ),
      (∀ a b c, R a b c = R b a c) → (∀ a b c, R a b c = R a c b) →
      ∀ (t : Fin 3 → ℝ), permTraceEval o R t (Equiv.swap 0 3) = permTraceEval o R t 1 := by
    intro o ho R hR12 hR23 t
    have hsw : Equiv.swap (0 : Fin 4) 3 =
        Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
      ext x; fin_cases x <;> decide
    rw [hsw, permTraceEval_mul_right _ _ o ho R hR12 hR23 t h01,
      permTraceEval_mul_right _ _ o ho R hR12 hR23 t h12,
      permTraceEval_mul_right _ _ o ho R hR12 hR23 t h23,
      permTraceEval_mul_right _ _ o ho R hR12 hR23 t h12, h01 o ho R hR12 hR23 t]
  intro o ho R hR12 hR23 t
  fin_cases i <;> fin_cases j
  · rw [Equiv.swap_self]; rfl
  · exact h01 o ho R hR12 hR23 t
  · exact h02 o ho R hR12 hR23 t
  · exact h03 o ho R hR12 hR23 t
  · rw [Equiv.swap_comm]; exact h01 o ho R hR12 hR23 t
  · rw [Equiv.swap_self]; rfl
  · exact h12 o ho R hR12 hR23 t
  · exact h13 o ho R hR12 hR23 t
  · rw [Equiv.swap_comm]; exact h02 o ho R hR12 hR23 t
  · rw [Equiv.swap_comm]; exact h12 o ho R hR12 hR23 t
  · rw [Equiv.swap_self]; rfl
  · exact h23 o ho R hR12 hR23 t
  · rw [Equiv.swap_comm]; exact h03 o ho R hR12 hR23 t
  · rw [Equiv.swap_comm]; exact h13 o ho R hR12 hR23 t
  · rw [Equiv.swap_comm]; exact h23 o ho R hR12 hR23 t
  · rw [Equiv.swap_self]; rfl

theorem fourPointTracePoly_perm (σ : Equiv.Perm (Fin 4))
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR12 : ∀ i j k, R i j k = R j i k) (hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ) :
    fourPointTracePoly
      (o (σ 0) (σ 1)) (o (σ 0) (σ 2)) (o (σ 0) (σ 3))
      (o (σ 1) (σ 2)) (o (σ 1) (σ 3)) (o (σ 2) (σ 3))
      (R (σ 0) (σ 1) (σ 2)) (R (σ 0) (σ 1) (σ 3))
      (R (σ 0) (σ 2) (σ 3)) (R (σ 1) (σ 2) (σ 3))
      (pairTraceSelector t σ 0) (pairTraceSelector t σ 1) (pairTraceSelector t σ 2) =
      fourPointTracePoly (o 0 1) (o 0 2) (o 0 3) (o 1 2) (o 1 3) (o 2 3)
        (R 0 1 2) (R 0 1 3) (R 0 2 3) (R 1 2 3) (t 0) (t 1) (t 2) := by
  have hmain : ∀ π : Equiv.Perm (Fin 4),
      ∀ (o' : Fin 4 → Fin 4 → ℝ), (∀ a b, o' a b = o' b a) →
      ∀ (R' : Fin 4 → Fin 4 → Fin 4 → ℝ),
      (∀ a b c, R' a b c = R' b a c) → (∀ a b c, R' a b c = R' a c b) →
      ∀ (t' : Fin 3 → ℝ), permTraceEval o' R' t' π = permTraceEval o' R' t' 1 := by
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one => intros; rfl
    | swap_mul π x y _ ih =>
      intro o' ho' R' hR12' hR23' t'
      rw [permTraceEval_mul_right (Equiv.swap x y) π o' ho' R' hR12' hR23' t' ih]
      exact permTraceEval_swap_all x y o' ho' R' hR12' hR23' t'
  have h1 := hmain σ o ho R hR12 hR23 t
  simpa [permTraceEval, pairTraceSelector, unorderedPairClass] using h1

theorem fourPointInvariant_automorphism_invariant
    (g : NativeAlbertAutomorphism) (p : Fin 4 → Albert) :
    fourPointInvariant (fun i => g.linearEquiv (p i)) = fourPointInvariant p := by
  have hpair : ∀ x y : Albert,
      tracePairing (g.linearEquiv x) (g.linearEquiv y) = tracePairing x y := fun x y => by
    unfold tracePairing
    rw [← g.preserves_product, g.preserves_trace]
  have ho : ∀ i j, fpOverlap (fun k => g.linearEquiv (p k)) i j = fpOverlap p i j := fun i j =>
    hpair (p i) (p j)
  have hR : ∀ i j k, fpTriangle (fun m => g.linearEquiv (p m)) i j k = fpTriangle p i j k :=
    fun i j k => by
    unfold fpTriangle
    rw [← g.preserves_product, hpair]
  have ht1 : fpDoublePair1 (fun m => g.linearEquiv (p m)) = fpDoublePair1 p := by
    unfold fpDoublePair1
    rw [← g.preserves_product, ← g.preserves_product, hpair]
  have ht2 : fpDoublePair2 (fun m => g.linearEquiv (p m)) = fpDoublePair2 p := by
    unfold fpDoublePair2
    rw [← g.preserves_product, ← g.preserves_product, hpair]
  have ht3 : fpDoublePair3 (fun m => g.linearEquiv (p m)) = fpDoublePair3 p := by
    unfold fpDoublePair3
    rw [← g.preserves_product, ← g.preserves_product, hpair]
  unfold fourPointInvariant fpOmega1 fpOmega2 fpOmega3
  simp only [ho, hR, ht1, ht2, ht3]

private theorem pairTraceSelector_one (t : Fin 3 → ℝ) : pairTraceSelector t 1 = t := by
  funext k; fin_cases k <;> rfl

private def dpVec (q : Fin 4 → Albert) : Fin 3 → ℝ :=
  ![fpDoublePair1 q, fpDoublePair2 q, fpDoublePair3 q]

private theorem dpVec_swap01 (q : Fin 4 → Albert) :
    dpVec (fun i => q (Equiv.swap 0 1 i)) = pairTraceSelector (dpVec q) (Equiv.swap 0 1) := by
  have idx0 : unorderedPairClass (Equiv.swap (0 : Fin 4) 1 0) (Equiv.swap 0 1 1) = 0 := by decide
  have idx1 : unorderedPairClass (Equiv.swap (0 : Fin 4) 1 0) (Equiv.swap 0 1 2) = 2 := by decide
  have idx2 : unorderedPairClass (Equiv.swap (0 : Fin 4) 1 0) (Equiv.swap 0 1 3) = 1 := by decide
  funext k
  fin_cases k
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx0]
    change fpDoublePair1 (fun i => q (Equiv.swap 0 1 i)) = fpDoublePair1 q
    simp only [fpDoublePair1, swap01_0, swap01_1, swap01_2, swap01_3]
    rw [jordanMul_comm (q 1) (q 0)]
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx1]
    change fpDoublePair2 (fun i => q (Equiv.swap 0 1 i)) = fpDoublePair3 q
    simp only [fpDoublePair2, fpDoublePair3, swap01_0, swap01_1, swap01_2, swap01_3]
    rw [tracePairing_comm]
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx2]
    change fpDoublePair3 (fun i => q (Equiv.swap 0 1 i)) = fpDoublePair2 q
    simp only [fpDoublePair2, fpDoublePair3, swap01_0, swap01_1, swap01_2, swap01_3]
    rw [tracePairing_comm]

private theorem dpVec_swap12 (q : Fin 4 → Albert) :
    dpVec (fun i => q (Equiv.swap 1 2 i)) = pairTraceSelector (dpVec q) (Equiv.swap 1 2) := by
  have idx0 : unorderedPairClass (Equiv.swap (1 : Fin 4) 2 0) (Equiv.swap 1 2 1) = 1 := by decide
  have idx1 : unorderedPairClass (Equiv.swap (1 : Fin 4) 2 0) (Equiv.swap 1 2 2) = 0 := by decide
  have idx2 : unorderedPairClass (Equiv.swap (1 : Fin 4) 2 0) (Equiv.swap 1 2 3) = 2 := by decide
  funext k
  fin_cases k
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx0]
    change fpDoublePair1 (fun i => q (Equiv.swap 1 2 i)) = fpDoublePair2 q
    simp only [fpDoublePair1, fpDoublePair2, swap12_0, swap12_1, swap12_2, swap12_3]
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx1]
    change fpDoublePair2 (fun i => q (Equiv.swap 1 2 i)) = fpDoublePair1 q
    simp only [fpDoublePair2, fpDoublePair1, swap12_0, swap12_1, swap12_2, swap12_3]
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx2]
    change fpDoublePair3 (fun i => q (Equiv.swap 1 2 i)) = fpDoublePair3 q
    simp only [fpDoublePair3, swap12_0, swap12_1, swap12_2, swap12_3]
    rw [jordanMul_comm (q 2) (q 1)]

private theorem dpVec_swap23 (q : Fin 4 → Albert) :
    dpVec (fun i => q (Equiv.swap 2 3 i)) = pairTraceSelector (dpVec q) (Equiv.swap 2 3) := by
  have idx0 : unorderedPairClass (Equiv.swap (2 : Fin 4) 3 0) (Equiv.swap 2 3 1) = 0 := by decide
  have idx1 : unorderedPairClass (Equiv.swap (2 : Fin 4) 3 0) (Equiv.swap 2 3 2) = 2 := by decide
  have idx2 : unorderedPairClass (Equiv.swap (2 : Fin 4) 3 0) (Equiv.swap 2 3 3) = 1 := by decide
  funext k
  fin_cases k
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx0]
    change fpDoublePair1 (fun i => q (Equiv.swap 2 3 i)) = fpDoublePair1 q
    simp only [fpDoublePair1, swap23_0, swap23_1, swap23_2, swap23_3]
    rw [jordanMul_comm (q 3) (q 2)]
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx1]
    change fpDoublePair2 (fun i => q (Equiv.swap 2 3 i)) = fpDoublePair3 q
    simp only [fpDoublePair2, fpDoublePair3, swap23_0, swap23_1, swap23_2, swap23_3]
  · dsimp only [dpVec, pairTraceSelector]
    rw [idx2]
    change fpDoublePair3 (fun i => q (Equiv.swap 2 3 i)) = fpDoublePair2 q
    simp only [fpDoublePair3, fpDoublePair2, swap23_0, swap23_1, swap23_2, swap23_3]

private theorem dpVec_mul (σ τ : Equiv.Perm (Fin 4)) (q : Fin 4 → Albert)
    (hσ : ∀ q', dpVec (fun i => q' (σ i)) = pairTraceSelector (dpVec q') σ)
    (hτ : ∀ q', dpVec (fun i => q' (τ i)) = pairTraceSelector (dpVec q') τ) :
    dpVec (fun i => q ((σ * τ) i)) = pairTraceSelector (dpVec q) (σ * τ) := by
  have h1 : dpVec (fun i => q ((σ * τ) i)) = dpVec (fun i => (fun m => q (σ m)) (τ i)) := rfl
  rw [h1, hτ (fun m => q (σ m)), hσ q, pairTraceSelector_mul]

private theorem dpVec_swap_all (a b : Fin 4) (q : Fin 4 → Albert) :
    dpVec (fun i => q (Equiv.swap a b i)) = pairTraceSelector (dpVec q) (Equiv.swap a b) := by
  have h01 : ∀ q', dpVec (fun i => q' (Equiv.swap 0 1 i)) = pairTraceSelector (dpVec q') (Equiv.swap 0 1) :=
    dpVec_swap01
  have h12 : ∀ q', dpVec (fun i => q' (Equiv.swap 1 2 i)) = pairTraceSelector (dpVec q') (Equiv.swap 1 2) :=
    dpVec_swap12
  have h23 : ∀ q', dpVec (fun i => q' (Equiv.swap 2 3 i)) = pairTraceSelector (dpVec q') (Equiv.swap 2 3) :=
    dpVec_swap23
  have h02 : ∀ q', dpVec (fun i => q' (Equiv.swap 0 2 i)) = pairTraceSelector (dpVec q') (Equiv.swap 0 2) := by
    intro q'
    have hsw : Equiv.swap (0 : Fin 4) 2 = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
      ext x; fin_cases x <;> decide
    rw [hsw]
    exact dpVec_mul _ _ q' (fun r => dpVec_mul _ _ r h01 h12) h01
  have h13 : ∀ q', dpVec (fun i => q' (Equiv.swap 1 3 i)) = pairTraceSelector (dpVec q') (Equiv.swap 1 3) := by
    intro q'
    have hsw : Equiv.swap (1 : Fin 4) 3 = Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 1 2 := by
      ext x; fin_cases x <;> decide
    rw [hsw]
    exact dpVec_mul _ _ q' (fun r => dpVec_mul _ _ r h12 h23) h12
  have h03 : ∀ q', dpVec (fun i => q' (Equiv.swap 0 3 i)) = pairTraceSelector (dpVec q') (Equiv.swap 0 3) := by
    intro q'
    have hsw : Equiv.swap (0 : Fin 4) 3 =
        Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
      ext x; fin_cases x <;> decide
    rw [hsw]
    exact dpVec_mul _ _ q' (fun r1 => dpVec_mul _ _ r1
      (fun r2 => dpVec_mul _ _ r2 (fun r3 => dpVec_mul _ _ r3 h01 h12) h23) h12) h01
  fin_cases a <;> fin_cases b
  · rw [Equiv.swap_self]; exact (pairTraceSelector_one (dpVec q)).symm
  · exact h01 q
  · exact h02 q
  · exact h03 q
  · rw [Equiv.swap_comm]; exact h01 q
  · rw [Equiv.swap_self]; exact (pairTraceSelector_one (dpVec q)).symm
  · exact h12 q
  · exact h13 q
  · rw [Equiv.swap_comm]; exact h02 q
  · rw [Equiv.swap_comm]; exact h12 q
  · rw [Equiv.swap_self]; exact (pairTraceSelector_one (dpVec q)).symm
  · exact h23 q
  · rw [Equiv.swap_comm]; exact h03 q
  · rw [Equiv.swap_comm]; exact h13 q
  · rw [Equiv.swap_comm]; exact h23 q
  · rw [Equiv.swap_self]; exact (pairTraceSelector_one (dpVec q)).symm

private theorem dpVec_perm (π : Equiv.Perm (Fin 4)) :
    ∀ q : Fin 4 → Albert, dpVec (fun i => q (π i)) = pairTraceSelector (dpVec q) π := by
  induction π using Equiv.Perm.swap_induction_on with
  | one =>
    intro q
    exact (pairTraceSelector_one (dpVec q)).symm
  | swap_mul π x y _ ih =>
    intro q
    exact dpVec_mul (Equiv.swap x y) π q (dpVec_swap_all x y) ih

theorem fourPointInvariant_perm_invariant
    (σ : Equiv.Perm (Fin 4)) (p : Fin 4 → Albert) :
    fourPointInvariant (fun i => p (σ i)) = fourPointInvariant p := by
  let t : Fin 3 → ℝ := dpVec p
  have hω : ∀ (q : Fin 4 → Albert),
      fourPointInvariant q =
      fourPointTracePoly
        (fpOverlap q 0 1) (fpOverlap q 0 2) (fpOverlap q 0 3)
        (fpOverlap q 1 2) (fpOverlap q 1 3) (fpOverlap q 2 3)
        (fpTriangle q 0 1 2) (fpTriangle q 0 1 3)
        (fpTriangle q 0 2 3) (fpTriangle q 1 2 3)
        (fpDoublePair1 q) (fpDoublePair2 q) (fpDoublePair3 q) := by
    intro q
    unfold fourPointInvariant fourPointTracePoly fpOmega1 fpOmega2 fpOmega3
    congr 1
  have hdp_all := dpVec_perm σ p
  have hdp0 : fpDoublePair1 (fun i => p (σ i)) = pairTraceSelector t σ 0 :=
    congrFun hdp_all 0
  have hdp1 : fpDoublePair2 (fun i => p (σ i)) = pairTraceSelector t σ 1 :=
    congrFun hdp_all 1
  have hdp2 : fpDoublePair3 (fun i => p (σ i)) = pairTraceSelector t σ 2 :=
    congrFun hdp_all 2
  rw [hω (fun i => p (σ i)), hω p]
  simp only [fpOverlap, fpTriangle] at *
  rw [hdp0, hdp1, hdp2]
  exact fourPointTracePoly_perm σ (fpOverlap p) (fpOverlap_symm p)
    (fpTriangle p) (fpTriangle_swap12 p) (fpTriangle_swap23 p) t

/-! ## Section 2: Rank-Three Trace Relation (`prop:fp:tracerel`) and Rank-Four Failure (`rem:fp:tracerel-rank(b)`) -/

structure RankThreeCubicModel (V : Type*) [AddCommGroup V] [Module ℝ V] where
  mul : V → V → V
  one : V
  tr : V →ₗ[ℝ] ℝ
  mul_comm : ∀ x y, mul x y = mul y x
  mul_add_left : ∀ x y z, mul (x + y) z = mul x z + mul y z
  mul_smul_left : ∀ (r : ℝ) x y, mul (r • x) y = r • mul x y
  mul_one_left : ∀ x, mul one x = x
  tr_one : tr one = 3
  tr_assoc : ∀ x y z, tr (mul (mul x y) z) = tr (mul x (mul y z))
  cubic_identity : ∀ x : V, ∃ N : ℝ,
    mul x (mul x x) - tr x • mul x x +
      ((1 / 2 : ℝ) * ((tr x) ^ 2 - tr (mul x x))) • x = N • one

theorem newton_quartic_of_cubic_identity {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : RankThreeCubicModel V) (x : V) :
    (M.tr x) ^ 4 - 6 * (M.tr x) ^ 2 * M.tr (M.mul x x)
      + 3 * (M.tr (M.mul x x)) ^ 2 + 8 * M.tr x * M.tr (M.mul x (M.mul x x))
      - 6 * M.tr (M.mul (M.mul x x) (M.mul x x)) = 0 := by
  obtain ⟨N, hcub⟩ := M.cubic_identity x
  have htr1 := congrArg M.tr hcub
  simp only [map_sub, map_add, map_smul, smul_eq_mul, M.tr_one] at htr1
  have htr2 := congrArg (fun y => M.tr (M.mul x y)) hcub
  have hmul_sub : ∀ a b : V, M.mul x (a - b) = M.mul x a - M.mul x b := fun a b => by
    rw [M.mul_comm x (a - b), sub_eq_add_neg, M.mul_add_left,
      ← neg_one_smul ℝ b, M.mul_smul_left, neg_one_smul, ← sub_eq_add_neg,
      M.mul_comm a x, M.mul_comm b x]
  have hmul_add : ∀ a b : V, M.mul x (a + b) = M.mul x a + M.mul x b := fun a b => by
    rw [M.mul_comm x (a + b), M.mul_add_left, M.mul_comm a x, M.mul_comm b x]
  have hmul_smul : ∀ (r : ℝ) (a : V), M.mul x (r • a) = r • M.mul x a := fun r a => by
    rw [M.mul_comm x (r • a), M.mul_smul_left, M.mul_comm a x]
  rw [hmul_add, hmul_sub, hmul_smul, hmul_smul, hmul_smul,
    map_add, map_sub, map_smul, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul] at htr2
  rw [← M.tr_assoc x x (M.mul x x)] at htr2
  have hxo : M.tr (M.mul x M.one) = M.tr x := by
    rw [M.mul_comm, M.mul_one_left]
  rw [hxo] at htr2
  have hmul1 : M.tr x * (M.tr (M.mul x (M.mul x x)) - M.tr x * M.tr (M.mul x x) +
      1 / 2 * (M.tr x ^ 2 - M.tr (M.mul x x)) * M.tr x) = 3 * (N * M.tr x) := by
    rw [htr1]; ring
  linarith [hmul1, htr2]

private def diff4 (F : (Fin 4 → ℝ) → ℝ) : ℝ :=
  ∑ S : Finset (Fin 4), (-1 : ℝ) ^ (4 - S.card) * F (fun i => if i ∈ S then 1 else 0)

private theorem diff4_zero : diff4 (fun _ => 0) = 0 := by
  simp [diff4]

private theorem diff4_add (F G : (Fin 4 → ℝ) → ℝ) :
    diff4 (fun x => F x + G x) = diff4 F + diff4 G := by
  unfold diff4
  simp only [mul_add, Finset.sum_add_distrib]

private theorem diff4_sub (F G : (Fin 4 → ℝ) → ℝ) :
    diff4 (fun x => F x - G x) = diff4 F - diff4 G := by
  unfold diff4
  simp only [mul_sub, Finset.sum_sub_distrib]

private theorem diff4_smul (c : ℝ) (F : (Fin 4 → ℝ) → ℝ) :
    diff4 (fun x => c * F x) = c * diff4 F := by
  unfold diff4
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

private def IsPerm4 (t : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧
  t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2

private instance : DecidablePred IsPerm4 := fun _t => inferInstanceAs (Decidable (_ ∧ _))

private theorem diff4_monom (i j k l : Fin 4) :
    diff4 (fun x => x i * x j * x k * x l) = if IsPerm4 (i, j, k, l) then 1 else 0 := by
  by_cases hp : IsPerm4 (i, j, k, l)
  · simp only [hp, ↓reduceIte]
    unfold diff4
    have huniv : ∀ S : Finset (Fin 4), S ≠ Finset.univ →
        (-1 : ℝ) ^ (4 - S.card) *
          ((if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then 1 else 0) *
            (if k ∈ S then 1 else 0) * (if l ∈ S then 1 else 0)) = 0 := by
      intro S hS
      have hcard : ({i, j, k, l} : Finset (Fin 4)).card = 4 := by
        rcases hp with ⟨hij, hik, hil, hjk, hjl, hkl⟩
        simp [Finset.card_insert_of_notMem, hij, hik, hil, hjk, hjl, hkl]
      have heq : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using hcard)
      obtain ⟨m, hm⟩ : ∃ m : Fin 4, m ∉ S := by
        by_contra hall
        push Not at hall
        exact hS (Finset.eq_univ_iff_forall.mpr hall)
      have hm4 : m ∈ ({i, j, k, l} : Finset (Fin 4)) := by rw [heq]; exact Finset.mem_univ m
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm4
      rcases hm4 with rfl | rfl | rfl | rfl <;> simp [hm]
    rw [Finset.sum_eq_single Finset.univ (fun S _ hS => huniv S hS) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · simp only [hp, ↓reduceIte]
    have hex_dec : ∀ a b c d : Fin 4, ¬ IsPerm4 (a, b, c, d) →
        ∃ m : Fin 4, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d := by decide
    obtain ⟨m, hma, hmb, hmc, hmd⟩ := hex_dec i j k l hp
    unfold diff4
    have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset (Fin 4)))
      (fun S => m ∈ S)
      (fun S => (-1 : ℝ) ^ (4 - S.card) *
        ((if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then 1 else 0) *
          (if k ∈ S then 1 else 0) * (if l ∈ S then 1 else 0)))).symm
    rw [hsplit]
    have hbij :
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun S => m ∈ S),
          (-1 : ℝ) ^ (4 - S.card) *
            ((if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then 1 else 0) *
              (if k ∈ S then 1 else 0) * (if l ∈ S then 1 else 0)) =
        - ∑ S ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun S => ¬ m ∈ S),
          (-1 : ℝ) ^ (4 - S.card) *
            ((if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then 1 else 0) *
              (if k ∈ S then 1 else 0) * (if l ∈ S then 1 else 0)) := by
      rw [← Finset.sum_neg_distrib]
      symm
      refine Finset.sum_bij (fun S _ => insert m S) ?_ ?_ ?_ ?_
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
        exact Finset.mem_insert_self m S
      · intro S1 hS1 S2 hS2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS1 hS2
        have h1 : (insert m S1).erase m = S1 := Finset.erase_insert hS1
        have h2 : (insert m S2).erase m = S2 := Finset.erase_insert hS2
        rw [← h1, ← h2, heq]
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        refine ⟨S.erase m, ?_, Finset.insert_erase hS⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Finset.notMem_erase m S
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        have hcard : (insert m S).card = S.card + 1 := Finset.card_insert_of_notMem hS
        have hle : S.card ≤ 3 := by
          have hs : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr (fun h => hS (h ▸ Finset.mem_univ m))
          have hlt := Finset.card_lt_card hs
          rw [Finset.card_univ, Fintype.card_fin] at hlt
          omega
        have hpow : (-1 : ℝ) ^ (4 - (insert m S).card) = - (-1 : ℝ) ^ (4 - S.card) := by
          rw [hcard, show 4 - S.card = (4 - (S.card + 1)) + 1 by omega, pow_succ]
          ring
        simp only [Finset.mem_insert, hma.symm, hmb.symm, hmc.symm, hmd.symm, false_or, hpow]
        ring
    rw [hbij, neg_add_cancel]

private theorem diff4_sum_fin4 (g : Fin 4 → (Fin 4 → ℝ) → ℝ) :
    diff4 (fun x => ∑ a : Fin 4, g a x) = ∑ a : Fin 4, diff4 (g a) := by
  simp only [Fin.sum_univ_four, diff4_add]

private theorem diff4_sum4 (c : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    diff4 (fun x => ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        x i * x j * x k * x l * c i j k l) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        if IsPerm4 (i, j, k, l) then c i j k l else 0 := by
  rw [diff4_sum_fin4 (fun i x => ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
    x i * x j * x k * x l * c i j k l)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diff4_sum_fin4 (fun j x => ∑ k : Fin 4, ∑ l : Fin 4,
    x i * x j * x k * x l * c i j k l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diff4_sum_fin4 (fun k x => ∑ l : Fin 4,
    x i * x j * x k * x l * c i j k l)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [diff4_sum_fin4 (fun l x => x i * x j * x k * x l * c i j k l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hsmul : diff4 (fun x => x i * x j * x k * x l * c i j k l) =
      c i j k l * diff4 (fun x => x i * x j * x k * x l) := by
    rw [← diff4_smul]
    congr 1; funext x; ring
  rw [hsmul, diff4_monom]
  split_ifs <;> ring

private def perm4List : List (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
  [(0,1,2,3), (0,1,3,2), (0,2,1,3), (0,2,3,1), (0,3,1,2), (0,3,2,1),
   (1,0,2,3), (1,0,3,2), (1,2,0,3), (1,2,3,0), (1,3,0,2), (1,3,2,0),
   (2,0,1,3), (2,0,3,1), (2,1,0,3), (2,1,3,0), (2,3,0,1), (2,3,1,0),
   (3,0,1,2), (3,0,2,1), (3,1,0,2), (3,1,2,0), (3,2,0,1), (3,2,1,0)]

private theorem sum_isPerm4_eq_perm4List (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      if IsPerm4 (i, j, k, l) then f i j k l else 0) =
    (perm4List.map (fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2)).sum := by
  have hprod :
      (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        if IsPerm4 (i, j, k, l) then f i j k l else 0) =
      ∑ t ∈ (Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4 × Fin 4)).filter IsPerm4,
        f t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type]
  have hset : (Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4 × Fin 4)).filter IsPerm4 =
      perm4List.toFinset := by decide
  have hnodup : perm4List.Nodup := by decide
  rw [hprod, hset, List.sum_toFinset _ hnodup]

theorem rankThree_fourIdempotent_trace_relation
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : RankThreeCubicModel V) (p : Fin 4 → V)
    (_hidem : ∀ i, M.mul (p i) (p i) = p i) (htr : ∀ i, M.tr (p i) = 1) :
    let o := fun i j => M.tr (M.mul (p i) (p j))
    let R := fun i j k => M.tr (M.mul (M.mul (p i) (p j)) (p k))
    let t1 := M.tr (M.mul (M.mul (p 0) (p 1)) (M.mul (p 2) (p 3)))
    let t2 := M.tr (M.mul (M.mul (p 0) (p 2)) (M.mul (p 1) (p 3)))
    let t3 := M.tr (M.mul (M.mul (p 0) (p 3)) (M.mul (p 1) (p 2)))
    t1 + t2 + t3 =
      1 / 2 - 1 / 2 * (o 0 1 + o 0 2 + o 0 3 + o 1 2 + o 1 3 + o 2 3)
        + 1 / 2 * (o 0 1 * o 2 3 + o 0 2 * o 1 3 + o 0 3 * o 1 2)
        + R 0 1 2 + R 0 1 3 + R 0 2 3 + R 1 2 3 := by
  -- Helper bilinearity of `M.mul`
  have mul_add_r : ∀ a b c : V, M.mul a (b + c) = M.mul a b + M.mul a c := fun a b c => by
    rw [M.mul_comm, M.mul_add_left, M.mul_comm b a, M.mul_comm c a]
  have mul_smul_r : ∀ (r : ℝ) (a b : V), M.mul a (r • b) = r • M.mul a b := fun r a b => by
    rw [M.mul_comm, M.mul_smul_left, M.mul_comm b a]
  have mul_sum4_l : ∀ (f : Fin 4 → V) (y : V),
      M.mul (∑ i : Fin 4, f i) y = ∑ i : Fin 4, M.mul (f i) y := by
    intro f y
    simp only [Fin.sum_univ_four, M.mul_add_left]
  have mul_sum4_r : ∀ (x : V) (f : Fin 4 → V),
      M.mul x (∑ i : Fin 4, f i) = ∑ i : Fin 4, M.mul x (f i) := by
    intro x f
    simp only [Fin.sum_univ_four, mul_add_r]
  let o : Fin 4 → Fin 4 → ℝ := fun i j => M.tr (M.mul (p i) (p j))
  let R : Fin 4 → Fin 4 → Fin 4 → ℝ := fun i j k => M.tr (M.mul (M.mul (p i) (p j)) (p k))
  let q4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
    fun i j k l => M.tr (M.mul (M.mul (p i) (p j)) (M.mul (p k) (p l)))
  let x : (Fin 4 → ℝ) → V := fun lam => ∑ i : Fin 4, lam i • p i
  have hs1 : ∀ lam, M.tr (x lam) = ∑ i : Fin 4, lam i := fun lam => by
    simp [x, map_sum, map_smul, htr]
  have hs2 : ∀ lam, M.tr (M.mul (x lam) (x lam)) =
      ∑ i : Fin 4, ∑ j : Fin 4, lam i * lam j * o i j := fun lam => by
    simp only [x, mul_sum4_l, mul_sum4_r, map_sum, M.mul_smul_left, mul_smul_r, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only [o]; ring
  have hs3 : ∀ lam, M.tr (M.mul (x lam) (M.mul (x lam) (x lam))) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, lam i * lam j * lam k * R i j k := fun lam => by
    simp only [x, mul_sum4_l, mul_sum4_r, map_sum, M.mul_smul_left, mul_smul_r, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    dsimp only [R]
    rw [M.tr_assoc (p i) (p j) (p k)]
    ring
  have hs4 : ∀ lam, M.tr (M.mul (M.mul (x lam) (x lam)) (M.mul (x lam) (x lam))) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        lam i * lam j * lam k * lam l * q4 i j k l := fun lam => by
    simp only [x, mul_sum4_l, mul_sum4_r, map_sum, M.mul_smul_left, mul_smul_r, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    dsimp only [q4]; ring
  have hvanish : ∀ lam,
      (M.tr (x lam)) ^ 4 - 6 * (M.tr (x lam)) ^ 2 * M.tr (M.mul (x lam) (x lam))
        + 3 * (M.tr (M.mul (x lam) (x lam))) ^ 2
        + 8 * M.tr (x lam) * M.tr (M.mul (x lam) (M.mul (x lam) (x lam)))
        - 6 * M.tr (M.mul (M.mul (x lam) (x lam)) (M.mul (x lam) (x lam))) = 0 :=
    fun lam => newton_quartic_of_cubic_identity M (x lam)
  have hdiff_zero : diff4 (fun (lam : Fin 4 → ℝ) =>
      (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4, lam i * lam j * lam k * lam l * 1)
      - 6 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          lam i * lam j * lam k * lam l * o k l)
      + 3 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          lam i * lam j * lam k * lam l * (o i j * o k l))
      + 8 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          lam i * lam j * lam k * lam l * R j k l)
      - 6 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          lam i * lam j * lam k * lam l * q4 i j k l)) = 0 := by
    have heq : (fun (lam : Fin 4 → ℝ) =>
      (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4, lam i * lam j * lam k * lam l * 1)
      - 6 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          lam i * lam j * lam k * lam l * o k l)
      + 3 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          lam i * lam j * lam k * lam l * (o i j * o k l))
      + 8 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          lam i * lam j * lam k * lam l * R j k l)
      - 6 * (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
          lam i * lam j * lam k * lam l * q4 i j k l)) = fun _ => 0 := by
      funext lam
      have hv := hvanish lam
      rw [hs1, hs2, hs3, hs4] at hv
      have hsum_mul : ∀ f g : Fin 4 → ℝ,
          (∑ i : Fin 4, f i) * (∑ j : Fin 4, g j) = ∑ i : Fin 4, ∑ j : Fin 4, f i * g j := by
        intro f g
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
      have h1 : (∑ i : Fin 4, lam i) ^ 4 =
          ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
            lam i * lam j * lam k * lam l * 1 := by
        simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      have h2 : (∑ i : Fin 4, lam i) ^ 2 * (∑ k : Fin 4, ∑ l : Fin 4, lam k * lam l * o k l) =
          ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
            lam i * lam j * lam k * lam l * o k l := by
        have hsq : (∑ i : Fin 4, lam i) ^ 2 = ∑ i : Fin 4, ∑ j : Fin 4, lam i * lam j := by
          rw [sq, hsum_mul]
        rw [hsq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
      have h3 : (∑ i : Fin 4, ∑ j : Fin 4, lam i * lam j * o i j) ^ 2 =
          ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
            lam i * lam j * lam k * lam l * (o i j * o k l) := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
      have h4 : (∑ i : Fin 4, lam i) *
          (∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4, lam j * lam k * lam l * R j k l) =
          ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
            lam i * lam j * lam k * lam l * R j k l := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
      rw [← h1, ← h2, ← h3, ← h4]
      linarith [hv]
    rw [heq, diff4_zero]
  rw [diff4_sub, diff4_add, diff4_add, diff4_sub,
    diff4_smul, diff4_smul, diff4_smul, diff4_smul,
    diff4_sum4, diff4_sum4, diff4_sum4, diff4_sum4, diff4_sum4,
    sum_isPerm4_eq_perm4List, sum_isPerm4_eq_perm4List, sum_isPerm4_eq_perm4List,
    sum_isPerm4_eq_perm4List, sum_isPerm4_eq_perm4List] at hdiff_zero
  have ho_symm : ∀ a b, o a b = o b a := fun a b => by
    dsimp only [o]; rw [M.mul_comm]
  have hR_symm12 : ∀ a b c, R a b c = R b a c := fun a b c => by
    dsimp only [R]; rw [M.mul_comm (p a) (p b)]
  have hR_symm23 : ∀ a b c, R a b c = R a c b := fun a b c => by
    dsimp only [R]; rw [M.tr_assoc, M.mul_comm (p b) (p c), ← M.tr_assoc]
  have hR_perm : ∀ a b c,
      R a c b = R a b c ∧ R b a c = R a b c ∧ R b c a = R a b c ∧
      R c a b = R a b c ∧ R c b a = R a b c := fun a b c =>
    ⟨hR_symm23 a c b, hR_symm12 b a c,
     by rw [hR_symm23 b c a, hR_symm12 b a c],
     by rw [hR_symm12 c a b, hR_symm23 a c b],
     by rw [hR_symm12 c b a, hR_symm23 b c a, hR_symm12 b a c]⟩
  have hq4_symm12 : ∀ a b c d, q4 a b c d = q4 b a c d := fun a b c d => by
    dsimp only [q4]; rw [M.mul_comm (p a) (p b)]
  have hq4_symm34 : ∀ a b c d, q4 a b c d = q4 a b d c := fun a b c d => by
    dsimp only [q4]; rw [M.mul_comm (p c) (p d)]
  have hq4_comm : ∀ a b c d, q4 a b c d = q4 c d a b := fun a b c d => by
    dsimp only [q4]; rw [M.mul_comm (M.mul (p a) (p b)) (M.mul (p c) (p d))]
  have hq4_class : ∀ a b c d,
      q4 b a c d = q4 a b c d ∧ q4 a b d c = q4 a b c d ∧ q4 b a d c = q4 a b c d ∧
      q4 c d a b = q4 a b c d ∧ q4 d c a b = q4 a b c d ∧
      q4 c d b a = q4 a b c d ∧ q4 d c b a = q4 a b c d := fun a b c d =>
    ⟨hq4_symm12 b a c d, hq4_symm34 a b d c,
     by rw [hq4_symm12 b a d c, hq4_symm34 a b d c],
     hq4_comm c d a b,
     by rw [hq4_symm12 d c a b, hq4_comm c d a b],
     by rw [hq4_symm34 c d b a, hq4_comm c d a b],
     by rw [hq4_symm12 d c b a, hq4_symm34 c d b a, hq4_comm c d a b]⟩
  simp only [perm4List, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hdiff_zero
  rw [ho_symm 1 0, ho_symm 2 0, ho_symm 3 0, ho_symm 2 1, ho_symm 3 1, ho_symm 3 2] at hdiff_zero
  obtain ⟨hR012a, hR012b, hR012c, hR012d, hR012e⟩ := hR_perm 0 1 2
  obtain ⟨hR013a, hR013b, hR013c, hR013d, hR013e⟩ := hR_perm 0 1 3
  obtain ⟨hR023a, hR023b, hR023c, hR023d, hR023e⟩ := hR_perm 0 2 3
  obtain ⟨hR123a, hR123b, hR123c, hR123d, hR123e⟩ := hR_perm 1 2 3
  rw [hR012a, hR012b, hR012c, hR012d, hR012e,
      hR013a, hR013b, hR013c, hR013d, hR013e,
      hR023a, hR023b, hR023c, hR023d, hR023e,
      hR123a, hR123b, hR123c, hR123d, hR123e] at hdiff_zero
  obtain ⟨hq1a, hq1b, hq1c, hq1d, hq1e, hq1f, hq1g⟩ := hq4_class 0 1 2 3
  obtain ⟨hq2a, hq2b, hq2c, hq2d, hq2e, hq2f, hq2g⟩ := hq4_class 0 2 1 3
  obtain ⟨hq3a, hq3b, hq3c, hq3d, hq3e, hq3f, hq3g⟩ := hq4_class 0 3 1 2
  rw [hq1a, hq1b, hq1c, hq1d, hq1e, hq1f, hq1g,
      hq2a, hq2b, hq2c, hq2d, hq2e, hq2f, hq2g,
      hq3a, hq3b, hq3c, hq3d, hq3e, hq3f, hq3g] at hdiff_zero
  dsimp only [q4] at hdiff_zero
  dsimp only [o, R]
  linarith

def albertRankThreeCubicModel : RankThreeCubicModel Albert where
  mul := jordanMul
  one := albertUnit
  tr :=
    { toFun := albertTrace
      map_add' := albertTrace_add
      map_smul' := albertTrace_smul }
  mul_comm := jordanMul_comm
  mul_add_left := jordanMul_add_left
  mul_smul_left := jordanMul_smul_left
  mul_one_left := jordanMul_albertUnit_left
  tr_one := by simp [albertTrace, albertUnit]
  tr_assoc x y z := NativeAnalysis.tracePairing_associative x y z
  cubic_identity x := by
    refine ⟨albertCubicNorm x, ?_⟩
    have h1 := jordanMul_albertSharp x
    rw [albertSharp_eq_jordanMul x, jordanMul_add_right, jordanMul_sub_right,
      jordanMul_smul_right, jordanMul_smul_right, jordanMul_albertUnit_right] at h1
    simpa [tracePairing] using h1

theorem albert_fourAtom_trace_relation (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    fpDoublePair1 p + fpDoublePair2 p + fpDoublePair3 p =
      1 / 2
        - 1 / 2 * (fpOverlap p 0 1 + fpOverlap p 0 2 + fpOverlap p 0 3
            + fpOverlap p 1 2 + fpOverlap p 1 3 + fpOverlap p 2 3)
        + 1 / 2 * (fpOverlap p 0 1 * fpOverlap p 2 3
            + fpOverlap p 0 2 * fpOverlap p 1 3 + fpOverlap p 0 3 * fpOverlap p 1 2)
        + fpTriangle p 0 1 2 + fpTriangle p 0 1 3 + fpTriangle p 0 2 3 + fpTriangle p 1 2 3 := by
  exact rankThree_fourIdempotent_trace_relation albertRankThreeCubicModel p
    (fun i => (hp i).1) (fun i => (hp i).2)

private theorem matrix_symMul_jordan_identity {n : ℕ} {K : Type*} [CommRing K] [Module ℝ K]
    [IsScalarTower ℝ K K] [SMulCommClass ℝ K K] (A B : Matrix (Fin n) (Fin n) K) :
    let symMul : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K :=
      fun X Y => (1 / 2 : ℝ) • (X * Y + Y * X)
    symMul (symMul A B) (symMul A A) = symMul A (symMul B (symMul A A)) := by
  intro symMul
  simp only [symMul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply]
  ring

theorem rankFour_unitVector_trace_relation_excess {n : ℕ}
    (v : Fin 4 → (Fin n → ℝ)) (hv : ∀ i, ∑ k, (v i k) ^ 2 = 1) :
    let P : Fin 4 → Matrix (Fin n) (Fin n) ℝ := fun i => Matrix.of (fun a b => v i a * v i b)
    let symMul : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
      fun A B => (1 / 2 : ℝ) • (A * B + B * A)
    let G : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (fun i j => ∑ k, v i k * v j k)
    let o := fun i j => Matrix.trace (symMul (P i) (P j))
    let R := fun i j k => Matrix.trace (symMul (symMul (P i) (P j)) (P k))
    let t1 := Matrix.trace (symMul (symMul (P 0) (P 1)) (symMul (P 2) (P 3)))
    let t2 := Matrix.trace (symMul (symMul (P 0) (P 2)) (symMul (P 1) (P 3)))
    let t3 := Matrix.trace (symMul (symMul (P 0) (P 3)) (symMul (P 1) (P 2)))
    (t1 + t2 + t3) -
      (1 / 2 - 1 / 2 * (o 0 1 + o 0 2 + o 0 3 + o 1 2 + o 1 3 + o 2 3)
        + 1 / 2 * (o 0 1 * o 2 3 + o 0 2 * o 1 3 + o 0 3 * o 1 2)
        + R 0 1 2 + R 0 1 3 + R 0 2 3 + R 1 2 3) = -(1 / 2 : ℝ) * G.det := by
  intro P symMul G o R t1 t2 t3
  let g : Fin 4 → Fin 4 → ℝ := fun i j => ∑ k, v i k * v j k
  have hg_symm : ∀ i j, g i j = g j i := fun i j => by
    dsimp only [g]
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hg_diag : ∀ i, g i i = 1 := fun i => by
    simpa only [g, sq] using hv i
  have hP_mul : ∀ i j : Fin 4,
      P i * P j = g i j • Matrix.of (fun a b => v i a * v j b) := by
    intro i j
    ext a b
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, P, g, smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  have htr_outer : ∀ i j : Fin 4,
      Matrix.trace (Matrix.of (fun a b => v i a * v j b)) = g i j := fun i j => by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, g]
  have h_o : ∀ i j, o i j = (g i j) ^ 2 := fun i j => by
    dsimp only [o, symMul]
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_comm (P j) (P i),
      hP_mul, Matrix.trace_smul, htr_outer]
    simp [smul_eq_mul]; ring
  have hP_mul3 : ∀ i j k : Fin 4,
      P i * P j * P k = (g i j * g j k) • Matrix.of (fun a b => v i a * v k b) := by
    intro i j k
    rw [hP_mul i j, Matrix.smul_mul]
    ext a b
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, P, g, smul_eq_mul]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ => by ring
  have h_R : ∀ i j k, R i j k = g i j * g j k * g k i := fun i j k => by
    dsimp only [R, symMul]
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.trace_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_mul_comm (P k), Matrix.trace_mul_comm (P k),
      Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (P i) (P j) (P k), ← Matrix.mul_assoc (P j) (P i) (P k),
      hP_mul3 i j k, hP_mul3 j i k,
      Matrix.trace_smul, Matrix.trace_smul, htr_outer i k, htr_outer j k,
      hg_symm j i, hg_symm i k, hg_symm j k]
    simp [smul_eq_mul]; ring
  have h_t : ∀ a b c d : Fin 4,
      Matrix.trace (symMul (symMul (P a) (P b)) (symMul (P c) (P d))) =
        (1 / 2 : ℝ) * (g a b * g b c * g c d * g d a + g a b * g b d * g d c * g c a) := by
    intro a b c d
    dsimp only [symMul]
    have h4 : ∀ p q r s : Fin 4,
        Matrix.trace (P p * P q * (P r * P s)) = g p q * g q r * g r s * g s p := by
      intro p q r s
      rw [hP_mul p q, hP_mul r s, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_smul, Matrix.trace_smul]
      have htr : Matrix.trace (Matrix.of (fun u w => v p u * v q w) *
          Matrix.of (fun u w => v r u * v s w)) = g q r * g s p := by
        have hm : Matrix.of (fun u w => v p u * v q w) * Matrix.of (fun u w => v r u * v s w) =
            g q r • Matrix.of (fun u w => v p u * v s w) := by
          ext u w
          simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, g, smul_eq_mul]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m _ => by ring
        rw [hm, Matrix.trace_smul, htr_outer p s, hg_symm p s]
        simp [smul_eq_mul]
      rw [htr]
      simp [smul_eq_mul]; ring
    rw [Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_mul_comm ((1 / 2 : ℝ) • (P c * P d + P d * P c)) ((1 / 2 : ℝ) • (P a * P b + P b * P a))]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    rw [h4 a b c d, h4 a b d c, h4 b a c d, h4 b a d c]
    rw [hg_symm b a, hg_symm d c, hg_symm b c, hg_symm d a, hg_symm b d, hg_symm c a]
    simp [smul_eq_mul]; ring
  have ht1' : t1 = (1 / 2 : ℝ) * (g 0 1 * g 1 2 * g 2 3 * g 3 0 + g 0 1 * g 1 3 * g 3 2 * g 2 0) :=
    h_t 0 1 2 3
  have ht2' : t2 = (1 / 2 : ℝ) * (g 0 2 * g 2 1 * g 1 3 * g 3 0 + g 0 2 * g 2 3 * g 3 1 * g 1 0) :=
    h_t 0 2 1 3
  have ht3' : t3 = (1 / 2 : ℝ) * (g 0 3 * g 3 1 * g 1 2 * g 2 0 + g 0 3 * g 3 2 * g 2 1 * g 1 0) :=
    h_t 0 3 1 2
  have hG_det : G.det =
      1 - (g 0 1 ^ 2 + g 0 2 ^ 2 + g 0 3 ^ 2 + g 1 2 ^ 2 + g 1 3 ^ 2 + g 2 3 ^ 2)
      + (g 0 1 ^ 2 * g 2 3 ^ 2 + g 0 2 ^ 2 * g 1 3 ^ 2 + g 0 3 ^ 2 * g 1 2 ^ 2)
      + 2 * (g 0 1 * g 1 2 * g 0 2 + g 0 1 * g 1 3 * g 0 3 + g 0 2 * g 2 3 * g 0 3 + g 1 2 * g 2 3 * g 1 3)
      - 2 * (g 0 1 * g 1 2 * g 2 3 * g 0 3 + g 0 1 * g 1 3 * g 2 3 * g 0 2 + g 0 2 * g 1 2 * g 1 3 * g 0 3) := by
    have hGg : ∀ i j : Fin 4, G i j = g i j := fun _ _ => rfl
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp only [Matrix.det_fin_three, Matrix.submatrix_apply, hGg,
      Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def, Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num
    simp only [hg_diag, hg_symm 1 0, hg_symm 2 0, hg_symm 3 0, hg_symm 2 1, hg_symm 3 1, hg_symm 3 2]
    ring
  rw [ht1', ht2', ht3', h_o, h_o, h_o, h_o, h_o, h_o, h_R, h_R, h_R, h_R, hG_det,
    hg_symm 1 0, hg_symm 2 0, hg_symm 3 0, hg_symm 2 1, hg_symm 3 1, hg_symm 3 2]
  ring

theorem rankFour_trace_relation_counterexample :
    ∃ (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ),
      let symMul : Matrix (Fin 4) (Fin 4) ℝ → Matrix (Fin 4) (Fin 4) ℝ → Matrix (Fin 4) (Fin 4) ℝ :=
        fun A B => (1 / 2 : ℝ) • (A * B + B * A)
      (∀ i, (P i)ᵀ = P i) ∧
      (∀ i, symMul (P i) (P i) = P i) ∧
      (∀ i, Matrix.trace (P i) = 1) ∧
      (∀ A B : Matrix (Fin 4) (Fin 4) ℝ,
        symMul (symMul A B) (symMul A A) = symMul A (symMul B (symMul A A))) ∧
      let o := fun i j => Matrix.trace (symMul (P i) (P j))
      let R := fun i j k => Matrix.trace (symMul (symMul (P i) (P j)) (P k))
      let t1 := Matrix.trace (symMul (symMul (P 0) (P 1)) (symMul (P 2) (P 3)))
      let t2 := Matrix.trace (symMul (symMul (P 0) (P 2)) (symMul (P 1) (P 3)))
      let t3 := Matrix.trace (symMul (symMul (P 0) (P 3)) (symMul (P 1) (P 2)))
      (t1 + t2 + t3) -
        (1 / 2 - 1 / 2 * (o 0 1 + o 0 2 + o 0 3 + o 1 2 + o 1 3 + o 2 3)
          + 1 / 2 * (o 0 1 * o 2 3 + o 0 2 * o 1 3 + o 0 3 * o 1 2)
          + R 0 1 2 + R 0 1 3 + R 0 2 3 + R 1 2 3) = -(1 / 2 : ℝ) := by
  let v : Fin 4 → (Fin 4 → ℝ) := fun i k => if i = k then 1 else 0
  have hv : ∀ i, ∑ k, (v i k) ^ 2 = 1 := fun i => by
    fin_cases i <;> simp [v]
  let P : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ := fun i => Matrix.of (fun a b => v i a * v i b)
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    ext a b
    simp [P, mul_comm]
  · intro i
    ext a b
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, P, v, smul_eq_mul]
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp <;> norm_num
  · intro i
    fin_cases i <;> simp [P, v, Matrix.trace]
  · intro A B
    exact matrix_symMul_jordan_identity A B
  · have hex := rankFour_unitVector_trace_relation_excess v hv
    have hG1 : Matrix.of (fun i j : Fin 4 => ∑ k, v i k * v j k) = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [v]
    dsimp only at hex
    rw [hG1, Matrix.det_one, mul_one] at hex
    exact hex

theorem rankFour_trace_relation_counterexample_complex :
    ∃ (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ),
      let symMul : Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ :=
        fun A B => (1 / 2 : ℝ) • (A * B + B * A)
      (∀ i, (P i)ᴴ = P i) ∧
      (∀ i, symMul (P i) (P i) = P i) ∧
      (∀ i, (Matrix.trace (P i)).re = 1) ∧
      (∀ A B : Matrix (Fin 4) (Fin 4) ℂ,
        symMul (symMul A B) (symMul A A) = symMul A (symMul B (symMul A A))) ∧
      let o := fun i j => (Matrix.trace (symMul (P i) (P j))).re
      let R := fun i j k => (Matrix.trace (symMul (symMul (P i) (P j)) (P k))).re
      let t1 := (Matrix.trace (symMul (symMul (P 0) (P 1)) (symMul (P 2) (P 3)))).re
      let t2 := (Matrix.trace (symMul (symMul (P 0) (P 2)) (symMul (P 1) (P 3)))).re
      let t3 := (Matrix.trace (symMul (symMul (P 0) (P 3)) (symMul (P 1) (P 2)))).re
      (t1 + t2 + t3) -
        (1 / 2 - 1 / 2 * (o 0 1 + o 0 2 + o 0 3 + o 1 2 + o 1 3 + o 2 3)
          + 1 / 2 * (o 0 1 * o 2 3 + o 0 2 * o 1 3 + o 0 3 * o 1 2)
          + R 0 1 2 + R 0 1 3 + R 0 2 3 + R 1 2 3) = -(1 / 2 : ℝ) := by
  let P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
    fun i => Matrix.of (fun a b => if a = i ∧ b = i then 1 else 0)
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, P]
    split_ifs <;> simp_all
  · intro i
    ext a b
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, P]
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp <;> norm_num
  · intro i
    fin_cases i <;> simp [P, Matrix.trace]
  · intro A B
    exact matrix_symMul_jordan_identity A B
  · have h0 : ∀ p q : Fin 4, p ≠ q → P p * P q = 0 := by
      intro p q hpq
      ext r s
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply, P]
      fin_cases p <;> fin_cases q <;> (try exact absurd rfl hpq) <;>
        fin_cases r <;> fin_cases s <;> simp
    have ho : ∀ i j : Fin 4, i ≠ j →
        (Matrix.trace ((1 / 2 : ℝ) • (P i * P j + P j * P i))).re = 0 := by
      intro i j hij
      rw [h0 i j hij, h0 j i hij.symm, add_zero, smul_zero, Matrix.trace_zero, Complex.zero_re]
    have hR : ∀ i j k : Fin 4, i ≠ j → j ≠ k → i ≠ k →
        (Matrix.trace ((1 / 2 : ℝ) • (((1 / 2 : ℝ) • (P i * P j + P j * P i)) * P k +
          P k * ((1 / 2 : ℝ) • (P i * P j + P j * P i))))).re = 0 := by
      intro i j k hij hjk hik
      rw [h0 i j hij, h0 j i hij.symm, add_zero, smul_zero, Matrix.zero_mul,
        Matrix.mul_zero, add_zero, smul_zero, Matrix.trace_zero, Complex.zero_re]
    have ht : ∀ a b c d : Fin 4,
        a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        (Matrix.trace ((1 / 2 : ℝ) • (((1 / 2 : ℝ) • (P a * P b + P b * P a)) *
          ((1 / 2 : ℝ) • (P c * P d + P d * P c)) +
          ((1 / 2 : ℝ) • (P c * P d + P d * P c)) *
          ((1 / 2 : ℝ) • (P a * P b + P b * P a))))).re = 0 := by
      intro a b c d hab hac had hbc hbd hcd
      simp only [h0 a b hab, h0 b a hab.symm, h0 c d hcd, h0 d c hcd.symm,
        add_zero, smul_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]
    dsimp only
    rw [ht 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ht 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ht 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ho 0 1 (by decide), ho 0 2 (by decide), ho 0 3 (by decide),
      ho 1 2 (by decide), ho 1 3 (by decide), ho 2 3 (by decide),
      hR 0 1 2 (by decide) (by decide) (by decide),
      hR 0 1 3 (by decide) (by decide) (by decide),
      hR 0 2 3 (by decide) (by decide) (by decide),
      hR 1 2 3 (by decide) (by decide) (by decide)]
    norm_num

/-! ## Section 3: Unrestricted Sparse Formula (`lem:A:Aform`) and `fixedS` Evaluation -/

theorem octDyad_real0_isAtom (v0 : ℝ) (v1 v2 : Octonion)
    (hnorm : v0 ^ 2 + octNormSq v1 + octNormSq v2 = 1) :
    IsAtom (octDyad ![octonionScalar v0, v1, v2]) := by
  let p := octDyad ![octonionScalar v0, v1, v2]
  have hd0 : p.1 0 = v0 ^ 2 := by
    change octNormSq (octonionScalar v0) = v0 ^ 2
    exact octNormSq_scalar v0
  have hd1 : p.1 1 = octNormSq v1 := rfl
  have hd2 : p.1 2 = octNormSq v2 := rfl
  have hu0 : p.2 0 = v0 • octonionConj v1 := by
    simp [p, octDyad, octonionMul_scalar_left]
  have hu1 : p.2 1 = v0 • octonionConj v2 := by
    simp [p, octDyad, octonionMul_scalar_left]
  have hu2 : p.2 2 = octonionMul v1 (octonionConj v2) := rfl
  constructor
  · apply albert_ext
    · rw [jordanMul_diag_0, hd0, hu0, hu1,
        octDot_smul_left, octDot_smul_right, octDot_smul_left, octDot_smul_right,
        octDot_self, octDot_self, octNormSq_conj, octNormSq_conj]
      nlinarith [hnorm]
    · rw [jordanMul_diag_1, hd1, hu0, hu2,
        octDot_smul_left, octDot_smul_right, octDot_self, octNormSq_conj,
        octDot_self, octNormSq_mul, octNormSq_conj]
      nlinarith [hnorm, octNormSq_nonneg v1, octNormSq_nonneg v2]
    · rw [jordanMul_diag_2, hd2, hu1, hu2,
        octDot_smul_left, octDot_smul_right, octDot_self, octNormSq_conj,
        octDot_self, octNormSq_mul, octNormSq_conj]
      nlinarith [hnorm, octNormSq_nonneg v1, octNormSq_nonneg v2]
    · rw [jordanMul_off_0, hd0, hd1, hu0, hu1, hu2,
        octonionConj_mul, octonionConj_conj, octonionMul_smul_left,
        octMul_conj_left_cancel, smul_smul, smul_smul]
      have hsc : (1 / 2 : ℝ) * (((v0 ^ 2 + octNormSq v1) * v0 +
          (v0 ^ 2 + octNormSq v1) * v0) + v0 * octNormSq v2 + v0 * octNormSq v2) = v0 := by
        have hlin : (1 / 2 : ℝ) * (((v0 ^ 2 + octNormSq v1) * v0 +
            (v0 ^ 2 + octNormSq v1) * v0) + v0 * octNormSq v2 + v0 * octNormSq v2) =
            (v0 ^ 2 + octNormSq v1 + octNormSq v2) * v0 := by ring
        rw [hlin, hnorm, one_mul]
      calc _ = ((1 / 2 : ℝ) * (((v0 ^ 2 + octNormSq v1) * v0 +
            (v0 ^ 2 + octNormSq v1) * v0) + v0 * octNormSq v2 + v0 * octNormSq v2)) •
          octonionConj v1 := by module
        _ = v0 • octonionConj v1 := by rw [hsc]
    · rw [jordanMul_off_1, hd0, hd2, hu0, hu1, hu2,
        octonionMul_smul_left, octMul_conj_left_cancel, smul_smul, smul_smul]
      have hsc : (1 / 2 : ℝ) * (((v0 ^ 2 + octNormSq v2) * v0 +
          (v0 ^ 2 + octNormSq v2) * v0) + v0 * octNormSq v1 + v0 * octNormSq v1) = v0 := by
        have hlin : (1 / 2 : ℝ) * (((v0 ^ 2 + octNormSq v2) * v0 +
            (v0 ^ 2 + octNormSq v2) * v0) + v0 * octNormSq v1 + v0 * octNormSq v1) =
            (v0 ^ 2 + octNormSq v1 + octNormSq v2) * v0 := by ring
        rw [hlin, hnorm, one_mul]
      calc _ = ((1 / 2 : ℝ) * (((v0 ^ 2 + octNormSq v2) * v0 +
            (v0 ^ 2 + octNormSq v2) * v0) + v0 * octNormSq v1 + v0 * octNormSq v1)) •
          octonionConj v2 := by module
        _ = v0 • octonionConj v2 := by rw [hsc]
    · rw [jordanMul_off_2, hd1, hd2, hu0, hu1, hu2,
        octonionConj_smul, octonionConj_conj, octonionMul_smul_left, octonionMul_smul_right,
        smul_smul]
      have hsc : (1 / 2 : ℝ) • ((octNormSq v1 + octNormSq v2) • octonionMul v1 (octonionConj v2) +
          (octNormSq v1 + octNormSq v2) • octonionMul v1 (octonionConj v2) +
          (v0 * v0) • octonionMul v1 (octonionConj v2) +
          (v0 * v0) • octonionMul v1 (octonionConj v2)) = octonionMul v1 (octonionConj v2) := by
        have hsum : (1 / 2 : ℝ) * ((octNormSq v1 + octNormSq v2) + (octNormSq v1 + octNormSq v2) +
            v0 * v0 + v0 * v0) = 1 := by nlinarith [hnorm]
        calc _ = ((1 / 2 : ℝ) * ((octNormSq v1 + octNormSq v2) + (octNormSq v1 + octNormSq v2) +
              v0 * v0 + v0 * v0)) • octonionMul v1 (octonionConj v2) := by module
          _ = octonionMul v1 (octonionConj v2) := by rw [hsum, one_smul]
      exact hsc
  · unfold albertTrace
    rw [Fin.sum_univ_three, hd0, hd1, hd2, hnorm]

def sparseFourConfigOct (B0 B1 C0 C1 C2 C3 D0 : ℝ) (X Y : Octonion) : Fin 4 → Albert :=
  ![octDyad ![octonionScalar 1, 0, 0],
    octDyad ![octonionScalar B0, octonionScalar B1, 0],
    octDyad ![octonionScalar C0, octonionScalar C1 + C2 • octI, octonionScalar C3],
    octDyad ![octonionScalar D0, X, Y]]

def sparseFourConfig (B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 : ℝ) (Y : Octonion) : Fin 4 → Albert :=
  sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 (octonionScalar x0 + x1 • octI + x2 • octJ) Y

private theorem sparse_p0_eq :
    octDyad ![octonionScalar 1, 0, 0] = diagAtom 0 := by
  apply albert_ext <;> simp [octDyad, diagAtom, octNormSq_scalar, octNormSq_zero,
    octonionConj_zero, octonionMul_zero_right]

private theorem sparse_octReal_eq_dot_one (x : Octonion) :
    octonionReal x = octDot x (octonionScalar 1) := by
  rw [octDot_scalar_right, one_mul]

theorem sparseFourConfigOct_traces (B0 B1 C0 C1 C2 C3 D0 : ℝ) (X Y : Octonion) :
    let p := sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y
    let z := octonionScalar C1 + C2 • octI
    let g1 := octonionScalar (B0 * C0) + B1 • z
    let g2 := octonionScalar (B0 * D0) + B1 • X
    let g3 := octonionScalar (C0 * D0) + octonionMul (octonionConj z) X + C3 • Y
    fpOverlap p 0 1 = B0 ^ 2 ∧
    fpOverlap p 0 2 = C0 ^ 2 ∧
    fpOverlap p 0 3 = D0 ^ 2 ∧
    fpOverlap p 1 2 = octNormSq g1 ∧
    fpOverlap p 1 3 = octNormSq g2 ∧
    fpOverlap p 2 3 = octNormSq g3 ∧
    fpTriangle p 0 1 2 = B0 * C0 * octonionReal g1 ∧
    fpTriangle p 0 1 3 = B0 * D0 * octonionReal g2 ∧
    fpTriangle p 0 2 3 = C0 * D0 * octonionReal g3 ∧
    fpTriangle p 1 2 3 = octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2)) ∧
    fpOmega1 p = C0 * D0 * octonionReal (octonionMul g1 (octonionConj g2)) ∧
    fpOmega2 p = B0 * D0 * octonionReal (octonionMul g1 g3) ∧
    fpOmega3 p = B0 * C0 * octonionReal (octonionMul g2 (octonionConj g3)) := by
  intro p z g1 g2 g3
  have hp0 : p 0 = diagAtom 0 := sparse_p0_eq
  have hp1_d0 : (p 1).1 0 = B0 ^ 2 := by
    simp [p, sparseFourConfigOct, octDyad, octNormSq_scalar]
  have hp1_d1 : (p 1).1 1 = B1 ^ 2 := by
    simp [p, sparseFourConfigOct, octDyad, octNormSq_scalar]
  have hp1_d2 : (p 1).1 2 = 0 := by simp [p, sparseFourConfigOct, octDyad, octNormSq_zero]
  have hp1_u0 : (p 1).2 0 = octonionScalar (B0 * B1) := by
    simp [p, sparseFourConfigOct, octDyad, octonionMul_scalar_left, octonionConj_scalar,
      octonionScalar_smul]
  have hp1_u1 : (p 1).2 1 = 0 := by
    simp [p, sparseFourConfigOct, octDyad, octonionConj_zero, octonionMul_zero_right]
  have hp1_u2 : (p 1).2 2 = 0 := by
    simp [p, sparseFourConfigOct, octDyad, octonionConj_zero, octonionMul_zero_right]
  have hp2_d0 : (p 2).1 0 = C0 ^ 2 := by
    simp [p, sparseFourConfigOct, octDyad, octNormSq_scalar]
  have hp2_d1 : (p 2).1 1 = octNormSq z := rfl
  have hp2_d2 : (p 2).1 2 = C3 ^ 2 := by
    simp [p, sparseFourConfigOct, octDyad, octNormSq_scalar]
  have hp2_u0 : (p 2).2 0 = C0 • octonionConj z := by
    simp [p, sparseFourConfigOct, octDyad, z, octonionMul_scalar_left]
  have hp2_u1 : (p 2).2 1 = octonionScalar (C0 * C3) := by
    simp [p, sparseFourConfigOct, octDyad, octonionMul_scalar_left, octonionConj_scalar,
      octonionScalar_smul]
  have hp2_u2 : (p 2).2 2 = C3 • z := by
    simp [p, sparseFourConfigOct, octDyad, z, octonionConj_scalar, octonionMul_scalar_right]
  have hp3_d0 : (p 3).1 0 = D0 ^ 2 := by
    simp [p, sparseFourConfigOct, octDyad, octNormSq_scalar]
  have hp3_d1 : (p 3).1 1 = octNormSq X := rfl
  have hp3_d2 : (p 3).1 2 = octNormSq Y := rfl
  have hp3_u0 : (p 3).2 0 = D0 • octonionConj X := by
    simp [p, sparseFourConfigOct, octDyad, octonionMul_scalar_left]
  have hp3_u1 : (p 3).2 1 = D0 • octonionConj Y := by
    simp [p, sparseFourConfigOct, octDyad, octonionMul_scalar_left]
  have hp3_u2 : (p 3).2 2 = octonionMul X (octonionConj Y) := rfl
  -- Useful dot/norm expansions for g1, g2, g3:
  have hg1_norm : octNormSq g1 = B0 ^ 2 * C0 ^ 2 + B1 ^ 2 * octNormSq z +
      2 * B0 * B1 * C0 * octonionReal z := by
    dsimp only [g1]
    rw [octNormSq_add, octNormSq_smul, octDot_smul_right, octDot_scalar_left, octNormSq_scalar]
    ring
  have hg2_norm : octNormSq g2 = B0 ^ 2 * D0 ^ 2 + B1 ^ 2 * octNormSq X +
      2 * B0 * B1 * D0 * octonionReal X := by
    dsimp only [g2]
    rw [octNormSq_add, octNormSq_smul, octDot_smul_right, octDot_scalar_left, octNormSq_scalar]
    ring
  have hcyc_zXY : octDot z (octonionMul X (octonionConj Y)) =
      octDot (octonionMul (octonionConj z) X) Y := by
    symm
    rw [octDot_mul_left, octonionConj_conj, octDot_comm, octDot_mul_right]
  have hg3_norm : octNormSq g3 = C0 ^ 2 * D0 ^ 2 + octNormSq z * octNormSq X + C3 ^ 2 * octNormSq Y +
      2 * C0 * D0 * octonionReal (octonionMul (octonionConj z) X) +
      2 * C0 * C3 * D0 * octonionReal Y +
      2 * C3 * octDot (octonionMul (octonionConj z) X) Y := by
    dsimp only [g3]
    rw [octNormSq_add, octNormSq_add, octNormSq_smul, octNormSq_mul, octNormSq_conj,
      octDot_smul_right, octDot_add_left, octDot_scalar_left, octDot_scalar_left,
      octNormSq_scalar]
    ring
  -- Now prove all 13 equations cleanly!
  have ho01 : fpOverlap p 0 1 = B0 ^ 2 := by
    rw [fpOverlap, hp0, tracePairing_diagAtom 0, hp1_d0]
  have ho02 : fpOverlap p 0 2 = C0 ^ 2 := by
    rw [fpOverlap, hp0, tracePairing_diagAtom 0, hp2_d0]
  have ho03 : fpOverlap p 0 3 = D0 ^ 2 := by
    rw [fpOverlap, hp0, tracePairing_diagAtom 0, hp3_d0]
  have ho12 : fpOverlap p 1 2 = octNormSq g1 := by
    rw [fpOverlap, tracePairing_eq_coords, hp1_d0, hp1_d1, hp1_d2, hp1_u0, hp1_u1, hp1_u2,
      hp2_d0, hp2_d1, hp2_d2, hp2_u0, hp2_u1, hp2_u2,
      octDot_zero_left, octDot_zero_left, octDot_smul_right, octDot_scalar_left,
      octonionReal_conj, hg1_norm]
    ring
  have ho13 : fpOverlap p 1 3 = octNormSq g2 := by
    rw [fpOverlap, tracePairing_eq_coords, hp1_d0, hp1_d1, hp1_d2, hp1_u0, hp1_u1, hp1_u2,
      hp3_d0, hp3_d1, hp3_d2, hp3_u0, hp3_u1, hp3_u2,
      octDot_zero_left, octDot_zero_left, octDot_smul_right, octDot_scalar_left,
      octonionReal_conj, hg2_norm]
    ring
  have ho23 : fpOverlap p 2 3 = octNormSq g3 := by
    rw [fpOverlap, tracePairing_eq_coords, hp2_d0, hp2_d1, hp2_d2, hp2_u0, hp2_u1, hp2_u2,
      hp3_d0, hp3_d1, hp3_d2, hp3_u0, hp3_u1, hp3_u2,
      octDot_smul_left, octDot_smul_right, octDot_smul_right, octDot_scalar_left, octDot_smul_left,
      octonionReal_conj, hcyc_zXY, hg3_norm]
    have hdot_conj : octDot (octonionConj z) (octonionConj X) =
        octonionReal (octonionMul (octonionConj z) X) := by
      unfold octDot
      rw [octonionConj_conj]
    rw [hdot_conj]
    ring
  have hR012 : fpTriangle p 0 1 2 = B0 * C0 * octonionReal g1 := by
    rw [fpTriangle, NativeAnalysis.tracePairing_associative, hp0, tracePairing_diagAtom 0,
      jordanMul_diag_0, hp1_d0, hp1_u0, hp1_u1, hp2_d0, hp2_u0, hp2_u1,
      octDot_zero_left, octDot_smul_right, octDot_scalar_left, octonionReal_conj]
    simp only [g1, z, octonionReal_add, octonionReal_smul, octonionReal_scalar]
    ring
  have hR013 : fpTriangle p 0 1 3 = B0 * D0 * octonionReal g2 := by
    rw [fpTriangle, NativeAnalysis.tracePairing_associative, hp0, tracePairing_diagAtom 0,
      jordanMul_diag_0, hp1_d0, hp1_u0, hp1_u1, hp3_d0, hp3_u0, hp3_u1,
      octDot_zero_left, octDot_smul_right, octDot_scalar_left, octonionReal_conj]
    dsimp only [g2]
    rw [octonionReal_add, octonionReal_smul, octonionReal_scalar]
    ring
  have hR023 : fpTriangle p 0 2 3 = C0 * D0 * octonionReal g3 := by
    rw [fpTriangle, NativeAnalysis.tracePairing_associative, hp0, tracePairing_diagAtom 0,
      jordanMul_diag_0, hp2_d0, hp2_u0, hp2_u1, hp3_d0, hp3_u0, hp3_u1,
      octDot_smul_left, octDot_smul_right, octDot_smul_right, octDot_scalar_left, octonionReal_conj]
    have hdot : octDot (octonionConj z) (octonionConj X) =
        octonionReal (octonionMul (octonionConj z) X) := by
      unfold octDot; rw [octonionConj_conj]
    rw [hdot]
    dsimp only [g3]
    rw [octonionReal_add, octonionReal_add, octonionReal_smul, octonionReal_scalar]
    ring
  -- For `R123` and `ω1, ω2, ω3`, use explicit `jordanMul (p 1) (p 2)`, `jordanMul (p 1) (p 3)`, `jordanMul (p 2) (p 3)` entries!
  have hj12_d0 : (jordanMul (p 1) (p 2)).1 0 = B0 * C0 * octonionReal g1 := by
    rw [← tracePairing_diagAtom 0, ← hp0, ← NativeAnalysis.tracePairing_associative]
    exact hR012
  have hj12_d1 : (jordanMul (p 1) (p 2)).1 1 =
      B1 ^ 2 * octNormSq z + B0 * B1 * C0 * octonionReal z := by
    rw [jordanMul_diag_1, hp1_d1, hp1_u0, hp1_u2, hp2_d1, hp2_u0, hp2_u2,
      octDot_zero_left, octDot_smul_right, octDot_scalar_left, octonionReal_conj]
    ring
  have hj12_d2 : (jordanMul (p 1) (p 2)).1 2 = 0 := by
    rw [jordanMul_diag_2, hp1_d2, hp1_u1, hp1_u2, hp2_d2, hp2_u1, hp2_u2,
      octDot_zero_left, octDot_zero_left]
    ring
  have hj12_u0 : (jordanMul (p 1) (p 2)).2 0 =
      (1 / 2 : ℝ) • (B0 • octonionMul (octonionConj z) g1 + (B1 * C0) • octonionConj g1) := by
    rw [jordanMul_off_0, hp1_d0, hp1_d1, hp1_u0, hp1_u1, hp1_u2,
      hp2_d0, hp2_d1, hp2_u0, hp2_u1, hp2_u2,
      octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right, add_zero, add_zero]
    dsimp only [g1]
    rw [octonionMul_add_right, octonionMul_smul_right, octonionMul_scalar_right,
      octMul_conj_self,
      octonionConj_add, octonionConj_smul, octonionConj_scalar,
      octonionScalar_eq_smul (B0 * B1), octonionScalar_eq_smul (B0 * C0),
      octonionScalar_eq_smul (octNormSq z)]
    have hcz_exp : octonionScalar C1 + C2 • octonionConj octI = octonionConj z := by
      dsimp only [z]
      rw [octonionConj_add, octonionConj_smul, octonionConj_scalar]
    have hcg1_exp : octonionConj ((B0 * C0) • octonionScalar 1 + B1 • z) =
        (B0 * C0) • octonionScalar 1 + B1 • octonionConj z := by
      rw [octonionConj_add, octonionConj_smul, octonionConj_smul, octonionConj_scalar]
    rw [hcz_exp, hcg1_exp]
    have hlhs : (1 / 2 : ℝ) • ((B0 ^ 2 + B1 ^ 2) • C0 • octonionConj z +
          (C0 ^ 2 + octNormSq z) • (B0 * B1) • octonionScalar 1) =
        ((1 / 2 : ℝ) * ((B0 ^ 2 + B1 ^ 2) * C0)) • octonionConj z +
        ((1 / 2 : ℝ) * ((C0 ^ 2 + octNormSq z) * (B0 * B1))) • octonionScalar 1 := by
      simp only [smul_add, smul_smul]
    have hrhs : (1 / 2 : ℝ) • (B0 • ((B0 * C0) • octonionConj z + B1 • (octNormSq z • octonionScalar 1)) +
          (B1 * C0) • ((B0 * C0) • octonionScalar 1 + B1 • octonionConj z)) =
        ((1 / 2 : ℝ) * (B0 * (B0 * C0)) + (1 / 2 : ℝ) * ((B1 * C0) * B1)) • octonionConj z +
        ((1 / 2 : ℝ) * (B0 * (B1 * octNormSq z)) + (1 / 2 : ℝ) * ((B1 * C0) * (B0 * C0))) •
          octonionScalar 1 := by
      simp only [smul_add, smul_smul, add_smul]
      abel
    rw [hlhs, hrhs]
    congr 1
    · congr 1; ring
    · congr 1; ring
  have hj12_u1 : (jordanMul (p 1) (p 2)).2 1 = (1 / 2 : ℝ) • ((B0 * C3) • g1) := by
    rw [jordanMul_off_1, hp1_d0, hp1_d2, hp1_u0, hp1_u1, hp1_u2,
      hp2_d0, hp2_d2, hp2_u0, hp2_u1, hp2_u2,
      octonionMul_zero_right, add_zero, smul_zero, add_zero]
    dsimp only [g1]
    rw [octonionMul_smul_right, octonionMul_scalar_left,
      octonionScalar_eq_smul (C0 * C3), octonionScalar_eq_smul (B0 * C0)]
    simp only [smul_add, smul_smul]
    module
  have hj12_u2 : (jordanMul (p 1) (p 2)).2 2 = (1 / 2 : ℝ) • ((B1 * C3) • g1) := by
    rw [jordanMul_off_2, hp1_d1, hp1_d2, hp1_u0, hp1_u1, hp1_u2,
      hp2_d1, hp2_d2, hp2_u0, hp2_u1, hp2_u2,
      octonionConj_scalar, octonionMul_zero_right, add_zero]
    dsimp only [g1]
    rw [octonionMul_scalar_left, octonionScalar_eq_smul (C0 * C3),
      octonionScalar_eq_smul (B0 * C0)]
    simp only [smul_add, smul_smul]
    module
  -- Useful helper: `conj z` commutes with `g1` since both lie in `span {1, i}`
  have hcz_g1_comm : octonionMul (octonionConj z) g1 = octonionMul g1 (octonionConj z) := by
    dsimp only [g1]
    rw [octonionMul_add_right, octonionMul_add_left, octonionMul_scalar_right,
      octonionMul_scalar_left, octonionMul_smul_right, octonionMul_smul_left,
      octMul_conj_self, octMul_self_conj]
  -- Alternativity: `[g1, conj z, X] = 0`
  have halt_zX : octonionMul (octonionMul g1 (octonionConj z)) X =
      octonionMul g1 (octonionMul (octonionConj z) X) := by
    obtain ⟨φ, hφ, hz_mem, hX_mem⟩ := exists_quatEmbedding_containing_pair octI X
    have hz_range : z ∈ Set.range φ := by
      rcases hz_mem with ⟨qi, hqi⟩
      dsimp only [z]
      rw [octonionScalar_eq_smul]
      exact ⟨C1 • 1 + C2 • qi, by simp [hφ.map_one, hqi]⟩
    have hcz_range : octonionConj z ∈ Set.range φ := by
      rcases hz_range with ⟨qz, hqz⟩
      exact ⟨star qz, by rw [hφ.map_star, hqz]⟩
    have hg1_range : g1 ∈ Set.range φ := by
      rcases hz_range with ⟨qz, hqz⟩
      dsimp only [g1]
      rw [octonionScalar_eq_smul]
      exact ⟨(B0 * C0) • 1 + B1 • qz, by simp [hφ.map_one, hqz]⟩
    have h0 := octAssociator_eq_zero_of_quatEmbedding φ hφ hg1_range hcz_range hX_mem
    unfold octAssociator at h0
    exact sub_eq_zero.mp h0
  -- Prove R123:
  have hR123 : fpTriangle p 1 2 3 = octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2)) := by
    rw [fpTriangle, tracePairing_eq_coords, hj12_d0, hj12_d1, hj12_d2, hj12_u0, hj12_u1, hj12_u2,
      hp3_d0, hp3_d1, hp3_d2, hp3_u0, hp3_u1, hp3_u2]
    have h_u0 : 2 * octDot ((1 / 2 : ℝ) • (B0 • octonionMul (octonionConj z) g1 +
          (B1 * C0) • octonionConj g1)) (D0 • octonionConj X) =
        B0 * D0 * octonionReal (octonionMul (octonionMul g1 (octonionConj z)) X) +
        B1 * C0 * D0 * octonionReal (octonionMul g1 (octonionConj X)) := by
      rw [octDot_smul_left, octDot_smul_right, octDot_add_left, octDot_smul_left, octDot_smul_left,
        hcz_g1_comm]
      have h1 : octDot (octonionMul g1 (octonionConj z)) (octonionConj X) =
          octonionReal (octonionMul (octonionMul g1 (octonionConj z)) X) := by
        unfold octDot; rw [octonionConj_conj]
      have h2 : octDot (octonionConj g1) (octonionConj X) =
          octonionReal (octonionMul g1 (octonionConj X)) := by
        unfold octDot
        rw [octonionConj_conj, ← octonionReal_conj, octonionConj_mul, octonionConj_conj,
          octonionReal_mul_comm]
      rw [h1, h2]; ring
    have h_u1 : 2 * octDot ((1 / 2 : ℝ) • ((B0 * C3) • g1)) (D0 • octonionConj Y) =
        B0 * C3 * D0 * octonionReal (octonionMul g1 Y) := by
      rw [octDot_smul_left, octDot_smul_left, octDot_smul_right]
      have h1 : octDot g1 (octonionConj Y) = octonionReal (octonionMul g1 Y) := by
        unfold octDot; rw [octonionConj_conj]
      rw [h1]; ring
    have h_u2 : 2 * octDot ((1 / 2 : ℝ) • ((B1 * C3) • g1)) (octonionMul X (octonionConj Y)) =
        B1 * C3 * octonionReal (octonionMul (octonionMul g1 Y) (octonionConj X)) := by
      rw [octDot_smul_left, octDot_smul_left, octDot_comm, octDot_mul_right, octonionConj_conj,
        octDot_comm]
      have h1 : octDot (octonionMul g1 Y) X =
          octonionReal (octonionMul (octonionMul g1 Y) (octonionConj X)) := rfl
      rw [h1]; ring
    have h_d1 : (B1 ^ 2 * octNormSq z + B0 * B1 * C0 * octonionReal z) * octNormSq X =
        B1 * octonionReal (octonionMul (octonionMul (octonionMul g1 (octonionConj z)) X) (octonionConj X)) := by
      rw [octMul_conj_right_cancel, octonionReal_smul]
      have hgz : octonionReal (octonionMul g1 (octonionConj z)) =
          B0 * C0 * octonionReal z + B1 * octNormSq z := by
        dsimp only [g1]
        rw [octonionMul_add_left, octonionMul_smul_left, octonionMul_scalar_left,
          octonionReal_add, octonionReal_smul, octonionReal_smul, octonionReal_conj,
          octMul_self_conj, octonionReal_scalar]
      rw [hgz]; ring
    have h_lhs : B0 * C0 * octonionReal g1 * D0 ^ 2 +
        (B1 ^ 2 * octNormSq z + B0 * B1 * C0 * octonionReal z) * octNormSq X + 0 * octNormSq Y +
        2 * (octDot ((1 / 2 : ℝ) • (B0 • octonionMul (octonionConj z) g1 +
              (B1 * C0) • octonionConj g1)) (D0 • octonionConj X) +
          octDot ((1 / 2 : ℝ) • ((B0 * C3) • g1)) (D0 • octonionConj Y) +
          octDot ((1 / 2 : ℝ) • ((B1 * C3) • g1)) (octonionMul X (octonionConj Y))) =
        B0 * C0 * D0 ^ 2 * octonionReal g1 +
        B1 * C0 * D0 * octonionReal (octonionMul g1 (octonionConj X)) +
        B0 * D0 * octonionReal (octonionMul (octonionMul g1 (octonionConj z)) X) +
        B1 * octonionReal (octonionMul (octonionMul (octonionMul g1 (octonionConj z)) X) (octonionConj X)) +
        B0 * C3 * D0 * octonionReal (octonionMul g1 Y) +
        B1 * C3 * octonionReal (octonionMul (octonionMul g1 Y) (octonionConj X)) := by
      linarith [h_u0, h_u1, h_u2, h_d1]
    rw [h_lhs]
    -- Now expand RHS `octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2))`:
    dsimp only [g3, g2]
    simp only [octonionMul_add_right, octonionMul_smul_right, octonionMul_scalar_right,
      octonionConj_add, octonionConj_smul, octonionConj_scalar,
      octonionMul_add_left, octonionMul_smul_left,
      octonionReal_add, octonionReal_smul, halt_zX]
    ring
  -- Now prove t1, t2, t3 formulas using the first-row rule:
  have hrow0 : ∀ x y : Albert,
      tracePairing (jordanMul (diagAtom 0) x) y =
        x.1 0 * y.1 0 + octDot (x.2 0) (y.2 0) + octDot (x.2 1) (y.2 1) := fun x y => by
    rw [NativeAnalysis.tracePairing_associative, tracePairing_diagAtom 0, jordanMul_diag_0]
  have ht1_eq : 2 * fpDoublePair1 p =
      B0 * C0 * octonionReal (octonionMul g2 (octonionConj g3)) +
      B0 * D0 * octonionReal (octonionMul g1 g3) := by
    unfold fpDoublePair1
    rw [hp0, hrow0, hp1_d0, hp1_u0, hp1_u1, octDot_zero_left, add_zero]
    have hj23_d0 : (jordanMul (p 2) (p 3)).1 0 = C0 * D0 * octonionReal g3 := by
      rw [← tracePairing_diagAtom 0, ← hp0, ← NativeAnalysis.tracePairing_associative]
      exact hR023
    have hj23_u0 : (jordanMul (p 2) (p 3)).2 0 =
        (1 / 2 : ℝ) • (C0 • octonionMul g3 (octonionConj X) +
          D0 • octonionMul (octonionConj g3) (octonionConj z)) := by
      rw [jordanMul_off_0, hp2_d0, hp2_d1, hp2_u0, hp2_u1, hp2_u2,
        hp3_d0, hp3_d1, hp3_u0, hp3_u1, hp3_u2]
      dsimp only [g3]
      simp only [octonionConj_add, octonionConj_smul, octonionConj_scalar,
        octonionConj_mul, octonionConj_conj,
        octonionMul_add_left, octonionMul_smul_left, octonionMul_scalar_left,
        octMul_conj_right_cancel]
      simp only [octonionMul_smul_right, smul_add, smul_smul]
      module
    rw [hj23_d0, hj23_u0, octDot_smul_right, octDot_scalar_left]
    simp only [octonionReal_add, octonionReal_smul]
    have hg2g3 : octonionReal (octonionMul g2 (octonionConj g3)) =
        B0 * D0 * octonionReal g3 + B1 * octonionReal (octonionMul g3 (octonionConj X)) := by
      dsimp only [g2]
      rw [octonionMul_add_left, octonionMul_smul_left, octonionMul_scalar_left,
        octonionReal_add, octonionReal_smul, octonionReal_smul, octonionReal_conj,
        octonionReal_mul_comm X (octonionConj g3), ← octonionReal_conj (octonionMul (octonionConj g3) X),
        octonionConj_mul, octonionConj_conj, octonionReal_mul_comm (octonionConj X) g3]
    have hg1g3 : octonionReal (octonionMul g1 g3) =
        B0 * C0 * octonionReal g3 + B1 * octonionReal (octonionMul (octonionConj g3) (octonionConj z)) := by
      dsimp only [g1]
      rw [octonionMul_add_left, octonionMul_smul_left, octonionMul_scalar_left,
        octonionReal_add, octonionReal_smul, octonionReal_smul,
        ← octonionReal_conj (octonionMul z g3), octonionConj_mul]
    rw [hg2g3, hg1g3]
    ring
  have ht2_eq : 2 * fpDoublePair2 p =
      B0 * C0 * octonionReal (octonionMul g2 (octonionConj g3)) +
      C0 * D0 * octonionReal (octonionMul g1 (octonionConj g2)) := by
    unfold fpDoublePair2
    rw [hp0, hrow0, hp2_d0, hp2_u0, hp2_u1]
    have hj13_d0 : (jordanMul (p 1) (p 3)).1 0 = B0 * D0 * octonionReal g2 := by
      rw [← tracePairing_diagAtom 0, ← hp0, ← NativeAnalysis.tracePairing_associative]
      exact hR013
    have hj13_u0 : (jordanMul (p 1) (p 3)).2 0 =
        (1 / 2 : ℝ) • (B0 • octonionMul g2 (octonionConj X) +
          (B1 * D0) • octonionConj g2) := by
      rw [jordanMul_off_0, hp1_d0, hp1_d1, hp1_u0, hp1_u1, hp1_u2,
        hp3_d0, hp3_d1, hp3_u0, hp3_u1, hp3_u2,
        octonionConj_zero, octonionMul_zero_left, octonionMul_zero_right, add_zero, add_zero]
      dsimp only [g2]
      rw [octonionMul_add_left, octonionMul_smul_left, octonionMul_scalar_left,
        octMul_self_conj,
        octonionConj_add, octonionConj_smul, octonionConj_scalar,
        octonionScalar_eq_smul (B0 * B1), octonionScalar_eq_smul (B0 * D0),
        octonionScalar_eq_smul (octNormSq X)]
      simp only [smul_add, smul_smul]
      module
    have hj13_u1 : (jordanMul (p 1) (p 3)).2 1 =
        (1 / 2 : ℝ) • (B0 • octonionMul g2 (octonionConj Y)) := by
      rw [jordanMul_off_1, hp1_d0, hp1_d2, hp1_u0, hp1_u1, hp1_u2,
        hp3_d0, hp3_d2, hp3_u0, hp3_u1, hp3_u2,
        octonionMul_zero_right, add_zero, add_zero]
      dsimp only [g2]
      rw [octonionMul_add_left, octonionMul_smul_left, octonionMul_scalar_left,
        octonionMul_scalar_left]
      simp only [smul_zero, add_zero, smul_add, smul_smul]
      congr 1
      congr 1; ring
    rw [hj13_d0, hj13_u0, hj13_u1]
    have hdot1 : octDot (C0 • octonionConj z) ((1 / 2 : ℝ) • (B0 • octonionMul g2 (octonionConj X) +
          (B1 * D0) • octonionConj g2)) =
        (1 / 2 : ℝ) * (B0 * C0 * octonionReal (octonionMul g2 (octonionMul (octonionConj X) z)) +
          B1 * C0 * D0 * octonionReal (octonionMul g2 (octonionConj z))) := by
      rw [octDot_smul_left, octDot_smul_right, octDot_add_right, octDot_smul_right, octDot_smul_right]
      have ha : octDot (octonionConj z) (octonionMul g2 (octonionConj X)) =
          octonionReal (octonionMul g2 (octonionMul (octonionConj X) z)) := by
        rw [octDot_comm, octDot_mul_right, octonionConj_conj]
        unfold octDot
        rw [octonionConj_mul, octonionConj_conj]
      have hb : octDot (octonionConj z) (octonionConj g2) =
          octonionReal (octonionMul g2 (octonionConj z)) := by
        unfold octDot
        rw [octonionConj_conj, octonionReal_mul_comm]
      rw [ha, hb]; ring
    have hdot2 : octDot (octonionScalar (C0 * C3))
          ((1 / 2 : ℝ) • (B0 • octonionMul g2 (octonionConj Y))) =
        (1 / 2 : ℝ) * (B0 * C0 * C3 * octonionReal (octonionMul g2 (octonionConj Y))) := by
      rw [octDot_smul_right, octDot_smul_right, octDot_scalar_left, octonionReal_mul_comm]
      ring
    rw [hdot1, hdot2]
    have hg2g3 : octonionReal (octonionMul g2 (octonionConj g3)) =
        C0 * D0 * octonionReal g2 +
        octonionReal (octonionMul g2 (octonionMul (octonionConj X) z)) +
        C3 * octonionReal (octonionMul g2 (octonionConj Y)) := by
      dsimp only [g3]
      rw [octonionConj_add, octonionConj_add, octonionConj_scalar, octonionConj_smul,
        octonionConj_mul, octonionConj_conj, octonionMul_add_right, octonionMul_add_right,
        octonionMul_scalar_right, octonionMul_smul_right, octonionReal_add, octonionReal_add,
        octonionReal_smul, octonionReal_smul]
    have hg1g2 : octonionReal (octonionMul g1 (octonionConj g2)) =
        B0 * C0 * octonionReal (octonionConj g2) +
        B1 * octonionReal (octonionMul g2 (octonionConj z)) := by
      dsimp only [g1]
      rw [octonionMul_add_left, octonionMul_smul_left, octonionMul_scalar_left,
        octonionReal_add, octonionReal_smul, octonionReal_smul,
        ← octonionReal_conj (octonionMul z (octonionConj g2)), octonionConj_mul, octonionConj_conj]
    rw [hg2g3, hg1g2, octonionReal_conj]
    ring
  have ht3_eq : 2 * fpDoublePair3 p =
      B0 * D0 * octonionReal (octonionMul g1 g3) +
      C0 * D0 * octonionReal (octonionMul g1 (octonionConj g2)) := by
    unfold fpDoublePair3
    rw [hp0, hrow0, hp3_d0, hp3_u0, hp3_u1, hj12_d0, hj12_u0, hj12_u1]
    have hdot1 : octDot (D0 • octonionConj X) ((1 / 2 : ℝ) • (B0 • octonionMul (octonionConj z) g1 +
          (B1 * C0) • octonionConj g1)) =
        (1 / 2 : ℝ) * (B0 * D0 * octonionReal (octonionMul g1 (octonionMul (octonionConj z) X)) +
          B1 * C0 * D0 * octonionReal (octonionMul g1 (octonionConj X))) := by
      rw [octDot_smul_left, octDot_smul_right, octDot_add_right, octDot_smul_right, octDot_smul_right,
        hcz_g1_comm]
      have ha : octDot (octonionConj X) (octonionMul g1 (octonionConj z)) =
          octonionReal (octonionMul g1 (octonionMul (octonionConj z) X)) := by
        rw [octDot_comm]; unfold octDot; rw [octonionConj_conj, halt_zX]
      have hb : octDot (octonionConj X) (octonionConj g1) =
          octonionReal (octonionMul g1 (octonionConj X)) := by
        unfold octDot
        rw [octonionConj_conj, octonionReal_mul_comm]
      rw [ha, hb]; ring
    have hdot2 : octDot (D0 • octonionConj Y) ((1 / 2 : ℝ) • ((B0 * C3) • g1)) =
        (1 / 2 : ℝ) * (B0 * D0 * C3 * octonionReal (octonionMul g1 Y)) := by
      rw [octDot_smul_left, octDot_smul_right, octDot_smul_right]
      have ha : octDot (octonionConj Y) g1 = octonionReal (octonionMul g1 Y) := by
        rw [octDot_comm]; unfold octDot; rw [octonionConj_conj]
      rw [ha]; ring
    rw [hdot1, hdot2]
    have hg1g3 : octonionReal (octonionMul g1 g3) =
        C0 * D0 * octonionReal g1 +
        octonionReal (octonionMul g1 (octonionMul (octonionConj z) X)) +
        C3 * octonionReal (octonionMul g1 Y) := by
      dsimp only [g3]
      rw [octonionMul_add_right, octonionMul_add_right, octonionMul_scalar_right,
        octonionMul_smul_right, octonionReal_add, octonionReal_add, octonionReal_smul, octonionReal_smul]
    have hg1g2 : octonionReal (octonionMul g1 (octonionConj g2)) =
        B0 * D0 * octonionReal g1 + B1 * octonionReal (octonionMul g1 (octonionConj X)) := by
      dsimp only [g2]
      rw [octonionConj_add, octonionConj_smul, octonionConj_scalar,
        octonionMul_add_right, octonionMul_smul_right, octonionMul_scalar_right,
        octonionReal_add, octonionReal_smul, octonionReal_smul]
    rw [hg1g3, hg1g2]
    ring
  refine ⟨ho01, ho02, ho03, ho12, ho13, ho23, hR012, hR013, hR023, hR123, ?_, ?_, ?_⟩
  · unfold fpOmega1; linarith [ht1_eq, ht2_eq, ht3_eq]
  · unfold fpOmega2; linarith [ht1_eq, ht2_eq, ht3_eq]
  · unfold fpOmega3; linarith [ht1_eq, ht2_eq, ht3_eq]

def fpGramMatrix (_oAB _oAC _oAD oBC oBD oCD RABC RABD RACD ω1 ω2 ω3 a b c : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let x1 := RABC / (a * b)
  let x2 := RABD / (a * c)
  let x3 := RACD / (b * c)
  Matrix.of ![![oBC - x1 ^ 2, ω1 / (b * c) - x1 * x2, x1 * x3 - ω2 / (a * c)],
    ![ω1 / (b * c) - x1 * x2, oBD - x2 ^ 2, ω3 / (a * b) - x2 * x3],
    ![x1 * x3 - ω2 / (a * c), ω3 / (a * b) - x2 * x3, oCD - x3 ^ 2]]

def fpGramTripleScalar (_oAB _oAC _oAD _oBC _oBD _oCD RABC RABD RACD RBCD ω1 ω2 ω3 a b c : ℝ) : ℝ :=
  let x1 := RABC / (a * b)
  let x2 := RABD / (a * c)
  let x3 := RACD / (b * c)
  let G12 := ω1 / (b * c) - x1 * x2
  let G13 := x1 * x3 - ω2 / (a * c)
  let G23 := ω3 / (a * b) - x2 * x3
  RBCD - x1 * x2 * x3 + x2 * G13 - x1 * G23 - x3 * G12

def fpGramMatrixPoly (d1 d2 d3 x1 x2 x3 r q t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![d1 - x1 ^ 2, r - x1 * x2, x1 * x3 - q],
    ![r - x1 * x2, d2 - x2 ^ 2, t - x2 * x3],
    ![x1 * x3 - q, t - x2 * x3, d3 - x3 ^ 2]]

def fpGramTriplePoly (x1 x2 x3 r q t R : ℝ) : ℝ :=
  R + 2 * x1 * x2 * x3 - (x3 * r + x2 * q + x1 * t)

private theorem gramDet_sub_sq_eq (d1 d2 d3 x1 x2 x3 r q t R : ℝ) :
    (fpGramMatrixPoly d1 d2 d3 x1 x2 x3 r q t).det - (fpGramTriplePoly x1 x2 x3 r q t R) ^ 2 =
      d1 * d2 * d3 - x1 ^ 2 * d2 * d3 - x2 ^ 2 * d1 * d3 - x3 ^ 2 * d1 * d2
        - R ^ 2 - 4 * x1 * x2 * x3 * R
        - d1 * t ^ 2 - d2 * q ^ 2 - d3 * r ^ 2
        + 2 * r * (x1 * x2 * d3 + x3 * R)
        + 2 * q * (x1 * x3 * d2 + x2 * R)
        + 2 * t * (x2 * x3 * d1 + x1 * R)
        - 2 * r * q * t := by
  rw [Matrix.det_fin_three]
  unfold fpGramMatrixPoly fpGramTriplePoly
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem fourPointOmegaPoly_det_poly (a b c d1 d2 d3 x1 x2 x3 r q t R : ℝ) :
    a ^ 2 * b ^ 2 * c ^ 2 *
      ((fpGramMatrixPoly d1 d2 d3 x1 x2 x3 r q t).det - (fpGramTriplePoly x1 x2 x3 r q t R) ^ 2) =
      fourPointOmegaPoly (a ^ 2) (b ^ 2) (c ^ 2) d1 d2 d3
        (a * b * x1) (a * c * x2) (b * c * x3) R (b * c * r) (a * c * q) (a * b * t) := by
  rw [gramDet_sub_sq_eq]
  unfold fourPointOmegaPoly
  ring

theorem fourPointOmegaPoly_eq_gram_det
    (oAB oAC oAD oBC oBD oCD RABC RABD RACD RBCD ω1 ω2 ω3 a b c : ℝ)
    (ha : a ^ 2 = oAB) (hb : b ^ 2 = oAC) (hc : c ^ 2 = oAD)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    a ^ 2 * b ^ 2 * c ^ 2 *
      ((fpGramMatrix oAB oAC oAD oBC oBD oCD RABC RABD RACD ω1 ω2 ω3 a b c).det -
       (fpGramTripleScalar oAB oAC oAD oBC oBD oCD RABC RABD RACD RBCD ω1 ω2 ω3 a b c) ^ 2) =
      fourPointOmegaPoly oAB oAC oAD oBC oBD oCD RABC RABD RACD RBCD ω1 ω2 ω3 := by
  have hdet := fourPointOmegaPoly_det_poly a b c oBC oBD oCD
    (RABC / (a * b)) (RABD / (a * c)) (RACD / (b * c))
    (ω1 / (b * c)) (ω2 / (a * c)) (ω3 / (a * b)) RBCD
  have hG : fpGramMatrix oAB oAC oAD oBC oBD oCD RABC RABD RACD ω1 ω2 ω3 a b c =
      fpGramMatrixPoly oBC oBD oCD
        (RABC / (a * b)) (RABD / (a * c)) (RACD / (b * c))
        (ω1 / (b * c)) (ω2 / (a * c)) (ω3 / (a * b)) := rfl
  have hs : fpGramTripleScalar oAB oAC oAD oBC oBD oCD RABC RABD RACD RBCD ω1 ω2 ω3 a b c =
      fpGramTriplePoly (RABC / (a * b)) (RABD / (a * c)) (RACD / (b * c))
        (ω1 / (b * c)) (ω2 / (a * c)) (ω3 / (a * b)) RBCD := by
    unfold fpGramTripleScalar fpGramTriplePoly
    ring
  rw [hG, hs, hdet, ha, hb, hc]
  have hab : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have hac : a * c ≠ 0 := mul_ne_zero ha0 hc0
  have hbc : b * c ≠ 0 := mul_ne_zero hb0 hc0
  rw [mul_div_cancel₀ _ hab, mul_div_cancel₀ _ hac, mul_div_cancel₀ _ hbc,
    mul_div_cancel₀ _ hbc, mul_div_cancel₀ _ hac, mul_div_cancel₀ _ hab]

theorem fpGramMatrixPoly_eq_octonion_gram (g1 g2 g3 : Octonion) :
    fpGramMatrixPoly (octNormSq g1) (octNormSq g2) (octNormSq g3)
      (octonionReal g1) (octonionReal g2) (octonionReal g3)
      (octonionReal (octonionMul g1 (octonionConj g2)))
      (octonionReal (octonionMul g1 g3))
      (octonionReal (octonionMul g2 (octonionConj g3))) =
      Matrix.of (fun k l : Fin 3 => octDot (![octIm g1, octIm g2, octIm g3] k) (![octIm g1, octIm g2, octIm g3] l)) := by
  have hsplit_norm : ∀ g : Octonion, octNormSq g - (octonionReal g) ^ 2 = octDot (octIm g) (octIm g) := by
    intro g
    have h : g = octonionScalar (octonionReal g) + octIm g := by simp [octIm]
    conv_lhs =>
      arg 1
      rw [← octDot_self, h, octDot_add_left, octDot_add_right, octDot_add_right,
        octDot_scalar_octIm, octDot_comm (octIm g) (octonionScalar _), octDot_scalar_octIm,
        octDot_scalar_left, octonionReal_scalar]
    ring
  have hsplit_conj : ∀ a b : Octonion,
      octonionReal (octonionMul a (octonionConj b)) - octonionReal a * octonionReal b =
        octDot (octIm a) (octIm b) := fun a b => by
    have ha : a = octonionScalar (octonionReal a) + octIm a := by simp [octIm]
    have hb : b = octonionScalar (octonionReal b) + octIm b := by simp [octIm]
    conv_lhs =>
      arg 1
      change octDot a b
      rw [ha, hb, octDot_add_left, octDot_add_right, octDot_add_right, octDot_scalar_octIm,
        octDot_comm (octIm a) (octonionScalar _), octDot_scalar_octIm,
        octDot_scalar_left, octonionReal_scalar]
    ring
  have hsplit_mul : ∀ a b : Octonion,
      octonionReal a * octonionReal b - octonionReal (octonionMul a b) =
        octDot (octIm a) (octIm b) := fun a b => by
    rw [octonionReal_mul_split]; ring
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp only [fpGramMatrixPoly, Matrix.of_apply]
  · exact hsplit_norm g1
  · exact hsplit_conj g1 g2
  · exact hsplit_mul g1 g3
  · rw [octDot_comm]; exact hsplit_conj g1 g2
  · exact hsplit_norm g2
  · exact hsplit_conj g2 g3
  · rw [octDot_comm]; exact hsplit_mul g1 g3
  · rw [octDot_comm]; exact hsplit_conj g2 g3
  · exact hsplit_norm g3

theorem fpGramTriplePoly_eq_octonion_cross (g1 g2 g3 : Octonion) :
    fpGramTriplePoly (octonionReal g1) (octonionReal g2) (octonionReal g3)
      (octonionReal (octonionMul g1 (octonionConj g2)))
      (octonionReal (octonionMul g1 g3))
      (octonionReal (octonionMul g2 (octonionConj g3)))
      (octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2))) =
      octDot (octCross (octIm g1) (octIm g3)) (octIm g2) := by
  let u1 := octIm g1
  let u2 := octIm g2
  let u3 := octIm g3
  have hs1 : octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2)) =
      octonionReal g1 * octonionReal g3 * octonionReal g2
      - octonionReal g2 * octDot u1 u3
      + octonionReal g1 * octDot u3 u2
      + octonionReal g3 * octDot u1 u2
      + octDot (octCross u1 u3) u2 := by
    have hg1 : g1 = octonionScalar (octonionReal g1) + u1 := by simp [u1, octIm]
    have hg2 : g2 = octonionScalar (octonionReal g2) + u2 := by simp [u2, octIm]
    have hg3 : g3 = octonionScalar (octonionReal g3) + u3 := by simp [u3, octIm]
    have hconj2 : octonionConj g2 = octonionScalar (octonionReal g2) - u2 := by
      conv_lhs => rw [hg2]
      rw [octonionConj_add, octonionConj_scalar, octConj_octIm]
      abel
    have hu13 : octonionMul u1 u3 = (-octDot u1 u3) • octonionScalar 1 + octCross u1 u3 := by
      rw [octonionMul_imag_eq (octonionReal_octIm g1) (octonionReal_octIm g3), octOne_eq_scalar]
    have hre_prod : octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2)) =
        octonionReal (octonionMul g1 g3) * octonionReal (octonionConj g2) -
        octDot (octIm (octonionMul g1 g3)) (octIm (octonionConj g2)) :=
      octonionReal_mul_split _ _
    have hsc_sub : ∀ a b : ℝ, octonionScalar (a - b) = octonionScalar a - octonionScalar b := by
      intro a b
      rw [sub_eq_add_neg, octonionScalar_add, octonionScalar_eq_smul (-b), octonionScalar_eq_smul b]
      module
    have hg13 : octonionMul g1 g3 =
        octonionScalar (octonionReal g1 * octonionReal g3 - octDot u1 u3) +
        (octonionReal g1 • u3 + octonionReal g3 • u1 + octCross u1 u3) := by
      have hsc_neg : ∀ a : ℝ, octonionScalar (-a) = -octonionScalar a := by
        intro a
        rw [← neg_one_mul a, octonionScalar_eq_smul, octonionScalar_eq_smul a]
        module
      conv_lhs => rw [hg1, hg3]
      rw [octonionMul_add_left, octonionMul_add_right, octonionMul_add_right,
        octonionMul_scalar_left, octonionMul_scalar_left, octonionMul_scalar_right,
        ← octonionScalar_smul, hu13, ← octonionScalar_smul, mul_one, hsc_sub, hsc_neg]
      abel
    have him13 : octIm (octonionMul g1 g3) =
        octonionReal g1 • u3 + octonionReal g3 • u1 + octCross u1 u3 := by
      rw [hg13, octIm_add, octIm_scalar, zero_add,
        (octIm_eq_self_iff _).mpr (by
          rw [octonionReal_add, octonionReal_add, octonionReal_smul, octonionReal_smul,
            octonionReal_octIm, octonionReal_octIm, octonionReal_octCross]; ring)]
    have him_c2 : octIm (octonionConj g2) = -u2 := by
      rw [hconj2, octIm_sub, octIm_scalar, zero_sub, (octIm_eq_self_iff _).mpr (octonionReal_octIm g2)]
    rw [hre_prod, octonionReal_conj, octonionReal_mul_split g1 g3, him13, him_c2,
      octDot_neg_right, octDot_add_left, octDot_add_left, octDot_smul_left, octDot_smul_left]
    change _ = _
    dsimp only [u1, u2, u3]
    ring
  unfold fpGramTriplePoly
  have him_conj : ∀ g : Octonion, octIm (octonionConj g) = -octIm g := fun g => by
    have hg : g = octonionScalar (octonionReal g) + octIm g := by simp [octIm]
    rw [octIm, octonionReal_conj]
    conv_lhs => arg 1; rw [hg]
    rw [octonionConj_add, octonionConj_scalar, octConj_octIm]
    abel
  rw [hs1, octonionReal_mul_split g1 g3]
  have hc12 : octonionReal (octonionMul g1 (octonionConj g2)) =
      octonionReal g1 * octonionReal g2 + octDot u1 u2 := by
    rw [octonionReal_mul_split, octonionReal_conj, him_conj g2]
    change octonionReal g1 * octonionReal g2 - octDot u1 (-u2) = _
    rw [octDot_neg_right]; ring
  have hc23 : octonionReal (octonionMul g2 (octonionConj g3)) =
      octonionReal g2 * octonionReal g3 + octDot u2 u3 := by
    rw [octonionReal_mul_split, octonionReal_conj, him_conj g3]
    change octonionReal g2 * octonionReal g3 - octDot u2 (-u3) = _
    rw [octDot_neg_right]; ring
  rw [hc12, hc23, octDot_comm u3 u2]
  ring

theorem sparseFourConfigOct_fourPointInvariant
    (B0 B1 C0 C1 C2 C3 D0 : ℝ) (X Y : Octonion) :
    fourPointInvariant (sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y) =
      (1 / 4 : ℝ) * B0 ^ 2 * B1 ^ 4 * C0 ^ 2 * C2 ^ 2 * C3 ^ 2 * D0 ^ 2 *
        octNormSq (octAssociator octI X Y) := by
  let p := sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y
  let z := octonionScalar C1 + C2 • octI
  let g1 := octonionScalar (B0 * C0) + B1 • z
  let g2 := octonionScalar (B0 * D0) + B1 • X
  let g3 := octonionScalar (C0 * D0) + octonionMul (octonionConj z) X + C3 • Y
  have htr := sparseFourConfigOct_traces B0 B1 C0 C1 C2 C3 D0 X Y
  rcases htr with ⟨ho01, ho02, ho03, ho12, ho13, ho23, hR012, hR013, hR023, hR123, hω1, hω2, hω3⟩
  have hfp : fourPointInvariant p =
      B0 ^ 2 * C0 ^ 2 * D0 ^ 2 *
        ((fpGramMatrixPoly (octNormSq g1) (octNormSq g2) (octNormSq g3)
          (octonionReal g1) (octonionReal g2) (octonionReal g3)
          (octonionReal (octonionMul g1 (octonionConj g2)))
          (octonionReal (octonionMul g1 g3))
          (octonionReal (octonionMul g2 (octonionConj g3)))).det -
         (fpGramTriplePoly (octonionReal g1) (octonionReal g2) (octonionReal g3)
          (octonionReal (octonionMul g1 (octonionConj g2)))
          (octonionReal (octonionMul g1 g3))
          (octonionReal (octonionMul g2 (octonionConj g3)))
          (octonionReal (octonionMul (octonionMul g1 g3) (octonionConj g2)))) ^ 2) := by
    rw [fourPointOmegaPoly_det_poly B0 C0 D0]
    unfold fourPointInvariant
    rw [ho01, ho02, ho03, ho12, ho13, ho23, hR012, hR013, hR023, hR123, hω1, hω2, hω3]
  have hG_eq := fpGramMatrixPoly_eq_octonion_gram g1 g2 g3
  have hs_eq := fpGramTriplePoly_eq_octonion_cross g1 g2 g3
  rw [hfp, hG_eq, hs_eq, harvey_lawson_132 g1 g2 g3]
  -- Now reduce `octAssociator g1 g3 g2 = (B1 ^ 2 * C2 * C3) • octAssociator octI Y X`:
  have hassoc_red : octAssociator g1 g3 g2 = (B1 ^ 2 * C2 * C3) • octAssociator octI Y X := by
    dsimp only [g1, g2, g3, z]
    rw [octAssociator_add_left, octAssociator_scalar_left, zero_add, octAssociator_smul_left]
    rw [octAssociator_add_right, octAssociator_scalar_right, zero_add, octAssociator_smul_right]
    rw [octAssociator_add_mid, octAssociator_add_mid, octAssociator_scalar_mid, zero_add,
      octAssociator_smul_mid]
    have hzx : octAssociator (octonionScalar C1 + C2 • octI)
        (octonionMul (octonionConj (octonionScalar C1 + C2 • octI)) X) X = 0 := by
      obtain ⟨φ, hφ, hi_mem, hX_mem⟩ := exists_quatEmbedding_containing_pair octI X
      have hz_mem : octonionScalar C1 + C2 • octI ∈ Set.range φ := by
        rcases hi_mem with ⟨qi, hqi⟩
        rw [octonionScalar_eq_smul]
        exact ⟨C1 • 1 + C2 • qi, by simp [hφ.map_one, hqi]⟩
      have hcz_mem : octonionConj (octonionScalar C1 + C2 • octI) ∈ Set.range φ := by
        rcases hz_mem with ⟨qz, hqz⟩
        exact ⟨star qz, by rw [hφ.map_star, hqz]⟩
      have hczX_mem : octonionMul (octonionConj (octonionScalar C1 + C2 • octI)) X ∈ Set.range φ := by
        rcases hcz_mem with ⟨q1, hq1⟩
        rcases hX_mem with ⟨q2, hq2⟩
        exact ⟨q1 * q2, by rw [hφ.map_mul, hq1, hq2]⟩
      exact octAssociator_eq_zero_of_quatEmbedding φ hφ hz_mem hczX_mem hX_mem
    rw [hzx, zero_add, octAssociator_add_left, octAssociator_scalar_left, zero_add,
      octAssociator_smul_left, smul_smul, smul_smul, smul_smul]
    congr 1; ring
  rw [hassoc_red, octNormSq_smul, octAssociator_swap_23 octI Y X, octNormSq_neg]
  ring

theorem sparseFourConfig_fourPointInvariant
    (B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 y0 y1 y2 y3 y4 : ℝ) :
    let Y := octonionScalar y0 + y1 • octI + y2 • octJ + y3 • octK + y4 • octL
    fourPointInvariant (sparseFourConfig B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 Y) =
      B0 ^ 2 * B1 ^ 4 * C0 ^ 2 * C2 ^ 2 * C3 ^ 2 * D0 ^ 2 * x2 ^ 2 * y4 ^ 2 := by
  intro Y
  unfold sparseFourConfig
  rw [sparseFourConfigOct_fourPointInvariant]
  have hass : octAssociator octI (octonionScalar x0 + x1 • octI + x2 • octJ) Y =
      (x2 * y4) • octAssociator octI octJ octL := by
    rw [octAssociator_add_mid, octAssociator_add_mid, octAssociator_scalar_mid,
      octAssociator_smul_mid, octAssociator_self_left, smul_zero, zero_add, zero_add,
      octAssociator_smul_mid]
    dsimp only [Y]
    rw [octAssociator_add_right, octAssociator_add_right, octAssociator_add_right,
      octAssociator_add_right, octAssociator_scalar_right,
      octAssociator_smul_right, octAssociator_smul_right, octAssociator_smul_right,
      octAssociator_smul_right]
    have hIJ_I : octAssociator octI octJ octI = 0 := octAssociator_self_outer octI octJ
    have hIJ_J : octAssociator octI octJ octJ = 0 := octAssociator_self_right octI octJ
    have hIJ_K : octAssociator octI octJ octK = 0 := by
      have h1 : octI ∈ Set.range quatEmbed1 := ⟨⟨0, 1, 0, 0⟩, by apply oct_ext <;> simp [quatEmbed1_apply, octI]⟩
      have h2 : octJ ∈ Set.range quatEmbed1 := ⟨⟨0, 0, 1, 0⟩, by apply oct_ext <;> simp [quatEmbed1_apply, octJ]⟩
      have h3 : octK ∈ Set.range quatEmbed1 := ⟨⟨0, 0, 0, 1⟩, by apply oct_ext <;> simp [quatEmbed1_apply, octK]⟩
      exact octAssociator_eq_zero_of_quatEmbedding quatEmbed1 quatEmbed1_isQuatEmbedding h1 h2 h3
    rw [hIJ_I, hIJ_J, hIJ_K, smul_zero, smul_zero, smul_zero,
      add_zero, add_zero, add_zero, zero_add, smul_smul]
  rw [hass, octNormSq_smul, octNormSq_octAssociator_I_J_L]
  ring

theorem fourPointInvariant_fixedS :
    fourPointInvariant fixedS = 1 / 5832 := by
  have hQ := nativeCornerQ_eq_fpOmega fixedS
  have hQf := nativeCornerQ_fixedS
  rw [hQf] at hQ
  have hω2 : fpOmega2 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 0) hQ.symm
  have hω3 : fpOmega3 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 1) hQ.symm
  have hω1 : fpOmega1 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 2) hQ.symm
  have ho : ∀ i j : Fin 4, i ≠ j →
      fpOverlap fixedS i j = if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 / 2 else 1 / 3 := by
    intro i j hij
    change nativeOverlaps fixedS i j = _
    rw [nativeOverlaps_fixedS_eq]
    simp [hij]
  have hR012 : fpTriangle fixedS 0 1 2 = 1 / 6 := by
    rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]
    simp [fixedSTriangleVal]
  have hR013 : fpTriangle fixedS 0 1 3 = 1 / 6 := by
    rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]
    simp [fixedSTriangleVal]
  have hR023 : fpTriangle fixedS 0 2 3 = 1 / 9 := by
    rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]
    simp [fixedSTriangleVal]
  have hR123 : fpTriangle fixedS 1 2 3 = 1 / 9 := by
    rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]
    simp [fixedSTriangleVal]
  unfold fourPointInvariant fourPointOmegaPoly
  rw [ho 0 1 (by decide), ho 0 2 (by decide), ho 0 3 (by decide),
    ho 1 2 (by decide), ho 1 3 (by decide), ho 2 3 (by decide),
    hR012, hR013, hR023, hR123, hω1, hω2, hω3]
  norm_num

/-! ## Section 4: Tetrahedral Determinant Identity (`prop:Dacal`) -/

def tetraQOfTraces (t : Fin 3 → ℝ) (j k l m : Fin 4) : ℝ :=
  t (unorderedPairClass j m) + t (unorderedPairClass j k) - t (unorderedPairClass j l)

def fpTetraDtet (σ : Equiv.Perm (Fin 4))
    (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  let j := σ 0
  let k := σ 1
  let l := σ 2
  let m := σ 3
  let ν1 := Real.sqrt (o j k * o k l * o l j)
  let ν2 := Real.sqrt (o j l * o l m * o m j)
  let ν3 := Real.sqrt (o j m * o m k * o k j)
  let c1 := R j k l / ν1
  let c2 := R j l m / ν2
  let c3 := R j m k / ν3
  let c4 := R k l m / Real.sqrt (o k l * o l m * o m k)
  let K12 := tetraQOfTraces t j k l m / Real.sqrt (o j k * o k l * o l m * o m j)
  let K23 := tetraQOfTraces t j l m k / Real.sqrt (o j l * o l m * o m k * o k j)
  let K31 := tetraQOfTraces t j m k l / Real.sqrt (o j m * o m k * o k l * o l j)
  let M11 := 1 - c1 ^ 2
  let M22 := 1 - c2 ^ 2
  let M33 := 1 - c3 ^ 2
  let M12 := c1 * c2 - K12
  let M23 := c2 * c3 - K23
  let M13 := c3 * c1 - K31
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![![M11, M12, M13], ![M12, M22, M23], ![M13, M23, M33]]
  let S := c1 * c2 * c3 - c1 * M23 - c2 * M13 - c3 * M12
  M.det - (c4 - S) ^ 2

private theorem prop_Dacal_poly_id
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i)
    (hpos : ∀ i j, i ≠ j → 0 < o i j)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (_hR12 : ∀ i j k, R i j k = R j i k) (hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ) :
    fpTetraDtet 1 o R t *
        (o 0 1 * o 0 2 * o 0 3 * o 1 2 * o 1 3 * o 2 3) =
      fourPointTracePoly (o 0 1) (o 0 2) (o 0 3) (o 1 2) (o 1 3) (o 2 3)
        (R 0 1 2) (R 0 1 3) (R 0 2 3) (R 1 2 3) (t 0) (t 1) (t 2) := by
  let a := Real.sqrt (o 0 1)
  let b := Real.sqrt (o 0 2)
  let c := Real.sqrt (o 0 3)
  let d := Real.sqrt (o 1 2)
  let e' := Real.sqrt (o 1 3)
  let f := Real.sqrt (o 2 3)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (hpos 0 1 (by decide))
  have hb0 : 0 < b := Real.sqrt_pos.mpr (hpos 0 2 (by decide))
  have hc0 : 0 < c := Real.sqrt_pos.mpr (hpos 0 3 (by decide))
  have hd0 : 0 < d := Real.sqrt_pos.mpr (hpos 1 2 (by decide))
  have he0 : 0 < e' := Real.sqrt_pos.mpr (hpos 1 3 (by decide))
  have hf0 : 0 < f := Real.sqrt_pos.mpr (hpos 2 3 (by decide))
  have ha2 : a ^ 2 = o 0 1 := Real.sq_sqrt (hpos 0 1 (by decide)).le
  have hb2 : b ^ 2 = o 0 2 := Real.sq_sqrt (hpos 0 2 (by decide)).le
  have hc2 : c ^ 2 = o 0 3 := Real.sq_sqrt (hpos 0 3 (by decide)).le
  have hd2 : d ^ 2 = o 1 2 := Real.sq_sqrt (hpos 1 2 (by decide)).le
  have he2 : e' ^ 2 = o 1 3 := Real.sq_sqrt (hpos 1 3 (by decide)).le
  have hf2 : f ^ 2 = o 2 3 := Real.sq_sqrt (hpos 2 3 (by decide)).le
  let ω1 := t 1 + t 2 - t 0
  let ω2 := t 0 + t 2 - t 1
  let ω3 := t 0 + t 1 - t 2
  have hQ12 : tetraQOfTraces t 0 1 2 3 = ω2 := by
    simp [tetraQOfTraces, unorderedPairClass, ω2]; ring
  have hQ23 : tetraQOfTraces t 0 2 3 1 = ω3 := by
    simp [tetraQOfTraces, unorderedPairClass, ω3]
  have hQ31 : tetraQOfTraces t 0 3 1 2 = ω1 := by
    simp [tetraQOfTraces, unorderedPairClass, ω1]
  have hnu1 : Real.sqrt (o 0 1 * o 1 2 * o 2 0) = a * b * d := by
    rw [ho 2 0, ← ha2, ← hb2, ← hd2,
      show a ^ 2 * d ^ 2 * b ^ 2 = (a * b * d) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hnu2 : Real.sqrt (o 0 2 * o 2 3 * o 3 0) = b * c * f := by
    rw [ho 3 0, ← hb2, ← hc2, ← hf2,
      show b ^ 2 * f ^ 2 * c ^ 2 = (b * c * f) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hnu3 : Real.sqrt (o 0 3 * o 3 1 * o 1 0) = a * c * e' := by
    rw [ho 3 1, ho 1 0, ← ha2, ← hc2, ← he2,
      show c ^ 2 * e' ^ 2 * a ^ 2 = (a * c * e') ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hnu4 : Real.sqrt (o 1 2 * o 2 3 * o 3 1) = d * e' * f := by
    rw [ho 3 1, ← hd2, ← he2, ← hf2,
      show d ^ 2 * f ^ 2 * e' ^ 2 = (d * e' * f) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hK1 : Real.sqrt (o 0 1 * o 1 2 * o 2 3 * o 3 0) = a * c * d * f := by
    rw [ho 3 0, ← ha2, ← hc2, ← hd2, ← hf2,
      show a ^ 2 * d ^ 2 * f ^ 2 * c ^ 2 = (a * c * d * f) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hK2 : Real.sqrt (o 0 2 * o 2 3 * o 3 1 * o 1 0) = a * b * e' * f := by
    rw [ho 3 1, ho 1 0, ← ha2, ← hb2, ← he2, ← hf2,
      show b ^ 2 * f ^ 2 * e' ^ 2 * a ^ 2 = (a * b * e' * f) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hK3 : Real.sqrt (o 0 3 * o 3 1 * o 1 2 * o 2 0) = b * c * d * e' := by
    rw [ho 3 1, ho 2 0, ← hb2, ← hc2, ← hd2, ← he2,
      show c ^ 2 * e' ^ 2 * d ^ 2 * b ^ 2 = (b * c * d * e') ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hgram := fourPointOmegaPoly_eq_gram_det
    (o 0 1) (o 0 2) (o 0 3) (o 1 2) (o 1 3) (o 2 3)
    (R 0 1 2) (R 0 1 3) (R 0 2 3) (R 1 2 3) ω1 ω2 ω3 a b c
    ha2 hb2 hc2 ha0.ne' hb0.ne' hc0.ne'
  unfold fourPointTracePoly
  rw [← hgram]
  have hR_031 : R 0 3 1 = R 0 1 3 := hR23 0 3 1
  unfold fpTetraDtet
  simp only [Equiv.Perm.one_apply]
  rw [hQ12, hQ23, hQ31, hnu1, hnu2, hnu3, hnu4, hK1, hK2, hK3, hR_031]
  unfold fpGramMatrix fpGramTripleScalar
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [← ha2, ← hb2, ← hc2, ← hd2, ← he2, ← hf2]
  field_simp [ha0.ne', hb0.ne', hc0.ne', hd0.ne', he0.ne', hf0.ne']
  ring

private theorem overlap_prod_perm (σ : Equiv.Perm (Fin 4))
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i) :
    o (σ 0) (σ 1) * o (σ 0) (σ 2) * o (σ 0) (σ 3) *
      o (σ 1) (σ 2) * o (σ 1) (σ 3) * o (σ 2) (σ 3) =
    o 0 1 * o 0 2 * o 0 3 * o 1 2 * o 1 3 * o 2 3 := by
  let P (o' : Fin 4 → Fin 4 → ℝ) : ℝ :=
    o' 0 1 * o' 0 2 * o' 0 3 * o' 1 2 * o' 1 3 * o' 2 3
  have hadj : ∀ (s : Equiv.Perm (Fin 4)),
      s = Equiv.swap 0 1 ∨ s = Equiv.swap 1 2 ∨ s = Equiv.swap 2 3 →
      ∀ o' : Fin 4 → Fin 4 → ℝ, (∀ a b, o' a b = o' b a) →
        P (fun i j => o' (s i) (s j)) = P o' := by
    intro s hs o' ho'
    rcases hs with rfl | rfl | rfl
    · simp only [P, swap01_0, swap01_1, swap01_2, swap01_3]
      rw [ho' 1 0]; ring
    · simp only [P, swap12_0, swap12_1, swap12_2, swap12_3]
      rw [ho' 2 1]; ring
    · simp only [P, swap23_0, swap23_1, swap23_2, swap23_3]
      rw [ho' 3 2]; ring
  have hmul : ∀ (τ π : Equiv.Perm (Fin 4)),
      (∀ o' : Fin 4 → Fin 4 → ℝ, (∀ a b, o' a b = o' b a) → P (fun i j => o' (τ i) (τ j)) = P o') →
      (∀ o' : Fin 4 → Fin 4 → ℝ, (∀ a b, o' a b = o' b a) → P (fun i j => o' (π i) (π j)) = P o') →
      ∀ o' : Fin 4 → Fin 4 → ℝ, (∀ a b, o' a b = o' b a) →
        P (fun i j => o' ((τ * π) i) ((τ * π) j)) = P o' := by
    intro τ π hτ hπ o' ho'
    simp only [Equiv.Perm.mul_apply]
    rw [hπ (fun i j => o' (τ i) (τ j)) (fun i j => ho' (τ i) (τ j)), hτ o' ho']
  have hsw : ∀ i j : Fin 4, ∀ o' : Fin 4 → Fin 4 → ℝ, (∀ a b, o' a b = o' b a) →
      P (fun a b => o' (Equiv.swap i j a) (Equiv.swap i j b)) = P o' := by
    have h01 := hadj (Equiv.swap 0 1) (Or.inl rfl)
    have h12 := hadj (Equiv.swap 1 2) (Or.inr (Or.inl rfl))
    have h23 := hadj (Equiv.swap 2 3) (Or.inr (Or.inr rfl))
    have h02 : ∀ o' : Fin 4 → Fin 4 → ℝ, (∀ a b, o' a b = o' b a) →
        P (fun a b => o' (Equiv.swap 0 2 a) (Equiv.swap 0 2 b)) = P o' := by
      have h : Equiv.swap (0 : Fin 4) 2 = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
        ext x; fin_cases x <;> decide
      rw [h]; exact hmul _ _ (hmul _ _ h01 h12) h01
    have h13 : ∀ o' : Fin 4 → Fin 4 → ℝ, (∀ a b, o' a b = o' b a) →
        P (fun a b => o' (Equiv.swap 1 3 a) (Equiv.swap 1 3 b)) = P o' := by
      have h : Equiv.swap (1 : Fin 4) 3 = Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 1 2 := by
        ext x; fin_cases x <;> decide
      rw [h]; exact hmul _ _ (hmul _ _ h12 h23) h12
    have h03 : ∀ o' : Fin 4 → Fin 4 → ℝ, (∀ a b, o' a b = o' b a) →
        P (fun a b => o' (Equiv.swap 0 3 a) (Equiv.swap 0 3 b)) = P o' := by
      have h : Equiv.swap (0 : Fin 4) 3 =
          Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
        ext x; fin_cases x <;> decide
      rw [h]; exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ h01 h12) h23) h12) h01
    intro i j o' ho'
    fin_cases i <;> fin_cases j
    · simp
    · exact h01 o' ho'
    · exact h02 o' ho'
    · exact h03 o' ho'
    · rw [Equiv.swap_comm]; exact h01 o' ho'
    · simp
    · exact h12 o' ho'
    · exact h13 o' ho'
    · rw [Equiv.swap_comm]; exact h02 o' ho'
    · rw [Equiv.swap_comm]; exact h12 o' ho'
    · simp
    · exact h23 o' ho'
    · rw [Equiv.swap_comm]; exact h03 o' ho'
    · rw [Equiv.swap_comm]; exact h13 o' ho'
    · rw [Equiv.swap_comm]; exact h23 o' ho'
    · simp
  have hall : ∀ π : Equiv.Perm (Fin 4), ∀ o' : Fin 4 → Fin 4 → ℝ,
      (∀ a b, o' a b = o' b a) → P (fun i j => o' (π i) (π j)) = P o' := by
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one => intros; rfl
    | swap_mul π x y _ ih => exact hmul (Equiv.swap x y) π (hsw x y) ih
  exact hall σ o ho

private theorem tetraQOfTraces_pairTraceSelector (t : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 4)) :
    tetraQOfTraces (pairTraceSelector t σ) 0 1 2 3 = tetraQOfTraces t (σ 0) (σ 1) (σ 2) (σ 3) ∧
    tetraQOfTraces (pairTraceSelector t σ) 0 2 3 1 = tetraQOfTraces t (σ 0) (σ 2) (σ 3) (σ 1) ∧
    tetraQOfTraces (pairTraceSelector t σ) 0 3 1 2 = tetraQOfTraces t (σ 0) (σ 3) (σ 1) (σ 2) := by
  have h03 : unorderedPairClass (0 : Fin 4) 3 = 2 := by decide
  have h01 : unorderedPairClass (0 : Fin 4) 1 = 0 := by decide
  have h02 : unorderedPairClass (0 : Fin 4) 2 = 1 := by decide
  simp [tetraQOfTraces, pairTraceSelector, h03, h01, h02]

theorem prop_Dacal_poly (σ : Equiv.Perm (Fin 4))
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i)
    (hpos : ∀ i j, i ≠ j → 0 < o i j)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR12 : ∀ i j k, R i j k = R j i k) (hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ) :
    fpTetraDtet σ o R t *
        (o 0 1 * o 0 2 * o 0 3 * o 1 2 * o 1 3 * o 2 3) =
      fourPointTracePoly (o 0 1) (o 0 2) (o 0 3) (o 1 2) (o 1 3) (o 2 3)
        (R 0 1 2) (R 0 1 3) (R 0 2 3) (R 1 2 3) (t 0) (t 1) (t 2) := by
  let o' : Fin 4 → Fin 4 → ℝ := fun i j => o (σ i) (σ j)
  let R' : Fin 4 → Fin 4 → Fin 4 → ℝ := fun i j k => R (σ i) (σ j) (σ k)
  let t' : Fin 3 → ℝ := pairTraceSelector t σ
  have ho' : ∀ i j, o' i j = o' j i := fun i j => ho (σ i) (σ j)
  have hpos' : ∀ i j, i ≠ j → 0 < o' i j := fun i j hij => hpos (σ i) (σ j) (fun h => hij (σ.injective h))
  have hR12' : ∀ i j k, R' i j k = R' j i k := fun i j k => hR12 (σ i) (σ j) (σ k)
  have hR23' : ∀ i j k, R' i j k = R' i k j := fun i j k => hR23 (σ i) (σ j) (σ k)
  obtain ⟨hQ1, hQ2, hQ3⟩ := tetraQOfTraces_pairTraceSelector t σ
  have hD_eq : fpTetraDtet σ o R t = fpTetraDtet 1 o' R' t' := by
    unfold fpTetraDtet
    simp only [Equiv.Perm.one_apply]
    rw [hQ1, hQ2, hQ3]
  rw [hD_eq, ← overlap_prod_perm σ o ho]
  rw [prop_Dacal_poly_id o' ho' hpos' R' hR12' hR23' t']
  exact fourPointTracePoly_perm σ o ho R hR12 hR23 t

theorem fpTetraDtet_perm_invariant (σ : Equiv.Perm (Fin 4))
    (o : Fin 4 → Fin 4 → ℝ) (ho : ∀ i j, o i j = o j i)
    (hpos : ∀ i j, i ≠ j → 0 < o i j)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR12 : ∀ i j k, R i j k = R j i k) (hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ) :
    fpTetraDtet σ o R t = fpTetraDtet 1 o R t := by
  have h1 := prop_Dacal_poly σ o ho hpos R hR12 hR23 t
  have h2 := prop_Dacal_poly 1 o ho hpos R hR12 hR23 t
  have hprod : o 0 1 * o 0 2 * o 0 3 * o 1 2 * o 1 3 * o 2 3 ≠ 0 := by
    have h01 := (hpos 0 1 (by decide)).ne'
    have h02 := (hpos 0 2 (by decide)).ne'
    have h03 := (hpos 0 3 (by decide)).ne'
    have h12 := (hpos 1 2 (by decide)).ne'
    have h13 := (hpos 1 3 (by decide)).ne'
    have h23 := (hpos 2 3 (by decide)).ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h01 h02) h03) h12) h13) h23
  exact mul_right_cancel₀ hprod (h1.trans h2.symm)

theorem fpTetraDtet_atoms (σ : Equiv.Perm (Fin 4)) (p : Fin 4 → Albert)
    (hpos : ∀ i j, i ≠ j → 0 < fpOverlap p i j) :
    fpTetraDtet σ (fpOverlap p) (fpTriangle p) ![fpDoublePair1 p, fpDoublePair2 p, fpDoublePair3 p] *
        (fpOverlap p 0 1 * fpOverlap p 0 2 * fpOverlap p 0 3 *
          fpOverlap p 1 2 * fpOverlap p 1 3 * fpOverlap p 2 3) =
      fourPointInvariant p := by
  have h := prop_Dacal_poly σ (fpOverlap p) (fpOverlap_symm p) hpos
    (fpTriangle p) (fpTriangle_swap12 p) (fpTriangle_swap23 p)
    ![fpDoublePair1 p, fpDoublePair2 p, fpDoublePair3 p]
  refine h.trans ?_
  unfold fourPointTracePoly fourPointInvariant fpOmega1 fpOmega2 fpOmega3
  change fourPointOmegaPoly (fpOverlap p 0 1) (fpOverlap p 0 2) (fpOverlap p 0 3)
    (fpOverlap p 1 2) (fpOverlap p 1 3) (fpOverlap p 2 3)
    (fpTriangle p 0 1 2) (fpTriangle p 0 1 3) (fpTriangle p 0 2 3) (fpTriangle p 1 2 3)
    (fpDoublePair2 p + fpDoublePair3 p - fpDoublePair1 p)
    (fpDoublePair1 p + fpDoublePair3 p - fpDoublePair2 p)
    (fpDoublePair1 p + fpDoublePair2 p - fpDoublePair3 p) = _
  rfl

theorem tetrahedronDiscriminant_eq_overlap_mul_fourPointInvariant (p : Fin 4 → Albert) :
    tetrahedronDiscriminant (nativeOverlaps p) (nativeTriangles p) (nativeCornerQ p) =
      fpOverlap p 0 1 * fpOverlap p 0 2 * fpOverlap p 0 3 * fourPointInvariant p := by
  have hQ := nativeCornerQ_eq_fpOmega p
  have ho20 : nativeOverlaps p 2 0 = fpOverlap p 0 2 := fpOverlap_symm p 2 0
  have ho30 : nativeOverlaps p 3 0 = fpOverlap p 0 3 := fpOverlap_symm p 3 0
  have ho31 : nativeOverlaps p 3 1 = fpOverlap p 1 3 := fpOverlap_symm p 3 1
  have ho10 : nativeOverlaps p 1 0 = fpOverlap p 0 1 := fpOverlap_symm p 1 0
  have hR031 : nativeTriangles p 0 3 1 = fpTriangle p 0 1 3 := by
    rw [← fpTriangle_eq_nativeTriangles, fpTriangle_swap23]
  have hR012 : nativeTriangles p 0 1 2 = fpTriangle p 0 1 2 := (fpTriangle_eq_nativeTriangles p 0 1 2).symm
  have hR023 : nativeTriangles p 0 2 3 = fpTriangle p 0 2 3 := (fpTriangle_eq_nativeTriangles p 0 2 3).symm
  have hR123 : nativeTriangles p 1 2 3 = fpTriangle p 1 2 3 := (fpTriangle_eq_nativeTriangles p 1 2 3).symm
  unfold tetrahedronDiscriminant
  rw [hQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [ho20, ho30, ho31, ho10, hR031, hR012, hR023, hR123]
  change _ = fpOverlap p 0 1 * fpOverlap p 0 2 * fpOverlap p 0 3 *
    fourPointOmegaPoly (nativeOverlaps p 0 1) (nativeOverlaps p 0 2) (nativeOverlaps p 0 3)
      (nativeOverlaps p 1 2) (nativeOverlaps p 1 3) (nativeOverlaps p 2 3)
      (fpTriangle p 0 1 2) (fpTriangle p 0 1 3) (fpTriangle p 0 2 3) (fpTriangle p 1 2 3)
      (fpOmega1 p) (fpOmega2 p) (fpOmega3 p)
  unfold fourPointOmegaPoly nativeOverlaps fpOverlap
  ring

/-! ## Section 5: Triangular Local Inverse and Principal Ideal (`rem:fp:tracerel-rank(a)`) -/

def fourPointTraceVec (p : Fin 4 → Albert) : Fin 13 → ℝ :=
  ![fpOverlap p 0 1, fpOverlap p 0 2, fpOverlap p 0 3,
    fpOverlap p 1 2, fpOverlap p 1 3, fpOverlap p 2 3,
    fpTriangle p 0 1 2, fpTriangle p 0 1 3, fpTriangle p 0 2 3,
    fpDoublePair1 p, fpDoublePair2 p, fpDoublePair3 p,
    fpTriangle p 1 2 3]

def traceRelationMvPoly : MvPolynomial (Fin 13) ℝ :=
  MvPolynomial.X 12 -
    (MvPolynomial.X 9 + MvPolynomial.X 10 + MvPolynomial.X 11
      - MvPolynomial.C (1 / 2)
      + MvPolynomial.C (1 / 2) *
          (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 +
           MvPolynomial.X 3 + MvPolynomial.X 4 + MvPolynomial.X 5)
      - MvPolynomial.C (1 / 2) *
          (MvPolynomial.X 0 * MvPolynomial.X 5 +
           MvPolynomial.X 1 * MvPolynomial.X 4 +
           MvPolynomial.X 2 * MvPolynomial.X 3)
      - MvPolynomial.X 6 - MvPolynomial.X 7 - MvPolynomial.X 8)

theorem traceRelationMvPoly_eval_eq_zero (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    MvPolynomial.eval (fourPointTraceVec p) traceRelationMvPoly = 0 := by
  have hrel := albert_fourAtom_trace_relation p hp
  simp only [traceRelationMvPoly, map_sub, map_add, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_C]
  change fpTriangle p 1 2 3 -
      (fpDoublePair1 p + fpDoublePair2 p + fpDoublePair3 p - 1 / 2 +
        1 / 2 * (fpOverlap p 0 1 + fpOverlap p 0 2 + fpOverlap p 0 3 +
          fpOverlap p 1 2 + fpOverlap p 1 3 + fpOverlap p 2 3) -
        1 / 2 * (fpOverlap p 0 1 * fpOverlap p 2 3 + fpOverlap p 0 2 * fpOverlap p 1 3 +
          fpOverlap p 0 3 * fpOverlap p 1 2) -
        fpTriangle p 0 1 2 - fpTriangle p 0 1 3 - fpTriangle p 0 2 3) = 0
  linarith [hrel]

def tToOmega (τ : Fin 12 → ℝ) : Fin 12 → ℝ :=
  fun i =>
    if i = 9 then τ 10 + τ 11 - τ 9
    else if i = 10 then τ 9 + τ 11 - τ 10
    else if i = 11 then τ 9 + τ 10 - τ 11
    else τ i

def omegaToT (τ : Fin 12 → ℝ) : Fin 12 → ℝ :=
  fun i =>
    if i = 9 then (τ 10 + τ 11) / 2
    else if i = 10 then (τ 9 + τ 11) / 2
    else if i = 11 then (τ 9 + τ 10) / 2
    else τ i

private theorem continuous_tToOmega : Continuous tToOmega := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [tToOmega] <;> fun_prop

private theorem omegaToT_tToOmega (τ : Fin 12 → ℝ) : omegaToT (tToOmega τ) = τ := by
  funext i
  fin_cases i <;> simp [omegaToT, tToOmega] <;> ring

def invA (τ : Fin 12 → ℝ) : ℝ := Real.sqrt (τ 0)
def invB (τ : Fin 12 → ℝ) : ℝ := Real.sqrt (1 - (invA τ) ^ 2)
def invC (τ : Fin 12 → ℝ) : ℝ := Real.sqrt (τ 1)
def invC1 (τ : Fin 12 → ℝ) : ℝ := (τ 6 / (invA τ * invC τ) - invA τ * invC τ) / invB τ
def invRadC2 (τ : Fin 12 → ℝ) : ℝ := τ 3 - (invA τ * invC τ + invB τ * invC1 τ) ^ 2
def invC2 (τ : Fin 12 → ℝ) : ℝ := Real.sqrt (invRadC2 τ) / invB τ
def invRadH (τ : Fin 12 → ℝ) : ℝ := 1 - (invC τ) ^ 2 - (invC1 τ) ^ 2 - (invC2 τ) ^ 2
def invH (τ : Fin 12 → ℝ) : ℝ := Real.sqrt (invRadH τ)
def invD (τ : Fin 12 → ℝ) : ℝ := Real.sqrt (τ 2)
def invX0 (τ : Fin 12 → ℝ) : ℝ := (τ 7 / (invA τ * invD τ) - invA τ * invD τ) / invB τ
def invXsq (τ : Fin 12 → ℝ) : ℝ :=
  (τ 4 - (invA τ * invD τ) ^ 2 - 2 * invA τ * invD τ * invB τ * invX0 τ) / (invB τ) ^ 2
def invU (τ : Fin 12 → ℝ) : ℝ := invA τ * invC τ + invB τ * invC1 τ
def invV (τ : Fin 12 → ℝ) : ℝ := invB τ * invC2 τ
def invQ0 (τ : Fin 12 → ℝ) : ℝ := invA τ * invD τ + invB τ * invX0 τ
def invX1 (τ : Fin 12 → ℝ) : ℝ :=
  (τ 9 / (invC τ * invD τ) - invU τ * invQ0 τ) / (invV τ * invB τ)
def invRadX2 (τ : Fin 12 → ℝ) : ℝ := invXsq τ - (invX0 τ) ^ 2 - (invX1 τ) ^ 2
def invX2 (τ : Fin 12 → ℝ) : ℝ := Real.sqrt (invRadX2 τ)
def invM (τ : Fin 12 → ℝ) : ℝ := τ 8 / (invC τ * invD τ)
def invN (τ : Fin 12 → ℝ) : ℝ := (invU τ * invM τ - τ 10 / (invA τ * invD τ)) / invV τ
def invP (τ : Fin 12 → ℝ) : ℝ :=
  (τ 11 / (invA τ * invC τ) - invQ0 τ * invM τ - invB τ * invX1 τ * invN τ) / (invB τ * invX2 τ)
def invK0 (τ : Fin 12 → ℝ) : ℝ := invC τ * invD τ + invC1 τ * invX0 τ + invC2 τ * invX1 τ
def invK1 (τ : Fin 12 → ℝ) : ℝ := invC1 τ * invX1 τ - invC2 τ * invX0 τ
def invK2 (τ : Fin 12 → ℝ) : ℝ := invC1 τ * invX2 τ
def invK3 (τ : Fin 12 → ℝ) : ℝ := -(invC2 τ * invX2 τ)
def invY0 (τ : Fin 12 → ℝ) : ℝ := (invM τ - invK0 τ) / invH τ
def invY1 (τ : Fin 12 → ℝ) : ℝ := (invN τ - invK1 τ) / invH τ
def invY2 (τ : Fin 12 → ℝ) : ℝ := (invP τ - invK2 τ) / invH τ
def invYsq (τ : Fin 12 → ℝ) : ℝ := 1 - (invD τ) ^ 2 - invXsq τ
def invY3 (τ : Fin 12 → ℝ) : ℝ :=
  ((invK0 τ) ^ 2 + (invK1 τ) ^ 2 + (invK2 τ) ^ 2 + (invK3 τ) ^ 2 +
    (invH τ) ^ 2 * invYsq τ +
    2 * invH τ * (invK0 τ * invY0 τ + invK1 τ * invY1 τ + invK2 τ * invY2 τ) - τ 5) /
    (2 * invH τ * invC2 τ * invX2 τ)
def invRadY4 (τ : Fin 12 → ℝ) : ℝ :=
  invYsq τ - (invY0 τ) ^ 2 - (invY1 τ) ^ 2 - (invY2 τ) ^ 2 - (invY3 τ) ^ 2
def invY4 (τ : Fin 12 → ℝ) : ℝ := Real.sqrt (invRadY4 τ)

def triangularLocalInverse (τ : Fin 12 → ℝ) : Fin 4 → Albert :=
  let τw := tToOmega τ
  let Y := octonionScalar (invY0 τw) + invY1 τw • octI + invY2 τw • octJ +
    invY3 τw • octK + invY4 τw • octL
  sparseFourConfig (invA τw) (invB τw) (invC τw) (invC1 τw) (invC2 τw) (invH τw)
    (invD τw) (invX0 τw) (invX1 τw) (invX2 τw) Y

private theorem octNormSq_Y_coords (y0 y1 y2 y3 y4 : ℝ) :
    octNormSq (octonionScalar y0 + y1 • octI + y2 • octJ + y3 • octK + y4 • octL) =
      y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2 := by
  rw [octNormSq_eq_coords]
  simp only [oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd,
    QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add,
    QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add,
    QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
    QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]
  simp only [octonionScalar, octI, octJ, octK, octL,
    QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero,
    QuaternionAlgebra.imJ_zero, QuaternionAlgebra.imK_zero]
  ring

private theorem octNormSq_X_coords (x0 x1 x2 : ℝ) :
    octNormSq (octonionScalar x0 + x1 • octI + x2 • octJ) =
      x0 ^ 2 + x1 ^ 2 + x2 ^ 2 := by
  have h := octNormSq_Y_coords x0 x1 x2 0 0
  simpa using h

private theorem octNormSq_z_coords (C1 C2 : ℝ) :
    octNormSq (octonionScalar C1 + C2 • octI) = C1 ^ 2 + C2 ^ 2 := by
  have h := octNormSq_Y_coords C1 C2 0 0 0
  simpa using h

private theorem oct_g3_eq (C D C1 C2 H x0 x1 x2 y0 y1 y2 y3 y4 : ℝ) :
    octonionScalar (C * D) +
      octonionMul (octonionConj (octonionScalar C1 + C2 • octI))
        (octonionScalar x0 + x1 • octI + x2 • octJ) +
      H • (octonionScalar y0 + y1 • octI + y2 • octJ + y3 • octK + y4 • octL) =
    octonionScalar (C * D + C1 * x0 + C2 * x1 + H * y0) +
      (C1 * x1 - C2 * x0 + H * y1) • octI +
      (C1 * x2 + H * y2) • octJ +
      (-(C2 * x2) + H * y3) • octK +
      (H * y4) • octL := by
  apply oct_ext <;>
    simp only [oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd,
      oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd,
      QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add,
      QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add,
      QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
      QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul,
      QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub,
      QuaternionAlgebra.imJ_sub, QuaternionAlgebra.imK_sub,
      QuaternionAlgebra.re_neg, QuaternionAlgebra.imI_neg,
      QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg,
      QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
      QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star,
      QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, smul_eq_mul] <;>
    simp only [octonionScalar, octI, octJ, octK, octL,
      QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero,
      QuaternionAlgebra.imJ_zero, QuaternionAlgebra.imK_zero] <;>
    ring

private theorem octonionReal_mul_5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ) :
    octonionReal (octonionMul
      (octonionScalar a0 + a1 • octI + a2 • octJ + a3 • octK + a4 • octL)
      (octonionScalar b0 + b1 • octI + b2 • octJ + b3 • octK + b4 • octL)) =
      a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3 - a4 * b4 := by
  simp only [octonionReal, oct_mul_fst, oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd,
    QuaternionAlgebra.re_sub, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star,
    QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add,
    QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul,
    smul_eq_mul]
  simp only [octonionScalar, octI, octJ, octK, octL,
    QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero,
    QuaternionAlgebra.imJ_zero, QuaternionAlgebra.imK_zero]
  ring

private theorem octonionReal_mul_conj_5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ) :
    octonionReal (octonionMul
      (octonionScalar a0 + a1 • octI + a2 • octJ + a3 • octK + a4 • octL)
      (octonionConj (octonionScalar b0 + b1 • octI + b2 • octJ + b3 • octK + b4 • octL))) =
      a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4 := by
  simp only [octonionReal, oct_mul_fst, oct_conj_fst, oct_conj_snd,
    oct_add_fst, oct_add_snd, oct_smul_fst, oct_smul_snd,
    QuaternionAlgebra.re_sub, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star,
    QuaternionAlgebra.re_neg, QuaternionAlgebra.imI_neg, QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg,
    QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add,
    QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul,
    smul_eq_mul]
  simp only [octonionScalar, octI, octJ, octK, octL,
    QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero,
    QuaternionAlgebra.imJ_zero, QuaternionAlgebra.imK_zero]
  ring

private theorem oct_g1_expand (a b c1 c2 : ℝ) :
    octonionScalar a + b • (octonionScalar c1 + c2 • octI) =
      octonionScalar (a + b * c1) + (b * c2) • octI + (0 : ℝ) • octJ + (0 : ℝ) • octK + (0 : ℝ) • octL := by
  conv_lhs => rw [smul_add, smul_smul, ← octonionScalar_smul, ← add_assoc, ← octonionScalar_add]
  conv_rhs => simp only [zero_smul, add_zero]

private theorem oct_g2_expand (a b x0 x1 x2 : ℝ) :
    octonionScalar a + b • (octonionScalar x0 + x1 • octI + x2 • octJ) =
      octonionScalar (a + b * x0) + (b * x1) • octI + (b * x2) • octJ + (0 : ℝ) • octK + (0 : ℝ) • octL := by
  conv_lhs =>
    rw [smul_add, smul_add, smul_smul, smul_smul, ← octonionScalar_smul,
      ← add_assoc, ← add_assoc, ← octonionScalar_add]
  conv_rhs => simp only [zero_smul, add_zero]

private theorem triangularLocalInverse_open_nbhd_at (τ0 τS : Fin 12 → ℝ)
    (hτS_def : τS = tToOmega τ0)
    (h0 : τS 0 = 1 / 2) (h1 : τS 1 = 1 / 3) (h2 : τS 2 = 1 / 3)
    (h3 : τS 3 = 1 / 3) (h4 : τS 4 = 1 / 3) (h5 : τS 5 = 1 / 3)
    (h6 : τS 6 = 1 / 6) (h7 : τS 7 = 1 / 6) (h8 : τS 8 = 1 / 9)
    (h9 : τS 9 = 1 / 18) (h10 : τS 10 = 1 / 18) (h11 : τS 11 = 1 / 18) :
    ∃ U : Set (Fin 12 → ℝ), IsOpen U ∧
      τ0 ∈ U ∧
      ∀ τ ∈ U,
        (∀ i, IsAtom (triangularLocalInverse τ i)) ∧
        Fin.init (fourPointTraceVec (triangularLocalInverse τ)) = τ := by
  have haS : invA τS = 1 / Real.sqrt 2 := by simp [invA, h0]
  have haS_pos : 0 < invA τS := by rw [haS]; positivity
  have haS2 : (invA τS) ^ 2 = 1 / 2 := by simp [invA, h0]
  have hrad2S : 1 - (invA τS) ^ 2 = 1 / 2 := by rw [haS2]; norm_num
  have hbS : invB τS = 1 / Real.sqrt 2 := by simp [invB, hrad2S]
  have hbS_pos : 0 < invB τS := by rw [hbS]; positivity
  have hbS2 : (invB τS) ^ 2 = 1 / 2 := by simp [invB, hrad2S]
  have hcS : invC τS = 1 / Real.sqrt 3 := by simp [invC, h1]
  have hcS_pos : 0 < invC τS := by rw [hcS]; positivity
  have hcS2 : (invC τS) ^ 2 = 1 / 3 := by simp [invC, h1]
  have hdS : invD τS = 1 / Real.sqrt 3 := by simp [invD, h2]
  have hdS_pos : 0 < invD τS := by rw [hdS]; positivity
  have hdS2 : (invD τS) ^ 2 = 1 / 3 := by simp [invD, h2]
  have hC1S : invC1 τS = 0 := by
    unfold invC1
    have hac : (invA τS * invC τS) ^ 2 = 1 / 6 := by
      rw [mul_pow, haS2, hcS2]; norm_num
    have hnum : τS 6 / (invA τS * invC τS) - invA τS * invC τS = 0 := by
      rw [h6]; field_simp [haS_pos.ne', hcS_pos.ne']; linarith [hac]
    rw [hnum, zero_div]
  have hradC2S : invRadC2 τS = 1 / 6 := by
    unfold invRadC2
    rw [h3, hC1S, mul_zero, add_zero, mul_pow, haS2, hcS2]
    norm_num
  have hC2S : invC2 τS = 1 / Real.sqrt 3 := by
    unfold invC2
    rw [hradC2S, hbS, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    have h6_eq : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    rw [h6_eq]
    field_simp
  have hC2S_pos : 0 < invC2 τS := by rw [hC2S]; positivity
  have hC2S2 : (invC2 τS) ^ 2 = 1 / 3 := by
    rw [hC2S, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hradHS : invRadH τS = 1 / 3 := by
    unfold invRadH
    rw [hcS2, hC1S, hC2S2]; norm_num
  have hHS_pos : 0 < invH τS := by simp [invH, hradHS]
  have hHS2 : (invH τS) ^ 2 = 1 / 3 := by simp [invH, hradHS]
  have hx0S : invX0 τS = 0 := by
    unfold invX0
    have had : (invA τS * invD τS) ^ 2 = 1 / 6 := by
      rw [mul_pow, haS2, hdS2]; norm_num
    have hnum : τS 7 / (invA τS * invD τS) - invA τS * invD τS = 0 := by
      rw [h7]; field_simp [haS_pos.ne', hdS_pos.ne']; linarith [had]
    rw [hnum, zero_div]
  have hXsqS : invXsq τS = 1 / 3 := by
    unfold invXsq
    rw [h4, hx0S, mul_zero, sub_zero, hbS2, mul_pow, haS2, hdS2]
    norm_num
  have hx1S : invX1 τS = 0 := by
    unfold invX1 invU invQ0
    rw [h9, hC1S, hx0S]
    simp only [mul_zero, add_zero]
    have hcd : invC τS * invD τS = 1 / 3 := by rw [hcS, hdS]; field_simp; norm_num
    have ha2 : invA τS * invA τS = 1 / 2 := by simpa [sq] using haS2
    rw [hcd]
    have hnum : (1 / 18 : ℝ) / (1 / 3) - (invA τS * invC τS) * (invA τS * invD τS) = 0 := by
      have : (invA τS * invC τS) * (invA τS * invD τS) =
          (invA τS * invA τS) * (invC τS * invD τS) := by ring
      rw [this, ha2, hcd]; norm_num
    rw [hnum, zero_div]
  have hradX2S : invRadX2 τS = 1 / 3 := by
    unfold invRadX2
    rw [hXsqS, hx0S, hx1S]; norm_num
  have hx2S_pos : 0 < invX2 τS := by simp [invX2, hradX2S]
  have hx2S2 : (invX2 τS) ^ 2 = 1 / 3 := by simp [invX2, hradX2S]
  have hmS : invM τS = 1 / 3 := by
    unfold invM
    have hcd : invC τS * invD τS = 1 / 3 := by rw [hcS, hdS]; field_simp; norm_num
    rw [h8, hcd]; norm_num
  have hnS : invN τS = 0 := by
    unfold invN invU
    rw [h10, hmS, hC1S, mul_zero, add_zero]
    have had : invA τS * invD τS = 1 / Real.sqrt 6 := by
      rw [haS, hdS, div_mul_div_comm, one_mul, ← Real.sqrt_mul (by norm_num)]; norm_num
    have h6_eq : (invA τS * invC τS) * (1 / 3) - (1 / 18) / (invA τS * invD τS) = 0 := by
      have hac : invA τS * invC τS = 1 / Real.sqrt 6 := by
        rw [haS, hcS, div_mul_div_comm, one_mul, ← Real.sqrt_mul (by norm_num)]; norm_num
      rw [hac, had]; field_simp; norm_num
    rw [h6_eq, zero_div]
  have hpS : invP τS = 0 := by
    unfold invP invQ0
    rw [h11, hmS, hx0S, hx1S, hnS, mul_zero, mul_zero, sub_zero]
    have hac : invA τS * invC τS = 1 / Real.sqrt 6 := by
      rw [haS, hcS, div_mul_div_comm, one_mul, ← Real.sqrt_mul (by norm_num)]; norm_num
    have had : invA τS * invD τS = 1 / Real.sqrt 6 := by
      rw [haS, hdS, div_mul_div_comm, one_mul, ← Real.sqrt_mul (by norm_num)]; norm_num
    rw [hac, had, add_zero]
    have hnum : (1 / 18 : ℝ) / (1 / Real.sqrt 6) - (1 / Real.sqrt 6) * (1 / 3) = 0 := by
      field_simp; norm_num
    rw [hnum, zero_div]
  have hK0S : invK0 τS = 1 / 3 := by
    unfold invK0
    have hcd : invC τS * invD τS = 1 / 3 := by rw [hcS, hdS]; field_simp; norm_num
    rw [hcd, hC1S, hx0S, hx1S]; ring
  have hK1S : invK1 τS = 0 := by simp [invK1, hC1S, hx0S, hx1S]
  have hK2S : invK2 τS = 0 := by simp [invK2, hC1S]
  have hK3S : invK3 τS = -(1 / 3) := by
    unfold invK3
    have hc2x2 : invC2 τS * invX2 τS = 1 / 3 := by
      have hsq : (invC2 τS * invX2 τS - 1 / 3) * (invC2 τS * invX2 τS + 1 / 3) = 0 := by
        have h1' : (invC2 τS * invX2 τS) ^ 2 = 1 / 9 := by
          rw [mul_pow, hC2S2, hx2S2]; norm_num
        linarith [show (invC2 τS * invX2 τS - 1 / 3) * (invC2 τS * invX2 τS + 1 / 3) =
          (invC2 τS * invX2 τS) ^ 2 - 1 / 9 by ring]
      have hpos : 0 < invC2 τS * invX2 τS + 1 / 3 := by
        linarith [mul_pos hC2S_pos hx2S_pos]
      rcases mul_eq_zero.mp hsq with h | h
      · linarith
      · linarith
    rw [hc2x2]
  have hy0S : invY0 τS = 0 := by simp [invY0, hmS, hK0S]
  have hy1S : invY1 τS = 0 := by simp [invY1, hnS, hK1S]
  have hy2S : invY2 τS = 0 := by simp [invY2, hpS, hK2S]
  have hYsqS : invYsq τS = 1 / 3 := by
    unfold invYsq; rw [hdS2, hXsqS]; norm_num
  have hy3S : invY3 τS = 0 := by
    unfold invY3
    rw [hK0S, hK1S, hK2S, hK3S, hHS2, hYsqS, hy0S, hy1S, hy2S, h5]
    norm_num
  have hradY4S : invRadY4 τS = 1 / 3 := by
    unfold invRadY4
    rw [hYsqS, hy0S, hy1S, hy2S, hy3S]; norm_num
  have hc_a : ContinuousAt invA τS := (continuous_apply 0).continuousAt.sqrt
  have hc_rad2 : ContinuousAt (fun τ => 1 - (invA τ) ^ 2) τS :=
    continuousAt_const.sub (hc_a.pow 2)
  have hc_b : ContinuousAt invB τS := hc_rad2.sqrt
  have hc_c : ContinuousAt invC τS := (continuous_apply 1).continuousAt.sqrt
  have hc_d : ContinuousAt invD τS := (continuous_apply 2).continuousAt.sqrt
  have hc_C1 : ContinuousAt invC1 τS :=
    (((continuous_apply 6).continuousAt.div (hc_a.mul hc_c)
      (mul_ne_zero haS_pos.ne' hcS_pos.ne')).sub (hc_a.mul hc_c)).div hc_b hbS_pos.ne'
  have hc_radC2 : ContinuousAt invRadC2 τS :=
    (continuous_apply 3).continuousAt.sub (((hc_a.mul hc_c).add (hc_b.mul hc_C1)).pow 2)
  have hc_C2 : ContinuousAt invC2 τS := hc_radC2.sqrt.div hc_b hbS_pos.ne'
  have hc_radH : ContinuousAt invRadH τS :=
    ((continuousAt_const.sub (hc_c.pow 2)).sub (hc_C1.pow 2)).sub (hc_C2.pow 2)
  have hc_H : ContinuousAt invH τS := hc_radH.sqrt
  have hc_x0 : ContinuousAt invX0 τS :=
    (((continuous_apply 7).continuousAt.div (hc_a.mul hc_d)
      (mul_ne_zero haS_pos.ne' hdS_pos.ne')).sub (hc_a.mul hc_d)).div hc_b hbS_pos.ne'
  have hc_Xsq : ContinuousAt invXsq τS :=
    (((continuous_apply 4).continuousAt.sub ((hc_a.mul hc_d).pow 2)).sub
      ((((continuousAt_const.mul hc_a).mul hc_d).mul hc_b).mul hc_x0)).div
      (hc_b.pow 2) (pow_ne_zero 2 hbS_pos.ne')
  have hc_U : ContinuousAt invU τS := (hc_a.mul hc_c).add (hc_b.mul hc_C1)
  have hc_V : ContinuousAt invV τS := hc_b.mul hc_C2
  have hc_Q0 : ContinuousAt invQ0 τS := (hc_a.mul hc_d).add (hc_b.mul hc_x0)
  have hc_x1 : ContinuousAt invX1 τS :=
    (((continuous_apply 9).continuousAt.div (hc_c.mul hc_d)
      (mul_ne_zero hcS_pos.ne' hdS_pos.ne')).sub (hc_U.mul hc_Q0)).div
      (hc_V.mul hc_b) (mul_ne_zero (mul_ne_zero hbS_pos.ne' hC2S_pos.ne') hbS_pos.ne')
  have hc_radX2 : ContinuousAt invRadX2 τS :=
    (hc_Xsq.sub (hc_x0.pow 2)).sub (hc_x1.pow 2)
  have hc_x2 : ContinuousAt invX2 τS := hc_radX2.sqrt
  have hc_M : ContinuousAt invM τS :=
    (continuous_apply 8).continuousAt.div (hc_c.mul hc_d) (mul_ne_zero hcS_pos.ne' hdS_pos.ne')
  have hc_N : ContinuousAt invN τS :=
    ((hc_U.mul hc_M).sub ((continuous_apply 10).continuousAt.div (hc_a.mul hc_d)
      (mul_ne_zero haS_pos.ne' hdS_pos.ne'))).div hc_V (mul_ne_zero hbS_pos.ne' hC2S_pos.ne')
  have hc_P : ContinuousAt invP τS :=
    ((((continuous_apply 11).continuousAt.div (hc_a.mul hc_c)
      (mul_ne_zero haS_pos.ne' hcS_pos.ne')).sub (hc_Q0.mul hc_M)).sub
      ((hc_b.mul hc_x1).mul hc_N)).div (hc_b.mul hc_x2) (mul_ne_zero hbS_pos.ne' hx2S_pos.ne')
  have hc_K0 : ContinuousAt invK0 τS :=
    ((hc_c.mul hc_d).add (hc_C1.mul hc_x0)).add (hc_C2.mul hc_x1)
  have hc_K1 : ContinuousAt invK1 τS := (hc_C1.mul hc_x1).sub (hc_C2.mul hc_x0)
  have hc_K2 : ContinuousAt invK2 τS := hc_C1.mul hc_x2
  have hc_K3 : ContinuousAt invK3 τS := (hc_C2.mul hc_x2).neg
  have hc_y0 : ContinuousAt invY0 τS := (hc_M.sub hc_K0).div hc_H hHS_pos.ne'
  have hc_y1 : ContinuousAt invY1 τS := (hc_N.sub hc_K1).div hc_H hHS_pos.ne'
  have hc_y2 : ContinuousAt invY2 τS := (hc_P.sub hc_K2).div hc_H hHS_pos.ne'
  have hc_Ysq : ContinuousAt invYsq τS := (continuousAt_const.sub (hc_d.pow 2)).sub hc_Xsq
  have hc_y3 : ContinuousAt invY3 τS :=
    (((((((hc_K0.pow 2).add (hc_K1.pow 2)).add (hc_K2.pow 2)).add (hc_K3.pow 2)).add
      ((hc_H.pow 2).mul hc_Ysq)).add
      ((continuousAt_const.mul hc_H).mul
        (((hc_K0.mul hc_y0).add (hc_K1.mul hc_y1)).add (hc_K2.mul hc_y2)))).sub
      (continuous_apply 5).continuousAt).div
      (((continuousAt_const.mul hc_H).mul hc_C2).mul hc_x2)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hHS_pos.ne') hC2S_pos.ne') hx2S_pos.ne')
  have hc_radY4 : ContinuousAt invRadY4 τS :=
    (((hc_Ysq.sub (hc_y0.pow 2)).sub (hc_y1.pow 2)).sub (hc_y2.pow 2)).sub (hc_y3.pow 2)
  have hev : ∀ᶠ τ in nhds τS,
      0 < τ 0 ∧ 0 < 1 - (invA τ) ^ 2 ∧ 0 < τ 1 ∧ 0 < invRadC2 τ ∧
      0 < invRadH τ ∧ 0 < τ 2 ∧ 0 < invRadX2 τ ∧ 0 < invRadY4 τ := by
    have p0 : ∀ᶠ τ in nhds τS, 0 < τ 0 :=
      (continuous_apply 0).continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by rw [h0]; norm_num))
    have p1 : ∀ᶠ τ in nhds τS, 0 < 1 - (invA τ) ^ 2 :=
      hc_rad2.preimage_mem_nhds (Ioi_mem_nhds (by rw [hrad2S]; norm_num))
    have p2 : ∀ᶠ τ in nhds τS, 0 < τ 1 :=
      (continuous_apply 1).continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by rw [h1]; norm_num))
    have p3 : ∀ᶠ τ in nhds τS, 0 < invRadC2 τ :=
      hc_radC2.preimage_mem_nhds (Ioi_mem_nhds (by rw [hradC2S]; norm_num))
    have p4 : ∀ᶠ τ in nhds τS, 0 < invRadH τ :=
      hc_radH.preimage_mem_nhds (Ioi_mem_nhds (by rw [hradHS]; norm_num))
    have p5 : ∀ᶠ τ in nhds τS, 0 < τ 2 :=
      (continuous_apply 2).continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by rw [h2]; norm_num))
    have p6 : ∀ᶠ τ in nhds τS, 0 < invRadX2 τ :=
      hc_radX2.preimage_mem_nhds (Ioi_mem_nhds (by rw [hradX2S]; norm_num))
    have p7 : ∀ᶠ τ in nhds τS, 0 < invRadY4 τ :=
      hc_radY4.preimage_mem_nhds (Ioi_mem_nhds (by rw [hradY4S]; norm_num))
    exact p0.and (p1.and (p2.and (p3.and (p4.and (p5.and (p6.and p7))))))
  obtain ⟨Uw, hUw_sub, hUw_open, hτS_Uw⟩ := mem_nhds_iff.mp hev
  have hτ0_pre : τ0 ∈ tToOmega ⁻¹' Uw := by
    change tToOmega τ0 ∈ Uw
    rw [← hτS_def]
    exact hτS_Uw
  refine ⟨tToOmega ⁻¹' Uw, hUw_open.preimage continuous_tToOmega, hτ0_pre, ?_⟩
  intro τ hτ
  have hpos8 := hUw_sub hτ
  rcases hpos8 with ⟨ht0, hrad2, ht1, hradC2, hradH, ht2, hradX2, hradY4⟩
  let τw := tToOmega τ
  change 0 < τw 0 at ht0
  change 0 < 1 - (invA τw) ^ 2 at hrad2
  change 0 < τw 1 at ht1
  change 0 < invRadC2 τw at hradC2
  change 0 < invRadH τw at hradH
  change 0 < τw 2 at ht2
  change 0 < invRadX2 τw at hradX2
  change 0 < invRadY4 τw at hradY4
  have ha_pos : 0 < invA τw := Real.sqrt_pos.mpr ht0
  have hb_pos : 0 < invB τw := Real.sqrt_pos.mpr hrad2
  have hc_pos : 0 < invC τw := Real.sqrt_pos.mpr ht1
  have hC2_pos : 0 < invC2 τw := div_pos (Real.sqrt_pos.mpr hradC2) hb_pos
  have hH_pos : 0 < invH τw := Real.sqrt_pos.mpr hradH
  have hd_pos : 0 < invD τw := Real.sqrt_pos.mpr ht2
  have hx2_pos : 0 < invX2 τw := Real.sqrt_pos.mpr hradX2
  have hy4_pos : 0 < invY4 τw := Real.sqrt_pos.mpr hradY4
  have ha2 : (invA τw) ^ 2 = τw 0 := Real.sq_sqrt ht0.le
  have hb2 : (invB τw) ^ 2 = 1 - (invA τw) ^ 2 := Real.sq_sqrt hrad2.le
  have hc2 : (invC τw) ^ 2 = τw 1 := Real.sq_sqrt ht1.le
  have hd2 : (invD τw) ^ 2 = τw 2 := Real.sq_sqrt ht2.le
  have hC2_2 : (invB τw * invC2 τw) ^ 2 = invRadC2 τw := by
    unfold invC2
    rw [mul_div_cancel₀ _ hb_pos.ne', Real.sq_sqrt hradC2.le]
  have hH2 : (invH τw) ^ 2 = invRadH τw := Real.sq_sqrt hradH.le
  have hx2_2 : (invX2 τw) ^ 2 = invRadX2 τw := Real.sq_sqrt hradX2.le
  have hy4_2 : (invY4 τw) ^ 2 = invRadY4 τw := Real.sq_sqrt hradY4.le
  let Y := octonionScalar (invY0 τw) + invY1 τw • octI + invY2 τw • octJ +
    invY3 τw • octK + invY4 τw • octL
  let X := octonionScalar (invX0 τw) + invX1 τw • octI + invX2 τw • octJ
  let p := triangularLocalInverse τ
  have hp_eq : p = sparseFourConfigOct (invA τw) (invB τw) (invC τw) (invC1 τw) (invC2 τw)
      (invH τw) (invD τw) X Y := rfl
  have hy0_eq : invC τw * invD τw + invC1 τw * invX0 τw + invC2 τw * invX1 τw +
      invH τw * invY0 τw = invM τw := by
    change invK0 τw + invH τw * invY0 τw = invM τw
    unfold invY0; field_simp [hH_pos.ne']; ring
  have hy1_eq : invC1 τw * invX1 τw - invC2 τw * invX0 τw +
      invH τw * invY1 τw = invN τw := by
    change invK1 τw + invH τw * invY1 τw = invN τw
    unfold invY1; field_simp [hH_pos.ne']; ring
  have hy2_eq : invC1 τw * invX2 τw + invH τw * invY2 τw = invP τw := by
    change invK2 τw + invH τw * invY2 τw = invP τw
    unfold invY2; field_simp [hH_pos.ne']; ring
  have hg3_eq : octonionScalar (invC τw * invD τw) +
      octonionMul (octonionConj (octonionScalar (invC1 τw) + invC2 τw • octI)) X +
      invH τw • Y =
      octonionScalar (invM τw) + invN τw • octI + invP τw • octJ +
      (invK3 τw + invH τw * invY3 τw) • octK + (invH τw * invY4 τw) • octL := by
    dsimp only [X, Y]
    rw [oct_g3_eq, hy0_eq, hy1_eq, hy2_eq]
    rfl
  constructor
  · intro i
    fin_cases i
    · change IsAtom (p 0); rw [hp_eq]
      exact octDyad_real0_isAtom 1 0 0 (by simp [octNormSq_zero])
    · change IsAtom (p 1); rw [hp_eq]
      exact octDyad_real0_isAtom (invA τw) (octonionScalar (invB τw)) 0 (by
        rw [octNormSq_scalar, octNormSq_zero]; linarith [hb2])
    · change IsAtom (p 2); rw [hp_eq]
      refine octDyad_real0_isAtom (invC τw) (octonionScalar (invC1 τw) + invC2 τw • octI)
        (octonionScalar (invH τw)) ?_
      rw [octNormSq_z_coords, octNormSq_scalar]
      have : (invH τw) ^ 2 = 1 - (invC τw) ^ 2 - (invC1 τw) ^ 2 - (invC2 τw) ^ 2 := hH2
      linarith [this]
    · change IsAtom (p 3); rw [hp_eq]
      refine octDyad_real0_isAtom (invD τw) X Y ?_
      rw [octNormSq_X_coords, octNormSq_Y_coords]
      have h1' : (invX2 τw) ^ 2 = invXsq τw - (invX0 τw) ^ 2 - (invX1 τw) ^ 2 := hx2_2
      have h2' : (invY4 τw) ^ 2 =
          (1 - (invD τw) ^ 2 - invXsq τw) - (invY0 τw) ^ 2 - (invY1 τw) ^ 2 -
          (invY2 τw) ^ 2 - (invY3 τw) ^ 2 := hy4_2
      linarith [h1', h2']
  · have htr := sparseFourConfigOct_traces (invA τw) (invB τw) (invC τw) (invC1 τw) (invC2 τw)
      (invH τw) (invD τw) X Y
    rcases htr with ⟨ho01, ho02, ho03, ho12, ho13, ho23, hR012, hR013, hR023, _, hω1, hω2, hω3⟩
    have ho01' : fpOverlap p 0 1 = τw 0 := by rw [hp_eq, ho01, ha2]
    have ho02' : fpOverlap p 0 2 = τw 1 := by rw [hp_eq, ho02, hc2]
    have ho03' : fpOverlap p 0 3 = τw 2 := by rw [hp_eq, ho03, hd2]
    have ho12' : fpOverlap p 1 2 = τw 3 := by
      rw [hp_eq, ho12]
      rw [octNormSq_add, octNormSq_smul, octNormSq_z_coords, octDot_smul_right,
        octDot_scalar_left, octonionReal_add, octonionReal_smul, octonionReal_scalar,
        octNormSq_scalar]
      have hi_re : octonionReal octI = 0 := rfl
      rw [hi_re, mul_zero, add_zero]
      have hsq : (invA τw * invC τw) ^ 2 + (invB τw) ^ 2 * ((invC1 τw) ^ 2 + (invC2 τw) ^ 2) +
          2 * (invB τw) * ((invA τw * invC τw) * invC1 τw) =
          (invA τw * invC τw + invB τw * invC1 τw) ^ 2 + (invB τw * invC2 τw) ^ 2 := by ring
      linarith [hsq, hC2_2, show invRadC2 τw = τw 3 - (invA τw * invC τw + invB τw * invC1 τw) ^ 2 from rfl]
    have ho13' : fpOverlap p 1 3 = τw 4 := by
      rw [hp_eq, ho13]
      rw [octNormSq_add, octNormSq_smul, octNormSq_X_coords, octDot_smul_right,
        octDot_scalar_left, octonionReal_add, octonionReal_add, octonionReal_smul,
        octonionReal_smul, octonionReal_scalar, octNormSq_scalar]
      have hi_re : octonionReal octI = 0 := rfl
      have hj_re : octonionReal octJ = 0 := rfl
      rw [hi_re, hj_re, mul_zero, mul_zero, add_zero, add_zero]
      have hXsq_eq : (invX0 τw) ^ 2 + (invX1 τw) ^ 2 + (invX2 τw) ^ 2 = invXsq τw := by
        linarith [hx2_2, show invRadX2 τw = invXsq τw - (invX0 τw) ^ 2 - (invX1 τw) ^ 2 from rfl]
      rw [hXsq_eq]
      unfold invXsq
      field_simp [hb_pos.ne']
      ring
    have ho23' : fpOverlap p 2 3 = τw 5 := by
      rw [hp_eq, ho23, hg3_eq, octNormSq_Y_coords]
      have hy0_re : invM τw = invK0 τw + invH τw * invY0 τw := by
        unfold invY0; field_simp [hH_pos.ne']; ring
      have hy1_re : invN τw = invK1 τw + invH τw * invY1 τw := by
        unfold invY1; field_simp [hH_pos.ne']; ring
      have hy2_re : invP τw = invK2 τw + invH τw * invY2 τw := by
        unfold invY2; field_simp [hH_pos.ne']; ring
      have hy4_eq : (invH τw * invY4 τw) ^ 2 = (invH τw) ^ 2 * invRadY4 τw := by
        rw [mul_pow, hy4_2]
      have hy3_eq : invY3 τw * (2 * invH τw * invC2 τw * invX2 τw) =
          (invK0 τw) ^ 2 + (invK1 τw) ^ 2 + (invK2 τw) ^ 2 + (invK3 τw) ^ 2 +
          (invH τw) ^ 2 * invYsq τw +
          2 * invH τw * (invK0 τw * invY0 τw + invK1 τw * invY1 τw + invK2 τw * invY2 τw) - τw 5 := by
        unfold invY3
        rw [div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hH_pos.ne') hC2_pos.ne') hx2_pos.ne')]
      have hK3_def : invK3 τw = -(invC2 τw * invX2 τw) := rfl
      rw [hK3_def] at hy3_eq
      rw [hy0_re, hy1_re, hy2_re, hy4_eq,
        show invRadY4 τw = invYsq τw - (invY0 τw) ^ 2 - (invY1 τw) ^ 2 - (invY2 τw) ^ 2 - (invY3 τw) ^ 2 from rfl,
        hK3_def]
      linarith [hy3_eq, show
        (invK0 τw + invH τw * invY0 τw) ^ 2 + (invK1 τw + invH τw * invY1 τw) ^ 2 +
          (invK2 τw + invH τw * invY2 τw) ^ 2 + (-(invC2 τw * invX2 τw) + invH τw * invY3 τw) ^ 2 +
          (invH τw) ^ 2 * (invYsq τw - (invY0 τw) ^ 2 - (invY1 τw) ^ 2 - (invY2 τw) ^ 2 - (invY3 τw) ^ 2) =
        (invK0 τw) ^ 2 + (invK1 τw) ^ 2 + (invK2 τw) ^ 2 + (-(invC2 τw * invX2 τw)) ^ 2 +
          (invH τw) ^ 2 * invYsq τw +
          2 * invH τw * (invK0 τw * invY0 τw + invK1 τw * invY1 τw + invK2 τw * invY2 τw) -
          invY3 τw * (2 * invH τw * invC2 τw * invX2 τw) by ring]
    have hR012' : fpTriangle p 0 1 2 = τw 6 := by
      rw [hp_eq, hR012, oct_g1_expand]
      have hre : octonionReal (octonionScalar (invA τw * invC τw + invB τw * invC1 τw) +
          (invB τw * invC2 τw) • octI + (0 : ℝ) • octJ + (0 : ℝ) • octK + (0 : ℝ) • octL) =
          invA τw * invC τw + invB τw * invC1 τw := by
        simp only [octonionReal_add, octonionReal_smul, octonionReal_scalar]
        have hi_re : octonionReal octI = 0 := rfl
        have hj_re : octonionReal octJ = 0 := rfl
        have hk_re : octonionReal octK = 0 := rfl
        have hl_re : octonionReal octL = 0 := rfl
        rw [hi_re, hj_re, hk_re, hl_re]
        ring
      rw [hre]
      unfold invC1
      field_simp [ha_pos.ne', hb_pos.ne', hc_pos.ne']
      ring
    have hR013' : fpTriangle p 0 1 3 = τw 7 := by
      rw [hp_eq, hR013, oct_g2_expand]
      have hre : octonionReal (octonionScalar (invA τw * invD τw + invB τw * invX0 τw) +
          (invB τw * invX1 τw) • octI + (invB τw * invX2 τw) • octJ + (0 : ℝ) • octK + (0 : ℝ) • octL) =
          invA τw * invD τw + invB τw * invX0 τw := by
        simp only [octonionReal_add, octonionReal_smul, octonionReal_scalar]
        have hi_re : octonionReal octI = 0 := rfl
        have hj_re : octonionReal octJ = 0 := rfl
        have hk_re : octonionReal octK = 0 := rfl
        have hl_re : octonionReal octL = 0 := rfl
        rw [hi_re, hj_re, hk_re, hl_re]
        ring
      rw [hre]
      unfold invX0
      field_simp [ha_pos.ne', hb_pos.ne', hd_pos.ne']
      ring
    have hR023' : fpTriangle p 0 2 3 = τw 8 := by
      rw [hp_eq, hR023, hg3_eq]
      have hre : octonionReal (octonionScalar (invM τw) + invN τw • octI + invP τw • octJ +
          (invK3 τw + invH τw * invY3 τw) • octK + (invH τw * invY4 τw) • octL) = invM τw := by
        simp only [octonionReal_add, octonionReal_smul, octonionReal_scalar]
        have hi_re : octonionReal octI = 0 := rfl
        have hj_re : octonionReal octJ = 0 := rfl
        have hk_re : octonionReal octK = 0 := rfl
        have hl_re : octonionReal octL = 0 := rfl
        rw [hi_re, hj_re, hk_re, hl_re]
        ring
      rw [hre]
      unfold invM
      field_simp [hc_pos.ne', hd_pos.ne']
    have hω1' : fpOmega1 p = τw 9 := by
      rw [hp_eq, hω1, oct_g1_expand, oct_g2_expand, octonionReal_mul_conj_5]
      have hre : (invA τw * invC τw + invB τw * invC1 τw) * (invA τw * invD τw + invB τw * invX0 τw) +
          (invB τw * invC2 τw) * (invB τw * invX1 τw) + 0 * (invB τw * invX2 τw) + 0 * 0 + 0 * 0 =
          invU τw * invQ0 τw + invV τw * invB τw * invX1 τw := by
        unfold invU invQ0 invV; ring
      rw [hre]
      unfold invX1
      field_simp [hc_pos.ne', hd_pos.ne', hC2_pos.ne', hb_pos.ne',
        show invV τw = invB τw * invC2 τw from rfl]
      ring
    have hω2' : fpOmega2 p = τw 10 := by
      rw [hp_eq, hω2, oct_g1_expand, hg3_eq, octonionReal_mul_5]
      have hre : (invA τw * invC τw + invB τw * invC1 τw) * invM τw -
          (invB τw * invC2 τw) * invN τw - 0 * invP τw -
          0 * (invK3 τw + invH τw * invY3 τw) - 0 * (invH τw * invY4 τw) =
          invU τw * invM τw - invV τw * invN τw := by
        unfold invU invV; ring
      rw [hre]
      unfold invN
      field_simp [ha_pos.ne', hd_pos.ne', hb_pos.ne', hC2_pos.ne',
        show invV τw = invB τw * invC2 τw from rfl]
      ring
    have hω3' : fpOmega3 p = τw 11 := by
      rw [hp_eq, hω3, oct_g2_expand, hg3_eq, octonionReal_mul_conj_5]
      have hre : (invA τw * invD τw + invB τw * invX0 τw) * invM τw +
          (invB τw * invX1 τw) * invN τw + (invB τw * invX2 τw) * invP τw +
          0 * (invK3 τw + invH τw * invY3 τw) + 0 * (invH τw * invY4 τw) =
          invQ0 τw * invM τw + invB τw * invX1 τw * invN τw + invB τw * invX2 τw * invP τw := by
        unfold invQ0; ring
      rw [hre]
      unfold invP
      field_simp [ha_pos.ne', hc_pos.ne', hb_pos.ne', hx2_pos.ne']
      ring
    have ht1' : fpDoublePair1 p = τ 9 := by
      have h := congrArg (fun v : Fin 12 → ℝ => v 9) (omegaToT_tToOmega τ)
      dsimp only [omegaToT] at h
      simp only [Fin.isValue, ↓reduceIte] at h
      change (τw 10 + τw 11) / 2 = τ 9 at h
      rw [← hω2', ← hω3'] at h
      unfold fpOmega2 fpOmega3 at h
      linarith
    have ht2' : fpDoublePair2 p = τ 10 := by
      have h := congrArg (fun v : Fin 12 → ℝ => v 10) (omegaToT_tToOmega τ)
      dsimp only [omegaToT] at h
      simp only [Fin.isValue, show (10 : Fin 12) ≠ 9 by decide, ↓reduceIte] at h
      change (τw 9 + τw 11) / 2 = τ 10 at h
      rw [← hω1', ← hω3'] at h
      unfold fpOmega1 fpOmega3 at h
      linarith
    have ht3' : fpDoublePair3 p = τ 11 := by
      have h := congrArg (fun v : Fin 12 → ℝ => v 11) (omegaToT_tToOmega τ)
      dsimp only [omegaToT] at h
      simp only [Fin.isValue, show (11 : Fin 12) ≠ 9 by decide,
        show (11 : Fin 12) ≠ 10 by decide, ↓reduceIte] at h
      change (τw 9 + τw 10) / 2 = τ 11 at h
      rw [← hω1', ← hω2'] at h
      unfold fpOmega1 fpOmega2 at h
      linarith
    funext i
    fin_cases i
    · exact ho01'
    · exact ho02'
    · exact ho03'
    · exact ho12'
    · exact ho13'
    · exact ho23'
    · exact hR012'
    · exact hR013'
    · exact hR023'
    · exact ht1'
    · exact ht2'
    · exact ht3'

theorem triangularLocalInverse_open_nbhd :
    ∃ U : Set (Fin 12 → ℝ), IsOpen U ∧
      Fin.init (fourPointTraceVec fixedS) ∈ U ∧
      ∀ τ ∈ U,
        (∀ i, IsAtom (triangularLocalInverse τ i)) ∧
        Fin.init (fourPointTraceVec (triangularLocalInverse τ)) = τ := by
  let τ0 := Fin.init (fourPointTraceVec fixedS)
  let τS := tToOmega τ0
  have hQ := nativeCornerQ_eq_fpOmega fixedS
  rw [nativeCornerQ_fixedS] at hQ
  have hω2 : fpOmega2 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 0) hQ.symm
  have hω3 : fpOmega3 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 1) hQ.symm
  have hω1 : fpOmega1 fixedS = 1 / 18 := by simpa using congrArg (fun v : Fin 3 → ℝ => v 2) hQ.symm
  have ho : ∀ i j : Fin 4, i ≠ j →
      fpOverlap fixedS i j = if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 / 2 else 1 / 3 := by
    intro i j hij
    change nativeOverlaps fixedS i j = _
    rw [nativeOverlaps_fixedS_eq]
    simp [hij]
  have hR012 : fpTriangle fixedS 0 1 2 = 1 / 6 := by
    rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]; simp [fixedSTriangleVal]
  have hR013 : fpTriangle fixedS 0 1 3 = 1 / 6 := by
    rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]; simp [fixedSTriangleVal]
  have hR023 : fpTriangle fixedS 0 2 3 = 1 / 9 := by
    rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]; simp [fixedSTriangleVal]
  have hτ9 : τS 9 = fpOmega1 fixedS := by
    simp [τS, tToOmega, τ0, Fin.init, fourPointTraceVec, fpOmega1]
  have hτ10 : τS 10 = fpOmega2 fixedS := by
    simp [τS, tToOmega, τ0, Fin.init, fourPointTraceVec, fpOmega2]
  have hτ11 : τS 11 = fpOmega3 fixedS := by
    simp [τS, tToOmega, τ0, Fin.init, fourPointTraceVec, fpOmega3]
  have h0 : τS 0 = 1 / 2 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using ho 0 1 (by decide)
  have h1 : τS 1 = 1 / 3 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using ho 0 2 (by decide)
  have h2 : τS 2 = 1 / 3 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using ho 0 3 (by decide)
  have h3 : τS 3 = 1 / 3 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using ho 1 2 (by decide)
  have h4 : τS 4 = 1 / 3 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using ho 1 3 (by decide)
  have h5 : τS 5 = 1 / 3 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using ho 2 3 (by decide)
  have h6 : τS 6 = 1 / 6 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using hR012
  have h7 : τS 7 = 1 / 6 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using hR013
  have h8 : τS 8 = 1 / 9 := by simpa [τS, tToOmega, τ0, Fin.init, fourPointTraceVec] using hR023
  have h9 : τS 9 = 1 / 18 := hτ9.trans hω1
  have h10 : τS 10 = 1 / 18 := hτ10.trans hω2
  have h11 : τS 11 = 1 / 18 := hτ11.trans hω3
  exact triangularLocalInverse_open_nbhd_at τ0 τS rfl h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem mvPolynomial_eq_zero_of_eq_zero_on_open :
    ∀ {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (U : Set (Fin n → ℝ)),
      IsOpen U → U.Nonempty → (∀ x ∈ U, MvPolynomial.eval x P = 0) → P = 0
  | 0, P, U, _, ⟨x0, hx0⟩, hvanish => by
    have hev := hvanish x0 hx0
    have heq : P = MvPolynomial.C (MvPolynomial.eval x0 P) := by
      clear hvanish hev
      induction P using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => rw [map_add, map_add, ← hp, ← hq]
      | mul_X p i => exact Fin.elim0 i
    rw [heq, hev, map_zero]
  | n + 1, P, U, hU, ⟨v, hv⟩, hvanish => by
    let emb : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun p => Fin.cons p.1 p.2
    have hemb : Continuous emb := by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ ?_ i
      · exact continuous_fst
      · intro j; exact (continuous_apply j).comp continuous_snd
    have hpre : IsOpen (emb ⁻¹' U) := hU.preimage hemb
    have hv_mem : (v 0, Fin.tail v) ∈ emb ⁻¹' U := by
      change Fin.cons (v 0) (Fin.tail v) ∈ U
      simpa [Fin.cons_self_tail] using hv
    obtain ⟨I, U', hI, hU', hv0I, hvU', hsub⟩ := isOpen_prod_iff.mp hpre (v 0) (Fin.tail v) hv_mem
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hI (v 0) hv0I
    let Q := MvPolynomial.finSuccEquiv ℝ n P
    have h_finSucc_C : ∀ {m : ℕ} (a : ℝ),
        (MvPolynomial.finSuccEquiv ℝ m) (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
      intro m a
      have h0 := congrArg (fun f : ℝ →+* MvPolynomial (Fin (m + 1)) ℝ => f a)
        (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := ℝ) m)
      have h1 := congrArg (MvPolynomial.finSuccEquiv ℝ m) h0
      simpa [Function.comp_apply] using h1.symm
    have heval_cons : ∀ (t : ℝ) (u : Fin n → ℝ) (R : MvPolynomial (Fin (n + 1)) ℝ),
        Polynomial.eval t ((MvPolynomial.finSuccEquiv ℝ n R).map (MvPolynomial.eval₂Hom (RingHom.id ℝ) u)) =
          MvPolynomial.eval (Fin.cons t u) R := by
      intro t u R
      induction R using MvPolynomial.induction_on with
      | C a => rw [h_finSucc_C, Polynomial.map_C, Polynomial.eval_C]; simp
      | add p q hp hq => simp [map_add, Polynomial.eval_add, hp, hq]
      | mul_X p i hp =>
        simp only [map_mul, Polynomial.map_mul, Polynomial.eval_mul, hp]
        congr 1
        refine Fin.cases ?_ ?_ i
        · simp [MvPolynomial.finSuccEquiv_X_zero]
        · intro j; simp [MvPolynomial.finSuccEquiv_X_succ]
    have hQ_coeff : ∀ k : ℕ, Q.coeff k = 0 := by
      intro k
      apply mvPolynomial_eq_zero_of_eq_zero_on_open (Q.coeff k) U' hU' ⟨Fin.tail v, hvU'⟩
      intro u hu
      let q : Polynomial ℝ := Q.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) u)
      have hq_zero : q = 0 := by
        by_contra hq_ne
        have hinf : (Set.Ioo (v 0 - ε) (v 0 + ε)).Infinite :=
          Set.Ioo_infinite (by linarith)
        have hsub_roots : Set.Ioo (v 0 - ε) (v 0 + ε) ⊆ (q.roots.toFinset : Set ℝ) := by
          intro t ht
          have ht_ball : t ∈ Metric.ball (v 0) ε := by
            rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
            exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
          have ht_U : Fin.cons t u ∈ U := by
            change emb (t, u) ∈ U
            exact hsub (Set.mk_mem_prod (hball ht_ball) hu)
          have ht_eval : q.eval t = 0 := by
            simpa [q, Q, heval_cons t u P] using hvanish (Fin.cons t u) ht_U
          exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq_ne).mpr ht_eval)
        exact hinf ((q.roots.toFinset.finite_toSet).subset hsub_roots)
      have hc := congrArg (fun p : Polynomial ℝ => p.coeff k) hq_zero
      change (Q.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) u)).coeff k = 0 at hc
      rw [Polynomial.coeff_map] at hc
      exact hc
    have hQ0 : Q = 0 := Polynomial.ext fun k => by simp [hQ_coeff k]
    exact (MvPolynomial.finSuccEquiv ℝ n).injective (by simpa [Q] using hQ0)

theorem fourAtom_trace_ideal_principal (F : MvPolynomial (Fin 13) ℝ)
    (hvanish : ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) →
      MvPolynomial.eval (fourPointTraceVec p) F = 0) :
    ∃ G : MvPolynomial (Fin 13) ℝ, F = traceRelationMvPoly * G := by
  let swap012 : Equiv.Perm (Fin 13) := Equiv.swap 0 12
  let ren : MvPolynomial (Fin 13) ℝ ≃ₐ[ℝ] MvPolynomial (Fin 13) ℝ :=
    MvPolynomial.renameEquiv ℝ swap012
  let e : MvPolynomial (Fin 13) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin 12) ℝ) :=
    ren.trans (MvPolynomial.finSuccEquiv ℝ 12)
  let Q0 : MvPolynomial (Fin 13) ℝ :=
    MvPolynomial.X 9 + MvPolynomial.X 10 + MvPolynomial.X 11
      - MvPolynomial.C (1 / 2)
      + MvPolynomial.C (1 / 2) *
          (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 +
           MvPolynomial.X 3 + MvPolynomial.X 4 + MvPolynomial.X 5)
      - MvPolynomial.C (1 / 2) *
          (MvPolynomial.X 0 * MvPolynomial.X 5 +
           MvPolynomial.X 1 * MvPolynomial.X 4 +
           MvPolynomial.X 2 * MvPolynomial.X 3)
      - MvPolynomial.X 6 - MvPolynomial.X 7 - MvPolynomial.X 8
  let Q_base : MvPolynomial (Fin 12) ℝ :=
    MvPolynomial.X 9 + MvPolynomial.X 10 + MvPolynomial.X 11
      - MvPolynomial.C (1 / 2)
      + MvPolynomial.C (1 / 2) *
          (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 +
           MvPolynomial.X 3 + MvPolynomial.X 4 + MvPolynomial.X 5)
      - MvPolynomial.C (1 / 2) *
          (MvPolynomial.X 0 * MvPolynomial.X 5 +
           MvPolynomial.X 1 * MvPolynomial.X 4 +
           MvPolynomial.X 2 * MvPolynomial.X 3)
      - MvPolynomial.X 6 - MvPolynomial.X 7 - MvPolynomial.X 8
  let mapIdx12 : Fin 12 → Fin 12 := fun i =>
    if i = 0 then 11 else ⟨i.val - 1, by omega⟩
  let invIdx12 : Fin 12 → Fin 12 := fun j =>
    if h : j = 11 then 0 else ⟨j.val + 1, by
      have hj := j.isLt
      have hne : j.val ≠ 11 := fun hv => h (Fin.ext hv)
      omega⟩
  let Q_sw : MvPolynomial (Fin 12) ℝ := MvPolynomial.rename mapIdx12 Q_base
  have hsw012 : ∀ i : Fin 12, swap012 ⟨i.val, by omega⟩ = (mapIdx12 i).succ := by
    intro i; fin_cases i <;> decide
  have hsw12 : swap012 12 = 0 := by decide
  have he_X : ∀ i : Fin 12, e (MvPolynomial.X ⟨i.val, by omega⟩) =
      Polynomial.C (MvPolynomial.X (mapIdx12 i)) := by
    intro i
    dsimp only [e, ren]
    rw [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      hsw012 i, MvPolynomial.finSuccEquiv_X_succ]
  have he_X' : ∀ (i : Fin 13) (hi : i.val < 12),
      e (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X (mapIdx12 ⟨i.val, hi⟩)) := by
    intro i hi
    exact he_X ⟨i.val, hi⟩
  have he_C : ∀ r : ℝ, e (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
    intro r
    dsimp only [e, ren]
    rw [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
    have h0 := congrArg (fun f : ℝ →+* MvPolynomial (Fin 13) ℝ => f r)
      (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := ℝ) 12)
    have h1 := congrArg (MvPolynomial.finSuccEquiv ℝ 12) h0
    simpa [Function.comp_apply] using h1.symm
  have he_12 : e (MvPolynomial.X 12) = Polynomial.X := by
    dsimp only [e, ren]
    rw [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      hsw12, MvPolynomial.finSuccEquiv_X_zero]
  have hrel_e : e traceRelationMvPoly = Polynomial.X - Polynomial.C Q_sw := by
    unfold traceRelationMvPoly
    change e (MvPolynomial.X 12 - Q0) = _
    rw [map_sub, he_12]
    have hq : e Q0 = Polynomial.C Q_sw := by
      dsimp only [Q0, Q_sw, Q_base]
      simp only [map_sub, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C, he_C]
      rw [he_X' 0 (by decide), he_X' 1 (by decide), he_X' 2 (by decide), he_X' 3 (by decide),
        he_X' 4 (by decide), he_X' 5 (by decide), he_X' 6 (by decide), he_X' 7 (by decide),
        he_X' 8 (by decide), he_X' 9 (by decide), he_X' 10 (by decide), he_X' 11 (by decide)]
      rfl
    rw [hq]
  have hdiv :
      e F = Polynomial.C ((e F).eval Q_sw) +
        (Polynomial.X - Polynomial.C Q_sw) * ((e F) /ₘ (Polynomial.X - Polynomial.C Q_sw)) := by
    have h0 := (Polynomial.modByMonic_add_div (e F) (Polynomial.X - Polynomial.C Q_sw)).symm
    rwa [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h0
  let rem12 : MvPolynomial (Fin 12) ℝ := (e F).eval Q_sw
  obtain ⟨U, hU_open, hτS_U, hU_prop⟩ := triangularLocalInverse_open_nbhd
  let U_sw : Set (Fin 12 → ℝ) := {u | (fun i : Fin 12 => u (mapIdx12 i)) ∈ U}
  have hmap_cont : Continuous (fun (u : Fin 12 → ℝ) (i : Fin 12) => u (mapIdx12 i)) :=
    continuous_pi fun i => continuous_apply (mapIdx12 i)
  have hU_sw_open : IsOpen U_sw := hU_open.preimage hmap_cont
  have hU_sw_ne : U_sw.Nonempty := by
    let τS := Fin.init (fourPointTraceVec fixedS)
    refine ⟨fun j => τS (invIdx12 j), ?_⟩
    show (fun i => τS (invIdx12 (mapIdx12 i))) ∈ U
    have hback : (fun i : Fin 12 => τS (invIdx12 (mapIdx12 i))) = τS := by
      funext i; fin_cases i <;> rfl
    rwa [hback]
  have hrem_vanish : ∀ u ∈ U_sw, MvPolynomial.eval u rem12 = 0 := by
    intro u hu
    let τ : Fin 12 → ℝ := fun i => u (mapIdx12 i)
    have hτ_U : τ ∈ U := hu
    obtain ⟨hp_atom, hp_init⟩ := hU_prop τ hτ_U
    let p := triangularLocalInverse τ
    have heval_Qsw : MvPolynomial.eval u Q_sw = fourPointTraceVec p 12 := by
      have hrel0 := traceRelationMvPoly_eval_eq_zero p hp_atom
      have hrel_eval : fourPointTraceVec p 12 = MvPolynomial.eval τ Q_base := by
        have hQ0_eval : MvPolynomial.eval (fourPointTraceVec p) Q0 =
            MvPolynomial.eval (Fin.init (fourPointTraceVec p)) Q_base := by
          simp [Q0, Q_base, Fin.init]
        have htr : MvPolynomial.eval (fourPointTraceVec p) traceRelationMvPoly =
            fourPointTraceVec p 12 - MvPolynomial.eval (fourPointTraceVec p) Q0 := by
          change MvPolynomial.eval (fourPointTraceVec p) (MvPolynomial.X 12 - Q0) = _
          simp
        rw [htr, hQ0_eval, hp_init] at hrel0
        linarith
      rw [hrel_eval]
      dsimp only [Q_sw]
      rw [MvPolynomial.eval_rename]
      rfl
    have heval_eval : ∀ (R : MvPolynomial (Fin 13) ℝ),
        MvPolynomial.eval u ((e R).eval Q_sw) = MvPolynomial.eval (fourPointTraceVec p) R := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C a =>
        simp [he_C]
      | add r₁ r₂ hr₁ hr₂ =>
        simp [map_add, Polynomial.eval_add, hr₁, hr₂]
      | mul_X r i hr =>
        simp only [map_mul, Polynomial.eval_mul, hr]
        congr 1
        by_cases hi12 : i = 12
        · subst hi12
          rw [he_12, Polynomial.eval_X, MvPolynomial.eval_X]
          exact heval_Qsw
        · have hi_lt : i.val < 12 := by omega
          rw [he_X' i hi_lt, Polynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_X]
          exact congrArg (fun v : Fin 12 → ℝ => v ⟨i.val, hi_lt⟩) hp_init.symm
    change MvPolynomial.eval u ((e F).eval Q_sw) = 0
    rw [heval_eval F]
    exact hvanish p hp_atom
  have hrem0 : rem12 = 0 :=
    mvPolynomial_eq_zero_of_eq_zero_on_open rem12 U_sw hU_sw_open hU_sw_ne hrem_vanish
  have hrem0' : (e F).eval Q_sw = 0 := hrem0
  rw [hrem0', map_zero, zero_add] at hdiv
  rw [← hrel_e] at hdiv
  refine ⟨e.symm ((e F) /ₘ (e traceRelationMvPoly)), ?_⟩
  have hback := congrArg e.symm hdiv
  simpa [map_mul] using hback

end AlbertSequential


