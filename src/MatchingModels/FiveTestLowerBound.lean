/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.FiveTestClifford
public import MatchingModels.MatrixClassIBridge
import Mathlib.Tactic.NormNum

/-!
# Five-Test Lower-Bound Comparators (`cor:five:minimum` lower bounds)

Constructs the explicit 12-dimensional complex Hilbert comparators (and their real Hilbert,
quaternionic, and algebraic lifts) realizing the `1 / 2 : 1 / 2` mixture of `pentadFPlus` and
`pentadFMinus` in the standard `ℂ^6 ⊕ ℂ^6` block representation, and proves agreement with `pentadF`:

* from `pentadF 0` (using state `P₀ / 4`) through word length `9` (`L_min(p₀) ≥ 10`),
* from `(1 / 3 : ℝ) • albertUnit` (using state `I₁₂ / 12`) through word length `10`
  (`L_min(e/3) ≥ 11`),

together with the exact separating-word probabilities and defects `± 1 / 1296` at length `10`
(`pentadSepWord10`, `pentadAltSepWord10`) and `± 1 / 3888` at length `11` (`pentadSepWord11`,
`pentadAltSepWord11`).
-/

set_option autoImplicit false

@[expose] public section

namespace AlbertSequential.MatchingModels

noncomputable section

/-- Six-dimensional complex projection pentad for `pentadFPlus`. -/
def pentadProjPlus : Fin 5 → Matrix (Fin 6) (Fin 6) ℂ :=
  quatProj6 standardQuaternionicWindow pentadFPlus pentadFPlus_mem_standardQuaternionicWindow

/-- Six-dimensional complex projection pentad for `pentadFMinus`. -/
def pentadProjMinus : Fin 5 → Matrix (Fin 6) (Fin 6) ℂ :=
  quatProj6 standardQuaternionicWindow pentadFMinus pentadFMinus_mem_standardQuaternionicWindow

theorem pentadProjPlus_hermitian (i : Fin 5) : (pentadProjPlus i).IsHermitian :=
  quatProj6_hermitian standardQuaternionicWindow pentadFPlus
    pentadFPlus_mem_standardQuaternionicWindow i

theorem pentadProjMinus_hermitian (i : Fin 5) : (pentadProjMinus i).IsHermitian :=
  quatProj6_hermitian standardQuaternionicWindow pentadFMinus
    pentadFMinus_mem_standardQuaternionicWindow i

theorem pentadProjPlus_idempotent (i : Fin 5) :
    pentadProjPlus i * pentadProjPlus i = pentadProjPlus i :=
  quatProj6_idempotent standardQuaternionicWindow pentadFPlus
    pentadFPlus_mem_standardQuaternionicWindow pentadFPlus_isAtom i

theorem pentadProjMinus_idempotent (i : Fin 5) :
    pentadProjMinus i * pentadProjMinus i = pentadProjMinus i :=
  quatProj6_idempotent standardQuaternionicWindow pentadFMinus
    pentadFMinus_mem_standardQuaternionicWindow pentadFMinus_isAtom i

theorem pentadProjPlus_trace (i : Fin 5) : Matrix.trace (pentadProjPlus i) = 2 :=
  quatProj6_trace standardQuaternionicWindow pentadFPlus
    pentadFPlus_mem_standardQuaternionicWindow pentadFPlus_isAtom i

theorem pentadProjMinus_trace (i : Fin 5) : Matrix.trace (pentadProjMinus i) = 2 :=
  quatProj6_trace standardQuaternionicWindow pentadFMinus
    pentadFMinus_mem_standardQuaternionicWindow pentadFMinus_isAtom i

/-- Direct-sum comparator on `ℂ^12` in state `P₀ / 4`, modeling the `(1/2, 1/2)` mixture of
`pentadFPlus` and `pentadFMinus` from `p₀`. -/
def fiveTestComparator_p0 : HilbertProjectiveData (Fin 5) ℂ (EuclideanSpace ℂ (Fin 12)) :=
  c12Proj0MixtureModel pentadProjPlus pentadProjMinus
    pentadProjPlus_hermitian pentadProjPlus_idempotent
    pentadProjMinus_hermitian pentadProjMinus_idempotent
    0 (pentadProjPlus_trace 0) (pentadProjMinus_trace 0)

/-- Direct-sum comparator on `ℂ^12` in the maximally mixed state `I₁₂ / 12`, modeling the
`(1/2, 1/2)` mixture of `pentadFPlus` and `pentadFMinus` from `e / 3`. -/
def fiveTestComparator_e3 : HilbertProjectiveData (Fin 5) ℂ (EuclideanSpace ℂ (Fin 12)) :=
  c12BlockMixtureModel pentadProjPlus pentadProjMinus
    pentadProjPlus_hermitian pentadProjPlus_idempotent
    pentadProjMinus_hermitian pentadProjMinus_idempotent
    (1 / 2 : ℝ) (by constructor <;> norm_num)

theorem fiveTestComparator_p0_probability (w : Word (Fin 5)) :
    fiveTestComparator_p0.probability w =
      (1 / 2 : ℝ) * nativeWordProbability pentadFPlus (pentadFPlus 0) w +
      (1 / 2 : ℝ) * nativeWordProbability pentadFMinus (pentadFMinus 0) w := by
  rw [fiveTestComparator_p0, c12Proj0MixtureModel_probability]
  dsimp only [pentadProjPlus, pentadProjMinus]
  rw [quatProj6_wordProb_atom, quatProj6_wordProb_atom]

theorem fiveTestComparator_e3_probability (w : Word (Fin 5)) :
    fiveTestComparator_e3.probability w =
      (1 / 2 : ℝ) * nativeWordProbability pentadFPlus ((1 / 3 : ℝ) • albertUnit) w +
      (1 / 2 : ℝ) * nativeWordProbability pentadFMinus ((1 / 3 : ℝ) • albertUnit) w := by
  rw [fiveTestComparator_e3, c12BlockMixtureModel_probability]
  dsimp only [pentadProjPlus, pentadProjMinus]
  rw [quatProj6_wordProb_e3, quatProj6_wordProb_e3, show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]

/-- Complex Hilbert Class-(I) lower bound from `p₀`: matches `pentadF` through word length `9`. -/
theorem fiveTestComparator_p0_matches (w : Word (Fin 5)) (hw : w.length ≤ 9) :
    fiveTestComparator_p0.probability w = nativeWordProbability pentadF (pentadF 0) w := by
  rw [fiveTestComparator_p0_probability, pentadF_p0_match_avg w hw]

/-- Complex Hilbert Class-(I) lower bound from `e / 3`: matches `pentadF` through word length `10`. -/
theorem fiveTestComparator_e3_matches (w : Word (Fin 5)) (hw : w.length ≤ 10) :
    fiveTestComparator_e3.probability w =
      nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w := by
  rw [fiveTestComparator_e3_probability, pentadF_e3_match_avg w hw]

theorem fiveTestComparator_p0_toAlgebraic_matches (w : Word (Fin 5)) (hw : w.length ≤ 9) :
    fiveTestComparator_p0.toAlgebraic.probability w =
      nativeWordProbability pentadF (pentadF 0) w := by
  rw [HilbertProjectiveData.toAlgebraic_probability, fiveTestComparator_p0_matches w hw]

theorem fiveTestComparator_e3_toAlgebraic_matches (w : Word (Fin 5)) (hw : w.length ≤ 10) :
    fiveTestComparator_e3.toAlgebraic.probability w =
      nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w := by
  rw [HilbertProjectiveData.toAlgebraic_probability, fiveTestComparator_e3_matches w hw]

/-- Real Hilbert Class-(I) comparator from `p₀`. -/
def fiveTestComparator_p0_real :
    HilbertProjectiveData (Fin 5) ℝ (CyclicHilbert fiveTestComparator_p0.toAlgebraic) :=
  hilbertComplexToReal fiveTestComparator_p0

/-- Real Hilbert Class-(I) comparator from `e / 3`. -/
def fiveTestComparator_e3_real :
    HilbertProjectiveData (Fin 5) ℝ (CyclicHilbert fiveTestComparator_e3.toAlgebraic) :=
  hilbertComplexToReal fiveTestComparator_e3

theorem fiveTestComparator_p0_real_matches (w : Word (Fin 5)) (hw : w.length ≤ 9) :
    fiveTestComparator_p0_real.probability w = nativeWordProbability pentadF (pentadF 0) w :=
  (hilbertComplexToReal_probability fiveTestComparator_p0 w).trans
    (fiveTestComparator_p0_matches w hw)

theorem fiveTestComparator_e3_real_matches (w : Word (Fin 5)) (hw : w.length ≤ 10) :
    fiveTestComparator_e3_real.probability w =
      nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w :=
  (hilbertComplexToReal_probability fiveTestComparator_e3 w).trans
    (fiveTestComparator_e3_matches w hw)

/-- Quaternionic Class-(I) comparator from `p₀`. -/
def fiveTestComparator_p0_quat :
    QuaternionicProjectiveData (Fin 5)
      (fourCopyQuaternionicStructure (H := CyclicHilbert fiveTestComparator_p0.toAlgebraic)) :=
  hilbertComplexToQuaternionic fiveTestComparator_p0

/-- Quaternionic Class-(I) comparator from `e / 3`. -/
def fiveTestComparator_e3_quat :
    QuaternionicProjectiveData (Fin 5)
      (fourCopyQuaternionicStructure (H := CyclicHilbert fiveTestComparator_e3.toAlgebraic)) :=
  hilbertComplexToQuaternionic fiveTestComparator_e3

theorem fiveTestComparator_p0_quat_matches (w : Word (Fin 5)) (hw : w.length ≤ 9) :
    fiveTestComparator_p0_quat.toAlgebraic.probability w =
      nativeWordProbability pentadF (pentadF 0) w :=
  (hilbertComplexToQuaternionic_probability fiveTestComparator_p0 w).trans
    (fiveTestComparator_p0_matches w hw)

theorem fiveTestComparator_p0_quat_state_matches (w : Word (Fin 5)) (hw : w.length ≤ 9) :
    fiveTestComparator_p0_quat.state (fiveTestComparator_p0_quat.wordEffect w) =
      nativeWordProbability pentadF (pentadF 0) w :=
  (hilbertComplexToQuaternionic_state_wordEffect fiveTestComparator_p0 w).trans
    (fiveTestComparator_p0_matches w hw)

theorem fiveTestComparator_e3_quat_matches (w : Word (Fin 5)) (hw : w.length ≤ 10) :
    fiveTestComparator_e3_quat.toAlgebraic.probability w =
      nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w :=
  (hilbertComplexToQuaternionic_probability fiveTestComparator_e3 w).trans
    (fiveTestComparator_e3_matches w hw)

theorem fiveTestComparator_e3_quat_state_matches (w : Word (Fin 5)) (hw : w.length ≤ 10) :
    fiveTestComparator_e3_quat.state (fiveTestComparator_e3_quat.wordEffect w) =
      nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w :=
  (hilbertComplexToQuaternionic_state_wordEffect fiveTestComparator_e3 w).trans
    (fiveTestComparator_e3_matches w hw)

/-- Explicit length-10 separation from `p₀` (`+ 1 / 1296` defect at `pentadSepWord10`). -/
theorem fiveTestComparator_p0_sepWord10 :
    fiveTestComparator_p0.probability pentadSepWord10 = 1549 / 419904 ∧
    fiveTestComparator_p0.probability pentadSepWord10 -
      nativeWordProbability pentadF (pentadF 0) pentadSepWord10 = 1 / 1296 := by
  rw [fiveTestComparator_p0_probability]
  obtain ⟨hL, hK, hmK, _⟩ := pentadSepWord10_values
  rw [hL, hK, hmK]
  constructor <;> norm_num

/-- Explicit length-10 separation from `p₀` (`- 1 / 1296` defect at `pentadAltSepWord10`). -/
theorem fiveTestComparator_p0_altSepWord10 :
    fiveTestComparator_p0.probability pentadAltSepWord10 = 901 / 419904 ∧
    nativeWordProbability pentadF (pentadF 0) pentadAltSepWord10 -
      fiveTestComparator_p0.probability pentadAltSepWord10 = 1 / 1296 := by
  rw [fiveTestComparator_p0_probability]
  obtain ⟨hL, hK, hmK, _⟩ := pentadAltSepWord10_values
  rw [hL, hK, hmK]
  constructor <;> norm_num

/-- Explicit length-11 separation from `e / 3` (`+ 1 / 3888` defect at `pentadSepWord11`). -/
theorem fiveTestComparator_e3_sepWord11 :
    fiveTestComparator_e3.probability pentadSepWord11 = 1549 / 1259712 ∧
    fiveTestComparator_e3.probability pentadSepWord11 -
      nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) pentadSepWord11 = 1 / 3888 := by
  rw [fiveTestComparator_e3_probability]
  obtain ⟨hL, hK, hmK, _⟩ := pentadSepWord11_values
  rw [hL, hK, hmK]
  constructor <;> norm_num

/-- Explicit length-11 separation from `e / 3` (`- 1 / 3888` defect at `pentadAltSepWord11`). -/
theorem fiveTestComparator_e3_altSepWord11 :
    fiveTestComparator_e3.probability pentadAltSepWord11 = 901 / 1259712 ∧
    nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) pentadAltSepWord11 -
      fiveTestComparator_e3.probability pentadAltSepWord11 = 1 / 3888 := by
  rw [fiveTestComparator_e3_probability]
  obtain ⟨hL, hK, hmK, _⟩ := pentadAltSepWord11_values
  rw [hL, hK, hmK]
  constructor <;> norm_num

end

end AlbertSequential.MatchingModels
