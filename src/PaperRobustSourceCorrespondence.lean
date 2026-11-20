/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.RobustNativeMS
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential.BlockB

/-- A rational coefficient of the printed expression, after the mandatory leading yes on A. -/
def sourceCoefficient (w : Word Letter) (L : List (ℚ × Word Letter)) : ℚ :=
  (L.map fun m => if addYesA m.2 = w then m.1 else 0).sum

private theorem sourceCoefficient_append (w : Word Letter) (L R : List (ℚ × Word Letter)) :
    sourceCoefficient w (L ++ R) = sourceCoefficient w L + sourceCoefficient w R := by
  simp [sourceCoefficient]

private theorem sourceCoefficient_flatMap {T : Type*} (w : Word Letter) (l : List T)
    (f : T → List (ℚ × Word Letter)) :
    sourceCoefficient w (l.flatMap f) = (l.map fun z => sourceCoefficient w (f z)).sum := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [List.flatMap_cons, sourceCoefficient_append, List.map_cons, List.sum_cons, ih]

theorem toE3Functional_coefficient_eq_source (L : List (ℚ × Word Letter)) (w : Word Letter) :
    (toE3Functional L).coefficients w = (sourceCoefficient w L : ℝ) := by
  change FiniteRealWordFunctional.coefficientsOfTerms (toE3Functional L).terms w = _
  induction L with
  | nil => simp [toE3Functional, sourceCoefficient, FiniteRealWordFunctional.coefficientsOfTerms_nil]
  | cons m L ih =>
    simp only [toE3Functional, List.map_cons, List.sum_cons, sourceCoefficient,
      FiniteRealWordFunctional.coefficientsOfTerms_cons, Finsupp.add_apply] at ih ⊢
    rw [ih]
    by_cases h : addYesA m.2 = w
    · subst h
      simp [Finsupp.single_eq_same]
    · simp only [h, ↓reduceIte, Finsupp.single_eq_of_ne (Ne.symm h), zero_add]

/-- One occurrence's four contributions in A.2; every equality test is on
the actual prefixed word, so multiple contributions to one word are retained. -/
def sourceDefectCoefficient (T : TraceTable) (θ k : ℚ) (d : Defect) (w : Word Letter) : ℚ :=
  let ε := epsQ T θ d.α
  let z := |k * d.y|
  (if addYesA (yesWord d.α) = w then z * ε / 2 else 0) +
  (if addYesA d.long = w then z / (2 * ε) else 0) +
  (if addYesA d.mid = w then -(z * d.c / ε) else 0) +
  (if addYesA d.short = w then z * (d.c * d.c) / (2 * ε) else 0)

/-- Coefficients of the accompanying recorded Gram derivation are exactly those
of the deposited table-plus-AGM formula on that derivation. -/
theorem robust_coefficient_recorded_formula (T : TraceTable) (θ : ℚ) (pairs : List (ℚ × Entry))
    (w : Word Letter) :
    (toE3Functional (lam2 T θ pairs)).coefficients w =
      (((pairs.map fun p =>
          (p.2.tabs.map fun m => if addYesA m.2.toWord = w then p.1 * m.1 else 0).sum +
          (p.2.defs.map fun d => sourceDefectCoefficient T θ p.1 d w).sum).sum : ℚ) : ℝ) := by
  rw [toE3Functional_coefficient_eq_source]
  congr 1
  rw [lam2, sourceCoefficient_flatMap]
  congr 1
  apply List.map_congr_left
  intro p _
  rw [entryTerms, sourceCoefficient_append, sourceCoefficient_flatMap]
  congr 1
  · simp [sourceCoefficient, List.map_map, Function.comp_def]
  · congr 1
    apply List.map_congr_left
    intro d _
    simp only [sourceCoefficient, defTerms, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, sourceDefectCoefficient, add_assoc]

/-- The RR example uses the letter D on the left of the exact same R2 residual
that is already in D's range. Drop it only from the final three records. -/
def eM_301_literalAlpha : Entry :=
  { eM_301 with defs := eM_301.defs.take 3 ++
      ((eM_301.defs.drop 3).map fun d => { d with α := d.α.dropLast }) }

theorem residual301_retains_D :
    (eM_301.defs.drop 3).map (fun d => (d.α, d.q)) =
      List.replicate 3 ([3, 2, 1, 3].map lt, lt 3) := by decide +kernel

theorem residual301_removal_keeps_gram_identity : eM_301_literalAlpha.ok = true := by decide +kernel

theorem residual301_removal_changes_probability_bucket :
    piQ tableM ([3, 2, 1, 3].map lt) = 1 / 81 ∧
    piQ tableM ([3, 2, 1].map lt) = 1 / 27 := by decide +kernel

/-- Transposing the symmetric HH inner product gives another local derivation
preserving the two absolute counters. The outer Gram arguments stay fixed. -/
def eM_41_transposedDerivation : Entry :=
  { eM_92 with u1 := eM_41.u1, u2 := eM_41.u2 }

theorem residual41_transposed_valid : eM_41_transposedDerivation.ok = true := by decide +kernel

private def bucketProfile (T : TraceTable) (k : ℚ) (e : Entry) : List (ℚ × ℚ) :=
  e.defs.map fun d => (piQ T d.α, |k * d.y|)

private theorem residual41_sameProfile :
    bucketProfile tableM (-81) eM_41 = bucketProfile tableM (-81) eM_41_transposedDerivation := by
  decide +kernel

theorem residual41_transposed_counters :
    counterT [(-81, eM_41)] = counterT [(-81, eM_41_transposedDerivation)] ∧
      ∀ pi : ℚ, counterW tableM [(-81, eM_41)] pi =
        counterW tableM [(-81, eM_41_transposedDerivation)] pi := by
  constructor
  · decide +kernel
  · intro pi
    have h := congrArg (fun l : List (ℚ × ℚ) =>
      (l.map fun p => if p.1 = pi then p.2 else 0).sum) residual41_sameProfile
    simpa [counterW, bucketProfile, List.map_map, Function.comp_def] using h

theorem residual41_transposed_distinct_coefficient :
    sourceCoefficient [(0, true), (1, true), (2, true)] (entryTerms tableM thetaM (-81, eM_41)) =
      243 / 524288 ∧
    sourceCoefficient [(0, true), (1, true), (2, true)]
      (entryTerms tableM thetaM (-81, eM_41_transposedDerivation)) = -393216 := by decide +kernel

end AlbertSequential.LengthSeven.Robust
