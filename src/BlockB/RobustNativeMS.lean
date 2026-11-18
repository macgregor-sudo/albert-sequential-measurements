/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RobustCert.Exact
public import RobustCert.RobustM
public import RobustCert.RobustS
public import LengthSeven.TableValues
public import LengthSeven.Adapters
public import LengthSeven.NativeBinding
public import Uniform.Main
public import RealWordFunctionals
public import ComplexWindowDeterminantAndMax
public import FixedSBinding
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Unconditional Native Certificates at `M` and `S` (`thm:cer:seven` and `prop:robust(a)`)

Binds the thirteen trace equalities of
`RobustCert` to the native Albert quadruples `maximizerConfig` (`M`) and `fixedS` (`S`), and
composing with `LengthSeven.TableValues`, `LengthSeven.Adapters`, `Uniform.Main`, and
`FiniteRealWordFunctional` to obtain unconditional native theorems with zero trace or
`TableValues` hypotheses:

1. **Trace bindings**: `isTracesM_maximizerConfig`, `tableM_holds_maximizerConfig`,
   `isTracesS_fixedS`, `tableS_holds_fixedS`.
2. **Exact certificates (`thm:cer:seven(a)`)**: `seven_M_e3_*`, `seven_M_pA_*`, `seven_S_e3_*`,
   `seven_S_pA_*` across algebraic (`AlgebraicProjectiveData`), real/complex Hilbert
   (`HilbertProjectiveData` with `[RCLike 𝕜]`), and quaternionic (`QuaternionicProjectiveData`)
   models, using the explicit single certificate vectors `certM` and `certS`.
3. **Robust certificates (`thm:cer:seven(b)` and `prop:robust(a)`)**: explicit functionals
   `robustFunctionalM` and `robustFunctionalS : FiniteRealWordFunctional 4` supported on reduced
   words of length `≤ 7` beginning with `(0, true)`, nonnegative on every model in all three
   classes, evaluating on `nativeWordProbability ... ((1 / 3 : ℝ) • albertUnit)` to
   `-(4588961 / 169869312 : ℝ)` (`M`) and `-(412734271 / 18345885696 : ℝ)` (`S`), with merged
   `coefficientNorm` within both the tighter Lean bounds (`4470 * 10^6`, `19519 * 10^6`) and
   paper bounds (`5268 * 10^6`, `2892 * 10^7`), yielding explicit uniform separation margins
   `51 / 10^13 < δ`, `6 / 10^12 < δ` (`M`) and `77 / 10^14 < δ`, `115 / 10^14 < δ` (`S`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.BlockB

open AlbertSequential AlbertSequential.LengthSeven
open AlbertSequential.LengthSeven.Cert AlbertSequential.LengthSeven.Robust
open AlbertSequential.LengthSeven.LemmaA

/-! ## Section 1: Thirteen Trace Bindings for `maximizerConfig` and `fixedS` -/

theorem isTracesM_maximizerConfig : IsTracesM (nativeTraceData maximizerConfig) := by
  obtain ⟨ho, hR, -, -, -, -, -, -, -⟩ := maximizerConfig_traces 1
  apply isTracesM_of
  · exact ho 0 1 (by decide)
  · exact ho 0 2 (by decide)
  · exact ho 0 3 (by decide)
  · exact ho 1 2 (by decide)
  · exact ho 1 3 (by decide)
  · exact ho 2 3 (by decide)
  · exact hR 0 1 2 (by decide) (by decide) (by decide)
  · exact hR 0 1 3 (by decide) (by decide) (by decide)
  · exact hR 0 2 3 (by decide) (by decide) (by decide)
  · exact hR 1 2 3 (by decide) (by decide) (by decide)
  · exact nativeTraceData_om_maximizer 1 (by decide)
  · exact nativeTraceData_om_maximizer 2 (by decide)
  · exact nativeTraceData_om_maximizer 3 (by decide)

theorem tableM_holds_maximizerConfig : tableM.Holds (nativeTraceData maximizerConfig) := by
  obtain ⟨ho, hR, -, -, -, -, -, -, -⟩ := maximizerConfig_traces 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [tableM] <;> push_cast
  · exact ho 0 1 (by decide)
  · exact ho 0 2 (by decide)
  · exact ho 0 3 (by decide)
  · exact ho 1 2 (by decide)
  · exact ho 1 3 (by decide)
  · exact ho 2 3 (by decide)
  · exact hR 0 1 2 (by decide) (by decide) (by decide)
  · exact hR 0 1 3 (by decide) (by decide) (by decide)
  · exact hR 0 2 3 (by decide) (by decide) (by decide)
  · exact hR 1 2 3 (by decide) (by decide) (by decide)
  · exact nativeTraceData_om_maximizer 1 (by decide)
  · exact nativeTraceData_om_maximizer 2 (by decide)
  · exact nativeTraceData_om_maximizer 3 (by decide)

private theorem fixedS_overlap_eval (i j : Fin 4) (hij : i ≠ j) :
    (nativeTraceData fixedS).o i j =
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then (1 / 2 : ℝ) else 1 / 3 := by
  rw [nativeTraceData_o]
  change nativeOverlaps fixedS i j = _
  rw [nativeOverlaps_fixedS_eq]
  simp [hij]

private theorem fixedS_triangle_eval (i j k : Fin 4) :
    (nativeTraceData fixedS).R i j k = fixedSTriangleVal i j k := by
  rw [nativeTraceData_R]
  change fpTriangle fixedS i j k = _
  rw [fpTriangle_eq_nativeTriangles, nativeTriangles_fixedS_eq]

theorem isTracesS_fixedS : IsTracesS (nativeTraceData fixedS) := by
  apply isTracesS_of
  · simpa using fixedS_overlap_eval 0 1 (by decide)
  · simpa using fixedS_overlap_eval 0 2 (by decide)
  · simpa using fixedS_overlap_eval 0 3 (by decide)
  · simpa using fixedS_overlap_eval 1 2 (by decide)
  · simpa using fixedS_overlap_eval 1 3 (by decide)
  · simpa using fixedS_overlap_eval 2 3 (by decide)
  · rw [fixedS_triangle_eval]; simp [fixedSTriangleVal]
  · rw [fixedS_triangle_eval]; simp [fixedSTriangleVal]
  · rw [fixedS_triangle_eval]; simp [fixedSTriangleVal]
  · rw [fixedS_triangle_eval]; simp [fixedSTriangleVal]
  · exact nativeTraceData_om_fixedS 1 (by decide)
  · exact nativeTraceData_om_fixedS 2 (by decide)
  · exact nativeTraceData_om_fixedS 3 (by decide)

theorem tableS_holds_fixedS : tableS.Holds (nativeTraceData fixedS) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [tableS] <;> push_cast
  · simpa using fixedS_overlap_eval 0 1 (by decide)
  · simpa using fixedS_overlap_eval 0 2 (by decide)
  · simpa using fixedS_overlap_eval 0 3 (by decide)
  · simpa using fixedS_overlap_eval 1 2 (by decide)
  · simpa using fixedS_overlap_eval 1 3 (by decide)
  · simpa using fixedS_overlap_eval 2 3 (by decide)
  · rw [fixedS_triangle_eval]; simp [fixedSTriangleVal]
  · rw [fixedS_triangle_eval]; simp [fixedSTriangleVal]
  · rw [fixedS_triangle_eval]; simp [fixedSTriangleVal]
  · rw [fixedS_triangle_eval]; simp [fixedSTriangleVal]
  · exact nativeTraceData_om_fixedS 1 (by decide)
  · exact nativeTraceData_om_fixedS 2 (by decide)
  · exact nativeTraceData_om_fixedS 3 (by decide)

/-! ## Section 2: `thm:cer:seven(a)` via Explicit Certificate Vectors `certM` and `certS` -/

private theorem seven_pA_algebraic_of_traces
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    {p : Fin 4 → Albert} (hp : ∀ i, IsAtom (p i))
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hnot : ∀ W : WalkForm A,
      TableValues (nativeTraceData p) (nativeWordProbability p (p 0)) →
      ¬ W.Reproduces wordsE3 (nativeWordProbability p (p 0)))
    (hM : ∀ u : Word (Fin 4), u.length ≤ 6 → M.probability u = nativeWordProbability p (p 0) u) :
    False := by
  have h1 : M.probability [(0, true)] = 1 := by
    rw [hM _ (by simp), val_one p hp 0 0]
    exact tracePairing_atom_self (p 0) (hp 0)
  have h : 0 < M.probability [(0, true)] := by rw [h1]; norm_num
  have hrep : (WalkForm.ofAlgebraic M h).Reproduces wordsE3 (nativeWordProbability p (p 0)) :=
    WalkForm.ofAlgebraic_reproduces M h _ _ fun u hu => by
      rw [Uniform.probability_cons_yesA_of_certain M h1 u, h1, div_one]
      exact hM u hu
  exact hnot (WalkForm.ofAlgebraic M h) (tableValues_native p hp) hrep

/-- `thm:cer:seven(a)` for `M` from `e/3`, algebraic class, proved via `certM`. -/
theorem seven_M_e3_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w) :
    False := by
  obtain ⟨h, hrep, hT⟩ := lemmaA_e3_inputs M maximizerConfig maximizerConfig_isAtom hM
  exact seven_M isTracesM_maximizerConfig hT hrep

/-- `thm:cer:seven(a)` for `M` from `e/3`, real or complex Hilbert spaces, via `certM`. -/
theorem seven_M_e3_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) 𝕜 H)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w) :
    False :=
  seven_M_e3_algebraic M.toAlgebraic fun w hw h0 => by
    rw [M.toAlgebraic_probability]; exact hM w hw h0

/-- `thm:cer:seven(a)` for `M` from `e/3`, quaternionic models, via `certM`. -/
theorem seven_M_e3_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 4) Q)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
      M.state (M.wordEffect w) =
        nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w) :
    False :=
  seven_M_e3_algebraic M.toAlgebraic fun w hw h0 => by
    rw [M.toAlgebraic_probability]; exact hM w hw h0

/-- `thm:cer:seven(a)` for `M` from `p_A`, algebraic class, proved via `certM`. -/
theorem seven_M_pA_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hM : ∀ u : Word (Fin 4), u.length ≤ 6 →
      M.probability u = nativeWordProbability maximizerConfig (maximizerConfig 0) u) :
    False :=
  seven_pA_algebraic_of_traces maximizerConfig_isAtom M
    (fun _ hT => seven_M isTracesM_maximizerConfig hT) hM

/-- `thm:cer:seven(a)` for `M` from `p_A`, real or complex Hilbert spaces, via `certM`. -/
theorem seven_M_pA_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) 𝕜 H)
    (hM : ∀ u : Word (Fin 4), u.length ≤ 6 →
      M.probability u = nativeWordProbability maximizerConfig (maximizerConfig 0) u) :
    False :=
  seven_M_pA_algebraic M.toAlgebraic fun u hu => by
    rw [M.toAlgebraic_probability]; exact hM u hu

/-- `thm:cer:seven(a)` for `M` from `p_A`, quaternionic models, via `certM`. -/
theorem seven_M_pA_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 4) Q)
    (hM : ∀ u : Word (Fin 4), u.length ≤ 6 →
      M.state (M.wordEffect u) =
        nativeWordProbability maximizerConfig (maximizerConfig 0) u) :
    False :=
  seven_M_pA_algebraic M.toAlgebraic fun u hu => by
    rw [M.toAlgebraic_probability]; exact hM u hu

/-- `thm:cer:seven(a)` for `S` from `e/3`, algebraic class, proved via `certS`. -/
theorem seven_S_e3_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w) :
    False := by
  obtain ⟨h, hrep, hT⟩ := lemmaA_e3_inputs M fixedS fixedS_isAtom hM
  exact seven_S isTracesS_fixedS hT hrep

/-- `thm:cer:seven(a)` for `S` from `e/3`, real or complex Hilbert spaces, via `certS`. -/
theorem seven_S_e3_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) 𝕜 H)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w) :
    False :=
  seven_S_e3_algebraic M.toAlgebraic fun w hw h0 => by
    rw [M.toAlgebraic_probability]; exact hM w hw h0

/-- `thm:cer:seven(a)` for `S` from `e/3`, quaternionic models, via `certS`. -/
theorem seven_S_e3_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 4) Q)
    (hM : ∀ w : Word (Fin 4), w.length ≤ 7 → w.head? = some (0, true) →
      M.state (M.wordEffect w) =
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w) :
    False :=
  seven_S_e3_algebraic M.toAlgebraic fun w hw h0 => by
    rw [M.toAlgebraic_probability]; exact hM w hw h0

/-- `thm:cer:seven(a)` for `S` from `p_A`, algebraic class, proved via `certS`. -/
theorem seven_S_pA_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hM : ∀ u : Word (Fin 4), u.length ≤ 6 →
      M.probability u = nativeWordProbability fixedS (fixedS 0) u) :
    False :=
  seven_pA_algebraic_of_traces fixedS_isAtom M
    (fun _ hT => seven_S isTracesS_fixedS hT) hM

/-- `thm:cer:seven(a)` for `S` from `p_A`, real or complex Hilbert spaces, via `certS`. -/
theorem seven_S_pA_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) 𝕜 H)
    (hM : ∀ u : Word (Fin 4), u.length ≤ 6 →
      M.probability u = nativeWordProbability fixedS (fixedS 0) u) :
    False :=
  seven_S_pA_algebraic M.toAlgebraic fun u hu => by
    rw [M.toAlgebraic_probability]; exact hM u hu

/-- `thm:cer:seven(a)` for `S` from `p_A`, quaternionic models, via `certS`. -/
theorem seven_S_pA_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 4) Q)
    (hM : ∀ u : Word (Fin 4), u.length ≤ 6 →
      M.state (M.wordEffect u) =
        nativeWordProbability fixedS (fixedS 0) u) :
    False :=
  seven_S_pA_algebraic M.toAlgebraic fun u hu => by
    rw [M.toAlgebraic_probability]; exact hM u hu

/-! ## Section 3: Parametric Lift of `lam2` to `FiniteRealWordFunctional 4` on `e/3` Words -/

/-- Normalize a `p_A`-side word to an `A`-yes initial `e/3` word by merging any leading `(0, true)`. -/
def addYesA (w : Word (Fin 4)) : Word (Fin 4) := (0, true) :: dropYesA w

/-- Boolean check for `IsReducedWord`. -/
def isReducedBool : Word (Fin 4) → Bool
  | [] => true
  | [_] => true
  | a :: b :: w => decide (a.1 ≠ b.1) && isReducedBool (b :: w)

private theorem isReducedBool_iff : ∀ w : Word (Fin 4), isReducedBool w = true ↔ IsReducedWord w
  | [] => by simp [isReducedBool, IsReducedWord]
  | [_] => by simp [isReducedBool, IsReducedWord]
  | a :: b :: w => by
    simp only [isReducedBool, IsReducedWord, Bool.and_eq_true, decide_eq_true_eq]
    exact and_congr Iff.rfl (isReducedBool_iff (b :: w))

/-- Word-only structural check for an `Entry` (touches no rationals or `epsQ`). -/
def wordOk (w : Word (Fin 4)) : Bool :=
  decide ((dropYesA w).length ≤ 6) && isReducedBool (addYesA w)

def entryWordsOk (e : Entry) : Bool :=
  e.tabs.all (fun m => wordOk m.2.toWord) &&
  e.defs.all (fun d =>
    wordOk (yesWord d.α) && wordOk d.long && wordOk d.mid && wordOk d.short)

private theorem lam2_wordsOk (T : TraceTable) (θ : ℚ) (pairs : List (ℚ × Entry))
    (hok : pairs.all (fun p => entryWordsOk p.2) = true) :
    ∀ m ∈ lam2 T θ pairs, (dropYesA m.2).length ≤ 6 ∧ IsReducedWord (addYesA m.2) := by
  have hspec : ∀ w : Word (Fin 4), wordOk w = true →
      (dropYesA w).length ≤ 6 ∧ IsReducedWord (addYesA w) := by
    intro w hw
    simp only [wordOk, Bool.and_eq_true, decide_eq_true_eq, isReducedBool_iff] at hw
    exact hw
  intro m hm
  unfold lam2 at hm
  rw [List.mem_flatMap] at hm
  obtain ⟨p, hp, hm⟩ := hm
  have hpe := List.all_eq_true.mp hok p hp
  simp only [entryWordsOk, Bool.and_eq_true] at hpe
  obtain ⟨htabs, hdefs⟩ := hpe
  unfold entryTerms at hm
  rw [List.mem_append] at hm
  rcases hm with htab | hdef
  · rw [List.mem_map] at htab
    obtain ⟨t, ht, rfl⟩ := htab
    exact hspec t.2.toWord (List.all_eq_true.mp htabs t ht)
  · rw [List.mem_flatMap] at hdef
    obtain ⟨d, hd, hm⟩ := hdef
    have hde := List.all_eq_true.mp hdefs d hd
    simp only [Bool.and_eq_true] at hde
    obtain ⟨⟨⟨hα, hlong⟩, hmid⟩, hshort⟩ := hde
    simp only [defTerms, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact hspec _ hα
    · exact hspec _ hlong
    · exact hspec _ hmid
    · exact hspec _ hshort

/-- Lift a rational word functional from `p_A` (`lam2`) to an `e/3` `FiniteRealWordFunctional 4`. -/
def toE3Functional (L : List (ℚ × Word Letter)) : FiniteRealWordFunctional 4 where
  terms := L.map fun m => ((m.1 : ℝ), addYesA m.2)

private theorem toE3Functional_terms_rational (L : List (ℚ × Word Letter)) :
    ∀ t ∈ (toE3Functional L).terms, ∃ q : ℚ, t.1 = (q : ℝ) := by
  intro t ht
  rw [toE3Functional, List.mem_map] at ht
  obtain ⟨m, -, rfl⟩ := ht
  exact ⟨m.1, rfl⟩

private theorem toE3Functional_coefficients_rational (L : List (ℚ × Word Letter)) (w : Word (Fin 4)) :
    ∃ q : ℚ, (toE3Functional L).coefficients w = (q : ℝ) := by
  refine ⟨(L.map fun m => if addYesA m.2 = w then m.1 else 0).sum, ?_⟩
  change FiniteRealWordFunctional.coefficientsOfTerms (toE3Functional L).terms w = _
  induction L with
  | nil => simp [toE3Functional, FiniteRealWordFunctional.coefficientsOfTerms_nil]
  | cons m L ih =>
    simp only [toE3Functional, List.map_cons, List.sum_cons,
      FiniteRealWordFunctional.coefficientsOfTerms_cons, Finsupp.add_apply] at ih ⊢
    rw [ih]
    by_cases h : addYesA m.2 = w
    · subst h
      simp [Finsupp.single_eq_same]
    · simp only [h, ↓reduceIte, Finsupp.single_eq_of_ne (Ne.symm h), zero_add]

private theorem toE3Functional_support_spec (L : List (ℚ × Word Letter))
    (hL : ∀ m ∈ L, (dropYesA m.2).length ≤ 6 ∧ IsReducedWord (addYesA m.2)) :
    (∀ t ∈ (toE3Functional L).terms,
      t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
    (∀ w ∈ (toE3Functional L).coefficients.support,
      w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) := by
  have hterms : ∀ t ∈ (toE3Functional L).terms,
      t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2 := by
    intro t ht
    rw [toE3Functional, List.mem_map] at ht
    obtain ⟨m, hm, rfl⟩ := ht
    obtain ⟨hlen, hred⟩ := hL m hm
    exact ⟨Nat.succ_le_succ hlen, rfl, hred⟩
  refine ⟨hterms, fun w hw => ?_⟩
  by_contra hbad
  have hzero : (toE3Functional L).coefficients w = 0 := by
    apply FiniteRealWordFunctional.coefficientsOfTerms_apply_eq_zero_of_absent
    intro t ht heq
    exact hbad (heq ▸ hterms t ht)
  exact (Finsupp.mem_support_iff.mp hw) hzero

private theorem toE3Functional_coefficientNorm_le (L : List (ℚ × Word Letter)) :
    (toE3Functional L).coefficientNorm ≤ (l1 L : ℝ) := by
  refine (toE3Functional L).coefficientNorm_le_rawCoefficientBound.trans_eq ?_
  change wordAmplitudeCoefficientBound (toE3Functional L).terms = (l1 L : ℝ)
  induction L with
  | nil => simp [toE3Functional, wordAmplitudeCoefficientBound_nil, l1]
  | cons m L ih =>
    simp only [toE3Functional, List.map_cons, wordAmplitudeCoefficientBound_cons, l1,
      List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_abs] at ih ⊢
    rw [ih]

private theorem toE3Functional_evaluate_algebraic_eq
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) (h : 0 < M.probability [(0, true)])
    (L : List (ℚ × Word Letter)) :
    (toE3Functional L).evaluate M.probability =
      M.probability [(0, true)] *
        evalF (fun w => (WalkForm.ofAlgebraic M h).normSq ((WalkForm.ofAlgebraic M h).vec w)) L := by
  induction L with
  | nil => simp [toE3Functional, FiniteRealWordFunctional.evaluate, evalF]
  | cons m L ih =>
    have hns := WalkForm.ofAlgebraic_normSq_vec M h (dropYesA m.2)
    rw [WalkForm.normSq_vec_dropYesA] at hns
    have hterm : M.probability (addYesA m.2) =
        M.probability [(0, true)] *
          (WalkForm.ofAlgebraic M h).normSq ((WalkForm.ofAlgebraic M h).vec m.2) := by
      have hdiv : M.probability (addYesA m.2) / M.probability [(0, true)] =
          (WalkForm.ofAlgebraic M h).normSq ((WalkForm.ofAlgebraic M h).vec m.2) := hns.symm
      rw [div_eq_iff h.ne'] at hdiv
      rw [hdiv, mul_comm]
    simp only [toE3Functional, FiniteRealWordFunctional.evaluate, evalF,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, hterm]
    ring

private theorem toE3Functional_evaluate_algebraic_eq_zero
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) (h0 : M.probability [(0, true)] = 0)
    (L : List (ℚ × Word Letter)) :
    (toE3Functional L).evaluate M.probability = 0 := by
  induction L with
  | nil => simp [toE3Functional, FiniteRealWordFunctional.evaluate]
  | cons m L ih =>
    have hm0 : M.probability (addYesA m.2) = 0 :=
      M.probability_append_eq_zero [(0, true)] (dropYesA m.2) h0
    simp only [toE3Functional, FiniteRealWordFunctional.evaluate,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [hm0, mul_zero, zero_add, ih]

private theorem toE3Functional_nonneg_algebraic
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) (L : List (ℚ × Word Letter))
    (hnonneg : ∀ h : 0 < M.probability [(0, true)],
      0 ≤ evalF (fun w => (WalkForm.ofAlgebraic M h).normSq ((WalkForm.ofAlgebraic M h).vec w)) L) :
    0 ≤ (toE3Functional L).evaluate M.probability := by
  by_cases h : 0 < M.probability [(0, true)]
  · rw [toE3Functional_evaluate_algebraic_eq M h L]
    exact mul_nonneg h.le (hnonneg h)
  · have h0 : M.probability [(0, true)] = 0 :=
      le_antisymm (not_lt.mp h) (M.probability_nonneg _)
    rw [toE3Functional_evaluate_algebraic_eq_zero M h0 L]

private theorem toE3Functional_evaluate_native_e3
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (L : List (ℚ × Word Letter)) :
    (toE3Functional L).evaluate (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) =
      (1 / 3 : ℝ) * evalF (nativeWordProbability p (p 0)) L := by
  have hT := tableValues_native p hp
  induction L with
  | nil => simp [toE3Functional, FiniteRealWordFunctional.evaluate, evalF]
  | cons m L ih =>
    have hval : nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (addYesA m.2) =
        (1 / 3 : ℝ) * nativeWordProbability p (p 0) m.2 := by
      change nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) ((0, true) :: dropYesA m.2) = _
      rw [e3_conditioning p hp (dropYesA m.2), hT.f_dropYesA m.2]
    simp only [toE3Functional, FiniteRealWordFunctional.evaluate, evalF,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, hval]
    ring

private theorem margin_of_functional
    (c : FiniteRealWordFunctional 4) (f g : Word (Fin 4) → ℝ) (γ B : ℝ)
    (hpos : 0 < γ) (hc : c.coefficientNorm ≤ B)
    (hmodel : 0 ≤ c.evaluate f) (htarget : c.evaluate g = -γ) (δ : ℝ)
    (hδ : ∀ w ∈ c.coefficients.support, |f w - g w| ≤ δ) :
    γ ≤ c.coefficientNorm * δ ∧ (∀ m_low : ℝ, m_low * B < γ → m_low < δ) := by
  have hne : c.coefficients.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hc0 : c.coefficients = 0 := Finsupp.support_eq_empty.mp hemp
    have hz : c.evaluate g = 0 := by rw [c.evaluate_eq_coefficients, hc0, Finsupp.sum_zero_index]
    linarith
  obtain ⟨w₀, hw₀⟩ := hne
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ w₀ hw₀)
  have hsep : γ ≤ c.coefficientNorm * δ :=
    c.separation_forces_error f g δ γ hδ0 hδ hmodel (by linarith)
  refine ⟨hsep, fun m_low hm => ?_⟩
  have hB : γ ≤ B * δ := hsep.trans (mul_le_mul_of_nonneg_right hc hδ0)
  have hB0 : 0 ≤ B := c.coefficientNorm_nonneg.trans hc
  by_contra hle
  have hmul : B * δ ≤ B * m_low := mul_le_mul_of_nonneg_left (not_lt.mp hle) hB0
  linarith

/-! ## Section 4: Unconditional `thm:cer:seven(b)` and `prop:robust(a)` for `M` and `S` -/

private theorem pairsM1_wordsOk : pairsM1.all (fun p => entryWordsOk p.2) = true := by decide
private theorem pairsM2_wordsOk : pairsM2.all (fun p => entryWordsOk p.2) = true := by decide
private theorem pairsM3_wordsOk : pairsM3.all (fun p => entryWordsOk p.2) = true := by decide
private theorem pairsM4_wordsOk : pairsM4.all (fun p => entryWordsOk p.2) = true := by decide

private theorem pairsM_wordsOk : pairsM.all (fun p => entryWordsOk p.2) = true := by
  simp only [pairsM, List.all_append, pairsM1_wordsOk, pairsM2_wordsOk,
    pairsM3_wordsOk, pairsM4_wordsOk, Bool.and_self]

private theorem pairsS1_wordsOk : pairsS1.all (fun p => entryWordsOk p.2) = true := by decide
private theorem pairsS2_wordsOk : pairsS2.all (fun p => entryWordsOk p.2) = true := by decide
private theorem pairsS3_wordsOk : pairsS3.all (fun p => entryWordsOk p.2) = true := by decide
private theorem pairsS4_wordsOk : pairsS4.all (fun p => entryWordsOk p.2) = true := by decide

private theorem pairsS_wordsOk : pairsS.all (fun p => entryWordsOk p.2) = true := by
  simp only [pairsS, List.all_append, pairsS1_wordsOk, pairsS2_wordsOk,
    pairsS3_wordsOk, pairsS4_wordsOk, Bool.and_self]

/-- Explicit robust separator functional `Λ_M` (`thm:cer:seven(b)`) on `e/3` words of length `≤ 7`
beginning with `(0, true)`. -/
def robustFunctionalM : FiniteRealWordFunctional 4 :=
  toE3Functional (lam2 tableM thetaM pairsM)

/-- Explicit robust separator functional `Λ_S` (`thm:cer:seven(b)`) on `e/3` words of length `≤ 7`
beginning with `(0, true)`. -/
def robustFunctionalS : FiniteRealWordFunctional 4 :=
  toE3Functional (lam2 tableS thetaS pairsS)

theorem robustFunctionalM_rational :
    ∀ t ∈ robustFunctionalM.terms, ∃ q : ℚ, t.1 = (q : ℝ) :=
  toE3Functional_terms_rational _

theorem robustFunctionalM_coefficients_rational (w : Word (Fin 4)) :
    ∃ q : ℚ, robustFunctionalM.coefficients w = (q : ℝ) :=
  toE3Functional_coefficients_rational _ w

theorem robustFunctionalM_support :
    (∀ t ∈ robustFunctionalM.terms,
      t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
    (∀ w ∈ robustFunctionalM.coefficients.support,
      w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) :=
  toE3Functional_support_spec _ (lam2_wordsOk tableM thetaM pairsM pairsM_wordsOk)

theorem robustFunctionalM_hasHorizon : robustFunctionalM.HasHorizon 7 :=
  fun t ht => (robustFunctionalM_support.1 t ht).1

theorem robustFunctionalM_eval_e3 :
    robustFunctionalM.evaluate
        (nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit)) =
      -(4588961 / 169869312 : ℝ) := by
  rw [robustFunctionalM, toE3Functional_evaluate_native_e3 maximizerConfig maximizerConfig_isAtom,
    lam2_oct_M tableM_holds_maximizerConfig
      (tableValues_native maximizerConfig maximizerConfig_isAtom)]
  ring

theorem robustFunctionalM_coefficientNorm_le :
    robustFunctionalM.coefficientNorm ≤ 4470 * 10 ^ 6 := by
  refine (toE3Functional_coefficientNorm_le _).trans ?_
  exact_mod_cast l1_M

theorem robustFunctionalM_coefficientNorm_le_paper :
    robustFunctionalM.coefficientNorm ≤ 5268 * 10 ^ 6 :=
  robustFunctionalM_coefficientNorm_le.trans (by norm_num)

theorem robustFunctionalM_nonneg_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) :
    0 ≤ robustFunctionalM.evaluate M.probability :=
  toE3Functional_nonneg_algebraic M _ fun h => lam2_nonneg_M (WalkForm.ofAlgebraic M h)

theorem robustFunctionalM_nonneg_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) 𝕜 H) :
    0 ≤ robustFunctionalM.evaluate M.probability := by
  have h := robustFunctionalM_nonneg_algebraic M.toAlgebraic
  simpa only [FiniteRealWordFunctional.evaluate, M.toAlgebraic_probability] using h

theorem robustFunctionalM_nonneg_quaternionic {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 4) Q) :
    0 ≤ robustFunctionalM.evaluate (fun w => M.state (M.wordEffect w)) := by
  have h := robustFunctionalM_nonneg_algebraic M.toAlgebraic
  simpa only [FiniteRealWordFunctional.evaluate, M.toAlgebraic_probability] using h

theorem robust_M_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) (δ : ℝ)
    (hδ : ∀ w ∈ robustFunctionalM.coefficients.support,
      |M.probability w - nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) :
    (4588961 / 169869312 : ℝ) ≤ robustFunctionalM.coefficientNorm * δ ∧
      (51 / 10 ^ 13 : ℝ) < δ ∧ (6 / 10 ^ 12 : ℝ) < δ := by
  obtain ⟨hsep, hm⟩ := margin_of_functional robustFunctionalM M.probability
    (nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit))
    (4588961 / 169869312) (4470 * 10 ^ 6) (by norm_num)
    robustFunctionalM_coefficientNorm_le (robustFunctionalM_nonneg_algebraic M)
    robustFunctionalM_eval_e3 δ hδ
  refine ⟨hsep, hm (51 / 10 ^ 13) (by norm_num), hm (6 / 10 ^ 12) (by norm_num)⟩

theorem robust_M_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) 𝕜 H) (δ : ℝ)
    (hδ : ∀ w ∈ robustFunctionalM.coefficients.support,
      |M.probability w - nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) :
    (4588961 / 169869312 : ℝ) ≤ robustFunctionalM.coefficientNorm * δ ∧
      (51 / 10 ^ 13 : ℝ) < δ ∧ (6 / 10 ^ 12 : ℝ) < δ :=
  robust_M_algebraic M.toAlgebraic δ fun w hw => by
    rw [M.toAlgebraic_probability]; exact hδ w hw

theorem robust_M_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 4) Q) (δ : ℝ)
    (hδ : ∀ w ∈ robustFunctionalM.coefficients.support,
      |M.state (M.wordEffect w) -
        nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) :
    (4588961 / 169869312 : ℝ) ≤ robustFunctionalM.coefficientNorm * δ ∧
      (51 / 10 ^ 13 : ℝ) < δ ∧ (6 / 10 ^ 12 : ℝ) < δ :=
  robust_M_algebraic M.toAlgebraic δ fun w hw => by
    rw [M.toAlgebraic_probability]; exact hδ w hw

theorem robustFunctionalS_rational :
    ∀ t ∈ robustFunctionalS.terms, ∃ q : ℚ, t.1 = (q : ℝ) :=
  toE3Functional_terms_rational _

theorem robustFunctionalS_coefficients_rational (w : Word (Fin 4)) :
    ∃ q : ℚ, robustFunctionalS.coefficients w = (q : ℝ) :=
  toE3Functional_coefficients_rational _ w

theorem robustFunctionalS_support :
    (∀ t ∈ robustFunctionalS.terms,
      t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
    (∀ w ∈ robustFunctionalS.coefficients.support,
      w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) :=
  toE3Functional_support_spec _ (lam2_wordsOk tableS thetaS pairsS pairsS_wordsOk)

theorem robustFunctionalS_hasHorizon : robustFunctionalS.HasHorizon 7 :=
  fun t ht => (robustFunctionalS_support.1 t ht).1

theorem robustFunctionalS_eval_e3 :
    robustFunctionalS.evaluate
        (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) =
      -(412734271 / 18345885696 : ℝ) := by
  rw [robustFunctionalS, toE3Functional_evaluate_native_e3 fixedS fixedS_isAtom,
    lam2_oct_S tableS_holds_fixedS (tableValues_native fixedS fixedS_isAtom)]
  ring

theorem robustFunctionalS_coefficientNorm_le :
    robustFunctionalS.coefficientNorm ≤ 19519 * 10 ^ 6 := by
  refine (toE3Functional_coefficientNorm_le _).trans ?_
  exact_mod_cast l1_S

theorem robustFunctionalS_coefficientNorm_le_paper :
    robustFunctionalS.coefficientNorm ≤ 2892 * 10 ^ 7 :=
  robustFunctionalS_coefficientNorm_le.trans (by norm_num)

theorem robustFunctionalS_nonneg_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) :
    0 ≤ robustFunctionalS.evaluate M.probability :=
  toE3Functional_nonneg_algebraic M _ fun h => lam2_nonneg_S (WalkForm.ofAlgebraic M h)

theorem robustFunctionalS_nonneg_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) 𝕜 H) :
    0 ≤ robustFunctionalS.evaluate M.probability := by
  have h := robustFunctionalS_nonneg_algebraic M.toAlgebraic
  simpa only [FiniteRealWordFunctional.evaluate, M.toAlgebraic_probability] using h

theorem robustFunctionalS_nonneg_quaternionic {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 4) Q) :
    0 ≤ robustFunctionalS.evaluate (fun w => M.state (M.wordEffect w)) := by
  have h := robustFunctionalS_nonneg_algebraic M.toAlgebraic
  simpa only [FiniteRealWordFunctional.evaluate, M.toAlgebraic_probability] using h

theorem robust_S_algebraic {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) (δ : ℝ)
    (hδ : ∀ w ∈ robustFunctionalS.coefficients.support,
      |M.probability w - nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) :
    (412734271 / 18345885696 : ℝ) ≤ robustFunctionalS.coefficientNorm * δ ∧
      (77 / 10 ^ 14 : ℝ) < δ ∧ (115 / 10 ^ 14 : ℝ) < δ := by
  obtain ⟨hsep, hm⟩ := margin_of_functional robustFunctionalS M.probability
    (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit))
    (412734271 / 18345885696) (19519 * 10 ^ 6) (by norm_num)
    robustFunctionalS_coefficientNorm_le (robustFunctionalS_nonneg_algebraic M)
    robustFunctionalS_eval_e3 δ hδ
  refine ⟨hsep, hm (77 / 10 ^ 14) (by norm_num), hm (115 / 10 ^ 14) (by norm_num)⟩

theorem robust_S_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) 𝕜 H) (δ : ℝ)
    (hδ : ∀ w ∈ robustFunctionalS.coefficients.support,
      |M.probability w - nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) :
    (412734271 / 18345885696 : ℝ) ≤ robustFunctionalS.coefficientNorm * δ ∧
      (77 / 10 ^ 14 : ℝ) < δ ∧ (115 / 10 ^ 14 : ℝ) < δ :=
  robust_S_algebraic M.toAlgebraic δ fun w hw => by
    rw [M.toAlgebraic_probability]; exact hδ w hw

theorem robust_S_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 4) Q) (δ : ℝ)
    (hδ : ∀ w ∈ robustFunctionalS.coefficients.support,
      |M.state (M.wordEffect w) -
        nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) :
    (412734271 / 18345885696 : ℝ) ≤ robustFunctionalS.coefficientNorm * δ ∧
      (77 / 10 ^ 14 : ℝ) < δ ∧ (115 / 10 ^ 14 : ℝ) < δ :=
  robust_S_algebraic M.toAlgebraic δ fun w hw => by
    rw [M.toAlgebraic_probability]; exact hδ w hw

/-! ## Section 5: Bundled Challenge Statements for `thm:cer:seven(b)` -/

/-- `thm:cer:seven(b)` + `prop:robust(a)` for `M`, algebraic comparator class (`Type u`). -/
theorem thm_cer_seven_b_M_algebraic.{u} :
    ∃ Λ : FiniteRealWordFunctional 4,
      (∀ t ∈ Λ.terms, (∃ q : ℚ, t.1 = (q : ℝ)) ∧
        t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
      (∀ w ∈ Λ.coefficients.support,
        w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) ∧
      Λ.evaluate (nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit)) =
        -(4588961 / 169869312 : ℝ) ∧
      Λ.coefficientNorm ≤ 5268 * 10 ^ 6 ∧
      Λ.coefficientNorm ≤ 4470 * 10 ^ 6 ∧
      (∀ (A : Type u) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin 4) A),
        0 ≤ Λ.evaluate M.probability) ∧
      (∀ (A : Type u) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin 4) A) (δ : ℝ),
        (∀ w ∈ Λ.coefficients.support,
          |M.probability w - nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) →
        (4588961 / 169869312 : ℝ) ≤ Λ.coefficientNorm * δ ∧
          (51 / 10 ^ 13 : ℝ) < δ ∧ (6 / 10 ^ 12 : ℝ) < δ) :=
  ⟨robustFunctionalM,
    fun t ht => ⟨robustFunctionalM_rational t ht, robustFunctionalM_support.1 t ht⟩,
    robustFunctionalM_support.2,
    robustFunctionalM_eval_e3,
    robustFunctionalM_coefficientNorm_le_paper,
    robustFunctionalM_coefficientNorm_le,
    fun _ _ _ _ _ _ _ M => robustFunctionalM_nonneg_algebraic M,
    fun _ _ _ _ _ _ _ M δ hδ => robust_M_algebraic M δ hδ⟩

/-- `thm:cer:seven(b)` + `prop:robust(a)` for `M`, real and complex Hilbert spaces (`[RCLike 𝕜]`). -/
theorem thm_cer_seven_b_M_hilbert.{u, v} :
    ∃ Λ : FiniteRealWordFunctional 4,
      (∀ t ∈ Λ.terms, (∃ q : ℚ, t.1 = (q : ℝ)) ∧
        t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
      (∀ w ∈ Λ.coefficients.support,
        w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) ∧
      Λ.evaluate (nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit)) =
        -(4588961 / 169869312 : ℝ) ∧
      Λ.coefficientNorm ≤ 5268 * 10 ^ 6 ∧
      Λ.coefficientNorm ≤ 4470 * 10 ^ 6 ∧
      (∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData (Fin 4) 𝕜 H),
        0 ≤ Λ.evaluate M.probability) ∧
      (∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData (Fin 4) 𝕜 H) (δ : ℝ),
        (∀ w ∈ Λ.coefficients.support,
          |M.probability w - nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) →
        (4588961 / 169869312 : ℝ) ≤ Λ.coefficientNorm * δ ∧
          (51 / 10 ^ 13 : ℝ) < δ ∧ (6 / 10 ^ 12 : ℝ) < δ) :=
  ⟨robustFunctionalM,
    fun t ht => ⟨robustFunctionalM_rational t ht, robustFunctionalM_support.1 t ht⟩,
    robustFunctionalM_support.2,
    robustFunctionalM_eval_e3,
    robustFunctionalM_coefficientNorm_le_paper,
    robustFunctionalM_coefficientNorm_le,
    fun _ _ _ _ _ _ M => robustFunctionalM_nonneg_hilbert M,
    fun _ _ _ _ _ _ M δ hδ => robust_M_hilbert M δ hδ⟩

/-- `thm:cer:seven(b)` + `prop:robust(a)` for `M`, quaternionic models. -/
theorem thm_cer_seven_b_M_quaternionic.{u} :
    ∃ Λ : FiniteRealWordFunctional 4,
      (∀ t ∈ Λ.terms, (∃ q : ℚ, t.1 = (q : ℝ)) ∧
        t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
      (∀ w ∈ Λ.coefficients.support,
        w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) ∧
      Λ.evaluate (nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit)) =
        -(4588961 / 169869312 : ℝ) ∧
      Λ.coefficientNorm ≤ 5268 * 10 ^ 6 ∧
      Λ.coefficientNorm ≤ 4470 * 10 ^ 6 ∧
      (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData (Fin 4) Q),
        0 ≤ Λ.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData (Fin 4) Q) (δ : ℝ),
        (∀ w ∈ Λ.coefficients.support,
          |M.state (M.wordEffect w) -
            nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) →
        (4588961 / 169869312 : ℝ) ≤ Λ.coefficientNorm * δ ∧
          (51 / 10 ^ 13 : ℝ) < δ ∧ (6 / 10 ^ 12 : ℝ) < δ) :=
  ⟨robustFunctionalM,
    fun t ht => ⟨robustFunctionalM_rational t ht, robustFunctionalM_support.1 t ht⟩,
    robustFunctionalM_support.2,
    robustFunctionalM_eval_e3,
    robustFunctionalM_coefficientNorm_le_paper,
    robustFunctionalM_coefficientNorm_le,
    fun _ _ _ _ _ M => robustFunctionalM_nonneg_quaternionic M,
    fun _ _ _ _ _ M δ hδ => robust_M_quaternionic M δ hδ⟩

/-- `thm:cer:seven(b)` + `prop:robust(a)` for `S`, algebraic comparator class (`Type u`). -/
theorem thm_cer_seven_b_S_algebraic.{u} :
    ∃ Λ : FiniteRealWordFunctional 4,
      (∀ t ∈ Λ.terms, (∃ q : ℚ, t.1 = (q : ℝ)) ∧
        t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
      (∀ w ∈ Λ.coefficients.support,
        w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) ∧
      Λ.evaluate (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) =
        -(412734271 / 18345885696 : ℝ) ∧
      Λ.coefficientNorm ≤ 2892 * 10 ^ 7 ∧
      Λ.coefficientNorm ≤ 19519 * 10 ^ 6 ∧
      (∀ (A : Type u) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin 4) A),
        0 ≤ Λ.evaluate M.probability) ∧
      (∀ (A : Type u) [Ring A] [StarRing A] [Module ℝ A]
        [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
        (M : AlgebraicProjectiveData (Fin 4) A) (δ : ℝ),
        (∀ w ∈ Λ.coefficients.support,
          |M.probability w - nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) →
        (412734271 / 18345885696 : ℝ) ≤ Λ.coefficientNorm * δ ∧
          (77 / 10 ^ 14 : ℝ) < δ ∧ (115 / 10 ^ 14 : ℝ) < δ) :=
  ⟨robustFunctionalS,
    fun t ht => ⟨robustFunctionalS_rational t ht, robustFunctionalS_support.1 t ht⟩,
    robustFunctionalS_support.2,
    robustFunctionalS_eval_e3,
    robustFunctionalS_coefficientNorm_le_paper,
    robustFunctionalS_coefficientNorm_le,
    fun _ _ _ _ _ _ _ M => robustFunctionalS_nonneg_algebraic M,
    fun _ _ _ _ _ _ _ M δ hδ => robust_S_algebraic M δ hδ⟩

/-- `thm:cer:seven(b)` + `prop:robust(a)` for `S`, real and complex Hilbert spaces (`[RCLike 𝕜]`). -/
theorem thm_cer_seven_b_S_hilbert.{u, v} :
    ∃ Λ : FiniteRealWordFunctional 4,
      (∀ t ∈ Λ.terms, (∃ q : ℚ, t.1 = (q : ℝ)) ∧
        t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
      (∀ w ∈ Λ.coefficients.support,
        w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) ∧
      Λ.evaluate (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) =
        -(412734271 / 18345885696 : ℝ) ∧
      Λ.coefficientNorm ≤ 2892 * 10 ^ 7 ∧
      Λ.coefficientNorm ≤ 19519 * 10 ^ 6 ∧
      (∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData (Fin 4) 𝕜 H),
        0 ≤ Λ.evaluate M.probability) ∧
      (∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData (Fin 4) 𝕜 H) (δ : ℝ),
        (∀ w ∈ Λ.coefficients.support,
          |M.probability w - nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) →
        (412734271 / 18345885696 : ℝ) ≤ Λ.coefficientNorm * δ ∧
          (77 / 10 ^ 14 : ℝ) < δ ∧ (115 / 10 ^ 14 : ℝ) < δ) :=
  ⟨robustFunctionalS,
    fun t ht => ⟨robustFunctionalS_rational t ht, robustFunctionalS_support.1 t ht⟩,
    robustFunctionalS_support.2,
    robustFunctionalS_eval_e3,
    robustFunctionalS_coefficientNorm_le_paper,
    robustFunctionalS_coefficientNorm_le,
    fun _ _ _ _ _ _ M => robustFunctionalS_nonneg_hilbert M,
    fun _ _ _ _ _ _ M δ hδ => robust_S_hilbert M δ hδ⟩

/-- `thm:cer:seven(b)` + `prop:robust(a)` for `S`, quaternionic models. -/
theorem thm_cer_seven_b_S_quaternionic.{u} :
    ∃ Λ : FiniteRealWordFunctional 4,
      (∀ t ∈ Λ.terms, (∃ q : ℚ, t.1 = (q : ℝ)) ∧
        t.2.length ≤ 7 ∧ t.2.head? = some (0, true) ∧ IsReducedWord t.2) ∧
      (∀ w ∈ Λ.coefficients.support,
        w.length ≤ 7 ∧ w.head? = some (0, true) ∧ IsReducedWord w) ∧
      Λ.evaluate (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) =
        -(412734271 / 18345885696 : ℝ) ∧
      Λ.coefficientNorm ≤ 2892 * 10 ^ 7 ∧
      Λ.coefficientNorm ≤ 19519 * 10 ^ 6 ∧
      (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData (Fin 4) Q),
        0 ≤ Λ.evaluate (fun w => M.state (M.wordEffect w))) ∧
      (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData (Fin 4) Q) (δ : ℝ),
        (∀ w ∈ Λ.coefficients.support,
          |M.state (M.wordEffect w) -
            nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) w| ≤ δ) →
        (412734271 / 18345885696 : ℝ) ≤ Λ.coefficientNorm * δ ∧
          (77 / 10 ^ 14 : ℝ) < δ ∧ (115 / 10 ^ 14 : ℝ) < δ) :=
  ⟨robustFunctionalS,
    fun t ht => ⟨robustFunctionalS_rational t ht, robustFunctionalS_support.1 t ht⟩,
    robustFunctionalS_support.2,
    robustFunctionalS_eval_e3,
    robustFunctionalS_coefficientNorm_le_paper,
    robustFunctionalS_coefficientNorm_le,
    fun _ _ _ _ _ M => robustFunctionalS_nonneg_quaternionic M,
    fun _ _ _ _ _ M δ hδ => robust_S_quaternionic M δ hδ⟩

#print axioms isTracesM_maximizerConfig
#print axioms tableM_holds_maximizerConfig
#print axioms isTracesS_fixedS
#print axioms tableS_holds_fixedS
#print axioms seven_M_e3_algebraic
#print axioms seven_M_e3_hilbert
#print axioms seven_M_e3_quaternionic
#print axioms seven_M_pA_algebraic
#print axioms seven_M_pA_hilbert
#print axioms seven_M_pA_quaternionic
#print axioms seven_S_e3_algebraic
#print axioms seven_S_e3_hilbert
#print axioms seven_S_e3_quaternionic
#print axioms seven_S_pA_algebraic
#print axioms seven_S_pA_hilbert
#print axioms seven_S_pA_quaternionic
#print axioms robustFunctionalM_rational
#print axioms robustFunctionalM_coefficients_rational
#print axioms robustFunctionalM_support
#print axioms robustFunctionalM_hasHorizon
#print axioms robustFunctionalM_eval_e3
#print axioms robustFunctionalM_coefficientNorm_le
#print axioms robustFunctionalM_coefficientNorm_le_paper
#print axioms robustFunctionalM_nonneg_algebraic
#print axioms robustFunctionalM_nonneg_hilbert
#print axioms robustFunctionalM_nonneg_quaternionic
#print axioms robust_M_algebraic
#print axioms robust_M_hilbert
#print axioms robust_M_quaternionic
#print axioms robustFunctionalS_rational
#print axioms robustFunctionalS_coefficients_rational
#print axioms robustFunctionalS_support
#print axioms robustFunctionalS_hasHorizon
#print axioms robustFunctionalS_eval_e3
#print axioms robustFunctionalS_coefficientNorm_le
#print axioms robustFunctionalS_coefficientNorm_le_paper
#print axioms robustFunctionalS_nonneg_algebraic
#print axioms robustFunctionalS_nonneg_hilbert
#print axioms robustFunctionalS_nonneg_quaternionic
#print axioms robust_S_algebraic
#print axioms robust_S_hilbert
#print axioms robust_S_quaternionic
#print axioms thm_cer_seven_b_M_algebraic
#print axioms thm_cer_seven_b_M_hilbert
#print axioms thm_cer_seven_b_M_quaternionic
#print axioms thm_cer_seven_b_S_algebraic
#print axioms thm_cer_seven_b_S_hilbert
#print axioms thm_cer_seven_b_S_quaternionic

end AlbertSequential.BlockB
