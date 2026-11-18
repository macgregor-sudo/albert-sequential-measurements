/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.UniversalSix
public import Uniform.Main

/-!
# Exact Minimum Separating Word Length `L_min = 7` (`thm:cer:uniform`)

Combines:
- the length-`≤ 6` universal Class-(I) matching models (`MatchingModels.UniversalSix`,
  `prop:cer:universalsix`), which rule out separation for every `L ≤ 6`; and
- the uniform length-seven non-reproducibility theorems (`Uniform.Main`,
  `uniform_lengthSeven_e3_hilbert`, `uniform_lengthSeven_e3_quaternionic`,
  `uniform_lengthSeven_e3_algebraic`), which establish separation for every `L ≥ 7`.

Concludes that for every atom quadruple `p : Fin 4 → Albert` with `0 < fourPointInvariant p`,
the minimum separating word length from `e / 3` across Class (I) (real Hilbert, complex Hilbert,
and quaternionic projective models), as well as across `AlgebraicProjectiveData`, is exact:
`L_min(p) = 7` (`IsLeast`, `sInf`, and `Nat.find`).
-/

@[expose] public section

set_option autoImplicit false

namespace AlbertSequential.MatchingModels

open AlbertSequential
open AlbertSequential.LengthSeven
open AlbertSequential.LengthSeven.Uniform

/- Lean 4.36 / Mathlib v4.36.0: `Real.lt` is no longer an `irreducible_def`; in this non-module file
defeq checks of `0 < fourPointInvariant p` would evaluate the invariant. No proof here needs its body. -/
attribute [local irreducible] fourPointInvariant

/-- Real-Hilbert Class-(I) separation from `e / 3` at word length `L`. -/
def SeparatesRealHilbertFromE3 (p : Fin 4 → Albert) (L : ℕ) : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) ℝ H),
    ¬ (∀ w : Word (Fin 4), w.length ≤ L →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)

/-- Complex-Hilbert Class-(I) separation from `e / 3` at word length `L`. -/
def SeparatesComplexHilbertFromE3 (p : Fin 4 → Albert) (L : ℕ) : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 4) ℂ H),
    ¬ (∀ w : Word (Fin 4), w.length ≤ L →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)

/-- Quaternionic Class-(I) separation from `e / 3` at word length `L`. -/
def SeparatesQuaternionicFromE3 (p : Fin 4 → Albert) (L : ℕ) : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData (Fin 4) Q),
    ¬ (∀ w : Word (Fin 4), w.length ≤ L →
      M.state (M.wordEffect w) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)

/-- Class-(I) separation from `e / 3` at word length `L`: no ideal projective model over `ℝ`,
`ℂ`, or `ℍ` reproduces `nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)` on all words of
length `≤ L`. -/
def SeparatesFromE3AtLength (p : Fin 4 → Albert) (L : ℕ) : Prop :=
  SeparatesRealHilbertFromE3 p L ∧
  SeparatesComplexHilbertFromE3 p L ∧
  SeparatesQuaternionicFromE3 p L

/-- Comparator-class (`AlgebraicProjectiveData`) separation from `e / 3` at word length `L`. -/
def SeparatesAlgebraicFromE3AtLength (p : Fin 4 → Albert) (L : ℕ) : Prop :=
  ∀ {A : Type} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin 4) A),
    ¬ (∀ w : Word (Fin 4), w.length ≤ L →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w)

/-- Minimum separating word length `L_min` (`thm:cer:uniform`) from `e / 3` in
Class (I). -/
noncomputable def lMin (p : Fin 4 → Albert) : ℕ :=
  sInf {L : ℕ | 1 ≤ L ∧ SeparatesFromE3AtLength p L}

private theorem nat_sInf_eq_of_isLeast {S : Set ℕ} {n : ℕ} (h : IsLeast S n) : sInf S = n :=
  le_antisymm (Nat.sInf_le h.1) (le_csInf ⟨n, h.1⟩ h.2)

/-! ## Lower Bounds (`L ≤ 6` Fails to Separate) -/

theorem not_separatesRealHilbertFromE3_of_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : L ≤ 6) :
    ¬ SeparatesRealHilbertFromE3 p L := by
  intro hsep
  obtain ⟨H, _, _, _, M, hmatch⟩ := prop_cer_universalsix_real p hp hA
  exact hsep M fun w hw => hmatch w (le_trans hw hL)

theorem not_separatesComplexHilbertFromE3_of_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : L ≤ 6) :
    ¬ SeparatesComplexHilbertFromE3 p L := by
  intro hsep
  obtain ⟨M, hmatch⟩ := prop_cer_universalsix_c12 p hp hA
  exact hsep M fun w hw => hmatch w (le_trans hw hL)

theorem not_separatesQuaternionicFromE3_of_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : L ≤ 6) :
    ¬ SeparatesQuaternionicFromE3 p L := by
  intro hsep
  obtain ⟨H, _, _, _, Q, M, hmatch⟩ := prop_cer_universalsix_quaternionic p hp hA
  exact hsep M fun w hw => hmatch w (le_trans hw hL)

theorem not_separatesFromE3AtLength_of_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : L ≤ 6) :
    ¬ SeparatesFromE3AtLength p L := by
  intro hsep
  exact not_separatesComplexHilbertFromE3_of_le_six p hp hA hL hsep.2.1

theorem not_separatesAlgebraicFromE3AtLength_of_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : L ≤ 6) :
    ¬ SeparatesAlgebraicFromE3AtLength p L := by
  intro hsep
  obtain ⟨A, _, _, _, _, _, _, M, hmatch⟩ := prop_cer_universalsix_algebraic p hp hA
  exact hsep M fun w hw => hmatch w (le_trans hw hL)

/-! ## Upper Bounds (`L ≥ 7` Separates) -/

theorem separatesRealHilbertFromE3_of_seven_le (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : 7 ≤ L) :
    SeparatesRealHilbertFromE3 p L := by
  intro H _ _ _ M hmatch
  exact uniform_lengthSeven_e3_hilbert p hp hA M fun w hw _ => hmatch w (le_trans hw hL)

theorem separatesComplexHilbertFromE3_of_seven_le (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : 7 ≤ L) :
    SeparatesComplexHilbertFromE3 p L := by
  intro H _ _ _ M hmatch
  exact uniform_lengthSeven_e3_hilbert p hp hA M fun w hw _ => hmatch w (le_trans hw hL)

theorem separatesQuaternionicFromE3_of_seven_le (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : 7 ≤ L) :
    SeparatesQuaternionicFromE3 p L := by
  intro H _ _ _ Q M hmatch
  exact uniform_lengthSeven_e3_quaternionic p hp hA M fun w hw _ => hmatch w (le_trans hw hL)

theorem separatesFromE3AtLength_of_seven_le (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : 7 ≤ L) :
    SeparatesFromE3AtLength p L :=
  ⟨separatesRealHilbertFromE3_of_seven_le p hp hA hL,
    separatesComplexHilbertFromE3_of_seven_le p hp hA hL,
    separatesQuaternionicFromE3_of_seven_le p hp hA hL⟩

theorem separatesAlgebraicFromE3AtLength_of_seven_le (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {L : ℕ} (hL : 7 ≤ L) :
    SeparatesAlgebraicFromE3AtLength p L := by
  intro A _ _ _ _ _ _ M hmatch
  exact uniform_lengthSeven_e3_algebraic p hp hA M fun w hw _ => hmatch w (le_trans hw hL)

/-! ## Exact Characterization and `L_min = 7` -/

theorem separatesFromE3AtLength_iff_seven_le (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (L : ℕ) :
    SeparatesFromE3AtLength p L ↔ 7 ≤ L := by
  constructor
  · intro hsep
    by_contra hlt
    exact not_separatesFromE3AtLength_of_le_six p hp hA (Nat.lt_succ_iff.mp (lt_of_not_ge hlt)) hsep
  · exact separatesFromE3AtLength_of_seven_le p hp hA

theorem separatesAlgebraicFromE3AtLength_iff_seven_le (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (L : ℕ) :
    SeparatesAlgebraicFromE3AtLength p L ↔ 7 ≤ L := by
  constructor
  · intro hsep
    by_contra hlt
    exact not_separatesAlgebraicFromE3AtLength_of_le_six p hp hA
      (Nat.lt_succ_iff.mp (lt_of_not_ge hlt)) hsep
  · exact separatesAlgebraicFromE3AtLength_of_seven_le p hp hA

theorem separatesFromE3AtLength_iff_algebraic (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (L : ℕ) :
    SeparatesFromE3AtLength p L ↔ SeparatesAlgebraicFromE3AtLength p L :=
  (separatesFromE3AtLength_iff_seven_le p hp hA L).trans
    (separatesAlgebraicFromE3AtLength_iff_seven_le p hp hA L).symm

/-- `L_min = 7` (`IsLeast` over `ℕ`) for Class-(I) separation from `e / 3`. -/
theorem lMin_e3_eq_seven (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    IsLeast {L : ℕ | SeparatesFromE3AtLength p L} 7 := by
  refine ⟨separatesFromE3AtLength_of_seven_le p hp hA le_rfl, fun L hL => ?_⟩
  exact (separatesFromE3AtLength_iff_seven_le p hp hA L).mp hL

/-- `L_min = 7` (`IsLeast` over `{L : ℕ | 1 ≤ L ∧ SeparatesFromE3AtLength p L}`). -/
theorem lMin_e3_ge_one_isLeast (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    IsLeast {L : ℕ | 1 ≤ L ∧ SeparatesFromE3AtLength p L} 7 := by
  refine ⟨⟨by decide, separatesFromE3AtLength_of_seven_le p hp hA le_rfl⟩, fun L hL => ?_⟩
  exact (separatesFromE3AtLength_iff_seven_le p hp hA L).mp hL.2

/-- `sInf {L : ℕ | SeparatesFromE3AtLength p L} = 7`. -/
theorem lMin_e3_sInf_eq_seven (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    sInf {L : ℕ | SeparatesFromE3AtLength p L} = 7 :=
  nat_sInf_eq_of_isLeast (lMin_e3_eq_seven p hp hA)

/-- `lMin p = 7`. -/
theorem lMin_eq_seven (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    lMin p = 7 :=
  nat_sInf_eq_of_isLeast (lMin_e3_ge_one_isLeast p hp hA)

/-- `Nat.find` form of `L_min = 7` for Class-(I) separation from `e / 3`. -/
theorem lMin_e3_natFind_eq_seven (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    @Nat.find (fun L => SeparatesFromE3AtLength p L) (Classical.decPred _)
        ⟨7, separatesFromE3AtLength_of_seven_le p hp hA le_rfl⟩ = 7 := by
  classical
  refine le_antisymm ?_ ?_
  · exact Nat.find_min' _ (separatesFromE3AtLength_of_seven_le p hp hA le_rfl)
  · exact (separatesFromE3AtLength_iff_seven_le p hp hA _).mp (Nat.find_spec _)

/-- `L_min = 7` (`IsLeast` over `ℕ`) for `AlgebraicProjectiveData` separation from `e / 3`. -/
theorem lMin_e3_algebraic_isLeast (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    IsLeast {L : ℕ | SeparatesAlgebraicFromE3AtLength p L} 7 := by
  refine ⟨separatesAlgebraicFromE3AtLength_of_seven_le p hp hA le_rfl, fun L hL => ?_⟩
  exact (separatesAlgebraicFromE3AtLength_iff_seven_le p hp hA L).mp hL

/-- `sInf {L : ℕ | SeparatesAlgebraicFromE3AtLength p L} = 7`. -/
theorem lMin_e3_algebraic_sInf_eq_seven (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    sInf {L : ℕ | SeparatesAlgebraicFromE3AtLength p L} = 7 :=
  nat_sInf_eq_of_isLeast (lMin_e3_algebraic_isLeast p hp hA)

end AlbertSequential.MatchingModels
