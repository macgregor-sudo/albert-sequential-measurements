/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.FiveTestLowerBound
public import FiveTest.Main

/-!
# Minimum Separating Word Length (`cor:five:minimum` equality)

Composes the explicit 12-dimensional Class-(I) comparators from `MatchingModels.FiveTestLowerBound`
with the unconditional non-reproducibility upper bounds from `FiveTest.Main` (`cor_five_minimum_upper_p0`,
`cor_five_minimum_upper_e3`, `five_short_p0_hilbert`, `five_short_e3_hilbert`,
`five_short_p0_quaternionic`, `five_short_e3_quaternionic`) to establish `cor:five:minimum`:

* `L_min(p₀) = 10`,
* `L_min(e / 3) = 11`,

as exact `IsLeast` and `sInf` theorems across real Hilbert (`ℝ`), complex Hilbert (`ℂ`),
quaternionic (`QuaternionicOperatorStructure`), full Class-(I), and `AlgebraicProjectiveData`
sequential projective models.
-/

@[expose] public section

set_option autoImplicit false

namespace AlbertSequential.MatchingModels

open AlbertSequential.FiveTest

/-- `NoRealHilbertMatch ρ L`: no real Hilbert projective model reproduces `pentadF` from `ρ`
through word length `L`. -/
def FiveTestSeparatesRealHilbert (ρ : Albert) (L : ℕ) : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 5) ℝ H),
    ¬ (∀ w : Word (Fin 5), w.length ≤ L → M.probability w = nativeWordProbability pentadF ρ w)

/-- `FiveTestSeparatesComplexHilbert ρ L`: no complex Hilbert projective model reproduces
`pentadF` from `ρ` through word length `L`. -/
def FiveTestSeparatesComplexHilbert (ρ : Albert) (L : ℕ) : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : HilbertProjectiveData (Fin 5) ℂ H),
    ¬ (∀ w : Word (Fin 5), w.length ≤ L → M.probability w = nativeWordProbability pentadF ρ w)

/-- `FiveTestSeparatesQuaternionic ρ L`: no quaternionic projective model reproduces `pentadF`
from `ρ` through word length `L`. -/
def FiveTestSeparatesQuaternionic (ρ : Albert) (L : ℕ) : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData (Fin 5) Q),
    ¬ (∀ w : Word (Fin 5), w.length ≤ L →
      M.state (M.wordEffect w) = nativeWordProbability pentadF ρ w)

/-- `FiveTestSeparatesClassI ρ L`: no model in class (I) (`ℝ` Hilbert, `ℂ` Hilbert, or `ℍ`)
reproduces `pentadF` from `ρ` through word length `L`. -/
def FiveTestSeparatesClassI (ρ : Albert) (L : ℕ) : Prop :=
  FiveTestSeparatesRealHilbert ρ L ∧
  FiveTestSeparatesComplexHilbert ρ L ∧
  FiveTestSeparatesQuaternionic ρ L

/-- `FiveTestSeparatesAlgebraic ρ L`: no `AlgebraicProjectiveData` model reproduces `pentadF` from
`ρ` through word length `L`. -/
def FiveTestSeparatesAlgebraic (ρ : Albert) (L : ℕ) : Prop :=
  ∀ {A : Type} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin 5) A),
    ¬ (∀ w : Word (Fin 5), w.length ≤ L → M.probability w = nativeWordProbability pentadF ρ w)

private theorem nat_sInf_eq_of_isLeast {S : Set ℕ} {n : ℕ} (h : IsLeast S n) : sInf S = n :=
  le_antisymm (Nat.sInf_le h.1) (le_csInf ⟨n, h.1⟩ h.2)

/-! ## Exact `L_min` theorems from `p₀` (`= 10`) -/

theorem cor_five_minimum_p0_isLeast_complex :
    IsLeast {L : ℕ | FiveTestSeparatesComplexHilbert (pentadF 0) L} 10 := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _ M hM
    exact five_short_p0_hilbert M fun w hw => by
      rw [HilbertProjectiveData.toAlgebraic_probability]
      exact hM w hw
  · intro L hL
    by_contra hlt
    have h9 : L ≤ 9 := by omega
    exact hL fiveTestComparator_p0 fun w hw =>
      fiveTestComparator_p0_matches w (hw.trans h9)

theorem cor_five_minimum_p0_isLeast_real :
    IsLeast {L : ℕ | FiveTestSeparatesRealHilbert (pentadF 0) L} 10 := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _ M hM
    exact five_short_p0_hilbert M fun w hw => by
      rw [HilbertProjectiveData.toAlgebraic_probability]
      exact hM w hw
  · intro L hL
    by_contra hlt
    have h9 : L ≤ 9 := by omega
    exact hL fiveTestComparator_p0_real fun w hw =>
      fiveTestComparator_p0_real_matches w (hw.trans h9)

theorem cor_five_minimum_p0_isLeast_quaternionic :
    IsLeast {L : ℕ | FiveTestSeparatesQuaternionic (pentadF 0) L} 10 := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _ Q M hM
    exact five_short_p0_quaternionic M fun w hw => by
      rw [QuaternionicProjectiveData.toAlgebraic_probability]
      exact hM w hw
  · intro L hL
    by_contra hlt
    have h9 : L ≤ 9 := by omega
    exact hL fiveTestComparator_p0_quat fun w hw =>
      fiveTestComparator_p0_quat_state_matches w (hw.trans h9)

/-- **`cor:five:minimum`, first half (`L_min(p₀) = 10` for model class (I)).** -/
theorem cor_five_minimum_p0_isLeast_classI :
    IsLeast {L : ℕ | FiveTestSeparatesClassI (pentadF 0) L} 10 :=
  ⟨⟨cor_five_minimum_p0_isLeast_real.1, cor_five_minimum_p0_isLeast_complex.1,
    cor_five_minimum_p0_isLeast_quaternionic.1⟩,
   fun _ hL => cor_five_minimum_p0_isLeast_complex.2 hL.2.1⟩

/-- **`cor:five:minimum`, first half (`sInf` form for model class (I)).** -/
theorem cor_five_minimum_p0_sInf_classI :
    sInf {L : ℕ | FiveTestSeparatesClassI (pentadF 0) L} = 10 :=
  nat_sInf_eq_of_isLeast cor_five_minimum_p0_isLeast_classI

theorem cor_five_minimum_p0_isLeast_algebraic :
    IsLeast {L : ℕ | FiveTestSeparatesAlgebraic (pentadF 0) L} 10 := by
  refine ⟨?_, ?_⟩
  · intro A _ _ _ _ _ _ M hM
    exact cor_five_minimum_upper_p0 10 le_rfl M hM
  · intro L hL
    by_contra hlt
    have h9 : L ≤ 9 := by omega
    exact hL fiveTestComparator_p0.toAlgebraic fun w hw =>
      fiveTestComparator_p0_toAlgebraic_matches w (hw.trans h9)

theorem cor_five_minimum_p0_sInf_algebraic :
    sInf {L : ℕ | FiveTestSeparatesAlgebraic (pentadF 0) L} = 10 :=
  nat_sInf_eq_of_isLeast cor_five_minimum_p0_isLeast_algebraic

/-! ## Exact `L_min` theorems from `e / 3` (`= 11`) -/

theorem cor_five_minimum_e3_isLeast_complex :
    IsLeast {L : ℕ | FiveTestSeparatesComplexHilbert ((1 / 3 : ℝ) • albertUnit) L} 11 := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _ M hM
    exact five_short_e3_hilbert M fun w hw _ => by
      rw [HilbertProjectiveData.toAlgebraic_probability]
      exact hM w hw
  · intro L hL
    by_contra hlt
    have h10 : L ≤ 10 := by omega
    exact hL fiveTestComparator_e3 fun w hw =>
      fiveTestComparator_e3_matches w (hw.trans h10)

theorem cor_five_minimum_e3_isLeast_real :
    IsLeast {L : ℕ | FiveTestSeparatesRealHilbert ((1 / 3 : ℝ) • albertUnit) L} 11 := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _ M hM
    exact five_short_e3_hilbert M fun w hw _ => by
      rw [HilbertProjectiveData.toAlgebraic_probability]
      exact hM w hw
  · intro L hL
    by_contra hlt
    have h10 : L ≤ 10 := by omega
    exact hL fiveTestComparator_e3_real fun w hw =>
      fiveTestComparator_e3_real_matches w (hw.trans h10)

theorem cor_five_minimum_e3_isLeast_quaternionic :
    IsLeast {L : ℕ | FiveTestSeparatesQuaternionic ((1 / 3 : ℝ) • albertUnit) L} 11 := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _ Q M hM
    exact five_short_e3_quaternionic M fun w hw _ => by
      rw [QuaternionicProjectiveData.toAlgebraic_probability]
      exact hM w hw
  · intro L hL
    by_contra hlt
    have h10 : L ≤ 10 := by omega
    exact hL fiveTestComparator_e3_quat fun w hw =>
      fiveTestComparator_e3_quat_state_matches w (hw.trans h10)

/-- **`cor:five:minimum`, second half (`L_min(e / 3) = 11` for model class (I)).** -/
theorem cor_five_minimum_e3_isLeast_classI :
    IsLeast {L : ℕ | FiveTestSeparatesClassI ((1 / 3 : ℝ) • albertUnit) L} 11 :=
  ⟨⟨cor_five_minimum_e3_isLeast_real.1, cor_five_minimum_e3_isLeast_complex.1,
    cor_five_minimum_e3_isLeast_quaternionic.1⟩,
   fun _ hL => cor_five_minimum_e3_isLeast_complex.2 hL.2.1⟩

/-- **`cor:five:minimum`, second half (`sInf` form for model class (I)).** -/
theorem cor_five_minimum_e3_sInf_classI :
    sInf {L : ℕ | FiveTestSeparatesClassI ((1 / 3 : ℝ) • albertUnit) L} = 11 :=
  nat_sInf_eq_of_isLeast cor_five_minimum_e3_isLeast_classI

theorem cor_five_minimum_e3_isLeast_algebraic :
    IsLeast {L : ℕ | FiveTestSeparatesAlgebraic ((1 / 3 : ℝ) • albertUnit) L} 11 := by
  refine ⟨?_, ?_⟩
  · intro A _ _ _ _ _ _ M hM
    exact cor_five_minimum_upper_e3 11 le_rfl M hM
  · intro L hL
    by_contra hlt
    have h10 : L ≤ 10 := by omega
    exact hL fiveTestComparator_e3.toAlgebraic fun w hw =>
      fiveTestComparator_e3_toAlgebraic_matches w (hw.trans h10)

theorem cor_five_minimum_e3_sInf_algebraic :
    sInf {L : ℕ | FiveTestSeparatesAlgebraic ((1 / 3 : ℝ) • albertUnit) L} = 11 :=
  nat_sInf_eq_of_isLeast cor_five_minimum_e3_isLeast_algebraic

end AlbertSequential.MatchingModels
