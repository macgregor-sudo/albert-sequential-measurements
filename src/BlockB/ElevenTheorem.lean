/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockB.ElevenCore
public import BlockB.ElevenSupport
public import BlockB.StateSupport
public import BoundedWordEffects
public import QuaternionicProjectiveData
public import NativeCubicLowerBounds
public import NativeDiagonalProduct

/-!
# Length-Eleven Certificate Theorem (`thm:eleven`)

Composes `BlockB.ElevenCore`, `BlockB.ElevenSupport`, `BlockB.StateSupport`,
`Ends.Eleven`, and the model bridges (`HilbertProjectiveData.toAlgebraic`,
`QuaternionicProjectiveData.toAlgebraic`) to prove parts (a), (b), (c) and the
combined package `thm_eleven_full` of paper `thm:eleven` for arbitrary four
atoms `p : Fin 4 → Albert` satisfying `0 < fourPointInvariant p`.

The explicit margin matches the paper's `m = (min_j Δ_j) det(y) / 4` directly:
by `atomCorner_discriminant_swapBase`, all four base discriminants equal `Δ_0`,
and `jordanDet (p 0 + p 1 + p 2 + p 3) / 4` lower-bounds `tracePairing ρ y`
uniformly across all Albert density operators `ρ`.
-/

@[expose] public section

noncomputable section

namespace AlbertSequential.BlockB

open AlbertSequential
open AlbertSequential.NativeAnalysis
open AlbertSequential.Ends.Eleven

/- Lean 4.36 / Mathlib v4.36.0: `Real.lt` (and the other `Real` operations) are no longer
`irreducible_def`s; in this non-module file failing defeq checks such as `0 < x` against `0 < y` would
evaluate `fourPointInvariant`, `tracePairing` and `albertTrace` into Cauchy sequences. Proofs here
unfold them only through their equation lemmas (`unfold`, `simp only`). -/
attribute [local irreducible] fourPointInvariant tracePairing albertTrace

/-! ## Section 1: Cubic determinant bound on `p_A + p_B + p_C + p_D` -/

/-- Jordan cubic determinant `det(x) = ((tr x)^3 - 3 tr(x) tr(x^2) + 2 tr(x^3)) / 6`
on `Albert`. -/
def jordanDet (x : Albert) : ℝ :=
  ((albertTrace x) ^ 3 - 3 * albertTrace x * albertTrace (jordanMul x x) +
    2 * albertTrace (jordanMul x (jordanMul x x))) / 6

theorem jordanDet_automorphism (g : NativeAlbertAutomorphism) (x : Albert) :
    jordanDet (g.linearEquiv x) = jordanDet x := by
  simp only [jordanDet, ← g.preserves_product, g.preserves_trace]

theorem jordanDet_diagonal (d : Fin 3 → ℝ) :
    jordanDet (diagonalElement d) = d 0 * d 1 * d 2 := by
  simp only [jordanDet, diagonal_product, diagonal_trace, Fin.sum_univ_three]
  ring

private theorem albertTrace_add' (x y : Albert) :
    albertTrace (x + y) = albertTrace x + albertTrace y := by
  unfold albertTrace
  rw [show (∑ i : Fin 3, (x + y).1 i) = ∑ i : Fin 3, (x.1 i + y.1 i) from rfl,
    Finset.sum_add_distrib]

private theorem tracePairing_sub_right' (x y z : Albert) :
    tracePairing x (y - z) = tracePairing x y - tracePairing x z := by
  unfold tracePairing
  rw [jordanMul_sub_right, albertTrace_sub]

private theorem tracePairing_smul_right' (c : ℝ) (x y : Albert) :
    tracePairing x (c • y) = c * tracePairing x y := by
  unfold tracePairing
  rw [jordanMul_smul_right, albertTrace_smul]

private theorem tracePairing_albertUnit_right' (ρ : Albert) :
    tracePairing ρ albertUnit = albertTrace ρ := by
  unfold tracePairing
  rw [jordanMul_albertUnit_right]

private theorem atomSum_diagonalization_pos (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    {g : NativeAlbertAutomorphism} {d : Fin 3 → ℝ}
    (hdiag : g.linearEquiv (p 0 + p 1 + p 2 + p 3) = diagonalElement d) :
    (∀ i : Fin 3, 0 < d i) ∧ d 0 + d 1 + d 2 = 4 := by
  have hd_pos : ∀ i : Fin 3, 0 < d i := by
    intro i
    let q : Albert := (nativeAutomorphismInverse g).linearEquiv (diagAtom i)
    have hq_atom : IsAtom q :=
      nativeAutomorphism_isAtom (nativeAutomorphismInverse g) (diagAtom i) (diagAtom_isAtom i)
    have hq_dens : IsDensity q := ⟨isPositive_idempotent q hq_atom.1, hq_atom.2⟩
    have hpos := atomSum_pairing_pos p hp hA q hq_dens
    have heq : tracePairing q (p 0 + p 1 + p 2 + p 3) = d i := by
      calc tracePairing q (p 0 + p 1 + p 2 + p 3)
          = tracePairing (g.linearEquiv q) (g.linearEquiv (p 0 + p 1 + p 2 + p 3)) :=
            (nativeAutomorphism_pairing g q (p 0 + p 1 + p 2 + p 3)).symm
        _ = tracePairing (diagAtom i) (diagonalElement d) := by
            simp only [q, nativeAutomorphismInverse_apply, LinearEquiv.apply_symm_apply, hdiag]
        _ = d i := by
            rw [tracePairing_diagAtom]
            rfl
    simpa only [heq] using hpos
  have hd_sum : d 0 + d 1 + d 2 = 4 := by
    calc d 0 + d 1 + d 2
        = ∑ i : Fin 3, d i := (Fin.sum_univ_three d).symm
      _ = albertTrace (diagonalElement d) := (diagonal_trace d).symm
      _ = albertTrace (g.linearEquiv (p 0 + p 1 + p 2 + p 3)) := by rw [← hdiag]
      _ = albertTrace (p 0 + p 1 + p 2 + p 3) := g.preserves_trace _
      _ = albertTrace (p 0) + albertTrace (p 1) + albertTrace (p 2) + albertTrace (p 3) := by
          simp only [albertTrace_add']
      _ = 4 := by
          rw [(hp 0).2, (hp 1).2, (hp 2).2, (hp 3).2]
          norm_num
  exact ⟨hd_pos, hd_sum⟩

theorem jordanDet_atomSum_pos (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    0 < jordanDet (p 0 + p 1 + p 2 + p 3) := by
  obtain ⟨g, d, hdiag⟩ := nativeDiagonalization (p 0 + p 1 + p 2 + p 3)
  obtain ⟨hd_pos, -⟩ := atomSum_diagonalization_pos p hp hA hdiag
  rw [← jordanDet_automorphism g, hdiag, jordanDet_diagonal]
  exact mul_pos (mul_pos (hd_pos 0) (hd_pos 1)) (hd_pos 2)

theorem jordanDet_div_four_le_atomSum (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ) :
    jordanDet (p 0 + p 1 + p 2 + p 3) / 4 ≤ tracePairing ρ (p 0 + p 1 + p 2 + p 3) := by
  obtain ⟨g, d, hdiag⟩ := nativeDiagonalization (p 0 + p 1 + p 2 + p 3)
  obtain ⟨hd_pos, hd_sum⟩ := atomSum_diagonalization_pos p hp hA hdiag
  have hdet_eq : jordanDet (p 0 + p 1 + p 2 + p 3) = d 0 * d 1 * d 2 := by
    rw [← jordanDet_automorphism g, hdiag, jordanDet_diagonal]
  set c : ℝ := jordanDet (p 0 + p 1 + p 2 + p 3) / 4
  have hc_le_entry : ∀ i : Fin 3, c ≤ d i := by
    intro i
    change jordanDet (p 0 + p 1 + p 2 + p 3) / 4 ≤ d i
    rw [hdet_eq]
    have h0 := hd_pos 0
    have h1 := hd_pos 1
    have h2 := hd_pos 2
    have h012 : ∀ a b e : ℝ, 0 < a → 0 < b → 0 < e → a + b + e = 4 → a * b * e / 4 ≤ a := by
      intro a b e ha hb he habe
      have hbe : 4 * (b * e) ≤ 16 := by nlinarith [sq_nonneg (b - e)]
      have hmul : a * (b * e) ≤ 4 * a := by nlinarith
      linarith
    fin_cases i
    · change d 0 * d 1 * d 2 / 4 ≤ d 0
      exact h012 (d 0) (d 1) (d 2) h0 h1 h2 hd_sum
    · change d 0 * d 1 * d 2 / 4 ≤ d 1
      have h := h012 (d 1) (d 0) (d 2) h1 h0 h2 (by linarith)
      linarith [show d 0 * d 1 * d 2 = d 1 * d 0 * d 2 by ring]
    · change d 0 * d 1 * d 2 / 4 ≤ d 2
      have h := h012 (d 2) (d 0) (d 1) h2 h0 h1 (by linarith)
      linarith [show d 0 * d 1 * d 2 = d 2 * d 0 * d 1 by ring]
  have hpos_diag : IsPositive (diagonalElement (fun i => d i - c)) :=
    diagonal_positive_of_entries _ (fun i => sub_nonneg.mpr (hc_le_entry i))
  have hshift :
      g.linearEquiv (p 0 + p 1 + p 2 + p 3 - c • albertUnit) =
        diagonalElement (fun i => d i - c) := by
    rw [map_sub, map_smul, g.preserves_unit, hdiag]
    exact diagonal_sub_scalar_unit d c
  have hpos_diff : IsPositive (p 0 + p 1 + p 2 + p 3 - c • albertUnit) := by
    rw [← LinearEquiv.symm_apply_apply g.linearEquiv (p 0 + p 1 + p 2 + p 3 - c • albertUnit)]
    change IsPositive ((nativeAutomorphismInverse g).linearEquiv _)
    rw [hshift]
    exact nativeAutomorphism_positive (nativeAutomorphismInverse g) _ hpos_diag
  have hpair := tracePairing_positive_nonnegative ρ (p 0 + p 1 + p 2 + p 3 - c • albertUnit)
    hρ.1 hpos_diff
  rw [tracePairing_sub_right', tracePairing_smul_right', tracePairing_albertUnit_right',
    hρ.2, mul_one] at hpair
  linarith

/-! ## Section 2: Explicit margin and combined separator on `elevenUnion` -/

/-- Exact quantitative margin `m = Δ_0 * det(y) / 4` for `y = p_A + p_B + p_C + p_D`.
Since `atomCorner_discriminant_swapBase` shows `Δ_j = Δ_0` for all `j : Fin 4`,
this matches `(min_j Δ_j) det(y) / 4`. -/
def elevenMargin (p : Fin 4 → Albert) : ℝ :=
  (atomCornerData p).scalarParameters.discriminant *
    (jordanDet (p 0 + p 1 + p 2 + p 3) / 4)

theorem elevenMargin_pos (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    0 < elevenMargin p := by
  exact mul_pos (atomCorner_discriminant_pos p hp hA)
    (div_pos (jordanDet_atomSum_pos p hp hA) (by norm_num))

/-- The explicit four-base combined residual-telescope witness at `m = elevenMargin p`. -/
def elevenSeparator (p : Fin 4 → Albert) : FiniteRealWordFunctional 4 :=
  combinedCornerWitness
    (fun j => atomCornerData (p ∘ Equiv.swap 0 j))
    (fun j => atomCornerScalar (p ∘ Equiv.swap 0 j))
    (fun j a => swapBase j a)
    (fun _ => 1)
    (elevenMargin p)

theorem elevenSeparator_eq_atomCornerWitness (p : Fin 4 → Albert) :
    elevenSeparator p = atomCornerWitness p (elevenMargin p) := by
  unfold elevenSeparator atomCornerWitness
  rw [show (fun j a => swapBase j a) = (fun j => (Equiv.swap 0 j : Fin 4 → Fin 4)) from rfl]

theorem elevenSeparator_terms_mem (p : Fin 4 → Albert) :
    ∀ t ∈ (elevenSeparator p).terms,
      (t.2 = [] ∨ t.2 ∈ elevenUnion) ∧ IsReducedWord t.2 :=
  (combinedCornerWitness_swapBase_support
    (fun j => atomCornerData (p ∘ Equiv.swap 0 j))
    (fun j => atomCornerScalar (p ∘ Equiv.swap 0 j))
    (fun _ => 1) (elevenMargin p)).1

private theorem support_of_terms_mem {n : ℕ} (c : FiniteRealWordFunctional n)
    (P : Word (Fin n) → Prop) (h : ∀ t ∈ c.terms, P t.2) :
    ∀ w ∈ c.coefficients.support, P w := by
  classical
  intro w hw
  by_contra hnot
  have hzero : c.coefficients w = 0 := by
    apply FiniteRealWordFunctional.coefficientsOfTerms_apply_eq_zero_of_absent
    intro t ht heq
    exact hnot (heq ▸ h t ht)
  exact (Finsupp.mem_support_iff.mp hw) hzero

theorem elevenSeparator_support (p : Fin 4 → Albert) :
    (∀ t ∈ (elevenSeparator p).terms,
      (t.2 = [] ∨ t.2 ∈ elevenUnion) ∧ IsReducedWord t.2) ∧
    (∀ w ∈ (elevenSeparator p).coefficients.support,
      (w = [] ∨ w ∈ elevenUnion) ∧ IsReducedWord w) :=
  ⟨elevenSeparator_terms_mem p,
    support_of_terms_mem (elevenSeparator p) _ (elevenSeparator_terms_mem p)⟩

theorem elevenSeparator_horizon (p : Fin 4 → Albert) :
    (elevenSeparator p).HasHorizon 11 := by
  rw [elevenSeparator_eq_atomCornerWitness p]
  exact atomCornerWitness_horizon p (elevenMargin p)

theorem elevenSeparator_nonneg_algebraic
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : AlgebraicProjectiveData (Fin 4) A) :
    0 ≤ (elevenSeparator p).evaluate M.probability := by
  rw [elevenSeparator_eq_atomCornerWitness p]
  exact atomCornerWitness_model_nonnegative p hp hA M (elevenMargin p) (elevenMargin_pos p hp hA)

theorem elevenSeparator_nonneg_hilbert
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : HilbertProjectiveData (Fin 4) 𝕜 H) :
    0 ≤ (elevenSeparator p).evaluate M.probability := by
  have h : (elevenSeparator p).evaluate M.toAlgebraic.probability =
      (elevenSeparator p).evaluate M.probability := by
    unfold FiniteRealWordFunctional.evaluate
    exact congrArg List.sum (List.map_congr_left fun t _ => by rw [M.toAlgebraic_probability])
  rw [← h]
  exact elevenSeparator_nonneg_algebraic p hp hA M.toAlgebraic

theorem elevenSeparator_nonneg_quaternionic
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H}
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : QuaternionicProjectiveData (Fin 4) Q) :
    0 ≤ (elevenSeparator p).evaluate (fun w => M.state (M.wordEffect w)) := by
  have h : (elevenSeparator p).evaluate M.toAlgebraic.probability =
      (elevenSeparator p).evaluate (fun w => M.state (M.wordEffect w)) := by
    unfold FiniteRealWordFunctional.evaluate
    exact congrArg List.sum (List.map_congr_left fun t _ => by rw [M.toAlgebraic_probability])
  rw [← h]
  exact elevenSeparator_nonneg_algebraic p hp hA M.toAlgebraic

theorem elevenSeparator_native_le
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ) :
    (elevenSeparator p).evaluate (nativeWordProbability p ρ) ≤ -(elevenMargin p / 2) := by
  rw [elevenSeparator_eq_atomCornerWitness p]
  have hdisc : 0 ≤ (atomCornerData p).scalarParameters.discriminant :=
    (atomCorner_discriminant_pos p hp hA).le
  have hmargin : elevenMargin p ≤
      (atomCornerData p).scalarParameters.discriminant *
        tracePairing ρ (p 0 + p 1 + p 2 + p 3) := by
    unfold elevenMargin
    exact mul_le_mul_of_nonneg_left (jordanDet_div_four_le_atomSum p hp hA ρ hρ) hdisc
  exact atomCornerWitness_native_le p hp hA ρ hρ (elevenMargin p)
    (elevenMargin_pos p hp hA) hmargin

/-! ## Section 3: Helper probability identities at `[]` -/

private theorem algebraic_probability_nil
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) : M.probability [] = 1 := by
  simp [AlgebraicProjectiveData.probability, wordOperator, wordAmplitude, M.state_unit]

private theorem native_probability_nil (p : Fin 4 → Albert)
    {ρ : Albert} (hρ : IsDensity ρ) : nativeWordProbability p ρ [] = 1 := by
  rw [nativeWordProbability_eq_pairing]
  change tracePairing ρ albertUnit = 1
  rw [tracePairing_albertUnit_right', hρ.2]

/-! ## Section 4: `thm:eleven` Part (a) on `elevenBase` (`2,041` reduced words from `e / 3`) -/

/-- **thm:eleven (a), algebraic comparator class.**
From the maximally mixed state `(1 / 3 : ℝ) • albertUnit`, no algebraic sequential
model reproduces the Albert word probabilities on `Ends.Eleven.elevenBase`. -/
theorem thm_eleven_a_algebraic
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hM : ∀ w ∈ elevenBase,
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) : False := by
  set m₀ : ℝ := (atomCornerData p).scalarParameters.discriminant * (1 / 3 : ℝ)
  have hm₀ : 0 < m₀ := mul_pos (atomCorner_discriminant_pos p hp hA) (by norm_num)
  have hnonneg : 0 ≤ (atomCornerSingleBaseWitness p m₀).evaluate M.probability :=
    atomCornerSingleBaseWitness_model_nonnegative p hp hA M m₀ hm₀
  have hmix : IsDensity ((1 / 3 : ℝ) • albertUnit) := native_maximally_mixed_density
  have hsing : nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) [(0, true)] = 1 / 3 := by
    rw [nativeWordProbability_eq_pairing, nativeWordEffect_singleton p (fun i => (hp i).1)]
    change tracePairing ((1 / 3 : ℝ) • albertUnit) (p 0) = 1 / 3
    unfold tracePairing
    rw [jordanMul_comm, jordanMul_smul_right, albertTrace_smul, jordanMul_albertUnit_right,
      (hp 0).2, mul_one]
  have hnat : (atomCornerSingleBaseWitness p m₀).evaluate
      (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) ≤ -(m₀ / 2) := by
    refine atomCornerSingleBaseWitness_native_le p hp _ hmix m₀ hm₀ ?_
    rw [hsing]
  have heq : (atomCornerSingleBaseWitness p m₀).evaluate M.probability =
      (atomCornerSingleBaseWitness p m₀).evaluate
        (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) := by
    simp only [atomCornerSingleBaseWitness, constructiveResidualSeparator_evaluate]
    have hocc :
        ((cornerResidualTelescopeOccurrences (atomCornerData p) (atomCornerScalar p)).map
          (fun o => o.leaf.wordFunctional.evaluate M.probability)).sum =
        ((cornerResidualTelescopeOccurrences (atomCornerData p) (atomCornerScalar p)).map
          (fun o => o.leaf.wordFunctional.evaluate
            (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)))).sum :=
      congrArg List.sum (List.map_congr_left (cornerResidualTelescope_eq_of_eqOn_elevenBase
        (atomCornerData p) (atomCornerScalar p) hM))
    have hbase :
        (cornerBaseFunctional (atomCornerData p)).evaluate M.probability =
        (cornerBaseFunctional (atomCornerData p)).evaluate
          (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) :=
      cornerBaseFunctional_eq_of_eqOn_elevenBase (atomCornerData p) hM
    rw [hocc, hbase, algebraic_probability_nil M, native_probability_nil p hmix]
  linarith

/-- **thm:eleven (a), real or complex Hilbert-space models.** -/
theorem thm_eleven_a_hilbert
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : HilbertProjectiveData (Fin 4) 𝕜 H)
    (hM : ∀ w ∈ elevenBase,
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) : False :=
  thm_eleven_a_algebraic p hp hA M.toAlgebraic fun w hw => by
    rw [M.toAlgebraic_probability]
    exact hM w hw

/-- **thm:eleven (a), right quaternionic Hilbert-space models.** -/
theorem thm_eleven_a_quaternionic
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H}
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : QuaternionicProjectiveData (Fin 4) Q)
    (hM : ∀ w ∈ elevenBase,
      M.state (M.wordEffect w) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) : False :=
  thm_eleven_a_algebraic p hp hA M.toAlgebraic fun w hw => by
    rw [M.toAlgebraic_probability]
    exact hM w hw

/-! ## Section 5: `thm:eleven` Part (b) on `elevenUnion` (`8,164` reduced words, every state `ρ`) -/

/-- **thm:eleven (b), algebraic comparator class.**
For EVERY density operator `ρ : Albert`, no algebraic sequential model reproduces
`nativeWordProbability p ρ` on `elevenUnion`. -/
theorem thm_eleven_b_algebraic
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : AlgebraicProjectiveData (Fin 4) A)
    (hM : ∀ w ∈ elevenUnion, M.probability w = nativeWordProbability p ρ w) : False := by
  have hnonneg : 0 ≤ (elevenSeparator p).evaluate M.probability :=
    elevenSeparator_nonneg_algebraic p hp hA M
  have hnat : (elevenSeparator p).evaluate (nativeWordProbability p ρ) ≤ -(elevenMargin p / 2) :=
    elevenSeparator_native_le p hp hA ρ hρ
  have hm_pos := elevenMargin_pos p hp hA
  have heq : (elevenSeparator p).evaluate M.probability =
      (elevenSeparator p).evaluate (nativeWordProbability p ρ) := by
    unfold FiniteRealWordFunctional.evaluate
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rcases (elevenSeparator_terms_mem p t ht).1 with ht_nil | hw_mem
    · rw [ht_nil, algebraic_probability_nil M, native_probability_nil p hρ]
    · rw [hM t.2 hw_mem]
  linarith

/-- **thm:eleven (b), real or complex Hilbert-space models.** -/
theorem thm_eleven_b_hilbert
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : HilbertProjectiveData (Fin 4) 𝕜 H)
    (hM : ∀ w ∈ elevenUnion, M.probability w = nativeWordProbability p ρ w) : False :=
  thm_eleven_b_algebraic p hp hA ρ hρ M.toAlgebraic fun w hw => by
    rw [M.toAlgebraic_probability]
    exact hM w hw

/-- **thm:eleven (b), right quaternionic Hilbert-space models.** -/
theorem thm_eleven_b_quaternionic
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Q : QuaternionicOperatorStructure H}
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (ρ : Albert) (hρ : IsDensity ρ)
    (M : QuaternionicProjectiveData (Fin 4) Q)
    (hM : ∀ w ∈ elevenUnion,
      M.state (M.wordEffect w) = nativeWordProbability p ρ w) : False :=
  thm_eleven_b_algebraic p hp hA ρ hρ M.toAlgebraic fun w hw => by
    rw [M.toAlgebraic_probability]
    exact hM w hw

/-! ## Section 6: `thm:eleven` Part (c) and combined headline `thm_eleven_full` -/

/-- **thm:eleven (c): uniform finite linear witness and strict gap `γ > 0`.**
There exist a finite real word functional `Λ` supported on `{[]} ∪ elevenUnion`
(with reduced words and horizon `11`) and `γ > 0` (`γ = elevenMargin p / 2`)
such that `0 ≤ Λ.evaluate` on all algebraic, real/complex Hilbert, and
quaternionic sequential models, while `Λ.evaluate (nativeWordProbability p ρ) ≤ -γ`
for every Albert density operator `ρ`. -/
theorem thm_eleven_c.{u, v, w}
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    ∃ Λ : FiniteRealWordFunctional 4, ∃ γ : ℝ, 0 < γ ∧
      (∀ wd ∈ Λ.coefficients.support, (wd = [] ∨ wd ∈ elevenUnion) ∧ IsReducedWord wd) ∧
      Λ.HasHorizon 11 ∧
      (∀ {A : Type u} [Ring A] [StarRing A] [Module ℝ A]
          [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
          (M : AlgebraicProjectiveData (Fin 4) A), 0 ≤ Λ.evaluate M.probability) ∧
      (∀ {𝕜 : Type v} {H : Type u} [RCLike 𝕜] [NormedAddCommGroup H]
          [InnerProductSpace 𝕜 H] [CompleteSpace H]
          (M : HilbertProjectiveData (Fin 4) 𝕜 H), 0 ≤ Λ.evaluate M.probability) ∧
      (∀ {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
          {Q : QuaternionicOperatorStructure H}
          (M : QuaternionicProjectiveData (Fin 4) Q),
          0 ≤ Λ.evaluate (fun wd => M.state (M.wordEffect wd))) ∧
      (∀ ρ : Albert, IsDensity ρ → Λ.evaluate (nativeWordProbability p ρ) ≤ -γ) := by
  refine ⟨elevenSeparator p, elevenMargin p / 2, div_pos (elevenMargin_pos p hp hA) (by norm_num),
    (elevenSeparator_support p).2, elevenSeparator_horizon p, ?_, ?_, ?_, ?_⟩
  · intro A _ _ _ _ _ _ M
    exact elevenSeparator_nonneg_algebraic p hp hA M
  · intro 𝕜 H _ _ _ _ M
    exact elevenSeparator_nonneg_hilbert p hp hA M
  · intro H _ _ _ Q M
    exact elevenSeparator_nonneg_quaternionic p hp hA M
  · intro ρ hρ
    exact elevenSeparator_native_le p hp hA ρ hρ

/-- **Combined `thm:eleven` headline (word-set ledger equivalence, parts (a), (b), and (c)).** -/
theorem thm_eleven_full.{u, v, w}
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    elevenBase.card = 2041 ∧
      elevenLedgerWords = elevenBase ∧
      elevenUnion.card = 8164 ∧
      (∀ {A : Type u} [Ring A] [StarRing A] [Module ℝ A]
          [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
          (M : AlgebraicProjectiveData (Fin 4) A),
          (∀ wd ∈ elevenBase,
            M.probability wd = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) wd) → False) ∧
      (∀ {𝕜 : Type v} {H : Type u} [RCLike 𝕜] [NormedAddCommGroup H]
          [InnerProductSpace 𝕜 H] [CompleteSpace H]
          (M : HilbertProjectiveData (Fin 4) 𝕜 H),
          (∀ wd ∈ elevenBase,
            M.probability wd = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) wd) → False) ∧
      (∀ {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
          {Q : QuaternionicOperatorStructure H}
          (M : QuaternionicProjectiveData (Fin 4) Q),
          (∀ wd ∈ elevenBase,
            M.state (M.wordEffect wd) =
              nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) wd) → False) ∧
      (∀ (ρ : Albert), IsDensity ρ →
        (∀ {A : Type u} [Ring A] [StarRing A] [Module ℝ A]
            [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
            (M : AlgebraicProjectiveData (Fin 4) A),
            (∀ wd ∈ elevenUnion, M.probability wd = nativeWordProbability p ρ wd) → False) ∧
        (∀ {𝕜 : Type v} {H : Type u} [RCLike 𝕜] [NormedAddCommGroup H]
            [InnerProductSpace 𝕜 H] [CompleteSpace H]
            (M : HilbertProjectiveData (Fin 4) 𝕜 H),
            (∀ wd ∈ elevenUnion, M.probability wd = nativeWordProbability p ρ wd) → False) ∧
        (∀ {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            {Q : QuaternionicOperatorStructure H}
            (M : QuaternionicProjectiveData (Fin 4) Q),
            (∀ wd ∈ elevenUnion,
              M.state (M.wordEffect wd) = nativeWordProbability p ρ wd) → False)) ∧
      (∃ Λ : FiniteRealWordFunctional 4, ∃ γ : ℝ, 0 < γ ∧
        (∀ wd ∈ Λ.coefficients.support, (wd = [] ∨ wd ∈ elevenUnion) ∧ IsReducedWord wd) ∧
        Λ.HasHorizon 11 ∧
        (∀ {A : Type u} [Ring A] [StarRing A] [Module ℝ A]
            [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
            (M : AlgebraicProjectiveData (Fin 4) A), 0 ≤ Λ.evaluate M.probability) ∧
        (∀ {𝕜 : Type v} {H : Type u} [RCLike 𝕜] [NormedAddCommGroup H]
            [InnerProductSpace 𝕜 H] [CompleteSpace H]
            (M : HilbertProjectiveData (Fin 4) 𝕜 H), 0 ≤ Λ.evaluate M.probability) ∧
        (∀ {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
            {Q : QuaternionicOperatorStructure H}
            (M : QuaternionicProjectiveData (Fin 4) Q),
            0 ≤ Λ.evaluate (fun wd => M.state (M.wordEffect wd))) ∧
        (∀ ρ : Albert, IsDensity ρ → Λ.evaluate (nativeWordProbability p ρ) ≤ -γ)) := by
  refine ⟨elevenBase_card, elevenLedgerWords_eq_elevenBase, elevenUnion_card,
    ?_, ?_, ?_, ?_, thm_eleven_c p hp hA⟩
  · intro A _ _ _ _ _ _ M hM
    exact thm_eleven_a_algebraic p hp hA M hM
  · intro 𝕜 H _ _ _ _ M hM
    exact thm_eleven_a_hilbert p hp hA M hM
  · intro H _ _ _ Q M hM
    exact thm_eleven_a_quaternionic p hp hA M hM
  · intro ρ hρ
    refine ⟨?_, ?_, ?_⟩
    · intro A _ _ _ _ _ _ M hM
      exact thm_eleven_b_algebraic p hp hA ρ hρ M hM
    · intro 𝕜 H _ _ _ _ M hM
      exact thm_eleven_b_hilbert p hp hA ρ hρ M hM
    · intro H _ _ _ Q M hM
      exact thm_eleven_b_quaternionic p hp hA ρ hρ M hM

end AlbertSequential.BlockB
