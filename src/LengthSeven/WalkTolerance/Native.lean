/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.WalkTolerance.Main
public import LengthSeven.TableValues
public import Ends.UniformSevenMargin

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.LemmaA.WalkTolerance

open AlbertSequential.NativeAnalysis AlbertSequential.Ends
open AlbertSequential.LengthSeven.Uniform

/-- Every entry of the actual 28-history Gram is stable under perturbations
of the table read from the first atom. The constant is fixed by the traces
and the literal finite derivation before choosing the model or its universe. -/
theorem gram_within_atoms {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : WalkForm V) (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (ε : ℝ)
    (hε : 0 ≤ ε) (h : W.Approximates wordsE3 (nativeWordProbability p (p 0)) ε)
    (i j : Fin 28) :
    Within (Real.sqrt ε) (gramCost (nativeTraceData p))
      (W.form (W.pathVec (word28 i)) (W.pathVec (word28 j)))
      (gram28 (nativeTraceData p) i j) := by
  have b : W.Approximates wordsE3 (nativeWordProbability p (p 0)) (min ε 1) := by
    intro w hw
    have hn := nativeWordProbability_density_bounds p (fun i => (hp i).1)
      (p 0) ⟨isPositive_idempotent (p 0) (hp 0).1, (hp 0).2⟩ w
    have hw₁ : W.normSq (W.vec w) ≤ 1 :=
      (W.normSq_seqL_le w W.ξ).trans (by rw [WalkForm.normSq, W.unit])
    have hw₀ := W.psd (W.vec w)
    change 0 ≤ W.normSq (W.vec w) at hw₀
    exact le_min (h w hw) (abs_le.mpr ⟨by linarith [hn.2], by linarith [hn.1]⟩)
  have hb := lemmaA_within
    (⟨le_min hε zero_le_one, min_le_right _ _, _, tableValues_native p hp, b⟩ :
      ShortTableInput W (nativeTraceData p) (min ε 1)) i j
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (min_le_left _ _)) (gramCost_nonneg _))

section Algebraic

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- A small error in the literal reduced length-seven table from the maximally
mixed state controls the actual Gram of the conditioned walk. The factor
`√8` is the cost of dividing by the model's probability of the first yes. -/
theorem gram_within_e3 (M : AlgebraicProjectiveData Letter A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hsmall : uniformSevenError p M.probability ≤ 1 / 12) :
    ∃ h : 0 < M.probability [(0, true)], ∀ i j : Fin 28,
      Within (Real.sqrt (uniformSevenError p M.probability)) (Real.sqrt 8 * gramCost (nativeTraceData p))
        ((WalkForm.ofAlgebraic M h).form ((WalkForm.ofAlgebraic M h).pathVec (word28 i))
          ((WalkForm.ofAlgebraic M h).pathVec (word28 j))) (gram28 (nativeTraceData p) i j) := by
  let ε := uniformSevenError p M.probability
  let ρ := (1 / 3 : ℝ) • albertUnit
  have he₀ : 0 ≤ ε := finiteWordError_nonnegative _ _ _ _
  have he₁ : ε ≤ 1 / 12 := hsmall
  have err (u : Word Letter) (hu : u ∈ wordsE3) :
      |M.probability ((0, true) :: u) - (1 / 3) * nativeWordProbability p (p 0) u| ≤ ε := by
    rw [← e3_conditioning p hp]
    have hm : (0, true) :: u ∈ sevenAYesWords := by
      apply (mem_sevenAYesWords _).mpr
      change u.length ≤ 6 at hu
      change u.length + 1 ≤ 7 ∧ some ((0 : Letter), true) = some (0, true)
      exact ⟨by omega, rfl⟩
    have h := Finset.le_sup' (fun w => |M.probability w - nativeWordProbability p ρ w|) hm
    change _ ≤ finiteWordError sevenAYesWords sevenAYesWords_nonempty
      M.probability (nativeWordProbability p ρ) at h
    rwa [sevenAYesWordError_eq_reduced M p hp ρ] at h
  let q := M.probability [(0, true)]
  have hqε : |q - 1 / 3| ≤ ε := by
    simpa only [nativeWordProbability, nativeBranchState, List.foldl_nil, (hp 0).2, mul_one]
      using err [] (by decide)
  have hq : 1 / 4 ≤ q := by linarith only [(abs_le.mp hqε).1, he₁]
  have hq₀ : 0 < q := by linarith only [hq]
  refine ⟨hq₀, ?_⟩
  have errCond : (WalkForm.ofAlgebraic M hq₀).Approximates wordsE3 (nativeWordProbability p (p 0)) (8 * ε) := by
    intro u hu
    let f := nativeWordProbability p (p 0) u
    let m := M.probability ((0, true) :: u)
    have hf := nativeWordProbability_density_bounds p (fun i => (hp i).1)
      (p 0) ⟨isPositive_idempotent (p 0) (hp 0).1, (hp 0).2⟩ u
    have hfn : |f| ≤ 1 := (abs_of_nonneg hf.1).trans_le hf.2
    rw [WalkForm.ofAlgebraic_normSq_vec]
    change |m / q - f| ≤ 8 * ε
    rw [show m / q - f = ((m - (1 / 3) * f) + (1 / 3 - q) * f) / q by field_simp; ring,
      abs_div, abs_of_nonneg hq₀.le]
    apply (div_le_iff₀ hq₀).mpr
    calc
      _ ≤ |m - (1 / 3) * f| + |(1 / 3 - q) * f| := abs_add_le _ _
      _ ≤ ε + ε * 1 := by
        rw [abs_mul, abs_sub_comm (1 / 3) q]
        exact add_le_add (err u hu) (mul_le_mul hqε hfn (abs_nonneg _) he₀)
      _ ≤ (8 * ε) * q := by nlinarith only [mul_nonneg he₀ (sub_nonneg.mpr hq)]
  intro i j
  have hb := gram_within_atoms (WalkForm.ofAlgebraic M hq₀) p hp (8 * ε) (by positivity) errCond i j
  unfold Within at hb ⊢
  change _ ≤ (Real.sqrt 8 * gramCost (nativeTraceData p)) * Real.sqrt ε
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)] at hb
  exact hb.trans_eq (by ring)

end Algebraic

/-- Real or complex physical word probabilities and the associated conditioned walk. -/
theorem gram_within_e3_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData Letter 𝕜 H)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hsmall : uniformSevenError p M.probability ≤ 1 / 12) :
    ∃ h : 0 < M.toAlgebraic.probability [(0, true)], ∀ i j : Fin 28,
      Within (Real.sqrt (uniformSevenError p M.probability))
        (Real.sqrt 8 * gramCost (nativeTraceData p))
        ((WalkForm.ofHilbert M h).form ((WalkForm.ofHilbert M h).pathVec (word28 i))
          ((WalkForm.ofHilbert M h).pathVec (word28 j))) (gram28 (nativeTraceData p) i j) := by
  have he := funext M.toAlgebraic_probability
  obtain ⟨h, hb⟩ := gram_within_e3 M.toAlgebraic p hp (by rwa [he])
  refine ⟨h, fun i j => ?_⟩
  rw [← he]
  exact hb i j

/-- Right-quaternionic physical word probabilities and the associated conditioned walk. -/
theorem gram_within_e3_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H} (M : QuaternionicProjectiveData Letter Q)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hsmall : uniformSevenError p (fun w => M.state (M.wordEffect w)) ≤ 1 / 12) :
    ∃ h : 0 < M.toAlgebraic.probability [(0, true)], ∀ i j : Fin 28,
      Within (Real.sqrt (uniformSevenError p (fun w => M.state (M.wordEffect w))))
        (Real.sqrt 8 * gramCost (nativeTraceData p))
        ((WalkForm.ofQuaternionic M h).form ((WalkForm.ofQuaternionic M h).pathVec (word28 i))
          ((WalkForm.ofQuaternionic M h).pathVec (word28 j))) (gram28 (nativeTraceData p) i j) := by
  have he := funext M.toAlgebraic_probability
  obtain ⟨h, hb⟩ := gram_within_e3 M.toAlgebraic p hp (by rwa [he])
  refine ⟨h, fun i j => ?_⟩
  rw [← he]
  exact hb i j

end AlbertSequential.LengthSeven.LemmaA.WalkTolerance
