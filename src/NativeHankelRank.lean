/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeWordSpan
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! An existential finite Hankel rank witness, derived from the actual native
word span and its positive trace form. No fixed list or computed rank is used. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis
open scoped BigOperators Matrix

theorem native_finrank : Module.finrank ℝ Albert = 27 :=
  recoveredCoordinateEquiv.finrank_eq.trans Glennie.albert_finrank

theorem exists_independent_native_word_effects {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) :
    ∃ w : Fin 27 → Word ι, LinearIndependent ℝ (fun i => nativeWordEffect p (w i)) := by
  letI : FiniteDimensional ℝ Albert := recoveredCoordinateEquiv.symm.finiteDimensional
  have hspan : Submodule.span ℝ (Set.range (nativeWordEffect p)) = ⊤ :=
    nativeWordEffectSpan_eq_top p hp hg
  have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range (nativeWordEffect p))) = 27 := by
    rw [hspan, finrank_top, native_finrank]
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range (nativeWordEffect p))
  rw [hdim] at hex
  obtain ⟨v, hv, _, hlin⟩ := hex
  choose w hw using hv
  refine ⟨w, ?_⟩
  have heq : (fun i => nativeWordEffect p (w i)) = v := funext hw
  rwa [heq]

def nativeTraceGram {n : Type*} (v : n → Albert) : Matrix n n ℝ :=
  fun i j => tracePairing (v i) (v j)

theorem tracePairing_sum_smul_right {n : Type*} [Fintype n]
    (x : Albert) (v : n → Albert) (c : n → ℝ) :
    tracePairing x (∑ i, c i • v i) = ∑ i, c i * tracePairing x (v i) := by
  change nativePairingFunctional x (∑ i, c i • v i) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  rfl

theorem tracePairing_sum_smul_left {n : Type*} [Fintype n]
    (x : Albert) (v : n → Albert) (c : n → ℝ) :
    tracePairing (∑ i, c i • v i) x = ∑ i, c i * tracePairing (v i) x := by
  rw [tracePairing_comm, tracePairing_sum_smul_right]
  congr 1
  funext i
  rw [tracePairing_comm]

theorem nativeTraceGram_quadratic {n : Type*} [Fintype n]
    (v : n → Albert) (c : n → ℝ) :
    star c ⬝ᵥ (nativeTraceGram v *ᵥ c) =
      tracePairing (∑ i, c i • v i) (∑ i, c i • v i) := by
  simp only [tracePairing_sum_smul_left, tracePairing_sum_smul_right,
    dotProduct, Matrix.mulVec, nativeTraceGram, Pi.star_apply, star_trivial,
    Finset.mul_sum]
  congr 1
  funext i
  congr 1
  funext j
  rw [tracePairing_comm (v j) (v i)]
  ring

theorem nativeTraceGram_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → Albert) (hv : LinearIndependent ℝ v) : (nativeTraceGram v).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.ext
    intro i j
    exact tracePairing_comm (v j) (v i)
  · intro c hc
    rw [nativeTraceGram_quadratic]
    have hn : (∑ i, c i • v i) ≠ 0 := by
      intro hz
      apply hc
      funext i
      exact (Fintype.linearIndependent_iff.mp hv c hz) i
    exact lt_of_le_of_ne (tracePairing_positive_definite _).1
      (Ne.symm (fun hz => hn ((tracePairing_positive_definite _).2.mp hz)))

def nativeFiniteHankel {ι n m : Type*} (p : ι → Albert) (ρ : Albert)
    (u : n → Word ι) (v : m → Word ι) : Matrix n m ℝ :=
  fun i j => nativeWordProbability p ρ (u i ++ v j)

theorem exists_native_hankel_rank27 {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) :
    ∃ u v : Fin 27 → Word ι,
      (nativeFiniteHankel p ((1 / 3 : ℝ) • albertUnit) u v).rank = 27 := by
  obtain ⟨w, hw⟩ := exists_independent_native_word_effects p hp hg
  refine ⟨fun i => (w i).reverse, w, ?_⟩
  have heq : nativeFiniteHankel p ((1 / 3 : ℝ) • albertUnit)
      (fun i => (w i).reverse) w =
      (1 / 3 : ℝ) • nativeTraceGram (fun i => nativeWordEffect p (w i)) := by
    apply Matrix.ext
    intro i j
    simp only [nativeFiniteHankel, nativeHankel_e3_pairing, List.reverse_reverse,
      Matrix.smul_apply, smul_eq_mul, nativeTraceGram]
  rw [heq]
  have hbase := nativeTraceGram_posDef _ hw
  have hpd : ((1 / 3 : ℝ) • nativeTraceGram
      (fun i => nativeWordEffect p (w i))).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.ext
      intro i j
      change (1 / 3 : ℝ) * tracePairing (nativeWordEffect p (w j)) (nativeWordEffect p (w i)) =
        (1 / 3 : ℝ) * tracePairing (nativeWordEffect p (w i)) (nativeWordEffect p (w j))
      rw [tracePairing_comm]
    · intro c hc
      simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using
        mul_pos (show (0 : ℝ) < 1 / 3 by norm_num) (hbase.dotProduct_mulVec_pos hc)
  simpa using Matrix.rank_of_isUnit _ hpd.isUnit

end AlbertSequential
