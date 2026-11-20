/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TaggedDilationDefect
import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

noncomputable section

open scoped BigOperators
open Polynomial

namespace AlbertSequential.NativeAnalysis

/-- The actual corner-effect characteristic polynomial. For orthogonal atoms
the nonzero eigenvalue is one. For equal atoms both factors are powers of X. -/
theorem nativeCornerYesEffect_charpoly (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    (nativeCornerYesEffect p hp q).charpoly =
      X^8 * (X - C (1 - tracePairing p q))^8 := by
  classical
  let A := nativeCornerYesEffect p hp q
  let c := 1 - tracePairing p q
  change A.charpoly = X^8 * (X - C c)^8
  obtain ⟨hsq, ht⟩ := nativeCornerYesEffect_square_trace p q hp hq
  change A * A = c • A at hsq
  change Matrix.trace A = 8 * c at ht
  have hA : A.PosSemidef := nativeCornerYesEffect_positive p hp q hq
  by_cases hc : c = 0
  · have hzero : A = 0 := hA.trace_eq_zero_iff.mp (by rw [ht, hc, mul_zero])
    rw [hzero, Matrix.charpoly_zero, spinorCoordinate_card, hc, map_zero, sub_zero, ← pow_add]
  let H := hA.isHermitian
  let F := Unitary.conjStarAlgAut ℝ (Matrix SpinorCoordinate SpinorCoordinate ℝ)
    (star H.eigenvectorUnitary)
  have hdiag : F A = Matrix.diagonal H.eigenvalues := by
    simpa only [F, RCLike.ofReal_real_eq_id, Function.id_comp] using
      H.conjStarAlgAut_star_eigenvectorUnitary
  have hdiagSq := congrArg F hsq
  rw [map_mul, map_smul, hdiag, Matrix.diagonal_mul_diagonal] at hdiagSq
  have hvals (i : SpinorCoordinate) : H.eigenvalues i = 0 ∨ H.eigenvalues i = c := by
    have hi := congrArg (fun M : Matrix SpinorCoordinate SpinorCoordinate ℝ => M i i) hdiagSq
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul] at hi
    have hprod : H.eigenvalues i * (H.eigenvalues i - c) = 0 := by linear_combination hi
    exact (mul_eq_zero.mp hprod).imp id sub_eq_zero.mp
  let s := Finset.univ.filter (fun i => H.eigenvalues i = c)
  let t := Finset.univ.filter (fun i => H.eigenvalues i ≠ c)
  have htrace : ∑ i, H.eigenvalues i = 8 * c := by
    simpa only [H.trace_eq_sum_eigenvalues, RCLike.ofReal_real_eq_id, id_eq] using ht
  have hsum : ∑ i, H.eigenvalues i = (s.card : ℝ) * c := by
    calc
      _ = ∑ i, if H.eigenvalues i = c then c else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : H.eigenvalues i = c
        · simp [h]
        · simp [(hvals i).resolve_right h]
      _ = _ := by rw [← Finset.sum_filter]; simp [s, nsmul_eq_mul]
  have hs : s.card = 8 := by
    exact_mod_cast mul_right_cancel₀ hc (hsum.symm.trans htrace)
  have hcard : s.card + t.card = 16 := by
    simpa only [s, t, Finset.card_univ, spinorCoordinate_card] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset SpinorCoordinate))
        (fun i => H.eigenvalues i = c)
  have ht' : t.card = 8 := by omega
  have hps : ∏ i ∈ s, (X - C (H.eigenvalues i)) = (X - C c)^8 := by
    calc
      _ = ∏ _i ∈ s, (X - C c) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := by rw [Finset.prod_const, hs]
  have hpt : ∏ i ∈ t, (X - C (H.eigenvalues i)) = X^8 := by
    calc
      _ = ∏ _i ∈ t, (X : Polynomial ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [(hvals i).resolve_right (Finset.mem_filter.mp hi).2, map_zero, sub_zero]
      _ = _ := by rw [Finset.prod_const, ht']
  rw [H.charpoly_eq]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => H.eigenvalues i = c)]
  change (∏ i ∈ s, (X - C (H.eigenvalues i))) * (∏ i ∈ t, (X - C (H.eigenvalues i))) = _
  rw [hps, hpt, mul_comm]

end AlbertSequential.NativeAnalysis
