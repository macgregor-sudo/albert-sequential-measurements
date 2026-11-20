/- SPDX-License-Identifier: Apache-2.0 -/
module
public import OptimalSpectralFrames
public import Mathlib.LinearAlgebra.Trace

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem matrix_trace_of_idempotent {A : Matrix n n ℂ} (h : A*A=A) :
    A.trace = (A.rank : ℂ) := by
  have he : IsIdempotentElem A.toLin' := by
    change A.toLin'.comp A.toLin' = A.toLin'
    rw [← Matrix.toLin'_mul, h]
  exact (A.trace_toLin'_eq.symm).trans ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr he).trace

/-- The unused no-outcome space has exactly the number of ancillary slots
left after allocating one slot per non-idempotent eigenvalue. -/
theorem reducedSpectralFrame_residual_rank (U : unitary (Matrix n n ℂ)) (a : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, a i ≤ 1) (e : {i // a i - a i * a i ≠ 0} ↪ m) :
    let s := fun i => Real.sqrt (a i)
    let c := fun i => Real.sqrt (1-a i)
    let V := reducedSpectralFrame U a e s c
    let W := reducedSpectralFrame U a e c (fun i => -s i)
    (1 - V * Vᴴ - W * Wᴴ).rank = Fintype.card m - Fintype.card {i // a i - a i * a i ≠ 0} := by
  classical
  intro s c V W
  let J : Matrix (n ⊕ m) n ℂ := fromRows 1 0
  let Q := 1 - V * Vᴴ - W * Wᴴ
  obtain ⟨hV,hW,hVW,hVJ,hWJ,hJ⟩ := reducedSpectralFrame_data U a ha hc e
  have hQ := (sharpDilationResidual_of_partialFrames J V W _ _ hV hW hVW hVJ hWJ hJ).2.1
  have htrace (f : n → ℝ) : (unitaryRealDiagonal U f).trace = ∑ i, (f i : ℂ) := by
    unfold unitaryRealDiagonal
    rw [Matrix.trace_map]
    simp
  have hsum : (Vᴴ * V).trace + (Wᴴ * W).trace =
      (Fintype.card n : ℂ) + (Fintype.card {i // a i - a i*a i ≠ 0} : ℂ) := by
    change ((reducedSpectralFrame U a e s c)ᴴ * _).trace + ((reducedSpectralFrame U a e c (fun i => -s i))ᴴ * _).trace = _
    dsimp only [V,W]
    rw [reducedSpectralFrame_cross, reducedSpectralFrame_cross, htrace, htrace, ← Finset.sum_add_distrib]
    have hslot (i : n) := reducedSpectralFrame_scalar (a i) (ha i) (hc i)
    have hcard : (Fintype.card {i // a i - a i*a i ≠ 0} : ℂ) =
        ∑ i, if a i-a i*a i ≠ 0 then 1 else 0 := by
      rw [Fintype.card_subtype, Finset.sum_boole]
    have hones : (Fintype.card n : ℂ) = ∑ _ : n, (1 : ℂ) := by simp
    rw [hcard, hones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [s,c,defectIndicator]
    rw [(hslot i).1, (hslot i).2.1]
    by_cases h0 : a i = 0
    · simp [h0]
    by_cases h1 : a i = 1
    · simp [h1]
    have hd : a i-a i*a i ≠ 0 := by
      rw [show a i-a i*a i = a i*(1-a i) by ring]
      exact mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
    simp [h0,h1,hd]
  have h := matrix_trace_of_idempotent hQ
  change (1 - V * Vᴴ - W * Wᴴ).trace = (Q.rank : ℂ) at h
  rw [Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_one,Matrix.trace_mul_comm V,Matrix.trace_mul_comm W,
    Fintype.card_sum, Nat.cast_add] at h
  have he : (Q.rank : ℂ) + (Fintype.card {i // a i-a i*a i ≠ 0} : ℂ) = Fintype.card m := by
    linear_combination -hsum - h
  have he' : Q.rank + Fintype.card {i // a i-a i*a i ≠ 0} = Fintype.card m := by exact_mod_cast he
  change Q.rank = _
  omega

end AlbertSequential
