/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeNewtonCubic

/-! A positive native element with trace T and monic cubic
x³-Tx²+Bx-Ce=0 lies above (C/B)e when B>0. Only x is diagonalized;
no simultaneous diagonalization of a preparation state is assumed. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential.NativeAnalysis
open scoped BigOperators

private theorem coord_sub (x y : Albert) (i : Fin 3) : (x - y).1 i = x.1 i - y.1 i := rfl
private theorem coord_add (x y : Albert) (i : Fin 3) : (x + y).1 i = x.1 i + y.1 i := rfl
private theorem coord_smul (r : ℝ) (x : Albert) (i : Fin 3) : (r • x).1 i = r * x.1 i := rfl
private theorem coord_zero (i : Fin 3) : (0 : Albert).1 i = 0 := rfl
private theorem off_sub (x y : Albert) (i : Fin 3) : (x - y).2 i = x.2 i - y.2 i := rfl
private theorem off_smul (r : ℝ) (x : Albert) (i : Fin 3) : (r • x).2 i = r • x.2 i := rfl

theorem nativeAutomorphism_positive (g : NativeAlbertAutomorphism) (x : Albert)
    (hx : IsPositive x) : IsPositive (g.linearEquiv x) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨g.linearEquiv y, g.preserves_product y y⟩

theorem diagonal_positive_of_entries (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i) :
    IsPositive (diagonalElement d) := by
  refine ⟨diagonalElement (fun i => Real.sqrt (d i)), ?_⟩
  rw [diagonal_square]
  congr 1
  funext i
  exact (Real.sq_sqrt (hd i)).symm

theorem diagonal_sub_scalar_unit (d : Fin 3 → ℝ) (c : ℝ) :
    diagonalElement d - c • albertUnit = diagonalElement (fun i => d i - c) := by
  apply Prod.ext
  · funext i
    rw [coord_sub, coord_smul]
    change d i - c * 1 = d i - c
    rw [mul_one]
  · funext i
    rw [off_sub, off_smul]
    change 0 - c • (0 : Octonion) = 0
    rw [smul_zero, sub_self]

theorem scalar_monicCubic_lower (T B C t : ℝ) (hB : 0 < B) (hupper : t ≤ T)
    (hcubic : t ^ 3 - T * t ^ 2 + B * t - C = 0) : C / B ≤ t := by
  apply (div_le_iff₀ hB).mpr
  have hnegative : t ^ 2 * (t - T) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (sub_nonpos.mpr hupper)
  nlinarith

theorem native_positive_lower_of_monicCubic (x : Albert) (hx : IsPositive x)
    (T B C : ℝ) (hT : albertTrace x = T) (hB : 0 < B)
    (hcubic : jordanMul x (jordanMul x x) - T • jordanMul x x + B • x - C • albertUnit = 0) :
    IsPositive (x - (C / B) • albertUnit) := by
  obtain ⟨g, d, hd⟩ := nativeDiagonalization x
  have hdiag : IsPositive (diagonalElement d) := by
    rw [← hd]
    exact nativeAutomorphism_positive g x hx
  have hnonneg (i : Fin 3) : 0 ≤ d i := by
    have h := tracePairing_positive_nonnegative (diagAtom i) (diagonalElement d)
      (isPositive_idempotent _ (diagAtom_isAtom i).1) hdiag
    rwa [tracePairing_diagAtom] at h
  have hsum : (∑ i : Fin 3, d i) = T := by
    rw [← diagonal_trace, ← hd, g.preserves_trace, hT]
  have hupper (i : Fin 3) : d i ≤ T := by
    calc
      d i ≤ ∑ k : Fin 3, d k := Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
      _ = T := hsum
  have hc := congrArg g.linearEquiv hcubic
  simp only [map_sub, map_add, map_smul, map_zero, g.preserves_product,
    g.preserves_unit, hd, diagonal_product] at hc
  have hlower (i : Fin 3) : C / B ≤ d i := by
    have hi := congrArg (fun y : Albert => y.1 i) hc
    rw [coord_sub, coord_add, coord_sub, coord_smul, coord_smul, coord_smul, coord_zero] at hi
    simp only [diagonalElement, albertUnit, mul_one] at hi
    change d i * (d i * d i) - T * (d i * d i) + B * d i - C = 0 at hi
    apply scalar_monicCubic_lower T B C (d i) hB (hupper i)
    nlinarith [hi]
  have hpositive : IsPositive (diagonalElement (fun i => d i - C / B)) :=
    diagonal_positive_of_entries _ (fun i => sub_nonneg.mpr (hlower i))
  have hmap : g.linearEquiv (x - (C / B) • albertUnit) = diagonalElement (fun i => d i - C / B) := by
    rw [map_sub, map_smul, g.preserves_unit, hd, diagonal_sub_scalar_unit]
  have hback := nativeAutomorphism_positive (nativeAutomorphismInverse g) _ hpositive
  rw [← hmap] at hback
  simpa only [nativeAutomorphismInverse_apply, LinearEquiv.symm_apply_apply] using hback

end AlbertSequential.NativeAnalysis
