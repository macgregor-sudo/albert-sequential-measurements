/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeAlbertLaws
public import OctonionGeometry
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-! # Ingredients of `thm:glennie`, general statements

* The octonion part of the defect computation: with `B(u) = iu − ui`,
  `B(uv) − B(u)v − uB(v) = −3[i,u,v]` for all octonions (`octAdI_leibniz_defect`); for
  `u, v ⊥ ℂ_i`, `[i,u,v] = −2i·π⊥(uv)` (`assoc_i_of_perp`), `π⊥(uv)` is orthogonal to
  `u, iu, v, iv` (`projPerp_orth`), and `|π⊥(uv)|² = |u|²|v|² − |h(u,v)|²` with
  `h(u,v) = −π_ℂ(uv)` (`normSq_projPerp`), hence `|[i,u,v]|² = 4(|u|²|v|² − |h(u,v)|²)`
  (`normSq_assoc_i`).
* The scalar part of the constant: with `β = g_AB g_BC g_CA`, `o_xy = |g_xy|²` and the
  eight-word value `T₁ = 3O − β² + β̄(1 − Σo)`, one has `Im T₁ = −N_W · Im β` with
  `N_W = 1 − Σo + 2 Re β` (`window_T1_im`), and `T₁ + T₂ = 2i·Im T₁` for `T₂ = −conj T₁`; so
  `Tr Y = −192(T₁+T₂) = 384 i N_W Im β` and `λ = 128 N_W Im β` (`window_lambda`).
  The eight-word trace expansion itself (traces of products of rank-one projections) is the
  rank-one product rule `rankOne_mul` together with `trace_rankOne`.

Conventions: `octI = (i,0)`, `ℂ_i = span(1, i)` = quaternion coordinates `re, imI` of the first
component; `π_ℂ`, `π⊥` the orthogonal projections. -/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

/-! ## Octonions -/

theorem oct_ext' {x y : Octonion} (h1 : x.1.re = y.1.re) (h2 : x.1.imI = y.1.imI)
    (h3 : x.1.imJ = y.1.imJ) (h4 : x.1.imK = y.1.imK) (h5 : x.2.re = y.2.re)
    (h6 : x.2.imI = y.2.imI) (h7 : x.2.imJ = y.2.imJ) (h8 : x.2.imK = y.2.imK) : x = y := by
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

@[simp] theorem oct_add_fst (x y : Octonion) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem oct_add_snd (x y : Octonion) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem oct_sub_fst (x y : Octonion) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem oct_sub_snd (x y : Octonion) : (x - y).2 = x.2 - y.2 := rfl
@[simp] theorem oct_smul_fst (r : ℝ) (x : Octonion) : (r • x).1 = r • x.1 := rfl
@[simp] theorem oct_smul_snd (r : ℝ) (x : Octonion) : (r • x).2 = r • x.2 := rfl

@[simp] theorem oct_mul_fst (x y : Octonion) : (octonionMul x y).1 = x.1 * y.1 - star y.2 * x.2 := rfl
@[simp] theorem oct_mul_snd (x y : Octonion) : (octonionMul x y).2 = y.2 * x.1 + x.2 * star y.1 := rfl
@[simp] theorem oct_conj_fst (x : Octonion) : (octonionConj x).1 = star x.1 := rfl
@[simp] theorem oct_conj_snd (x : Octonion) : (octonionConj x).2 = -x.2 := rfl
@[simp] theorem oct_neg_fst (x : Octonion) : (-x).1 = -x.1 := rfl
@[simp] theorem oct_neg_snd (x : Octonion) : (-x).2 = -x.2 := rfl
@[simp] theorem oct_zero_fst : (0 : Octonion).1 = 0 := rfl
@[simp] theorem oct_zero_snd : (0 : Octonion).2 = 0 := rfl
@[simp] theorem oct_scalar_fst (r : ℝ) : (octonionScalar r).1 = ⟨r, 0, 0, 0⟩ := rfl
@[simp] theorem oct_scalar_snd (r : ℝ) : (octonionScalar r).2 = 0 := rfl
@[simp] theorem octI_fst : octI.1 = ⟨0, 1, 0, 0⟩ := rfl
@[simp] theorem octI_snd : octI.2 = 0 := rfl
theorem oct_real_eq (x : Octonion) : octonionReal x = x.1.re := rfl

/-- `B(u) = iu − ui` (entrywise `ad_i`). -/
def octAdI (u : Octonion) : Octonion := octonionMul octI u - octonionMul u octI

/-- The associator `[a,b,c] = (ab)c − a(bc)`. -/
def octAssoc (a b c : Octonion) : Octonion :=
  octonionMul (octonionMul a b) c - octonionMul a (octonionMul b c)

/-- `π_ℂ`, the orthogonal projection onto `ℂ_i = span(1, i)`. -/
def projC (u : Octonion) : Octonion := (⟨u.1.re, u.1.imI, 0, 0⟩, 0)

@[simp] theorem projC_fst (u : Octonion) : (projC u).1 = ⟨u.1.re, u.1.imI, 0, 0⟩ := rfl
@[simp] theorem projC_snd (u : Octonion) : (projC u).2 = 0 := rfl

/-- `π⊥ = 1 − π_ℂ`. -/
def projPerp (u : Octonion) : Octonion := u - projC u

/-- `u ⊥ ℂ_i`. -/
def InCperp (u : Octonion) : Prop := u.1.re = 0 ∧ u.1.imI = 0

/-- `|h(u,v)|²`, `h(u,v) = −π_ℂ(uv)`. -/
def hNormSq (u v : Octonion) : ℝ :=
  (octonionMul u v).1.re ^ 2 + (octonionMul u v).1.imI ^ 2

/-- Leibniz defect of `ad_i` on octonions: `B(uv) − B(u)v − uB(v) = −3[i,u,v]`. -/
theorem octAdI_leibniz_defect (u v : Octonion) :
    octAdI (octonionMul u v) - octonionMul (octAdI u) v - octonionMul u (octAdI v) =
      (-3 : ℝ) • octAssoc octI u v := by
  apply oct_ext' <;>
    simp [octAdI, octAssoc, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, oct_add_fst, oct_add_snd, oct_sub_fst, oct_sub_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

/-- For `u, v ⊥ ℂ_i`: `[i,u,v] = −2i·π⊥(uv)`. -/
theorem assoc_i_of_perp (u v : Octonion) (hu : InCperp u) (hv : InCperp v) :
    octAssoc octI u v = (-2 : ℝ) • octonionMul octI (projPerp (octonionMul u v)) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  apply oct_ext' <;>
    simp [octAssoc, projPerp, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, projC_fst, projC_snd, oct_add_fst, oct_add_snd, oct_sub_fst, oct_sub_snd, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hu1, hu2, hv1, hv2] <;> ring

theorem octNormSq_coords (x : Octonion) :
    octNormSq x = x.1.re ^ 2 + x.1.imI ^ 2 + x.1.imJ ^ 2 + x.1.imK ^ 2 +
      x.2.re ^ 2 + x.2.imI ^ 2 + x.2.imJ ^ 2 + x.2.imK ^ 2 := by
  simp [octNormSq, octDot, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, Quaternion.re_mul]
  ring

theorem octDot_coords (x y : Octonion) :
    octDot x y = x.1.re * y.1.re + x.1.imI * y.1.imI + x.1.imJ * y.1.imJ + x.1.imK * y.1.imK +
      x.2.re * y.2.re + x.2.imI * y.2.imI + x.2.imJ * y.2.imJ + x.2.imK * y.2.imK := by
  simp [octDot, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, Quaternion.re_mul]
  ring

/-- `|π⊥(uv)|² = |u|²|v|² − |h(u,v)|²` for `u, v ⊥ ℂ_i`. -/
theorem normSq_projPerp (u v : Octonion) (hu : InCperp u) (hv : InCperp v) :
    octNormSq (projPerp (octonionMul u v)) = octNormSq u * octNormSq v - hNormSq u v := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  rw [octNormSq_coords, octNormSq_coords, octNormSq_coords]
  simp [hNormSq, projPerp, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, projC_fst, projC_snd, oct_sub_fst, oct_sub_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hu1, hu2, hv1, hv2]
  ring

/-- `π⊥(uv)` is orthogonal to `u, iu, v, iv` (`u, v ⊥ ℂ_i`). -/
theorem projPerp_orth (u v : Octonion) (hu : InCperp u) (hv : InCperp v) :
    octDot (projPerp (octonionMul u v)) u = 0 ∧
      octDot (projPerp (octonionMul u v)) (octonionMul octI u) = 0 ∧
      octDot (projPerp (octonionMul u v)) v = 0 ∧
      octDot (projPerp (octonionMul u v)) (octonionMul octI v) = 0 := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [octDot_coords] <;>
    simp [projPerp, oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, projC_fst, projC_snd, oct_sub_fst, oct_sub_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hu1, hu2, hv1, hv2] <;> ring

/-- `|[i,u,v]|² = 4(|u|²|v|² − |h(u,v)|²)` for `u, v ⊥ ℂ_i`. -/
theorem normSq_assoc_i (u v : Octonion) (hu : InCperp u) (hv : InCperp v) :
    octNormSq (octAssoc octI u v) = 4 * (octNormSq u * octNormSq v - hNormSq u v) := by
  rw [← normSq_projPerp u v hu hv, assoc_i_of_perp u v hu hv]
  rw [octNormSq_coords, octNormSq_coords]
  simp [oct_mul_fst, oct_mul_snd, oct_conj_fst, oct_conj_snd, oct_neg_fst, oct_neg_snd, oct_zero_fst, oct_zero_snd, oct_scalar_fst, oct_scalar_snd, octI_fst, octI_snd, oct_real_eq, oct_smul_fst, oct_smul_snd, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

/-! ## The window constant -/

/-- With `β = g₀₁ g₁₂ ḡ₀₂`, `o_xy = |g_xy|²` and `T₁ = 3O − β² + β̄(1 − Σo)` (the value of the
eight-word expansion of `Tr(c_AB c_AC c_BC)`), `Im T₁ = −N_W · Im β`, `N_W = 1 − Σo + 2 Re β`. -/
theorem window_T1_im (g01 g02 g12 : ℂ) :
    let β := g01 * g12 * (starRingEnd ℂ) g02
    let o01 := Complex.normSq g01
    let o02 := Complex.normSq g02
    let o12 := Complex.normSq g12
    let T1 : ℂ := 3 * ((o01 * o02 * o12 : ℝ) : ℂ) - β ^ 2 + (starRingEnd ℂ) β * ((1 - o01 - o02 - o12 : ℝ) : ℂ)
    T1.im = -((1 - o01 - o02 - o12 + 2 * β.re) * β.im) := by
  intro β o01 o02 o12 T1
  simp only [T1, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.conj_re, Complex.conj_im, pow_two]
  norm_num
  ring

/-- `T₂ = −conj T₁` gives `Tr Y = −192(T₁ + T₂) = 384 i N_W Im β` and `λ = Tr Y/(3i) = 128 N_W Im β`;
here as the arithmetic: `−192·(T₁ − conj T₁) = 384 i·(N_W Im β)` when `Im T₁ = −N_W Im β`. -/
theorem window_lambda (T1 : ℂ) (NW imβ : ℝ) (h : T1.im = -(NW * imβ)) :
    (-192 : ℂ) * (T1 - (starRingEnd ℂ) T1) = 384 * Complex.I * ((NW * imβ : ℝ) : ℂ) ∧
      (384 * Complex.I * ((NW * imβ : ℝ) : ℂ)) / (3 * Complex.I) = ((128 * NW * imβ : ℝ) : ℂ) := by
  constructor
  · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h] <;> ring
  · have hI : (3 : ℂ) * Complex.I ≠ 0 := by simp
    field_simp
    push_cast
    ring

/-! ## Rank-one products (the eight-word trace expansion) -/

open Matrix in
/-- `(u v*)(w z*) = (v*·w) u z*`. -/
theorem rankOne_mul (u v w z : Fin 3 → ℂ) :
    vecMulVec u v * vecMulVec w z = (v ⬝ᵥ w) • vecMulVec u z := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

open Matrix in
theorem trace_rankOne (u z : Fin 3 → ℂ) : (vecMulVec u z).trace = z ⬝ᵥ u := by
  simp [Matrix.trace, vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

end

end AlbertSequential.AppF
