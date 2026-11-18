module

public import LemmaB.Sources
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Lemma B, part 4: sources and ghost data of `Ξ_x`, the Gram matrix and its determinant

Paper: proof of lem:cer:negative, "The three vectors", "The Gram matrix", "The determinant".
Proved: `𝒬(Ξ_x, Ξ_x) = 4 D̂ α_x (α_x + μ_x)`, `𝒬(Ξ_x, Ξ_y) = -4 D̂ μ m_z`, the determinant of
the Gram matrix of the `Ξ_x` in denominator-free form `-256 D̂³ μ³ m`, and of the `Ξ_x/(2α_x)`
in the paper's form `-4 D̂³ ∏ m_x / ∏ μ_x` (`= -4 D̂³ / ∏ (1 - o_Ax)` when `m_x = 1/o_Ax`).
All under the single hypothesis `τ = 0`.
-/

@[expose] public section

namespace LemmaB

variable {K : Type*} [Field K] (p : Params K)

/-! ### Pairings with the sources (eq:cer:ghost) -/

theorem W_srcg (β : C8 K) (a : K) : W p β (a • gee) = p.Dhat * (a * β 7) := by
  rw [W_smul_right, W_gee]; ring

theorem W_src1 (β : C8 K) (a t : K) :
    W p β (a • gee + t • h1s' p gee) = p.Dhat * (a * β 7 + t * ((p.c1 - 1) * β 7 + β 4)) := by
  simp [h1s', W, eps1, gee, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13,
    Params.A23, Params.Dhat, Params.detM]; ring

theorem W_src2 (β : C8 K) (a t : K) :
    W p β (a • gee + t • h2s' p gee) = p.Dhat * (a * β 7 + t * ((p.c2 - 1) * β 7 + β 5)) := by
  simp [h2s', W, eps2, gee, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13,
    Params.A23, Params.Dhat, Params.detM]; ring

theorem W_src3 (β : C8 K) (a t : K) :
    W p β (a • gee + t • h3s' p gee) = p.Dhat * (a * β 7 + t * ((p.c3 - 1) * β 7 + β 6)) := by
  simp [h3s', W, eps3, gee, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13,
    Params.A23, Params.Dhat, Params.detM]; ring

/-! ### Sources of the three vectors -/

section withTR

variable (hτ : p.tau = 0)
include hτ

theorem src_XiB : src p (XiB p) =
    ![(2 * p.αB) • gee, (2 * p.αB) • gee + (-2 * p.μB) • h2s' p gee,
      (-2 * p.αB) • gee + (2 * p.μC) • h3s' p gee, (-2 * p.αB) • gee + (2 * p.μD) • h1s' p gee] := by
  funext x
  simp only [XiB, src_sub, src_add, src_smul, src_gA, src_kD p hτ, src_kB' p hτ, src_kC' p hτ,
    src_kD' p hτ]
  fin_cases x <;> funext i <;> fin_cases i <;> simp <;> ring

theorem src_XiC : src p (XiC p) =
    ![(2 * p.αC) • gee, (-2 * p.αC) • gee + (2 * p.μB) • h2s' p gee,
      (2 * p.αC) • gee + (-2 * p.μC) • h3s' p gee, (-2 * p.αC) • gee + (2 * p.μD) • h1s' p gee] := by
  funext x
  simp only [XiC, src_sub, src_add, src_smul, src_gA, src_kB p hτ, src_kB' p hτ, src_kC' p hτ,
    src_kD' p hτ]
  fin_cases x <;> funext i <;> fin_cases i <;> simp <;> ring

theorem src_XiD : src p (XiD p) =
    ![(2 * p.αD) • gee, (-2 * p.αD) • gee + (2 * p.μB) • h2s' p gee,
      (-2 * p.αD) • gee + (2 * p.μC) • h3s' p gee, (2 * p.αD) • gee + (-2 * p.μD) • h1s' p gee] := by
  funext x
  simp only [XiD, src_sub, src_add, src_smul, src_gA, src_kC p hτ, src_kB' p hτ, src_kC' p hτ,
    src_kD' p hτ]
  fin_cases x <;> funext i <;> fin_cases i <;> simp <;> ring

end withTR

/-! ### Ghost data `([·]_g, [·]_{χ_{a(w)}})` of the three vectors (no trace relation needed)

Frames `B, C, D` pair with `χ_2, χ_3, χ_1` (coordinates 5, 6, 4). -/

set_option maxHeartbeats 2000000 in
theorem ghost_XiB :
    XiB p 0 7 = 0 ∧ XiB p 1 7 = 2 * p.αB ∧ XiB p 1 5 = -2 * p.αB * p.c2 ∧
    XiB p 2 7 = 0 ∧ XiB p 2 6 = 0 ∧ XiB p 3 7 = 0 ∧ XiB p 3 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [XiB, gA, kD, kB', kC', kD', KB, KC, KD, polar, h1', h2', h3', h1s', h2s', h3s',
      eps1, eps2, eps3, e1v, e2v, e3v, gee, Params.αB, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;> ring

set_option maxHeartbeats 2000000 in
theorem ghost_XiC :
    XiC p 0 7 = 0 ∧ XiC p 1 7 = 0 ∧ XiC p 1 5 = 0 ∧
    XiC p 2 7 = 2 * p.αC ∧ XiC p 2 6 = -2 * p.αC * p.c3 ∧ XiC p 3 7 = 0 ∧ XiC p 3 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [XiC, gA, kB, kB', kC', kD', KB, KC, KD, polar, h1', h2', h3', h1s', h2s', h3s',
      eps1, eps2, eps3, e1v, e2v, e3v, gee, Params.αC, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;> ring

set_option maxHeartbeats 2000000 in
theorem ghost_XiD :
    XiD p 0 7 = 0 ∧ XiD p 1 7 = 0 ∧ XiD p 1 5 = 0 ∧
    XiD p 2 7 = 0 ∧ XiD p 2 6 = 0 ∧ XiD p 3 7 = 2 * p.αD ∧ XiD p 3 4 = -2 * p.αD * p.c1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [XiD, gA, kC, kB', kC', kD', KB, KC, KD, polar, h1', h2', h3', h1s', h2s', h3s',
      eps1, eps2, eps3, e1v, e2v, e3v, gee, Params.αD, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;> ring

/-! ### The Gram matrix -/

/-- The value of the Gram matrix claimed in lem:cer:negative, `0 = B, 1 = C, 2 = D`. -/
def gramXi : Matrix (Fin 3) (Fin 3) K :=
  !![4 * p.Dhat * p.αB * (p.αB + p.μB), -4 * p.Dhat * p.μ * p.mD, -4 * p.Dhat * p.μ * p.mC;
     -4 * p.Dhat * p.μ * p.mD, 4 * p.Dhat * p.αC * (p.αC + p.μC), -4 * p.Dhat * p.μ * p.mB;
     -4 * p.Dhat * p.μ * p.mC, -4 * p.Dhat * p.μ * p.mB, 4 * p.Dhat * p.αD * (p.αD + p.μD)]

theorem gram_Xi (hτ : p.tau = 0) (x y : Fin 3) : Q p (Xi p x) (Xi p y) = gramXi p x y := by
  obtain ⟨b0, b1, b1', b2, b2', b3, b3'⟩ := ghost_XiB p
  obtain ⟨c0, c1, c1', c2, c2', c3, c3'⟩ := ghost_XiC p
  obtain ⟨d0, d1, d1', d2, d2', d3, d3'⟩ := ghost_XiD p
  fin_cases x <;> fin_cases y <;>
    simp only [Xi, gramXi, Q_eq_src, src_XiB p hτ, src_XiC p hτ, src_XiD p hτ,
      Fin.sum_univ_four, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Matrix.of_apply, W_srcg, W_src1, W_src2, W_src3,
      b0, b1, b1', b2, b2', b3, b3', c0, c1, c1', c2, c2', c3, c3', d0, d1, d1', d2, d2', d3, d3'] <;>
    simp only [Params.αB, Params.αC, Params.αD, Params.μ, Params.μB, Params.μC, Params.μD] <;> ring

/-- The Gram matrix of `Ξ_B, Ξ_C, Ξ_D` under `𝒬`. -/
def gramMatrix : Matrix (Fin 3) (Fin 3) K := Matrix.of fun x y => Q p (Xi p x) (Xi p y)

theorem gramMatrix_eq (hτ : p.tau = 0) : gramMatrix p = gramXi p := by
  ext x y; exact gram_Xi p hτ x y

/-- Denominator-free determinant identity: `det = -256 D̂³ μ³ m`. -/
theorem det_gramXi : (gramXi p).det = -256 * p.Dhat ^ 3 * p.μ ^ 3 * p.m := by
  rw [Matrix.det_fin_three]
  simp [gramXi, Params.αB, Params.αC, Params.αD, Params.μ, Params.m, Params.μB, Params.μC,
    Params.μD]
  ring

theorem det_gramMatrix (hτ : p.tau = 0) :
    (gramMatrix p).det = -256 * p.Dhat ^ 3 * p.μ ^ 3 * p.m := by
  rw [gramMatrix_eq p hτ, det_gramXi]

/-- The `α_x`, indexed `0 = B, 1 = C, 2 = D`. -/
def αv : Fin 3 → K := ![p.αB, p.αC, p.αD]

/-- The paper's normalised determinant: for `E_x = Ξ_x/(2α_x)`,
`det Gram(E) = -4 D̂³ ∏_x m_x / ∏_x μ_x` (which is `-4 D̂³/∏(1 - o_Ax)` for `m_x = 1/o_Ax`). -/
theorem det_gram_normalised (hτ : p.tau = 0) (h2 : (2 : K) ≠ 0) (hB : p.μB ≠ 0) (hC : p.μC ≠ 0)
    (hD : p.μD ≠ 0) :
    (Matrix.of fun x y => Q p ((2 * αv p x)⁻¹ • Xi p x) ((2 * αv p y)⁻¹ • Xi p y)).det =
      -4 * p.Dhat ^ 3 * (p.mB * p.mC * p.mD) / (p.μB * p.μC * p.μD) := by
  simp only [Q_smul_left, Q_smul_right, gram_Xi p hτ]
  rw [Matrix.det_fin_three]
  simp [gramXi, αv, Params.αB, Params.αC, Params.αD, Params.μ, Params.μB, Params.μC, Params.μD]
  simp only [Params.μB, Params.μC, Params.μD] at hB hC hD
  field_simp
  ring

end LemmaB
