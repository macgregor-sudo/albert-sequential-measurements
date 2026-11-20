/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThreeAtomAndFourPoint
public import GramFactor
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quaternionic Pairs on a Line of Double-Pair Traces (`prop:cer:quatpair`)

Formalizes `prop:cer:quatpair` (a), (b), (c):
- (a) For four atoms `p : Fin 4 → Albert` with `0 < fourPointInvariant p`, `tVec p ∈ planePi o R`,
  and `M_mat o R (tVec p)` is positive definite (`M.PosDef`, `M.PosSemidef`, `0 < M.det`,
  positive leading principal minors, and `0 < Dtet o R (tVec p)`).
- (b) For any `t ∈ planePi o R` with `(M_mat o R t).PosSemidef` and `Dtet o R t = 0`, explicit
  Cholesky vectors in `ℍ³` give four atoms `q : Fin 4 → Albert` inside
  `standardQuaternionicWindow.subalgebra` realizing all 13 traces `(o, R, t)`.
- (c) For every direction `v ≠ 0` with `v 0 + v 1 + v 2 = 0`, the line `s ↦ tVec p + s • v`
  meets the boundary of `Π_+` on both sides of `0`, yielding `s_+ > 0 > s_-` and `lam ∈ (0, 1)`
  with `tVec p = lam • t^+ + (1 - lam) • t^-` and matching quaternionic quadruples `qPlus, qMinus`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace AlbertSequential.MatchingModels

open scoped Matrix Topology
open AlbertSequential

/-! ## Local Helpers -/

private theorem albert_ext {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (hu0 : x.2 0 = y.2 0) (hu1 : x.2 1 = y.2 1) (hu2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext i <;> fin_cases i
  · exact hd0
  · exact hd1
  · exact hd2
  · exact hu0
  · exact hu1
  · exact hu2

@[simp] private theorem quat_zero_re : (0 : Quaternion ℝ).re = 0 := rfl
@[simp] private theorem quat_one_re : (1 : Quaternion ℝ).re = 1 := rfl
@[simp] private theorem quat_add_re (a b : Quaternion ℝ) : (a + b).re = a.re + b.re := rfl
@[simp] private theorem quat_sub_re (a b : Quaternion ℝ) : (a - b).re = a.re - b.re := rfl
@[simp] private theorem quat_neg_re (a : Quaternion ℝ) : (-a).re = -a.re := rfl
@[simp] private theorem quat_smul_re (r : ℝ) (a : Quaternion ℝ) : (r • a).re = r * a.re := rfl
@[simp] private theorem quat_star_re (a : Quaternion ℝ) : (star a).re = a.re := Quaternion.re_star a

private theorem forall_fin3 (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i
  | 0 => h0 | 1 => h1 | 2 => h2

private theorem forall_fin4 (P : Fin 4 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ i, P i
  | 0 => h0 | 1 => h1 | 2 => h2 | 3 => h3

private theorem quat_re_mul_comm (x y : Quaternion ℝ) : (x * y).re = (y * x).re := by
  simp only [Quaternion.re_mul]; ring

private theorem quat_real_mul_left (r : ℝ) (q : Quaternion ℝ) :
    (⟨r, 0, 0, 0⟩ : Quaternion ℝ) * q = r • q := by
  ext <;> simp

private theorem quat_real_mul_right (q : Quaternion ℝ) (r : ℝ) :
    q * (⟨r, 0, 0, 0⟩ : Quaternion ℝ) = r • q := by
  ext <;> simp [mul_comm]

private theorem quat_ofReal_eq_smul (r : ℝ) :
    (⟨r, 0, 0, 0⟩ : Quaternion ℝ) = r • (1 : Quaternion ℝ) := by
  ext <;> simp

private theorem quat_real_star (r : ℝ) :
    star (⟨r, 0, 0, 0⟩ : Quaternion ℝ) = ⟨r, 0, 0, 0⟩ := by
  ext <;> simp

private theorem quat_real_normSq (r : ℝ) :
    (star (⟨r, 0, 0, 0⟩ : Quaternion ℝ) * ⟨r, 0, 0, 0⟩).re = r ^ 2 := by
  rw [quat_real_star]
  simp only [Quaternion.re_mul, mul_zero, sub_zero]
  ring

private theorem quatNormSq_eq_mul_star_re (q : Quaternion ℝ) :
    (q * star q).re = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-! ## Section 1: Plane `Π`, Matrix `M(t)`, and Statistic `D_tet(t)` -/

/-- Right-hand side `τ(o, R)` of the rank-three four-atom trace relation (`eq:fp:tracerel`). -/
def tauOf (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  1 / 2
    - 1 / 2 * (o 0 1 + o 0 2 + o 0 3 + o 1 2 + o 1 3 + o 2 3)
    + 1 / 2 * (o 0 1 * o 2 3 + o 0 2 * o 1 3 + o 0 3 * o 1 2)
    + R 0 1 2 + R 0 1 3 + R 0 2 3 + R 1 2 3

/-- The affine plane `Π = {t ∈ ℝ³ : t₁ + t₂ + t₃ = τ(o, R)}`. -/
def planePi (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) : Set (Fin 3 → ℝ) :=
  {t | t 0 + t 1 + t 2 = tauOf o R}

/-- The vector `t^𝕁 = (t₁, t₂, t₃)` of native double-pair traces. -/
def tVec (p : Fin 4 → Albert) : Fin 3 → ℝ :=
  ![fpDoublePair1 p, fpDoublePair2 p, fpDoublePair3 p]

def tetraC1 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  R 0 1 2 / Real.sqrt (o 0 1 * o 1 2 * o 2 0)

def tetraC2 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  R 0 2 3 / Real.sqrt (o 0 2 * o 2 3 * o 3 0)

def tetraC3 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  R 0 3 1 / Real.sqrt (o 0 3 * o 3 1 * o 1 0)

def tetraC4 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  R 1 2 3 / Real.sqrt (o 1 2 * o 2 3 * o 3 1)

def tetraK12 (o : Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  tetraQOfTraces t 0 1 2 3 / Real.sqrt (o 0 1 * o 1 2 * o 2 3 * o 3 0)

def tetraK23 (o : Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  tetraQOfTraces t 0 2 3 1 / Real.sqrt (o 0 2 * o 2 3 * o 3 1 * o 1 0)

def tetraK31 (o : Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  tetraQOfTraces t 0 3 1 2 / Real.sqrt (o 0 3 * o 3 1 * o 1 2 * o 2 0)

/-- Symmetric `3 × 3` matrix `M(t)` of (`eq:fp:D`) at base `A = 0` and order `(1, 2, 3)`. -/
def M_mat (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let c1 := tetraC1 o R
  let c2 := tetraC2 o R
  let c3 := tetraC3 o R
  let M11 := 1 - c1 ^ 2
  let M22 := 1 - c2 ^ 2
  let M33 := 1 - c3 ^ 2
  let M12 := c1 * c2 - tetraK12 o t
  let M23 := c2 * c3 - tetraK23 o t
  let M13 := c3 * c1 - tetraK31 o t
  Matrix.of ![![M11, M12, M13], ![M12, M22, M23], ![M13, M23, M33]]

def tetraS (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  let c1 := tetraC1 o R
  let c2 := tetraC2 o R
  let c3 := tetraC3 o R
  let M := M_mat o R t
  c1 * c2 * c3 - c1 * M 1 2 - c2 * M 0 2 - c3 * M 0 1

/-- Tetrahedron statistic `D_tet(o, R, t)` at base `0` and order `(1, 2, 3)`. -/
def Dtet (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) : ℝ :=
  fpTetraDtet 1 o R t

theorem Dtet_eq_det_sub_sq (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    Dtet o R t = (M_mat o R t).det - (tetraC4 o R - tetraS o R t) ^ 2 := by
  rfl

theorem M_mat_isSymm (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    (M_mat o R t).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem M_mat_isHermitian (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    (M_mat o R t).IsHermitian := by
  ext i j
  simpa [Matrix.conjTranspose_apply] using congrFun (congrFun (M_mat_isSymm o R t).eq i) j

theorem M_mat_00 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    M_mat o R t 0 0 = 1 - (tetraC1 o R) ^ 2 := rfl
theorem M_mat_11 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    M_mat o R t 1 1 = 1 - (tetraC2 o R) ^ 2 := rfl
theorem M_mat_22 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    M_mat o R t 2 2 = 1 - (tetraC3 o R) ^ 2 := rfl
theorem M_mat_01 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    M_mat o R t 0 1 = tetraC1 o R * tetraC2 o R - tetraK12 o t := rfl
theorem M_mat_12 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    M_mat o R t 1 2 = tetraC2 o R * tetraC3 o R - tetraK23 o t := rfl
theorem M_mat_02 (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t : Fin 3 → ℝ) :
    M_mat o R t 0 2 = tetraC3 o R * tetraC1 o R - tetraK31 o t := rfl

theorem tVec_mem_planePi (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    tVec p ∈ planePi (fpOverlap p) (fpTriangle p) := by
  change tVec p 0 + tVec p 1 + tVec p 2 = tauOf (fpOverlap p) (fpTriangle p)
  simp only [tVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  exact albert_fourAtom_trace_relation p hp

/-! ## Section 2: Strict Bounds and Positive Definiteness (`prop:cer:quatpair` (a)) -/

/-- When `0 < fourPointInvariant p`, every distinct pair of atoms has overlap strictly in `(0, 1)`. -/
theorem overlap_pos_lt_one_of_fourPoint_pos (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) {i j : Fin 4} (hij : i ≠ j) :
    0 < fpOverlap p i j ∧ fpOverlap p i j < 1 := by
  obtain ⟨h0, h1⟩ := atom_tracePairing_bounds (p i) (p j) (hp i) (hp j)
  refine ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_⟩
  · intro heq
    have hmul : jordanMul (p i) (p j) = 0 :=
      (atom_tracePairing_eq_zero_iff (p i) (p j) (hp i) (hp j)).mp heq.symm
    obtain ⟨Q, hQ⟩ := lemma_A_degenerate p hp ⟨i, j, hij, Or.inr hmul⟩
    have hz := lemma_A_zero_of_quat Q p hp hQ
    linarith
  · intro heq
    have heqp : p i = p j :=
      (atom_tracePairing_eq_one_iff (p i) (p j) (hp i) (hp j)).mp heq
    obtain ⟨Q, hQ⟩ := lemma_A_degenerate p hp ⟨i, j, hij, Or.inl heqp⟩
    have hz := lemma_A_zero_of_quat Q p hp hQ
    linarith

/-- When `0 < fourPointInvariant p`, `N(p_A + p_B + p_C) = 1 - o_AB - o_AC - o_BC + 2 R_ABC > 0`. -/
theorem tripleNorm_pos_of_fourPoint_pos (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    0 < 1 - fpOverlap p 0 1 - fpOverlap p 0 2 - fpOverlap p 1 2 + 2 * fpTriangle p 0 1 2 := by
  have h01 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (0 : Fin 4) ≠ 1)
  have h02 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (0 : Fin 4) ≠ 2)
  have h03 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (0 : Fin 4) ≠ 3)
  obtain ⟨g, B0, B1, C0, C1, C2, C3, D0, x0, x1, x2, y0, y1, y2, y3, y4,
    hB0, hB1, hC0, _hC2, hC3, _hD0, _hx2, _hy4, hBs, hCs, _hDs, hcfg⟩ :=
    lemma_A_normal p hp h01.1 h01.2 h02.1 h03.1
  let X : Octonion := octonionScalar x0 + x1 • octI + x2 • octJ
  let Y : Octonion := octonionScalar y0 + y1 • octI + y2 • octJ + y3 • octK + y4 • octL
  let q := fun i => g.linearEquiv (p i)
  have hinv : fourPointInvariant q = fourPointInvariant p :=
    fourPointInvariant_automorphism_invariant g p
  have hcfg' : q = sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y := by
    simpa [q, X, Y, sparseFourConfig, octOne_eq_scalar, octonionScalar_eq_smul y0] using hcfg
  have hA_q : fourPointInvariant q =
      B0 ^ 2 * B1 ^ 4 * C0 ^ 2 * C2 ^ 2 * C3 ^ 2 * D0 ^ 2 * x2 ^ 2 * y4 ^ 2 := by
    have hcfg'' : q = sparseFourConfig B0 B1 C0 C1 C2 C3 D0 x0 x1 x2 Y := hcfg'
    rw [hcfg'', sparseFourConfig_fourPointInvariant]
  have hC3_ne : C3 ≠ 0 := by
    intro h0
    rw [h0] at hA_q
    linarith [hinv, hA_q]
  have htr := sparseFourConfigOct_traces B0 B1 C0 C1 C2 C3 D0 X Y
  have ho01_eq : fpOverlap p 0 1 = B0 ^ 2 := by
    have hg01 : fpOverlap q 0 1 = fpOverlap p 0 1 := g.map_tracePairing (p 0) (p 1)
    rw [← hg01, hcfg']; exact htr.1
  have ho02_eq : fpOverlap p 0 2 = C0 ^ 2 := by
    have hg02 : fpOverlap q 0 2 = fpOverlap p 0 2 := g.map_tracePairing (p 0) (p 2)
    rw [← hg02, hcfg']; exact htr.2.1
  have ho12_eq : fpOverlap p 1 2 = (B0 * C0 + B1 * C1) ^ 2 + (B1 * C2) ^ 2 := by
    have hg12 : fpOverlap q 1 2 = fpOverlap p 1 2 := g.map_tracePairing (p 1) (p 2)
    have hI0 : octonionReal octI = 0 := rfl
    have hI1 : octDot octI octI = 1 := by
      rw [octDot_self, octNormSq_eq_coords, octI]
      norm_num
    rw [← hg12, hcfg', htr.2.2.2.1, ← octDot_self]
    simp only [octDot_add_left, octDot_add_right, octDot_smul_left, octDot_smul_right,
      octDot_scalar_left, octonionReal_scalar, hI0, mul_zero,
      octDot_comm octI (octonionScalar _), hI1]
    ring
  have hR012_eq : fpTriangle p 0 1 2 = B0 * C0 * (B0 * C0 + B1 * C1) := by
    have hg012 : fpTriangle q 0 1 2 = fpTriangle p 0 1 2 := by
      unfold fpTriangle
      rw [← g.preserves_product, g.map_tracePairing]
    have hI0 : octonionReal octI = 0 := rfl
    rw [← hg012, hcfg', htr.2.2.2.2.2.2.1, octonionReal_add, octonionReal_scalar,
      octonionReal_smul, octonionReal_add, octonionReal_scalar, octonionReal_smul, hI0]
    ring
  have hid : 1 - fpOverlap p 0 1 - fpOverlap p 0 2 - fpOverlap p 1 2 + 2 * fpTriangle p 0 1 2 =
      B1 ^ 2 * C3 ^ 2 := by
    have hB0_sq : B0 ^ 2 = 1 - B1 ^ 2 := by linarith
    have hC0_sq : C0 ^ 2 = 1 - C1 ^ 2 - C2 ^ 2 - C3 ^ 2 := by linarith
    rw [ho01_eq, ho02_eq, ho12_eq, hR012_eq]
    have h00 : B0 ^ 2 * C0 ^ 2 = (1 - B1 ^ 2) * (1 - C1 ^ 2 - C2 ^ 2 - C3 ^ 2) := by
      rw [hB0_sq, hC0_sq]
    have hpow : (B0 * C0) ^ 2 = B0 ^ 2 * C0 ^ 2 := by ring
    calc
      1 - B0 ^ 2 - C0 ^ 2 - ((B0 * C0 + B1 * C1) ^ 2 + (B1 * C2) ^ 2) +
          2 * (B0 * C0 * (B0 * C0 + B1 * C1))
        = 1 - B0 ^ 2 - C0 ^ 2 + (B0 * C0) ^ 2 - (B1 * C1) ^ 2 - (B1 * C2) ^ 2 := by ring
      _ = 1 - (1 - B1 ^ 2) - (1 - C1 ^ 2 - C2 ^ 2 - C3 ^ 2) +
          (1 - B1 ^ 2) * (1 - C1 ^ 2 - C2 ^ 2 - C3 ^ 2) - (B1 * C1) ^ 2 - (B1 * C2) ^ 2 := by
            rw [hpow, h00, hB0_sq, hC0_sq]
      _ = B1 ^ 2 * C3 ^ 2 := by ring
  rw [hid]
  exact mul_pos (sq_pos_of_pos hB1) (sq_pos_of_ne_zero hC3_ne)

private theorem octDot_scalar_octIm' (r : ℝ) (x : Octonion) :
    octDot (octonionScalar r) (octIm x) = 0 := by
  rw [octDot_scalar_left, octonionReal_octIm, mul_zero]

private theorem octIm_normSq_eq (g : Octonion) :
    octNormSq g - (octonionReal g) ^ 2 = octNormSq (octIm g) := by
  have h : g = octonionScalar (octonionReal g) + octIm g := by simp [octIm]
  conv_lhs =>
    arg 1
    rw [← octDot_self, h, octDot_add_left, octDot_add_right, octDot_add_right,
      octDot_scalar_octIm', octDot_comm (octIm g) (octonionScalar _), octDot_scalar_octIm',
      octDot_scalar_left, octonionReal_scalar]
  rw [octDot_self]
  ring

private theorem octIm_dot_conj (a b : Octonion) :
    octonionReal (octonionMul a (octonionConj b)) - octonionReal a * octonionReal b =
      octDot (octIm a) (octIm b) := by
  have ha : a = octonionScalar (octonionReal a) + octIm a := by simp [octIm]
  have hb : b = octonionScalar (octonionReal b) + octIm b := by simp [octIm]
  conv_lhs =>
    arg 1
    change octDot a b
    rw [ha, hb, octDot_add_left, octDot_add_right, octDot_add_right,
      octDot_scalar_octIm', octDot_comm (octIm a) (octonionScalar _), octDot_scalar_octIm',
      octDot_scalar_left, octonionReal_scalar]
  ring

private theorem octIm_dot_mul (a b : Octonion) :
    octonionReal a * octonionReal b - octonionReal (octonionMul a b) =
      octDot (octIm a) (octIm b) := by
  have ha : a = octonionScalar (octonionReal a) + octIm a := by simp [octIm]
  have hb : b = octonionScalar (octonionReal b) + octIm b := by simp [octIm]
  have him : octonionReal (octonionMul (octIm a) (octIm b)) = -octDot (octIm a) (octIm b) :=
    octonionReal_mul_imag_eq (octonionReal_octIm a) (octonionReal_octIm b)
  conv_lhs =>
    arg 2
    rw [ha, hb, octonionMul_add_left, octonionMul_add_right, octonionMul_add_right,
      octonionMul_scalar_left, octonionMul_scalar_left, octonionMul_scalar_right,
      octonionReal_add, octonionReal_add, octonionReal_add,
      octonionReal_smul, octonionReal_smul, octonionReal_smul,
      octonionReal_scalar, octonionReal_octIm, octonionReal_octIm, him]
  ring

/-- Normalized triangle and pair cosines together with the corresponding imaginary Gram matrix. -/
theorem octonion_holonomy_gram_data
    (o : Fin 4 → Fin 4 → ℝ) (ho_symm : ∀ i j, o i j = o j i)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (hR23 : ∀ i j k, R i j k = R i k j)
    (t : Fin 3 → ℝ) (B0 C0 D0 d e' f : ℝ)
    (hB0 : 0 < B0) (hC0 : 0 < C0) (hD0 : 0 < D0)
    (hd0 : 0 < d) (he0 : 0 < e') (hf0 : 0 < f)
    (g1 g2 g3 : Octonion)
    (ho01 : o 0 1 = B0 ^ 2) (ho02 : o 0 2 = C0 ^ 2) (ho03 : o 0 3 = D0 ^ 2)
    (ho12 : o 1 2 = octNormSq g1) (ho13 : o 1 3 = octNormSq g2) (ho23 : o 2 3 = octNormSq g3)
    (hd2 : d ^ 2 = o 1 2) (he2 : e' ^ 2 = o 1 3) (hf2 : f ^ 2 = o 2 3)
    (hR012 : R 0 1 2 = B0 * C0 * octonionReal g1)
    (hR013 : R 0 1 3 = B0 * D0 * octonionReal g2)
    (hR023 : R 0 2 3 = C0 * D0 * octonionReal g3)
    (hω1 : t 1 + t 2 - t 0 = C0 * D0 * octonionReal (octonionMul g1 (octonionConj g2)))
    (hω2 : t 0 + t 2 - t 1 = B0 * D0 * octonionReal (octonionMul g1 g3))
    (hω3 : t 0 + t 1 - t 2 = B0 * C0 * octonionReal (octonionMul g2 (octonionConj g3))) :
    let w : Fin 3 → Octonion := ![(1 / d) • octIm g1, (1 / f) • octIm g3, (-1 / e') • octIm g2]
    M_mat o R t = Matrix.of (fun i j => octDot (w i) (w j)) ∧
      tetraC1 o R = octonionReal g1 / d ∧ tetraC2 o R = octonionReal g3 / f ∧
      tetraC3 o R = octonionReal g2 / e' ∧
      tetraK12 o t = octonionReal (octonionMul g1 g3) / (d * f) ∧
      tetraK23 o t = octonionReal (octonionMul g2 (octonionConj g3)) / (e' * f) ∧
      tetraK31 o t = octonionReal (octonionMul g1 (octonionConj g2)) / (d * e') := by
  intro w
  have ho12_pos : 0 < o 1 2 := by rw [← hd2]; exact sq_pos_of_pos hd0
  have ho13_pos : 0 < o 1 3 := by rw [← he2]; exact sq_pos_of_pos he0
  have ho23_pos : 0 < o 2 3 := by rw [← hf2]; exact sq_pos_of_pos hf0
  have hnu1 : Real.sqrt (o 0 1 * o 1 2 * o 2 0) = B0 * C0 * d := by
    rw [ho_symm 2 0, ho01, ho02, ← hd2,
      show B0 ^ 2 * d ^ 2 * C0 ^ 2 = (B0 * C0 * d) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg hB0.le hC0.le) hd0.le)
  have hnu2 : Real.sqrt (o 0 2 * o 2 3 * o 3 0) = C0 * D0 * f := by
    rw [ho_symm 3 0, ho02, ho03, ← hf2,
      show C0 ^ 2 * f ^ 2 * D0 ^ 2 = (C0 * D0 * f) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg hC0.le hD0.le) hf0.le)
  have hnu3 : Real.sqrt (o 0 3 * o 3 1 * o 1 0) = B0 * D0 * e' := by
    rw [ho_symm 3 1, ho_symm 1 0, ho01, ho03, ← he2,
      show D0 ^ 2 * e' ^ 2 * B0 ^ 2 = (B0 * D0 * e') ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg hB0.le hD0.le) he0.le)
  have hden12 : Real.sqrt (o 0 1 * o 1 2 * o 2 3 * o 3 0) = B0 * D0 * d * f := by
    rw [ho_symm 3 0, ho01, ho03, ← hd2, ← hf2,
      show B0 ^ 2 * d ^ 2 * f ^ 2 * D0 ^ 2 = (B0 * D0 * d * f) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg hB0.le hD0.le) hd0.le) hf0.le)
  have hden23 : Real.sqrt (o 0 2 * o 2 3 * o 3 1 * o 1 0) = B0 * C0 * e' * f := by
    rw [ho_symm 3 1, ho_symm 1 0, ho01, ho02, ← he2, ← hf2,
      show C0 ^ 2 * f ^ 2 * e' ^ 2 * B0 ^ 2 = (B0 * C0 * e' * f) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg hB0.le hC0.le) he0.le) hf0.le)
  have hden31 : Real.sqrt (o 0 3 * o 3 1 * o 1 2 * o 2 0) = C0 * D0 * d * e' := by
    rw [ho_symm 3 1, ho_symm 2 0, ho02, ho03, ← hd2, ← he2,
      show D0 ^ 2 * e' ^ 2 * d ^ 2 * C0 ^ 2 = (C0 * D0 * d * e') ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg hC0.le hD0.le) hd0.le) he0.le)
  have hQ12 : tetraQOfTraces t 0 1 2 3 = t 0 + t 2 - t 1 := by
    simp [tetraQOfTraces, unorderedPairClass]; ring
  have hQ23 : tetraQOfTraces t 0 2 3 1 = t 0 + t 1 - t 2 := by
    simp [tetraQOfTraces, unorderedPairClass]
  have hQ31 : tetraQOfTraces t 0 3 1 2 = t 1 + t 2 - t 0 := by
    simp [tetraQOfTraces, unorderedPairClass]
  have hc1 : tetraC1 o R = octonionReal g1 / d := by
    unfold tetraC1; rw [hR012, hnu1]; field_simp [hB0.ne', hC0.ne', hd0.ne']
  have hc2 : tetraC2 o R = octonionReal g3 / f := by
    unfold tetraC2; rw [hR023, hnu2]; field_simp [hC0.ne', hD0.ne', hf0.ne']
  have hc3 : tetraC3 o R = octonionReal g2 / e' := by
    unfold tetraC3; rw [hR23 0 3 1, hR013, hnu3]; field_simp [hB0.ne', hD0.ne', he0.ne']
  have hK12 : tetraK12 o t = octonionReal (octonionMul g1 g3) / (d * f) := by
    unfold tetraK12; rw [hQ12, hω2, hden12]; field_simp [hB0.ne', hD0.ne', hd0.ne', hf0.ne']
  have hK23 : tetraK23 o t = octonionReal (octonionMul g2 (octonionConj g3)) / (e' * f) := by
    unfold tetraK23; rw [hQ23, hω3, hden23]; field_simp [hB0.ne', hC0.ne', he0.ne', hf0.ne']
  have hK31 : tetraK31 o t = octonionReal (octonionMul g1 (octonionConj g2)) / (d * e') := by
    unfold tetraK31; rw [hQ31, hω1, hden31]; field_simp [hC0.ne', hD0.ne', hd0.ne', he0.ne']
  have hn1 := octIm_normSq_eq g1
  have hn2 := octIm_normSq_eq g2
  have hn3 := octIm_normSq_eq g3
  have hd13 := octIm_dot_mul g1 g3
  have hd12 := octIm_dot_conj g1 g2
  have hd23 := octIm_dot_conj g2 g3
  simp_rw [← octDot_self] at hn1 hn2 hn3
  have hw0 : w 0 = (1 / d) • octIm g1 := rfl
  have hw1 : w 1 = (1 / f) • octIm g3 := rfl
  have hw2 : w 2 = (-1 / e') • octIm g2 := rfl
  have h00 : M_mat o R t 0 0 = octDot (w 0) (w 0) := by
    rw [M_mat_00, hc1, hw0, octDot_smul_left, octDot_smul_right, ← hn1, octDot_self, ← ho12, ← hd2]
    field_simp [hd0.ne']
  have h11 : M_mat o R t 1 1 = octDot (w 1) (w 1) := by
    rw [M_mat_11, hc2, hw1, octDot_smul_left, octDot_smul_right, ← hn3, octDot_self, ← ho23, ← hf2]
    field_simp [hf0.ne']
  have h22 : M_mat o R t 2 2 = octDot (w 2) (w 2) := by
    rw [M_mat_22, hc3, hw2, octDot_smul_left, octDot_smul_right, ← hn2, octDot_self, ← ho13, ← he2]
    field_simp [he0.ne']
  have h01 : M_mat o R t 0 1 = octDot (w 0) (w 1) := by
    rw [M_mat_01, hc1, hc2, hK12, hw0, hw1, octDot_smul_left, octDot_smul_right, ← hd13]
    field_simp [hd0.ne', hf0.ne']
  have h02 : M_mat o R t 0 2 = octDot (w 0) (w 2) := by
    rw [M_mat_02, hc1, hc3, hK31, hw0, hw2, octDot_smul_left, octDot_smul_right, ← hd12]
    field_simp [hd0.ne', he0.ne']; ring
  have h12 : M_mat o R t 1 2 = octDot (w 1) (w 2) := by
    rw [M_mat_12, hc2, hc3, hK23, hw1, hw2, octDot_smul_left, octDot_smul_right,
      octDot_comm (octIm g3) (octIm g2), ← hd23]
    field_simp [hf0.ne', he0.ne']; ring
  have hsym := (M_mat_isSymm o R t).eq
  refine ⟨?_, hc1, hc2, hc3, hK12, hK23, hK31⟩
  ext i j
  refine forall_fin3 (fun i => ∀ j, M_mat o R t i j = (Matrix.of fun i j => octDot (w i) (w j)) i j)
    ?_ ?_ ?_ i j
  · refine forall_fin3 _ ?_ ?_ ?_
    · simpa only [Matrix.of_apply] using h00
    · simpa only [Matrix.of_apply] using h01
    · simpa only [Matrix.of_apply] using h02
  · refine forall_fin3 _ ?_ ?_ ?_
    · have h := congrFun (congrFun hsym 0) 1; dsimp at h
      simp only [Matrix.of_apply]; rw [h, h01, octDot_comm]
    · simpa only [Matrix.of_apply] using h11
    · simpa only [Matrix.of_apply] using h12
  · refine forall_fin3 _ ?_ ?_ ?_
    · have h := congrFun (congrFun hsym 0) 2; dsimp at h
      simp only [Matrix.of_apply]; rw [h, h02, octDot_comm]
    · have h := congrFun (congrFun hsym 1) 2; dsimp at h
      simp only [Matrix.of_apply]; rw [h, h12, octDot_comm]
    · simpa only [Matrix.of_apply] using h22

/-- Explicit Gram realization of `M_mat` at `tVec p` via the three imaginary octonion
edge-amplitudes (`prop:cer:quatpair` (a), `M = T G' T`). -/
theorem M_mat_posSemidef_of_atoms (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    (M_mat (fpOverlap p) (fpTriangle p) (tVec p)).PosSemidef := by
  have h01 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (0 : Fin 4) ≠ 1)
  have h02 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (0 : Fin 4) ≠ 2)
  have h03 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (0 : Fin 4) ≠ 3)
  have h12 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (1 : Fin 4) ≠ 2)
  have h13 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (1 : Fin 4) ≠ 3)
  have h23 := overlap_pos_lt_one_of_fourPoint_pos p hp hA (by decide : (2 : Fin 4) ≠ 3)
  obtain ⟨g, B0, B1, C0, C1, C2, C3, D0, x0, x1, x2, y0, y1, y2, y3, y4,
    hB0, _hB1, hC0, _hC2, _hC3, hD0, _hx2, _hy4, _hBs, _hCs, _hDs, hcfg⟩ :=
    lemma_A_normal p hp h01.1 h01.2 h02.1 h03.1
  let X : Octonion := octonionScalar x0 + x1 • octI + x2 • octJ
  let Y : Octonion := octonionScalar y0 + y1 • octI + y2 • octJ + y3 • octK + y4 • octL
  let q := fun i => g.linearEquiv (p i)
  have hcfg' : q = sparseFourConfigOct B0 B1 C0 C1 C2 C3 D0 X Y := by
    simpa [q, X, Y, sparseFourConfig, octOne_eq_scalar, octonionScalar_eq_smul y0] using hcfg
  let z := octonionScalar C1 + C2 • octI
  let g1 := octonionScalar (B0 * C0) + B1 • z
  let g2 := octonionScalar (B0 * D0) + B1 • X
  let g3 := octonionScalar (C0 * D0) + octonionMul (octonionConj z) X + C3 • Y
  have htr := sparseFourConfigOct_traces B0 B1 C0 C1 C2 C3 D0 X Y
  have ho_eq : ∀ i j, fpOverlap q i j = fpOverlap p i j := fun i j => g.map_tracePairing (p i) (p j)
  have hR_eq : ∀ i j k, fpTriangle q i j k = fpTriangle p i j k := fun i j k => by
    unfold fpTriangle; rw [← g.preserves_product, g.map_tracePairing]
  have hdp_eq : fpDoublePair1 q = fpDoublePair1 p ∧ fpDoublePair2 q = fpDoublePair2 p ∧
      fpDoublePair3 q = fpDoublePair3 p := by
    refine ⟨?_, ?_, ?_⟩
    · unfold fpDoublePair1
      rw [← g.preserves_product, ← g.preserves_product, g.map_tracePairing]
    · unfold fpDoublePair2
      rw [← g.preserves_product, ← g.preserves_product, g.map_tracePairing]
    · unfold fpDoublePair3
      rw [← g.preserves_product, ← g.preserves_product, g.map_tracePairing]
  have hp01 : fpOverlap p 0 1 = B0 ^ 2 := by rw [← ho_eq 0 1, hcfg']; exact htr.1
  have hp02 : fpOverlap p 0 2 = C0 ^ 2 := by rw [← ho_eq 0 2, hcfg']; exact htr.2.1
  have hp03 : fpOverlap p 0 3 = D0 ^ 2 := by rw [← ho_eq 0 3, hcfg']; exact htr.2.2.1
  have hp12 : fpOverlap p 1 2 = octNormSq g1 := by rw [← ho_eq 1 2, hcfg']; exact htr.2.2.2.1
  have hp13 : fpOverlap p 1 3 = octNormSq g2 := by rw [← ho_eq 1 3, hcfg']; exact htr.2.2.2.2.1
  have hp23 : fpOverlap p 2 3 = octNormSq g3 := by rw [← ho_eq 2 3, hcfg']; exact htr.2.2.2.2.2.1
  have hpR012 : fpTriangle p 0 1 2 = B0 * C0 * octonionReal g1 := by
    rw [← hR_eq 0 1 2, hcfg']; exact htr.2.2.2.2.2.2.1
  have hpR013 : fpTriangle p 0 1 3 = B0 * D0 * octonionReal g2 := by
    rw [← hR_eq 0 1 3, hcfg']; exact htr.2.2.2.2.2.2.2.1
  have hpR023 : fpTriangle p 0 2 3 = C0 * D0 * octonionReal g3 := by
    rw [← hR_eq 0 2 3, hcfg']; exact htr.2.2.2.2.2.2.2.2.1
  have hpω1 : tVec p 1 + tVec p 2 - tVec p 0 =
      C0 * D0 * octonionReal (octonionMul g1 (octonionConj g2)) := by
    dsimp only [tVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← hdp_eq.1, ← hdp_eq.2.1, ← hdp_eq.2.2, hcfg']
    exact htr.2.2.2.2.2.2.2.2.2.2.1
  have hpω2 : tVec p 0 + tVec p 2 - tVec p 1 =
      B0 * D0 * octonionReal (octonionMul g1 g3) := by
    dsimp only [tVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← hdp_eq.1, ← hdp_eq.2.1, ← hdp_eq.2.2, hcfg']
    exact htr.2.2.2.2.2.2.2.2.2.2.2.1
  have hpω3 : tVec p 0 + tVec p 1 - tVec p 2 =
      B0 * C0 * octonionReal (octonionMul g2 (octonionConj g3)) := by
    dsimp only [tVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← hdp_eq.1, ← hdp_eq.2.1, ← hdp_eq.2.2, hcfg']
    exact htr.2.2.2.2.2.2.2.2.2.2.2.2
  let d := Real.sqrt (fpOverlap p 1 2)
  let e' := Real.sqrt (fpOverlap p 1 3)
  let f := Real.sqrt (fpOverlap p 2 3)
  have hM_gram := (octonion_holonomy_gram_data (fpOverlap p) (fpOverlap_symm p)
    (fpTriangle p) (fpTriangle_swap23 p) (tVec p) B0 C0 D0 d e' f
    hB0 hC0 hD0 (Real.sqrt_pos.mpr h12.1) (Real.sqrt_pos.mpr h13.1) (Real.sqrt_pos.mpr h23.1)
    g1 g2 g3 hp01 hp02 hp03 hp12 hp13 hp23
    (Real.sq_sqrt h12.1.le) (Real.sq_sqrt h13.1.le) (Real.sq_sqrt h23.1.le)
    hpR012 hpR013 hpR023 hpω1 hpω2 hpω3).1
  rw [hM_gram]
  let w : Fin 3 → Octonion := ![(1 / d) • octIm g1, (1 / f) • octIm g3, (-1 / e') • octIm g2]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [Matrix.conjTranspose_apply, octDot_comm]
  · intro v
    have hsum : star v ⬝ᵥ (Matrix.of (fun i j => octDot (w i) (w j)) *ᵥ v) =
        octNormSq (v 0 • w 0 + v 1 • w 1 + v 2 • w 2) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.of_apply]
      rw [← octDot_self]
      simp only [octDot_add_left, octDot_add_right, octDot_smul_left, octDot_smul_right]
      rw [octDot_comm (w 1) (w 0), octDot_comm (w 2) (w 0), octDot_comm (w 2) (w 1)]
      ring
    rw [hsum]
    exact octNormSq_nonneg _

/-- Positive definiteness from `PosSemidef` and `0 < det`. -/
theorem posDef_of_posSemidef_det_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hpsd : M.PosSemidef) (hdet : 0 < M.det) : M.PosDef := by
  obtain ⟨B, hB⟩ := exists_realGramFactor hpsd
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.isHermitian
  intro x hx
  have hnonneg : 0 ≤ star x ⬝ᵥ (M *ᵥ x) := hpsd.dotProduct_mulVec_nonneg x
  by_contra hle
  have hzero : star x ⬝ᵥ (M *ᵥ x) = 0 := le_antisymm (not_lt.mp hle) hnonneg
  have hBx : (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = 0 := by
    have h1 : star x ⬝ᵥ (M *ᵥ x) = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
      rw [hB, star_trivial, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    linarith
  have hBx0 : B *ᵥ x = 0 := by
    funext i
    have hsum : ∑ k : Fin n, (B *ᵥ x) k ^ 2 = 0 := by
      simpa [dotProduct, sq] using hBx
    have hi : (B *ᵥ x) i ^ 2 = 0 := by
      have hle_i : (B *ᵥ x) i ^ 2 ≤ ∑ k : Fin n, (B *ᵥ x) k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      linarith [sq_nonneg ((B *ᵥ x) i)]
    exact sq_eq_zero_iff.mp hi
  have hMx0 : M *ᵥ x = 0 := by
    rw [hB, ← Matrix.mulVec_mulVec, hBx0, Matrix.mulVec_zero]
  exact hx (Matrix.eq_zero_of_mulVec_eq_zero hdet.ne' hMx0)

/-- `prop:cer:quatpair` (a): `t^𝕁 ∈ Π`, `0 < D_tet(t^𝕁)`, and `M(t^𝕁)` is positive definite
with strictly positive determinant and leading principal minors. -/
theorem prop_cer_quatpair_a (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    tVec p ∈ planePi (fpOverlap p) (fpTriangle p) ∧
    (M_mat (fpOverlap p) (fpTriangle p) (tVec p)).PosDef ∧
    (M_mat (fpOverlap p) (fpTriangle p) (tVec p)).PosSemidef ∧
    0 < (M_mat (fpOverlap p) (fpTriangle p) (tVec p)).det ∧
    0 < Dtet (fpOverlap p) (fpTriangle p) (tVec p) ∧
    0 < M_mat (fpOverlap p) (fpTriangle p) (tVec p) 0 0 ∧
    0 < M_mat (fpOverlap p) (fpTriangle p) (tVec p) 0 0 *
          M_mat (fpOverlap p) (fpTriangle p) (tVec p) 1 1 -
        (M_mat (fpOverlap p) (fpTriangle p) (tVec p) 0 1) ^ 2 := by
  have hpi := tVec_mem_planePi p hp
  have hpos : ∀ i j, i ≠ j → 0 < fpOverlap p i j := fun i j hij =>
    (overlap_pos_lt_one_of_fourPoint_pos p hp hA hij).1
  have hDacal := fpTetraDtet_atoms 1 p hpos
  have hprod : 0 < fpOverlap p 0 1 * fpOverlap p 0 2 * fpOverlap p 0 3 *
      fpOverlap p 1 2 * fpOverlap p 1 3 * fpOverlap p 2 3 := by
    have h01 := hpos 0 1 (by decide)
    have h02 := hpos 0 2 (by decide)
    have h03 := hpos 0 3 (by decide)
    have h12 := hpos 1 2 (by decide)
    have h13 := hpos 1 3 (by decide)
    have h23 := hpos 2 3 (by decide)
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos h01 h02) h03) h12) h13) h23
  have hD_pos : 0 < Dtet (fpOverlap p) (fpTriangle p) (tVec p) := by
    change 0 < fpTetraDtet 1 (fpOverlap p) (fpTriangle p) (tVec p)
    have hDacal' : fpTetraDtet 1 (fpOverlap p) (fpTriangle p) (tVec p) *
        (fpOverlap p 0 1 * fpOverlap p 0 2 * fpOverlap p 0 3 *
          fpOverlap p 1 2 * fpOverlap p 1 3 * fpOverlap p 2 3) = fourPointInvariant p := by
      simpa [tVec] using hDacal
    nlinarith
  have hdet_pos : 0 < (M_mat (fpOverlap p) (fpTriangle p) (tVec p)).det := by
    have hEq := Dtet_eq_det_sub_sq (fpOverlap p) (fpTriangle p) (tVec p)
    nlinarith [sq_nonneg (tetraC4 (fpOverlap p) (fpTriangle p) -
      tetraS (fpOverlap p) (fpTriangle p) (tVec p))]
  have hpsd := M_mat_posSemidef_of_atoms p hp hA
  have hpd := posDef_of_posSemidef_det_pos hpsd hdet_pos
  have hM00 : 0 < M_mat (fpOverlap p) (fpTriangle p) (tVec p) 0 0 := by
    have h := hpd.dotProduct_mulVec_pos (x := ![1, 0, 0]) (by
      intro hz; have := congrFun hz 0; norm_num at this)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_three] using h
  have hM2x2 : 0 < M_mat (fpOverlap p) (fpTriangle p) (tVec p) 0 0 *
      M_mat (fpOverlap p) (fpTriangle p) (tVec p) 1 1 -
      (M_mat (fpOverlap p) (fpTriangle p) (tVec p) 0 1) ^ 2 := by
    let M := M_mat (fpOverlap p) (fpTriangle p) (tVec p)
    let x : Fin 3 → ℝ := ![M 0 1, -M 0 0, 0]
    have hx_ne : x ≠ 0 := by
      intro hz
      have h1 := congrFun hz 1
      simp only [x, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply, neg_eq_zero] at h1
      linarith
    have hx := hpd.dotProduct_mulVec_pos hx_ne
    have hsym := (M_mat_isSymm (fpOverlap p) (fpTriangle p) (tVec p)).eq
    have h10 : M 1 0 = M 0 1 := by simpa using congrFun (congrFun hsym 0) 1
    have hval : star x ⬝ᵥ (M *ᵥ x) = M 0 0 * (M 0 0 * M 1 1 - M 0 1 ^ 2) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_three, x,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, h10]
      ring
    rw [hval] at hx
    nlinarith
  exact ⟨hpi, hpd, hpsd, hdet_pos, hD_pos, hM00, hM2x2⟩

/-! ## Section 3: Quaternionic Cholesky Realization (`prop:cer:quatpair` (b)) -/

private def qInner (u v : Fin 3 → Quaternion ℝ) : Quaternion ℝ :=
  ∑ k : Fin 3, star (u k) * v k

private theorem qInner_conj (u v : Fin 3 → Quaternion ℝ) :
    star (qInner u v) = qInner v u := by
  unfold qInner
  rw [Fin.sum_univ_three, Fin.sum_univ_three, star_add, star_add,
    star_mul, star_mul, star_mul, star_star, star_star, star_star]

private theorem qInner_self_re (u : Fin 3 → Quaternion ℝ) :
    (qInner u u).re = ∑ k : Fin 3, (star (u k) * u k).re := by
  unfold qInner
  rw [Fin.sum_univ_three, Fin.sum_univ_three, quat_add_re, quat_add_re]

private def quatRank1 (u : Fin 3 → Quaternion ℝ) (q : Quaternion ℝ)
    (v : Fin 3 → Quaternion ℝ) : QuatMatrix3 :=
  Matrix.of (fun i j => u i * q * star (v j))

private def quatDyadMat3 (u : Fin 3 → Quaternion ℝ) : QuatMatrix3 :=
  quatRank1 u 1 u

private def quatDyadHerm3 (u : Fin 3 → Quaternion ℝ) : QuatHermitian3 :=
  ⟨quatDyadMat3 u, by
    rw [selfAdjoint.mem_iff]
    ext i j <;> simp [quatDyadMat3, quatRank1, Matrix.star_apply, star_mul]⟩

private def quatDyadAlbert (u : Fin 3 → Quaternion ℝ) : Albert :=
  standardQuaternionicWindow.embedding (quatDyadHerm3 u)

private theorem quatDyadAlbert_eq_octDyad (u : Fin 3 → Quaternion ℝ) :
    quatDyadAlbert u = octDyad (fun i => quatEmbed1 (u i)) := by
  rw [octDyad_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding u]
  apply albert_ext
  · simp [quatDyadAlbert, standardQuaternionicWindow, quatMatrixToAlbert, quatDyadHerm3,
      quatDyadMat3, quatRank1, quatDyad]
  · simp [quatDyadAlbert, standardQuaternionicWindow, quatMatrixToAlbert, quatDyadHerm3,
      quatDyadMat3, quatRank1, quatDyad]
  · simp [quatDyadAlbert, standardQuaternionicWindow, quatMatrixToAlbert, quatDyadHerm3,
      quatDyadMat3, quatRank1, quatDyad]
  · simp [quatDyadAlbert, standardQuaternionicWindow, quatMatrixToAlbert, quatDyadHerm3,
      quatDyadMat3, quatRank1, quatDyad]
  · simp [quatDyadAlbert, standardQuaternionicWindow, quatMatrixToAlbert, quatDyadHerm3,
      quatDyadMat3, quatRank1, quatDyad]
  · simp [quatDyadAlbert, standardQuaternionicWindow, quatMatrixToAlbert, quatDyadHerm3,
      quatDyadMat3, quatRank1, quatDyad]

private theorem quatDyadAlbert_mem_std (u : Fin 3 → Quaternion ℝ) :
    quatDyadAlbert u ∈ standardQuaternionicWindow.subalgebra.carrier := by
  rw [← standardQuaternionicWindow.range_eq]
  exact ⟨quatDyadHerm3 u, rfl⟩

private theorem quatDyadAlbert_isAtom (u : Fin 3 → Quaternion ℝ)
    (hu : (qInner u u).re = 1) : IsAtom (quatDyadAlbert u) := by
  rw [quatDyadAlbert_eq_octDyad, octDyad_eq_quatDyad quatEmbed1 quatEmbed1_isQuatEmbedding u]
  refine quatDyad_isAtom quatEmbed1 quatEmbed1_isQuatEmbedding u 1 one_ne_zero ?_
  have h1 : ∀ k : Fin 3, (u k * star (u k)).re = (star (u k) * u k).re :=
    fun k => quat_re_mul_comm _ _
  rw [Fin.sum_univ_three]
  rw [qInner_self_re, Fin.sum_univ_three] at hu
  simp only [quatNormSq]
  linarith [quatNormSq_eq_mul_star_re (u 0), quatNormSq_eq_mul_star_re (u 1),
    quatNormSq_eq_mul_star_re (u 2), h1 0, h1 1, h1 2]

private theorem quat_re_sum (s : Fin 3 → Quaternion ℝ) :
    (∑ k : Fin 3, s k).re = ∑ k : Fin 3, (s k).re := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three, quat_add_re, quat_add_re]

private theorem quat_trace_sum_re (A B : QuatHermitian3) :
    tracePairing (standardQuaternionicWindow.embedding A)
        (standardQuaternionicWindow.embedding B) =
      ∑ k : Fin 3, (((A : QuatMatrix3) * (B : QuatMatrix3)) k k).re := by
  let C : QuatHermitian3 :=
    ⟨(1 / 2 : ℝ) • ((A : QuatMatrix3) * (B : QuatMatrix3) +
      (B : QuatMatrix3) * (A : QuatMatrix3)), by
      rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial,
        A.prop, B.prop, add_comm]⟩
  have hjm := standardQuaternionicWindow.preserves_product A B C rfl
  unfold tracePairing
  rw [← hjm, standardQuaternionicWindow.preserves_trace]
  have hcomm : ∑ i : Fin 3, (((B : QuatMatrix3) * (A : QuatMatrix3)) i i).re =
      ∑ i : Fin 3, (((A : QuatMatrix3) * (B : QuatMatrix3)) i i).re := by
    simp only [Matrix.mul_apply, Fin.sum_univ_three, quat_add_re]
    simp only [quat_re_mul_comm ((B : QuatMatrix3) _ _) ((A : QuatMatrix3) _ _)]
    ring
  have hC_re : ∀ i : Fin 3, ((C : QuatMatrix3) i i).re =
      (1 / 2 : ℝ) * ((((A : QuatMatrix3) * (B : QuatMatrix3)) i i).re +
        (((B : QuatMatrix3) * (A : QuatMatrix3)) i i).re) := fun i => rfl
  rw [hC_re 0, hC_re 1, hC_re 2]
  have hsumA : ∑ i : Fin 3, (((A : QuatMatrix3) * (B : QuatMatrix3)) i i).re =
      (((A : QuatMatrix3) * (B : QuatMatrix3)) 0 0).re +
        (((A : QuatMatrix3) * (B : QuatMatrix3)) 1 1).re +
        (((A : QuatMatrix3) * (B : QuatMatrix3)) 2 2).re := Fin.sum_univ_three _
  have hsumB : ∑ i : Fin 3, (((B : QuatMatrix3) * (A : QuatMatrix3)) i i).re =
      (((B : QuatMatrix3) * (A : QuatMatrix3)) 0 0).re +
        (((B : QuatMatrix3) * (A : QuatMatrix3)) 1 1).re +
        (((B : QuatMatrix3) * (A : QuatMatrix3)) 2 2).re := Fin.sum_univ_three _
  linarith

private theorem quatRank1_mul_entry (u v x y : Fin 3 → Quaternion ℝ) (q r : Quaternion ℝ)
    (i j : Fin 3) :
    (quatRank1 u q v * quatRank1 x r y) i j = quatRank1 u (q * qInner v x * r) y i j := by
  simp only [Matrix.mul_apply, quatRank1, Matrix.of_apply, qInner]
  rw [show u i * (q * (∑ k : Fin 3, star (v k) * x k) * r) * star (y j) =
      ∑ k : Fin 3, (u i * q * star (v k)) * (x k * r * star (y j)) by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]]

private theorem quatRank1_mul (u v x y : Fin 3 → Quaternion ℝ) (q r : Quaternion ℝ) :
    quatRank1 u q v * quatRank1 x r y = quatRank1 u (q * qInner v x * r) y := by
  ext i j
  · exact congrArg (fun a : Quaternion ℝ => a.re) (quatRank1_mul_entry u v x y q r i j)
  · exact congrArg (fun a : Quaternion ℝ => a.imI) (quatRank1_mul_entry u v x y q r i j)
  · exact congrArg (fun a : Quaternion ℝ => a.imJ) (quatRank1_mul_entry u v x y q r i j)
  · exact congrArg (fun a : Quaternion ℝ => a.imK) (quatRank1_mul_entry u v x y q r i j)

private theorem quatRank1_trace_re (u v : Fin 3 → Quaternion ℝ) (q : Quaternion ℝ) :
    ∑ k : Fin 3, (quatRank1 u q v k k).re = (q * qInner v u).re := by
  have hterm : ∀ k : Fin 3, (quatRank1 u q v k k).re = (q * (star (v k) * u k)).re := fun k => by
    dsimp only [quatRank1, Matrix.of_apply]
    rw [mul_assoc, quat_re_mul_comm (u k), mul_assoc]
  simp_rw [hterm]
  rw [← quat_re_sum]
  congr 1
  simp only [qInner, Finset.mul_sum]

private theorem quatDyadMat_trace_mul (u v : Fin 3 → Quaternion ℝ) :
    ∑ k : Fin 3, ((quatDyadMat3 u * quatDyadMat3 v) k k).re =
      (qInner u v * qInner v u).re := by
  unfold quatDyadMat3
  rw [quatRank1_mul, quatRank1_trace_re, one_mul, mul_one]

private theorem quatDyadMat_trace_mul3 (u v w : Fin 3 → Quaternion ℝ) :
    ∑ k : Fin 3, ((quatDyadMat3 u * quatDyadMat3 v * quatDyadMat3 w) k k).re =
      (qInner u v * qInner v w * qInner w u).re := by
  unfold quatDyadMat3
  rw [quatRank1_mul, quatRank1_mul, quatRank1_trace_re, one_mul, mul_one, mul_one]

private theorem quatDyadMat_trace_mul4 (u v w z : Fin 3 → Quaternion ℝ) :
    ∑ k : Fin 3, ((quatDyadMat3 u * quatDyadMat3 v * quatDyadMat3 w * quatDyadMat3 z) k k).re =
      (qInner u v * qInner v w * qInner w z * qInner z u).re := by
  unfold quatDyadMat3
  rw [quatRank1_mul, quatRank1_mul, quatRank1_mul, quatRank1_trace_re,
    one_mul, mul_one, mul_one, mul_one]

private theorem quatDyadAlbert_tracePairing (u v : Fin 3 → Quaternion ℝ) :
    tracePairing (quatDyadAlbert u) (quatDyadAlbert v) = (qInner u v * star (qInner u v)).re := by
  unfold quatDyadAlbert
  rw [quat_trace_sum_re]
  change ∑ k : Fin 3, ((quatDyadMat3 u * quatDyadMat3 v) k k).re = _
  rw [quatDyadMat_trace_mul, qInner_conj]

private theorem quatDyadAlbert_triangle (u v w : Fin 3 → Quaternion ℝ) :
    tracePairing (jordanMul (quatDyadAlbert u) (quatDyadAlbert v)) (quatDyadAlbert w) =
      (qInner u v * qInner v w * qInner w u).re := by
  let P := quatDyadHerm3 u
  let Q := quatDyadHerm3 v
  let R := quatDyadHerm3 w
  let PQ : QuatHermitian3 :=
    ⟨(1 / 2 : ℝ) • ((P : QuatMatrix3) * (Q : QuatMatrix3) +
      (Q : QuatMatrix3) * (P : QuatMatrix3)), by
      rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial,
        P.prop, Q.prop, add_comm]⟩
  have hjm : jordanMul (quatDyadAlbert u) (quatDyadAlbert v) =
      standardQuaternionicWindow.embedding PQ :=
    (standardQuaternionicWindow.preserves_product P Q PQ rfl).symm
  change tracePairing (jordanMul (quatDyadAlbert u) (quatDyadAlbert v))
      (standardQuaternionicWindow.embedding R) = _
  rw [hjm, quat_trace_sum_re]
  have hsum : ∑ k : Fin 3, (((PQ : QuatMatrix3) * (R : QuatMatrix3)) k k).re =
      (1 / 2 : ℝ) * (∑ k : Fin 3, ((quatDyadMat3 u * quatDyadMat3 v * quatDyadMat3 w) k k).re +
        ∑ k : Fin 3, ((quatDyadMat3 v * quatDyadMat3 u * quatDyadMat3 w) k k).re) := by
    have hmul : ∀ k : Fin 3, (((PQ : QuatMatrix3) * (R : QuatMatrix3)) k k).re =
        (1 / 2 : ℝ) * (((quatDyadMat3 u * quatDyadMat3 v * quatDyadMat3 w) k k).re +
          ((quatDyadMat3 v * quatDyadMat3 u * quatDyadMat3 w) k k).re) := fun k => by
      have hPQ : (PQ : QuatMatrix3) = (1 / 2 : ℝ) • (quatDyadMat3 u * quatDyadMat3 v +
          quatDyadMat3 v * quatDyadMat3 u) := rfl
      have hR : (R : QuatMatrix3) = quatDyadMat3 w := rfl
      rw [hPQ, hR, Matrix.smul_mul, Matrix.add_mul]
      rfl
    simp_rw [hmul, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum, quatDyadMat_trace_mul3 u v w, quatDyadMat_trace_mul3 v u w]
  have hrev : (qInner v u * qInner u w * qInner w v).re =
      (qInner u v * qInner v w * qInner w u).re := by
    rw [← qInner_conj u v, ← qInner_conj w u, ← qInner_conj v w,
      ← star_mul, ← star_mul, quat_star_re, ← mul_assoc, quat_re_mul_comm _ (qInner u v),
      ← mul_assoc]
  rw [hrev]
  ring

private theorem quatDyadAlbert_doublePair (u v w z : Fin 3 → Quaternion ℝ) :
    tracePairing (jordanMul (quatDyadAlbert u) (quatDyadAlbert v))
        (jordanMul (quatDyadAlbert w) (quatDyadAlbert z)) =
      (1 / 2 : ℝ) * ((qInner u v * qInner v w * qInner w z * qInner z u).re +
        (qInner u v * qInner v z * qInner z w * qInner w u).re) := by
  let P := quatDyadHerm3 u
  let Q := quatDyadHerm3 v
  let R := quatDyadHerm3 w
  let S := quatDyadHerm3 z
  let PQ : QuatHermitian3 :=
    ⟨(1 / 2 : ℝ) • ((P : QuatMatrix3) * (Q : QuatMatrix3) +
      (Q : QuatMatrix3) * (P : QuatMatrix3)), by
      rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial,
        P.prop, Q.prop, add_comm]⟩
  let RS : QuatHermitian3 :=
    ⟨(1 / 2 : ℝ) • ((R : QuatMatrix3) * (S : QuatMatrix3) +
      (S : QuatMatrix3) * (R : QuatMatrix3)), by
      rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, star_trivial,
        R.prop, S.prop, add_comm]⟩
  have hjm1 : jordanMul (quatDyadAlbert u) (quatDyadAlbert v) =
      standardQuaternionicWindow.embedding PQ :=
    (standardQuaternionicWindow.preserves_product P Q PQ rfl).symm
  have hjm2 : jordanMul (quatDyadAlbert w) (quatDyadAlbert z) =
      standardQuaternionicWindow.embedding RS :=
    (standardQuaternionicWindow.preserves_product R S RS rfl).symm
  rw [hjm1, hjm2, quat_trace_sum_re]
  have hsum : ∑ k : Fin 3, (((PQ : QuatMatrix3) * (RS : QuatMatrix3)) k k).re =
      (1 / 4 : ℝ) * (
        ∑ k : Fin 3, ((quatDyadMat3 u * quatDyadMat3 v * quatDyadMat3 w * quatDyadMat3 z) k k).re +
        ∑ k : Fin 3, ((quatDyadMat3 u * quatDyadMat3 v * quatDyadMat3 z * quatDyadMat3 w) k k).re +
        ∑ k : Fin 3, ((quatDyadMat3 v * quatDyadMat3 u * quatDyadMat3 w * quatDyadMat3 z) k k).re +
        ∑ k : Fin 3, ((quatDyadMat3 v * quatDyadMat3 u * quatDyadMat3 z * quatDyadMat3 w) k k).re) := by
    have hmul : ∀ k : Fin 3, (((PQ : QuatMatrix3) * (RS : QuatMatrix3)) k k).re =
        (1 / 4 : ℝ) * (
          ((quatDyadMat3 u * quatDyadMat3 v * quatDyadMat3 w * quatDyadMat3 z) k k).re +
          ((quatDyadMat3 u * quatDyadMat3 v * quatDyadMat3 z * quatDyadMat3 w) k k).re +
          ((quatDyadMat3 v * quatDyadMat3 u * quatDyadMat3 w * quatDyadMat3 z) k k).re +
          ((quatDyadMat3 v * quatDyadMat3 u * quatDyadMat3 z * quatDyadMat3 w) k k).re) := fun k => by
      have hPQ : (PQ : QuatMatrix3) = (1 / 2 : ℝ) • (quatDyadMat3 u * quatDyadMat3 v +
          quatDyadMat3 v * quatDyadMat3 u) := rfl
      have hRS : (RS : QuatMatrix3) = (1 / 2 : ℝ) • (quatDyadMat3 w * quatDyadMat3 z +
          quatDyadMat3 z * quatDyadMat3 w) := rfl
      rw [hPQ, hRS, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      simp only [Matrix.smul_apply, Matrix.add_apply, quat_smul_re, quat_add_re, Matrix.mul_assoc]
      ring
    simp_rw [hmul, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum, quatDyadMat_trace_mul4 u v w z, quatDyadMat_trace_mul4 u v z w,
    quatDyadMat_trace_mul4 v u w z, quatDyadMat_trace_mul4 v u z w]
  have h1 : (qInner v u * qInner u w * qInner w z * qInner z v).re =
      (qInner u v * qInner v z * qInner z w * qInner w u).re := by
    rw [← qInner_conj u v, ← qInner_conj w u, ← qInner_conj z w, ← qInner_conj v z,
      ← star_mul, ← star_mul, ← star_mul, quat_star_re]
    simp only [← mul_assoc]
    rw [quat_re_mul_comm _ (qInner u v)]
    simp only [mul_assoc]
  have h2 : (qInner v u * qInner u z * qInner z w * qInner w v).re =
      (qInner u v * qInner v w * qInner w z * qInner z u).re := by
    rw [← qInner_conj u v, ← qInner_conj z u, ← qInner_conj w z, ← qInner_conj v w,
      ← star_mul, ← star_mul, ← star_mul, quat_star_re]
    simp only [← mul_assoc]
    rw [quat_re_mul_comm _ (qInner u v)]
    simp only [mul_assoc]
  rw [h1, h2]
  ring

private theorem quat_normSq_invScale (B1 α β c o1 o2 R : ℝ) (u : Quaternion ℝ)
    (hB1 : B1 ≠ 0) (hmul : star u * u = 1) (hre : u.re = c)
    (ha : α ^ 2 = o1) (hb : β ^ 2 = o2) (hR : α * β * c = R) :
    (star ((1 / B1 : ℝ) • (α • u - β • 1)) * ((1 / B1 : ℝ) • (α • u - β • 1))).re =
      (o1 - 2 * R + o2) / B1 ^ 2 := by
  let v : Quaternion ℝ := (1 / B1 : ℝ) • (α • u - β • 1)
  have hv : B1 • v = α • u - β • 1 := by
    dsimp only [v]
    rw [smul_smul, mul_one_div_cancel hB1, one_smul]
  have hsv : B1 • star v = α • star u - β • 1 := by
    dsimp only [v]
    rw [star_smul, star_trivial (1 / B1), star_sub, star_smul, star_trivial α,
      star_smul, star_trivial β, star_one, smul_smul, mul_one_div_cancel hB1, one_smul]
  have hmul_eq : B1 ^ 2 • (star v * v) = (α • star u - β • 1) * (α • u - β • 1) := by
    calc
      B1 ^ 2 • (star v * v) = B1 • (B1 • (star v * v)) := by rw [smul_smul, pow_two]
      _ = B1 • (star v * (B1 • v)) := by rw [← mul_smul_comm]
      _ = (B1 • star v) * (B1 • v) := by rw [← smul_mul_assoc]
      _ = (α • star u - β • 1) * (α • u - β • 1) := by rw [hv, hsv]
  have hre_num : ((α • star u - β • 1) * (α • u - β • 1)).re = o1 - 2 * R + o2 := by
    have hexp : (α • star u - β • (1 : Quaternion ℝ)) * (α • u - β • (1 : Quaternion ℝ)) =
        (α ^ 2) • (1 : Quaternion ℝ) - (α * β) • (u + star u) + (β ^ 2) • (1 : Quaternion ℝ) := by
      rw [sub_mul, mul_sub, mul_sub]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hmul, mul_one, one_mul, pow_two]
      rw [show β * α = α * β by ring]
      simp only [sub_eq_add_neg, neg_add, neg_neg, smul_add]
      abel
    rw [hexp, quat_add_re, quat_sub_re, quat_smul_re, quat_smul_re, quat_smul_re,
      quat_one_re, quat_add_re, quat_star_re, hre, ha, hb,
      show α * β * (c + c) = 2 * (α * β * c) by ring, hR]
    ring
  have hB1_sq_ne : B1 ^ 2 ≠ 0 := pow_ne_zero 2 hB1
  rw [eq_div_iff hB1_sq_ne, mul_comm]
  change (B1 ^ 2 • (star v * v)).re = o1 - 2 * R + o2
  rw [hmul_eq, hre_num]

private theorem quat_cholesky_vD_norm
    (o01 o02 o03 o12 o13 o23 R012 R013 R023 R123 t0 t1 t2 tau
      a b c d e' f B1 HC c1 c2 c3 c4 K12 K23 K31 : ℝ)
    (hs : Fin 3 → Quaternion ℝ)
    (h_re0 : (hs 0).re = c1) (h_re1 : (hs 1).re = c2) (h_re2 : (hs 2).re = c3)
    (h_star_mul : ∀ i : Fin 3, star (hs i) * hs i = 1)
    (h_mul_star : ∀ i : Fin 3, hs i * star (hs i) = 1)
    (h01_re : (hs 0 * hs 1).re = K12)
    (h12_re : (hs 1 * hs 2).re = K23)
    (h02_re : (hs 0 * hs 2).re = K31)
    (h012_re : (hs 0 * hs 1 * hs 2).re = c4)
    (hstar0_2_re : (star (hs 0) * hs 2).re = 2 * c1 * c3 - K31)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (he0 : e' ≠ 0) (hf0 : f ≠ 0)
    (hB1_ne : B1 ≠ 0) (hHC_ne : HC ≠ 0)
    (ha2 : a ^ 2 = o01) (hb2 : b ^ 2 = o02) (hc2 : c ^ 2 = o03)
    (hd2 : d ^ 2 = o12) (he2 : e' ^ 2 = o13) (hf2 : f ^ 2 = o23)
    (hB1_sq : B1 ^ 2 = 1 - o01)
    (hN_pos : 0 < 1 - o01 - o02 - o12 + 2 * R012)
    (hHC_sq : B1 ^ 2 * HC ^ 2 = 1 - o01 - o02 - o12 + 2 * R012)
    (hc1_val : a * b * d * c1 = R012) (hc2_val : b * c * f * c2 = R023)
    (hc3_val : a * c * e' * c3 = R013) (hc4_val : d * e' * f * c4 = R123)
    (hK12_val : a * c * d * f * K12 = t0 + t2 - t1)
    (hK23_val : a * b * e' * f * K23 = t0 + t1 - t2)
    (hK31_val : b * c * d * e' * K31 = t1 + t2 - t0)
    (htau : tau = 1 / 2 - 1 / 2 * (o01 + o02 + o03 + o12 + o13 + o23) +
      1 / 2 * (o01 * o23 + o02 * o13 + o03 * o12) + R012 + R013 + R023 + R123)
    (ht_pi : t0 + t1 + t2 = tau) :
    let zC : Quaternion ℝ := (1 / B1 : ℝ) • (d • hs 0 - (a * b : ℝ) • 1)
    let xD : Quaternion ℝ := (1 / B1 : ℝ) • (e' • star (hs 2) - (a * c : ℝ) • 1)
    let yD : Quaternion ℝ := (1 / HC : ℝ) • (f • hs 1 - (b * c : ℝ) • 1 - star zC * xD)
    (⟨c, 0, 0, 0⟩ * star (⟨c, 0, 0, 0⟩ : Quaternion ℝ)).re + (star xD * xD).re + (star yD * yD).re = 1 := by
  intro zC xD yD
  have hx_re : (star xD * xD).re = (o13 - 2 * R013 + o01 * o03) / B1 ^ 2 := by
    refine quat_normSq_invScale B1 e' (a * c) c3 o13 (o01 * o03) R013 (star (hs 2))
      hB1_ne (by rw [star_star]; exact h_mul_star 2) (by rw [quat_star_re, h_re2])
      he2 (by rw [mul_pow, ha2, hc2]) (by rw [show e' * (a * c) * c3 = a * c * e' * c3 by ring, hc3_val])
  let N_ABC := 1 - o01 - o02 - o12 + 2 * R012
  let W : Quaternion ℝ := (B1 ^ 2 * HC) • yD
  have hW_eq : W = (-(b * c) : ℝ) • 1 + (B1 ^ 2 * f) • hs 1 + (a * c * d) • star (hs 0) +
      (a * b * e') • star (hs 2) - (d * e') • (star (hs 0) * star (hs 2)) := by
    have hzsB : B1 • star zC = d • star (hs 0) - (a * b : ℝ) • 1 := by
      dsimp only [zC]
      rw [star_smul, star_trivial (1 / B1), star_sub, star_smul, star_trivial d,
        star_smul, star_trivial (a * b), star_one, smul_smul, mul_one_div_cancel hB1_ne, one_smul]
    have hxB : B1 • xD = e' • star (hs 2) - (a * c : ℝ) • 1 := by
      dsimp only [xD]
      rw [smul_smul, mul_one_div_cancel hB1_ne, one_smul]
    have hzx : B1 ^ 2 • (star zC * xD) =
        (d • star (hs 0) - (a * b : ℝ) • 1) * (e' • star (hs 2) - (a * c : ℝ) • 1) := by
      calc
        B1 ^ 2 • (star zC * xD) = B1 • (B1 • (star zC * xD)) := by rw [smul_smul, pow_two]
        _ = B1 • (star zC * (B1 • xD)) := by rw [← mul_smul_comm]
        _ = (B1 • star zC) * (B1 • xD) := by rw [← smul_mul_assoc]
        _ = (d • star (hs 0) - (a * b : ℝ) • 1) * (e' • star (hs 2) - (a * c : ℝ) • 1) := by
          rw [hzsB, hxB]
    have hzx_exp : B1 ^ 2 • (star zC * xD) = (d * e') • (star (hs 0) * star (hs 2)) -
        (a * c * d) • star (hs 0) - (a * b * e') • star (hs 2) + (a ^ 2 * b * c) • (1 : Quaternion ℝ) := by
      rw [hzx, sub_mul, mul_sub, mul_sub]
      simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_smul]
      rw [show e' * d = d * e' by ring, show e' * (a * b) = a * b * e' by ring,
        show a * c * (a * b) = a ^ 2 * b * c by ring]
      abel
    dsimp only [W, yD]
    rw [smul_smul, mul_assoc, mul_one_div_cancel hHC_ne, mul_one,
      smul_sub, smul_sub, hzx_exp, smul_smul, smul_smul]
    have hB1_a2 : B1 ^ 2 * (b * c) + a ^ 2 * b * c = b * c := by
      calc
        B1 ^ 2 * (b * c) + a ^ 2 * b * c = (1 - o01) * (b * c) + o01 * (b * c) := by
          rw [hB1_sq, ha2]; ring
        _ = b * c := by ring
    rw [show (-(b * c) : ℝ) • (1 : Quaternion ℝ) =
        (-(B1 ^ 2 * (b * c) + a ^ 2 * b * c)) • (1 : Quaternion ℝ) by rw [hB1_a2]]
    rw [neg_smul, add_smul]
    abel
  let q0 : Quaternion ℝ := 1
  let q1 : Quaternion ℝ := hs 1
  let q2 : Quaternion ℝ := star (hs 0)
  let q3 : Quaternion ℝ := star (hs 2)
  let q4 : Quaternion ℝ := star (hs 0) * star (hs 2)
  have hg00 : (star q0 * q0).re = 1 := by simp [q0]
  have hg11 : (star q1 * q1).re = 1 := by rw [h_star_mul 1]; simp
  have hg22 : (star q2 * q2).re = 1 := by
    change (star (star (hs 0)) * star (hs 0)).re = 1; rw [star_star, h_mul_star 0]; simp
  have hg33 : (star q3 * q3).re = 1 := by
    change (star (star (hs 2)) * star (hs 2)).re = 1; rw [star_star, h_mul_star 2]; simp
  have hg44 : (star q4 * q4).re = 1 := by
    have h : star q4 * q4 = 1 := by
      dsimp only [q4]
      rw [star_mul, star_star, star_star, mul_assoc, ← mul_assoc (hs 0), h_mul_star 0,
        one_mul, h_mul_star 2]
    rw [h]; simp
  have hg01 : (star q0 * q1).re = c2 := by simp [q0, q1, h_re1]
  have hg02 : (star q0 * q2).re = c1 := by simp [q0, q2, h_re0]
  have hg03 : (star q0 * q3).re = c3 := by simp [q0, q3, h_re2]
  have hg04 : (star q0 * q4).re = K31 := by
    dsimp only [q0, q4]; rw [star_one, one_mul, ← star_mul, quat_star_re, quat_re_mul_comm, h02_re]
  have hg12 : (star q1 * q2).re = K12 := by
    dsimp only [q1, q2]; rw [← quat_star_re, star_mul]; simp only [star_star]; exact h01_re
  have hg13 : (star q1 * q3).re = K23 := by
    dsimp only [q1, q3]; rw [← quat_star_re, star_mul]; simp only [star_star]
    rw [quat_re_mul_comm, h12_re]
  have hg14 : (star q1 * q4).re = c4 := by
    dsimp only [q1, q4]
    rw [← quat_star_re, star_mul, star_mul]; simp only [star_star]
    rw [mul_assoc, quat_re_mul_comm (hs 2), h012_re]
  have hg23 : (star q2 * q3).re = 2 * c1 * c3 - K31 := by
    dsimp only [q2, q3]; rw [← quat_star_re, star_mul]; simp only [star_star]
    rw [quat_re_mul_comm, hstar0_2_re]
  have hg24 : (star q2 * q4).re = c3 := by
    dsimp only [q2, q4]; rw [star_star, ← mul_assoc, h_mul_star 0, one_mul]; simp [h_re2]
  have hg34 : (star q3 * q4).re = c1 := by
    dsimp only [q3, q4]; rw [star_star, quat_re_mul_comm (hs 2), mul_assoc, h_star_mul 2, mul_one]
    simp [h_re0]
  have hsym : ∀ u v : Quaternion ℝ, (star u * v).re = (star v * u).re := fun u v => by
    rw [← quat_star_re (star u * v), star_mul, star_star]
  let x0 := -(b * c)
  let x1 := B1 ^ 2 * f
  let x2 := a * c * d
  let x3 := a * b * e'
  let x4 := -(d * e')
  have hW_lin : W = x0 • q0 + x1 • q1 + x2 • q2 + x3 • q3 + x4 • q4 := by
    rw [hW_eq]; dsimp only [x0, x1, x2, x3, x4, q0, q1, q2, q3, q4]
    rw [sub_eq_add_neg, ← neg_smul]
  have hW_norm : (star W * W).re =
      x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2
      + 2 * x0 * x1 * c2 + 2 * x0 * x2 * c1 + 2 * x0 * x3 * c3 + 2 * x0 * x4 * K31
      + 2 * x1 * x2 * K12 + 2 * x1 * x3 * K23 + 2 * x1 * x4 * c4
      + 2 * x2 * x3 * (2 * c1 * c3 - K31) + 2 * x2 * x4 * c3 + 2 * x3 * x4 * c1 := by
    rw [hW_lin]
    simp only [star_add, star_smul, star_trivial, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      quat_add_re, quat_smul_re]
    rw [hsym q1 q0, hsym q2 q0, hsym q3 q0, hsym q4 q0,
      hsym q2 q1, hsym q3 q1, hsym q4 q1,
      hsym q3 q2, hsym q4 q2, hsym q4 q3,
      hg00, hg11, hg22, hg33, hg44,
      hg01, hg02, hg03, hg04, hg12, hg13, hg14, hg23, hg24, hg34]
    ring
  have hW_poly : N_ABC * (1 - o01 - o03 - o13 + 2 * R013) - (star W * W).re =
      2 * B1 ^ 2 * (tau - (t0 + t1 + t2)) := by
    rw [hW_norm, htau]
    have hB1_a2 : B1 ^ 2 = 1 - a ^ 2 := by rw [hB1_sq, ha2]
    have hc1' : c1 = R012 / (a * b * d) := by rw [← hc1_val]; field_simp [ha0, hb0, hd0]
    have hc2' : c2 = R023 / (b * c * f) := by rw [← hc2_val]; field_simp [hb0, hc0, hf0]
    have hc3' : c3 = R013 / (a * c * e') := by rw [← hc3_val]; field_simp [ha0, hc0, he0]
    have hc4' : c4 = R123 / (d * e' * f) := by rw [← hc4_val]; field_simp [hd0, he0, hf0]
    have h12' : K12 = (t0 + t2 - t1) / (a * c * d * f) := by
      rw [← hK12_val]; field_simp [ha0, hc0, hd0, hf0]
    have h23' : K23 = (t0 + t1 - t2) / (a * b * e' * f) := by
      rw [← hK23_val]; field_simp [ha0, hb0, he0, hf0]
    have h31' : K31 = (t1 + t2 - t0) / (b * c * d * e') := by
      rw [← hK31_val]; field_simp [hb0, hc0, hd0, he0]
    dsimp only [N_ABC, x0, x1, x2, x3, x4]
    rw [hB1_a2, ← ha2, ← hb2, ← hc2, ← hd2, ← he2, ← hf2,
      hc1', hc2', hc3', hc4', h12', h23', h31']
    field_simp [ha0, hb0, hc0, hd0, he0, hf0]
    ring
  have hpi_eq : tau - (t0 + t1 + t2) = 0 := by linarith
  rw [hpi_eq, mul_zero, sub_eq_zero] at hW_poly
  have hy_re : (star yD * yD).re =
      (1 - o01 - o03 - o13 + 2 * R013) / B1 ^ 2 := by
    have hW_rel : (star W * W).re = (B1 ^ 2 * HC) ^ 2 * (star yD * yD).re := by
      dsimp only [W]
      rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, quat_smul_re, ← pow_two]
    have hpow : (B1 ^ 2 * HC) ^ 2 = B1 ^ 2 * N_ABC := by
      calc
        (B1 ^ 2 * HC) ^ 2 = B1 ^ 2 * (B1 ^ 2 * HC ^ 2) := by ring
        _ = B1 ^ 2 * N_ABC := by rw [hHC_sq]
    rw [hpow, ← hW_poly] at hW_rel
    have hmul_eq : (B1 ^ 2 * N_ABC) * (star yD * yD).re =
        N_ABC * (1 - o01 - o03 - o13 + 2 * R013) := hW_rel.symm
    have hdiv : B1 ^ 2 * (star yD * yD).re = 1 - o01 - o03 - o13 + 2 * R013 :=
      mul_left_cancel₀ hN_pos.ne' (by linarith)
    field_simp [hB1_ne]
    linarith
  have h0r : (⟨c, 0, 0, 0⟩ * star (⟨c, 0, 0, 0⟩ : Quaternion ℝ)).re = o03 := by
    rw [quat_real_star]; simp only [Quaternion.re_mul, mul_zero, sub_zero]; rw [← hc2]; ring
  rw [h0r, hx_re, hy_re]
  field_simp [hB1_ne]
  rw [hB1_sq]
  ring

private theorem quat_det_relation (c1 c2 c3 : ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    ((⟨c1, B 0 0, B 1 0, B 2 0⟩ : Quaternion ℝ) *
        ⟨c2, B 0 1, B 1 1, B 2 1⟩ *
        ⟨c3, B 0 2, B 1 2, B 2 2⟩).re =
      c1 * c2 * c3
        - c1 * (B 0 1 * B 0 2 + B 1 1 * B 1 2 + B 2 1 * B 2 2)
        - c2 * (B 0 0 * B 0 2 + B 1 0 * B 1 2 + B 2 0 * B 2 2)
        - c3 * (B 0 0 * B 0 1 + B 1 0 * B 1 1 + B 2 0 * B 2 1)
        - B.det := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Matrix.det_fin_three]
  ring

private theorem quat_unit_of_re_normSq (q : Quaternion ℝ) (hq : (q * star q).re = 1) :
    star q * q = 1 ∧ q * star q = 1 := by
  have h1 : q * star q = 1 := by
    ext
    · exact hq
    · simp; ring
    · simp; ring
    · simp; ring
  have h2 : star q * q = 1 := by
    ext
    · rw [quat_re_mul_comm]; exact hq
    · simp; ring
    · simp; ring
    · simp; ring
  exact ⟨h2, h1⟩

/-- `prop:cer:quatpair` (b) for any trace data `(o, R, t)` with `0 < N(p_A + p_B + p_C)`,
`t ∈ Π`, `M(t) succeq 0`, and `D_tet(t) = 0`. -/
theorem prop_cer_quatpair_b_of_data
    (o : Fin 4 → Fin 4 → ℝ) (ho_symm : ∀ i j, o i j = o j i)
    (ho_pos : ∀ i j, i ≠ j → 0 < o i j) (ho01_lt : o 0 1 < 1)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (_hR12 : ∀ i j k, R i j k = R j i k) (hR23 : ∀ i j k, R i j k = R i k j)
    (hN_pos : 0 < 1 - o 0 1 - o 0 2 - o 1 2 + 2 * R 0 1 2)
    (t : Fin 3 → ℝ) (ht_pi : t ∈ planePi o R)
    (hM_psd : (M_mat o R t).PosSemidef) (hD_zero : Dtet o R t = 0) :
    ∃ q : Fin 4 → Albert,
      (∀ i, IsAtom (q i)) ∧
      (∀ i, q i ∈ standardQuaternionicWindow.subalgebra.carrier) ∧
      (∀ i j, i ≠ j → fpOverlap q i j = o i j) ∧
      fpTriangle q 0 1 2 = R 0 1 2 ∧
      fpTriangle q 0 1 3 = R 0 1 3 ∧
      fpTriangle q 0 2 3 = R 0 2 3 ∧
      fpTriangle q 1 2 3 = R 1 2 3 ∧
      fpDoublePair1 q = t 0 ∧
      fpDoublePair2 q = t 1 ∧
      fpDoublePair3 q = t 2 := by
  obtain ⟨B0_mat, hB0_eq⟩ := exists_realGramFactor hM_psd
  let c1 := tetraC1 o R
  let c2 := tetraC2 o R
  let c3 := tetraC3 o R
  let c4 := tetraC4 o R
  let S := tetraS o R t
  have hdet_sq : B0_mat.det ^ 2 = (S - c4) ^ 2 := by
    have hMdet : (M_mat o R t).det = B0_mat.det ^ 2 := by
      rw [hB0_eq, Matrix.det_mul, Matrix.det_transpose]; ring
    have hD : (M_mat o R t).det - (c4 - S) ^ 2 = 0 := hD_zero
    linarith
  have hdet_cases : B0_mat.det = S - c4 ∨ B0_mat.det = -(S - c4) := sq_eq_sq_iff_eq_or_eq_neg.mp hdet_sq
  let B : Matrix (Fin 3) (Fin 3) ℝ := if B0_mat.det = S - c4 then B0_mat else -B0_mat
  have hB_gram : M_mat o R t = B.transpose * B := by
    dsimp only [B]
    split_ifs
    · exact hB0_eq
    · rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]; exact hB0_eq
  have hB_det : B.det = S - c4 := by
    dsimp only [B]
    split_ifs with h
    · exact h
    · rw [Matrix.det_neg, Fintype.card_fin]
      have h2 := hdet_cases.resolve_left h
      rw [h2]; ring
  let hs : Fin 3 → Quaternion ℝ := ![
    ⟨c1, B 0 0, B 1 0, B 2 0⟩,
    ⟨c2, B 0 1, B 1 1, B 2 1⟩,
    ⟨c3, B 0 2, B 1 2, B 2 2⟩]
  have hM_entry : ∀ i j : Fin 3,
      B 0 i * B 0 j + B 1 i * B 1 j + B 2 i * B 2 j = M_mat o R t i j := fun i j => by
    have h := congrFun (congrFun hB_gram.symm i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] using h
  have h_re0 : (hs 0).re = c1 := rfl
  have h_re1 : (hs 1).re = c2 := rfl
  have h_re2 : (hs 2).re = c3 := rfl
  have h_norm : ∀ i : Fin 3, (hs i * star (hs i)).re = 1 := fun i => by
    fin_cases i
    · have hmm := hM_entry 0 0
      rw [M_mat_00] at hmm
      rw [quatNormSq_eq_mul_star_re]; change c1 ^ 2 + B 0 0 ^ 2 + B 1 0 ^ 2 + B 2 0 ^ 2 = 1
      linarith
    · have hmm := hM_entry 1 1
      rw [M_mat_11] at hmm
      rw [quatNormSq_eq_mul_star_re]; change c2 ^ 2 + B 0 1 ^ 2 + B 1 1 ^ 2 + B 2 1 ^ 2 = 1
      linarith
    · have hmm := hM_entry 2 2
      rw [M_mat_22] at hmm
      rw [quatNormSq_eq_mul_star_re]; change c3 ^ 2 + B 0 2 ^ 2 + B 1 2 ^ 2 + B 2 2 ^ 2 = 1
      linarith
  have h_star_mul : ∀ i : Fin 3, star (hs i) * hs i = 1 := fun i =>
    (quat_unit_of_re_normSq (hs i) (h_norm i)).1
  have h_mul_star : ∀ i : Fin 3, hs i * star (hs i) = 1 := fun i =>
    (quat_unit_of_re_normSq (hs i) (h_norm i)).2
  have h01_re : (hs 0 * hs 1).re = tetraK12 o t := by
    have h01 := hM_entry 0 1
    rw [M_mat_01] at h01
    change (⟨c1, B 0 0, B 1 0, B 2 0⟩ * ⟨c2, B 0 1, B 1 1, B 2 1⟩ : Quaternion ℝ).re = _
    simp only [Quaternion.re_mul]; linarith
  have h12_re : (hs 1 * hs 2).re = tetraK23 o t := by
    have h12 := hM_entry 1 2
    rw [M_mat_12] at h12
    change (⟨c2, B 0 1, B 1 1, B 2 1⟩ * ⟨c3, B 0 2, B 1 2, B 2 2⟩ : Quaternion ℝ).re = _
    simp only [Quaternion.re_mul]; linarith
  have h02_re : (hs 0 * hs 2).re = tetraK31 o t := by
    have h02 := hM_entry 0 2
    rw [M_mat_02] at h02
    change (⟨c1, B 0 0, B 1 0, B 2 0⟩ * ⟨c3, B 0 2, B 1 2, B 2 2⟩ : Quaternion ℝ).re = _
    simp only [Quaternion.re_mul]; linarith
  have h012_re : (hs 0 * hs 1 * hs 2).re = c4 := by
    have h01 := hM_entry 0 1
    have h12 := hM_entry 1 2
    have h02 := hM_entry 0 2
    have hS_def : S = c1 * c2 * c3 - c1 * M_mat o R t 1 2 - c2 * M_mat o R t 0 2 -
        c3 * M_mat o R t 0 1 := rfl
    change ((⟨c1, B 0 0, B 1 0, B 2 0⟩ : Quaternion ℝ) *
        ⟨c2, B 0 1, B 1 1, B 2 1⟩ *
        ⟨c3, B 0 2, B 1 2, B 2 2⟩).re = c4
    rw [← h01, ← h12, ← h02] at hS_def
    rw [quat_det_relation]
    linarith [hS_def, hB_det]
  have hstar0_2_re : (star (hs 0) * hs 2).re = 2 * c1 * c3 - tetraK31 o t := by
    have h02 := hM_entry 0 2
    rw [M_mat_02] at h02
    change (star (⟨c1, B 0 0, B 1 0, B 2 0⟩ : Quaternion ℝ) *
        ⟨c3, B 0 2, B 1 2, B 2 2⟩).re = _
    simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star]
    linarith
  let a := Real.sqrt (o 0 1)
  let b := Real.sqrt (o 0 2)
  let c := Real.sqrt (o 0 3)
  let d := Real.sqrt (o 1 2)
  let e' := Real.sqrt (o 1 3)
  let f := Real.sqrt (o 2 3)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (ho_pos 0 1 (by decide))
  have hb0 : 0 < b := Real.sqrt_pos.mpr (ho_pos 0 2 (by decide))
  have hc0 : 0 < c := Real.sqrt_pos.mpr (ho_pos 0 3 (by decide))
  have hd0 : 0 < d := Real.sqrt_pos.mpr (ho_pos 1 2 (by decide))
  have he0 : 0 < e' := Real.sqrt_pos.mpr (ho_pos 1 3 (by decide))
  have hf0 : 0 < f := Real.sqrt_pos.mpr (ho_pos 2 3 (by decide))
  have ha2 : a ^ 2 = o 0 1 := Real.sq_sqrt (ho_pos 0 1 (by decide)).le
  have hb2 : b ^ 2 = o 0 2 := Real.sq_sqrt (ho_pos 0 2 (by decide)).le
  have hc2 : c ^ 2 = o 0 3 := Real.sq_sqrt (ho_pos 0 3 (by decide)).le
  have hd2 : d ^ 2 = o 1 2 := Real.sq_sqrt (ho_pos 1 2 (by decide)).le
  have he2 : e' ^ 2 = o 1 3 := Real.sq_sqrt (ho_pos 1 3 (by decide)).le
  have hf2 : f ^ 2 = o 2 3 := Real.sq_sqrt (ho_pos 2 3 (by decide)).le
  let B1 := Real.sqrt (1 - o 0 1)
  have hB1_pos : 0 < B1 := Real.sqrt_pos.mpr (by linarith)
  have hB1_sq : B1 ^ 2 = 1 - o 0 1 := Real.sq_sqrt (by linarith)
  let N_ABC := 1 - o 0 1 - o 0 2 - o 1 2 + 2 * R 0 1 2
  let HC := Real.sqrt N_ABC / B1
  have hHC_pos : 0 < HC := div_pos (Real.sqrt_pos.mpr hN_pos) hB1_pos
  have hHC_sq : B1 ^ 2 * HC ^ 2 = N_ABC := by
    dsimp only [HC]
    rw [div_pow, Real.sq_sqrt hN_pos.le]
    field_simp [hB1_pos.ne']
    ring
  let zC : Quaternion ℝ := (1 / B1 : ℝ) • (d • hs 0 - (a * b : ℝ) • 1)
  let xD : Quaternion ℝ := (1 / B1 : ℝ) • (e' • star (hs 2) - (a * c : ℝ) • 1)
  let yD : Quaternion ℝ := (1 / HC : ℝ) • (f • hs 1 - (b * c : ℝ) • 1 - star zC * xD)
  let vA : Fin 3 → Quaternion ℝ := ![1, 0, 0]
  let vB : Fin 3 → Quaternion ℝ := ![⟨a, 0, 0, 0⟩, ⟨B1, 0, 0, 0⟩, 0]
  let vC : Fin 3 → Quaternion ℝ := ![⟨b, 0, 0, 0⟩, zC, ⟨HC, 0, 0, 0⟩]
  let vD : Fin 3 → Quaternion ℝ := ![⟨c, 0, 0, 0⟩, xD, yD]
  have hnu1 : Real.sqrt (o 0 1 * o 1 2 * o 2 0) = a * b * d := by
    rw [ho_symm 2 0, ← ha2, ← hb2, ← hd2,
      show a ^ 2 * d ^ 2 * b ^ 2 = (a * b * d) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg ha0.le hb0.le) hd0.le)
  have hnu2 : Real.sqrt (o 0 2 * o 2 3 * o 3 0) = b * c * f := by
    rw [ho_symm 3 0, ← hb2, ← hc2, ← hf2,
      show b ^ 2 * f ^ 2 * c ^ 2 = (b * c * f) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg hb0.le hc0.le) hf0.le)
  have hnu3 : Real.sqrt (o 0 3 * o 3 1 * o 1 0) = a * c * e' := by
    rw [ho_symm 3 1, ho_symm 1 0, ← ha2, ← hc2, ← he2,
      show c ^ 2 * e' ^ 2 * a ^ 2 = (a * c * e') ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg ha0.le hc0.le) he0.le)
  have hnu4 : Real.sqrt (o 1 2 * o 2 3 * o 3 1) = d * e' * f := by
    rw [ho_symm 3 1, ← hd2, ← he2, ← hf2,
      show d ^ 2 * f ^ 2 * e' ^ 2 = (d * e' * f) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg hd0.le he0.le) hf0.le)
  have hden12 : Real.sqrt (o 0 1 * o 1 2 * o 2 3 * o 3 0) = a * c * d * f := by
    rw [ho_symm 3 0, ← ha2, ← hc2, ← hd2, ← hf2,
      show a ^ 2 * d ^ 2 * f ^ 2 * c ^ 2 = (a * c * d * f) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg ha0.le hc0.le) hd0.le) hf0.le)
  have hden23 : Real.sqrt (o 0 2 * o 2 3 * o 3 1 * o 1 0) = a * b * e' * f := by
    rw [ho_symm 3 1, ho_symm 1 0, ← ha2, ← hb2, ← he2, ← hf2,
      show b ^ 2 * f ^ 2 * e' ^ 2 * a ^ 2 = (a * b * e' * f) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg ha0.le hb0.le) he0.le) hf0.le)
  have hden31 : Real.sqrt (o 0 3 * o 3 1 * o 1 2 * o 2 0) = b * c * d * e' := by
    rw [ho_symm 3 1, ho_symm 2 0, ← hb2, ← hc2, ← hd2, ← he2,
      show c ^ 2 * e' ^ 2 * d ^ 2 * b ^ 2 = (b * c * d * e') ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg hb0.le hc0.le) hd0.le) he0.le)
  have hc1_val : a * b * d * c1 = R 0 1 2 := by
    dsimp only [c1, tetraC1]; rw [hnu1]; field_simp [ha0.ne', hb0.ne', hd0.ne']
  have hc2_val : b * c * f * c2 = R 0 2 3 := by
    dsimp only [c2, tetraC2]; rw [hnu2]; field_simp [hb0.ne', hc0.ne', hf0.ne']
  have hc3_val : a * c * e' * c3 = R 0 1 3 := by
    dsimp only [c3, tetraC3]; rw [hnu3, hR23 0 3 1]; field_simp [ha0.ne', hc0.ne', he0.ne']
  have hc4_val : d * e' * f * c4 = R 1 2 3 := by
    dsimp only [c4, tetraC4]; rw [hnu4]; field_simp [hd0.ne', he0.ne', hf0.ne']
  have hK12_val : a * c * d * f * tetraK12 o t = t 0 + t 2 - t 1 := by
    unfold tetraK12; rw [hden12]
    have hQ : tetraQOfTraces t 0 1 2 3 = t 0 + t 2 - t 1 := by
      simp [tetraQOfTraces, unorderedPairClass]; ring
    rw [hQ]; field_simp [ha0.ne', hc0.ne', hd0.ne', hf0.ne']
  have hK23_val : a * b * e' * f * tetraK23 o t = t 0 + t 1 - t 2 := by
    unfold tetraK23; rw [hden23]
    have hQ : tetraQOfTraces t 0 2 3 1 = t 0 + t 1 - t 2 := by
      simp [tetraQOfTraces, unorderedPairClass]
    rw [hQ]; field_simp [ha0.ne', hb0.ne', he0.ne', hf0.ne']
  have hK31_val : b * c * d * e' * tetraK31 o t = t 1 + t 2 - t 0 := by
    unfold tetraK31; rw [hden31]
    have hQ : tetraQOfTraces t 0 3 1 2 = t 1 + t 2 - t 0 := by
      simp [tetraQOfTraces, unorderedPairClass]
    rw [hQ]; field_simp [hb0.ne', hc0.ne', hd0.ne', he0.ne']
  have hvA_norm : (qInner vA vA).re = 1 := by
    rw [qInner_self_re, Fin.sum_univ_three]
    simp [vA]
  have hvB_norm : (qInner vB vB).re = 1 := by
    rw [qInner_self_re, Fin.sum_univ_three]
    simp only [vB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, add_zero, quat_real_normSq,
      quat_zero_re]
    linarith [ha2, hB1_sq]
  have hvC_norm : (qInner vC vC).re = 1 := by
    have hz_re : (star zC * zC).re = (o 1 2 - 2 * R 0 1 2 + o 0 1 * o 0 2) / B1 ^ 2 := by
      refine quat_normSq_invScale B1 d (a * b) c1 (o 1 2) (o 0 1 * o 0 2) (R 0 1 2) (hs 0)
        hB1_pos.ne' (h_star_mul 0) h_re0 hd2 (by rw [mul_pow, ha2, hb2])
        (by rw [show d * (a * b) * c1 = a * b * d * c1 by ring, hc1_val])
    rw [qInner_self_re, Fin.sum_univ_three]
    simp only [vC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, quat_real_normSq]
    rw [hb2, hz_re]
    have hHC_sq_div : HC ^ 2 = N_ABC / B1 ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hB1_pos.ne'), mul_comm]; exact hHC_sq
    rw [hHC_sq_div]
    dsimp only [N_ABC]
    field_simp [hB1_pos.ne']
    rw [hB1_sq]
    ring
  have hvD_norm : (qInner vD vD).re = 1 := by
    rw [qInner_self_re, Fin.sum_univ_three]
    simp only [vD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [quat_re_mul_comm (star (⟨c, 0, 0, 0⟩ : Quaternion ℝ))]
    exact quat_cholesky_vD_norm (o 0 1) (o 0 2) (o 0 3) (o 1 2) (o 1 3) (o 2 3)
      (R 0 1 2) (R 0 1 3) (R 0 2 3) (R 1 2 3) (t 0) (t 1) (t 2) (tauOf o R)
      a b c d e' f B1 HC c1 c2 c3 c4 (tetraK12 o t) (tetraK23 o t) (tetraK31 o t)
      hs h_re0 h_re1 h_re2 h_star_mul h_mul_star h01_re h12_re h02_re h012_re hstar0_2_re
      ha0.ne' hb0.ne' hc0.ne' hd0.ne' he0.ne' hf0.ne' hB1_pos.ne' hHC_pos.ne'
      ha2 hb2 hc2 hd2 he2 hf2 hB1_sq hN_pos hHC_sq
      hc1_val hc2_val hc3_val hc4_val hK12_val hK23_val hK31_val rfl ht_pi
  -- Pairwise qInner values
  have hAB : qInner vA vB = ⟨a, 0, 0, 0⟩ := by
    simp [qInner, Fin.sum_univ_three, vA, vB]
  have hAC : qInner vA vC = ⟨b, 0, 0, 0⟩ := by
    simp [qInner, Fin.sum_univ_three, vA, vC]
  have hAD : qInner vA vD = ⟨c, 0, 0, 0⟩ := by
    simp [qInner, Fin.sum_univ_three, vA, vD]
  have hBC : qInner vB vC = d • hs 0 := by
    simp only [qInner, Fin.sum_univ_three, vB, vC, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, add_zero]
    rw [quat_real_star, quat_real_star, quat_real_mul_left, quat_real_mul_left]
    have hz : B1 • zC = d • hs 0 - (a * b : ℝ) • 1 := by
      dsimp only [zC]; rw [smul_smul, mul_one_div_cancel hB1_pos.ne', one_smul]
    rw [hz, quat_ofReal_eq_smul b, smul_smul]
    abel
  have hBD : qInner vB vD = e' • star (hs 2) := by
    simp only [qInner, Fin.sum_univ_three, vB, vD, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_zero, zero_mul, add_zero]
    rw [quat_real_star, quat_real_star, quat_real_mul_left, quat_real_mul_left]
    have hx : B1 • xD = e' • star (hs 2) - (a * c : ℝ) • 1 := by
      dsimp only [xD]; rw [smul_smul, mul_one_div_cancel hB1_pos.ne', one_smul]
    rw [hx, quat_ofReal_eq_smul c, smul_smul]
    abel
  have hCD : qInner vC vD = f • hs 1 := by
    simp only [qInner, Fin.sum_univ_three, vC, vD, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [quat_real_star, quat_real_star, quat_real_mul_left, quat_real_mul_left]
    have hy : HC • yD = f • hs 1 - (b * c : ℝ) • 1 - star zC * xD := by
      dsimp only [yD]; rw [smul_smul, mul_one_div_cancel hHC_pos.ne', one_smul]
    rw [hy, quat_ofReal_eq_smul c, smul_smul]
    abel
  have hBA : qInner vB vA = ⟨a, 0, 0, 0⟩ := by
    rw [← qInner_conj vA vB, hAB, quat_real_star]
  have hCA : qInner vC vA = ⟨b, 0, 0, 0⟩ := by
    rw [← qInner_conj vA vC, hAC, quat_real_star]
  have hDA : qInner vD vA = ⟨c, 0, 0, 0⟩ := by
    rw [← qInner_conj vA vD, hAD, quat_real_star]
  have hCB : qInner vC vB = d • star (hs 0) := by
    rw [← qInner_conj vB vC, hBC, star_smul, star_trivial]
  have hDB : qInner vD vB = e' • hs 2 := by
    rw [← qInner_conj vB vD, hBD, star_smul, star_trivial, star_star]
  have hDC : qInner vD vC = f • star (hs 1) := by
    rw [← qInner_conj vC vD, hCD, star_smul, star_trivial]
  let vs : Fin 4 → Fin 3 → Quaternion ℝ := fun i =>
    match i with | 0 => vA | 1 => vB | 2 => vC | 3 => vD
  let q : Fin 4 → Albert := fun i => quatDyadAlbert (vs i)
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine forall_fin4 _ ?_ ?_ ?_ ?_
    · exact quatDyadAlbert_isAtom vA hvA_norm
    · exact quatDyadAlbert_isAtom vB hvB_norm
    · exact quatDyadAlbert_isAtom vC hvC_norm
    · exact quatDyadAlbert_isAtom vD hvD_norm
  · intro i
    exact quatDyadAlbert_mem_std (vs i)
  · intro i j hij
    have h01' : fpOverlap q 0 1 = o 0 1 := by
      rw [fpOverlap, quatDyadAlbert_tracePairing]
      change (qInner vA vB * star (qInner vA vB)).re = o 0 1
      rw [hAB, quat_real_star]; simp only [Quaternion.re_mul, mul_zero, sub_zero]; rw [← ha2]; ring
    have h02' : fpOverlap q 0 2 = o 0 2 := by
      rw [fpOverlap, quatDyadAlbert_tracePairing]
      change (qInner vA vC * star (qInner vA vC)).re = o 0 2
      rw [hAC, quat_real_star]; simp only [Quaternion.re_mul, mul_zero, sub_zero]; rw [← hb2]; ring
    have h03' : fpOverlap q 0 3 = o 0 3 := by
      rw [fpOverlap, quatDyadAlbert_tracePairing]
      change (qInner vA vD * star (qInner vA vD)).re = o 0 3
      rw [hAD, quat_real_star]; simp only [Quaternion.re_mul, mul_zero, sub_zero]; rw [← hc2]; ring
    have h12' : fpOverlap q 1 2 = o 1 2 := by
      rw [fpOverlap, quatDyadAlbert_tracePairing]
      change (qInner vB vC * star (qInner vB vC)).re = o 1 2
      rw [hBC, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, h_mul_star 0]
      simp only [quat_smul_re, quat_one_re, mul_one, ← pow_two]
      exact hd2
    have h13' : fpOverlap q 1 3 = o 1 3 := by
      rw [fpOverlap, quatDyadAlbert_tracePairing]
      change (qInner vB vD * star (qInner vB vD)).re = o 1 3
      rw [hBD, star_smul, star_trivial e', star_star,
        smul_mul_assoc, mul_smul_comm, smul_smul, h_star_mul 2]
      simp only [quat_smul_re, quat_one_re, mul_one, ← pow_two]
      exact he2
    have h23' : fpOverlap q 2 3 = o 2 3 := by
      rw [fpOverlap, quatDyadAlbert_tracePairing]
      change (qInner vC vD * star (qInner vC vD)).re = o 2 3
      rw [hCD, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, h_mul_star 1]
      simp only [quat_smul_re, quat_one_re, mul_one, ← pow_two]
      exact hf2
    revert hij
    refine forall_fin4 (fun i => ∀ j : Fin 4, i ≠ j → fpOverlap q i j = o i j) ?_ ?_ ?_ ?_ i j
    · refine forall_fin4 _ (fun h => absurd rfl h) (fun _ => h01') (fun _ => h02') (fun _ => h03')
    · refine forall_fin4 _ (fun _ => by rw [fpOverlap_symm, ho_symm 1 0]; exact h01')
        (fun h => absurd rfl h) (fun _ => h12') (fun _ => h13')
    · refine forall_fin4 _ (fun _ => by rw [fpOverlap_symm, ho_symm 2 0]; exact h02')
        (fun _ => by rw [fpOverlap_symm, ho_symm 2 1]; exact h12') (fun h => absurd rfl h) (fun _ => h23')
    · refine forall_fin4 _ (fun _ => by rw [fpOverlap_symm, ho_symm 3 0]; exact h03')
        (fun _ => by rw [fpOverlap_symm, ho_symm 3 1]; exact h13')
        (fun _ => by rw [fpOverlap_symm, ho_symm 3 2]; exact h23') (fun h => absurd rfl h)
  · rw [fpTriangle, quatDyadAlbert_triangle]
    change (qInner vA vB * qInner vB vC * qInner vC vA).re = _
    rw [hAB, hBC, hCA, quat_real_mul_left]
    simp only [quat_real_mul_right, smul_mul_assoc, smul_smul, quat_smul_re, h_re0]
    linear_combination hc1_val
  · rw [fpTriangle, quatDyadAlbert_triangle]
    change (qInner vA vB * qInner vB vD * qInner vD vA).re = _
    rw [hAB, hBD, hDA, quat_real_mul_left]
    simp only [quat_real_mul_right, smul_mul_assoc, smul_smul, quat_smul_re,
      quat_star_re, h_re2]
    linear_combination hc3_val
  · rw [fpTriangle, quatDyadAlbert_triangle]
    change (qInner vA vC * qInner vC vD * qInner vD vA).re = _
    rw [hAC, hCD, hDA, quat_real_mul_left]
    simp only [quat_real_mul_right, smul_mul_assoc, smul_smul, quat_smul_re, h_re1]
    linear_combination hc2_val
  · rw [fpTriangle, quatDyadAlbert_triangle]
    change (qInner vB vC * qInner vC vD * qInner vD vB).re = _
    rw [hBC, hCD, hDB]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, quat_smul_re, h012_re]
    linear_combination hc4_val
  · rw [fpDoublePair1, quatDyadAlbert_doublePair]
    change 1 / 2 * ((qInner vA vB * qInner vB vC * qInner vC vD * qInner vD vA).re +
      (qInner vA vB * qInner vB vD * qInner vD vC * qInner vC vA).re) = t 0
    rw [hAB, hBC, hCD, hDA, hBD, hDC, hCA,
      quat_real_mul_left, quat_real_mul_right, quat_real_mul_left, quat_real_mul_right]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, quat_smul_re, h01_re]
    have hrev : (star (hs 2) * star (hs 1)).re = tetraK23 o t := by
      rw [← star_mul, quat_star_re, h12_re]
    rw [hrev]
    linear_combination (1 / 2 : ℝ) * hK12_val + (1 / 2 : ℝ) * hK23_val
  · rw [fpDoublePair2, quatDyadAlbert_doublePair]
    change 1 / 2 * ((qInner vA vC * qInner vC vB * qInner vB vD * qInner vD vA).re +
      (qInner vA vC * qInner vC vD * qInner vD vB * qInner vB vA).re) = t 1
    rw [hAC, hCB, hBD, hDA, hCD, hDB, hBA,
      quat_real_mul_left, quat_real_mul_right, quat_real_mul_left, quat_real_mul_right]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, quat_smul_re, h12_re]
    have hrev : (star (hs 0) * star (hs 2)).re = tetraK31 o t := by
      rw [← star_mul, quat_star_re, quat_re_mul_comm, h02_re]
    rw [hrev]
    linear_combination (1 / 2 : ℝ) * hK23_val + (1 / 2 : ℝ) * hK31_val
  · rw [fpDoublePair3, quatDyadAlbert_doublePair]
    change 1 / 2 * ((qInner vA vD * qInner vD vB * qInner vB vC * qInner vC vA).re +
      (qInner vA vD * qInner vD vC * qInner vC vB * qInner vB vA).re) = t 2
    rw [hAD, hDB, hBC, hCA, hDC, hCB, hBA,
      quat_real_mul_left, quat_real_mul_right, quat_real_mul_left, quat_real_mul_right]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, quat_smul_re]
    have h20 : (hs 2 * hs 0).re = tetraK31 o t := by
      rw [quat_re_mul_comm, h02_re]
    have h10 : (star (hs 1) * star (hs 0)).re = tetraK12 o t := by
      rw [← star_mul, quat_star_re, h01_re]
    rw [h20, h10]
    linear_combination (1 / 2 : ℝ) * hK31_val + (1 / 2 : ℝ) * hK12_val

private theorem symm3_ordered_eq (f g : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h012 : f 0 1 2 = g 0 1 2) (h013 : f 0 1 3 = g 0 1 3)
    (h023 : f 0 2 3 = g 0 2 3) (h123 : f 1 2 3 = g 1 2 3)
    {a b c : Fin 4} (hab : a < b) (hbc : b < c) : f a b c = g a b c := by
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩; rcases c with ⟨c, hc⟩
  change a < b at hab; change b < c at hbc
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    first | exact h012 | exact h013 | exact h023 | exact h123

private theorem symm3_eq_of_four_distinct
    (f g : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hf12 : ∀ i j k, f i j k = f j i k) (hf23 : ∀ i j k, f i j k = f i k j)
    (hg12 : ∀ i j k, g i j k = g j i k) (hg23 : ∀ i j k, g i j k = g i k j)
    (hdiag : ∀ x y, f x x y = g x x y)
    (h012 : f 0 1 2 = g 0 1 2) (h013 : f 0 1 3 = g 0 1 3)
    (h023 : f 0 2 3 = g 0 2 3) (h123 : f 1 2 3 = g 1 2 3) :
    ∀ i j k, f i j k = g i j k := by
  intro i j k
  by_cases hij : i = j
  · subst hij; exact hdiag i k
  · by_cases hik : i = k
    · subst hik; rw [hf23, hg23]; exact hdiag i j
    · by_cases hjk : j = k
      · subst hjk; rw [hf12, hg12, hf23, hg23]; exact hdiag j i
      · suffices hsort : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c → f a b c = g a b c from
          hsort i j k hij hik hjk
        intro a b c hab hac hbc
        have hlt2 : ∀ x y z : Fin 4, x < y → x ≠ z → y ≠ z → f x y z = g x y z := by
          intro x y z hxy hxz hyz
          rcases lt_or_gt_of_ne hyz with hyz | hzy
          · exact symm3_ordered_eq f g h012 h013 h023 h123 hxy hyz
          · rw [hf23, hg23]
            rcases lt_or_gt_of_ne hxz with hxz | hzx
            · exact symm3_ordered_eq f g h012 h013 h023 h123 hxz hzy
            · rw [hf12, hg12]
              exact symm3_ordered_eq f g h012 h013 h023 h123 hzx hxy
        rcases lt_or_gt_of_ne hab with hab | hba
        · exact hlt2 a b c hab hac hbc
        · rw [hf12, hg12]
          exact hlt2 b a c hba hbc hac

/-- Full 13-trace matching for `prop:cer:quatpair` (b) instantiated from four atoms `p`
with `0 < fourPointInvariant p`. -/
theorem prop_cer_quatpair_b (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (t : Fin 3 → ℝ)
    (ht_pi : t ∈ planePi (fpOverlap p) (fpTriangle p))
    (hM_psd : (M_mat (fpOverlap p) (fpTriangle p) t).PosSemidef)
    (hD_zero : Dtet (fpOverlap p) (fpTriangle p) t = 0) :
    ∃ q : Fin 4 → Albert,
      (∀ i, IsAtom (q i)) ∧
      (∀ i, q i ∈ standardQuaternionicWindow.subalgebra.carrier) ∧
      (∀ i j, fpOverlap q i j = fpOverlap p i j) ∧
      (∀ i j k, fpTriangle q i j k = fpTriangle p i j k) ∧
      fpDoublePair1 q = t 0 ∧
      fpDoublePair2 q = t 1 ∧
      fpDoublePair3 q = t 2 := by
  have ho_bounds : ∀ i j, i ≠ j → 0 < fpOverlap p i j ∧ fpOverlap p i j < 1 :=
    fun i j hij => overlap_pos_lt_one_of_fourPoint_pos p hp hA hij
  have hN := tripleNorm_pos_of_fourPoint_pos p hp hA
  obtain ⟨q, hq_atom, hq_std, hq_o, hq_R012, hq_R013, hq_R023, hq_R123, ht0, ht1, ht2⟩ :=
    prop_cer_quatpair_b_of_data (fpOverlap p) (fpOverlap_symm p) (fun i j hij => (ho_bounds i j hij).1)
      (ho_bounds 0 1 (by decide)).2 (fpTriangle p) (fpTriangle_swap12 p) (fpTriangle_swap23 p)
      hN t ht_pi hM_psd hD_zero
  have hq_o_all : ∀ i j, fpOverlap q i j = fpOverlap p i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      unfold fpOverlap tracePairing
      rw [(hq_atom i).1, (hq_atom i).2, (hp i).1, (hp i).2]
    · exact hq_o i j hij
  have hq_R_all : ∀ i j k, fpTriangle q i j k = fpTriangle p i j k := by
    refine symm3_eq_of_four_distinct (fpTriangle q) (fpTriangle p)
      (fpTriangle_swap12 q) (fpTriangle_swap23 q)
      (fpTriangle_swap12 p) (fpTriangle_swap23 p)
      (fun x y => ?_) hq_R012 hq_R013 hq_R023 hq_R123
    unfold fpTriangle
    rw [(hq_atom x).1, (hp x).1]
    exact hq_o_all x y
  exact ⟨q, hq_atom, hq_std, hq_o_all, hq_R_all, ht0, ht1, ht2⟩

/-! ## Section 4: Boundary Intersection on Any Line in `Π` (`prop:cer:quatpair` (c)) -/

private theorem psd_of_minor_nonneg {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : M.IsSymm) (hM00 : 0 < M 0 0)
    (hA11 : 0 ≤ M 0 0 * M 1 1 - M 0 1 ^ 2)
    (hA22 : 0 ≤ M 0 0 * M 2 2 - M 0 2 ^ 2)
    (hdet : 0 ≤ M.det) : M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hsym.eq i) j
  · intro x
    let a11 := M 0 0 * M 1 1 - M 0 1 ^ 2
    let a22 := M 0 0 * M 2 2 - M 0 2 ^ 2
    let a12 := M 0 0 * M 1 2 - M 0 1 * M 0 2
    have h10 : M 1 0 = M 0 1 := by simpa using congrFun (congrFun hsym.eq 0) 1
    have h20 : M 2 0 = M 0 2 := by simpa using congrFun (congrFun hsym.eq 0) 2
    have h21 : M 2 1 = M 1 2 := by simpa using congrFun (congrFun hsym.eq 1) 2
    have hjac : a11 * a22 - a12 ^ 2 = M 0 0 * M.det := by
      dsimp only [a11, a22, a12]
      rw [Matrix.det_fin_three, h10, h20, h21]
      ring
    have hquad_2 : 0 ≤ a11 * x 1 ^ 2 + 2 * a12 * x 1 * x 2 + a22 * x 2 ^ 2 := by
      by_cases ha : a11 = 0
      · have ha12 : a12 = 0 := by
          have h0 : 0 ≤ M 0 0 * M.det := mul_nonneg hM00.le hdet
          have hsq : a12 ^ 2 ≤ 0 := by nlinarith [hjac, ha, h0]
          exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg a12))
        rw [ha, ha12]
        nlinarith [hA22, sq_nonneg (x 2)]
      · have ha_pos : 0 < a11 := lt_of_le_of_ne hA11 (Ne.symm ha)
        have hdecomp : a11 * (a11 * x 1 ^ 2 + 2 * a12 * x 1 * x 2 + a22 * x 2 ^ 2) =
            (a11 * x 1 + a12 * x 2) ^ 2 + (a11 * a22 - a12 ^ 2) * x 2 ^ 2 := by ring
        have hmd : 0 ≤ M 0 0 * M.det := mul_nonneg hM00.le hdet
        have hpos : 0 ≤ a11 * (a11 * x 1 ^ 2 + 2 * a12 * x 1 * x 2 + a22 * x 2 ^ 2) := by
          rw [hdecomp, hjac]
          nlinarith [sq_nonneg (a11 * x 1 + a12 * x 2), sq_nonneg (x 2), hmd]
        nlinarith
    have hmain : M 0 0 * (star x ⬝ᵥ (M *ᵥ x)) =
        (M 0 0 * x 0 + M 0 1 * x 1 + M 0 2 * x 2) ^ 2 +
          (a11 * x 1 ^ 2 + 2 * a12 * x 1 * x 2 + a22 * x 2 ^ 2) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
        h10, h20, h21, a11, a22, a12]
      ring
    nlinarith [sq_nonneg (M 0 0 * x 0 + M 0 1 * x 1 + M 0 2 * x 2)]

private theorem det_zero_of_minor_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : M.IsSymm) (hM00 : 0 < M 0 0) (hM11 : 0 < M 1 1)
    (_hA11 : 0 ≤ M 0 0 * M 1 1 - M 0 1 ^ 2)
    (_hA22 : 0 ≤ M 0 0 * M 2 2 - M 0 2 ^ 2)
    (_hB22 : 0 ≤ M 1 1 * M 2 2 - M 1 2 ^ 2)
    (hdet : 0 ≤ M.det)
    (hz : M 0 0 * M 1 1 - M 0 1 ^ 2 = 0 ∨ M 0 0 * M 2 2 - M 0 2 ^ 2 = 0 ∨
      M.det = 0 ∨ M 1 1 * M 2 2 - M 1 2 ^ 2 = 0) : M.det = 0 := by
  have h10 : M 1 0 = M 0 1 := by simpa using congrFun (congrFun hsym.eq 0) 1
  have h20 : M 2 0 = M 0 2 := by simpa using congrFun (congrFun hsym.eq 0) 2
  have h21 : M 2 1 = M 1 2 := by simpa using congrFun (congrFun hsym.eq 1) 2
  have hjac0 : (M 0 0 * M 1 1 - M 0 1 ^ 2) * (M 0 0 * M 2 2 - M 0 2 ^ 2) -
      (M 0 0 * M 1 2 - M 0 1 * M 0 2) ^ 2 = M 0 0 * M.det := by
    rw [Matrix.det_fin_three, h10, h20, h21]; ring
  have hjac1 : (M 1 1 * M 0 0 - M 0 1 ^ 2) * (M 1 1 * M 2 2 - M 1 2 ^ 2) -
      (M 1 1 * M 0 2 - M 0 1 * M 1 2) ^ 2 = M 1 1 * M.det := by
    rw [Matrix.det_fin_three, h10, h20, h21]; ring
  rcases hz with h1 | h2 | h3 | h4
  · have hle : M 0 0 * M.det ≤ 0 := by
      rw [← hjac0, h1, zero_mul, zero_sub]; exact neg_nonpos.mpr (sq_nonneg _)
    have hge : 0 ≤ M 0 0 * M.det := mul_nonneg hM00.le hdet
    exact (mul_eq_zero.mp (le_antisymm hle hge)).resolve_left hM00.ne'
  · have hle : M 0 0 * M.det ≤ 0 := by
      rw [← hjac0, h2, mul_zero, zero_sub]; exact neg_nonpos.mpr (sq_nonneg _)
    have hge : 0 ≤ M 0 0 * M.det := mul_nonneg hM00.le hdet
    exact (mul_eq_zero.mp (le_antisymm hle hge)).resolve_left hM00.ne'
  · exact h3
  · have hle : M 1 1 * M.det ≤ 0 := by
      rw [← hjac1, h4, mul_zero, zero_sub]; exact neg_nonpos.mpr (sq_nonneg _)
    have hge : 0 ≤ M 1 1 * M.det := mul_nonneg hM11.le hdet
    exact (mul_eq_zero.mp (le_antisymm hle hge)).resolve_left hM11.ne'

private theorem M_mat_line_continuous (o : Fin 4 → Fin 4 → ℝ) (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (t0 v : Fin 3 → ℝ) (i j : Fin 3) :
    Continuous (fun s : ℝ => M_mat o R (t0 + s • v) i j) := by
  have hQ : ∀ a b c d : Fin 4, Continuous (fun s : ℝ => tetraQOfTraces (t0 + s • v) a b c d) := by
    intro a b c d; unfold tetraQOfTraces
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; fun_prop
  have hK12 : Continuous (fun s : ℝ => tetraK12 o (t0 + s • v)) := by
    unfold tetraK12; exact (hQ 0 1 2 3).div_const _
  have hK23 : Continuous (fun s : ℝ => tetraK23 o (t0 + s • v)) := by
    unfold tetraK23; exact (hQ 0 2 3 1).div_const _
  have hK31 : Continuous (fun s : ℝ => tetraK31 o (t0 + s • v)) := by
    unfold tetraK31; exact (hQ 0 3 1 2).div_const _
  refine forall_fin3 (fun i => ∀ j, Continuous (fun s : ℝ => M_mat o R (t0 + s • v) i j))
    ?_ ?_ ?_ i j
  · refine forall_fin3 _ ?_ ?_ ?_
    · simp only [M_mat_00]; exact continuous_const
    · simp_rw [M_mat_01]; exact continuous_const.sub hK12
    · simp_rw [M_mat_02]; exact continuous_const.sub hK31
  · refine forall_fin3 _ ?_ ?_ ?_
    · have heq : (fun s : ℝ => M_mat o R (t0 + s • v) 1 0) = (fun s : ℝ => M_mat o R (t0 + s • v) 0 1) := by
        funext s; simpa using congrFun (congrFun (M_mat_isSymm o R (t0 + s • v)).eq 0) 1
      rw [heq]; simp_rw [M_mat_01]; exact continuous_const.sub hK12
    · simp only [M_mat_11]; exact continuous_const
    · simp_rw [M_mat_12]; exact continuous_const.sub hK23
  · refine forall_fin3 _ ?_ ?_ ?_
    · have heq : (fun s : ℝ => M_mat o R (t0 + s • v) 2 0) = (fun s : ℝ => M_mat o R (t0 + s • v) 0 2) := by
        funext s; simpa using congrFun (congrFun (M_mat_isSymm o R (t0 + s • v)).eq 0) 2
      rw [heq]; simp_rw [M_mat_02]; exact continuous_const.sub hK31
    · have heq : (fun s : ℝ => M_mat o R (t0 + s • v) 2 1) = (fun s : ℝ => M_mat o R (t0 + s • v) 1 2) := by
        funext s; simpa using congrFun (congrFun (M_mat_isSymm o R (t0 + s • v)).eq 1) 2
      rw [heq]; simp_rw [M_mat_12]; exact continuous_const.sub hK23
    · simp only [M_mat_22]; exact continuous_const

private theorem minors_pos_of_posDef {M : Matrix (Fin 3) (Fin 3) ℝ} (hpd : M.PosDef) :
    0 < M 0 0 ∧ 0 < M 1 1 ∧ 0 < M 2 2 ∧
      0 < M 0 0 * M 1 1 - M 0 1 ^ 2 ∧
      0 < M 0 0 * M 2 2 - M 0 2 ^ 2 ∧
      0 < M 1 1 * M 2 2 - M 1 2 ^ 2 := by
  have h10 : M 1 0 = M 0 1 := by simpa using congrFun (congrFun hpd.isHermitian.eq 0) 1
  have h20 : M 2 0 = M 0 2 := by simpa using congrFun (congrFun hpd.isHermitian.eq 0) 2
  have h21 : M 2 1 = M 1 2 := by simpa using congrFun (congrFun hpd.isHermitian.eq 1) 2
  have hM00 : 0 < M 0 0 := by
    have h := hpd.dotProduct_mulVec_pos (x := ![1, 0, 0]) (by
      intro hz; have := congrFun hz 0; norm_num at this)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_three] using h
  have hM11 : 0 < M 1 1 := by
    have h := hpd.dotProduct_mulVec_pos (x := ![0, 1, 0]) (by
      intro hz; have := congrFun hz 1; norm_num at this)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_three] using h
  have hM22 : 0 < M 2 2 := by
    have h := hpd.dotProduct_mulVec_pos (x := ![0, 0, 1]) (by
      intro hz; have := congrFun hz 2; norm_num at this)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_three] using h
  have hA11 : 0 < M 0 0 * M 1 1 - M 0 1 ^ 2 := by
    let x : Fin 3 → ℝ := ![M 0 1, -M 0 0, 0]
    have hx_ne : x ≠ 0 := by intro hz; have h1 := congrFun hz 1; simp [x] at h1; linarith
    have hx := hpd.dotProduct_mulVec_pos hx_ne
    have hval : star x ⬝ᵥ (M *ᵥ x) = M 0 0 * (M 0 0 * M 1 1 - M 0 1 ^ 2) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_three, x,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, h10]
      ring
    rw [hval] at hx; nlinarith
  have hA22 : 0 < M 0 0 * M 2 2 - M 0 2 ^ 2 := by
    let x : Fin 3 → ℝ := ![M 0 2, 0, -M 0 0]
    have hx_ne : x ≠ 0 := by intro hz; have h2 := congrFun hz 2; simp [x] at h2; linarith
    have hx := hpd.dotProduct_mulVec_pos hx_ne
    have hval : star x ⬝ᵥ (M *ᵥ x) = M 0 0 * (M 0 0 * M 2 2 - M 0 2 ^ 2) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_three, x,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, h20]
      ring
    rw [hval] at hx; nlinarith
  have hB22 : 0 < M 1 1 * M 2 2 - M 1 2 ^ 2 := by
    let x : Fin 3 → ℝ := ![0, M 1 2, -M 1 1]
    have hx_ne : x ≠ 0 := by intro hz; have h2 := congrFun hz 2; simp [x] at h2; linarith
    have hx := hpd.dotProduct_mulVec_pos hx_ne
    have hval : star x ⬝ᵥ (M *ᵥ x) = M 1 1 * (M 1 1 * M 2 2 - M 1 2 ^ 2) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_three, x,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, h21]
      ring
    rw [hval] at hx; nlinarith
  exact ⟨hM00, hM11, hM22, hA11, hA22, hB22⟩

private theorem exists_pos_zero_on_ray_of_data
    (o : Fin 4 → Fin 4 → ℝ) (ho_pos : ∀ i j, i ≠ j → 0 < o i j)
    (R : Fin 4 → Fin 4 → Fin 4 → ℝ) (t0 : Fin 3 → ℝ)
    (hpd : (M_mat o R t0).PosDef) (hD0 : 0 < Dtet o R t0)
    (v : Fin 3 → ℝ) (hv_ne : v ≠ 0) (hv_sum : v 0 + v 1 + v 2 = 0) :
    ∃ s : ℝ, 0 < s ∧
      (M_mat o R (t0 + s • v)).PosSemidef ∧
      Dtet o R (t0 + s • v) = 0 := by
  obtain ⟨hM00_0, hM11_0, hM22_0, hA11_0, hA22_0, hB22_0⟩ := minors_pos_of_posDef hpd
  have hdet0 : 0 < (M_mat o R t0).det := by
    have h := hD0
    rw [Dtet_eq_det_sub_sq] at h
    linarith [sq_nonneg (tetraC4 o R - tetraS o R t0)]
  have hdiag0 : ∀ s : ℝ, M_mat o R (t0 + s • v) 0 0 = M_mat o R t0 0 0 := fun _ => rfl
  have hdiag1 : ∀ s : ℝ, M_mat o R (t0 + s • v) 1 1 = M_mat o R t0 1 1 := fun _ => rfl
  have hdiag2 : ∀ s : ℝ, M_mat o R (t0 + s • v) 2 2 = M_mat o R t0 2 2 := fun _ => rfl
  let den12 := Real.sqrt (o 0 1 * o 1 2 * o 2 3 * o 3 0)
  let den23 := Real.sqrt (o 0 2 * o 2 3 * o 3 1 * o 1 0)
  let den31 := Real.sqrt (o 0 3 * o 3 1 * o 1 2 * o 2 0)
  have hden12_pos : 0 < den12 := Real.sqrt_pos.mpr (mul_pos (mul_pos (mul_pos (ho_pos 0 1 (by decide))
    (ho_pos 1 2 (by decide))) (ho_pos 2 3 (by decide))) (ho_pos 3 0 (by decide)))
  have hden23_pos : 0 < den23 := Real.sqrt_pos.mpr (mul_pos (mul_pos (mul_pos (ho_pos 0 2 (by decide))
    (ho_pos 2 3 (by decide))) (ho_pos 3 1 (by decide))) (ho_pos 1 0 (by decide)))
  have hden31_pos : 0 < den31 := Real.sqrt_pos.mpr (mul_pos (mul_pos (mul_pos (ho_pos 0 3 (by decide))
    (ho_pos 3 1 (by decide))) (ho_pos 1 2 (by decide))) (ho_pos 2 0 (by decide)))
  have hM01_aff : ∀ s, M_mat o R (t0 + s • v) 0 1 = M_mat o R t0 0 1 + (2 * v 1 / den12) * s := by
    intro s
    have hQ : tetraQOfTraces (t0 + s • v) 0 1 2 3 = tetraQOfTraces t0 0 1 2 3 - 2 * v 1 * s := by
      simp [tetraQOfTraces, unorderedPairClass]
      have hsum : s * v 0 + s * v 2 = -(s * v 1) := by linear_combination s * hv_sum
      linarith
    rw [M_mat_01, M_mat_01]
    change _ - tetraQOfTraces (t0 + s • v) 0 1 2 3 / den12 =
      _ - tetraQOfTraces t0 0 1 2 3 / den12 + 2 * v 1 / den12 * s
    rw [hQ]; ring
  have hM12_aff : ∀ s, M_mat o R (t0 + s • v) 1 2 = M_mat o R t0 1 2 + (2 * v 2 / den23) * s := by
    intro s
    have hQ : tetraQOfTraces (t0 + s • v) 0 2 3 1 = tetraQOfTraces t0 0 2 3 1 - 2 * v 2 * s := by
      simp [tetraQOfTraces, unorderedPairClass]
      have hsum : s * v 0 + s * v 1 = -(s * v 2) := by linear_combination s * hv_sum
      linarith
    rw [M_mat_12, M_mat_12]
    change _ - tetraQOfTraces (t0 + s • v) 0 2 3 1 / den23 =
      _ - tetraQOfTraces t0 0 2 3 1 / den23 + 2 * v 2 / den23 * s
    rw [hQ]; ring
  have hM02_aff : ∀ s, M_mat o R (t0 + s • v) 0 2 = M_mat o R t0 0 2 + (2 * v 0 / den31) * s := by
    intro s
    have hQ : tetraQOfTraces (t0 + s • v) 0 3 1 2 = tetraQOfTraces t0 0 3 1 2 - 2 * v 0 * s := by
      simp [tetraQOfTraces, unorderedPairClass]
      have hsum : s * v 1 + s * v 2 = -(s * v 0) := by linear_combination s * hv_sum
      linarith
    rw [M_mat_02, M_mat_02]
    change _ - tetraQOfTraces (t0 + s • v) 0 3 1 2 / den31 =
      _ - tetraQOfTraces t0 0 3 1 2 / den31 + 2 * v 0 / den31 * s
    rw [hQ]; ring
  let A11 : ℝ → ℝ := fun s => M_mat o R (t0 + s • v) 0 0 * M_mat o R (t0 + s • v) 1 1 -
    (M_mat o R (t0 + s • v) 0 1) ^ 2
  let A22 : ℝ → ℝ := fun s => M_mat o R (t0 + s • v) 0 0 * M_mat o R (t0 + s • v) 2 2 -
    (M_mat o R (t0 + s • v) 0 2) ^ 2
  let B22 : ℝ → ℝ := fun s => M_mat o R (t0 + s • v) 1 1 * M_mat o R (t0 + s • v) 2 2 -
    (M_mat o R (t0 + s • v) 1 2) ^ 2
  let detM : ℝ → ℝ := fun s => (M_mat o R (t0 + s • v)).det
  let minPos : ℝ → ℝ := fun s => min (min (A11 s) (A22 s)) (min (detM s) (B22 s))
  have hcont_entry : ∀ i j : Fin 3, Continuous (fun s => M_mat o R (t0 + s • v) i j) :=
    M_mat_line_continuous o R t0 v
  have hcont_det : Continuous detM := by
    simp only [detM, Matrix.det_fin_three]
    exact (((((hcont_entry 0 0).mul (hcont_entry 1 1)).mul (hcont_entry 2 2)).sub
        (((hcont_entry 0 0).mul (hcont_entry 1 2)).mul (hcont_entry 2 1))).sub
      (((hcont_entry 0 1).mul (hcont_entry 1 0)).mul (hcont_entry 2 2))).add
      (((hcont_entry 0 1).mul (hcont_entry 1 2)).mul (hcont_entry 2 0)) |>.add
      (((hcont_entry 0 2).mul (hcont_entry 1 0)).mul (hcont_entry 2 1)) |>.sub
      (((hcont_entry 0 2).mul (hcont_entry 1 1)).mul (hcont_entry 2 0))
  have hcont_min : Continuous minPos := by
    have hA11_c : Continuous A11 :=
      ((hcont_entry 0 0).mul (hcont_entry 1 1)).sub ((hcont_entry 0 1).pow 2)
    have hA22_c : Continuous A22 :=
      ((hcont_entry 0 0).mul (hcont_entry 2 2)).sub ((hcont_entry 0 2).pow 2)
    have hB22_c : Continuous B22 :=
      ((hcont_entry 1 1).mul (hcont_entry 2 2)).sub ((hcont_entry 1 2).pow 2)
    exact ((hA11_c.min hA22_c).min (hcont_det.min hB22_c))
  have hcont_Dtet : Continuous (fun s : ℝ => Dtet o R (t0 + s • v)) := by
    have hS_c : Continuous (fun s : ℝ => tetraS o R (t0 + s • v)) := by
      unfold tetraS
      exact (((continuous_const.sub (continuous_const.mul (hcont_entry 1 2))).sub
        (continuous_const.mul (hcont_entry 0 2))).sub
        (continuous_const.mul (hcont_entry 0 1)))
    simp_rw [Dtet_eq_det_sub_sq]
    exact hcont_det.sub ((continuous_const.sub hS_c).pow 2)
  have hv_comp : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv_ne; funext i; fin_cases i <;> [exact h.1; exact h.2.1; exact h.2.2]
  have exists_R_neg : ∃ R_bd : ℝ, 0 < R_bd ∧ minPos R_bd < 0 := by
    have hquad_neg : ∀ (m_prod a0 β : ℝ), β ≠ 0 → 0 ≤ m_prod →
        ∃ R_bd : ℝ, 0 < R_bd ∧ m_prod - (a0 + β * R_bd) ^ 2 < 0 := by
      intro m_prod a0 β hβ _hm
      let R_bd := (|a0| + Real.sqrt (m_prod + 1) + 1) / |β|
      have hβ_pos : 0 < |β| := abs_pos.mpr hβ
      have hR_pos : 0 < R_bd := div_pos (by positivity) hβ_pos
      refine ⟨R_bd, hR_pos, ?_⟩
      have hmul : |β * R_bd| = |a0| + Real.sqrt (m_prod + 1) + 1 := by
        rw [abs_mul, abs_of_pos hR_pos]
        dsimp only [R_bd]
        rw [mul_div_cancel₀ _ hβ_pos.ne']
      have htri : Real.sqrt (m_prod + 1) + 1 ≤ |a0 + β * R_bd| := by
        have h := abs_sub_abs_le_abs_sub (β * R_bd) (-a0)
        rw [abs_neg, sub_neg_eq_add, hmul, add_comm (β * R_bd) a0] at h
        linarith
      have hsq : m_prod + 1 ≤ (a0 + β * R_bd) ^ 2 := by
        have hnn : 0 ≤ Real.sqrt (m_prod + 1) := Real.sqrt_nonneg _
        have hs : (Real.sqrt (m_prod + 1) + 1) ^ 2 ≤ |a0 + β * R_bd| ^ 2 := by nlinarith
        rw [sq_abs] at hs
        have hsqrt2 : (Real.sqrt (m_prod + 1)) ^ 2 = m_prod + 1 :=
          Real.sq_sqrt (by linarith)
        nlinarith
      linarith
    rcases hv_comp with hv0 | hv1 | hv2
    · obtain ⟨R_bd, hR_pos, hneg⟩ := hquad_neg (M_mat o R t0 0 0 * M_mat o R t0 2 2)
        (M_mat o R t0 0 2) (2 * v 0 / den31)
        (div_ne_zero (mul_ne_zero (by norm_num) hv0) hden31_pos.ne')
        (mul_nonneg hM00_0.le hM22_0.le)
      refine ⟨R_bd, hR_pos, ?_⟩
      have hA22_R : A22 R_bd < 0 := by
        dsimp only [A22]; rw [hdiag0, hdiag2, hM02_aff]; exact hneg
      have hmin : minPos R_bd ≤ A22 R_bd :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    · obtain ⟨R_bd, hR_pos, hneg⟩ := hquad_neg (M_mat o R t0 0 0 * M_mat o R t0 1 1)
        (M_mat o R t0 0 1) (2 * v 1 / den12)
        (div_ne_zero (mul_ne_zero (by norm_num) hv1) hden12_pos.ne')
        (mul_nonneg hM00_0.le hM11_0.le)
      refine ⟨R_bd, hR_pos, ?_⟩
      have hA11_R : A11 R_bd < 0 := by
        dsimp only [A11]; rw [hdiag0, hdiag1, hM01_aff]; exact hneg
      have hmin : minPos R_bd ≤ A11 R_bd :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    · obtain ⟨R_bd, hR_pos, hneg⟩ := hquad_neg (M_mat o R t0 1 1 * M_mat o R t0 2 2)
        (M_mat o R t0 1 2) (2 * v 2 / den23)
        (div_ne_zero (mul_ne_zero (by norm_num) hv2) hden23_pos.ne')
        (mul_nonneg hM11_0.le hM22_0.le)
      refine ⟨R_bd, hR_pos, ?_⟩
      have hB22_R : B22 R_bd < 0 := by
        dsimp only [B22]; rw [hdiag1, hdiag2, hM12_aff]; exact hneg
      have hmin : minPos R_bd ≤ B22 R_bd :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
  obtain ⟨R_bd, hR_pos, hR_neg⟩ := exists_R_neg
  let S_set : Set ℝ := {s ∈ Set.Icc 0 R_bd | minPos s ≤ 0}
  have hS_closed : IsClosed S_set :=
    isClosed_Icc.inter (isClosed_le hcont_min continuous_const)
  have hS_ne : S_set.Nonempty := ⟨R_bd, ⟨hR_pos.le, le_rfl⟩, hR_neg.le⟩
  have hS_bdd : BddBelow S_set := ⟨0, fun _ hx => hx.1.1⟩
  let s1 := sInf S_set
  have hs1_mem : s1 ∈ S_set := hS_closed.csInf_mem hS_ne hS_bdd
  have hmin0 : 0 < minPos 0 := by
    simp only [minPos, A11, A22, B22, detM, zero_smul, add_zero]
    exact lt_min (lt_min hA11_0 hA22_0) (lt_min hdet0 hB22_0)
  have hs1_pos : 0 < s1 := by
    refine lt_of_le_of_ne hs1_mem.1.1 (fun h0 => ?_)
    have hle := hs1_mem.2
    rw [← h0] at hle
    linarith
  have hmin_ge0 : ∀ s ∈ Set.Ico 0 s1, 0 ≤ minPos s := by
    intro s hs
    by_contra hlt
    have hs_mem : s ∈ S_set := ⟨⟨hs.1, le_trans hs.2.le hs1_mem.1.2⟩, (not_le.mp hlt).le⟩
    have := csInf_le hS_bdd hs_mem
    linarith [hs.2]
  have hmin_s1_ge : 0 ≤ minPos s1 := by
    have hmem_nhds : ∀ᶠ s in 𝓝[<] s1, 0 ≤ minPos s := by
      filter_upwards [Ioo_mem_nhdsLT hs1_pos] with s hs
      exact hmin_ge0 s ⟨hs.1.le, hs.2⟩
    exact ge_of_tendsto ((hcont_min.tendsto s1).mono_left nhdsWithin_le_nhds) hmem_nhds
  have hmin_s1_eq : minPos s1 = 0 := le_antisymm hs1_mem.2 hmin_s1_ge
  have hmin_Icc : ∀ s ∈ Set.Icc 0 s1, 0 ≤ minPos s := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact hmin_s1_ge
    · exact hmin_ge0 s ⟨hs.1, hlt⟩
  have hdet_s1 : detM s1 = 0 := by
    have hmin0_cases : A11 s1 = 0 ∨ A22 s1 = 0 ∨ detM s1 = 0 ∨ B22 s1 = 0 := by
      have h_eq : min (min (A11 s1) (A22 s1)) (min (detM s1) (B22 s1)) = 0 := hmin_s1_eq
      rcases min_choice (min (A11 s1) (A22 s1)) (min (detM s1) (B22 s1)) with h12 | h34
      · rw [h12] at h_eq
        rcases min_choice (A11 s1) (A22 s1) with h1 | h2
        · exact Or.inl (h1.symm.trans h_eq)
        · exact Or.inr (Or.inl (h2.symm.trans h_eq))
      · rw [h34] at h_eq
        rcases min_choice (detM s1) (B22 s1) with h3 | h4
        · exact Or.inr (Or.inr (Or.inl (h3.symm.trans h_eq)))
        · exact Or.inr (Or.inr (Or.inr (h4.symm.trans h_eq)))
    dsimp only [minPos, A11, A22, B22, detM] at hmin_s1_ge
    exact det_zero_of_minor_zero (M_mat_isSymm o R (t0 + s1 • v))
      (by rw [hdiag0]; exact hM00_0) (by rw [hdiag1]; exact hM11_0)
      (le_trans (le_trans hmin_s1_ge (min_le_left _ _)) (min_le_left _ _))
      (le_trans (le_trans hmin_s1_ge (min_le_left _ _)) (min_le_right _ _))
      (le_trans (le_trans hmin_s1_ge (min_le_right _ _)) (min_le_right _ _))
      (le_trans (le_trans hmin_s1_ge (min_le_right _ _)) (min_le_left _ _))
      hmin0_cases
  have hD_s1 : Dtet o R (t0 + s1 • v) ≤ 0 := by
    rw [Dtet_eq_det_sub_sq]
    change detM s1 - (tetraC4 o R - tetraS o R (t0 + s1 • v)) ^ 2 ≤ 0
    rw [hdet_s1, zero_sub]
    exact neg_nonpos.mpr (sq_nonneg _)
  have hD_0 : 0 < Dtet o R (t0 + (0 : ℝ) • v) := by
    simpa [zero_smul, add_zero] using hD0
  have hivt : (0 : ℝ) ∈ Set.Icc (Dtet o R (t0 + s1 • v)) (Dtet o R (t0 + (0 : ℝ) • v)) :=
    ⟨hD_s1, hD_0.le⟩
  obtain ⟨s, hs_mem, hs_eq⟩ :=
    intermediate_value_Icc' hs1_pos.le hcont_Dtet.continuousOn hivt
  have hs_pos : 0 < s := by
    refine lt_of_le_of_ne hs_mem.1 (fun h0 => ?_)
    rw [← h0] at hs_eq
    linarith [hD_0]
  have hs_min : 0 ≤ minPos s := hmin_Icc s hs_mem
  have hs_psd : (M_mat o R (t0 + s • v)).PosSemidef := by
    dsimp only [minPos, A11, A22, B22, detM] at hs_min
    refine psd_of_minor_nonneg (M_mat_isSymm o R (t0 + s • v))
      (by rw [hdiag0]; exact hM00_0)
      (le_trans (le_trans hs_min (min_le_left _ _)) (min_le_left _ _))
      (le_trans (le_trans hs_min (min_le_left _ _)) (min_le_right _ _))
      (le_trans (le_trans hs_min (min_le_right _ _)) (min_le_left _ _))
  exact ⟨s, hs_pos, hs_psd, hs_eq⟩

private theorem exists_pos_zero_on_ray (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (v : Fin 3 → ℝ) (hv_ne : v ≠ 0)
    (hv_sum : v 0 + v 1 + v 2 = 0) :
    ∃ s : ℝ, 0 < s ∧
      (M_mat (fpOverlap p) (fpTriangle p) (tVec p + s • v)).PosSemidef ∧
      Dtet (fpOverlap p) (fpTriangle p) (tVec p + s • v) = 0 := by
  obtain ⟨_, hpd, _, _, hD0, _, _⟩ := prop_cer_quatpair_a p hp hA
  exact exists_pos_zero_on_ray_of_data (fpOverlap p)
    (fun i j hij => (overlap_pos_lt_one_of_fourPoint_pos p hp hA hij).1)
    (fpTriangle p) (tVec p) hpd hD0 v hv_ne hv_sum

/-- `prop:cer:quatpair` (c) for any line `ℓ = {t^𝕁 + s • v}` in `Π` (`v ≠ 0`, `v₀ + v₁ + v₂ = 0`). -/
theorem prop_cer_quatpair_c_line (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (v : Fin 3 → ℝ) (hv_ne : v ≠ 0)
    (hv_sum : v 0 + v 1 + v 2 = 0) :
    ∃ (sPos sNeg lam : ℝ) (qPlus qMinus : Fin 4 → Albert),
      0 < sPos ∧ sNeg < 0 ∧ 0 < lam ∧ lam < 1 ∧
      let tPlus := tVec p + sPos • v
      let tMinus := tVec p + sNeg • v
      tPlus ∈ planePi (fpOverlap p) (fpTriangle p) ∧
      tMinus ∈ planePi (fpOverlap p) (fpTriangle p) ∧
      (M_mat (fpOverlap p) (fpTriangle p) tPlus).PosSemidef ∧
      (M_mat (fpOverlap p) (fpTriangle p) tMinus).PosSemidef ∧
      Dtet (fpOverlap p) (fpTriangle p) tPlus = 0 ∧
      Dtet (fpOverlap p) (fpTriangle p) tMinus = 0 ∧
      tVec p = lam • tPlus + (1 - lam) • tMinus ∧
      (∀ i, IsAtom (qPlus i)) ∧
      (∀ i, qPlus i ∈ standardQuaternionicWindow.subalgebra.carrier) ∧
      (∀ i, IsAtom (qMinus i)) ∧
      (∀ i, qMinus i ∈ standardQuaternionicWindow.subalgebra.carrier) ∧
      (∀ i j, fpOverlap qPlus i j = fpOverlap p i j) ∧
      (∀ i j, fpOverlap qMinus i j = fpOverlap p i j) ∧
      (∀ i j k, fpTriangle qPlus i j k = fpTriangle p i j k) ∧
      (∀ i j k, fpTriangle qMinus i j k = fpTriangle p i j k) ∧
      fpDoublePair1 p = lam * fpDoublePair1 qPlus + (1 - lam) * fpDoublePair1 qMinus ∧
      fpDoublePair2 p = lam * fpDoublePair2 qPlus + (1 - lam) * fpDoublePair2 qMinus ∧
      fpDoublePair3 p = lam * fpDoublePair3 qPlus + (1 - lam) * fpDoublePair3 qMinus := by
  obtain ⟨sPos, hsPos, hM_plus, hD_plus⟩ := exists_pos_zero_on_ray p hp hA v hv_ne hv_sum
  have hnv_ne : -v ≠ 0 := neg_ne_zero.mpr hv_ne
  have hnv_sum : (-v) 0 + (-v) 1 + (-v) 2 = 0 := by
    simp only [Pi.neg_apply]; linarith
  obtain ⟨sNegMag, hsNegMag, hM_minus', hD_minus'⟩ :=
    exists_pos_zero_on_ray p hp hA (-v) hnv_ne hnv_sum
  let sNeg := -sNegMag
  have hsNeg : sNeg < 0 := neg_lt_zero.mpr hsNegMag
  have h_eq_minus : tVec p + sNeg • v = tVec p + sNegMag • (-v) := by
    dsimp only [sNeg]; rw [smul_neg, neg_smul]
  have hM_minus : (M_mat (fpOverlap p) (fpTriangle p) (tVec p + sNeg • v)).PosSemidef := by
    rw [h_eq_minus]; exact hM_minus'
  have hD_minus : Dtet (fpOverlap p) (fpTriangle p) (tVec p + sNeg • v) = 0 := by
    rw [h_eq_minus]; exact hD_minus'
  have hpi0 := tVec_mem_planePi p hp
  have htPlus_pi : tVec p + sPos • v ∈ planePi (fpOverlap p) (fpTriangle p) := by
    change (tVec p + sPos • v) 0 + (tVec p + sPos • v) 1 + (tVec p + sPos • v) 2 =
      tauOf (fpOverlap p) (fpTriangle p)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h0 : tVec p 0 + tVec p 1 + tVec p 2 = tauOf (fpOverlap p) (fpTriangle p) := hpi0
    calc
      tVec p 0 + sPos * v 0 + (tVec p 1 + sPos * v 1) + (tVec p 2 + sPos * v 2)
        = (tVec p 0 + tVec p 1 + tVec p 2) + sPos * (v 0 + v 1 + v 2) := by ring
      _ = tauOf (fpOverlap p) (fpTriangle p) := by rw [h0, hv_sum]; ring
  have htMinus_pi : tVec p + sNeg • v ∈ planePi (fpOverlap p) (fpTriangle p) := by
    change (tVec p + sNeg • v) 0 + (tVec p + sNeg • v) 1 + (tVec p + sNeg • v) 2 =
      tauOf (fpOverlap p) (fpTriangle p)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h0 : tVec p 0 + tVec p 1 + tVec p 2 = tauOf (fpOverlap p) (fpTriangle p) := hpi0
    calc
      tVec p 0 + sNeg * v 0 + (tVec p 1 + sNeg * v 1) + (tVec p 2 + sNeg * v 2)
        = (tVec p 0 + tVec p 1 + tVec p 2) + sNeg * (v 0 + v 1 + v 2) := by ring
      _ = tauOf (fpOverlap p) (fpTriangle p) := by rw [h0, hv_sum]; ring
  obtain ⟨qPlus, hqp_atom, hqp_std, hqp_o, hqp_R, hqp_t0, hqp_t1, hqp_t2⟩ :=
    prop_cer_quatpair_b p hp hA (tVec p + sPos • v) htPlus_pi hM_plus hD_plus
  obtain ⟨qMinus, hqm_atom, hqm_std, hqm_o, hqm_R, hqm_t0, hqm_t1, hqm_t2⟩ :=
    prop_cer_quatpair_b p hp hA (tVec p + sNeg • v) htMinus_pi hM_minus hD_minus
  let lam := -sNeg / (sPos - sNeg)
  have hden : 0 < sPos - sNeg := by linarith
  have hlam_pos : 0 < lam := div_pos (by linarith) hden
  have hlam_lt1 : lam < 1 := by rw [div_lt_one hden]; linarith
  have hconv : tVec p = lam • (tVec p + sPos • v) + (1 - lam) • (tVec p + sNeg • v) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lam]
    field_simp [hden.ne']
    ring
  have ht0_aff : fpDoublePair1 p = lam * fpDoublePair1 qPlus + (1 - lam) * fpDoublePair1 qMinus := by
    have hc := congrFun hconv 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
    rw [hqp_t0, hqm_t0]
    simpa [tVec] using hc
  have ht1_aff : fpDoublePair2 p = lam * fpDoublePair2 qPlus + (1 - lam) * fpDoublePair2 qMinus := by
    have hc := congrFun hconv 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
    rw [hqp_t1, hqm_t1]
    simpa [tVec] using hc
  have ht2_aff : fpDoublePair3 p = lam * fpDoublePair3 qPlus + (1 - lam) * fpDoublePair3 qMinus := by
    have hc := congrFun hconv 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
    rw [hqp_t2, hqm_t2]
    simpa [tVec] using hc
  exact ⟨sPos, sNeg, lam, qPlus, qMinus, hsPos, hsNeg, hlam_pos, hlam_lt1,
    htPlus_pi, htMinus_pi, hM_plus, hM_minus, hD_plus, hD_minus, hconv,
    hqp_atom, hqp_std, hqm_atom, hqm_std, hqp_o, hqm_o, hqp_R, hqm_R,
    ht0_aff, ht1_aff, ht2_aff⟩

/-- Explicit specialization of `prop_cer_quatpair_c_line` along `v = (1, -1, 0)`. -/
theorem prop_cer_quatpair_c (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ (lam : ℝ) (qPlus qMinus : Fin 4 → Albert),
      0 < lam ∧ lam < 1 ∧
      (∀ i, IsAtom (qPlus i)) ∧
      (∀ i, qPlus i ∈ standardQuaternionicWindow.subalgebra.carrier) ∧
      (∀ i, IsAtom (qMinus i)) ∧
      (∀ i, qMinus i ∈ standardQuaternionicWindow.subalgebra.carrier) ∧
      (∀ i j, fpOverlap qPlus i j = fpOverlap p i j) ∧
      (∀ i j, fpOverlap qMinus i j = fpOverlap p i j) ∧
      (∀ i j k, fpTriangle qPlus i j k = fpTriangle p i j k) ∧
      (∀ i j k, fpTriangle qMinus i j k = fpTriangle p i j k) ∧
      fpDoublePair1 p = lam * fpDoublePair1 qPlus + (1 - lam) * fpDoublePair1 qMinus ∧
      fpDoublePair2 p = lam * fpDoublePair2 qPlus + (1 - lam) * fpDoublePair2 qMinus ∧
      fpDoublePair3 p = lam * fpDoublePair3 qPlus + (1 - lam) * fpDoublePair3 qMinus := by
  let v : Fin 3 → ℝ := ![1, -1, 0]
  have hv_ne : v ≠ 0 := by
    intro h; have := congrFun h 0; simp [v] at this
  have hv_sum : v 0 + v 1 + v 2 = 0 := by simp [v]
  obtain ⟨_, _, lam, qPlus, qMinus, _, _, hlam0, hlam1, _, _, _, _, _, _, _,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    prop_cer_quatpair_c_line p hp hA v hv_ne hv_sum
  exact ⟨lam, qPlus, qMinus, hlam0, hlam1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end AlbertSequential.MatchingModels
