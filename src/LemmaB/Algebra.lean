module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Lemma B (lem:cer:negative), part 1: the eight-dimensional algebra `𝒞` by structure constants

Paper: core `sec:cer`, paragraph "The comparison form" (eq:cer:Cbasis, eq:cer:epschi,
eq:cer:ghost). The paper builds `𝒞` as the Clifford algebra `Cl_{0,3}` with `ε_a = Σ Λ_{ak} γ_k`,
`M̂ = Λ Λᵀ`, which presupposes `M̂` positive definite. Here `𝒞` is presented by **structure constants** in the basis of eq:cer:Cbasis

  index 0: `1`,  1–3: `ε_1, ε_2, ε_3`,  4–6: `χ_1, χ_2, χ_3`,  7: `g`,

polynomial in the thirteen parameters, with no square root and no positivity. Only left
multiplication by the generators `ε_a` is needed (the model uses only left multiplications by
`ĥ_a = ĉ_a + ε_a`, `ĥ_a^* = ĉ_a - ε_a` and the reflection `ς`), so `𝒞` enters through the
operators `epsMul a` (the matrices `N_a`), and the form `ϑ(ū v)` through its Gram matrix `W` in
this basis. The paper's facts are proved below as lemmas: the Clifford relations
`ε_a ε_b + ε_b ε_a = -2 M̂_ab`, skewness of `ε_a` (conjugation), `[ε_a β]_g = [β]_{χ_a}`
(eq:cer:epschi), the ghost formulas (eq:cer:ghost), centrality of `Γ̂`, `Γ̂² = det M̂`, and the
uniqueness of a symmetric form with skew generators and `⟨1, β⟩ = [β]_1` (so this form is the
paper's `ϑ(ū v)`).

Everything is over an arbitrary field `K`.
-/

@[expose] public section

namespace LemmaB

/-- The thirteen parameters of the comparison form, in the paper's notation:
`m_B, m_C, m_D` (`m_x = 1/o_Ax`), `ĉ_1, ĉ_2, ĉ_3`, the symmetric matrix `M̂`, and `b̂`.
Edges: `1 = BC`, `2 = CD`, `3 = DB`. -/
structure Params (K : Type*) where
  mB : K
  mC : K
  mD : K
  c1 : K
  c2 : K
  c3 : K
  M11 : K
  M22 : K
  M33 : K
  M12 : K
  M13 : K
  M23 : K
  b : K

variable {K : Type*} [Field K]

/-- Elements of `𝒞` as coordinate vectors in the basis `1, ε_1, ε_2, ε_3, χ_1, χ_2, χ_3, g`. -/
abbrev C8 (K : Type*) := Fin 8 → K

namespace Params

variable (p : Params K)

/-- Adjugate of `M̂`. -/
def A11 : K := p.M22 * p.M33 - p.M23 ^ 2
def A22 : K := p.M11 * p.M33 - p.M13 ^ 2
def A33 : K := p.M11 * p.M22 - p.M12 ^ 2
def A12 : K := p.M13 * p.M23 - p.M12 * p.M33
def A13 : K := p.M12 * p.M23 - p.M13 * p.M22
def A23 : K := p.M12 * p.M13 - p.M11 * p.M23

/-- `det M̂`. -/
def detM : K :=
  p.M11 * p.M22 * p.M33 + 2 * p.M12 * p.M13 * p.M23
    - p.M11 * p.M23 ^ 2 - p.M22 * p.M13 ^ 2 - p.M33 * p.M12 ^ 2

/-- `D̂ = det M̂ - b̂²` (paper, display before eq:cer:Dhat). -/
def Dhat : K := p.detM - p.b ^ 2

/-- `μ_x = m_x - 1`. -/
def μB : K := p.mB - 1
def μC : K := p.mC - 1
def μD : K := p.mD - 1
/-- `μ = μ_B μ_C μ_D`, `m = m_B m_C m_D`. -/
def μ : K := p.μB * p.μC * p.μD
def m : K := p.mB * p.mC * p.mD
/-- `α_x = μ / μ_x` (as the product of the other two `μ`). -/
def αB : K := p.μC * p.μD
def αC : K := p.μD * p.μB
def αD : K := p.μB * p.μC

/-- `d_a = (ĉ_a - 1)² + M̂_aa`. -/
def d1 : K := (p.c1 - 1) ^ 2 + p.M11
def d2 : K := (p.c2 - 1) ^ 2 + p.M22
def d3 : K := (p.c3 - 1) ^ 2 + p.M33

/-- `Ŝ` evaluated at shifted `ĉ`: `Ŝ' = c'_1 c'_2 c'_3 - c'_1 M̂_23 - c'_2 M̂_13 - c'_3 M̂_12`. -/
def Sprime : K :=
  (p.c1 - 1) * (p.c2 - 1) * (p.c3 - 1) - (p.c1 - 1) * p.M23 - (p.c2 - 1) * p.M13
    - (p.c3 - 1) * p.M12

/-- The paper's `τ = μ - μ_D d_1 - μ_B d_2 - μ_C d_3 + 2(b̂ + Ŝ')`
(proof of lem:cer:negative, "Where the trace relation enters"). Its vanishing is the only
use of the trace relation. -/
def tau : K := p.μ - p.μD * p.d1 - p.μB * p.d2 - p.μC * p.d3 + 2 * (p.b + p.Sprime)

end Params

variable (p : Params K)

/-- Left multiplication by `ε_1` (the matrix `N_1`; columns = input coordinates). -/
def eps1 (v : C8 K) : C8 K :=
  ![-p.M11 * v 1 - p.M12 * v 2 - p.M13 * v 3 + p.b * v 4,
    v 0 - p.M13 * v 5 + p.M12 * v 6 - p.b * v 7,
    p.M13 * v 4 - p.M11 * v 6,
    -p.M12 * v 4 + p.M11 * v 5,
    -p.M11 * v 7,
    -v 3 - p.M12 * v 7,
    v 2 - p.M13 * v 7,
    v 4]

/-- Left multiplication by `ε_2`. -/
def eps2 (v : C8 K) : C8 K :=
  ![-p.M12 * v 1 - p.M22 * v 2 - p.M23 * v 3 + p.b * v 5,
    -p.M23 * v 5 + p.M22 * v 6,
    v 0 + p.M23 * v 4 - p.M12 * v 6 - p.b * v 7,
    -p.M22 * v 4 + p.M12 * v 5,
    v 3 - p.M12 * v 7,
    -p.M22 * v 7,
    -v 1 - p.M23 * v 7,
    v 5]

/-- Left multiplication by `ε_3`. -/
def eps3 (v : C8 K) : C8 K :=
  ![-p.M13 * v 1 - p.M23 * v 2 - p.M33 * v 3 + p.b * v 6,
    p.M23 * v 6 - p.M33 * v 5,
    p.M33 * v 4 - p.M13 * v 6,
    v 0 - p.M23 * v 4 + p.M13 * v 5 - p.b * v 7,
    -v 2 - p.M13 * v 7,
    v 1 - p.M23 * v 7,
    -p.M33 * v 7,
    v 6]

/-- The bilinear form `⟨u, v⟩_𝒞 = ϑ(ū v)` in the basis of eq:cer:Cbasis:
`⟨1,1⟩ = 1`, `⟨ε_a, ε_b⟩ = M̂_ab`, `⟨χ_a, χ_b⟩ = (adj M̂)_ab`, `⟨ε_a, χ_b⟩ = -b̂ δ_ab`,
`⟨g, g⟩ = D̂`, all other basis pairings zero. -/
def W (v w : C8 K) : K :=
  v 0 * w 0
  + p.M11 * v 1 * w 1 + p.M22 * v 2 * w 2 + p.M33 * v 3 * w 3
  + p.M12 * (v 1 * w 2 + v 2 * w 1) + p.M13 * (v 1 * w 3 + v 3 * w 1)
  + p.M23 * (v 2 * w 3 + v 3 * w 2)
  + p.A11 * v 4 * w 4 + p.A22 * v 5 * w 5 + p.A33 * v 6 * w 6
  + p.A12 * (v 4 * w 5 + v 5 * w 4) + p.A13 * (v 4 * w 6 + v 6 * w 4)
  + p.A23 * (v 5 * w 6 + v 6 * w 5)
  - p.b * (v 1 * w 4 + v 4 * w 1 + v 2 * w 5 + v 5 * w 2 + v 3 * w 6 + v 6 * w 3)
  + p.Dhat * v 7 * w 7

/-- The reflection `ς(β) = β - 2[β]_g g`. -/
def sig (v : C8 K) : C8 K := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, -v 7]

/-- Basis vectors `1` and `g` of `𝒞`, and `ε_a = ε_a · 1`. -/
def one8 : C8 K := ![1, 0, 0, 0, 0, 0, 0, 0]
def gee : C8 K := ![0, 0, 0, 0, 0, 0, 0, 1]
def e1v : C8 K := ![0, 1, 0, 0, 0, 0, 0, 0]
def e2v : C8 K := ![0, 0, 1, 0, 0, 0, 0, 0]
def e3v : C8 K := ![0, 0, 0, 1, 0, 0, 0, 0]

/-- `ĥ_a = ĉ_a + ε_a` and `ĥ_a^* = ĉ_a - ε_a`, acting by left multiplication. -/
def h1 (v : C8 K) : C8 K := p.c1 • v + eps1 p v
def h2 (v : C8 K) : C8 K := p.c2 • v + eps2 p v
def h3 (v : C8 K) : C8 K := p.c3 • v + eps3 p v
def h1s (v : C8 K) : C8 K := p.c1 • v - eps1 p v
def h2s (v : C8 K) : C8 K := p.c2 • v - eps2 p v
def h3s (v : C8 K) : C8 K := p.c3 • v - eps3 p v

/-- The volume element `Γ̂ = ε_1ε_2ε_3 + M̂_23 ε_1 - M̂_13 ε_2 + M̂_12 ε_3` (eq:fp:volume). -/
def Gam (v : C8 K) : C8 K :=
  eps1 p (eps2 p (eps3 p v)) + p.M23 • eps1 p v - p.M13 • eps2 p v + p.M12 • eps3 p v

section relations

/-! ### Clifford relations (paper: `ε_a ε_b + ε_b ε_a = -2 M̂_ab`) -/

theorem eps1_sq (v : C8 K) : eps1 p (eps1 p v) = (-p.M11) • v := by
  funext i; fin_cases i <;> simp [eps1] <;> ring

theorem eps2_sq (v : C8 K) : eps2 p (eps2 p v) = (-p.M22) • v := by
  funext i; fin_cases i <;> simp [eps2] <;> ring

theorem eps3_sq (v : C8 K) : eps3 p (eps3 p v) = (-p.M33) • v := by
  funext i; fin_cases i <;> simp [eps3] <;> ring

theorem eps12_anti (v : C8 K) :
    eps1 p (eps2 p v) + eps2 p (eps1 p v) = (-2 * p.M12) • v := by
  funext i; fin_cases i <;> simp [eps1, eps2] <;> ring

theorem eps13_anti (v : C8 K) :
    eps1 p (eps3 p v) + eps3 p (eps1 p v) = (-2 * p.M13) • v := by
  funext i; fin_cases i <;> simp [eps1, eps3] <;> ring

theorem eps23_anti (v : C8 K) :
    eps2 p (eps3 p v) + eps3 p (eps2 p v) = (-2 * p.M23) • v := by
  funext i; fin_cases i <;> simp [eps2, eps3] <;> ring

/-! ### The basis of eq:cer:Cbasis is generated from `1` -/

theorem eps_one : eps1 p (one8) = e1v ∧ eps2 p (one8) = e2v ∧ eps3 p (one8) = e3v := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp [eps1, eps2, eps3, one8, e1v, e2v, e3v]

/-- `χ_1 = ε_2ε_3 + M̂_23`, `χ_2 = ε_3ε_1 + M̂_13`, `χ_3 = ε_1ε_2 + M̂_12`,
`g = Γ̂ - b̂` (eq:cer:Cbasis), as elements obtained from `1`. -/
theorem chi_basis :
    eps2 p (eps3 p one8) + p.M23 • one8 = ![0, 0, 0, 0, 1, 0, 0, 0] ∧
    eps3 p (eps1 p one8) + p.M13 • one8 = ![0, 0, 0, 0, 0, 1, 0, 0] ∧
    eps1 p (eps2 p one8) + p.M12 • one8 = ![0, 0, 0, 0, 0, 0, 1, 0] ∧
    Gam p one8 - p.b • one8 = gee := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
    simp [eps1, eps2, eps3, Gam, one8, gee] <;> ring

/-! ### eq:cer:epschi: `[ε_a β]_g = [β]_{χ_a}` -/

theorem eps1_g (v : C8 K) : eps1 p v 7 = v 4 := by simp [eps1]
theorem eps2_g (v : C8 K) : eps2 p v 7 = v 5 := by simp [eps2]
theorem eps3_g (v : C8 K) : eps3 p v 7 = v 6 := by simp [eps3]

/-! ### Volume element: central, square `det M̂` -/

theorem Gam_comm1 (v : C8 K) : Gam p (eps1 p v) = eps1 p (Gam p v) := by
  funext i; fin_cases i <;> simp [Gam, eps1, eps2, eps3] <;> ring

theorem Gam_comm2 (v : C8 K) : Gam p (eps2 p v) = eps2 p (Gam p v) := by
  funext i; fin_cases i <;> simp [Gam, eps1, eps2, eps3] <;> ring

theorem Gam_comm3 (v : C8 K) : Gam p (eps3 p v) = eps3 p (Gam p v) := by
  funext i; fin_cases i <;> simp [Gam, eps1, eps2, eps3] <;> ring

theorem Gam_sq (v : C8 K) : Gam p (Gam p v) = p.detM • v := by
  funext i; fin_cases i <;> simp [Gam, eps1, eps2, eps3, Params.detM] <;> ring

/-! ### The form -/

theorem W_symm (v w : C8 K) : W p v w = W p w v := by
  simp only [W]; ring

/-- Skewness of `ε_1` (conjugation reverses the sign of `ε_a`). -/
theorem W_eps1 (v w : C8 K) : W p v (eps1 p w) = -W p (eps1 p v) w := by
  simp [W, eps1, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13, Params.A23,
    Params.Dhat, Params.detM]
  ring

theorem W_eps2 (v w : C8 K) : W p v (eps2 p w) = -W p (eps2 p v) w := by
  simp [W, eps2, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13, Params.A23,
    Params.Dhat, Params.detM]
  ring

theorem W_eps3 (v w : C8 K) : W p v (eps3 p w) = -W p (eps3 p v) w := by
  simp [W, eps3, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13, Params.A23,
    Params.Dhat, Params.detM]
  ring

theorem W_sig (v w : C8 K) : W p v (sig w) = W p (sig v) w := by
  simp [W, sig]

theorem W_one (v : C8 K) : W p one8 v = v 0 := by
  simp [W, one8]

/-- eq:cer:ghost, first identity: `⟨β, g⟩ = D̂ [β]_g`. -/
theorem W_gee (v : C8 K) : W p v gee = p.Dhat * v 7 := by
  simp [W, gee]

/-- eq:cer:ghost, second identity: with `g_a = -ε_a g`, `⟨β, g_a⟩ = D̂ [β]_{χ_a}`. -/
theorem W_g1 (v : C8 K) : W p v (-eps1 p gee) = p.Dhat * v 4 := by
  simp [W, eps1, gee, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13, Params.A23, Params.Dhat, Params.detM]; ring

theorem W_g2 (v : C8 K) : W p v (-eps2 p gee) = p.Dhat * v 5 := by
  simp [W, eps2, gee, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13, Params.A23, Params.Dhat, Params.detM]; ring

theorem W_g3 (v : C8 K) : W p v (-eps3 p gee) = p.Dhat * v 6 := by
  simp [W, eps3, gee, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13, Params.A23, Params.Dhat, Params.detM]; ring

/-- Bilinearity of `W`. -/
theorem W_add_left (u v w : C8 K) : W p (u + v) w = W p u w + W p v w := by
  simp only [W, Pi.add_apply]; ring
theorem W_add_right (u v w : C8 K) : W p u (v + w) = W p u v + W p u w := by
  simp only [W, Pi.add_apply]; ring
theorem W_smul_left (c : K) (v w : C8 K) : W p (c • v) w = c * W p v w := by
  simp only [W, Pi.smul_apply, smul_eq_mul]; ring
theorem W_smul_right (c : K) (v w : C8 K) : W p v (c • w) = c * W p v w := by
  simp only [W, Pi.smul_apply, smul_eq_mul]; ring

/-- `W` as a bilinear map. -/
def Wl : C8 K →ₗ[K] C8 K →ₗ[K] K :=
  LinearMap.mk₂ K (W p) (W_add_left p) (W_smul_left p) (W_add_right p) (W_smul_right p)

@[simp] theorem Wl_apply (v w : C8 K) : Wl p v w = W p v w := rfl

/-- Uniqueness: any bilinear map `B` on `𝒞` for which the three generators are skew and
`B 1 β = [β]_1` is the form `W`. So `W` is the paper's `ϑ(ū v)`, whatever presentation of `𝒞`
is used (the paper's `ϑ` is the `1`-coefficient in the basis eq:cer:Cbasis and conjugation
reverses the generators). -/
theorem W_unique (B : C8 K →ₗ[K] C8 K →ₗ[K] K)
    (h1 : ∀ v w, B v (eps1 p w) = -B (eps1 p v) w)
    (h2 : ∀ v w, B v (eps2 p w) = -B (eps2 p v) w)
    (h3 : ∀ v w, B v (eps3 p w) = -B (eps3 p v) w)
    (hone : ∀ w, B one8 w = w 0) (v w : C8 K) : B v w = W p v w := by
  -- express every `v` through words in the generators applied to `1`
  have hv : v = v 0 • one8 + v 1 • eps1 p one8 + v 2 • eps2 p one8 + v 3 • eps3 p one8
      + v 4 • (eps2 p (eps3 p one8) + p.M23 • one8)
      + v 5 • (eps3 p (eps1 p one8) + p.M13 • one8)
      + v 6 • (eps1 p (eps2 p one8) + p.M12 • one8)
      + v 7 • (eps1 p (eps2 p (eps3 p one8)) + p.M23 • eps1 p one8 - p.M13 • eps2 p one8
          + p.M12 • eps3 p one8 - p.b • one8) := by
    funext i; fin_cases i <;> simp [eps1, eps2, eps3, one8] <;> ring
  have h1' : ∀ v w, B (eps1 p v) w = -B v (eps1 p w) := fun v w => by rw [h1]; ring
  have h2' : ∀ v w, B (eps2 p v) w = -B v (eps2 p w) := fun v w => by rw [h2]; ring
  have h3' : ∀ v w, B (eps3 p v) w = -B v (eps3 p w) := fun v w => by rw [h3]; ring
  rw [hv]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, h1', h2', h3', map_neg, hone]
  simp [W, eps1, eps2, eps3, one8, Params.A11, Params.A22, Params.A33, Params.A12, Params.A13,
    Params.A23, Params.Dhat, Params.detM]
  ring

end relations

section linear

/-! ### Linearity of the generators and of `ς` -/

theorem sig_add (v w : C8 K) : sig (v + w) = sig v + sig w := by
  funext i; fin_cases i <;> simp [sig]; ring
theorem sig_smul (c : K) (v : C8 K) : sig (c • v) = c • sig v := by
  funext i; fin_cases i <;> simp [sig]
theorem sig_sub (v w : C8 K) : sig (v - w) = sig v - sig w := by
  funext i; fin_cases i <;> simp [sig]; ring

theorem eps1_add (v w : C8 K) : eps1 p (v + w) = eps1 p v + eps1 p w := by
  funext i; fin_cases i <;> simp [eps1] <;> ring
theorem eps2_add (v w : C8 K) : eps2 p (v + w) = eps2 p v + eps2 p w := by
  funext i; fin_cases i <;> simp [eps2] <;> ring
theorem eps3_add (v w : C8 K) : eps3 p (v + w) = eps3 p v + eps3 p w := by
  funext i; fin_cases i <;> simp [eps3] <;> ring
theorem eps1_smul (c : K) (v : C8 K) : eps1 p (c • v) = c • eps1 p v := by
  funext i; fin_cases i <;> simp [eps1] <;> ring
theorem eps2_smul (c : K) (v : C8 K) : eps2 p (c • v) = c • eps2 p v := by
  funext i; fin_cases i <;> simp [eps2] <;> ring
theorem eps3_smul (c : K) (v : C8 K) : eps3 p (c • v) = c • eps3 p v := by
  funext i; fin_cases i <;> simp [eps3] <;> ring
theorem eps1_sub (v w : C8 K) : eps1 p (v - w) = eps1 p v - eps1 p w := by
  funext i; fin_cases i <;> simp [eps1] <;> ring
theorem eps2_sub (v w : C8 K) : eps2 p (v - w) = eps2 p v - eps2 p w := by
  funext i; fin_cases i <;> simp [eps2] <;> ring
theorem eps3_sub (v w : C8 K) : eps3 p (v - w) = eps3 p v - eps3 p w := by
  funext i; fin_cases i <;> simp [eps3] <;> ring

theorem W_sub_left (u v w : C8 K) : W p (u - v) w = W p u w - W p v w := by
  simp only [W, Pi.sub_apply]; ring
theorem W_sub_right (u v w : C8 K) : W p u (v - w) = W p u v - W p u w := by
  simp only [W, Pi.sub_apply]; ring

end linear

end LemmaB
