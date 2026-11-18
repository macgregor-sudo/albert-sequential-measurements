module

public import LemmaB.Model

/-!
# Lemma B, part 3: the vectors `K_x[β]`, their sources, and the three vectors `Ξ_x`

Paper: proof of lem:cer:negative, paragraphs "Sources", "Where the trace relation enters",
"Six vectors", "The three vectors". Polar vectors `⟨u⟩ = (-u_B-u_C-u_D; u_B; u_C; u_D)`;
`ĥ_a' = ĥ_a - 1`, `ĥ_a'^* = ĥ_a^* - 1`;
`K_B[β] = ⟨(μ_Cμ_D - d_2)β, (ĥ_2'ĥ_3' - μ_D ĥ_1'^*)β, (ĥ_2'^*ĥ_1'^* - μ_C ĥ_3')β⟩`, and `K_C`, `K_D`
by the cyclic relabelling `B → C → D → B`, `1 → 2 → 3 → 1`;
`k_B = K_B[ε_1], k'_B = K_B[ε_2], k_C = K_C[ε_2], k'_C = K_C[ε_3], k_D = K_D[ε_3], k'_D = K_D[ε_1]`;
`Ξ_B = 2α_B((g;0;0;0) + ⟨k_D⟩) + μ_B⟨k'_B⟩ - μ_C⟨k'_C⟩ - μ_D⟨k'_D⟩`, cyclically.

The source computations `T⟨k⟩` are the only place where the hypothesis `τ = 0` (the trace
relation) is used; it appears as the explicit hypothesis `hτ : p.tau = 0`.
-/

@[expose] public section

namespace LemmaB

variable {K : Type*} [Field K] (p : Params K)

/-- `⟨u⟩ = (-u_B - u_C - u_D; u_B; u_C; u_D)`. -/
def polar (uB uC uD : C8 K) : V K := ![-(uB + uC + uD), uB, uC, uD]

/-- `(g; 0; 0; 0)`. -/
def gA : V K := ![gee, 0, 0, 0]

/-- `ĥ_a' = ĥ_a - 1` and `ĥ_a'^* = ĥ_a^* - 1`. -/
def h1' (v : C8 K) : C8 K := (p.c1 - 1) • v + eps1 p v
def h2' (v : C8 K) : C8 K := (p.c2 - 1) • v + eps2 p v
def h3' (v : C8 K) : C8 K := (p.c3 - 1) • v + eps3 p v
def h1s' (v : C8 K) : C8 K := (p.c1 - 1) • v - eps1 p v
def h2s' (v : C8 K) : C8 K := (p.c2 - 1) • v - eps2 p v
def h3s' (v : C8 K) : C8 K := (p.c3 - 1) • v - eps3 p v

/-- `K_B[β]`, `K_C[β]`, `K_D[β]`. -/
def KB (β : C8 K) : V K :=
  polar ((p.μC * p.μD - p.d2) • β) (h2' p (h3' p β) - p.μD • h1s' p β)
    (h2s' p (h1s' p β) - p.μC • h3' p β)
def KC (β : C8 K) : V K :=
  polar (h3s' p (h2s' p β) - p.μD • h1' p β) ((p.μD * p.μB - p.d3) • β)
    (h3' p (h1' p β) - p.μB • h2s' p β)
def KD (β : C8 K) : V K :=
  polar (h1' p (h2' p β) - p.μC • h3s' p β) (h1s' p (h3s' p β) - p.μB • h2' p β)
    ((p.μB * p.μC - p.d1) • β)

/-- The six vectors `k_x`, `k'_x`. -/
def kB : V K := KB p e1v
def kB' : V K := KB p e2v
def kC : V K := KC p e2v
def kC' : V K := KC p e3v
def kD : V K := KD p e3v
def kD' : V K := KD p e1v

/-- The three vectors `Ξ_B, Ξ_C, Ξ_D`. -/
def XiB : V K := (2 * p.αB) • (gA + kD p) + p.μB • kB' p - p.μC • kC' p - p.μD • kD' p
def XiC : V K := (2 * p.αC) • (gA + kB p) + p.μC • kC' p - p.μD • kD' p - p.μB • kB' p
def XiD : V K := (2 * p.αD) • (gA + kC p) + p.μD • kD' p - p.μB • kB' p - p.μC • kC' p

/-- `Ξ` indexed by `0 = B, 1 = C, 2 = D`. -/
def Xi : Fin 3 → V K := ![XiB p, XiC p, XiD p]

theorem src_sub (F G : V K) (x : Fin 4) : src p (F - G) x = src p F x - src p G x := by
  rw [eq_sub_iff_add_eq, ← src_add, sub_add_cancel]

theorem T_xA (x : Fin 4) (v : C8 K) : T p x 0 v = v := by
  fin_cases x <;> rfl

/-- `T(g;0;0;0) = (g;g;g;g)`. -/
theorem src_gA : src p (gA (K := K)) = ![gee, gee, gee, gee] := by
  funext x; fin_cases x <;>
    simp [src, Fin.sum_univ_four, gA, T_zero, T_xA]

section sources

variable (hτ : p.tau = 0)
include hτ

set_option maxHeartbeats 4000000 in
/-- `T⟨k_B⟩ = (0; -2g; 0; -2g)` (uses `τ = 0`). -/
theorem src_kB : src p (kB p) = ![0, (-2 : K) • gee, 0, (-2 : K) • gee] := by
  have h := hτ
  simp only [Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2,
    Params.d3, Params.Sprime] at h
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [src, Fin.sum_univ_four, T, kB, KB, polar, h1, h2, h3, h1s, h2s, h3s, h1', h2', h3',
      h1s', h2s', h3s', sig, eps1, eps2, eps3, e1v, gee, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;>
    first | ring1 | linear_combination h | linear_combination -h

set_option maxHeartbeats 4000000 in
/-- `T⟨k_C⟩ = (0; -2g; -2g; 0)` (uses `τ = 0`). -/
theorem src_kC : src p (kC p) = ![0, (-2 : K) • gee, (-2 : K) • gee, 0] := by
  have h := hτ
  simp only [Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2,
    Params.d3, Params.Sprime] at h
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [src, Fin.sum_univ_four, T, kC, KC, polar, h1, h2, h3, h1s, h2s, h3s, h1', h2', h3',
      h1s', h2s', h3s', sig, eps1, eps2, eps3, e2v, gee, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;>
    first | ring1 | linear_combination h | linear_combination -h

set_option maxHeartbeats 4000000 in
/-- `T⟨k_D⟩ = (0; 0; -2g; -2g)` (uses `τ = 0`). -/
theorem src_kD : src p (kD p) = ![0, 0, (-2 : K) • gee, (-2 : K) • gee] := by
  have h := hτ
  simp only [Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2,
    Params.d3, Params.Sprime] at h
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [src, Fin.sum_univ_four, T, kD, KD, polar, h1, h2, h3, h1s, h2s, h3s, h1', h2', h3',
      h1s', h2s', h3s', sig, eps1, eps2, eps3, e3v, gee, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;>
    first | ring1 | linear_combination h | linear_combination -h

set_option maxHeartbeats 4000000 in
/-- `T⟨k'_B⟩ = (0; -2ĥ_2'^* g; 0; 0)` (uses `τ = 0`). -/
theorem src_kB' : src p (kB' p) = ![0, (-2 : K) • h2s' p gee, 0, 0] := by
  have h := hτ
  simp only [Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2,
    Params.d3, Params.Sprime] at h
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [src, Fin.sum_univ_four, T, kB', KB, polar, h1, h2, h3, h1s, h2s, h3s, h1', h2', h3',
      h1s', h2s', h3s', sig, eps1, eps2, eps3, e2v, gee, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;>
    first | ring1 | linear_combination h | linear_combination -h

set_option maxHeartbeats 4000000 in
/-- `T⟨k'_C⟩ = (0; 0; -2ĥ_3'^* g; 0)` (uses `τ = 0`). -/
theorem src_kC' : src p (kC' p) = ![0, 0, (-2 : K) • h3s' p gee, 0] := by
  have h := hτ
  simp only [Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2,
    Params.d3, Params.Sprime] at h
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [src, Fin.sum_univ_four, T, kC', KC, polar, h1, h2, h3, h1s, h2s, h3s, h1', h2', h3',
      h1s', h2s', h3s', sig, eps1, eps2, eps3, e3v, gee, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;>
    first | ring1 | linear_combination h | linear_combination -h

set_option maxHeartbeats 4000000 in
/-- `T⟨k'_D⟩ = (0; 0; 0; -2ĥ_1'^* g)` (uses `τ = 0`). -/
theorem src_kD' : src p (kD' p) = ![0, 0, 0, (-2 : K) • h1s' p gee] := by
  have h := hτ
  simp only [Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2,
    Params.d3, Params.Sprime] at h
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [src, Fin.sum_univ_four, T, kD', KD, polar, h1, h2, h3, h1s, h2s, h3s, h1', h2', h3',
      h1s', h2s', h3s', sig, eps1, eps2, eps3, e1v, gee, Params.μB, Params.μC, Params.μD,
      Params.d1, Params.d2, Params.d3] <;>
    first | ring1 | linear_combination h | linear_combination -h

end sources

end LemmaB
