module

public import LemmaB.Lemma
-- build order only: keeps large modules from compiling concurrently (memory)
import AppF.GlennieS

/-!
# Lemma B, part 9: the intermediate claims printed in the proof of lem:cer:negative

These are not needed for `lemmaB_model` (which goes through `Ξ` directly), but they check the
paper's printed intermediate statements one by one, in the paper's own route:

* `ĥ_a ĥ_a^* = ĥ_a^* ĥ_a = ĉ_a² + M̂_aa` and `ĥ_a' ĥ_a'^* = d_a` (scalars);
* "Where the trace relation enters": for every `β`, `(Θ⁰ K_B[β])_C = (Θ⁰ K_B[β])_D = 0` and
  `(Θ⁰ K_B[β])_B = (τ + 2g)β`, with `g = Γ̂ - b̂` (no trace relation used), and cyclically;
* "Six vectors": the printed `g`- and `χ`-coefficients of `k_B`, `k'_B` and the ghost data;
* "Accessibility": the printed products of `ĥ`'s for the 28 amplitudes (every `ς` deletable).
-/

@[expose] public section

namespace LemmaB

variable {K : Type*} [Field K] (p : Params K)

theorem h1_h1s (v : C8 K) : h1 p (h1s p v) = (p.c1 ^ 2 + p.M11) • v ∧
    h1s p (h1 p v) = (p.c1 ^ 2 + p.M11) • v := by
  constructor <;> funext i <;> fin_cases i <;> simp [h1, h1s, eps1, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem h1'_h1s' (v : C8 K) : h1' p (h1s' p v) = p.d1 • v := by
  funext i; fin_cases i <;> simp [h1', h1s', eps1, Params.d1, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Untwisted polar operator `Θ⁰` (off-diagonal entries `ĥ_1'` (BC), `ĥ_1'^*` (CB), `ĥ_2'`
(CD), `ĥ_2'^*` (DC), `ĥ_3'` (DB), `ĥ_3'^*` (BD); diagonal `μ_x`), on the frames `B, C, D`. -/
def theta0 (uB uC uD : C8 K) : Fin 3 → C8 K :=
  ![p.μB • uB + h1' p uC + h3s' p uD,
    h1s' p uB + p.μC • uC + h2' p uD,
    h3' p uB + h2s' p uC + p.μD • uD]

set_option maxHeartbeats 8000000 in
/-- "Where the trace relation enters", frame `B`, for every `β` (no trace relation). -/
theorem theta0_KB (β : C8 K) :
    theta0 p (KB p β 1) (KB p β 2) (KB p β 3) =
      ![p.tau • β + (2 : K) • (Gam p β - p.b • β), 0, 0] := by
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [theta0, KB, polar, h1', h2', h3', h1s', h2s', h3s', Gam, eps1, eps2, eps3,
      Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2, Params.d3,
      Params.Sprime, Matrix.vecHead, Matrix.vecTail] <;> ring

set_option maxHeartbeats 8000000 in
theorem theta0_KC (β : C8 K) :
    theta0 p (KC p β 1) (KC p β 2) (KC p β 3) =
      ![0, p.tau • β + (2 : K) • (Gam p β - p.b • β), 0] := by
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [theta0, KC, polar, h1', h2', h3', h1s', h2s', h3s', Gam, eps1, eps2, eps3,
      Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2, Params.d3,
      Params.Sprime, Matrix.vecHead, Matrix.vecTail] <;> ring

set_option maxHeartbeats 8000000 in
theorem theta0_KD (β : C8 K) :
    theta0 p (KD p β 1) (KD p β 2) (KD p β 3) =
      ![0, 0, p.tau • β + (2 : K) • (Gam p β - p.b • β)] := by
  funext x; fin_cases x <;> funext i <;> fin_cases i <;>
    simp [theta0, KD, polar, h1', h2', h3', h1s', h2s', h3s', Gam, eps1, eps2, eps3,
      Params.tau, Params.μ, Params.μB, Params.μC, Params.μD, Params.d1, Params.d2, Params.d3,
      Params.Sprime, Matrix.vecHead, Matrix.vecTail] <;> ring

set_option maxHeartbeats 4000000 in
/-- Paper, "Six vectors": coefficients of `k_B` and `k'_B` entering eq:cer:twist, and the ghost
data `([·]_g, [·]_{χ_{a(w)}})` at the frames `B, C, D` (`a(B), a(C), a(D) = 2, 3, 1`). -/
theorem kB_data :
    -- k_B: [u_C]_g = 1, [u_C]_{χ_2} = ĉ_2 - 1, [u_D]_{χ_3} = ĉ_1 - 1, no other g-coefficient
    kB p 2 7 = 1 ∧ kB p 2 5 = p.c2 - 1 ∧ kB p 3 6 = p.c1 - 1 ∧ kB p 1 7 = 0 ∧ kB p 3 7 = 0 ∧
    -- ghost data of k_B: (0,0) at B, (1, 1 - ĉ_3) at C, (0,0) at D
    kB p 1 5 = 0 ∧ kB p 2 6 = 1 - p.c3 ∧ kB p 3 4 = 0 ∧
    -- k'_B: no g-coefficient, [u_C]_{χ_2} = 0, [u_D]_{χ_3} = 1 - ĉ_2
    kB' p 1 7 = 0 ∧ kB' p 2 7 = 0 ∧ kB' p 3 7 = 0 ∧ kB' p 2 5 = 0 ∧ kB' p 3 6 = 1 - p.c2 ∧
    -- ghost data of k'_B: (0,0) at B, (0, μ_D) at C, (0, μ_C) at D
    kB' p 1 5 = 0 ∧ kB' p 2 6 = p.μD ∧ kB' p 3 4 = p.μC := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [kB, kB', KB, polar, h1', h2', h3', h1s', h2s', h3s', eps1, eps2, eps3, e1v, e2v,
      Params.μB, Params.μC, Params.μD, Params.d1, Params.d2, Params.d3] <;> ring

/-! Paper, "Accessibility": the 28 amplitudes are the printed products of `ĥ`'s applied to `1`
(each `ς` deletable). Frames `A` and `B` as printed; `C`, `D` by the cyclic relabelling. -/
set_option maxHeartbeats 4000000 in
theorem amp_A0 : amp p (wordFI 0 0) = one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_A1 : amp p (wordFI 0 1) = h1 p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_A2 : amp p (wordFI 0 2) = h2 p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_A3 : amp p (wordFI 0 3) = h3 p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_A4 : amp p (wordFI 0 4) = h1 p (h2 p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_A5 : amp p (wordFI 0 5) = h3s p (h2s p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_A6 : amp p (wordFI 0 6) = h1s p (h3s p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_B0 : amp p (wordFI 1 0) = one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_B1 : amp p (wordFI 1 1) = h1 p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_B2 : amp p (wordFI 1 2) = h3s p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_B3 : amp p (wordFI 1 3) = h2s p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_B4 : amp p (wordFI 1 4) = h1 p (h2 p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_B5 : amp p (wordFI 1 5) = h3s p (h2s p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_B6 : amp p (wordFI 1 6) = h1 p (h2 p (h3 p one8)) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_C0 : amp p (wordFI 2 0) = one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_C1 : amp p (wordFI 2 1) = h2 p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_C2 : amp p (wordFI 2 2) = h1s p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_C3 : amp p (wordFI 2 3) = h3s p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_C4 : amp p (wordFI 2 4) = h2 p (h3 p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_C5 : amp p (wordFI 2 5) = h1s p (h3s p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_C6 : amp p (wordFI 2 6) = h2 p (h3 p (h1 p one8)) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_D0 : amp p (wordFI 3 0) = one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_D1 : amp p (wordFI 3 1) = h3 p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_D2 : amp p (wordFI 3 2) = h2s p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_D3 : amp p (wordFI 3 3) = h1s p one8 := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_D4 : amp p (wordFI 3 4) = h3 p (h1 p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_D5 : amp p (wordFI 3 5) = h2s p (h1s p one8) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

set_option maxHeartbeats 4000000 in
theorem amp_D6 : amp p (wordFI 3 6) = h3 p (h1 p (h2 p one8)) := by
  funext i; fin_cases i <;>
    simp [wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3,
      one8] <;> ring

end LemmaB
