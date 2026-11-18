module

public import LemmaB.Model

/-!
# Lemma B, part 5: the twenty-eight words, their amplitudes, and accessibility (existence only)

Paper: eq:cer:W28 and the paragraph "Accessibility" of the proof of lem:cer:negative.
For each frame `f` the seven amplitudes of the words of
frame `f` span the subspace `S_A = {[β]_g = 0}`, `S_B = {[β]_{χ_2} = -ĉ_2 [β]_g}`,
`S_C = {[β]_{χ_3} = -ĉ_3 [β]_g}`, `S_D = {[β]_{χ_1} = -ĉ_1 [β]_g}`; this is shown by explicit
back-substitution along the triangular pivot structure (pivots `±1`), with the coefficients
defined from the amplitudes' own coordinates (no coefficient polynomial is transcribed).
Machine-generated.
-/

@[expose] public section

namespace LemmaB

variable {K : Type*} [Field K] (p : Params K)

/-- The twenty-eight words of eq:cer:W28, in chronological order (`A, B, C, D = 0, 1, 2, 3`),
indexed by frame (last letter) and position in the paper's row. -/
def wordFI : Fin 4 → Fin 7 → List (Fin 4) :=
  ![![[], [2, 1, 0], [3, 2, 0], [1, 3, 0], [3, 2, 1, 0], [2, 3, 1, 0], [3, 1, 2, 0]],
    ![[1], [2, 1], [3, 1], [2, 3, 0, 1], [3, 2, 1], [2, 3, 1], [1, 3, 2, 1]],
    ![[2], [3, 2], [1, 2], [3, 1, 0, 2], [1, 3, 2], [3, 1, 2], [2, 1, 3, 2]],
    ![[3], [1, 3], [2, 3], [1, 2, 0, 3], [2, 1, 3], [1, 2, 3], [3, 2, 1, 3]]]

theorem frameOf_wordFI (f : Fin 4) (i : Fin 7) : frameOf p (wordFI f i) = f := by
  fin_cases f <;> fin_cases i <;> rfl

/-- Back-substitution coefficients for frame A. -/
def coefA (β : C8 K) : Fin 7 → K :=
  let a := fun i => amp p (wordFI 0 i)
  let c4 := a 4 6 * (β 6)
  let c5 := a 5 4 * (β 4 - c4 * a 4 4)
  let c6 := a 6 5 * (β 5 - c4 * a 4 5 - c5 * a 5 5)
  let c1 := a 1 1 * (β 1 - c4 * a 4 1 - c5 * a 5 1 - c6 * a 6 1)
  let c2 := a 2 2 * (β 2 - c4 * a 4 2 - c5 * a 5 2 - c6 * a 6 2 - c1 * a 1 2)
  let c3 := a 3 3 * (β 3 - c4 * a 4 3 - c5 * a 5 3 - c6 * a 6 3 - c1 * a 1 3 - c2 * a 2 3)
  let c0 := a 0 0 * (β 0 - c4 * a 4 0 - c5 * a 5 0 - c6 * a 6 0 - c1 * a 1 0 - c2 * a 2 0 - c3 * a 3 0)
  ![c0, c1, c2, c3, c4, c5, c6]

set_option maxHeartbeats 4000000 in
/-- The seven frame-A amplitudes span the frame-A subspace. -/
theorem spanA (β : C8 K) (hβ : β 7 = 0) :
    ∑ j, coefA p β j • amp p (wordFI 0 j) = β := by
  have e4 : coefA p β 4 = amp p (wordFI 0 4) 6 * (β 6) := rfl
  have e5 : coefA p β 5 = amp p (wordFI 0 5) 4 * (β 4 - coefA p β 4 * amp p (wordFI 0 4) 4) := rfl
  have e6 : coefA p β 6 = amp p (wordFI 0 6) 5 * (β 5 - coefA p β 4 * amp p (wordFI 0 4) 5 - coefA p β 5 * amp p (wordFI 0 5) 5) := rfl
  have e1 : coefA p β 1 = amp p (wordFI 0 1) 1 * (β 1 - coefA p β 4 * amp p (wordFI 0 4) 1 - coefA p β 5 * amp p (wordFI 0 5) 1 - coefA p β 6 * amp p (wordFI 0 6) 1) := rfl
  have e2 : coefA p β 2 = amp p (wordFI 0 2) 2 * (β 2 - coefA p β 4 * amp p (wordFI 0 4) 2 - coefA p β 5 * amp p (wordFI 0 5) 2 - coefA p β 6 * amp p (wordFI 0 6) 2 - coefA p β 1 * amp p (wordFI 0 1) 2) := rfl
  have e3 : coefA p β 3 = amp p (wordFI 0 3) 3 * (β 3 - coefA p β 4 * amp p (wordFI 0 4) 3 - coefA p β 5 * amp p (wordFI 0 5) 3 - coefA p β 6 * amp p (wordFI 0 6) 3 - coefA p β 1 * amp p (wordFI 0 1) 3 - coefA p β 2 * amp p (wordFI 0 2) 3) := rfl
  have e0 : coefA p β 0 = amp p (wordFI 0 0) 0 * (β 0 - coefA p β 4 * amp p (wordFI 0 4) 0 - coefA p β 5 * amp p (wordFI 0 5) 0 - coefA p β 6 * amp p (wordFI 0 6) 0 - coefA p β 1 * amp p (wordFI 0 1) 0 - coefA p β 2 * amp p (wordFI 0 2) 0 - coefA p β 3 * amp p (wordFI 0 3) 0) := rfl
  generalize coefA p β = c at e0 e1 e2 e3 e4 e5 e6 ⊢
  simp [Fin.sum_univ_seven, wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] at e0 e1 e2 e3 e4 e5 e6
  funext i
  fin_cases i <;> simp [Fin.sum_univ_seven, wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;>
    first
      | linear_combination e0
      | linear_combination -e0
      | linear_combination e1
      | linear_combination -e1
      | linear_combination e2
      | linear_combination -e2
      | linear_combination e3
      | linear_combination -e3
      | linear_combination e4
      | linear_combination -e4
      | linear_combination e5
      | linear_combination -e5
      | linear_combination e6
      | linear_combination -e6
      | linear_combination hβ
      | linear_combination -hβ

/-- Back-substitution coefficients for frame B. -/
def coefB (β : C8 K) : Fin 7 → K :=
  let a := fun i => amp p (wordFI 1 i)
  let c6 := a 6 7 * (β 7)
  let c4 := a 4 6 * (β 6 - c6 * a 6 6)
  let c5 := a 5 4 * (β 4 - c6 * a 6 4 - c4 * a 4 4)
  let c2 := a 2 3 * (β 3 - c6 * a 6 3 - c4 * a 4 3 - c5 * a 5 3)
  let c3 := a 3 2 * (β 2 - c6 * a 6 2 - c4 * a 4 2 - c5 * a 5 2 - c2 * a 2 2)
  let c1 := a 1 1 * (β 1 - c6 * a 6 1 - c4 * a 4 1 - c5 * a 5 1 - c2 * a 2 1 - c3 * a 3 1)
  let c0 := a 0 0 * (β 0 - c6 * a 6 0 - c4 * a 4 0 - c5 * a 5 0 - c2 * a 2 0 - c3 * a 3 0 - c1 * a 1 0)
  ![c0, c1, c2, c3, c4, c5, c6]

set_option maxHeartbeats 4000000 in
/-- The seven frame-B amplitudes span the frame-B subspace. -/
theorem spanB (β : C8 K) (hβ : β 5 = -p.c2 * β 7) :
    ∑ j, coefB p β j • amp p (wordFI 1 j) = β := by
  have e6 : coefB p β 6 = amp p (wordFI 1 6) 7 * (β 7) := rfl
  have e4 : coefB p β 4 = amp p (wordFI 1 4) 6 * (β 6 - coefB p β 6 * amp p (wordFI 1 6) 6) := rfl
  have e5 : coefB p β 5 = amp p (wordFI 1 5) 4 * (β 4 - coefB p β 6 * amp p (wordFI 1 6) 4 - coefB p β 4 * amp p (wordFI 1 4) 4) := rfl
  have e2 : coefB p β 2 = amp p (wordFI 1 2) 3 * (β 3 - coefB p β 6 * amp p (wordFI 1 6) 3 - coefB p β 4 * amp p (wordFI 1 4) 3 - coefB p β 5 * amp p (wordFI 1 5) 3) := rfl
  have e3 : coefB p β 3 = amp p (wordFI 1 3) 2 * (β 2 - coefB p β 6 * amp p (wordFI 1 6) 2 - coefB p β 4 * amp p (wordFI 1 4) 2 - coefB p β 5 * amp p (wordFI 1 5) 2 - coefB p β 2 * amp p (wordFI 1 2) 2) := rfl
  have e1 : coefB p β 1 = amp p (wordFI 1 1) 1 * (β 1 - coefB p β 6 * amp p (wordFI 1 6) 1 - coefB p β 4 * amp p (wordFI 1 4) 1 - coefB p β 5 * amp p (wordFI 1 5) 1 - coefB p β 2 * amp p (wordFI 1 2) 1 - coefB p β 3 * amp p (wordFI 1 3) 1) := rfl
  have e0 : coefB p β 0 = amp p (wordFI 1 0) 0 * (β 0 - coefB p β 6 * amp p (wordFI 1 6) 0 - coefB p β 4 * amp p (wordFI 1 4) 0 - coefB p β 5 * amp p (wordFI 1 5) 0 - coefB p β 2 * amp p (wordFI 1 2) 0 - coefB p β 3 * amp p (wordFI 1 3) 0 - coefB p β 1 * amp p (wordFI 1 1) 0) := rfl
  generalize coefB p β = c at e0 e1 e2 e3 e4 e5 e6 ⊢
  simp [Fin.sum_univ_seven, wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] at e0 e1 e2 e3 e4 e5 e6
  funext i
  fin_cases i <;> simp [Fin.sum_univ_seven, wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;>
    first
      | linear_combination e0
      | linear_combination -e0
      | linear_combination e1
      | linear_combination -e1
      | linear_combination e2
      | linear_combination -e2
      | linear_combination e3
      | linear_combination -e3
      | linear_combination e4
      | linear_combination -e4
      | linear_combination e5
      | linear_combination -e5
      | linear_combination e6
      | linear_combination -e6
      | linear_combination -hβ - p.c2 * e6
      | linear_combination hβ + p.c2 * e6
      | linear_combination -hβ + p.c2 * e6
      | linear_combination hβ - p.c2 * e6

/-- Back-substitution coefficients for frame C. -/
def coefC (β : C8 K) : Fin 7 → K :=
  let a := fun i => amp p (wordFI 2 i)
  let c6 := a 6 7 * (β 7)
  let c4 := a 4 4 * (β 4 - c6 * a 6 4)
  let c5 := a 5 5 * (β 5 - c6 * a 6 5 - c4 * a 4 5)
  let c2 := a 2 1 * (β 1 - c6 * a 6 1 - c4 * a 4 1 - c5 * a 5 1)
  let c3 := a 3 3 * (β 3 - c6 * a 6 3 - c4 * a 4 3 - c5 * a 5 3 - c2 * a 2 3)
  let c1 := a 1 2 * (β 2 - c6 * a 6 2 - c4 * a 4 2 - c5 * a 5 2 - c2 * a 2 2 - c3 * a 3 2)
  let c0 := a 0 0 * (β 0 - c6 * a 6 0 - c4 * a 4 0 - c5 * a 5 0 - c2 * a 2 0 - c3 * a 3 0 - c1 * a 1 0)
  ![c0, c1, c2, c3, c4, c5, c6]

set_option maxHeartbeats 4000000 in
/-- The seven frame-C amplitudes span the frame-C subspace. -/
theorem spanC (β : C8 K) (hβ : β 6 = -p.c3 * β 7) :
    ∑ j, coefC p β j • amp p (wordFI 2 j) = β := by
  have e6 : coefC p β 6 = amp p (wordFI 2 6) 7 * (β 7) := rfl
  have e4 : coefC p β 4 = amp p (wordFI 2 4) 4 * (β 4 - coefC p β 6 * amp p (wordFI 2 6) 4) := rfl
  have e5 : coefC p β 5 = amp p (wordFI 2 5) 5 * (β 5 - coefC p β 6 * amp p (wordFI 2 6) 5 - coefC p β 4 * amp p (wordFI 2 4) 5) := rfl
  have e2 : coefC p β 2 = amp p (wordFI 2 2) 1 * (β 1 - coefC p β 6 * amp p (wordFI 2 6) 1 - coefC p β 4 * amp p (wordFI 2 4) 1 - coefC p β 5 * amp p (wordFI 2 5) 1) := rfl
  have e3 : coefC p β 3 = amp p (wordFI 2 3) 3 * (β 3 - coefC p β 6 * amp p (wordFI 2 6) 3 - coefC p β 4 * amp p (wordFI 2 4) 3 - coefC p β 5 * amp p (wordFI 2 5) 3 - coefC p β 2 * amp p (wordFI 2 2) 3) := rfl
  have e1 : coefC p β 1 = amp p (wordFI 2 1) 2 * (β 2 - coefC p β 6 * amp p (wordFI 2 6) 2 - coefC p β 4 * amp p (wordFI 2 4) 2 - coefC p β 5 * amp p (wordFI 2 5) 2 - coefC p β 2 * amp p (wordFI 2 2) 2 - coefC p β 3 * amp p (wordFI 2 3) 2) := rfl
  have e0 : coefC p β 0 = amp p (wordFI 2 0) 0 * (β 0 - coefC p β 6 * amp p (wordFI 2 6) 0 - coefC p β 4 * amp p (wordFI 2 4) 0 - coefC p β 5 * amp p (wordFI 2 5) 0 - coefC p β 2 * amp p (wordFI 2 2) 0 - coefC p β 3 * amp p (wordFI 2 3) 0 - coefC p β 1 * amp p (wordFI 2 1) 0) := rfl
  generalize coefC p β = c at e0 e1 e2 e3 e4 e5 e6 ⊢
  simp [Fin.sum_univ_seven, wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] at e0 e1 e2 e3 e4 e5 e6
  funext i
  fin_cases i <;> simp [Fin.sum_univ_seven, wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;>
    first
      | linear_combination e0
      | linear_combination -e0
      | linear_combination e1
      | linear_combination -e1
      | linear_combination e2
      | linear_combination -e2
      | linear_combination e3
      | linear_combination -e3
      | linear_combination e4
      | linear_combination -e4
      | linear_combination e5
      | linear_combination -e5
      | linear_combination e6
      | linear_combination -e6
      | linear_combination -hβ - p.c3 * e6
      | linear_combination hβ + p.c3 * e6
      | linear_combination -hβ + p.c3 * e6
      | linear_combination hβ - p.c3 * e6

/-- Back-substitution coefficients for frame D. -/
def coefD (β : C8 K) : Fin 7 → K :=
  let a := fun i => amp p (wordFI 3 i)
  let c6 := a 6 7 * (β 7)
  let c4 := a 4 5 * (β 5 - c6 * a 6 5)
  let c5 := a 5 6 * (β 6 - c6 * a 6 6 - c4 * a 4 6)
  let c2 := a 2 2 * (β 2 - c6 * a 6 2 - c4 * a 4 2 - c5 * a 5 2)
  let c3 := a 3 1 * (β 1 - c6 * a 6 1 - c4 * a 4 1 - c5 * a 5 1 - c2 * a 2 1)
  let c1 := a 1 3 * (β 3 - c6 * a 6 3 - c4 * a 4 3 - c5 * a 5 3 - c2 * a 2 3 - c3 * a 3 3)
  let c0 := a 0 0 * (β 0 - c6 * a 6 0 - c4 * a 4 0 - c5 * a 5 0 - c2 * a 2 0 - c3 * a 3 0 - c1 * a 1 0)
  ![c0, c1, c2, c3, c4, c5, c6]

set_option maxHeartbeats 4000000 in
/-- The seven frame-D amplitudes span the frame-D subspace. -/
theorem spanD (β : C8 K) (hβ : β 4 = -p.c1 * β 7) :
    ∑ j, coefD p β j • amp p (wordFI 3 j) = β := by
  have e6 : coefD p β 6 = amp p (wordFI 3 6) 7 * (β 7) := rfl
  have e4 : coefD p β 4 = amp p (wordFI 3 4) 5 * (β 5 - coefD p β 6 * amp p (wordFI 3 6) 5) := rfl
  have e5 : coefD p β 5 = amp p (wordFI 3 5) 6 * (β 6 - coefD p β 6 * amp p (wordFI 3 6) 6 - coefD p β 4 * amp p (wordFI 3 4) 6) := rfl
  have e2 : coefD p β 2 = amp p (wordFI 3 2) 2 * (β 2 - coefD p β 6 * amp p (wordFI 3 6) 2 - coefD p β 4 * amp p (wordFI 3 4) 2 - coefD p β 5 * amp p (wordFI 3 5) 2) := rfl
  have e3 : coefD p β 3 = amp p (wordFI 3 3) 1 * (β 1 - coefD p β 6 * amp p (wordFI 3 6) 1 - coefD p β 4 * amp p (wordFI 3 4) 1 - coefD p β 5 * amp p (wordFI 3 5) 1 - coefD p β 2 * amp p (wordFI 3 2) 1) := rfl
  have e1 : coefD p β 1 = amp p (wordFI 3 1) 3 * (β 3 - coefD p β 6 * amp p (wordFI 3 6) 3 - coefD p β 4 * amp p (wordFI 3 4) 3 - coefD p β 5 * amp p (wordFI 3 5) 3 - coefD p β 2 * amp p (wordFI 3 2) 3 - coefD p β 3 * amp p (wordFI 3 3) 3) := rfl
  have e0 : coefD p β 0 = amp p (wordFI 3 0) 0 * (β 0 - coefD p β 6 * amp p (wordFI 3 6) 0 - coefD p β 4 * amp p (wordFI 3 4) 0 - coefD p β 5 * amp p (wordFI 3 5) 0 - coefD p β 2 * amp p (wordFI 3 2) 0 - coefD p β 3 * amp p (wordFI 3 3) 0 - coefD p β 1 * amp p (wordFI 3 1) 0) := rfl
  generalize coefD p β = c at e0 e1 e2 e3 e4 e5 e6 ⊢
  simp [Fin.sum_univ_seven, wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] at e0 e1 e2 e3 e4 e5 e6
  funext i
  fin_cases i <;> simp [Fin.sum_univ_seven, wordFI, amp, ampAux, List.foldl, T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8] <;>
    first
      | linear_combination e0
      | linear_combination -e0
      | linear_combination e1
      | linear_combination -e1
      | linear_combination e2
      | linear_combination -e2
      | linear_combination e3
      | linear_combination -e3
      | linear_combination e4
      | linear_combination -e4
      | linear_combination e5
      | linear_combination -e5
      | linear_combination e6
      | linear_combination -e6
      | linear_combination -hβ - p.c1 * e6
      | linear_combination hβ + p.c1 * e6
      | linear_combination -hβ + p.c1 * e6
      | linear_combination hβ - p.c1 * e6

end LemmaB
