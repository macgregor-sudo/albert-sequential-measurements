module

public import Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

/-!
# Diagonal Peirce Anchor for `AlbertSequential.Albert`

Clean-room formalization of the canonical diagonal Jordan frame `diagAtom i`
(`i : Fin 3`) and its Peirce-1 quadratic projection `U_{E_{ii}} x = x_{ii} E_{ii}`
on the compact real Albert algebra `AlbertSequential.Albert`.

## Mathematical & Paper Sources
- Core paper, Lemma `lem:A:slots(b)`:
  `U_{E_{kk}} x = ξ_k E_{kk}`.
- Core paper, equation `eq:set:pure`:
  `U_p x = ⟨p, x⟩ p` for a primitive idempotent `p`.
- J. Faraut and A. Korányi, *Analysis on Symmetric Cones* (1994),
  Props. II.3.3, III.2.2, and IV.1.1 (quadratic representation, Peirce
  decomposition, and pure projections).
- T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and
  Exceptional Groups* (2000), §5.3 (Hermitian `3 × 3` matrices over a
  composition algebra and canonical diagonal idempotents).
- P. Jordan, J. von Neumann, and E. Wigner, *Ann. of Math.* **35** (1934),
  29–64 (Jordan frames in `H_3(𝕆)`).

## Proof Strategy
Every proof remains at the `Octonion` (`Quaternion ℝ × Quaternion ℝ`) and
`Fin 3 × Fin 3` matrix level using Kronecker-delta collapse of
`albertMatrix (diagAtom i)` and `Module ℝ Octonion` cancellation
`2 • ((1/2) • (1/2) • z) - (1/2) • z = 0`, with zero quaternion-component
expansion and zero inherited `One`/`Mul`/`Star`/`Norm` instances on
`Octonion` or `Albert`.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential

private theorem octonion_zero_fst : (0 : Octonion).1 = 0 := rfl
private theorem octonion_zero_snd : (0 : Octonion).2 = 0 := rfl

private theorem octonionScalar_zero : octonionScalar 0 = 0 := by
  apply Prod.ext
  · apply Quaternion.ext <;> rfl
  · exact octonion_zero_snd.symm

private theorem octonionConj_zero : octonionConj 0 = 0 := by
  apply Prod.ext
  · change star (0 : Octonion).1 = (0 : Octonion).1
    rw [octonion_zero_fst, star_zero]
  · change -(0 : Octonion).2 = (0 : Octonion).2
    rw [octonion_zero_snd, neg_zero]

private theorem octonionMul_zero_left (z : Octonion) : octonionMul 0 z = 0 := by
  apply Prod.ext
  · change (0 : Octonion).1 * z.1 - star z.2 * (0 : Octonion).2 = (0 : Octonion).1
    rw [octonion_zero_fst, octonion_zero_snd, zero_mul, mul_zero, sub_zero]
  · change z.2 * (0 : Octonion).1 + (0 : Octonion).2 * star z.1 = (0 : Octonion).2
    rw [octonion_zero_fst, octonion_zero_snd, mul_zero, zero_mul, add_zero]

private theorem octonionMul_zero_right (z : Octonion) : octonionMul z 0 = 0 := by
  apply Prod.ext
  · change z.1 * (0 : Octonion).1 - star (0 : Octonion).2 * z.2 = (0 : Octonion).1
    rw [octonion_zero_fst, octonion_zero_snd, mul_zero, star_zero, zero_mul, sub_zero]
  · change (0 : Octonion).2 * z.1 + z.2 * star (0 : Octonion).1 = (0 : Octonion).2
    rw [octonion_zero_fst, octonion_zero_snd, zero_mul, star_zero, mul_zero, add_zero]

private theorem octonionScalar_one_fst : (octonionScalar 1).1 = (1 : Quaternion ℝ) := by
  apply Quaternion.ext <;> rfl

private theorem octonionScalar_one_snd : (octonionScalar 1).2 = (0 : Quaternion ℝ) := rfl

private theorem octonionMul_scalar_one_left (z : Octonion) :
    octonionMul (octonionScalar 1) z = z := by
  apply Prod.ext
  · change (octonionScalar 1).1 * z.1 - star z.2 * (octonionScalar 1).2 = z.1
    rw [octonionScalar_one_fst, octonionScalar_one_snd, one_mul, mul_zero, sub_zero]
  · change z.2 * (octonionScalar 1).1 + (octonionScalar 1).2 * star z.1 = z.2
    rw [octonionScalar_one_fst, octonionScalar_one_snd, mul_one, zero_mul, add_zero]

private theorem octonionMul_scalar_one_right (z : Octonion) :
    octonionMul z (octonionScalar 1) = z := by
  apply Prod.ext
  · change z.1 * (octonionScalar 1).1 - star (octonionScalar 1).2 * z.2 = z.1
    rw [octonionScalar_one_fst, octonionScalar_one_snd, mul_one, star_zero, zero_mul, sub_zero]
  · change (octonionScalar 1).2 * z.1 + z.2 * star (octonionScalar 1).1 = z.2
    rw [octonionScalar_one_fst, octonionScalar_one_snd, zero_mul, star_one, mul_one, zero_add]

private theorem octonionReal_zero : octonionReal 0 = 0 := rfl

private theorem octonionReal_albertMatrix_diag (x : Albert) (i : Fin 3) :
    octonionReal (albertMatrix x i i) = x.1 i := by
  fin_cases i <;> rfl

private theorem albert_zero_fst (j : Fin 3) : (0 : Albert).1 j = 0 := rfl
private theorem albert_zero_snd (k : Fin 3) : (0 : Albert).2 k = 0 := rfl
private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_sub_fst (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
private theorem albert_sub_snd (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

/-- Canonical diagonal primitive idempotent `E_{ii}` (`i : Fin 3`) in `Albert`. -/
def diagAtom (i : Fin 3) : Albert :=
  (fun j => if j = i then 1 else 0, fun _ => 0)

private theorem albertMatrix_diagAtom (i r s : Fin 3) :
    albertMatrix (diagAtom i) r s =
      if r = i ∧ s = i then octonionScalar 1 else 0 := by
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    simp [albertMatrix, diagAtom, octonionScalar_zero, octonionConj_zero]

private theorem octonionMatrixMul_diagAtom_left (i : Fin 3)
    (M : Fin 3 → Fin 3 → Octonion) (r s : Fin 3) :
    octonionMatrixMul (albertMatrix (diagAtom i)) M r s =
      if r = i then M i s else 0 := by
  unfold octonionMatrixMul
  simp only [albertMatrix_diagAtom]
  by_cases hr : r = i
  · rcases hr with rfl
    simp only [↓reduceIte, true_and]
    rw [Finset.sum_eq_single r]
    · simp [octonionMul_scalar_one_left]
    · intro k _ hkr
      simp [hkr, octonionMul_zero_left]
    · intro hr_mem
      exact absurd (Finset.mem_univ r) hr_mem
  · simp [hr, octonionMul_zero_left]

private theorem octonionMatrixMul_diagAtom_right (i : Fin 3)
    (M : Fin 3 → Fin 3 → Octonion) (r s : Fin 3) :
    octonionMatrixMul M (albertMatrix (diagAtom i)) r s =
      if s = i then M r i else 0 := by
  unfold octonionMatrixMul
  simp only [albertMatrix_diagAtom]
  by_cases hs : s = i
  · rcases hs with rfl
    simp only [↓reduceIte, and_true]
    rw [Finset.sum_eq_single s]
    · simp [octonionMul_scalar_one_right]
    · intro k _ hks
      simp [hks, octonionMul_zero_right]
    · intro hs_mem
      exact absurd (Finset.mem_univ s) hs_mem
  · simp [hs, octonionMul_zero_right]

private theorem jordanMul_diagAtom_diag (i j : Fin 3) (x : Albert) :
    (jordanMul (diagAtom i) x).1 j = if j = i then x.1 i else 0 := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) * octonionReal
      (octonionMatrixMul (albertMatrix (diagAtom i)) (albertMatrix x) j j +
        octonionMatrixMul (albertMatrix x) (albertMatrix (diagAtom i)) j j) =
    if j = i then x.1 i else 0
  rw [octonionMatrixMul_diagAtom_left, octonionMatrixMul_diagAtom_right]
  by_cases hj : j = i
  · rcases hj with rfl
    simp only [↓reduceIte]
    change (1 / 2 : ℝ) * (octonionReal (albertMatrix x j j) +
      octonionReal (albertMatrix x j j)) = x.1 j
    rw [octonionReal_albertMatrix_diag]
    ring
  · simp [hj, octonionReal_zero]

private theorem jordanMul_diagAtom_offDiag (i k : Fin 3) (x : Albert) :
    (jordanMul (diagAtom i) x).2 k =
      if i.val + k.val = 2 then 0 else (1 / 2 : ℝ) • x.2 k := by
  unfold jordanMul albertCoordinates
  change (1 / 2 : ℝ) •
      ![octonionMatrixMul (albertMatrix (diagAtom i)) (albertMatrix x) 0 1 +
          octonionMatrixMul (albertMatrix x) (albertMatrix (diagAtom i)) 0 1,
        octonionMatrixMul (albertMatrix (diagAtom i)) (albertMatrix x) 0 2 +
          octonionMatrixMul (albertMatrix x) (albertMatrix (diagAtom i)) 0 2,
        octonionMatrixMul (albertMatrix (diagAtom i)) (albertMatrix x) 1 2 +
          octonionMatrixMul (albertMatrix x) (albertMatrix (diagAtom i)) 1 2] k =
    if i.val + k.val = 2 then 0 else (1 / 2 : ℝ) • x.2 k
  fin_cases i <;> fin_cases k <;>
    simp [octonionMatrixMul_diagAtom_left, octonionMatrixMul_diagAtom_right,
      albertMatrix]

/-- Each canonical diagonal unit `diagAtom i` is an atom (trace-one idempotent). -/
theorem diagAtom_isAtom (i : Fin 3) : IsAtom (diagAtom i) := by
  constructor
  · apply Prod.ext <;> funext j
    · rw [jordanMul_diagAtom_diag]
      simp [diagAtom]
    · rw [jordanMul_diagAtom_offDiag]
      simp [diagAtom]
  · fin_cases i <;> simp [albertTrace, diagAtom]

/-- Distinct canonical diagonal atoms are Jordan-orthogonal. -/
theorem diagAtom_orthogonal {i j : Fin 3} (hij : i ≠ j) :
    jordanMul (diagAtom i) (diagAtom j) = 0 := by
  apply Prod.ext <;> funext k
  · rw [jordanMul_diagAtom_diag, albert_zero_fst]
    simp [diagAtom, hij]
  · rw [jordanMul_diagAtom_offDiag, albert_zero_snd]
    simp [diagAtom]

/-- The three canonical diagonal atoms sum to `albertUnit`. -/
theorem diagAtom_sum_eq_unit :
    ∑ i : Fin 3, diagAtom i = albertUnit := by
  apply Prod.ext <;> funext j
  · rw [Fin.sum_univ_three]
    simp only [albert_add_fst]
    fin_cases j <;> simp [diagAtom, albertUnit]
  · rw [Fin.sum_univ_three]
    simp only [albert_add_snd]
    simp [diagAtom, albertUnit]

/-- Peirce-1 quadratic projection: `U_{E_{ii}}(x) = x_{ii} E_{ii}`. -/
theorem quadraticMap_diagAtom (i : Fin 3) (x : Albert) :
    quadraticMap (diagAtom i) x = (x.1 i) • diagAtom i := by
  unfold quadraticMap
  rw [(diagAtom_isAtom i).1, two_smul]
  apply Prod.ext <;> funext k
  · simp only [albert_sub_fst, albert_add_fst, albert_smul_fst, jordanMul_diagAtom_diag]
    by_cases hk : k = i
    · rcases hk with rfl
      simp [diagAtom]
    · simp [hk, diagAtom]
  · simp only [albert_sub_snd, albert_add_snd, albert_smul_snd, jordanMul_diagAtom_offDiag]
    by_cases hk : i.val + k.val = 2
    · simp [hk, diagAtom]
    · simp only [hk, ↓reduceIte, diagAtom, smul_zero]
      module

/-- Trace pairing with a canonical diagonal atom extracts the `i`-th diagonal entry. -/
theorem tracePairing_diagAtom (i : Fin 3) (x : Albert) :
    tracePairing (diagAtom i) x = x.1 i := by
  unfold tracePairing albertTrace
  simp only [jordanMul_diagAtom_diag]
  fin_cases i <;> simp

end AlbertSequential
