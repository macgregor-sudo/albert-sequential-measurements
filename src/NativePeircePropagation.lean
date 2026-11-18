module

public import Defs
public import DiagPeirceAnchor
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Native Peirce Propagation for `AlbertSequential.Albert`

Clean-room formalization of the two canonical real off-diagonal connectors
`realConnector01` and `realConnector02`, their Peirce-`1/2` relations with
`diagAtom 0`, their Jordan squares, the native left-unit law
`jordanMul albertUnit x = x`, and the conditional zero-homomorphism corollary
`jordanHom_eq_zero_of_diagAtom0`.

## Mathematical & Paper Sources
- Core paper, Lemma `lem:A:slots(b)` (incident
  off-diagonal slot action `E_{11} ∘ F_k(a) = (1/2) F_k(a)`).
- Core paper, `thm:tet:albert`
  (final propagation step from `η(E_{11}) = 0` to `η = 0`, without claiming the
  fixed-`S` tetrahedron identities or discriminant).
- P. Jordan, J. von Neumann, and E. Wigner, *Ann. of Math.* **35** (1934),
  29–64 (Peirce `1/2` propagation in `H_3(𝕆)`).
- T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and
  Exceptional Groups* (2000), §5.3 (matrix unit products in `H_3(C)`).

## Slot Bindings
- `realConnector01 := upperSlot 0 (octonionScalar 1)` places `1` in matrix
  positions `(0,1)` and `(1,0)`, matching paper `F_3(1)`.
- `realConnector02 := upperSlot 1 (octonionScalar 1)` places `1` in matrix
  positions `(0,2)` and `(2,0)`, matching paper `F_2(1)` because
  `octonionConj (octonionScalar 1) = octonionScalar 1`.

## Proof Scope
All native matrix identities use only binary `octonionMul` unit and zero laws
with `octonionScalar 1` and `0` (no octonion associativity or quaternion
coordinate expansion). `jordanHom_eq_zero_of_diagAtom0` requires only
`[NonUnitalRing A] [Module ℝ A]`, with no `IsScalarTower`, `SMulCommClass`,
unitality, star, order, or nontriviality assumptions.
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

private theorem octonionConj_scalar_one :
    octonionConj (octonionScalar 1) = octonionScalar 1 := by
  apply Prod.ext
  · apply Quaternion.ext <;> simp [octonionConj, octonionScalar]
  · change -(0 : Quaternion ℝ) = 0
    simp

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

private theorem octonionScalar_one_fst :
    (octonionScalar 1).1 = (1 : Quaternion ℝ) := by
  apply Quaternion.ext <;> rfl

private theorem octonionScalar_one_snd :
    (octonionScalar 1).2 = (0 : Quaternion ℝ) := rfl

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
private theorem octonionReal_scalar_one : octonionReal (octonionScalar 1) = 1 := rfl
private theorem octonionReal_add (x y : Octonion) :
    octonionReal (x + y) = octonionReal x + octonionReal y := rfl

private theorem albert_add_fst (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
private theorem albert_add_snd (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
private theorem albert_smul_fst (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

private theorem albertCoordinates_fst (m : Fin 3 → Fin 3 → Octonion) (i : Fin 3) :
    (albertCoordinates m).1 i = octonionReal (m i i) := rfl

private theorem albertCoordinates_snd (m : Fin 3 → Fin 3 → Octonion) :
    (albertCoordinates m).2 = ![m 0 1, m 0 2, m 1 2] := rfl

private theorem octonionReal_albertMatrix_diag (x : Albert) (i : Fin 3) :
    octonionReal (albertMatrix x i i) = x.1 i := by
  fin_cases i <;> rfl

/-- Off-diagonal upper-slot embedding in `Albert` (`0 ↦ (0,1)`, `1 ↦ (0,2)`, `2 ↦ (1,2)`). -/
def upperSlot (k : Fin 3) (a : Octonion) : Albert :=
  (fun _ => 0, fun j => if j = k then a else 0)

/-- Canonical real `(0,1)+(1,0)` connector (paper `F_3(1)`). -/
def realConnector01 : Albert := upperSlot 0 (octonionScalar 1)

/-- Canonical real `(0,2)+(2,0)` connector (paper `F_2(1)`). -/
def realConnector02 : Albert := upperSlot 1 (octonionScalar 1)

/-- Nonzero-coordinate control for `diagAtom 0`. -/
theorem diagAtom0_coord_one : (diagAtom 0).1 0 = 1 := rfl

/-- Nonzero-coordinate control for `realConnector01`. -/
theorem realConnector01_coord_one : (realConnector01.2 0).1.re = 1 := rfl

/-- Nonzero-coordinate control for `realConnector02`. -/
theorem realConnector02_coord_one : (realConnector02.2 1).1.re = 1 := rfl

private theorem albertMatrix_diagAtom0 (r s : Fin 3) :
    albertMatrix (diagAtom 0) r s =
      if r = 0 ∧ s = 0 then octonionScalar 1 else 0 := by
  fin_cases r <;> fin_cases s <;>
    simp [albertMatrix, diagAtom, octonionScalar_zero, octonionConj_zero]

private theorem albertMatrix_realConnector01 (r s : Fin 3) :
    albertMatrix realConnector01 r s =
      if (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) then octonionScalar 1 else 0 := by
  fin_cases r <;> fin_cases s <;>
    simp [albertMatrix, realConnector01, upperSlot, octonionScalar_zero,
      octonionConj_zero, octonionConj_scalar_one]

private theorem albertMatrix_realConnector02 (r s : Fin 3) :
    albertMatrix realConnector02 r s =
      if (r = 0 ∧ s = 2) ∨ (r = 2 ∧ s = 0) then octonionScalar 1 else 0 := by
  fin_cases r <;> fin_cases s <;>
    simp [albertMatrix, realConnector02, upperSlot, octonionScalar_zero,
      octonionConj_zero, octonionConj_scalar_one]

private theorem albertMatrix_albertUnit (r s : Fin 3) :
    albertMatrix albertUnit r s = if r = s then octonionScalar 1 else 0 := by
  fin_cases r <;> fin_cases s <;>
    simp [albertMatrix, albertUnit, octonionConj_zero]

/-- `diagAtom 0` acts on `realConnector01` with eigenvalue `1 / 2`. -/
theorem jordanMul_diagAtom0_realConnector01 :
    jordanMul (diagAtom 0) realConnector01 =
      (1 / 2 : ℝ) • realConnector01 := by
  unfold jordanMul
  apply Prod.ext <;> funext idx
  · rw [albert_smul_fst, albert_smul_fst, albertCoordinates_fst]
    simp only [Pi.add_apply, octonionMatrixMul, Fin.sum_univ_three,
      albertMatrix_diagAtom0, albertMatrix_realConnector01]
    fin_cases idx <;>
      simp [octonionMul_zero_left, octonionMul_zero_right, octonionReal_zero,
        realConnector01, upperSlot]
  · rw [albert_smul_snd, albert_smul_snd, albertCoordinates_snd]
    simp only [Pi.add_apply, octonionMatrixMul, Fin.sum_univ_three,
      albertMatrix_diagAtom0, albertMatrix_realConnector01]
    fin_cases idx <;>
      simp [octonionMul_zero_right, octonionMul_scalar_one_left, realConnector01, upperSlot]

/-- `diagAtom 0` acts on `realConnector02` with eigenvalue `1 / 2`. -/
theorem jordanMul_diagAtom0_realConnector02 :
    jordanMul (diagAtom 0) realConnector02 =
      (1 / 2 : ℝ) • realConnector02 := by
  unfold jordanMul
  apply Prod.ext <;> funext idx
  · rw [albert_smul_fst, albert_smul_fst, albertCoordinates_fst]
    simp only [Pi.add_apply, octonionMatrixMul, Fin.sum_univ_three,
      albertMatrix_diagAtom0, albertMatrix_realConnector02]
    fin_cases idx <;>
      simp [octonionMul_zero_left, octonionMul_zero_right, octonionReal_zero,
        realConnector02, upperSlot]
  · rw [albert_smul_snd, albert_smul_snd, albertCoordinates_snd]
    simp only [Pi.add_apply, octonionMatrixMul, Fin.sum_univ_three,
      albertMatrix_diagAtom0, albertMatrix_realConnector02]
    fin_cases idx <;>
      simp [octonionMul_zero_left, octonionMul_zero_right,
        octonionMul_scalar_one_left, realConnector02, upperSlot]

/-- Jordan square of `realConnector01` is `diagAtom 0 + diagAtom 1`. -/
theorem jordanMul_realConnector01_self :
    jordanMul realConnector01 realConnector01 = diagAtom 0 + diagAtom 1 := by
  unfold jordanMul
  apply Prod.ext <;> funext idx
  · rw [albert_smul_fst, albert_add_fst, albertCoordinates_fst]
    simp only [Pi.add_apply, octonionMatrixMul, Fin.sum_univ_three,
      albertMatrix_realConnector01]
    fin_cases idx <;>
      simp [octonionMul_zero_right, octonionMul_scalar_one_left,
        octonionReal_add, octonionReal_zero, octonionReal_scalar_one, diagAtom] <;>
      norm_num
  · rw [albert_smul_snd, albert_add_snd, albertCoordinates_snd]
    simp only [Pi.add_apply, octonionMatrixMul, Fin.sum_univ_three,
      albertMatrix_realConnector01]
    fin_cases idx <;>
      simp [octonionMul_zero_left, octonionMul_zero_right, diagAtom]

/-- Jordan square of `realConnector02` is `diagAtom 0 + diagAtom 2`. -/
theorem jordanMul_realConnector02_self :
    jordanMul realConnector02 realConnector02 = diagAtom 0 + diagAtom 2 := by
  unfold jordanMul
  apply Prod.ext <;> funext idx
  · rw [albert_smul_fst, albert_add_fst, albertCoordinates_fst]
    simp only [Pi.add_apply, octonionMatrixMul, Fin.sum_univ_three,
      albertMatrix_realConnector02]
    fin_cases idx <;>
      simp [octonionMul_zero_right, octonionMul_scalar_one_left,
        octonionReal_add, octonionReal_zero, octonionReal_scalar_one, diagAtom] <;>
      norm_num
  · rw [albert_smul_snd, albert_add_snd, albertCoordinates_snd]
    simp only [Pi.add_apply, octonionMatrixMul, Fin.sum_univ_three,
      albertMatrix_realConnector02]
    fin_cases idx <;>
      simp [octonionMul_zero_left, octonionMul_zero_right, diagAtom]

private theorem octonionMatrixMul_albertUnit_left
    (M : Fin 3 → Fin 3 → Octonion) (r s : Fin 3) :
    octonionMatrixMul (albertMatrix albertUnit) M r s = M r s := by
  unfold octonionMatrixMul
  simp only [albertMatrix_albertUnit]
  rw [Finset.sum_eq_single r]
  · simp [octonionMul_scalar_one_left]
  · intro k _ hkr
    simp [Ne.symm hkr, octonionMul_zero_left]
  · intro hr_mem
    exact absurd (Finset.mem_univ r) hr_mem

private theorem octonionMatrixMul_albertUnit_right
    (M : Fin 3 → Fin 3 → Octonion) (r s : Fin 3) :
    octonionMatrixMul M (albertMatrix albertUnit) r s = M r s := by
  unfold octonionMatrixMul
  simp only [albertMatrix_albertUnit]
  rw [Finset.sum_eq_single s]
  · simp [octonionMul_scalar_one_right]
  · intro k _ hks
    simp [hks, octonionMul_zero_right]
  · intro hs_mem
    exact absurd (Finset.mem_univ s) hs_mem

/-- The native identity `albertUnit` is a left unit for `jordanMul`. -/
theorem jordanMul_albertUnit_left (x : Albert) :
    jordanMul albertUnit x = x := by
  unfold jordanMul albertCoordinates
  apply Prod.ext <;> funext i
  · change (1 / 2 : ℝ) * octonionReal
        (octonionMatrixMul (albertMatrix albertUnit) (albertMatrix x) i i +
          octonionMatrixMul (albertMatrix x) (albertMatrix albertUnit) i i) = x.1 i
    rw [octonionMatrixMul_albertUnit_left, octonionMatrixMul_albertUnit_right,
      octonionReal_add, octonionReal_albertMatrix_diag]
    ring
  · change (1 / 2 : ℝ) •
        ![octonionMatrixMul (albertMatrix albertUnit) (albertMatrix x) 0 1 +
            octonionMatrixMul (albertMatrix x) (albertMatrix albertUnit) 0 1,
          octonionMatrixMul (albertMatrix albertUnit) (albertMatrix x) 0 2 +
            octonionMatrixMul (albertMatrix x) (albertMatrix albertUnit) 0 2,
          octonionMatrixMul (albertMatrix albertUnit) (albertMatrix x) 1 2 +
            octonionMatrixMul (albertMatrix x) (albertMatrix albertUnit) 1 2] i = x.2 i
    simp only [octonionMatrixMul_albertUnit_left, octonionMatrixMul_albertUnit_right]
    fin_cases i <;> simp [albertMatrix] <;> module

private theorem half_smul_eq_zero {A : Type*} [AddCommGroup A] [Module ℝ A]
    {a : A} (h : (1 / 2 : ℝ) • a = 0) : a = 0 := by
  calc
    a = (1 : ℝ) • a := (one_smul ℝ a).symm
    _ = ((2 : ℝ) * (1 / 2 : ℝ)) • a := by norm_num
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • a) := mul_smul 2 (1 / 2) a
    _ = 0 := by rw [h, smul_zero]

private theorem map_diag_eq_zero_of_connector
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η)
    (h0 : η (diagAtom 0) = 0) {c d : Albert}
    (hc_half : jordanMul (diagAtom 0) c = (1 / 2 : ℝ) • c)
    (hc_sq : jordanMul c c = diagAtom 0 + d) :
    η d = 0 := by
  have hc_smul : (1 / 2 : ℝ) • η c = 0 := by
    calc
      (1 / 2 : ℝ) • η c = η ((1 / 2 : ℝ) • c) := (η.map_smul _ _).symm
      _ = η (jordanMul (diagAtom 0) c) := by rw [hc_half]
      _ = (1 / 2 : ℝ) • (η (diagAtom 0) * η c + η c * η (diagAtom 0)) := hη _ _
      _ = 0 := by rw [h0, zero_mul, mul_zero, add_zero, smul_zero]
  have hc : η c = 0 := half_smul_eq_zero hc_smul
  have hsum : η (diagAtom 0) + η d = 0 := by
    calc
      η (diagAtom 0) + η d = η (diagAtom 0 + d) := (η.map_add _ _).symm
      _ = η (jordanMul c c) := by rw [hc_sq]
      _ = (1 / 2 : ℝ) • (η c * η c + η c * η c) := hη _ _
      _ = 0 := by rw [hc, zero_mul, add_zero, smul_zero]
  rwa [h0, zero_add] at hsum

/-- Any real-linear Jordan homomorphism into a nonunital real-module ring
vanishing on `diagAtom 0` is identically zero. -/
theorem jordanHom_eq_zero_of_diagAtom0
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η)
    (h0 : η (diagAtom 0) = 0) : η = 0 := by
  have hdiag1 : η (diagAtom 1) = 0 :=
    map_diag_eq_zero_of_connector η hη h0
      jordanMul_diagAtom0_realConnector01 jordanMul_realConnector01_self
  have hdiag2 : η (diagAtom 2) = 0 :=
    map_diag_eq_zero_of_connector η hη h0
      jordanMul_diagAtom0_realConnector02 jordanMul_realConnector02_self
  have hunit : η albertUnit = 0 := by
    rw [← diagAtom_sum_eq_unit, Fin.sum_univ_three, map_add, map_add,
      h0, hdiag1, hdiag2, add_zero, add_zero]
  ext x
  calc
    η x = η (jordanMul albertUnit x) := by rw [jordanMul_albertUnit_left]
    _ = (1 / 2 : ℝ) • (η albertUnit * η x + η x * η albertUnit) := hη _ _
    _ = 0 := by rw [hunit, zero_mul, mul_zero, add_zero, smul_zero]

end AlbertSequential
