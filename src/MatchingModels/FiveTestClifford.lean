/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PentadArityAndHelly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Five-Test Peirce-Clifford Graded Agreement (`cor:five:minimum` lower-bound core)

Formalizes the quaternionic comparison pair `pentadFPlus` and `pentadFMinus` obtained from
`pentadF` by replacing `octL` in `pentadF 4` with `+octK` and `-octK` (where `octK = octonionMul octI octJ`),
proves that all members are atoms inside `standardQuaternionicWindow.subalgebra.carrier`, and proves
all-word equality with the average of `pentadFPlus` and `pentadFMinus` through length `9` from `pentadF 0`
and through length `10` from `(1 / 3 : ℝ) • albertUnit`, together with the explicit separating words
at length `10` (from `p₀`, defects `± 1 / 1296`) and length `11` (from `e / 3`, defects `± 1 / 3888`).

The agreement proof avoids word enumeration by verifying by `decide +kernel` on a pure integer
Cayley-Dickson Jordan mirror `IntMirror.{ZQ, ZO, ZA}` a 27-element graded Peirce-Clifford basis closing
under all five Jordan multiplications `L_{p_r}` (`r : Fin 5`) with `M₀(r) + c M₁(r)` (`c ∈ {0, +1, -1}`),
where `M₀` raises weight by at most `1` and `M₁` only jumps from weight `5` to weight `0`, followed by
a two-type reset-interval induction over chronological words.
-/

set_option autoImplicit false

@[expose] public section

namespace AlbertSequential.MatchingModels

/-! ## Section 1: Pure-Integer Cayley-Dickson Jordan Mirror `IntMirror.{ZQ, ZO, ZA}` -/

namespace IntMirror

structure ZQ where
  re : ℤ
  i : ℤ
  j : ℤ
  k : ℤ
deriving DecidableEq

namespace ZQ
def zero : ZQ := ⟨0, 0, 0, 0⟩
def add (a b : ZQ) : ZQ := ⟨a.re + b.re, a.i + b.i, a.j + b.j, a.k + b.k⟩
def neg (a : ZQ) : ZQ := ⟨-a.re, -a.i, -a.j, -a.k⟩
def smul (r : ℤ) (a : ZQ) : ZQ := ⟨r * a.re, r * a.i, r * a.j, r * a.k⟩
def star (a : ZQ) : ZQ := ⟨a.re, -a.i, -a.j, -a.k⟩
def mul (a b : ZQ) : ZQ :=
  ⟨a.re * b.re - a.i * b.i - a.j * b.j - a.k * b.k,
   a.re * b.i + a.i * b.re + a.j * b.k - a.k * b.j,
   a.re * b.j - a.i * b.k + a.j * b.re + a.k * b.i,
   a.re * b.k + a.i * b.j - a.j * b.i + a.k * b.re⟩
end ZQ

structure ZO where
  fst : ZQ
  snd : ZQ
deriving DecidableEq

namespace ZO
def zero : ZO := ⟨ZQ.zero, ZQ.zero⟩
def add (x y : ZO) : ZO := ⟨x.fst.add y.fst, x.snd.add y.snd⟩
def neg (x : ZO) : ZO := ⟨x.fst.neg, x.snd.neg⟩
def sub (x y : ZO) : ZO := x.add y.neg
def smul (r : ℤ) (x : ZO) : ZO := ⟨x.fst.smul r, x.snd.smul r⟩
def mul (x y : ZO) : ZO :=
  ⟨(x.fst.mul y.fst).add (((y.snd.star).mul x.snd).neg),
   (y.snd.mul x.fst).add (x.snd.mul y.fst.star)⟩
def conj (x : ZO) : ZO := ⟨x.fst.star, x.snd.neg⟩
def scalar (r : ℤ) : ZO := ⟨⟨r, 0, 0, 0⟩, ZQ.zero⟩
def real (x : ZO) : ℤ := x.fst.re
def normSq (x : ZO) : ℤ := (x.mul x.conj).real
def one : ZO := scalar 1
def I : ZO := ⟨⟨0, 1, 0, 0⟩, ZQ.zero⟩
def J : ZO := ⟨⟨0, 0, 1, 0⟩, ZQ.zero⟩
def K : ZO := ⟨⟨0, 0, 0, 1⟩, ZQ.zero⟩
def L : ZO := ⟨ZQ.zero, ⟨1, 0, 0, 0⟩⟩
end ZO

structure ZA where
  d0 : ℤ
  d1 : ℤ
  d2 : ℤ
  o0 : ZO
  o1 : ZO
  o2 : ZO
deriving DecidableEq

namespace ZA
def zero : ZA := ⟨0, 0, 0, ZO.zero, ZO.zero, ZO.zero⟩
def add (x y : ZA) : ZA :=
  ⟨x.d0 + y.d0, x.d1 + y.d1, x.d2 + y.d2, x.o0.add y.o0, x.o1.add y.o1, x.o2.add y.o2⟩
def smul (r : ℤ) (x : ZA) : ZA :=
  ⟨r * x.d0, r * x.d1, r * x.d2, x.o0.smul r, x.o1.smul r, x.o2.smul r⟩
def sub (x y : ZA) : ZA := x.add (y.smul (-1))
def unit : ZA := ⟨1, 1, 1, ZO.zero, ZO.zero, ZO.zero⟩
def diag0 : ZA := ⟨1, 0, 0, ZO.zero, ZO.zero, ZO.zero⟩

def mat (x : ZA) (i j : Fin 3) : ZO :=
  match i.val, j.val with
  | 0, 0 => ZO.scalar x.d0
  | 1, 1 => ZO.scalar x.d1
  | 2, 2 => ZO.scalar x.d2
  | 0, 1 => x.o0
  | 0, 2 => x.o1
  | 1, 2 => x.o2
  | 1, 0 => x.o0.conj
  | 2, 0 => x.o1.conj
  | 2, 1 => x.o2.conj
  | _, _ => ZO.zero

def mmul (a b : Fin 3 → Fin 3 → ZO) (i j : Fin 3) : ZO :=
  ((a i 0).mul (b 0 j)).add (((a i 1).mul (b 1 j)).add (((a i 2).mul (b 2 j)).add ZO.zero))

def coords (m : Fin 3 → Fin 3 → ZO) : ZA :=
  ⟨(m 0 0).real, (m 1 1).real, (m 2 2).real, m 0 1, m 0 2, m 1 2⟩

/-- Twice the Jordan product, computed purely over `ℤ`. -/
def jmul2 (x y : ZA) : ZA :=
  coords (fun i j => (mmul (mat x) (mat y) i j).add (mmul (mat y) (mat x) i j))

def tr (x : ZA) : ℤ := x.d0 + x.d1 + x.d2

/-- Twice the trace pairing, computed purely over `ℤ`. -/
def tp2 (x y : ZA) : ℤ := tr (jmul2 x y)

/-- Four times the quadratic operator `U_x(y)`, computed purely over `ℤ`. -/
def U4 (x y : ZA) : ZA := ((x.jmul2 (x.jmul2 y)).smul 2).sub ((x.jmul2 x).jmul2 y)

def dyad (v0 v1 v2 : ZO) : ZA :=
  ⟨v0.normSq, v1.normSq, v2.normSq, v0.mul v1.conj, v0.mul v2.conj, v1.mul v2.conj⟩
end ZA

noncomputable section

def castZQ (a : ZQ) : Quaternion ℝ := ⟨(a.re : ℝ), (a.i : ℝ), (a.j : ℝ), (a.k : ℝ)⟩
def castZO (x : ZO) : Octonion := (castZQ x.fst, castZQ x.snd)
def castZA (x : ZA) : Albert :=
  (![(x.d0 : ℝ), (x.d1 : ℝ), (x.d2 : ℝ)], ![castZO x.o0, castZO x.o1, castZO x.o2])

theorem castZQ_zero : castZQ ZQ.zero = 0 := by
  apply Quaternion.ext <;> simp [castZQ, ZQ.zero]
theorem castZQ_add (a b : ZQ) : castZQ (a.add b) = castZQ a + castZQ b := by
  apply Quaternion.ext <;> simp [castZQ, ZQ.add]
theorem castZQ_neg (a : ZQ) : castZQ a.neg = -castZQ a := by
  apply Quaternion.ext <;> simp [castZQ, ZQ.neg]
theorem castZQ_smul (r : ℤ) (a : ZQ) : castZQ (a.smul r) = (r : ℝ) • castZQ a := by
  apply Quaternion.ext <;> simp [castZQ, ZQ.smul]
theorem castZQ_star (a : ZQ) : castZQ a.star = star (castZQ a) := by
  apply Quaternion.ext <;> simp [castZQ, ZQ.star]
theorem castZQ_mul (a b : ZQ) : castZQ (a.mul b) = castZQ a * castZQ b := by
  apply Quaternion.ext <;> simp [castZQ, ZQ.mul] <;> ring

theorem castZO_zero : castZO ZO.zero = 0 := by
  simp only [castZO, ZO.zero, castZQ_zero]; rfl
theorem castZO_add (x y : ZO) : castZO (x.add y) = castZO x + castZO y := by
  simp only [castZO, ZO.add, castZQ_add]; rfl
theorem castZO_neg (x : ZO) : castZO x.neg = -castZO x := by
  simp only [castZO, ZO.neg, castZQ_neg]; rfl
theorem castZO_smul (r : ℤ) (x : ZO) : castZO (x.smul r) = (r : ℝ) • castZO x := by
  simp only [castZO, ZO.smul, castZQ_smul]; rfl
theorem castZO_mul (x y : ZO) : castZO (x.mul y) = octonionMul (castZO x) (castZO y) := by
  simp only [castZO, ZO.mul, castZQ_add, castZQ_neg, castZQ_mul, castZQ_star, octonionMul]
  rw [sub_eq_add_neg]
theorem castZO_conj (x : ZO) : castZO x.conj = octonionConj (castZO x) := by
  simp only [castZO, ZO.conj, castZQ_star, castZQ_neg, octonionConj]; rfl
theorem castZO_scalar (r : ℤ) : castZO (ZO.scalar r) = octonionScalar (r : ℝ) := by
  simp only [castZO, ZO.scalar, castZQ_zero, octonionScalar]
  congr 1; apply Quaternion.ext <;> simp [castZQ]
theorem castZO_real (x : ZO) : ((x.real : ℤ) : ℝ) = octonionReal (castZO x) := by
  simp [ZO.real, octonionReal, castZO, castZQ]
theorem castZO_normSq (x : ZO) : ((x.normSq : ℤ) : ℝ) = octNormSq (castZO x) := by
  rw [ZO.normSq, castZO_real, castZO_mul, castZO_conj]; rfl
theorem castZO_one : castZO ZO.one = octOne := by
  rw [ZO.one, castZO_scalar]; simp [octOne]
theorem castZO_I : castZO ZO.I = octI := by
  simp only [castZO, ZO.I, castZQ_zero, octI]; congr 1; apply Quaternion.ext <;> simp [castZQ]
theorem castZO_J : castZO ZO.J = octJ := by
  simp only [castZO, ZO.J, castZQ_zero, octJ]; congr 1; apply Quaternion.ext <;> simp [castZQ]
theorem castZO_K : castZO ZO.K = octK := by
  simp only [castZO, ZO.K, castZQ_zero, octK]; congr 1; apply Quaternion.ext <;> simp [castZQ]
theorem castZO_L : castZO ZO.L = octL := by
  simp only [castZO, ZO.L, castZQ_zero, octL]; congr 1; apply Quaternion.ext <;> simp [castZQ]

@[simp] theorem castZA_d0 (x : ZA) : (castZA x).1 0 = (x.d0 : ℝ) := rfl
@[simp] theorem castZA_d1 (x : ZA) : (castZA x).1 1 = (x.d1 : ℝ) := rfl
@[simp] theorem castZA_d2 (x : ZA) : (castZA x).1 2 = (x.d2 : ℝ) := rfl
@[simp] theorem castZA_o0 (x : ZA) : (castZA x).2 0 = castZO x.o0 := rfl
@[simp] theorem castZA_o1 (x : ZA) : (castZA x).2 1 = castZO x.o1 := rfl
@[simp] theorem castZA_o2 (x : ZA) : (castZA x).2 2 = castZO x.o2 := rfl

private theorem albert_smul_fst' (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
private theorem albert_smul_snd' (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl

private theorem albert_ext' {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

theorem castZA_zero : castZA ZA.zero = 0 := by
  apply albert_ext' <;> simp [castZA, ZA.zero, castZO_zero] <;> rfl
theorem castZA_add (x y : ZA) : castZA (x.add y) = castZA x + castZA y := by
  apply albert_ext' <;> simp [castZA, ZA.add, castZO_add] <;> rfl
theorem castZA_smul (r : ℤ) (x : ZA) : castZA (x.smul r) = (r : ℝ) • castZA x := by
  apply albert_ext' <;> simp [castZA, ZA.smul, castZO_smul] <;> rfl
theorem castZA_sub (x y : ZA) : castZA (x.sub y) = castZA x - castZA y := by
  rw [ZA.sub, castZA_add, castZA_smul, sub_eq_add_neg]; simp
theorem castZA_unit : castZA ZA.unit = albertUnit := by
  apply albert_ext' <;> simp [castZA, ZA.unit, castZO_zero] <;> rfl
theorem castZA_diag0 : castZA ZA.diag0 = diagAtom 0 := by
  apply albert_ext' <;> simp [castZA, ZA.diag0, castZO_zero, diagAtom]

theorem castZA_mat (x : ZA) (i j : Fin 3) : castZO (x.mat i j) = albertMatrix (castZA x) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [ZA.mat, albertMatrix, castZO_scalar, castZO_conj, castZA]

theorem castZA_mmul (a b : Fin 3 → Fin 3 → ZO) (i j : Fin 3) :
    castZO (ZA.mmul a b i j) =
      octonionMatrixMul (fun i j => castZO (a i j)) (fun i j => castZO (b i j)) i j := by
  simp only [ZA.mmul, castZO_add, castZO_mul, castZO_zero, octonionMatrixMul, Fin.sum_univ_three,
    add_zero, add_assoc]

private theorem jordanMul_fst' (X Y : Albert) (i : Fin 3) : (jordanMul X Y).1 i =
    (1 / 2 : ℝ) * octonionReal (octonionMatrixMul (albertMatrix X) (albertMatrix Y) i i +
      octonionMatrixMul (albertMatrix Y) (albertMatrix X) i i) := rfl
private theorem jordanMul_snd0' (X Y : Albert) : (jordanMul X Y).2 0 =
    (1 / 2 : ℝ) • (octonionMatrixMul (albertMatrix X) (albertMatrix Y) 0 1 +
      octonionMatrixMul (albertMatrix Y) (albertMatrix X) 0 1) := rfl
private theorem jordanMul_snd1' (X Y : Albert) : (jordanMul X Y).2 1 =
    (1 / 2 : ℝ) • (octonionMatrixMul (albertMatrix X) (albertMatrix Y) 0 2 +
      octonionMatrixMul (albertMatrix Y) (albertMatrix X) 0 2) := rfl
private theorem jordanMul_snd2' (X Y : Albert) : (jordanMul X Y).2 2 =
    (1 / 2 : ℝ) • (octonionMatrixMul (albertMatrix X) (albertMatrix Y) 1 2 +
      octonionMatrixMul (albertMatrix Y) (albertMatrix X) 1 2) := rfl

theorem castZA_jmul2 (x y : ZA) :
    castZA (x.jmul2 y) = (2 : ℝ) • jordanMul (castZA x) (castZA y) := by
  have hm : ∀ (u v : ZA) (i j : Fin 3), castZO (ZA.mmul u.mat v.mat i j) =
      octonionMatrixMul (albertMatrix (castZA u)) (albertMatrix (castZA v)) i j := by
    intro u v i j
    rw [castZA_mmul]
    have e : (fun i j => castZO (u.mat i j)) = albertMatrix (castZA u) := by
      funext i j; exact castZA_mat u i j
    have e' : (fun i j => castZO (v.mat i j)) = albertMatrix (castZA v) := by
      funext i j; exact castZA_mat v i j
    rw [e, e']
  apply albert_ext' <;>
    simp only [castZA_d0, castZA_d1, castZA_d2, castZA_o0, castZA_o1, castZA_o2,
      ZA.jmul2, ZA.coords, castZO_real, castZO_add, hm,
      albert_smul_fst', albert_smul_snd',
      jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2']
  · ring
  · ring
  · ring
  · rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul]
  · rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul]
  · rw [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul]

theorem castZA_tr (x : ZA) : ((x.tr : ℤ) : ℝ) = albertTrace (castZA x) := by
  simp [ZA.tr, albertTrace, Fin.sum_univ_three, castZA]

theorem castZA_tp2 (x y : ZA) :
    ((x.tp2 y : ℤ) : ℝ) = (2 : ℝ) * tracePairing (castZA x) (castZA y) := by
  rw [ZA.tp2, castZA_tr, castZA_jmul2, albertTrace_smul]; rfl

theorem castZA_U4 (x y : ZA) :
    castZA (x.U4 y) = (4 : ℝ) • quadraticMap (castZA x) (castZA y) := by
  rw [ZA.U4, castZA_sub, castZA_smul, castZA_jmul2, castZA_jmul2, castZA_jmul2, castZA_jmul2]
  rw [jordanMul_smul_right, jordanMul_smul_left, smul_smul, smul_smul, smul_smul]
  norm_num only
  rw [quadraticMap, two_nsmul, smul_sub, smul_add, ← add_smul]
  norm_num only

theorem castZA_dyad (v0 v1 v2 : ZO) :
    castZA (ZA.dyad v0 v1 v2) = octDyad ![castZO v0, castZO v1, castZO v2] := by
  apply albert_ext' <;>
    simp [castZA, ZA.dyad, octDyad, castZO_normSq, castZO_mul, castZO_conj]

end

end IntMirror

open IntMirror

/-! ## Section 2: Quaternionic Comparator Pentads `pentadFPlus` and `pentadFMinus` -/

def atomScale : Fin 5 → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 2

def qPentadScaled (u : ZO) : Fin 5 → ZA
  | 0 => ZA.diag0
  | 1 => ZA.dyad ZO.one ZO.one ZO.zero
  | 2 => ZA.dyad ZO.one ZO.I ZO.one
  | 3 => ZA.dyad ZO.one ZO.J ZO.zero
  | 4 => ZA.dyad ZO.one u ZO.zero

def qPentadZ6 (u : ZO) : Fin 5 → ZA
  | 0 => ZA.diag0.smul 6
  | 1 => (ZA.dyad ZO.one ZO.one ZO.zero).smul 3
  | 2 => (ZA.dyad ZO.one ZO.I ZO.one).smul 2
  | 3 => (ZA.dyad ZO.one ZO.J ZO.zero).smul 3
  | 4 => (ZA.dyad ZO.one u ZO.zero).smul 3

def zCompl (u : ZO) (r : Fin 5) : ZA :=
  (ZA.unit.smul (atomScale r)).sub (qPentadScaled u r)

private theorem qPentadZ6_K_atom :
    ∀ i : Fin 5, (qPentadZ6 ZO.K i).jmul2 (qPentadZ6 ZO.K i) = (qPentadZ6 ZO.K i).smul 12 ∧
      (qPentadZ6 ZO.K i).tr = 6 := by
  decide +kernel

private theorem qPentadZ6_mK_atom :
    ∀ i : Fin 5,
      (qPentadZ6 ZO.K.neg i).jmul2 (qPentadZ6 ZO.K.neg i) = (qPentadZ6 ZO.K.neg i).smul 12 ∧
      (qPentadZ6 ZO.K.neg i).tr = 6 := by
  decide +kernel

private theorem qPentadScaled_K_quat :
    ∀ i : Fin 5, (qPentadScaled ZO.K i).o0.snd = ZQ.zero ∧
      (qPentadScaled ZO.K i).o1.snd = ZQ.zero ∧ (qPentadScaled ZO.K i).o2.snd = ZQ.zero := by
  decide +kernel

private theorem qPentadScaled_mK_quat :
    ∀ i : Fin 5, (qPentadScaled ZO.K.neg i).o0.snd = ZQ.zero ∧
      (qPentadScaled ZO.K.neg i).o1.snd = ZQ.zero ∧
      (qPentadScaled ZO.K.neg i).o2.snd = ZQ.zero := by
  decide +kernel

noncomputable section

/-- Quaternionic comparator pentad obtained by replacing `octL` in `pentadF 4` with `+octK` (`+octI * octJ`). -/
def pentadFPlus : Fin 5 → Albert
  | 0 => diagAtom 0
  | 1 => (1 / 2 : ℝ) • octDyad ![octOne, octOne, 0]
  | 2 => (1 / 3 : ℝ) • octDyad ![octOne, octI, octOne]
  | 3 => (1 / 2 : ℝ) • octDyad ![octOne, octJ, 0]
  | 4 => (1 / 2 : ℝ) • octDyad ![octOne, octK, 0]

/-- Quaternionic comparator pentad obtained by replacing `octL` in `pentadF 4` with `-octK` (`-(octI * octJ)`). -/
def pentadFMinus : Fin 5 → Albert
  | 0 => diagAtom 0
  | 1 => (1 / 2 : ℝ) • octDyad ![octOne, octOne, 0]
  | 2 => (1 / 3 : ℝ) • octDyad ![octOne, octI, octOne]
  | 3 => (1 / 2 : ℝ) • octDyad ![octOne, octJ, 0]
  | 4 => (1 / 2 : ℝ) • octDyad ![octOne, -octK, 0]

theorem pentadFPlus_eq_pentadF_of_ne_four {i : Fin 5} (hi : i ≠ 4) :
    pentadFPlus i = pentadF i := by
  fin_cases i <;> first | rfl | exact absurd rfl hi

theorem pentadFMinus_eq_pentadF_of_ne_four {i : Fin 5} (hi : i ≠ 4) :
    pentadFMinus i = pentadF i := by
  fin_cases i <;> first | rfl | exact absurd rfl hi

theorem pentadFPlus_four_eq_ij :
    pentadFPlus 4 = (1 / 2 : ℝ) • octDyad ![octOne, octonionMul octI octJ, 0] := by
  rw [pentadFPlus, octK_eq_mul]

theorem pentadFMinus_four_eq_neg_ij :
    pentadFMinus 4 = (1 / 2 : ℝ) • octDyad ![octOne, -octonionMul octI octJ, 0] := by
  rw [pentadFMinus, octK_eq_mul]

theorem pentadF_eq_castScaled (i : Fin 5) :
    castZA (qPentadScaled ZO.L i) = (atomScale i : ℝ) • pentadF i := by
  fin_cases i
  · simp [qPentadScaled, atomScale, pentadF, castZA_diag0]
  · change castZA (ZA.dyad ZO.one ZO.one ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, octOne, 0])
    rw [castZA_dyad, castZO_one, castZO_zero, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.I ZO.one) =
      ((3 : ℤ) : ℝ) • ((1 / 3 : ℝ) • octDyad ![octOne, octI, octOne])
    rw [castZA_dyad, castZO_one, castZO_I, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.J ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, octJ, 0])
    rw [castZA_dyad, castZO_one, castZO_J, castZO_zero, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.L ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, octL, 0])
    rw [castZA_dyad, castZO_one, castZO_L, castZO_zero, smul_smul]; norm_num

theorem pentadFPlus_eq_castScaled (i : Fin 5) :
    castZA (qPentadScaled ZO.K i) = (atomScale i : ℝ) • pentadFPlus i := by
  fin_cases i
  · simp [qPentadScaled, atomScale, pentadFPlus, castZA_diag0]
  · change castZA (ZA.dyad ZO.one ZO.one ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, octOne, 0])
    rw [castZA_dyad, castZO_one, castZO_zero, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.I ZO.one) =
      ((3 : ℤ) : ℝ) • ((1 / 3 : ℝ) • octDyad ![octOne, octI, octOne])
    rw [castZA_dyad, castZO_one, castZO_I, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.J ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, octJ, 0])
    rw [castZA_dyad, castZO_one, castZO_J, castZO_zero, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.K ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, octK, 0])
    rw [castZA_dyad, castZO_one, castZO_K, castZO_zero, smul_smul]; norm_num

theorem pentadFMinus_eq_castScaled (i : Fin 5) :
    castZA (qPentadScaled ZO.K.neg i) = (atomScale i : ℝ) • pentadFMinus i := by
  fin_cases i
  · simp [qPentadScaled, atomScale, pentadFMinus, castZA_diag0]
  · change castZA (ZA.dyad ZO.one ZO.one ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, octOne, 0])
    rw [castZA_dyad, castZO_one, castZO_zero, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.I ZO.one) =
      ((3 : ℤ) : ℝ) • ((1 / 3 : ℝ) • octDyad ![octOne, octI, octOne])
    rw [castZA_dyad, castZO_one, castZO_I, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.J ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, octJ, 0])
    rw [castZA_dyad, castZO_one, castZO_J, castZO_zero, smul_smul]; norm_num
  · change castZA (ZA.dyad ZO.one ZO.K.neg ZO.zero) =
      ((2 : ℤ) : ℝ) • ((1 / 2 : ℝ) • octDyad ![octOne, -octK, 0])
    rw [castZA_dyad, castZO_one, castZO_neg, castZO_K, castZO_zero, smul_smul]; norm_num

private theorem castZA_qPentadZ6 (u : ZO) (F : Fin 5 → Albert)
    (hF : ∀ i, castZA (qPentadScaled u i) = (atomScale i : ℝ) • F i) (i : Fin 5) :
    castZA (qPentadZ6 u i) = (6 : ℝ) • F i := by
  have hi := hF i
  fin_cases i <;>
    simp only [qPentadZ6, castZA_smul] <;>
    simp only [qPentadScaled, atomScale] at hi <;>
    rw [hi, smul_smul] <;>
    norm_num

theorem pentadF_eq_castZ6 (i : Fin 5) : castZA (qPentadZ6 ZO.L i) = (6 : ℝ) • pentadF i :=
  castZA_qPentadZ6 ZO.L pentadF pentadF_eq_castScaled i

theorem pentadFPlus_eq_castZ6 (i : Fin 5) :
    castZA (qPentadZ6 ZO.K i) = (6 : ℝ) • pentadFPlus i :=
  castZA_qPentadZ6 ZO.K pentadFPlus pentadFPlus_eq_castScaled i

theorem pentadFMinus_eq_castZ6 (i : Fin 5) :
    castZA (qPentadZ6 ZO.K.neg i) = (6 : ℝ) • pentadFMinus i :=
  castZA_qPentadZ6 ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled i

private theorem isAtom_of_z6 {x : Albert} {zx : ZA} (hx : castZA zx = (6 : ℝ) • x)
    (hcheck : zx.jmul2 zx = zx.smul 12 ∧ zx.tr = 6) : IsAtom x := by
  have hj : jordanMul x x = x := by
    have h1 : castZA (zx.jmul2 zx) = (72 : ℝ) • jordanMul x x := by
      rw [castZA_jmul2, hx, jordanMul_smul_left, jordanMul_smul_right, smul_smul, smul_smul]
      norm_num
    have h2 : castZA (zx.smul 12) = (72 : ℝ) • x := by
      rw [castZA_smul, hx, smul_smul]; norm_num
    rw [hcheck.1, h2] at h1
    exact smul_right_injective Albert (by norm_num) h1.symm
  have ht : albertTrace x = 1 := by
    have h1 : (6 : ℝ) = albertTrace (castZA zx) := by
      rw [← castZA_tr, hcheck.2]; norm_num
    rw [hx, albertTrace_smul] at h1
    linarith
  exact ⟨hj, ht⟩

theorem pentadFPlus_isAtom (i : Fin 5) : IsAtom (pentadFPlus i) :=
  isAtom_of_z6 (pentadFPlus_eq_castZ6 i) (qPentadZ6_K_atom i)

theorem pentadFMinus_isAtom (i : Fin 5) : IsAtom (pentadFMinus i) :=
  isAtom_of_z6 (pentadFMinus_eq_castZ6 i) (qPentadZ6_mK_atom i)

private theorem mem_quat_of_scaled {x : Albert} {zx : ZA} {s : ℤ} (hs : (s : ℝ) ≠ 0)
    (hx : castZA zx = (s : ℝ) • x)
    (hquat : zx.o0.snd = ZQ.zero ∧ zx.o1.snd = ZQ.zero ∧ zx.o2.snd = ZQ.zero) :
    x ∈ standardQuaternionicWindow.subalgebra.carrier := by
  rw [mem_standardQuaternionicWindow_iff]
  have hz0 : (s : ℝ) • (x.2 0).2 = 0 := by
    change (((s : ℝ) • x).2 0).2 = 0
    rw [← hx]; simp [castZA, castZO, hquat.1, castZQ_zero]
  have hz1 : (s : ℝ) • (x.2 1).2 = 0 := by
    change (((s : ℝ) • x).2 1).2 = 0
    rw [← hx]; simp [castZA, castZO, hquat.2.1, castZQ_zero]
  have hz2 : (s : ℝ) • (x.2 2).2 = 0 := by
    change (((s : ℝ) • x).2 2).2 = 0
    rw [← hx]; simp [castZA, castZO, hquat.2.2, castZQ_zero]
  exact ⟨(smul_eq_zero.mp hz0).resolve_left hs,
    (smul_eq_zero.mp hz1).resolve_left hs,
    (smul_eq_zero.mp hz2).resolve_left hs⟩

theorem pentadFPlus_mem_standardQuaternionicWindow (i : Fin 5) :
    pentadFPlus i ∈ standardQuaternionicWindow.subalgebra.carrier := by
  have hs : ((atomScale i : ℤ) : ℝ) ≠ 0 := by fin_cases i <;> simp [atomScale]
  exact mem_quat_of_scaled hs (pentadFPlus_eq_castScaled i) (qPentadScaled_K_quat i)

theorem pentadFMinus_mem_standardQuaternionicWindow (i : Fin 5) :
    pentadFMinus i ∈ standardQuaternionicWindow.subalgebra.carrier := by
  have hs : ((atomScale i : ℤ) : ℝ) ≠ 0 := by fin_cases i <;> simp [atomScale]
  exact mem_quat_of_scaled hs (pentadFMinus_eq_castScaled i) (qPentadScaled_mK_quat i)

end

/-! ## Section 3: 27-Element Graded Peirce-Clifford Basis (`ℤ`-Verified via `decide +kernel`) -/

def basisLit_L (k : Fin 27) : ZA :=
  match k.val with
  | 0 => ⟨1, 1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 1 => ⟨0, 0, 1, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 2 => ⟨0, 0, 0, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 3 => ⟨1, -1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 4 => ⟨0, 0, 0, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 5 => ⟨0, 0, 0, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 6 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 7 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 8 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 9 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 10 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 11 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩⟩
  | 12 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 13 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 14 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩⟩
  | 15 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 16 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩⟩⟩
  | 17 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩⟩
  | 18 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 19 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩⟩⟩
  | 20 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩⟩⟩
  | 21 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩⟩⟩
  | 22 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩⟩⟩
  | 23 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 24 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 25 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 26 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | _ => ZA.zero

def basisLit_K (k : Fin 27) : ZA :=
  match k.val with
  | 0 => ⟨1, 1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 1 => ⟨0, 0, 1, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 2 => ⟨0, 0, 0, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 3 => ⟨1, -1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 4 => ⟨0, 0, 0, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 5 => ⟨0, 0, 0, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 6 => ⟨0, 0, 0, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 7 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 8 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 9 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 10 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 11 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 12 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 13 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 14 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 15 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 16 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 17 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 18 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 19 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 20 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 21 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 22 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 23 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 24 => ⟨0, 0, 0, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 25 => ⟨0, 0, 0, ⟨⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 26 => ⟨1, -1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | _ => ZA.zero

def basisLit_mK (k : Fin 27) : ZA :=
  match k.val with
  | 0 => ⟨1, 1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 1 => ⟨0, 0, 1, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 2 => ⟨0, 0, 0, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 3 => ⟨1, -1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 4 => ⟨0, 0, 0, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 5 => ⟨0, 0, 0, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 6 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 7 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 8 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 9 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 10 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 11 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 12 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 13 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 14 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 15 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 16 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 17 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 18 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 19 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 20 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 21 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 22 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 23 => ⟨0, 0, 0, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 24 => ⟨0, 0, 0, ⟨⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 25 => ⟨0, 0, 0, ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | 26 => ⟨-1, 1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
  | _ => ZA.zero

def basisWeight : Fin 27 → ℕ :=
  ![0, 0, 0,
    1, 1, 1, 1, 1,
    2, 2, 2, 2,
    3, 3, 3, 3, 3, 3,
    4, 4, 4, 4,
    5, 5, 5, 5, 5]

def trVecZ : Fin 27 → ℤ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | _ => 0

def m0RowZ12 (r : Fin 5) (k : Fin 27) : List (Fin 27 × ℤ) :=
  match r.val, k.val with
  | 0, 0 => [(0, 6), (3, 6)]
  | 0, 2 => [(2, 6)]
  | 0, 3 => [(0, 6), (3, 6)]
  | 0, 4 => [(4, 6)]
  | 0, 5 => [(5, 6)]
  | 0, 6 => [(6, 6)]
  | 0, 7 => [(7, 3), (8, 3)]
  | 0, 8 => [(7, 3), (8, 3)]
  | 0, 9 => [(9, 3), (12, 3)]
  | 0, 10 => [(10, 3), (13, 3)]
  | 0, 11 => [(11, 3), (14, 3)]
  | 0, 12 => [(9, 3), (12, 3)]
  | 0, 13 => [(10, 3), (13, 3)]
  | 0, 14 => [(11, 3), (14, 3)]
  | 0, 15 => [(15, 3), (18, 3)]
  | 0, 16 => [(16, 3), (19, 3)]
  | 0, 17 => [(17, 3), (20, 3)]
  | 0, 18 => [(15, 3), (18, 3)]
  | 0, 19 => [(16, 3), (19, 3)]
  | 0, 20 => [(17, 3), (20, 3)]
  | 0, 21 => [(21, 3), (22, 3)]
  | 0, 22 => [(21, 3), (22, 3)]
  | 0, 23 => [(23, 6)]
  | 0, 24 => [(24, 6)]
  | 0, 25 => [(25, 6)]
  | 0, 26 => [(26, 6)]
  | 1, 0 => [(0, 6), (4, 6)]
  | 1, 2 => [(2, 6)]
  | 1, 3 => [(3, 6)]
  | 1, 4 => [(0, 6), (4, 6)]
  | 1, 5 => [(5, 6)]
  | 1, 6 => [(6, 6)]
  | 1, 7 => [(7, 3), (9, 3)]
  | 1, 8 => [(8, 3), (12, -3)]
  | 1, 9 => [(7, 3), (9, 3)]
  | 1, 10 => [(10, 3), (15, 3)]
  | 1, 11 => [(11, 3), (16, 3)]
  | 1, 12 => [(8, -3), (12, 3)]
  | 1, 13 => [(13, 3), (18, -3)]
  | 1, 14 => [(14, 3), (19, -3)]
  | 1, 15 => [(10, 3), (15, 3)]
  | 1, 16 => [(11, 3), (16, 3)]
  | 1, 17 => [(17, 3), (21, 3)]
  | 1, 18 => [(13, -3), (18, 3)]
  | 1, 19 => [(14, -3), (19, 3)]
  | 1, 20 => [(20, 3), (22, -3)]
  | 1, 21 => [(17, 3), (21, 3)]
  | 1, 22 => [(20, -3), (22, 3)]
  | 1, 23 => [(23, 6)]
  | 1, 24 => [(24, 6)]
  | 1, 25 => [(25, 6)]
  | 1, 26 => [(26, 6)]
  | 2, 0 => [(0, 4), (2, 4), (7, 2)]
  | 2, 1 => [(1, 4), (7, 2)]
  | 2, 2 => [(0, 4), (2, 4), (7, 2)]
  | 2, 3 => [(3, 4), (8, 2)]
  | 2, 4 => [(4, 4), (9, 2)]
  | 2, 5 => [(5, 4), (10, 2)]
  | 2, 6 => [(6, 4), (11, 2)]
  | 2, 7 => [(0, 4), (1, 8), (2, 4), (7, 6)]
  | 2, 8 => [(3, 4), (8, 2)]
  | 2, 9 => [(4, 4), (9, 2)]
  | 2, 10 => [(5, 4), (10, 2)]
  | 2, 11 => [(6, 4), (11, 2)]
  | 2, 12 => [(12, 6)]
  | 2, 13 => [(13, 6)]
  | 2, 14 => [(14, 6)]
  | 2, 15 => [(15, 6)]
  | 2, 16 => [(16, 6)]
  | 2, 17 => [(17, 6)]
  | 2, 18 => [(18, 2), (23, 4)]
  | 2, 19 => [(19, 2), (24, 4)]
  | 2, 20 => [(20, 2), (25, 4)]
  | 2, 21 => [(21, 2), (26, 4)]
  | 2, 22 => [(22, 6)]
  | 2, 23 => [(18, 2), (23, 4)]
  | 2, 24 => [(19, 2), (24, 4)]
  | 2, 25 => [(20, 2), (25, 4)]
  | 2, 26 => [(21, 2), (26, 4)]
  | 3, 0 => [(0, 6), (5, 6)]
  | 3, 2 => [(2, 6)]
  | 3, 3 => [(3, 6)]
  | 3, 4 => [(4, 6)]
  | 3, 5 => [(0, 6), (5, 6)]
  | 3, 6 => [(6, 6)]
  | 3, 7 => [(7, 3), (10, 3)]
  | 3, 8 => [(8, 3), (13, -3)]
  | 3, 9 => [(9, 3), (15, -3)]
  | 3, 10 => [(7, 3), (10, 3)]
  | 3, 11 => [(11, 3), (17, 3)]
  | 3, 12 => [(12, 3), (18, 3)]
  | 3, 13 => [(8, -3), (13, 3)]
  | 3, 14 => [(14, 3), (20, -3)]
  | 3, 15 => [(9, -3), (15, 3)]
  | 3, 16 => [(16, 3), (21, -3)]
  | 3, 17 => [(11, 3), (17, 3)]
  | 3, 18 => [(12, 3), (18, 3)]
  | 3, 19 => [(19, 3), (22, 3)]
  | 3, 20 => [(14, -3), (20, 3)]
  | 3, 21 => [(16, -3), (21, 3)]
  | 3, 22 => [(19, 3), (22, 3)]
  | 3, 23 => [(23, 6)]
  | 3, 24 => [(24, 6)]
  | 3, 25 => [(25, 6)]
  | 3, 26 => [(26, 6)]
  | 4, 0 => [(0, 6), (6, 6)]
  | 4, 2 => [(2, 6)]
  | 4, 3 => [(3, 6)]
  | 4, 4 => [(4, 6)]
  | 4, 5 => [(5, 6)]
  | 4, 6 => [(0, 6), (6, 6)]
  | 4, 7 => [(7, 3), (11, 3)]
  | 4, 8 => [(8, 3), (14, -3)]
  | 4, 9 => [(9, 3), (16, -3)]
  | 4, 10 => [(10, 3), (17, -3)]
  | 4, 11 => [(7, 3), (11, 3)]
  | 4, 12 => [(12, 3), (19, 3)]
  | 4, 13 => [(13, 3), (20, 3)]
  | 4, 14 => [(8, -3), (14, 3)]
  | 4, 15 => [(15, 3), (21, 3)]
  | 4, 16 => [(9, -3), (16, 3)]
  | 4, 17 => [(10, -3), (17, 3)]
  | 4, 18 => [(18, 3), (22, -3)]
  | 4, 19 => [(12, 3), (19, 3)]
  | 4, 20 => [(13, 3), (20, 3)]
  | 4, 21 => [(15, 3), (21, 3)]
  | 4, 22 => [(18, -3), (22, 3)]
  | 4, 23 => [(23, 6)]
  | 4, 24 => [(24, 6)]
  | 4, 25 => [(25, 6)]
  | 4, 26 => [(26, 6)]
  | _, _ => []

def m1RowZ12 (r : Fin 5) (k : Fin 27) : List (Fin 27 × ℤ) :=
  match r.val, k.val with
  | 0, 26 => [(0, 6)]
  | 1, 25 => [(0, -6)]
  | 2, 22 => [(0, 4), (1, 8), (2, 4)]
  | 3, 24 => [(0, 6)]
  | 4, 23 => [(0, -6)]
  | _, _ => []

def sumTermsZA (l : List (Fin 27 × ℤ)) (f : Fin 27 → ZA) : ZA :=
  l.foldr (fun p acc => ((f p.1).smul p.2).add acc) ZA.zero

private theorem jmul_basis_L_0 : ∀ k : Fin 27,
    (qPentadZ6 ZO.L 0).jmul2 (basisLit_L k) = sumTermsZA (m0RowZ12 0 k) basisLit_L := by decide +kernel
private theorem jmul_basis_L_1 : ∀ k : Fin 27,
    (qPentadZ6 ZO.L 1).jmul2 (basisLit_L k) = sumTermsZA (m0RowZ12 1 k) basisLit_L := by decide +kernel
private theorem jmul_basis_L_2 : ∀ k : Fin 27,
    (qPentadZ6 ZO.L 2).jmul2 (basisLit_L k) = sumTermsZA (m0RowZ12 2 k) basisLit_L := by decide +kernel
private theorem jmul_basis_L_3 : ∀ k : Fin 27,
    (qPentadZ6 ZO.L 3).jmul2 (basisLit_L k) = sumTermsZA (m0RowZ12 3 k) basisLit_L := by decide +kernel
private theorem jmul_basis_L_4 : ∀ k : Fin 27,
    (qPentadZ6 ZO.L 4).jmul2 (basisLit_L k) = sumTermsZA (m0RowZ12 4 k) basisLit_L := by decide +kernel

private theorem jmul_basis_L (r : Fin 5) (k : Fin 27) :
    (qPentadZ6 ZO.L r).jmul2 (basisLit_L k) = sumTermsZA (m0RowZ12 r k) basisLit_L := by
  rcases r with ⟨_ | _ | _ | _ | _ | n, hr⟩
  · exact jmul_basis_L_0 k
  · exact jmul_basis_L_1 k
  · exact jmul_basis_L_2 k
  · exact jmul_basis_L_3 k
  · exact jmul_basis_L_4 k
  · exact absurd hr (by omega)

private theorem jmul_basis_K_0 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K 0).jmul2 (basisLit_K k) =
      (sumTermsZA (m0RowZ12 0 k) basisLit_K).add (sumTermsZA (m1RowZ12 0 k) basisLit_K) := by
  decide +kernel
private theorem jmul_basis_K_1 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K 1).jmul2 (basisLit_K k) =
      (sumTermsZA (m0RowZ12 1 k) basisLit_K).add (sumTermsZA (m1RowZ12 1 k) basisLit_K) := by
  decide +kernel
private theorem jmul_basis_K_2 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K 2).jmul2 (basisLit_K k) =
      (sumTermsZA (m0RowZ12 2 k) basisLit_K).add (sumTermsZA (m1RowZ12 2 k) basisLit_K) := by
  decide +kernel
private theorem jmul_basis_K_3 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K 3).jmul2 (basisLit_K k) =
      (sumTermsZA (m0RowZ12 3 k) basisLit_K).add (sumTermsZA (m1RowZ12 3 k) basisLit_K) := by
  decide +kernel
private theorem jmul_basis_K_4 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K 4).jmul2 (basisLit_K k) =
      (sumTermsZA (m0RowZ12 4 k) basisLit_K).add (sumTermsZA (m1RowZ12 4 k) basisLit_K) := by
  decide +kernel

private theorem jmul_basis_K (r : Fin 5) (k : Fin 27) :
    (qPentadZ6 ZO.K r).jmul2 (basisLit_K k) =
      (sumTermsZA (m0RowZ12 r k) basisLit_K).add (sumTermsZA (m1RowZ12 r k) basisLit_K) := by
  rcases r with ⟨_ | _ | _ | _ | _ | n, hr⟩
  · exact jmul_basis_K_0 k
  · exact jmul_basis_K_1 k
  · exact jmul_basis_K_2 k
  · exact jmul_basis_K_3 k
  · exact jmul_basis_K_4 k
  · exact absurd hr (by omega)

private theorem jmul_basis_mK_0 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K.neg 0).jmul2 (basisLit_mK k) =
      (sumTermsZA (m0RowZ12 0 k) basisLit_mK).sub (sumTermsZA (m1RowZ12 0 k) basisLit_mK) := by
  decide +kernel
private theorem jmul_basis_mK_1 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K.neg 1).jmul2 (basisLit_mK k) =
      (sumTermsZA (m0RowZ12 1 k) basisLit_mK).sub (sumTermsZA (m1RowZ12 1 k) basisLit_mK) := by
  decide +kernel
private theorem jmul_basis_mK_2 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K.neg 2).jmul2 (basisLit_mK k) =
      (sumTermsZA (m0RowZ12 2 k) basisLit_mK).sub (sumTermsZA (m1RowZ12 2 k) basisLit_mK) := by
  decide +kernel
private theorem jmul_basis_mK_3 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K.neg 3).jmul2 (basisLit_mK k) =
      (sumTermsZA (m0RowZ12 3 k) basisLit_mK).sub (sumTermsZA (m1RowZ12 3 k) basisLit_mK) := by
  decide +kernel
private theorem jmul_basis_mK_4 : ∀ k : Fin 27,
    (qPentadZ6 ZO.K.neg 4).jmul2 (basisLit_mK k) =
      (sumTermsZA (m0RowZ12 4 k) basisLit_mK).sub (sumTermsZA (m1RowZ12 4 k) basisLit_mK) := by
  decide +kernel

private theorem jmul_basis_mK (r : Fin 5) (k : Fin 27) :
    (qPentadZ6 ZO.K.neg r).jmul2 (basisLit_mK k) =
      (sumTermsZA (m0RowZ12 r k) basisLit_mK).sub (sumTermsZA (m1RowZ12 r k) basisLit_mK) := by
  rcases r with ⟨_ | _ | _ | _ | _ | n, hr⟩
  · exact jmul_basis_mK_0 k
  · exact jmul_basis_mK_1 k
  · exact jmul_basis_mK_2 k
  · exact jmul_basis_mK_3 k
  · exact jmul_basis_mK_4 k
  · exact absurd hr (by omega)

private theorem m0RowZ12_weight :
    ∀ r : Fin 5, ∀ k : Fin 27, ∀ p ∈ m0RowZ12 r k, basisWeight p.1 ≤ basisWeight k + 1 := by
  decide +kernel

private theorem m1RowZ12_weight :
    ∀ r : Fin 5, ∀ k : Fin 27, ∀ p ∈ m1RowZ12 r k, basisWeight k = 5 ∧ basisWeight p.1 = 0 := by
  decide +kernel

private theorem basisLit_tr_L : ∀ k : Fin 27, (basisLit_L k).tr = trVecZ k := by decide +kernel
private theorem basisLit_tr_K : ∀ k : Fin 27, (basisLit_K k).tr = trVecZ k := by decide +kernel
private theorem basisLit_tr_mK : ∀ k : Fin 27, (basisLit_mK k).tr = trVecZ k := by decide +kernel
private theorem unit_eq_basis_L : ZA.unit = (basisLit_L 0).add (basisLit_L 1) := by decide +kernel
private theorem unit_eq_basis_K : ZA.unit = (basisLit_K 0).add (basisLit_K 1) := by decide +kernel
private theorem unit_eq_basis_mK : ZA.unit = (basisLit_mK 0).add (basisLit_mK 1) := by decide +kernel
private theorem unitVec_weight : ∀ k : Fin 27, k.val = 0 ∨ k.val = 1 → basisWeight k = 0 := by
  decide +kernel

def listCoeffZ (l : List (Fin 27 × ℤ)) (j : Fin 27) : ℤ :=
  (l.map fun p => if p.1 = j then p.2 else 0).sum

def m0Coeff (r : Fin 5) (k j : Fin 27) : ℚ := (listCoeffZ (m0RowZ12 r k) j : ℚ) / 12
def m1Coeff (r : Fin 5) (k j : Fin 27) : ℚ := (listCoeffZ (m1RowZ12 r k) j : ℚ) / 12

private theorem listCoeffZ_ne_zero {l : List (Fin 27 × ℤ)} {j : Fin 27} (h : listCoeffZ l j ≠ 0) :
    ∃ p ∈ l, p.1 = j := by
  induction l with
  | nil => simp [listCoeffZ] at h
  | cons p t ih =>
    simp only [listCoeffZ, List.map_cons, List.sum_cons] at h ⊢
    by_cases hp : p.1 = j
    · exact ⟨p, by simp, hp⟩
    · simp only [hp, ↓reduceIte, zero_add] at h
      obtain ⟨q, hq, hqj⟩ := ih h
      exact ⟨q, by simp [hq], hqj⟩

private theorem m0Coeff_weight {r : Fin 5} {k j : Fin 27} (h : m0Coeff r k j ≠ 0) :
    basisWeight j ≤ basisWeight k + 1 := by
  have hz : listCoeffZ (m0RowZ12 r k) j ≠ 0 := by
    intro h0; apply h; simp [m0Coeff, h0]
  obtain ⟨p, hp, rfl⟩ := listCoeffZ_ne_zero hz
  exact m0RowZ12_weight r k p hp

private theorem m1Coeff_weight {r : Fin 5} {k j : Fin 27} (h : m1Coeff r k j ≠ 0) :
    basisWeight k = 5 ∧ basisWeight j = 0 := by
  have hz : listCoeffZ (m1RowZ12 r k) j ≠ 0 := by
    intro h0; apply h; simp [m1Coeff, h0]
  obtain ⟨p, hp, rfl⟩ := listCoeffZ_ne_zero hz
  exact m1RowZ12_weight r k p hp

def applyM0 (r : Fin 5) (v : Fin 27 → ℚ) (j : Fin 27) : ℚ :=
  ∑ k : Fin 27, v k * m0Coeff r k j

def applyM1 (r : Fin 5) (v : Fin 27 → ℚ) (j : Fin 27) : ℚ :=
  ∑ k : Fin 27, v k * m1Coeff r k j

def unitVec : Fin 27 → ℚ := fun k => if k.val = 0 ∨ k.val = 1 then 1 else 0

def coeff0 : List (Fin 5) → (Fin 27 → ℚ)
  | [] => unitVec
  | r :: L => applyM0 r (coeff0 L)

def coeff1 : List (Fin 5) → (Fin 27 → ℚ)
  | [] => 0
  | r :: L => applyM0 r (coeff1 L) + applyM1 r (coeff0 L)

private theorem coeff0_maxWeight (L : List (Fin 5)) (k : Fin 27) (hk : coeff0 L k ≠ 0) :
    basisWeight k ≤ L.length := by
  induction L generalizing k with
  | nil =>
    unfold coeff0 unitVec at hk
    by_cases h01 : k.val = 0 ∨ k.val = 1
    · rw [unitVec_weight k h01]; exact Nat.zero_le _
    · exact False.elim (hk (by split_ifs; rfl))
  | cons r L ih =>
    simp only [coeff0, applyM0] at hk
    obtain ⟨m, _, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    have hm1 : coeff0 L m ≠ 0 := left_ne_zero_of_mul hm
    have hm2 : m0Coeff r m k ≠ 0 := right_ne_zero_of_mul hm
    have hw := m0Coeff_weight hm2
    have hih := ih m hm1
    simp only [List.length_cons]
    omega

private theorem applyM1_eq_zero_of_weight_lt_five (r : Fin 5) (v : Fin 27 → ℚ)
    (hv : ∀ k : Fin 27, v k ≠ 0 → basisWeight k < 5) :
    applyM1 r v = 0 := by
  funext j
  simp only [applyM1, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hvk : v k = 0
  · simp [hvk]
  · have hlt := hv k hvk
    by_cases hm : m1Coeff r k j = 0
    · simp [hm]
    · have hw := (m1Coeff_weight hm).1
      omega

private theorem coeff1_eq_zero_of_le_five (L : List (Fin 5)) (hL : L.length ≤ 5) :
    coeff1 L = 0 := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    simp only [List.length_cons] at hL
    have ihL : coeff1 L = 0 := ih (by omega)
    simp only [coeff1, ihL]
    have h0 : applyM0 r 0 = 0 := by funext j; simp [applyM0]
    have h1 : applyM1 r (coeff0 L) = 0 :=
      applyM1_eq_zero_of_weight_lt_five r (coeff0 L) fun k hk => by
        have hw := coeff0_maxWeight L k hk
        omega
    rw [h0, h1, add_zero]

private theorem coeff1_maxWeight (L : List (Fin 5)) (k : Fin 27) (hk : coeff1 L k ≠ 0) :
    basisWeight k ≤ L.length - 6 := by
  induction L generalizing k with
  | nil => simp [coeff1] at hk
  | cons r L ih =>
    simp only [coeff1, Pi.add_apply] at hk
    have hcases : applyM0 r (coeff1 L) k ≠ 0 ∨ applyM1 r (coeff0 L) k ≠ 0 := by
      by_contra h
      push Not at h
      simp [h.1, h.2] at hk
    rcases hcases with h0 | h1
    · simp only [applyM0] at h0
      obtain ⟨m, _, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
      have hm1 : coeff1 L m ≠ 0 := left_ne_zero_of_mul hm
      have hm2 : m0Coeff r m k ≠ 0 := right_ne_zero_of_mul hm
      have hL6 : 6 ≤ L.length := by
        by_contra hlt
        have hz := coeff1_eq_zero_of_le_five L (by omega)
        simp [hz] at hm1
      have hw := m0Coeff_weight hm2
      have hih := ih m hm1
      simp only [List.length_cons]
      omega
    · simp only [applyM1] at h1
      obtain ⟨m, _, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      have hm2 : m1Coeff r m k ≠ 0 := right_ne_zero_of_mul hm
      have hw := (m1Coeff_weight hm2).2
      omega

noncomputable section

private theorem castZA_sumTermsZA (l : List (Fin 27 × ℤ)) (f : Fin 27 → ZA) :
    castZA (sumTermsZA l f) = (l.map fun p => (p.2 : ℝ) • castZA (f p.1)).sum := by
  induction l with
  | nil => simp [sumTermsZA, castZA_zero]
  | cons p t ih =>
    simp only [sumTermsZA, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [castZA_add, castZA_smul, ih]

private theorem list_sum_eq_fin_sum (l : List (Fin 27 × ℤ)) (g : Fin 27 → Albert) :
    (l.map fun p => (p.2 : ℝ) • g p.1).sum =
      ∑ j : Fin 27, (listCoeffZ l j : ℝ) • g j := by
  induction l with
  | nil => simp [listCoeffZ]
  | cons p t ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have hadd : (∑ j : Fin 27, (listCoeffZ (p :: t) j : ℝ) • g j) =
        (∑ j : Fin 27, ((if p.1 = j then p.2 else 0 : ℤ) : ℝ) • g j) +
        (∑ j : Fin 27, (listCoeffZ t j : ℝ) • g j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [listCoeffZ, List.map_cons, List.sum_cons, Int.cast_add, add_smul]
    have hsplit : (∑ j : Fin 27, ((if p.1 = j then p.2 else 0 : ℤ) : ℝ) • g j) =
        (p.2 : ℝ) • g p.1 := by
      have hite : ∀ j : Fin 27,
          ((if p.1 = j then p.2 else 0 : ℤ) : ℝ) • g j =
            if j = p.1 then (p.2 : ℝ) • g p.1 else 0 := fun j => by
        by_cases hj : j = p.1
        · subst hj; simp
        · have hj' : p.1 ≠ j := Ne.symm hj; simp [hj, hj']
      simp_rw [hite, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hadd, hsplit]

private theorem castZA_sumTermsZA_eq_fin (l : List (Fin 27 × ℤ)) (f : Fin 27 → ZA) :
    castZA (sumTermsZA l f) = ∑ j : Fin 27, (listCoeffZ l j : ℝ) • castZA (f j) := by
  rw [castZA_sumTermsZA, list_sum_eq_fin_sum l (fun j => castZA (f j))]

def evalBasis (b : Fin 27 → ZA) (v : Fin 27 → ℚ) : Albert :=
  ∑ k : Fin 27, (v k : ℝ) • castZA (b k)

private theorem jordanMul_sum_right {ι : Type*} (s : Finset ι) (x : Albert) (f : ι → Albert) :
    jordanMul x (∑ i ∈ s, f i) = ∑ i ∈ s, jordanMul x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jordanMul_zero_right x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, jordanMul_add_right, ih]

private theorem albertTrace_sum {ι : Type*} (s : Finset ι) (f : ι → Albert) :
    albertTrace (∑ i ∈ s, f i) = ∑ i ∈ s, albertTrace (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => change ∑ _ : Fin 3, (0 : ℝ) = 0; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, albertTrace_add, ih]

private theorem jordanMul_pentadF_basis (r : Fin 5) (k : Fin 27) :
    jordanMul (pentadF r) (castZA (basisLit_L k)) =
      ∑ j : Fin 27, (m0Coeff r k j : ℝ) • castZA (basisLit_L j) := by
  have h12 : (12 : ℝ) • jordanMul (pentadF r) (castZA (basisLit_L k)) =
      (12 : ℝ) • ∑ j : Fin 27, (m0Coeff r k j : ℝ) • castZA (basisLit_L j) := by
    calc (12 : ℝ) • jordanMul (pentadF r) (castZA (basisLit_L k))
        = (2 : ℝ) • jordanMul ((6 : ℝ) • pentadF r) (castZA (basisLit_L k)) := by
            rw [jordanMul_smul_left, smul_smul]; norm_num
      _ = castZA ((qPentadZ6 ZO.L r).jmul2 (basisLit_L k)) := by
            rw [castZA_jmul2, pentadF_eq_castZ6]
      _ = castZA (sumTermsZA (m0RowZ12 r k) basisLit_L) := by
            rw [jmul_basis_L]
      _ = ∑ j : Fin 27, (listCoeffZ (m0RowZ12 r k) j : ℝ) • castZA (basisLit_L j) :=
            castZA_sumTermsZA_eq_fin _ _
      _ = (12 : ℝ) • ∑ j : Fin 27, (m0Coeff r k j : ℝ) • castZA (basisLit_L j) := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul]; congr 1
            simp only [m0Coeff, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
            ring
  exact smul_right_injective Albert (by norm_num) h12

private theorem jordanMul_pentadFPlus_basis (r : Fin 5) (k : Fin 27) :
    jordanMul (pentadFPlus r) (castZA (basisLit_K k)) =
      ∑ j : Fin 27, ((m0Coeff r k j + m1Coeff r k j : ℚ) : ℝ) • castZA (basisLit_K j) := by
  have h12 : (12 : ℝ) • jordanMul (pentadFPlus r) (castZA (basisLit_K k)) =
      (12 : ℝ) • ∑ j : Fin 27, ((m0Coeff r k j + m1Coeff r k j : ℚ) : ℝ) •
        castZA (basisLit_K j) := by
    calc (12 : ℝ) • jordanMul (pentadFPlus r) (castZA (basisLit_K k))
        = (2 : ℝ) • jordanMul ((6 : ℝ) • pentadFPlus r) (castZA (basisLit_K k)) := by
            rw [jordanMul_smul_left, smul_smul]; norm_num
      _ = castZA ((qPentadZ6 ZO.K r).jmul2 (basisLit_K k)) := by
            rw [castZA_jmul2, pentadFPlus_eq_castZ6]
      _ = castZA ((sumTermsZA (m0RowZ12 r k) basisLit_K).add
            (sumTermsZA (m1RowZ12 r k) basisLit_K)) := by
            rw [jmul_basis_K]
      _ = (∑ j : Fin 27, (listCoeffZ (m0RowZ12 r k) j : ℝ) • castZA (basisLit_K j)) +
            (∑ j : Fin 27, (listCoeffZ (m1RowZ12 r k) j : ℝ) • castZA (basisLit_K j)) := by
            rw [castZA_add, castZA_sumTermsZA_eq_fin, castZA_sumTermsZA_eq_fin]
      _ = (12 : ℝ) • ∑ j : Fin 27, ((m0Coeff r k j + m1Coeff r k j : ℚ) : ℝ) •
            castZA (basisLit_K j) := by
            rw [← Finset.sum_add_distrib, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← add_smul, smul_smul]; congr 1
            simp only [m0Coeff, m1Coeff, Rat.cast_add, Rat.cast_div, Rat.cast_intCast,
              Rat.cast_ofNat]
            ring
  exact smul_right_injective Albert (by norm_num) h12

private theorem jordanMul_pentadFMinus_basis (r : Fin 5) (k : Fin 27) :
    jordanMul (pentadFMinus r) (castZA (basisLit_mK k)) =
      ∑ j : Fin 27, ((m0Coeff r k j - m1Coeff r k j : ℚ) : ℝ) • castZA (basisLit_mK j) := by
  have h12 : (12 : ℝ) • jordanMul (pentadFMinus r) (castZA (basisLit_mK k)) =
      (12 : ℝ) • ∑ j : Fin 27, ((m0Coeff r k j - m1Coeff r k j : ℚ) : ℝ) •
        castZA (basisLit_mK j) := by
    calc (12 : ℝ) • jordanMul (pentadFMinus r) (castZA (basisLit_mK k))
        = (2 : ℝ) • jordanMul ((6 : ℝ) • pentadFMinus r) (castZA (basisLit_mK k)) := by
            rw [jordanMul_smul_left, smul_smul]; norm_num
      _ = castZA ((qPentadZ6 ZO.K.neg r).jmul2 (basisLit_mK k)) := by
            rw [castZA_jmul2, pentadFMinus_eq_castZ6]
      _ = castZA ((sumTermsZA (m0RowZ12 r k) basisLit_mK).sub
            (sumTermsZA (m1RowZ12 r k) basisLit_mK)) := by
            rw [jmul_basis_mK]
      _ = (∑ j : Fin 27, (listCoeffZ (m0RowZ12 r k) j : ℝ) • castZA (basisLit_mK j)) -
            (∑ j : Fin 27, (listCoeffZ (m1RowZ12 r k) j : ℝ) • castZA (basisLit_mK j)) := by
            rw [castZA_sub, castZA_sumTermsZA_eq_fin, castZA_sumTermsZA_eq_fin]
      _ = (12 : ℝ) • ∑ j : Fin 27, ((m0Coeff r k j - m1Coeff r k j : ℚ) : ℝ) •
            castZA (basisLit_mK j) := by
            rw [← Finset.sum_sub_distrib, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← sub_smul, smul_smul]; congr 1
            simp only [m0Coeff, m1Coeff, Rat.cast_sub, Rat.cast_div, Rat.cast_intCast,
              Rat.cast_ofNat]
            ring
  exact smul_right_injective Albert (by norm_num) h12

private theorem evalBasis_unit (b : Fin 27 → ZA) (hunit : ZA.unit = (b 0).add (b 1)) :
    evalBasis b unitVec = albertUnit := by
  rw [← castZA_unit, hunit, castZA_add]
  unfold evalBasis unitVec
  have hterm : ∀ k : Fin 27,
      ((if k.val = 0 ∨ k.val = 1 then (1 : ℚ) else 0 : ℚ) : ℝ) • castZA (b k) =
        (if k = 0 then castZA (b 0) else 0) + (if k = 1 then castZA (b 1) else 0) := fun k => by
    fin_cases k <;> simp
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

def pentadChain (F : Fin 5 → Albert) (L : List (Fin 5)) : Albert :=
  L.foldr (fun r x => jordanMul (F r) x) albertUnit

private theorem pentadChain_nil (F : Fin 5 → Albert) : pentadChain F [] = albertUnit := rfl
private theorem pentadChain_cons (F : Fin 5 → Albert) (r : Fin 5) (L : List (Fin 5)) :
    pentadChain F (r :: L) = jordanMul (F r) (pentadChain F L) := rfl

private theorem jordanMul_evalBasis_generic (F : Fin 5 → Albert) (b : Fin 27 → ZA) (r : Fin 5)
    (v : Fin 27 → ℚ) (M : Fin 27 → Fin 27 → ℚ)
    (hstep : ∀ k : Fin 27, jordanMul (F r) (castZA (b k)) =
      ∑ j : Fin 27, (M k j : ℝ) • castZA (b j)) :
    jordanMul (F r) (evalBasis b v) =
      ∑ j : Fin 27, ((∑ k : Fin 27, v k * M k j : ℚ) : ℝ) • castZA (b j) := by
  unfold evalBasis
  rw [jordanMul_sum_right]
  simp_rw [jordanMul_smul_right, hstep, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Rat.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Rat.cast_mul]

private theorem pentadChain_eq_eval (L : List (Fin 5)) (hL : L.length ≤ 11) :
    pentadChain pentadF L = evalBasis basisLit_L (coeff0 L) ∧
    pentadChain pentadFPlus L = evalBasis basisLit_K (coeff0 L + coeff1 L) ∧
    pentadChain pentadFMinus L = evalBasis basisLit_mK (coeff0 L - coeff1 L) := by
  induction L with
  | nil =>
    simp only [pentadChain_nil, coeff0, coeff1, add_zero, sub_zero]
    exact ⟨(evalBasis_unit basisLit_L unit_eq_basis_L).symm,
      (evalBasis_unit basisLit_K unit_eq_basis_K).symm,
      (evalBasis_unit basisLit_mK unit_eq_basis_mK).symm⟩
  | cons r L ih =>
    simp only [List.length_cons] at hL
    obtain ⟨ih0, ihP, ihM⟩ := ih (by omega)
    have hkill : applyM1 r (coeff1 L) = 0 :=
      applyM1_eq_zero_of_weight_lt_five r (coeff1 L) fun k hk => by
        have hw := coeff1_maxWeight L k hk
        omega
    refine ⟨?_, ?_, ?_⟩
    · rw [pentadChain_cons, ih0]
      exact jordanMul_evalBasis_generic pentadF basisLit_L r (coeff0 L) (m0Coeff r)
        (jordanMul_pentadF_basis r)
    · rw [pentadChain_cons, ihP]
      rw [jordanMul_evalBasis_generic pentadFPlus basisLit_K r (coeff0 L + coeff1 L)
        (fun k j => m0Coeff r k j + m1Coeff r k j) (jordanMul_pentadFPlus_basis r)]
      unfold evalBasis
      refine Finset.sum_congr rfl fun j _ => ?_
      have hk_zero := congrFun hkill j
      simp only [applyM1, Pi.zero_apply] at hk_zero
      simp only [coeff0, coeff1, Pi.add_apply, applyM0, applyM1]
      congr 1; congr 1
      have halg : (∑ k : Fin 27, (coeff0 L k + coeff1 L k) * (m0Coeff r k j + m1Coeff r k j)) =
          (∑ k : Fin 27, coeff0 L k * m0Coeff r k j) +
            ((∑ k : Fin 27, coeff1 L k * m0Coeff r k j) +
              (∑ k : Fin 27, coeff0 L k * m1Coeff r k j)) +
            (∑ k : Fin 27, coeff1 L k * m1Coeff r k j) := by
        simp only [add_mul, mul_add, Finset.sum_add_distrib]
        ring
      rw [halg, hk_zero, add_zero]
    · rw [pentadChain_cons, ihM]
      rw [jordanMul_evalBasis_generic pentadFMinus basisLit_mK r (coeff0 L - coeff1 L)
        (fun k j => m0Coeff r k j - m1Coeff r k j) (jordanMul_pentadFMinus_basis r)]
      unfold evalBasis
      refine Finset.sum_congr rfl fun j _ => ?_
      have hk_zero := congrFun hkill j
      simp only [applyM1, Pi.zero_apply] at hk_zero
      simp only [coeff0, coeff1, Pi.sub_apply, Pi.add_apply, applyM0, applyM1]
      congr 1; congr 1
      have halg : (∑ k : Fin 27, (coeff0 L k - coeff1 L k) * (m0Coeff r k j - m1Coeff r k j)) =
          (∑ k : Fin 27, coeff0 L k * m0Coeff r k j) -
            ((∑ k : Fin 27, coeff1 L k * m0Coeff r k j) +
              (∑ k : Fin 27, coeff0 L k * m1Coeff r k j)) +
            (∑ k : Fin 27, coeff1 L k * m1Coeff r k j) := by
        simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
        ring
      rw [halg, hk_zero, add_zero]

private theorem albertTrace_evalBasis (b : Fin 27 → ZA) (htr : ∀ k : Fin 27, (b k).tr = trVecZ k)
    (v : Fin 27 → ℚ) :
    albertTrace (evalBasis b v) = ∑ k : Fin 27, (v k : ℝ) * ((trVecZ k : ℤ) : ℝ) := by
  unfold evalBasis
  rw [albertTrace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [albertTrace_smul, ← castZA_tr, htr k]

theorem pentadChain_trace_aff (L : List (Fin 5)) (hL : L.length ≤ 11) :
    albertTrace (pentadChain pentadF L) =
      (1 / 2 : ℝ) * albertTrace (pentadChain pentadFPlus L) +
      (1 / 2 : ℝ) * albertTrace (pentadChain pentadFMinus L) := by
  obtain ⟨h0, hP, hM⟩ := pentadChain_eq_eval L hL
  rw [h0, hP, hM,
    albertTrace_evalBasis basisLit_L basisLit_tr_L,
    albertTrace_evalBasis basisLit_K basisLit_tr_K,
    albertTrace_evalBasis basisLit_mK basisLit_tr_mK,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Rat.cast_add, Rat.cast_sub]
  ring

theorem pentadChain_trace_const (L : List (Fin 5)) (hL : L.length ≤ 5) :
    albertTrace (pentadChain pentadF L) = albertTrace (pentadChain pentadFPlus L) ∧
    albertTrace (pentadChain pentadF L) = albertTrace (pentadChain pentadFMinus L) := by
  obtain ⟨h0, hP, hM⟩ := pentadChain_eq_eval L (by omega)
  have hc1 : coeff1 L = 0 := coeff1_eq_zero_of_le_five L hL
  rw [h0, hP, hM, hc1, add_zero, sub_zero,
    albertTrace_evalBasis basisLit_L basisLit_tr_L,
    albertTrace_evalBasis basisLit_K basisLit_tr_K,
    albertTrace_evalBasis basisLit_mK basisLit_tr_mK]
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Two-Type Reset-Interval Chronological Word Induction -/

private def IsConst3 (c : ℝ × ℝ × ℝ) : Prop := c.1 = c.2.1 ∧ c.1 = c.2.2
private def IsAff3 (c : ℝ × ℝ × ℝ) : Prop := c.1 = (1 / 2 : ℝ) * c.2.1 + (1 / 2 : ℝ) * c.2.2

private theorem isConst3_smul {c : ℝ × ℝ × ℝ} (r : ℝ) (h : IsConst3 c) :
    IsConst3 (r * c.1, r * c.2.1, r * c.2.2) :=
  ⟨by rw [h.1], by rw [h.2]⟩

private theorem isAff3_smul {c : ℝ × ℝ × ℝ} (r : ℝ) (h : IsAff3 c) :
    IsAff3 (r * c.1, r * c.2.1, r * c.2.2) := by
  unfold IsAff3 at h ⊢
  rw [h]; ring

private theorem isConst3_mul {a b : ℝ × ℝ × ℝ} (ha : IsConst3 a) (hb : IsConst3 b) :
    IsConst3 (a.1 * b.1, a.2.1 * b.2.1, a.2.2 * b.2.2) :=
  ⟨by rw [ha.1, hb.1], by rw [ha.2, hb.2]⟩

private theorem isConst3_mul_isAff3 {a b : ℝ × ℝ × ℝ} (ha : IsConst3 a) (hb : IsAff3 b) :
    IsAff3 (a.1 * b.1, a.2.1 * b.2.1, a.2.2 * b.2.2) := by
  unfold IsAff3 at hb ⊢
  rw [← ha.1, ← ha.2, hb]; ring

private theorem isAff3_mul_isConst3 {a b : ℝ × ℝ × ℝ} (ha : IsAff3 a) (hb : IsConst3 b) :
    IsAff3 (a.1 * b.1, a.2.1 * b.2.1, a.2.2 * b.2.2) := by
  unfold IsAff3 at ha ⊢
  rw [← hb.1, ← hb.2, ha]; ring

private def TermValid (k : ℕ) (t : (ℝ × ℝ × ℝ) × List (Fin 5)) : Prop :=
  (IsConst3 t.1 ∧ t.2.length + k ≤ 10) ∨ (IsAff3 t.1 ∧ t.2.length + k ≤ 5)

private def stepTerm (a : Outcome (Fin 5)) (t : (ℝ × ℝ × ℝ) × List (Fin 5)) :
    List ((ℝ × ℝ × ℝ) × List (Fin 5)) :=
  let L := a.1 :: t.2
  let τ : ℝ × ℝ × ℝ :=
    (albertTrace (pentadChain pentadF L),
     albertTrace (pentadChain pentadFPlus L),
     albertTrace (pentadChain pentadFMinus L))
  let resetTerm : (ℝ × ℝ × ℝ) × List (Fin 5) :=
    ((t.1.1 * τ.1, t.1.2.1 * τ.2.1, t.1.2.2 * τ.2.2), [a.1])
  if a.2 then [resetTerm]
  else [t, ((-2 * t.1.1, -2 * t.1.2.1, -2 * t.1.2.2), a.1 :: t.2), resetTerm]

private def stepTerms (a : Outcome (Fin 5)) (ts : List ((ℝ × ℝ × ℝ) × List (Fin 5))) :
    List ((ℝ × ℝ × ℝ) × List (Fin 5)) :=
  ts.flatMap (stepTerm a)

private theorem quadraticMap_compl_atom {p x : Albert} (hp : IsAtom p) :
    quadraticMap (albertUnit - p) x = x - (2 : ℝ) • jordanMul p x + tracePairing p x • p := by
  have hp2 : jordanMul p p = p := hp.1
  have h1 : jordanMul (albertUnit - p) (albertUnit - p) = albertUnit - p := by
    simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
      jordanMul_albertUnit_right, hp2]
    abel
  have hq : quadraticMap p x = tracePairing p x • p := quadraticMap_atom p x hp
  have h2 : jordanMul p (jordanMul p x) + jordanMul p (jordanMul p x) =
      quadraticMap p x + jordanMul p x := by
    unfold quadraticMap
    rw [hp2, two_nsmul]
    abel
  have htwo : (2 : ℝ) • jordanMul p x = jordanMul p x + jordanMul p x := by
    rw [← one_add_one_eq_two, add_smul, one_smul]
  unfold quadraticMap
  rw [h1, two_nsmul]
  simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left]
  rw [show (x - jordanMul p x - (jordanMul p x - jordanMul p (jordanMul p x))) +
      (x - jordanMul p x - (jordanMul p x - jordanMul p (jordanMul p x))) -
      (x - jordanMul p x) =
      x - (jordanMul p x + jordanMul p x + jordanMul p x) +
        (jordanMul p (jordanMul p x) + jordanMul p (jordanMul p x)) by abel]
  rw [h2, hq, htwo]
  abel

private def evalList (F : Fin 5 → Albert) (proj : ℝ × ℝ × ℝ → ℝ)
    (ts : List ((ℝ × ℝ × ℝ) × List (Fin 5))) : Albert :=
  (ts.map fun t => proj t.1 • pentadChain F t.2).sum

private theorem evalList_stepTerms (F : Fin 5 → Albert) (hF : ∀ i, IsAtom (F i))
    (proj : ℝ × ℝ × ℝ → ℝ)
    (hτ : ∀ L : List (Fin 5),
      proj (albertTrace (pentadChain pentadF L),
        albertTrace (pentadChain pentadFPlus L),
        albertTrace (pentadChain pentadFMinus L)) = albertTrace (pentadChain F L))
    (hm2 : ∀ x y z : ℝ, proj (-2 * x, -2 * y, -2 * z) = -2 * proj (x, y, z))
    (hmul : ∀ x y z x' y' z' : ℝ,
      proj (x * x', y * y', z * z') = proj (x, y, z) * proj (x', y', z'))
    (a : Outcome (Fin 5)) (ts : List ((ℝ × ℝ × ℝ) × List (Fin 5))) :
    evalList F proj (stepTerms a ts) =
      quadraticMap (nativeOutcome F a) (evalList F proj ts) := by
  induction ts with
  | nil =>
    simp [stepTerms, evalList, quadraticMap_zero_right]
  | cons t ts ih =>
    simp only [stepTerms, List.flatMap_cons, evalList, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, quadraticMap_add_right] at ih ⊢
    rw [ih]
    congr 1
    have hsingle : ∀ r : Fin 5, pentadChain F [r] = F r := fun r => by
      simp [pentadChain, jordanMul_albertUnit_right]
    have htp : ∀ r L, tracePairing (F r) (pentadChain F L) =
        albertTrace (pentadChain F (r :: L)) := fun r L => rfl
    rcases a with ⟨r, b⟩
    cases b
    · simp only [stepTerm, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, nativeOutcome]
      rw [quadraticMap_smul_right, quadraticMap_compl_atom (hF r),
        hm2 t.1.1 t.1.2.1 t.1.2.2,
        hmul t.1.1 t.1.2.1 t.1.2.2
          (albertTrace (pentadChain pentadF (r :: t.2)))
          (albertTrace (pentadChain pentadFPlus (r :: t.2)))
          (albertTrace (pentadChain pentadFMinus (r :: t.2))),
        hτ (r :: t.2), hsingle r, ← htp r t.2, ← pentadChain_cons F r t.2]
      rw [smul_add, smul_sub, smul_smul, smul_smul,
        show -2 * proj (t.1.1, t.1.2.1, t.1.2.2) = -(proj (t.1.1, t.1.2.1, t.1.2.2) * 2) by ring,
        neg_smul, ← add_assoc, ← sub_eq_add_neg]
    · simp only [stepTerm, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, nativeOutcome]
      rw [quadraticMap_smul_right, quadraticMap_atom (F r) _ (hF r),
        hmul t.1.1 t.1.2.1 t.1.2.2
          (albertTrace (pentadChain pentadF (r :: t.2)))
          (albertTrace (pentadChain pentadFPlus (r :: t.2)))
          (albertTrace (pentadChain pentadFMinus (r :: t.2))),
        hτ (r :: t.2), hsingle r, ← htp r t.2, smul_smul]

private theorem stepTerm_valid {k : ℕ} {a : Outcome (Fin 5)}
    {t : (ℝ × ℝ × ℝ) × List (Fin 5)} (ht : TermValid (k + 1) t) :
    ∀ t' ∈ stepTerm a t, TermValid k t' := by
  let L := a.1 :: t.2
  let τ : ℝ × ℝ × ℝ :=
    (albertTrace (pentadChain pentadF L),
     albertTrace (pentadChain pentadFPlus L),
     albertTrace (pentadChain pentadFMinus L))
  let resetTerm : (ℝ × ℝ × ℝ) × List (Fin 5) :=
    ((t.1.1 * τ.1, t.1.2.1 * τ.2.1, t.1.2.2 * τ.2.2), [a.1])
  have hreset_of_const : IsConst3 t.1 → t.2.length + (k + 1) ≤ 10 →
      TermValid k resetTerm := by
    intro hc hlen
    by_cases h4 : t.2.length ≤ 4
    · have hL5 : L.length ≤ 5 := by simp only [L, List.length_cons]; omega
      have hτc := pentadChain_trace_const L hL5
      have hconst : IsConst3 τ := ⟨hτc.1, hτc.2⟩
      exact Or.inl ⟨isConst3_mul hc hconst, by simp [resetTerm]; omega⟩
    · have h5 : 5 ≤ t.2.length := by omega
      have hL11 : L.length ≤ 11 := by simp only [L, List.length_cons]; omega
      have hτa : IsAff3 τ := pentadChain_trace_aff L hL11
      exact Or.inr ⟨isConst3_mul_isAff3 hc hτa, by simp [resetTerm]; omega⟩
  have hreset_of_aff : IsAff3 t.1 → t.2.length + (k + 1) ≤ 5 →
      TermValid k resetTerm := by
    intro ha hlen
    have hL5 : L.length ≤ 5 := by simp only [L, List.length_cons]; omega
    have hτc := pentadChain_trace_const L hL5
    have hconst : IsConst3 τ := ⟨hτc.1, hτc.2⟩
    exact Or.inr ⟨isAff3_mul_isConst3 ha hconst, by simp [resetTerm]; omega⟩
  intro t' ht'
  rcases a with ⟨r, b⟩
  rcases ht with ⟨hc, hlen⟩ | ⟨ha, hlen⟩
  · cases b
    · simp only [stepTerm, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at ht'
      rcases ht' with rfl | rfl | rfl | ht'_nil
      · exact Or.inl ⟨hc, by omega⟩
      · exact Or.inl ⟨isConst3_smul (-2) hc, by simp only [List.length_cons]; omega⟩
      · exact hreset_of_const hc hlen
      · cases ht'_nil
    · simp only [stepTerm, ↓reduceIte, List.mem_singleton] at ht'
      rw [ht']
      exact hreset_of_const hc hlen
  · cases b
    · simp only [stepTerm, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at ht'
      rcases ht' with rfl | rfl | rfl | ht'_nil
      · exact Or.inr ⟨ha, by omega⟩
      · exact Or.inr ⟨isAff3_smul (-2) ha, by simp only [List.length_cons]; omega⟩
      · exact hreset_of_aff ha hlen
      · cases ht'_nil
    · simp only [stepTerm, ↓reduceIte, List.mem_singleton] at ht'
      rw [ht']
      exact hreset_of_aff ha hlen

private theorem stepTerms_valid {k : ℕ} {a : Outcome (Fin 5)}
    {ts : List ((ℝ × ℝ × ℝ) × List (Fin 5))} (hts : ∀ t ∈ ts, TermValid (k + 1) t) :
    ∀ t' ∈ stepTerms a ts, TermValid k t' := by
  intro t' ht'
  simp only [stepTerms, List.mem_flatMap] at ht'
  rcases ht' with ⟨t, ht_mem, ht'_mem⟩
  exact stepTerm_valid (hts t ht_mem) t' ht'_mem

private def foldTerms (w : Word (Fin 5)) (ts : List ((ℝ × ℝ × ℝ) × List (Fin 5))) :
    List ((ℝ × ℝ × ℝ) × List (Fin 5)) :=
  w.foldl (fun acc a => stepTerms a acc) ts

private theorem foldTerms_valid (w : Word (Fin 5))
    (ts : List ((ℝ × ℝ × ℝ) × List (Fin 5))) (hts : ∀ t ∈ ts, TermValid w.length t) :
    ∀ t ∈ foldTerms w ts, TermValid 0 t := by
  induction w generalizing ts with
  | nil => exact hts
  | cons a w ih =>
    simp only [foldTerms, List.foldl_cons] at ih ⊢
    simp only [List.length_cons] at hts
    exact ih (stepTerms a ts) (stepTerms_valid hts)

private theorem evalList_foldTerms (F : Fin 5 → Albert) (hF : ∀ i, IsAtom (F i))
    (proj : ℝ × ℝ × ℝ → ℝ)
    (hτ : ∀ L : List (Fin 5),
      proj (albertTrace (pentadChain pentadF L),
        albertTrace (pentadChain pentadFPlus L),
        albertTrace (pentadChain pentadFMinus L)) = albertTrace (pentadChain F L))
    (hm2 : ∀ x y z : ℝ, proj (-2 * x, -2 * y, -2 * z) = -2 * proj (x, y, z))
    (hmul : ∀ x y z x' y' z' : ℝ,
      proj (x * x', y * y', z * z') = proj (x, y, z) * proj (x', y', z'))
    (w : Word (Fin 5)) (ts : List ((ℝ × ℝ × ℝ) × List (Fin 5))) :
    evalList F proj (foldTerms w ts) = nativeBranchState F (evalList F proj ts) w := by
  induction w generalizing ts with
  | nil => rfl
  | cons a w ih =>
    simp only [foldTerms, List.foldl_cons, nativeBranchState] at ih ⊢
    rw [ih (stepTerms a ts), evalList_stepTerms F hF proj hτ hm2 hmul a ts]

private theorem trace_evalList_aff (ts : List ((ℝ × ℝ × ℝ) × List (Fin 5)))
    (hts : ∀ t ∈ ts, TermValid 0 t) :
    albertTrace (evalList pentadF Prod.fst ts) =
      (1 / 2 : ℝ) * albertTrace (evalList pentadFPlus (fun c => c.2.1) ts) +
      (1 / 2 : ℝ) * albertTrace (evalList pentadFMinus (fun c => c.2.2) ts) := by
  have halbert0 : albertTrace (0 : Albert) = 0 := by
    change ∑ _ : Fin 3, (0 : ℝ) = 0
    simp
  induction ts with
  | nil => simp [evalList, halbert0]
  | cons t ts ih =>
    have hts' : ∀ s ∈ ts, TermValid 0 s := fun s hs => hts s (by simp [hs])
    have ht0 : TermValid 0 t := hts t (by simp)
    have ih' := ih hts'
    simp only [evalList, List.map_cons, List.sum_cons, albertTrace_add, albertTrace_smul] at ih' ⊢
    have hterm : t.1.1 * albertTrace (pentadChain pentadF t.2) =
        (1 / 2 : ℝ) * (t.1.2.1 * albertTrace (pentadChain pentadFPlus t.2)) +
        (1 / 2 : ℝ) * (t.1.2.2 * albertTrace (pentadChain pentadFMinus t.2)) := by
      rcases ht0 with ⟨hc, hlen⟩ | ⟨ha, hlen⟩
      · have haff : IsAff3
            (albertTrace (pentadChain pentadF t.2),
             albertTrace (pentadChain pentadFPlus t.2),
             albertTrace (pentadChain pentadFMinus t.2)) := pentadChain_trace_aff t.2 (by omega)
        exact isConst3_mul_isAff3 hc haff
      · have hc := pentadChain_trace_const t.2 (by omega)
        have hconst : IsConst3
            (albertTrace (pentadChain pentadF t.2),
             albertTrace (pentadChain pentadFPlus t.2),
             albertTrace (pentadChain pentadFMinus t.2)) := ⟨hc.1, hc.2⟩
        exact isAff3_mul_isConst3 ha hconst
    linarith

private theorem pentadF_match_avg_of_init (ts : List ((ℝ × ℝ × ℝ) × List (Fin 5)))
    (w : Word (Fin 5)) (hts : ∀ t ∈ ts, TermValid w.length t) :
    nativeWordProbability pentadF (evalList pentadF Prod.fst ts) w =
      (1 / 2 : ℝ) * nativeWordProbability pentadFPlus (evalList pentadFPlus (fun c => c.2.1) ts) w +
      (1 / 2 : ℝ) * nativeWordProbability pentadFMinus (evalList pentadFMinus (fun c => c.2.2) ts) w := by
  unfold nativeWordProbability
  rw [← evalList_foldTerms pentadF pentadF_isAtom Prod.fst (fun _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ _ _ _ _ => rfl) w ts,
      ← evalList_foldTerms pentadFPlus pentadFPlus_isAtom (fun c => c.2.1) (fun _ => rfl)
        (fun _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) w ts,
      ← evalList_foldTerms pentadFMinus pentadFMinus_isAtom (fun c => c.2.2) (fun _ => rfl)
        (fun _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) w ts]
  exact trace_evalList_aff (foldTerms w ts) (foldTerms_valid w ts hts)

/-- All-word probability agreement between `pentadF` from `pentadF 0` and the average of
`pentadFPlus` and `pentadFMinus` for every binary word of length at most `9`. -/
theorem pentadF_p0_match_avg (w : Word (Fin 5)) (hw : w.length ≤ 9) :
    nativeWordProbability pentadF (pentadF 0) w =
      (1 / 2 : ℝ) * nativeWordProbability pentadFPlus (pentadFPlus 0) w +
      (1 / 2 : ℝ) * nativeWordProbability pentadFMinus (pentadFMinus 0) w := by
  let ts : List ((ℝ × ℝ × ℝ) × List (Fin 5)) := [((1, 1, 1), [0])]
  have hts : ∀ t ∈ ts, TermValid w.length t := by
    intro t ht
    simp only [ts, List.mem_singleton] at ht
    subst ht
    exact Or.inl ⟨⟨rfl, rfl⟩, by simp; omega⟩
  have h0 : evalList pentadF Prod.fst ts = pentadF 0 := by
    simp [ts, evalList, pentadChain, jordanMul_albertUnit_right]
  have hP : evalList pentadFPlus (fun c => c.2.1) ts = pentadFPlus 0 := by
    simp [ts, evalList, pentadChain, jordanMul_albertUnit_right]
  have hM : evalList pentadFMinus (fun c => c.2.2) ts = pentadFMinus 0 := by
    simp [ts, evalList, pentadChain, jordanMul_albertUnit_right]
  simpa only [h0, hP, hM] using pentadF_match_avg_of_init ts w hts

/-- All-word probability agreement between `pentadF` from `(1 / 3 : ℝ) • albertUnit` and the
average of `pentadFPlus` and `pentadFMinus` for every binary word of length at most `10`. -/
theorem pentadF_e3_match_avg (w : Word (Fin 5)) (hw : w.length ≤ 10) :
    nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w =
      (1 / 2 : ℝ) * nativeWordProbability pentadFPlus ((1 / 3 : ℝ) • albertUnit) w +
      (1 / 2 : ℝ) * nativeWordProbability pentadFMinus ((1 / 3 : ℝ) • albertUnit) w := by
  let ts : List ((ℝ × ℝ × ℝ) × List (Fin 5)) := [((1 / 3, 1 / 3, 1 / 3), [])]
  have hts : ∀ t ∈ ts, TermValid w.length t := by
    intro t ht
    simp only [ts, List.mem_singleton] at ht
    subst ht
    exact Or.inl ⟨⟨rfl, rfl⟩, by simp; omega⟩
  have h0 : evalList pentadF Prod.fst ts = (1 / 3 : ℝ) • albertUnit := by
    simp [ts, evalList, pentadChain]
  have hP : evalList pentadFPlus (fun c => c.2.1) ts = (1 / 3 : ℝ) • albertUnit := by
    simp [ts, evalList, pentadChain]
  have hM : evalList pentadFMinus (fun c => c.2.2) ts = (1 / 3 : ℝ) • albertUnit := by
    simp [ts, evalList, pentadChain]
  simpa only [h0, hP, hM] using pentadF_match_avg_of_init ts w hts

/-! ## Section 5: Explicit Separating Words at Lengths 10 (`p₀`) and 11 (`e/3`) -/

private def stX_0 : ZA := ⟨1, 0, 0, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stX_1 : ZA := ⟨4, 1, 1, ⟨⟨0, 2, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-2, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stX_2 : ZA := ⟨5, 5, 4, ⟨⟨-5, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-4, -2, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨4, 2, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stX_3 : ZA := ⟨5, 5, 8, ⟨⟨0, 0, 5, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-4, -2, 4, -2⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨4, 2, 4, -2⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stX_4 : ZA := ⟨53, 17, 50, ⟨⟨-6, 10, 21, -18⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-43, 6, 18, 21⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨6, -7, 21, -18⟩, ⟨0, 0, 0, 0⟩⟩⟩

private def stR_L_0 : ZA := ⟨1, 1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_L_1 : ZA := ⟨5, 5, 2, ⟨⟨0, 4, 0, 0⟩, ⟨-3, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, -3, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨-3, 0, 0, 0⟩⟩⟩
private def stR_L_2 : ZA := ⟨5, 5, 4, ⟨⟨0, 0, 5, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 1⟩, ⟨0, -3, -3, 0⟩⟩, ⟨⟨0, -1, 1, 0⟩, ⟨-3, 0, 0, 3⟩⟩⟩
private def stR_L_3 : ZA := ⟨5, 5, 8, ⟨⟨-5, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 1, -1, 1⟩, ⟨3, -3, -3, -3⟩⟩, ⟨⟨1, -1, 1, -1⟩, ⟨-3, 3, 3, 3⟩⟩⟩
private def stR_L_4 : ZA := ⟨35, 35, 50, ⟨⟨-21, 10, 6, 0⟩, ⟨-18, 0, 18, 0⟩⟩, ⟨⟨-25, 21, 0, 6⟩, ⟨0, -18, 0, -18⟩⟩, ⟨⟨21, -25, 6, 0⟩, ⟨-18, 0, 18, 0⟩⟩⟩

private def stY_L_0 : ZA := ⟨1, 1, 0, ⟨⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_L_1 : ZA := ⟨5, 5, 2, ⟨⟨0, 4, 0, 0⟩, ⟨-3, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 0, 0⟩, ⟨0, -3, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨-3, 0, 0, 0⟩⟩⟩
private def stY_L_2 : ZA := ⟨0, 5, 2, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 0⟩, ⟨-3, 0, 0, 0⟩⟩⟩
private def stY_L_3 : ZA := ⟨5, 5, 8, ⟨⟨-5, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 2, 0, 0⟩, ⟨6, 0, 0, 0⟩⟩, ⟨⟨0, -2, 0, 0⟩, ⟨-6, 0, 0, 0⟩⟩⟩
private def stY_L_4 : ZA := ⟨29, 41, 50, ⟨⟨-21, 10, 0, 0⟩, ⟨-18, -18, 0, 0⟩⟩, ⟨⟨-19, 21, 0, 0⟩, ⟨18, -18, 0, 0⟩⟩, ⟨⟨21, -31, 0, 0⟩, ⟨-18, -18, 0, 0⟩⟩⟩

private def stR_K_0 : ZA := ⟨1, 1, 0, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_K_1 : ZA := ⟨5, 5, 2, ⟨⟨0, 4, 0, -3⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 3, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, -3⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_K_2 : ZA := ⟨5, 5, 4, ⟨⟨0, 0, 5, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, -3, 3, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨3, -1, 1, -3⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_K_3 : ZA := ⟨5, 5, 8, ⟨⟨-5, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-4, -2, 2, 4⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨4, 2, -2, -4⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_K_4 : ZA := ⟨53, 17, 50, ⟨⟨-21, 10, 6, -18⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-43, 21, 18, 6⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨21, -7, 6, -18⟩, ⟨0, 0, 0, 0⟩⟩⟩

private def stY_K_0 : ZA := ⟨1, 1, 0, ⟨⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_K_1 : ZA := ⟨5, 5, 2, ⟨⟨0, 4, 0, -3⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, 3, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, -3⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_K_2 : ZA := ⟨0, 5, 2, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, -3⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_K_3 : ZA := ⟨5, 5, 8, ⟨⟨-5, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 2, 0, 6⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -2, 0, -6⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_K_4 : ZA := ⟨29, 41, 50, ⟨⟨-21, 10, 18, -18⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-19, 21, 18, 18⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨21, -31, 18, -18⟩, ⟨0, 0, 0, 0⟩⟩⟩

private def stR_mK_0 : ZA := ⟨1, 1, 0, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_mK_1 : ZA := ⟨5, 5, 2, ⟨⟨0, 4, 0, 3⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, -3, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 3⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_mK_2 : ZA := ⟨5, 5, 4, ⟨⟨0, 0, 5, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 3, -3, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-3, -1, 1, 3⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_mK_3 : ZA := ⟨5, 5, 8, ⟨⟨-5, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨2, 4, -4, -2⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-2, -4, 4, 2⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stR_mK_4 : ZA := ⟨17, 53, 50, ⟨⟨-21, 10, 6, 18⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-7, 21, -18, 6⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨21, -43, 6, 18⟩, ⟨0, 0, 0, 0⟩⟩⟩

private def stY_mK_0 : ZA := ⟨1, 1, 0, ⟨⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_mK_1 : ZA := ⟨5, 5, 2, ⟨⟨0, 4, 0, 3⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-1, 0, -3, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 3⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_mK_2 : ZA := ⟨0, 5, 2, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -1, 0, 3⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_mK_3 : ZA := ⟨5, 5, 8, ⟨⟨-5, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, 2, 0, -6⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨0, -2, 0, 6⟩, ⟨0, 0, 0, 0⟩⟩⟩
private def stY_mK_4 : ZA := ⟨29, 41, 50, ⟨⟨-21, 10, -18, 18⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨-19, 21, -18, -18⟩, ⟨0, 0, 0, 0⟩⟩, ⟨⟨21, -31, -18, 18⟩, ⟨0, 0, 0, 0⟩⟩⟩

private theorem stX_init_eq (u : ZO) : stX_0 = qPentadScaled u 0 := by
  change stX_0 = qPentadScaled ZO.L 0
  decide +kernel
private theorem stR_L_init_eq : stR_L_0 = qPentadScaled ZO.L 4 := by decide +kernel
private theorem stY_L_init_eq : stY_L_0 = qPentadScaled ZO.L 4 := by decide +kernel
private theorem stR_K_init_eq : stR_K_0 = qPentadScaled ZO.K 4 := by decide +kernel
private theorem stY_K_init_eq : stY_K_0 = qPentadScaled ZO.K 4 := by decide +kernel
private theorem stR_mK_init_eq : stR_mK_0 = qPentadScaled ZO.K.neg 4 := by decide +kernel
private theorem stY_mK_init_eq : stY_mK_0 = qPentadScaled ZO.K.neg 4 := by decide +kernel

private theorem stX_steps (u : ZO) :
    (zCompl u 2).U4 stX_0 = stX_1.smul 4 ∧
    (zCompl u 1).U4 stX_1 = stX_2.smul 4 ∧
    (zCompl u 3).U4 stX_2 = stX_3.smul 8 ∧
    (zCompl u 2).U4 stX_3 = stX_4.smul 4 := by
  change (zCompl ZO.L 2).U4 stX_0 = stX_1.smul 4 ∧
    (zCompl ZO.L 1).U4 stX_1 = stX_2.smul 4 ∧
    (zCompl ZO.L 3).U4 stX_2 = stX_3.smul 8 ∧
    (zCompl ZO.L 2).U4 stX_3 = stX_4.smul 4
  decide +kernel

private theorem stR_L_steps :
    (zCompl ZO.L 2).U4 stR_L_0 = stR_L_1.smul 4 ∧
    (zCompl ZO.L 3).U4 stR_L_1 = stR_L_2.smul 8 ∧
    (zCompl ZO.L 1).U4 stR_L_2 = stR_L_3.smul 8 ∧
    (zCompl ZO.L 2).U4 stR_L_3 = stR_L_4.smul 4 := by
  decide +kernel

private theorem stY_L_steps :
    (zCompl ZO.L 2).U4 stY_L_0 = stY_L_1.smul 4 ∧
    (zCompl ZO.L 0).U4 stY_L_1 = stY_L_2.smul 4 ∧
    (zCompl ZO.L 1).U4 stY_L_2 = stY_L_3.smul 4 ∧
    (zCompl ZO.L 2).U4 stY_L_3 = stY_L_4.smul 4 := by
  decide +kernel

private theorem stR_K_steps :
    (zCompl ZO.K 2).U4 stR_K_0 = stR_K_1.smul 4 ∧
    (zCompl ZO.K 3).U4 stR_K_1 = stR_K_2.smul 8 ∧
    (zCompl ZO.K 1).U4 stR_K_2 = stR_K_3.smul 8 ∧
    (zCompl ZO.K 2).U4 stR_K_3 = stR_K_4.smul 4 := by
  decide +kernel

private theorem stY_K_steps :
    (zCompl ZO.K 2).U4 stY_K_0 = stY_K_1.smul 4 ∧
    (zCompl ZO.K 0).U4 stY_K_1 = stY_K_2.smul 4 ∧
    (zCompl ZO.K 1).U4 stY_K_2 = stY_K_3.smul 4 ∧
    (zCompl ZO.K 2).U4 stY_K_3 = stY_K_4.smul 4 := by
  decide +kernel

private theorem stR_mK_steps :
    (zCompl ZO.K.neg 2).U4 stR_mK_0 = stR_mK_1.smul 4 ∧
    (zCompl ZO.K.neg 3).U4 stR_mK_1 = stR_mK_2.smul 8 ∧
    (zCompl ZO.K.neg 1).U4 stR_mK_2 = stR_mK_3.smul 8 ∧
    (zCompl ZO.K.neg 2).U4 stR_mK_3 = stR_mK_4.smul 4 := by
  decide +kernel

private theorem stY_mK_steps :
    (zCompl ZO.K.neg 2).U4 stY_mK_0 = stY_mK_1.smul 4 ∧
    (zCompl ZO.K.neg 0).U4 stY_mK_1 = stY_mK_2.smul 4 ∧
    (zCompl ZO.K.neg 1).U4 stY_mK_2 = stY_mK_3.smul 4 ∧
    (zCompl ZO.K.neg 2).U4 stY_mK_3 = stY_mK_4.smul 4 := by
  decide +kernel

private theorem tp2_checks_L :
    (qPentadScaled ZO.L 4).tp2 stX_4 = 140 ∧
    (qPentadScaled ZO.L 0).tp2 stR_L_4 = 70 ∧
    (qPentadScaled ZO.L 3).tp2 stY_L_4 = 140 := by
  decide +kernel

private theorem tp2_checks_K :
    (qPentadScaled ZO.K 4).tp2 stX_4 = 212 ∧
    (qPentadScaled ZO.K 0).tp2 stR_K_4 = 106 ∧
    (qPentadScaled ZO.K 3).tp2 stY_K_4 = 68 := by
  decide +kernel

private theorem tp2_checks_mK :
    (qPentadScaled ZO.K.neg 4).tp2 stX_4 = 68 ∧
    (qPentadScaled ZO.K.neg 0).tp2 stR_mK_4 = 34 ∧
    (qPentadScaled ZO.K.neg 3).tp2 stY_mK_4 = 212 := by
  decide +kernel

noncomputable section

private theorem castZA_zCompl (u : ZO) (F : Fin 5 → Albert)
    (hF : ∀ i, castZA (qPentadScaled u i) = (atomScale i : ℝ) • F i) (r : Fin 5) :
    castZA (zCompl u r) = (atomScale r : ℝ) • (albertUnit - F r) := by
  rw [zCompl, castZA_sub, castZA_smul, castZA_unit, hF r, smul_sub]

private theorem stepU4_eq {x y : Albert} {zx zy zx' : ZA} {d den_prev den_next : ℝ} {c : ℤ}
    (hx : castZA zx = d • x) (hy : castZA zy = den_prev • y)
    (hcheck : zx.U4 zy = zx'.smul c) (hc_ne : (c : ℝ) ≠ 0)
    (hscale : (c : ℝ) * den_next = 4 * d * d * den_prev) :
    castZA zx' = den_next • quadraticMap x y := by
  have hL : castZA (zx.U4 zy) = (c : ℝ) • castZA zx' := by rw [hcheck, castZA_smul]
  have hcoeff : 4 * d ^ 2 * den_prev = (c : ℝ) * den_next := by
    calc 4 * d ^ 2 * den_prev = 4 * d * d * den_prev := by ring
    _ = (c : ℝ) * den_next := hscale.symm
  have hR : castZA (zx.U4 zy) = (c : ℝ) • (den_next • quadraticMap x y) := by
    rw [castZA_U4, hx, hy, quadraticMap_smul_left, quadraticMap_smul_right, smul_smul, smul_smul,
      hcoeff, ← smul_smul]
  exact smul_right_injective Albert hc_ne (hL.symm.trans hR)

private theorem tp2_eq {x y : Albert} {zx zy : ZA} {s1 s2 : ℝ} {val : ℤ}
    (hx : castZA zx = s1 • x) (hy : castZA zy = s2 • y)
    (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0)
    (hcheck : zx.tp2 zy = val) :
    tracePairing x y = (val : ℝ) / (2 * s1 * s2) := by
  have h1 : ((val : ℤ) : ℝ) = (2 * s1 * s2) * tracePairing x y := by
    rw [← hcheck, castZA_tp2, hx, hy]
    unfold tracePairing
    rw [jordanMul_smul_left, jordanMul_smul_right, albertTrace_smul, albertTrace_smul]
    ring
  have hden : 2 * s1 * s2 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hs1) hs2
  field_simp [hden]
  linarith

private theorem tp2_eq_scaled (u : ZO) (F : Fin 5 → Albert)
    (hF : ∀ i, castZA (qPentadScaled u i) = (atomScale i : ℝ) • F i)
    (i : Fin 5) {y : Albert} {zy : ZA} {val : ℤ}
    (hy : castZA zy = (648 : ℝ) • y)
    (hcheck : (qPentadScaled u i).tp2 zy = val) :
    tracePairing (F i) y = (val : ℝ) / (2 * (atomScale i : ℝ) * 648) :=
  tp2_eq (hF i) hy (by fin_cases i <;> simp [atomScale]) (by norm_num) hcheck

private def compl4 (F : Fin 5 → Albert) (a b c d : Fin 5) (x : Albert) : Albert :=
  quadraticMap (albertUnit - F d) (quadraticMap (albertUnit - F c)
    (quadraticMap (albertUnit - F b) (quadraticMap (albertUnit - F a) x)))

private theorem compl4_X_cast (u : ZO) (F : Fin 5 → Albert)
    (hF : ∀ i, castZA (qPentadScaled u i) = (atomScale i : ℝ) • F i) :
    castZA stX_4 = (648 : ℝ) • compl4 F 2 1 3 2 (F 0) := by
  obtain ⟨hs0, hs1, hs2, hs3⟩ := stX_steps u
  have h0 : castZA stX_0 = (1 : ℝ) • F 0 := by
    rw [stX_init_eq u]; simpa [atomScale] using hF 0
  have h1 : castZA stX_1 = (9 : ℝ) • quadraticMap (albertUnit - F 2) (F 0) :=
    stepU4_eq (castZA_zCompl u F hF 2) h0 hs0 (by norm_num) (by norm_num [atomScale])
  have h2 : castZA stX_2 = (36 : ℝ) •
      quadraticMap (albertUnit - F 1) (quadraticMap (albertUnit - F 2) (F 0)) :=
    stepU4_eq (castZA_zCompl u F hF 1) h1 hs1 (by norm_num) (by norm_num [atomScale])
  have h3 : castZA stX_3 = (72 : ℝ) •
      quadraticMap (albertUnit - F 3)
        (quadraticMap (albertUnit - F 1) (quadraticMap (albertUnit - F 2) (F 0))) :=
    stepU4_eq (castZA_zCompl u F hF 3) h2 hs2 (by norm_num) (by norm_num [atomScale])
  exact stepU4_eq (castZA_zCompl u F hF 2) h3 hs3 (by norm_num) (by norm_num [atomScale])

private theorem compl4_R_cast (u : ZO) (F : Fin 5 → Albert)
    (hF : ∀ i, castZA (qPentadScaled u i) = (atomScale i : ℝ) • F i)
    {s0 s1 s2 s3 s4 : ZA} (hinit : s0 = qPentadScaled u 4)
    (hs : (zCompl u 2).U4 s0 = s1.smul 4 ∧ (zCompl u 3).U4 s1 = s2.smul 8 ∧
      (zCompl u 1).U4 s2 = s3.smul 8 ∧ (zCompl u 2).U4 s3 = s4.smul 4) :
    castZA s4 = (648 : ℝ) • compl4 F 2 3 1 2 (F 4) := by
  have h0 : castZA s0 = (2 : ℝ) • F 4 := by
    rw [hinit]; simpa [atomScale] using hF 4
  have h1 : castZA s1 = (18 : ℝ) • quadraticMap (albertUnit - F 2) (F 4) :=
    stepU4_eq (castZA_zCompl u F hF 2) h0 hs.1 (by norm_num) (by norm_num [atomScale])
  have h2 : castZA s2 = (36 : ℝ) •
      quadraticMap (albertUnit - F 3) (quadraticMap (albertUnit - F 2) (F 4)) :=
    stepU4_eq (castZA_zCompl u F hF 3) h1 hs.2.1 (by norm_num) (by norm_num [atomScale])
  have h3 : castZA s3 = (72 : ℝ) •
      quadraticMap (albertUnit - F 1)
        (quadraticMap (albertUnit - F 3) (quadraticMap (albertUnit - F 2) (F 4))) :=
    stepU4_eq (castZA_zCompl u F hF 1) h2 hs.2.2.1 (by norm_num) (by norm_num [atomScale])
  exact stepU4_eq (castZA_zCompl u F hF 2) h3 hs.2.2.2 (by norm_num) (by norm_num [atomScale])

private theorem compl4_Y_cast (u : ZO) (F : Fin 5 → Albert)
    (hF : ∀ i, castZA (qPentadScaled u i) = (atomScale i : ℝ) • F i)
    {s0 s1 s2 s3 s4 : ZA} (hinit : s0 = qPentadScaled u 4)
    (hs : (zCompl u 2).U4 s0 = s1.smul 4 ∧ (zCompl u 0).U4 s1 = s2.smul 4 ∧
      (zCompl u 1).U4 s2 = s3.smul 4 ∧ (zCompl u 2).U4 s3 = s4.smul 4) :
    castZA s4 = (648 : ℝ) • compl4 F 2 0 1 2 (F 4) := by
  have h0 : castZA s0 = (2 : ℝ) • F 4 := by
    rw [hinit]; simpa [atomScale] using hF 4
  have h1 : castZA s1 = (18 : ℝ) • quadraticMap (albertUnit - F 2) (F 4) :=
    stepU4_eq (castZA_zCompl u F hF 2) h0 hs.1 (by norm_num) (by norm_num [atomScale])
  have h2 : castZA s2 = (18 : ℝ) •
      quadraticMap (albertUnit - F 0) (quadraticMap (albertUnit - F 2) (F 4)) :=
    stepU4_eq (castZA_zCompl u F hF 0) h1 hs.2.1 (by norm_num) (by norm_num [atomScale])
  have h3 : castZA s3 = (72 : ℝ) •
      quadraticMap (albertUnit - F 1)
        (quadraticMap (albertUnit - F 0) (quadraticMap (albertUnit - F 2) (F 4))) :=
    stepU4_eq (castZA_zCompl u F hF 1) h2 hs.2.2.1 (by norm_num) (by norm_num [atomScale])
  exact stepU4_eq (castZA_zCompl u F hF 2) h3 hs.2.2.2 (by norm_num) (by norm_num [atomScale])

/-- Ten-letter square separating word `(X, yes 4, X^rev, yes 0)` of core appendix `app:cert`. -/
def pentadSepWord10 : Word (Fin 5) :=
  [(2, false), (1, false), (3, false), (2, false), (4, true),
   (2, false), (3, false), (1, false), (2, false), (0, true)]

/-- Eleven-letter separating word `(yes 0, pentadSepWord10)` from `e/3`. -/
def pentadSepWord11 : Word (Fin 5) := (0, true) :: pentadSepWord10

/-- Second ten-letter separating word `(X, yes 4, no 2, no 0, no 1, no 2, yes 3)`. -/
def pentadAltSepWord10 : Word (Fin 5) :=
  [(2, false), (1, false), (3, false), (2, false), (4, true),
   (2, false), (0, false), (1, false), (2, false), (3, true)]

/-- Second eleven-letter separating word `(yes 0, pentadAltSepWord10)` from `e/3`. -/
def pentadAltSepWord11 : Word (Fin 5) := (0, true) :: pentadAltSepWord10

theorem pentadSepWord10_length : pentadSepWord10.length = 10 := rfl
theorem pentadSepWord11_length : pentadSepWord11.length = 11 := rfl
theorem pentadAltSepWord10_length : pentadAltSepWord10.length = 10 := rfl
theorem pentadAltSepWord11_length : pentadAltSepWord11.length = 11 := rfl

private theorem compl4_smul (F : Fin 5 → Albert) (a b c d : Fin 5) (r : ℝ) (x : Albert) :
    compl4 F a b c d (r • x) = r • compl4 F a b c d x := by
  simp [compl4, quadraticMap_smul_right]

private theorem nativeWordProbability_sep10 (F : Fin 5 → Albert) (hF : ∀ i, IsAtom (F i)) :
    nativeWordProbability F (F 0) pentadSepWord10 =
      tracePairing (F 4) (compl4 F 2 1 3 2 (F 0)) *
        tracePairing (F 0) (compl4 F 2 3 1 2 (F 4)) := by
  simp only [nativeWordProbability, pentadSepWord10, nativeBranchState, List.foldl_cons,
    List.foldl_nil, nativeOutcome, Bool.false_eq_true, ↓reduceIte]
  change albertTrace (quadraticMap (F 0) (compl4 F 2 3 1 2
    (quadraticMap (F 4) (compl4 F 2 1 3 2 (F 0))))) = _
  rw [quadraticMap_atom (F 4) _ (hF 4), compl4_smul, quadraticMap_smul_right,
    quadraticMap_atom (F 0) _ (hF 0), albertTrace_smul, albertTrace_smul, (hF 0).2]
  ring

private theorem nativeWordProbability_altSep10 (F : Fin 5 → Albert) (hF : ∀ i, IsAtom (F i)) :
    nativeWordProbability F (F 0) pentadAltSepWord10 =
      tracePairing (F 4) (compl4 F 2 1 3 2 (F 0)) *
        tracePairing (F 3) (compl4 F 2 0 1 2 (F 4)) := by
  simp only [nativeWordProbability, pentadAltSepWord10, nativeBranchState, List.foldl_cons,
    List.foldl_nil, nativeOutcome, Bool.false_eq_true, ↓reduceIte]
  change albertTrace (quadraticMap (F 3) (compl4 F 2 0 1 2
    (quadraticMap (F 4) (compl4 F 2 1 3 2 (F 0))))) = _
  rw [quadraticMap_atom (F 4) _ (hF 4), compl4_smul, quadraticMap_smul_right,
    quadraticMap_atom (F 3) _ (hF 3), albertTrace_smul, albertTrace_smul, (hF 3).2]
  ring

private theorem quadraticMap_atom_unit {p : Albert} (hp : IsAtom p) :
    quadraticMap p albertUnit = p := by
  unfold quadraticMap
  rw [two_nsmul, jordanMul_albertUnit_right, hp.1, jordanMul_albertUnit_right]
  abel

private theorem nativeBranchState_smul (F : Fin 5 → Albert) (c : ℝ) (ρ : Albert)
    (w : Word (Fin 5)) :
    nativeBranchState F (c • ρ) w = c • nativeBranchState F ρ w := by
  induction w generalizing ρ with
  | nil => rfl
  | cons a w ih =>
    simp only [nativeBranchState, List.foldl_cons, quadraticMap_smul_right]
    exact ih _

private theorem nativeBranchState_cons (F : Fin 5 → Albert) (ρ : Albert) (a : Outcome (Fin 5))
    (w : Word (Fin 5)) :
    nativeBranchState F ρ (a :: w) = nativeBranchState F (quadraticMap (nativeOutcome F a) ρ) w :=
  rfl

private theorem nativeWordProbability_e3_yes0 (F : Fin 5 → Albert) (hF : IsAtom (F 0))
    (w : Word (Fin 5)) :
    nativeWordProbability F ((1 / 3 : ℝ) • albertUnit) ((0, true) :: w) =
      (1 / 3 : ℝ) * nativeWordProbability F (F 0) w := by
  rw [nativeWordProbability, nativeBranchState_cons,
    show nativeOutcome F (0, true) = F 0 from rfl,
    quadraticMap_smul_right, quadraticMap_atom_unit hF, nativeBranchState_smul, albertTrace_smul]
  rfl

theorem pentadSepWord10_values :
    nativeWordProbability pentadF (pentadF 0) pentadSepWord10 = 1225 / 419904 ∧
    nativeWordProbability pentadFPlus (pentadFPlus 0) pentadSepWord10 = 2809 / 419904 ∧
    nativeWordProbability pentadFMinus (pentadFMinus 0) pentadSepWord10 = 289 / 419904 ∧
    ((1 / 2 : ℝ) * nativeWordProbability pentadFPlus (pentadFPlus 0) pentadSepWord10 +
      (1 / 2 : ℝ) * nativeWordProbability pentadFMinus (pentadFMinus 0) pentadSepWord10 -
      nativeWordProbability pentadF (pentadF 0) pentadSepWord10 = 1 / 1296) := by
  rw [nativeWordProbability_sep10 pentadF pentadF_isAtom,
    nativeWordProbability_sep10 pentadFPlus pentadFPlus_isAtom,
    nativeWordProbability_sep10 pentadFMinus pentadFMinus_isAtom]
  have hL1 : tracePairing (pentadF 4) (compl4 pentadF 2 1 3 2 (pentadF 0)) = 35 / 648 := by
    rw [tp2_eq_scaled ZO.L pentadF pentadF_eq_castScaled 4
      (compl4_X_cast ZO.L pentadF pentadF_eq_castScaled) tp2_checks_L.1]
    norm_num [atomScale]
  have hL2 : tracePairing (pentadF 0) (compl4 pentadF 2 3 1 2 (pentadF 4)) = 35 / 648 := by
    rw [tp2_eq_scaled ZO.L pentadF pentadF_eq_castScaled 0
      (compl4_R_cast ZO.L pentadF pentadF_eq_castScaled stR_L_init_eq stR_L_steps)
      tp2_checks_L.2.1]
    norm_num [atomScale]
  have hK1 : tracePairing (pentadFPlus 4) (compl4 pentadFPlus 2 1 3 2 (pentadFPlus 0)) =
      53 / 648 := by
    rw [tp2_eq_scaled ZO.K pentadFPlus pentadFPlus_eq_castScaled 4
      (compl4_X_cast ZO.K pentadFPlus pentadFPlus_eq_castScaled) tp2_checks_K.1]
    norm_num [atomScale]
  have hK2 : tracePairing (pentadFPlus 0) (compl4 pentadFPlus 2 3 1 2 (pentadFPlus 4)) =
      53 / 648 := by
    rw [tp2_eq_scaled ZO.K pentadFPlus pentadFPlus_eq_castScaled 0
      (compl4_R_cast ZO.K pentadFPlus pentadFPlus_eq_castScaled stR_K_init_eq stR_K_steps)
      tp2_checks_K.2.1]
    norm_num [atomScale]
  have hmK1 : tracePairing (pentadFMinus 4) (compl4 pentadFMinus 2 1 3 2 (pentadFMinus 0)) =
      17 / 648 := by
    rw [tp2_eq_scaled ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled 4
      (compl4_X_cast ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled) tp2_checks_mK.1]
    norm_num [atomScale]
  have hmK2 : tracePairing (pentadFMinus 0) (compl4 pentadFMinus 2 3 1 2 (pentadFMinus 4)) =
      17 / 648 := by
    rw [tp2_eq_scaled ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled 0
      (compl4_R_cast ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled stR_mK_init_eq stR_mK_steps)
      tp2_checks_mK.2.1]
    norm_num [atomScale]
  rw [hL1, hL2, hK1, hK2, hmK1, hmK2]
  norm_num

theorem pentadSepWord11_values :
    nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) pentadSepWord11 = 1225 / 1259712 ∧
    nativeWordProbability pentadFPlus ((1 / 3 : ℝ) • albertUnit) pentadSepWord11 = 2809 / 1259712 ∧
    nativeWordProbability pentadFMinus ((1 / 3 : ℝ) • albertUnit) pentadSepWord11 = 289 / 1259712 ∧
    ((1 / 2 : ℝ) * nativeWordProbability pentadFPlus ((1 / 3 : ℝ) • albertUnit) pentadSepWord11 +
      (1 / 2 : ℝ) * nativeWordProbability pentadFMinus ((1 / 3 : ℝ) • albertUnit) pentadSepWord11 -
      nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) pentadSepWord11 = 1 / 3888) := by
  rw [pentadSepWord11,
    nativeWordProbability_e3_yes0 pentadF (pentadF_isAtom 0),
    nativeWordProbability_e3_yes0 pentadFPlus (pentadFPlus_isAtom 0),
    nativeWordProbability_e3_yes0 pentadFMinus (pentadFMinus_isAtom 0)]
  obtain ⟨hL, hK, hmK, hdiff⟩ := pentadSepWord10_values
  rw [hL, hK, hmK]
  norm_num

theorem pentadAltSepWord10_values :
    nativeWordProbability pentadF (pentadF 0) pentadAltSepWord10 = 1225 / 419904 ∧
    nativeWordProbability pentadFPlus (pentadFPlus 0) pentadAltSepWord10 = 901 / 419904 ∧
    nativeWordProbability pentadFMinus (pentadFMinus 0) pentadAltSepWord10 = 901 / 419904 ∧
    (nativeWordProbability pentadF (pentadF 0) pentadAltSepWord10 -
      ((1 / 2 : ℝ) * nativeWordProbability pentadFPlus (pentadFPlus 0) pentadAltSepWord10 +
        (1 / 2 : ℝ) * nativeWordProbability pentadFMinus (pentadFMinus 0) pentadAltSepWord10) =
      1 / 1296) := by
  rw [nativeWordProbability_altSep10 pentadF pentadF_isAtom,
    nativeWordProbability_altSep10 pentadFPlus pentadFPlus_isAtom,
    nativeWordProbability_altSep10 pentadFMinus pentadFMinus_isAtom]
  have hL1 : tracePairing (pentadF 4) (compl4 pentadF 2 1 3 2 (pentadF 0)) = 35 / 648 := by
    rw [tp2_eq_scaled ZO.L pentadF pentadF_eq_castScaled 4
      (compl4_X_cast ZO.L pentadF pentadF_eq_castScaled) tp2_checks_L.1]
    norm_num [atomScale]
  have hL2 : tracePairing (pentadF 3) (compl4 pentadF 2 0 1 2 (pentadF 4)) = 35 / 648 := by
    rw [tp2_eq_scaled ZO.L pentadF pentadF_eq_castScaled 3
      (compl4_Y_cast ZO.L pentadF pentadF_eq_castScaled stY_L_init_eq stY_L_steps)
      tp2_checks_L.2.2]
    norm_num [atomScale]
  have hK1 : tracePairing (pentadFPlus 4) (compl4 pentadFPlus 2 1 3 2 (pentadFPlus 0)) =
      53 / 648 := by
    rw [tp2_eq_scaled ZO.K pentadFPlus pentadFPlus_eq_castScaled 4
      (compl4_X_cast ZO.K pentadFPlus pentadFPlus_eq_castScaled) tp2_checks_K.1]
    norm_num [atomScale]
  have hK2 : tracePairing (pentadFPlus 3) (compl4 pentadFPlus 2 0 1 2 (pentadFPlus 4)) =
      17 / 648 := by
    rw [tp2_eq_scaled ZO.K pentadFPlus pentadFPlus_eq_castScaled 3
      (compl4_Y_cast ZO.K pentadFPlus pentadFPlus_eq_castScaled stY_K_init_eq stY_K_steps)
      tp2_checks_K.2.2]
    norm_num [atomScale]
  have hmK1 : tracePairing (pentadFMinus 4) (compl4 pentadFMinus 2 1 3 2 (pentadFMinus 0)) =
      17 / 648 := by
    rw [tp2_eq_scaled ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled 4
      (compl4_X_cast ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled) tp2_checks_mK.1]
    norm_num [atomScale]
  have hmK2 : tracePairing (pentadFMinus 3) (compl4 pentadFMinus 2 0 1 2 (pentadFMinus 4)) =
      53 / 648 := by
    rw [tp2_eq_scaled ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled 3
      (compl4_Y_cast ZO.K.neg pentadFMinus pentadFMinus_eq_castScaled stY_mK_init_eq stY_mK_steps)
      tp2_checks_mK.2.2]
    norm_num [atomScale]
  rw [hL1, hL2, hK1, hK2, hmK1, hmK2]
  norm_num

theorem pentadAltSepWord11_values :
    nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) pentadAltSepWord11 = 1225 / 1259712 ∧
    nativeWordProbability pentadFPlus ((1 / 3 : ℝ) • albertUnit) pentadAltSepWord11 =
      901 / 1259712 ∧
    nativeWordProbability pentadFMinus ((1 / 3 : ℝ) • albertUnit) pentadAltSepWord11 =
      901 / 1259712 ∧
    (nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) pentadAltSepWord11 -
      ((1 / 2 : ℝ) * nativeWordProbability pentadFPlus ((1 / 3 : ℝ) • albertUnit) pentadAltSepWord11 +
        (1 / 2 : ℝ) * nativeWordProbability pentadFMinus ((1 / 3 : ℝ) • albertUnit)
          pentadAltSepWord11) =
      1 / 3888) := by
  rw [pentadAltSepWord11,
    nativeWordProbability_e3_yes0 pentadF (pentadF_isAtom 0),
    nativeWordProbability_e3_yes0 pentadFPlus (pentadFPlus_isAtom 0),
    nativeWordProbability_e3_yes0 pentadFMinus (pentadFMinus_isAtom 0)]
  obtain ⟨hL, hK, hmK, hdiff⟩ := pentadAltSepWord10_values
  rw [hL, hK, hmK]
  norm_num

end

end

end AlbertSequential.MatchingModels
