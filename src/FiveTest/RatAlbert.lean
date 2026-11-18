/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PentadArityAndHelly
public import NativeAtomReflections
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # A computable rational mirror of the native Albert algebra

`QQ`, `QO`, `QA` are rational quaternions, octonions and Albert elements with the SAME
formulas as `Defs` (`octonionMul` is the compact Cayley–Dickson product
`(a,b)(c,d) = (ac − d̄b, da + bc̄)`, `jordanMul` is half the symmetrised `octonionMatrixMul`
of `albertMatrix`, slots `(0,1), (0,2), (1,2)`).  The casts `castQ/castO/castA` into the
native real objects are homomorphisms for every operation used (`castA_jmul`, `castA_U`,
`castA_tp`), so exact rational identities checked by `decide` transfer to the native
algebra.  No square root, no `native_decide`. -/

set_option autoImplicit false

@[expose] public section

namespace AlbertSequential.FiveTest

/-! ## Rational quaternions -/

structure QQ where
  re : ℚ
  i : ℚ
  j : ℚ
  k : ℚ
deriving DecidableEq

namespace QQ
def zero : QQ := ⟨0, 0, 0, 0⟩
def add (a b : QQ) : QQ := ⟨a.re + b.re, a.i + b.i, a.j + b.j, a.k + b.k⟩
def neg (a : QQ) : QQ := ⟨-a.re, -a.i, -a.j, -a.k⟩
def smul (r : ℚ) (a : QQ) : QQ := ⟨r * a.re, r * a.i, r * a.j, r * a.k⟩
def star (a : QQ) : QQ := ⟨a.re, -a.i, -a.j, -a.k⟩
def mul (a b : QQ) : QQ :=
  ⟨a.re * b.re - a.i * b.i - a.j * b.j - a.k * b.k,
   a.re * b.i + a.i * b.re + a.j * b.k - a.k * b.j,
   a.re * b.j - a.i * b.k + a.j * b.re + a.k * b.i,
   a.re * b.k + a.i * b.j - a.j * b.i + a.k * b.re⟩
end QQ

/-! ## Rational octonions (pairs, compact Cayley–Dickson) -/

structure QO where
  fst : QQ
  snd : QQ
deriving DecidableEq

namespace QO
def zero : QO := ⟨QQ.zero, QQ.zero⟩
def add (x y : QO) : QO := ⟨x.fst.add y.fst, x.snd.add y.snd⟩
def smul (r : ℚ) (x : QO) : QO := ⟨x.fst.smul r, x.snd.smul r⟩
def mul (x y : QO) : QO :=
  ⟨(x.fst.mul y.fst).add (((y.snd.star).mul x.snd).neg),
   (y.snd.mul x.fst).add (x.snd.mul y.fst.star)⟩
def conj (x : QO) : QO := ⟨x.fst.star, x.snd.neg⟩
def scalar (r : ℚ) : QO := ⟨⟨r, 0, 0, 0⟩, QQ.zero⟩
def real (x : QO) : ℚ := x.fst.re
def normSq (x : QO) : ℚ := (x.mul x.conj).real
def one : QO := scalar 1
def I : QO := ⟨⟨0, 1, 0, 0⟩, QQ.zero⟩
def J : QO := ⟨⟨0, 0, 1, 0⟩, QQ.zero⟩
def L : QO := ⟨QQ.zero, ⟨1, 0, 0, 0⟩⟩
end QO

/-! ## Rational Albert elements: three diagonal entries and slots (0,1), (0,2), (1,2) -/

structure QA where
  d0 : ℚ
  d1 : ℚ
  d2 : ℚ
  o0 : QO
  o1 : QO
  o2 : QO
deriving DecidableEq

namespace QA
def zero : QA := ⟨0, 0, 0, QO.zero, QO.zero, QO.zero⟩
def add (x y : QA) : QA := ⟨x.d0 + y.d0, x.d1 + y.d1, x.d2 + y.d2, x.o0.add y.o0, x.o1.add y.o1, x.o2.add y.o2⟩
def smul (r : ℚ) (x : QA) : QA := ⟨r * x.d0, r * x.d1, r * x.d2, x.o0.smul r, x.o1.smul r, x.o2.smul r⟩
def sub (x y : QA) : QA := x.add (y.smul (-1))
def unit : QA := ⟨1, 1, 1, QO.zero, QO.zero, QO.zero⟩
def diag0 : QA := ⟨1, 0, 0, QO.zero, QO.zero, QO.zero⟩

/-- `albertMatrix` over `ℚ`. -/
def mat (x : QA) (i j : Fin 3) : QO :=
  match i.val, j.val with
  | 0, 0 => QO.scalar x.d0
  | 1, 1 => QO.scalar x.d1
  | 2, 2 => QO.scalar x.d2
  | 0, 1 => x.o0
  | 0, 2 => x.o1
  | 1, 2 => x.o2
  | 1, 0 => x.o0.conj
  | 2, 0 => x.o1.conj
  | 2, 1 => x.o2.conj
  | _, _ => QO.zero

/-- `octonionMatrixMul` over `ℚ`, the three-term sum written out. -/
def mmul (a b : Fin 3 → Fin 3 → QO) (i j : Fin 3) : QO :=
  ((a i 0).mul (b 0 j)).add (((a i 1).mul (b 1 j)).add (((a i 2).mul (b 2 j)).add QO.zero))

def coords (m : Fin 3 → Fin 3 → QO) : QA :=
  ⟨(m 0 0).real, (m 1 1).real, (m 2 2).real, m 0 1, m 0 2, m 1 2⟩

/-- The Jordan product over `ℚ` (same formula as `jordanMul`). -/
def jmul (x y : QA) : QA :=
  (coords (fun i j => (mmul (mat x) (mat y) i j).add (mmul (mat y) (mat x) i j))).smul (1 / 2)

def tr (x : QA) : ℚ := x.d0 + x.d1 + x.d2
def tp (x y : QA) : ℚ := tr (jmul x y)
/-- `quadraticMap` over `ℚ`. -/
def U (x y : QA) : QA := ((jmul x (jmul x y)).add (jmul x (jmul x y))).sub (jmul (jmul x x) y)

/-- `octDyad` over `ℚ`. -/
def dyad (v0 v1 v2 : QO) : QA :=
  ⟨v0.normSq, v1.normSq, v2.normSq, v0.mul v1.conj, v0.mul v2.conj, v1.mul v2.conj⟩
end QA

/-! ## Casts into the native objects -/

noncomputable section

def castQ (a : QQ) : Quaternion ℝ := ⟨(a.re : ℝ), (a.i : ℝ), (a.j : ℝ), (a.k : ℝ)⟩
def castO (x : QO) : Octonion := (castQ x.fst, castQ x.snd)
def castA (x : QA) : Albert := (![(x.d0 : ℝ), (x.d1 : ℝ), (x.d2 : ℝ)], ![castO x.o0, castO x.o1, castO x.o2])

theorem castQ_zero : castQ QQ.zero = 0 := by
  apply Quaternion.ext <;> simp [castQ, QQ.zero]
theorem castQ_add (a b : QQ) : castQ (a.add b) = castQ a + castQ b := by
  apply Quaternion.ext <;> simp [castQ, QQ.add]
theorem castQ_neg (a : QQ) : castQ a.neg = - castQ a := by
  apply Quaternion.ext <;> simp [castQ, QQ.neg]
theorem castQ_smul (r : ℚ) (a : QQ) : castQ (a.smul r) = (r : ℝ) • castQ a := by
  apply Quaternion.ext <;> simp [castQ, QQ.smul]
theorem castQ_star (a : QQ) : castQ a.star = star (castQ a) := by
  apply Quaternion.ext <;> simp [castQ, QQ.star]
theorem castQ_mul (a b : QQ) : castQ (a.mul b) = castQ a * castQ b := by
  apply Quaternion.ext <;> simp [castQ, QQ.mul] <;> ring

theorem castO_zero : castO QO.zero = 0 := by
  simp only [castO, QO.zero, castQ_zero]; rfl
theorem castO_add (x y : QO) : castO (x.add y) = castO x + castO y := by
  simp only [castO, QO.add, castQ_add]; rfl
theorem castO_smul (r : ℚ) (x : QO) : castO (x.smul r) = (r : ℝ) • castO x := by
  simp only [castO, QO.smul, castQ_smul]; rfl
theorem castO_mul (x y : QO) : castO (x.mul y) = octonionMul (castO x) (castO y) := by
  simp only [castO, QO.mul, castQ_add, castQ_neg, castQ_mul, castQ_star, octonionMul]
  rw [sub_eq_add_neg]
theorem castO_conj (x : QO) : castO x.conj = octonionConj (castO x) := by
  simp only [castO, QO.conj, castQ_star, castQ_neg, octonionConj] <;> rfl
theorem castO_scalar (r : ℚ) : castO (QO.scalar r) = octonionScalar (r : ℝ) := by
  simp only [castO, QO.scalar, castQ_zero, octonionScalar]
  congr 1
  apply Quaternion.ext <;> simp [castQ]
theorem castO_real (x : QO) : ((x.real : ℚ) : ℝ) = octonionReal (castO x) := by
  simp [QO.real, octonionReal, castO, castQ]
theorem castO_normSq (x : QO) : ((x.normSq : ℚ) : ℝ) = octNormSq (castO x) := by
  rw [QO.normSq, castO_real, castO_mul, castO_conj]; rfl
theorem castO_one : castO QO.one = octOne := by
  rw [QO.one, castO_scalar]; simp [octOne]
theorem castO_I : castO QO.I = octI := by
  simp only [castO, QO.I, castQ_zero, octI]; congr 1; apply Quaternion.ext <;> simp [castQ]
theorem castO_J : castO QO.J = octJ := by
  simp only [castO, QO.J, castQ_zero, octJ]; congr 1; apply Quaternion.ext <;> simp [castQ]
theorem castO_L : castO QO.L = octL := by
  simp only [castO, QO.L, castQ_zero, octL]; congr 1; apply Quaternion.ext <;> simp [castQ]

@[simp] theorem castA_d0 (x : QA) : (castA x).1 0 = (x.d0 : ℝ) := rfl
@[simp] theorem castA_d1 (x : QA) : (castA x).1 1 = (x.d1 : ℝ) := rfl
@[simp] theorem castA_d2 (x : QA) : (castA x).1 2 = (x.d2 : ℝ) := rfl
@[simp] theorem castA_o0 (x : QA) : (castA x).2 0 = castO x.o0 := rfl
@[simp] theorem castA_o1 (x : QA) : (castA x).2 1 = castO x.o1 := rfl
@[simp] theorem castA_o2 (x : QA) : (castA x).2 2 = castO x.o2 := rfl

theorem albert_smul_fst' (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
theorem albert_smul_snd' (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl
theorem albert_mk_fst (d : Fin 3 → ℝ) (o : Fin 3 → Octonion) (j : Fin 3) :
    ((d, o) : Albert).1 j = d j := rfl
theorem albert_mk_snd (d : Fin 3 → ℝ) (o : Fin 3 → Octonion) (k : Fin 3) :
    ((d, o) : Albert).2 k = o k := rfl

theorem albert_ext' {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

theorem castA_add (x y : QA) : castA (x.add y) = castA x + castA y := by
  apply albert_ext' <;> simp [castA, QA.add, castO_add] <;> rfl
theorem castA_smul (r : ℚ) (x : QA) : castA (x.smul r) = (r : ℝ) • castA x := by
  apply albert_ext' <;> simp [castA, QA.smul, castO_smul] <;> rfl
theorem castA_sub (x y : QA) : castA (x.sub y) = castA x - castA y := by
  rw [QA.sub, castA_add, castA_smul, sub_eq_add_neg]; simp
theorem castA_unit : castA QA.unit = albertUnit := by
  apply albert_ext' <;> simp [castA, QA.unit, castO_zero] <;> rfl
theorem castA_diag0 : castA QA.diag0 = diagAtom 0 := by
  apply albert_ext' <;> simp [castA, QA.diag0, castO_zero, diagAtom]

theorem castA_mat (x : QA) (i j : Fin 3) : castO (x.mat i j) = albertMatrix (castA x) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [QA.mat, albertMatrix, castO_scalar, castO_conj, castA]

theorem castA_mmul (a b : Fin 3 → Fin 3 → QO) (i j : Fin 3) :
    castO (QA.mmul a b i j) =
      octonionMatrixMul (fun i j => castO (a i j)) (fun i j => castO (b i j)) i j := by
  simp only [QA.mmul, castO_add, castO_mul, castO_zero, octonionMatrixMul, Fin.sum_univ_three,
    add_zero, add_assoc]

theorem jordanMul_fst' (X Y : Albert) (i : Fin 3) : (jordanMul X Y).1 i =
    (1 / 2 : ℝ) * octonionReal (octonionMatrixMul (albertMatrix X) (albertMatrix Y) i i +
      octonionMatrixMul (albertMatrix Y) (albertMatrix X) i i) := rfl
theorem jordanMul_snd0' (X Y : Albert) : (jordanMul X Y).2 0 =
    (1 / 2 : ℝ) • (octonionMatrixMul (albertMatrix X) (albertMatrix Y) 0 1 +
      octonionMatrixMul (albertMatrix Y) (albertMatrix X) 0 1) := rfl
theorem jordanMul_snd1' (X Y : Albert) : (jordanMul X Y).2 1 =
    (1 / 2 : ℝ) • (octonionMatrixMul (albertMatrix X) (albertMatrix Y) 0 2 +
      octonionMatrixMul (albertMatrix Y) (albertMatrix X) 0 2) := rfl
theorem jordanMul_snd2' (X Y : Albert) : (jordanMul X Y).2 2 =
    (1 / 2 : ℝ) • (octonionMatrixMul (albertMatrix X) (albertMatrix Y) 1 2 +
      octonionMatrixMul (albertMatrix Y) (albertMatrix X) 1 2) := rfl

theorem castA_jmul (x y : QA) : castA (x.jmul y) = jordanMul (castA x) (castA y) := by
  have hm : ∀ (u v : QA) (i j : Fin 3), castO (QA.mmul u.mat v.mat i j) =
      octonionMatrixMul (albertMatrix (castA u)) (albertMatrix (castA v)) i j := by
    intro u v i j
    rw [castA_mmul]
    have e : (fun i j => castO (u.mat i j)) = albertMatrix (castA u) := by
      funext i j; exact castA_mat u i j
    have e' : (fun i j => castO (v.mat i j)) = albertMatrix (castA v) := by
      funext i j; exact castA_mat v i j
    rw [e, e']
  rw [QA.jmul, castA_smul]
  apply albert_ext' <;>
    simp only [jordanMul_fst', jordanMul_snd0', jordanMul_snd1', jordanMul_snd2'] <;>
    simp only [castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, QA.coords, castO_add,
      hm, castO_real, albert_smul_fst', albert_smul_snd', albert_mk_fst, albert_mk_snd,
      Pi.add_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, castO_smul] <;> norm_num

theorem castA_tr (x : QA) : ((x.tr : ℚ) : ℝ) = albertTrace (castA x) := by
  simp [QA.tr, albertTrace, Fin.sum_univ_three, castA]

theorem castA_tp (x y : QA) : ((x.tp y : ℚ) : ℝ) = tracePairing (castA x) (castA y) := by
  rw [QA.tp, castA_tr, castA_jmul]; rfl

theorem castA_U (x y : QA) : castA (x.U y) = quadraticMap (castA x) (castA y) := by
  rw [QA.U, castA_sub, castA_add, castA_jmul, castA_jmul, castA_jmul, castA_jmul, quadraticMap,
    two_nsmul]

theorem castA_dyad (v0 v1 v2 : QO) :
    castA (QA.dyad v0 v1 v2) = octDyad ![castO v0, castO v1, castO v2] := by
  apply albert_ext' <;>
    simp [castA, QA.dyad, octDyad, castO_normSq, castO_mul, castO_conj]

end

end AlbertSequential.FiveTest
