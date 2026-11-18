/- SPDX-License-Identifier: Apache-2.0 -/
module

public import AppF.Shestakov
public import FrameSlotNormalizers
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

/-! # Exact computable mirrors of the native Albert algebra

`EQ K`, `EO K`, `EA K` are quaternions, octonions and Albert elements over an exact scalar type
`K` (here `ℚ` and `ℚ(√2)`), with the SAME formulas as `Defs` (`octonionMul` is the compact
Cayley–Dickson product `(a,b)(c,d) = (ac − d̄b, da + bc̄)`, `jordanMul` is half the symmetrised
`octonionMatrixMul` of `albertMatrix`, slots `(0,1), (0,2), (1,2)`).  The casts into the native
real objects are homomorphisms for every operation used (`castA_add`, `castA_sub`,
`castA_jmul`, `castA_tp`, `castA_cubicNorm`), so identities checked by kernel evaluation
(`decide +kernel`; no `native_decide`) transfer to the native algebra.
-/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- Computable exact scalar operations. -/
class ExactOps (K : Type) where
  add : K → K → K
  mul : K → K → K
  neg : K → K
  zero : K
  half : K

/-- A ring-homomorphic map of the exact scalars into `ℝ`. -/
class ExactScalar (K : Type) extends ExactOps K where
  toR : K → ℝ
  toR_add : ∀ a b, toR (ExactOps.add a b) = toR a + toR b
  toR_mul : ∀ a b, toR (ExactOps.mul a b) = toR a * toR b
  toR_neg : ∀ a, toR (ExactOps.neg a) = - toR a
  toR_zero : toR ExactOps.zero = 0
  toR_half : toR ExactOps.half = 1 / 2

namespace ExactScalar
attribute [simp] toR_add toR_mul toR_neg toR_zero toR_half
end ExactScalar

open ExactScalar

instance ratOps : ExactOps ℚ where
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  zero := 0
  half := 1 / 2

noncomputable instance ratExact : ExactScalar ℚ where
  toR := fun a => (a : ℝ)
  toR_add := by intro a b; show ((a + b : ℚ) : ℝ) = _; push_cast; rfl
  toR_mul := by intro a b; show ((a * b : ℚ) : ℝ) = _; push_cast; rfl
  toR_neg := by intro a; show ((-a : ℚ) : ℝ) = _; push_cast; rfl
  toR_zero := by show ((0 : ℚ) : ℝ) = 0; simp
  toR_half := by show ((1 / 2 : ℚ) : ℝ) = 1 / 2; push_cast; ring

/-- `ℚ(√2)`: the pair `(a, b)` stands for `a + b√2`. -/
structure Q2 where
  a : ℚ
  b : ℚ
deriving DecidableEq

instance q2Ops : ExactOps Q2 where
  add := fun x y => ⟨x.a + y.a, x.b + y.b⟩
  mul := fun x y => ⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩
  neg := fun x => ⟨-x.a, -x.b⟩
  zero := ⟨0, 0⟩
  half := ⟨1 / 2, 0⟩

noncomputable instance q2Exact : ExactScalar Q2 where
  toR := fun x => (x.a : ℝ) + (x.b : ℝ) * Real.sqrt 2
  toR_add := by intro x y; show (((x.a + y.a : ℚ)) : ℝ) + ((x.b + y.b : ℚ) : ℝ) * _ = _; push_cast; ring
  toR_mul := by
    intro x y
    have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    show (((x.a * y.a + 2 * (x.b * y.b) : ℚ)) : ℝ) + ((x.a * y.b + x.b * y.a : ℚ) : ℝ) * _ = _
    push_cast
    linear_combination (-((x.b : ℝ) * (y.b : ℝ))) * h
  toR_neg := by intro x; show ((-x.a : ℚ) : ℝ) + ((-x.b : ℚ) : ℝ) * _ = _; push_cast; ring
  toR_zero := by show ((0 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * _ = 0; simp
  toR_half := by show ((1 / 2 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * _ = 1 / 2; push_cast; ring

variable {K : Type} [ExactOps K]

/-! ## Quaternions, octonions, Albert elements over `K` -/

structure EQ (K : Type) where
  re : K
  i : K
  j : K
  k : K
deriving DecidableEq

namespace EQ
def zero : EQ K := ⟨ExactOps.zero, ExactOps.zero, ExactOps.zero, ExactOps.zero⟩
def add (x y : EQ K) : EQ K := ⟨ExactOps.add x.re y.re, ExactOps.add x.i y.i,
  ExactOps.add x.j y.j, ExactOps.add x.k y.k⟩
def neg (x : EQ K) : EQ K := ⟨ExactOps.neg x.re, ExactOps.neg x.i, ExactOps.neg x.j,
  ExactOps.neg x.k⟩
def smul (r : K) (x : EQ K) : EQ K := ⟨ExactOps.mul r x.re, ExactOps.mul r x.i,
  ExactOps.mul r x.j, ExactOps.mul r x.k⟩
def star (x : EQ K) : EQ K := ⟨x.re, ExactOps.neg x.i, ExactOps.neg x.j, ExactOps.neg x.k⟩
/-- Hamilton product, written with `add`, `mul`, `neg` only. -/
def mul (x y : EQ K) : EQ K :=
  let ad := (ExactOps.add : K → K → K)
  let ml := (ExactOps.mul : K → K → K)
  let ng := (ExactOps.neg : K → K)
  ⟨ad (ad (ad (ml x.re y.re) (ng (ml x.i y.i))) (ng (ml x.j y.j))) (ng (ml x.k y.k)),
   ad (ad (ad (ml x.re y.i) (ml x.i y.re)) (ml x.j y.k)) (ng (ml x.k y.j)),
   ad (ad (ad (ml x.re y.j) (ng (ml x.i y.k))) (ml x.j y.re)) (ml x.k y.i),
   ad (ad (ad (ml x.re y.k) (ml x.i y.j)) (ng (ml x.j y.i))) (ml x.k y.re)⟩
end EQ

structure EO (K : Type) where
  fst : EQ K
  snd : EQ K
deriving DecidableEq

namespace EO
def zero : EO K := ⟨EQ.zero, EQ.zero⟩
def add (x y : EO K) : EO K := ⟨x.fst.add y.fst, x.snd.add y.snd⟩
def neg (x : EO K) : EO K := ⟨x.fst.neg, x.snd.neg⟩
def smul (r : K) (x : EO K) : EO K := ⟨x.fst.smul r, x.snd.smul r⟩
def mul (x y : EO K) : EO K :=
  ⟨(x.fst.mul y.fst).add ((y.snd.star.mul x.snd).neg), (y.snd.mul x.fst).add (x.snd.mul y.fst.star)⟩
def conj (x : EO K) : EO K := ⟨x.fst.star, x.snd.neg⟩
def scalar (r : K) : EO K := ⟨⟨r, ExactOps.zero, ExactOps.zero, ExactOps.zero⟩, EQ.zero⟩
def real (x : EO K) : K := x.fst.re
def dot (x y : EO K) : K := (x.mul y.conj).real
end EO

structure EA (K : Type) where
  d0 : K
  d1 : K
  d2 : K
  o0 : EO K
  o1 : EO K
  o2 : EO K
deriving DecidableEq

namespace EA
def add (x y : EA K) : EA K := ⟨ExactOps.add x.d0 y.d0, ExactOps.add x.d1 y.d1,
  ExactOps.add x.d2 y.d2, x.o0.add y.o0, x.o1.add y.o1, x.o2.add y.o2⟩
def neg (x : EA K) : EA K := ⟨ExactOps.neg x.d0, ExactOps.neg x.d1, ExactOps.neg x.d2,
  x.o0.neg, x.o1.neg, x.o2.neg⟩
def sub (x y : EA K) : EA K := x.add y.neg
def smul (r : K) (x : EA K) : EA K := ⟨ExactOps.mul r x.d0, ExactOps.mul r x.d1,
  ExactOps.mul r x.d2, x.o0.smul r, x.o1.smul r, x.o2.smul r⟩

/-- `albertMatrix` over `K`. -/
def mat (x : EA K) (i j : Fin 3) : EO K :=
  match i.val, j.val with
  | 0, 0 => EO.scalar x.d0
  | 1, 1 => EO.scalar x.d1
  | 2, 2 => EO.scalar x.d2
  | 0, 1 => x.o0
  | 0, 2 => x.o1
  | 1, 2 => x.o2
  | 1, 0 => x.o0.conj
  | 2, 0 => x.o1.conj
  | 2, 1 => x.o2.conj
  | _, _ => EO.zero

/-- `octonionMatrixMul` over `K`, the three-term sum written out. -/
def mmul (a b : Fin 3 → Fin 3 → EO K) (i j : Fin 3) : EO K :=
  ((a i 0).mul (b 0 j)).add (((a i 1).mul (b 1 j)).add (((a i 2).mul (b 2 j)).add EO.zero))

def coords (m : Fin 3 → Fin 3 → EO K) : EA K :=
  ⟨(m 0 0).real, (m 1 1).real, (m 2 2).real, m 0 1, m 0 2, m 1 2⟩

/-- The Jordan product over `K` (same formula as `jordanMul`). -/
def jmul (x y : EA K) : EA K :=
  (coords (fun i j => (mmul (mat x) (mat y) i j).add (mmul (mat y) (mat x) i j))).smul
    ExactOps.half

def tr (x : EA K) : K := ExactOps.add (ExactOps.add x.d0 x.d1) x.d2
def tp (x y : EA K) : K := tr (jmul x y)

/-- `albertCubicNorm` over `K`. -/
def cubicNorm (x : EA K) : K :=
  let ad := (ExactOps.add : K → K → K)
  let ml := (ExactOps.mul : K → K → K)
  let ng := (ExactOps.neg : K → K)
  ad (ad (ad (ad (ml (ml x.d0 x.d1) x.d2) (ng (ml x.d0 (x.o2.dot x.o2))))
    (ng (ml x.d1 (x.o1.dot x.o1)))) (ng (ml x.d2 (x.o0.dot x.o0))))
    (ad ((x.o0.mul x.o2).dot x.o1) ((x.o0.mul x.o2).dot x.o1))
end EA

/-- The exact operations, and `r = 2x − e` written as `x + x − e`. -/
def eaOps (K : Type) [ExactOps K] : JOps (EA K) := ⟨EA.add, EA.sub, EA.jmul⟩

/-! ## Casts into the native objects -/

noncomputable section

variable {K : Type} [ExactScalar K]

def castQ (x : EQ K) : Quaternion ℝ := ⟨toR x.re, toR x.i, toR x.j, toR x.k⟩
def castO (x : EO K) : Octonion := (castQ x.fst, castQ x.snd)
def castA (x : EA K) : Albert :=
  (![toR x.d0, toR x.d1, toR x.d2], ![castO x.o0, castO x.o1, castO x.o2])

theorem castQ_zero : castQ (EQ.zero : EQ K) = 0 := by
  apply Quaternion.ext <;> simp [castQ, EQ.zero]
theorem castQ_add (a b : EQ K) : castQ (a.add b) = castQ a + castQ b := by
  apply Quaternion.ext <;> simp [castQ, EQ.add]
theorem castQ_neg (a : EQ K) : castQ a.neg = - castQ a := by
  apply Quaternion.ext <;> simp [castQ, EQ.neg]
theorem castQ_smul (r : K) (a : EQ K) : castQ (a.smul r) = toR r • castQ a := by
  apply Quaternion.ext <;> simp [castQ, EQ.smul]
theorem castQ_star (a : EQ K) : castQ a.star = star (castQ a) := by
  apply Quaternion.ext <;> simp [castQ, EQ.star]
theorem castQ_mul (a b : EQ K) : castQ (a.mul b) = castQ a * castQ b := by
  apply Quaternion.ext <;>
    simp [castQ, EQ.mul, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

theorem castO_zero : castO (EO.zero : EO K) = 0 := by
  simp only [castO, EO.zero, castQ_zero]; rfl
theorem castO_add (x y : EO K) : castO (x.add y) = castO x + castO y := by
  simp only [castO, EO.add, castQ_add]; rfl
theorem castO_neg (x : EO K) : castO x.neg = - castO x := by
  simp only [castO, EO.neg, castQ_neg]; rfl
theorem castO_smul (r : K) (x : EO K) : castO (x.smul r) = toR r • castO x := by
  simp only [castO, EO.smul, castQ_smul]; rfl
theorem castO_mul (x y : EO K) : castO (x.mul y) = octonionMul (castO x) (castO y) := by
  simp only [castO, EO.mul, castQ_add, castQ_neg, castQ_mul, castQ_star, octonionMul]
  rw [sub_eq_add_neg]
theorem castO_conj (x : EO K) : castO x.conj = octonionConj (castO x) := by
  simp only [castO, EO.conj, castQ_star, castQ_neg, octonionConj]; rfl
theorem castO_scalar (r : K) : castO (EO.scalar r) = octonionScalar (toR r) := by
  simp only [castO, EO.scalar, castQ_zero, octonionScalar]
  congr 1
  apply Quaternion.ext <;> simp [castQ]
theorem castO_real (x : EO K) : toR x.real = octonionReal (castO x) := by
  simp [EO.real, octonionReal, castO, castQ]
theorem castO_dot (x y : EO K) : toR (x.dot y) = octDot (castO x) (castO y) := by
  rw [EO.dot, castO_real, castO_mul, castO_conj]; rfl

@[simp] theorem castA_d0 (x : EA K) : (castA x).1 0 = toR x.d0 := rfl
@[simp] theorem castA_d1 (x : EA K) : (castA x).1 1 = toR x.d1 := rfl
@[simp] theorem castA_d2 (x : EA K) : (castA x).1 2 = toR x.d2 := rfl
@[simp] theorem castA_o0 (x : EA K) : (castA x).2 0 = castO x.o0 := rfl
@[simp] theorem castA_o1 (x : EA K) : (castA x).2 1 = castO x.o1 := rfl
@[simp] theorem castA_o2 (x : EA K) : (castA x).2 2 = castO x.o2 := rfl

theorem albert_smul_fst' (r : ℝ) (x : Albert) (j : Fin 3) : (r • x).1 j = r * x.1 j := rfl
theorem albert_smul_snd' (r : ℝ) (x : Albert) (k : Fin 3) : (r • x).2 k = r • x.2 k := rfl
theorem albert_add_fst' (x y : Albert) (j : Fin 3) : (x + y).1 j = x.1 j + y.1 j := rfl
theorem albert_add_snd' (x y : Albert) (k : Fin 3) : (x + y).2 k = x.2 k + y.2 k := rfl
theorem albert_sub_fst' (x y : Albert) (j : Fin 3) : (x - y).1 j = x.1 j - y.1 j := rfl
theorem albert_sub_snd' (x y : Albert) (k : Fin 3) : (x - y).2 k = x.2 k - y.2 k := rfl
theorem albert_mk_fst (d : Fin 3 → ℝ) (o : Fin 3 → Octonion) (j : Fin 3) :
    ((d, o) : Albert).1 j = d j := rfl
theorem albert_mk_snd (d : Fin 3 → ℝ) (o : Fin 3 → Octonion) (k : Fin 3) :
    ((d, o) : Albert).2 k = o k := rfl

theorem albert_ext' {x y : Albert}
    (hd0 : x.1 0 = y.1 0) (hd1 : x.1 1 = y.1 1) (hd2 : x.1 2 = y.1 2)
    (ho0 : x.2 0 = y.2 0) (ho1 : x.2 1 = y.2 1) (ho2 : x.2 2 = y.2 2) : x = y := by
  apply Prod.ext <;> funext k <;> fin_cases k <;> assumption

theorem castA_add (x y : EA K) : castA (x.add y) = castA x + castA y := by
  apply albert_ext' <;>
    simp only [castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, EA.add, castO_add,
      albert_add_fst', albert_add_snd', toR_add]
theorem castA_neg (x : EA K) : castA x.neg = - castA x := by
  apply albert_ext' <;>
    simp only [castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, EA.neg, castO_neg,
      toR_neg] <;> rfl
theorem castA_sub (x y : EA K) : castA (x.sub y) = castA x - castA y := by
  rw [EA.sub, castA_add, castA_neg, sub_eq_add_neg]
theorem castA_smul (r : K) (x : EA K) : castA (x.smul r) = toR r • castA x := by
  apply albert_ext' <;>
    simp only [castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, EA.smul, castO_smul,
      albert_smul_fst', albert_smul_snd', toR_mul]

theorem castA_mat (x : EA K) (i j : Fin 3) : castO (x.mat i j) = albertMatrix (castA x) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [EA.mat, albertMatrix, castO_scalar, castO_conj, castA]

theorem castA_mmul (a b : Fin 3 → Fin 3 → EO K) (i j : Fin 3) :
    castO (EA.mmul a b i j) =
      octonionMatrixMul (fun i j => castO (a i j)) (fun i j => castO (b i j)) i j := by
  simp only [EA.mmul, castO_add, castO_mul, castO_zero, octonionMatrixMul, Fin.sum_univ_three,
    add_zero, add_assoc]

theorem jordanMul_fst' (x y : Albert) (i : Fin 3) : (jordanMul x y).1 i = (1 / 2 : ℝ) *
    octonionReal (octonionMatrixMul (albertMatrix x) (albertMatrix y) i i +
      octonionMatrixMul (albertMatrix y) (albertMatrix x) i i) := rfl
theorem jordanMul_snd0' (x y : Albert) : (jordanMul x y).2 0 = (1 / 2 : ℝ) •
    (octonionMatrixMul (albertMatrix x) (albertMatrix y) 0 1 +
      octonionMatrixMul (albertMatrix y) (albertMatrix x) 0 1) := rfl
theorem jordanMul_snd1' (x y : Albert) : (jordanMul x y).2 1 = (1 / 2 : ℝ) •
    (octonionMatrixMul (albertMatrix x) (albertMatrix y) 0 2 +
      octonionMatrixMul (albertMatrix y) (albertMatrix x) 0 2) := rfl
theorem jordanMul_snd2' (x y : Albert) : (jordanMul x y).2 2 = (1 / 2 : ℝ) •
    (octonionMatrixMul (albertMatrix x) (albertMatrix y) 1 2 +
      octonionMatrixMul (albertMatrix y) (albertMatrix x) 1 2) := rfl

theorem castA_jmul (x y : EA K) : castA (x.jmul y) = jordanMul (castA x) (castA y) := by
  have hm : ∀ (u v : EA K) (i j : Fin 3), castO (EA.mmul u.mat v.mat i j) =
      octonionMatrixMul (albertMatrix (castA u)) (albertMatrix (castA v)) i j := by
    intro u v i j
    rw [castA_mmul]
    have e : (fun i j => castO (u.mat i j)) = albertMatrix (castA u) := by
      funext i j; exact castA_mat u i j
    have e' : (fun i j => castO (v.mat i j)) = albertMatrix (castA v) := by
      funext i j; exact castA_mat v i j
    rw [e, e']
  apply albert_ext' <;>
    simp only [castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, EA.jmul, EA.smul,
      EA.coords, toR_mul, toR_half, castO_smul, castO_add, castO_real, hm, jordanMul_fst',
      jordanMul_snd0', jordanMul_snd1', jordanMul_snd2']

theorem castA_tr (x : EA K) : toR x.tr = albertTrace (castA x) := by
  simp [EA.tr, albertTrace, Fin.sum_univ_three, castA]

theorem castA_tp (x y : EA K) : toR (x.tp y) = tracePairing (castA x) (castA y) := by
  rw [EA.tp, castA_tr, castA_jmul]; rfl

theorem castA_cubicNorm (x : EA K) : toR x.cubicNorm = albertCubicNorm (castA x) := by
  simp only [EA.cubicNorm, toR_add, toR_mul, toR_neg, castO_dot, castO_mul, albertCubicNorm,
    castA_d0, castA_d1, castA_d2, castA_o0, castA_o1, castA_o2, octNormSq]
  ring

/-- Transport of the polarised Glennie value from the exact mirror. -/
theorem castA_glennieF (a b c d : EA K) :
    castA (glennieF (eaOps K) a b c d) =
      nativeGlennieF (castA a) (castA b) (castA c) (castA d) :=
  map_glennieF (o := eaOps K) (o' := nativeOps) castA castA_add castA_sub castA_jmul a b c d

end

end AlbertSequential.AppF
