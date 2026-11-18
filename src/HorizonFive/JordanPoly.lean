/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Statement
public import NativeJordanIdentity
public import NativeJordanQuadratic
public import UnitalJordanProduct

/-! # Jordan polynomials and their two evaluations (companion `app:cert:h5`, "Two evaluations")

The paper's `𝒫` is the free unital Jordan algebra on four letters.  Every statement of companion `app:cert:h5`
about `𝒫` is of the form "for all `F` (of bounded degree) with `σ̂(F) = 0`, `ν̂(F) = 0`", and both
`σ̂` and `ν̂` are unital Jordan homomorphisms.  They factor through any presentation of `𝒫` by
Jordan expressions, so this file works with the *syntax* `JPoly X` of Jordan expressions (unit, letters,
sums, real multiples, products) and evaluate it in any unital commutative bilinear product
(`JTarget`).  No quotient by the Jordan identity is needed for these statements: a polynomial of
degree at most `d` is represented by an expression of syntactic degree at most `d`, and both
evaluations respect every Jordan relation because their targets are Jordan algebras.

Degree conventions: `deg` is the syntactic total degree (sum over products, maximum over sums);
`LinearIn j F` is the syntactic form of "degree one in `x_j`" (every monomial has exactly one
`x_j`); `FreeOf j F` means `x_j` does not occur.

Targets: the special value `σ̂` sends `x_i` to the symmetry `r_i = 2P_i - 1` of the universal
projection algebra with the symmetrized product `X ∘ Y = (XY + YX)/2` (this is `ℝ[G]^+`); the
Albert value `ν̂` sends `x_i` to the native symmetry `s_i = 2p_i - e` with `jordanMul`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-- Jordan expressions on letters `X`. -/
inductive JPoly (X : Type) : Type where
  | one : JPoly X
  | var : X → JPoly X
  | add : JPoly X → JPoly X → JPoly X
  | smul : ℝ → JPoly X → JPoly X
  | mul : JPoly X → JPoly X → JPoly X

namespace JPoly
variable {X : Type}

/-- Syntactic total degree. -/
def deg : JPoly X → ℕ
  | one => 0
  | var _ => 1
  | add a b => max a.deg b.deg
  | smul _ a => a.deg
  | mul a b => a.deg + b.deg

/-- `x_j` does not occur. -/
inductive FreeOf (j : X) : JPoly X → Prop
  | one : FreeOf j one
  | var (x : X) : x ≠ j → FreeOf j (var x)
  | add (a b : JPoly X) : FreeOf j a → FreeOf j b → FreeOf j (add a b)
  | smul (r : ℝ) (a : JPoly X) : FreeOf j a → FreeOf j (smul r a)
  | mul (a b : JPoly X) : FreeOf j a → FreeOf j b → FreeOf j (mul a b)

/-- Degree one in `x_j`: every monomial contains exactly one `x_j`. -/
inductive LinearIn (j : X) : JPoly X → Prop
  | var : LinearIn j (var j)
  | add (a b : JPoly X) : LinearIn j a → LinearIn j b → LinearIn j (add a b)
  | smul (r : ℝ) (a : JPoly X) : LinearIn j a → LinearIn j (smul r a)
  | mulLeft (a b : JPoly X) : LinearIn j a → FreeOf j b → LinearIn j (mul a b)
  | mulRight (a b : JPoly X) : FreeOf j a → LinearIn j b → LinearIn j (mul a b)

/-- `U_a b = 2 a ∘ (a ∘ b) - (a ∘ a) ∘ b`. -/
def U (a b : JPoly X) : JPoly X :=
  add (smul 2 (mul a (mul a b))) (smul (-1) (mul (mul a a) b))

/-- `A_a b = 2 a ∘ b` (the paper's `A_s = 2L_s`). -/
def A (a b : JPoly X) : JPoly X := smul 2 (mul a b)

/-- The Jordan triple product `{a,b,c} = (a∘b)∘c + (c∘b)∘a - (a∘c)∘b`. -/
def triple (a b c : JPoly X) : JPoly X :=
  add (add (mul (mul a b) c) (mul (mul c b) a)) (smul (-1) (mul (mul a c) b))

end JPoly

/-- A real vector space with a bilinear commutative product and a two-sided unit.  Both
evaluation targets are of this kind (and are Jordan algebras; the Jordan identity is not needed
for evaluation). -/
structure JTarget (E : Type*) [AddCommGroup E] [Module ℝ E] where
  mul : E → E → E
  one : E
  add_mul : ∀ x y z, mul (x + y) z = mul x z + mul y z
  smul_mul : ∀ (r : ℝ) x y, mul (r • x) y = r • mul x y
  comm : ∀ x y, mul x y = mul y x
  one_mul : ∀ x, mul one x = x

namespace JTarget
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E)

theorem mul_add (x y z : E) : T.mul x (y + z) = T.mul x y + T.mul x z := by
  rw [T.comm, T.add_mul, T.comm y, T.comm z]

theorem mul_smul (r : ℝ) (x y : E) : T.mul x (r • y) = r • T.mul x y := by
  rw [T.comm, T.smul_mul, T.comm]

theorem mul_one (x : E) : T.mul x T.one = x := by rw [T.comm, T.one_mul]

theorem mul_neg (x y : E) : T.mul x (-y) = - T.mul x y := by
  rw [← neg_one_smul ℝ y, T.mul_smul, neg_one_smul]

theorem neg_mul (x y : E) : T.mul (-x) y = - T.mul x y := by
  rw [T.comm, T.mul_neg, T.comm]

theorem mul_sub (x y z : E) : T.mul x (y - z) = T.mul x y - T.mul x z := by
  rw [sub_eq_add_neg, T.mul_add, T.mul_neg, ← sub_eq_add_neg]

theorem sub_mul (x y z : E) : T.mul (x - y) z = T.mul x z - T.mul y z := by
  rw [T.comm, T.mul_sub, T.comm z, T.comm z]

/-- Evaluation of Jordan expressions. -/
def eval {X : Type} (v : X → E) : JPoly X → E
  | .one => T.one
  | .var x => v x
  | .add a b => eval v a + eval v b
  | .smul r a => r • eval v a
  | .mul a b => T.mul (eval v a) (eval v b)

/-- The quadratic operator `U_a b` in the target. -/
def Uop (a b : E) : E := (2 : ℝ) • T.mul a (T.mul a b) - T.mul (T.mul a a) b

/-- The operator `A_s = 2 L_s`. -/
def Aop (s b : E) : E := (2 : ℝ) • T.mul s b

theorem eval_U {X : Type} (v : X → E) (a b : JPoly X) :
    T.eval v (JPoly.U a b) = T.Uop (T.eval v a) (T.eval v b) := by
  simp only [JPoly.U, eval, Uop]
  module

theorem eval_A {X : Type} (v : X → E) (a b : JPoly X) :
    T.eval v (JPoly.A a b) = T.Aop (T.eval v a) (T.eval v b) := rfl

/-- Polarizing `U` at the unit: for a symmetry `s` (`s ∘ s = e`),
`U_{(e+s)/2} = (id + A_s + C_s)/4` and `U_{(e-s)/2} = (id - A_s + C_s)/4`, with `C_s = U_s`. -/
theorem Uop_half_plus (s y : E) (hs : T.mul s s = T.one) :
    T.Uop ((1 / 2 : ℝ) • (T.one + s)) y =
      (1 / 4 : ℝ) • (y + T.Aop s y + T.Uop s y) := by
  simp only [Uop, Aop, T.smul_mul, T.mul_smul, T.add_mul, T.mul_add, T.one_mul, T.mul_one, hs]
  module

theorem Uop_half_minus (s y : E) (hs : T.mul s s = T.one) :
    T.Uop ((1 / 2 : ℝ) • (T.one + (-1 : ℝ) • s)) y =
      (1 / 4 : ℝ) • (y - T.Aop s y + T.Uop s y) := by
  simp only [Uop, Aop, T.smul_mul, T.mul_smul, T.add_mul, T.mul_add, T.one_mul, T.mul_one, hs]
  module

end JTarget

/-! ## The two targets -/

/-- `ℝ[G]^+`-style target: any real algebra with `X ∘ Y = (XY + YX)/2`. -/
def specialTarget (R : Type*) [Ring R] [Algebra ℝ R] : JTarget R where
  mul x y := (1 / 2 : ℝ) • (x * y + y * x)
  one := 1
  add_mul x y z := by simp only [add_mul, _root_.mul_add]; module
  smul_mul r x y := by simp only [smul_mul_assoc, mul_smul_comm]; module
  comm x y := by rw [add_comm]
  one_mul x := by simp only [one_mul, _root_.mul_one]; module

theorem specialTarget_mul (R : Type*) [Ring R] [Algebra ℝ R] (x y : R) :
    (specialTarget R).mul x y = (1 / 2 : ℝ) • (x * y + y * x) := rfl

/-- In an associative algebra, `U_a b = a b a`. -/
theorem specialTarget_Uop (R : Type*) [Ring R] [Algebra ℝ R] (a b : R) :
    (specialTarget R).Uop a b = a * b * a := by
  simp only [JTarget.Uop, specialTarget_mul, smul_mul_assoc, mul_smul_comm, _root_.mul_add,
    add_mul, mul_assoc, smul_add, smul_smul]
  module

/-- The native Albert target. -/
def albertTarget : JTarget Albert where
  mul := jordanMul
  one := albertUnit
  add_mul := jordanMul_add_left
  smul_mul := jordanMul_smul_left
  comm := jordanMul_comm
  one_mul := jordanMul_albertUnit_left

theorem albertTarget_Uop (a b : Albert) : albertTarget.Uop a b = quadraticMap a b := by
  simp only [JTarget.Uop, albertTarget, quadraticMap, two_smul]

/-- The special symmetries `r_i = 2 P_i - 1` of the universal projection algebra. -/
def specialSymmetry (i : Test) : UniversalProjectionAlgebra 4 :=
  (2 : ℝ) • universalTests i - 1

/-- The native symmetries `s_i = 2 p_i - e`. -/
def nativeSymmetry (p : Test → Albert) (i : Test) : Albert := (2 : ℝ) • p i - albertUnit

/-- The special value `σ̂ : 𝒫 → ℝ[G]^+`, `x_i ↦ r_i`. -/
def specialEval (F : JPoly Test) : UniversalProjectionAlgebra 4 :=
  (specialTarget (UniversalProjectionAlgebra 4)).eval specialSymmetry F

/-- The Albert value `ν̂ : 𝒫 → J`, `x_i ↦ s_i = 2 p_i - e`. -/
def albertEval (p : Test → Albert) (F : JPoly Test) : Albert :=
  albertTarget.eval (nativeSymmetry p) F

theorem specialSymmetry_sq (i : Test) :
    (specialTarget (UniversalProjectionAlgebra 4)).mul (specialSymmetry i) (specialSymmetry i) =
      1 := by
  have hP : universalTests i * universalTests i = universalTests i :=
    universalProjection_idempotent i
  simp only [specialTarget_mul, specialSymmetry, sub_mul, _root_.mul_sub, smul_mul_assoc,
    mul_smul_comm, hP, one_mul, _root_.mul_one, smul_sub, smul_smul]
  module

theorem nativeSymmetry_sq (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (i : Test) : jordanMul (nativeSymmetry p i) (nativeSymmetry p i) = albertUnit := by
  simp only [nativeSymmetry, jordanMul_sub_left, jordanMul_sub_right, jordanMul_smul_left,
    jordanMul_smul_right, jordanMul_albertUnit_left, jordanMul_albertUnit_right, hp]
  module

/-! ## Linear combinations of Jordan expressions -/

/-- A finite real combination of Jordan expressions (paper: "a combination of symbols"). -/
abbrev JComb := JPoly Test →₀ ℝ

/-- Linear extension of the special value. -/
def specialEvalC (F : JComb) : UniversalProjectionAlgebra 4 :=
  F.sum fun G a => a • specialEval G

/-- Linear extension of the Albert value. -/
def albertEvalC (p : Test → Albert) (F : JComb) : Albert :=
  F.sum fun G a => a • albertEval p G

end AlbertSequential.HorizonFive
