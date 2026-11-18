/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeAlbertLaws
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-! # Shestakov's form of Glennie's identity (`thm:glennie`, definitions)

Paper (core appendix `sec:tet`, "Glennie's identity at four atoms"): for `x, y` in a Jordan algebra
`D_{x,y} = 4[L_x,L_y]`, `U_{[x,y]} = 4U_{x∘y} − 2(U_xU_y + U_yU_x)`,
`D^C_{x,y} = D³ + 3·D·U_{[x,y]}` (McCrimmon's operator order: `U` applied first, then `D`),
`ψ(x,y,z) = D^C_{x,y}(z²) − 2 z∘D^C_{x,y}(z)` and
`F(a,b,c,d) = [s²t²u²] ψ(sa+tb, sa+uc, d)`.

Lean encoding.  Everything is written over a bare record `JOps J` of three operations
(addition, subtraction, Jordan product); integer multiples are repeated additions
(`two`, `three`, `four`).  No algebraic law is assumed by the definitions, so the same
definitions evaluate in the native Albert algebra, in a special algebra `A⁺`, in the
second-order jet algebra and in the exact rational mirrors used for the instances.

`F` is defined through the multilinear polarisation `Phi` of `D^C`
(`Phi x x x y y y = D^C_{x,y}`, lemma `Phi_diag`): `Phi` is multilinear in its six
arguments whenever the product is bilinear, so the coefficient of `s²t²u²` in
`Phi(X,X,X,Y,Y,Y)` with `X = sa+tb`, `Y = sa+uc` is the sum over the 3·3 placements of one
`a` among the `x`-slots (the others `b`) and one `a` among the `y`-slots (the others `c`):
this is exactly `glennieF`.  (Multilinear expansion is not itself formalised here; it is the
reading of the definition.)

Proved here: the native operators are the paper's (`nativeD_eq`, `native_Upol_self`,
`native_Ubr_diag`, `native_psi_eq`); `ψ` vanishes identically in every special Jordan algebra
`A⁺`, `A` an associative real algebra, unital or not (`special_psi_eq_zero`); every map that
preserves the three operations transports `ψ` and `F` (`map_psi`, `map_glennieF`), hence every
Jordan homomorphism from the Albert algebra (or any `JOps` algebra) into `A⁺` kills all values
of `ψ` (`jordanHom_kills_psi`).
-/

@[expose] public section

namespace AlbertSequential.AppF

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- Three operations: addition, subtraction, Jordan product. -/
structure JOps (J : Type*) where
  add : J → J → J
  sub : J → J → J
  mul : J → J → J

section Generic

variable {J : Type*} (o : JOps J)

/-- `2w`, `3w`, `4w` as repeated additions. -/
def two (w : J) : J := o.add w w
def three (w : J) : J := o.add (o.add w w) w
def four (w : J) : J := o.add (o.add w w) (o.add w w)

/-- `D_{x,y} z = 4(x∘(y∘z) − y∘(x∘z))`, i.e. `4[L_x,L_y] z`. -/
def Dop (x y z : J) : J := four o (o.sub (o.mul x (o.mul y z)) (o.mul y (o.mul x z)))

/-- Polarised quadratic representation
`U_{w,w'} z = w∘(w'∘z) + w'∘(w∘z) − (w∘w')∘z`; `U_{w,w} = U_w = 2L_w² − L_{w²}`. -/
def Upol (w w' z : J) : J :=
  o.sub (o.add (o.mul w (o.mul w' z)) (o.mul w' (o.mul w z))) (o.mul (o.mul w w') z)

/-- A multilinear polarisation of `U_{[x,y]} = 4U_{x∘y} − 2(U_xU_y + U_yU_x)`:
`Ubr x x y y = U_{[x,y]}` (`Ubr_diag`). -/
def Ubr (x1 x2 y1 y2 z : J) : J :=
  o.sub (four o (Upol o (o.mul x1 y1) (o.mul x2 y2) z))
    (two o (o.add (Upol o x1 x2 (Upol o y1 y2 z)) (Upol o y1 y2 (Upol o x1 x2 z))))

/-- Multilinear polarisation of `D^C_{x,y} = D³ + 3·D·U_{[x,y]}`. -/
def Phi (x1 x2 x3 y1 y2 y3 z : J) : J :=
  o.add (Dop o x1 y1 (Dop o x2 y2 (Dop o x3 y3 z)))
    (three o (Dop o x1 y1 (Ubr o x2 x3 y2 y3 z)))

/-- `D^C_{x,y} z = D³z + 3·D(U_{[x,y]} z)`. -/
def DC (x y z : J) : J :=
  o.add (Dop o x y (Dop o x y (Dop o x y z))) (three o (Dop o x y (Ubr o x x y y z)))

theorem Phi_diag (x y z : J) : Phi o x x x y y y z = DC o x y z := rfl

/-- Shestakov's element `ψ(x,y,z) = D^C_{x,y}(z²) − 2 z∘D^C_{x,y}(z)`. -/
def psi (x y z : J) : J := o.sub (DC o x y (o.mul z z)) (two o (o.mul z (DC o x y z)))

/-- One placement term `Phi(…)(d²) − 2 d∘Phi(…)(d)` of the polarisation. -/
def glennieTerm (d x1 x2 x3 y1 y2 y3 : J) : J :=
  o.sub (Phi o x1 x2 x3 y1 y2 y3 (o.mul d d)) (two o (o.mul d (Phi o x1 x2 x3 y1 y2 y3 d)))

/-- `F(a,b,c,d) = [s²t²u²] ψ(sa+tb, sa+uc, d)`: the nine placements of one `a` among the
`x`-slots (others `b`) and one `a` among the `y`-slots (others `c`). -/
def glennieF (a b c d : J) : J :=
  o.add (o.add (o.add (glennieTerm o d a b b a c c) (glennieTerm o d a b b c a c))
      (o.add (glennieTerm o d a b b c c a) (glennieTerm o d b a b a c c)))
    (o.add (o.add (glennieTerm o d b a b c a c) (glennieTerm o d b a b c c a))
      (o.add (o.add (glennieTerm o d b b a a c c) (glennieTerm o d b b a c a c))
        (glennieTerm o d b b a c c a)))

end Generic

/-! ## Transport along operation-preserving maps -/

section Transport

variable {J J' : Type*} {o : JOps J} {o' : JOps J'} (φ : J → J')
  (hadd : ∀ x y, φ (o.add x y) = o'.add (φ x) (φ y))
  (hsub : ∀ x y, φ (o.sub x y) = o'.sub (φ x) (φ y))
  (hmul : ∀ x y, φ (o.mul x y) = o'.mul (φ x) (φ y))
include hadd hsub hmul

theorem map_Phi (x1 x2 x3 y1 y2 y3 z : J) :
    φ (Phi o x1 x2 x3 y1 y2 y3 z) = Phi o' (φ x1) (φ x2) (φ x3) (φ y1) (φ y2) (φ y3) (φ z) := by
  simp only [Phi, Dop, Ubr, Upol, two, three, four, hadd, hsub, hmul]

theorem map_DC (x y z : J) : φ (DC o x y z) = DC o' (φ x) (φ y) (φ z) := by
  simp only [DC, Dop, Ubr, Upol, two, three, four, hadd, hsub, hmul]

theorem map_psi (x y z : J) : φ (psi o x y z) = psi o' (φ x) (φ y) (φ z) := by
  simp only [psi, DC, Dop, Ubr, Upol, two, three, four, hadd, hsub, hmul]

theorem map_glennieF (a b c d : J) :
    φ (glennieF o a b c d) = glennieF o' (φ a) (φ b) (φ c) (φ d) := by
  simp only [glennieF, glennieTerm, Phi, Dop, Ubr, Upol, two, three, four, hadd, hsub, hmul]

end Transport

/-! ## The native Albert algebra -/

noncomputable section Native

/-- The native operations of `J = H₃(𝕆)`. -/
def nativeOps : JOps Albert := ⟨(· + ·), (· - ·), jordanMul⟩

/-- Native Shestakov element and native polarised Glennie value. -/
def nativePsi (x y z : Albert) : Albert := psi nativeOps x y z
def nativeGlennieF (a b c d : Albert) : Albert := glennieF nativeOps a b c d

/-- The symmetry `r = 2p − e` of an element. -/
def symmetryOf (p : Albert) : Albert := (2 : ℝ) • p - albertUnit

theorem nativeD_eq (x y z : Albert) :
    Dop nativeOps x y z =
      (4 : ℝ) • (jordanMul x (jordanMul y z) - jordanMul y (jordanMul x z)) := by
  simp only [Dop, four, nativeOps]
  module

theorem native_Upol_self (w z : Albert) : Upol nativeOps w w z = quadraticMap w z := by
  simp only [Upol, nativeOps, quadraticMap, two_nsmul]

theorem native_Ubr_diag (x y z : Albert) :
    Ubr nativeOps x x y y z =
      (4 : ℝ) • quadraticMap (jordanMul x y) z -
        (2 : ℝ) • (quadraticMap x (quadraticMap y z) + quadraticMap y (quadraticMap x z)) := by
  simp only [Ubr, four, two, native_Upol_self]
  simp only [nativeOps]
  module

theorem native_DC_eq (x y z : Albert) :
    DC nativeOps x y z =
      Dop nativeOps x y (Dop nativeOps x y (Dop nativeOps x y z)) +
        (3 : ℝ) • Dop nativeOps x y (Ubr nativeOps x x y y z) := by
  simp only [DC, three]
  simp only [nativeOps]
  module

theorem native_psi_eq (x y z : Albert) :
    nativePsi x y z =
      DC nativeOps x y (jordanMul z z) - (2 : ℝ) • jordanMul z (DC nativeOps x y z) := by
  simp only [nativePsi, psi, two]
  simp only [nativeOps]
  module

end Native

/-! ## Special Jordan algebras: `ψ` vanishes -/

section Special

variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

/-- `A⁺`: the Jordan product `x∘y = ½(xy + yx)` of an associative real algebra. -/
noncomputable def specialOps (A : Type*) [NonUnitalRing A] [Module ℝ A] : JOps A :=
  ⟨(· + ·), (· - ·), fun x y => (1 / 2 : ℝ) • (x * y + y * x)⟩

theorem special_mul_def (x y : A) : (specialOps A).mul x y = (1 / 2 : ℝ) • (x * y + y * x) := rfl

theorem special_D (x y z : A) :
    Dop (specialOps A) x y z = (x * y - y * x) * z - z * (x * y - y * x) := by
  simp only [Dop, four, specialOps, smul_add, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    smul_smul, mul_sub, sub_mul, mul_assoc]
  module

theorem special_Upol (w w' z : A) :
    Upol (specialOps A) w w' z = (1 / 2 : ℝ) • (w * z * w' + w' * z * w) := by
  simp only [Upol, specialOps, smul_add, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    smul_smul, mul_assoc]
  module

theorem special_Ubr_diag (x y z : A) :
    Ubr (specialOps A) x x y y z = (x * y - y * x) * z * (x * y - y * x) := by
  simp only [Ubr, four, two, special_Upol]
  simp only [specialOps, smul_add, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    smul_smul, mul_sub, sub_mul, mul_assoc]
  module

theorem special_DC (x y z : A) :
    DC (specialOps A) x y z =
      (x * y - y * x) * (x * y - y * x) * (x * y - y * x) * z -
        z * ((x * y - y * x) * (x * y - y * x) * (x * y - y * x)) := by
  simp only [DC, three, special_D, special_Ubr_diag]
  simp only [specialOps]
  generalize x * y - y * x = q
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  abel

theorem special_mul_self (z : A) : (specialOps A).mul z z = z * z := by
  simp only [specialOps]
  rw [← two_smul ℝ (z * z), smul_smul]
  norm_num

theorem special_two_mul (z w : A) : two (specialOps A) ((specialOps A).mul z w) = z * w + w * z := by
  simp only [two, specialOps]
  rw [← add_smul]
  norm_num

/-- Shestakov's element vanishes identically in every special Jordan algebra `A⁺`
(`A` associative, unital or not). -/
theorem special_psi_eq_zero (x y z : A) : psi (specialOps A) x y z = 0 := by
  have h := special_two_mul z (DC (specialOps A) x y z)
  simp only [psi]
  rw [h, special_mul_self, special_DC, special_DC]
  simp only [specialOps]
  generalize (x * y - y * x) * (x * y - y * x) * (x * y - y * x) = c
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  abel

/-- Every map preserving addition, subtraction and the Jordan product into `A⁺` kills every
value of `ψ`.  In particular every real-linear Jordan homomorphism `η : J → A` (unital or
not) does. -/
theorem opsHom_kills_psi {J : Type*} {o : JOps J} (φ : J → A)
    (hadd : ∀ x y, φ (o.add x y) = φ x + φ y) (hsub : ∀ x y, φ (o.sub x y) = φ x - φ y)
    (hmul : ∀ x y, φ (o.mul x y) = (1 / 2 : ℝ) • (φ x * φ y + φ y * φ x)) (x y z : J) :
    φ (psi o x y z) = 0 := by
  rw [map_psi (o' := specialOps A) φ hadd hsub hmul]
  exact special_psi_eq_zero _ _ _

theorem jordanHom_kills_psi (η : Albert →ₗ[ℝ] A) (hη : IsJordanHom η) (x y z : Albert) :
    η (nativePsi x y z) = 0 :=
  opsHom_kills_psi (o := nativeOps) η (fun a b => map_add η a b) (fun a b => map_sub η a b)
    (fun a b => hη a b) x y z

end Special

end AlbertSequential.AppF
