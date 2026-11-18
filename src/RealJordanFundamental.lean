/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE (the Apache-2.0 text, identical to Physlib's LICENSE).
Authors: Tom Ole Diem

Adapted from Physlib, https://github.com/leanprover-community/physlib, commit
08a6c1b5b8e6db340547142c3f7047635128c786, file
PhyslibAlpha/ProbabilisticTheory/JordanOrderUnit/Quadratic/Fundamental.lean.
Adapted declarations: cyclic_mulLeft_commutator, innerDerivation_add_left, innerDerivation_mul,
innerDerivation_comm, tripleOperator, triple_eq_V_apply, innerDerivation_sub_right,
innerDerivation_mul_left, tripleOperator_comm, tripleOperator_quadRep_step,
V_quadRep_eq_quadRep_triple, and quadRep_fundamental_apply, quadRep_fundamental (renamed here
quadraticRepresentation_fundamental_apply, quadraticRepresentation_fundamental).
Modifications: only the cyclic polarization and the derivation and triple arguments are kept; the
ambient class is weakened to NonUnitalNonAssocCommRing; imports, namespace, the operator
definitions (RealJordanOperators.lean) and the two endpoint names differ; the proof bodies are
otherwise unchanged. No Physlib import remains. Licence: Apache-2.0. See THIRD_PARTY_NOTICES.
Thanks to Tom Ole Diem and the Physlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to
Robert Hooke, 1676.
-/
module

public import RealJordanOperators

/-! Fundamental quadratic identity derived from the ordinary Jordan identity,
via inner derivations and the Jordan triple identity. Not an assumed axiom. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.RealJordan
variable {E : Type*} [NonUnitalNonAssocCommRing E]
  [Module ℝ E] [SMulCommClass ℝ E E] [IsCommJordan E]
local notation "L" => leftMultiplication
local notation "U" => quadraticRepresentation
omit [SMulCommClass ℝ E E] in
lemma cyclic_mulLeft_commutator (a b c x : E) :
    (a * ((b * c) * x) - (b * c) * (a * x)) +
        (b * ((c * a) * x) - (c * a) * (b * x)) +
          (c * ((a * b) * x) - (a * b) * (c * x)) = 0 := by
  have h := two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c
  have hx := DFunLike.congr_fun h x
  have hx' : (2 : ℕ) •
      ((a * ((b * c) * x) - (b * c) * (a * x)) +
        (b * ((c * a) * x) - (c * a) * (b * x)) +
          (c * ((a * b) * x) - (a * b) * (c * x))) = 0 := by
    exact hx
  have htwo : (2 : ℝ) •
      ((a * ((b * c) * x) - (b * c) * (a * x)) +
        (b * ((c * a) * x) - (c * a) * (b * x)) +
          (c * ((a * b) * x) - (a * b) * (c * x))) = 0 := by
    simpa [two_smul] using hx'
  calc
    _ = (1 / 2 : ℝ) • ((2 : ℝ) •
        ((a * ((b * c) * x) - (b * c) * (a * x)) +
          (b * ((c * a) * x) - (c * a) * (b * x)) +
            (c * ((a * b) * x) - (a * b) * (c * x)))) := by module
    _ = 0 := by rw [htwo]; module

omit [IsCommJordan E] in
lemma innerDerivation_add_left (a b c : E) :
    innerDerivation (a + b) c = innerDerivation a c + innerDerivation b c := by
  ext x
  simp only [innerDerivation_apply, LinearMap.add_apply]
  simp only [add_mul, mul_add]
  module

lemma innerDerivation_mul (a b x y : E) :
    innerDerivation a b (x * y) = (innerDerivation a b x) * y + x * (innerDerivation a b y) := by
  have h1 := cyclic_mulLeft_commutator a x y b
  have h2 := cyclic_mulLeft_commutator b x y a
  simp only [innerDerivation_apply, sub_mul, mul_sub]
  simp only [mul_comm] at h1 h2 ⊢
  linear_combination (norm := module) h1 - h2

lemma innerDerivation_comm (a b c d : E) :
    (innerDerivation a b).comp (innerDerivation c d) -
        (innerDerivation c d).comp (innerDerivation a b) =
      innerDerivation (innerDerivation a b c) d + innerDerivation c (innerDerivation a b d) := by
  ext z
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply]
  rw [innerDerivation_apply c d z, map_sub (innerDerivation a b),
    innerDerivation_apply c d (innerDerivation a b z)]
  rw [innerDerivation_mul a b c (d * z), innerDerivation_mul a b d (c * z),
    innerDerivation_mul a b d z, innerDerivation_mul a b c z]
  rw [innerDerivation_apply (innerDerivation a b c) d z,
    innerDerivation_apply c (innerDerivation a b d) z]
  simp only [mul_add]
  module

def tripleOperator (a b : E) : E →ₗ[ℝ] E := L (a * b) + innerDerivation a b

local notation "V" => tripleOperator

omit [IsCommJordan E] in
lemma triple_eq_V_apply (a b x : E) : V a b x = jordanTriple a b x := by
  simp only [tripleOperator, LinearMap.add_apply, innerDerivation_apply, mulLeft_apply,
    jordanTriple]
  rw [mul_comm x (b * a), mul_comm b a, mul_comm (a * x) b]
  abel

omit [IsCommJordan E] in
lemma innerDerivation_sub_right (a b c : E) :
    innerDerivation a (b - c) = innerDerivation a b - innerDerivation a c := by
  ext x
  simp only [innerDerivation_apply, LinearMap.sub_apply]
  simp only [sub_mul, mul_sub]
  module

lemma innerDerivation_mul_left (a b q e : E) :
    innerDerivation (a * b) q e = innerDerivation a (b * q) e + innerDerivation b (a * q) e := by
  have h := cyclic_mulLeft_commutator a b q e
  rw [mul_comm q a] at h
  simp only [innerDerivation_apply]
  linear_combination (norm := module) -h

lemma tripleOperator_comm (a b c d : E) :
    (V a b).comp (V c d) - (V c d).comp (V a b) =
      V (jordanTriple a b c) d - V c (jordanTriple b a d) := by
  ext e

  simp only [
    tripleOperator,
    LinearMap.sub_apply,
    LinearMap.comp_apply,
    LinearMap.add_apply,
    mulLeft_apply,
    map_add
  ]

  /-
  Expand the two inner derivations acting on products.
  -/
  have e1 :
      innerDerivation a b ((c * d) * e) =
        (innerDerivation a b c) * d * e +
          c * (innerDerivation a b d) * e +
            (c * d) * (innerDerivation a b e) := by
    rw [innerDerivation_mul a b (c * d) e]
    rw [innerDerivation_mul a b c d]
    rw [add_mul]

  have e2 :
      innerDerivation c d ((a * b) * e) =
        (innerDerivation c d a) * b * e +
          a * (innerDerivation c d b) * e +
            (a * b) * (innerDerivation c d e) := by
    rw [innerDerivation_mul c d (a * b) e]
    rw [innerDerivation_mul c d a b]
    rw [add_mul]

  /-
  Commutator of inner derivations.
  -/
  have e3 :
      innerDerivation a b (innerDerivation c d e) -
          innerDerivation c d (innerDerivation a b e) =
        innerDerivation (innerDerivation a b c) d e +
          innerDerivation c (innerDerivation a b d) e := by
    have h := DFunLike.congr_fun (innerDerivation_comm a b c d) e
    simpa only [
      LinearMap.sub_apply,
      LinearMap.comp_apply,
      LinearMap.add_apply
    ] using h

  /-
  Jordan cyclic identity for the product pair.
  -/
  have e4 :
      innerDerivation (a * b) (c * d) e =
        innerDerivation ((a * b) * c) d e -
          innerDerivation c ((a * b) * d) e := by
    have h := innerDerivation_mul_left (a * b) c d e
    rw [h]
    module

  /-
  Express the triple products in L_{ab} + D_{a,b} form.
  -/
  have hJ1 :
      jordanTriple a b c =
        (a * b) * c + innerDerivation a b c := by
    rw [← triple_eq_V_apply]
    rfl

  have hJ2 :
      jordanTriple b a d =
        (a * b) * d - innerDerivation a b d := by
    rw [← triple_eq_V_apply]
    simp only [
      tripleOperator,
      LinearMap.add_apply,
      mulLeft_apply
    ]
    rw [
      mul_comm b a,
      innerDerivation_swap b a,
      LinearMap.neg_apply
    ]
    module

  rw [hJ1, hJ2]

  simp only [
    add_mul,
    sub_mul,
    mul_sub,
    innerDerivation_add_left,
    LinearMap.add_apply
  ]

  /-
  Convert the raw left-multiplication commutator into an inner derivation.
  -/
  have e4' :
      a * b * (c * d * e) - c * d * (a * b * e) =
        innerDerivation (a * b * c) d e -
          innerDerivation c (a * b * d) e := by
    rw [← innerDerivation_apply, e4]

  /-
  Remaining product/derivation relation.
  -/
  have hQ :
      c * (a * b * d) * e - a * b * c * d * e -
          (innerDerivation c d a * b * e +
            a * (innerDerivation c d b) * e) = 0 := by
    have step1 :
        c * (a * b * d) * e =
          c * (d * (a * b)) * e := by
      rw [mul_comm (a * b) d]

    have step2 :
        a * b * c * d * e =
          d * (c * (a * b)) * e := by
      rw [
        mul_comm d (c * (a * b)),
        mul_comm c (a * b)
      ]

    have step3 :
        innerDerivation c d a * b * e +
            a * (innerDerivation c d b) * e =
          c * (d * (a * b)) * e -
            d * (c * (a * b)) * e := by
      have h6 :
          (innerDerivation c d a * b +
              a * innerDerivation c d b) * e =
            innerDerivation c d (a * b) * e := by
        rw [innerDerivation_mul c d a b]

      rw [add_mul] at h6
      rwa [
        innerDerivation_apply c d (a * b),
        sub_mul
      ] at h6

    rw [step1, step2, step3]
    module

  /-
  Expand the product derivations first.
  -/
  rw [e1, e2]

  simp only [
    innerDerivation_sub_right,
    LinearMap.sub_apply
  ]

  have e3' :
      innerDerivation a b (innerDerivation c d e) =
        innerDerivation c d (innerDerivation a b e) +
          innerDerivation (innerDerivation a b c) d e +
          innerDerivation c (innerDerivation a b d) e := by
    have h :=
      (sub_eq_iff_eq_add).mp e3
    calc
      innerDerivation a b (innerDerivation c d e) =
          (innerDerivation (innerDerivation a b c) d e +
            innerDerivation c (innerDerivation a b d) e) +
            innerDerivation c d (innerDerivation a b e) := h
      _ =
          innerDerivation c d (innerDerivation a b e) +
            innerDerivation (innerDerivation a b c) d e +
            innerDerivation c (innerDerivation a b d) e := by
        abel

  have e4'' :
      a * b * (c * d * e) =
        c * d * (a * b * e) +
          innerDerivation (a * b * c) d e -
          innerDerivation c (a * b * d) e := by
    have h :=
      (sub_eq_iff_eq_add).mp e4'
    calc
      a * b * (c * d * e) =
          (innerDerivation (a * b * c) d e -
            innerDerivation c (a * b * d) e) +
            c * d * (a * b * e) := h
      _ =
          c * d * (a * b * e) +
            innerDerivation (a * b * c) d e -
            innerDerivation c (a * b * d) e := by
        abel

  have hQ' :
      c * (a * b * d) * e =
        a * b * c * d * e +
          innerDerivation c d a * b * e +
          a * innerDerivation c d b * e := by
    have h :
        c * (a * b * d) * e - a * b * c * d * e =
          innerDerivation c d a * b * e +
            a * innerDerivation c d b * e := by
      have h0 := hQ
      -- hQ is `(X - Y) - Z = 0`, hence `X - Y = Z`.
      exact sub_eq_zero.mp h0

    have h' := (sub_eq_iff_eq_add).mp h
    calc
      c * (a * b * d) * e =
          (innerDerivation c d a * b * e +
            a * innerDerivation c d b * e) +
            a * b * c * d * e := h'
      _ =
          a * b * c * d * e +
            innerDerivation c d a * b * e +
            a * innerDerivation c d b * e := by
        abel

  rw [e3', e4'', hQ']

  abel

lemma tripleOperator_quadRep_step (x y z : E) :
    V x y (U x z) =
      (2 : ℝ) • V x z (U x y) - U x (jordanTriple y x z) := by
  have h := DFunLike.congr_fun (tripleOperator_comm x y x z) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
  have hVxzx : V x z x = U x z := (triple_eq_V_apply x z x).trans (jordanTriple_diag x z)
  have hVxyx : V x y x = U x y := (triple_eq_V_apply x y x).trans (jordanTriple_diag x y)
  have hdiagxyx : jordanTriple x y x = U x y := jordanTriple_diag x y
  rw [hVxzx, hVxyx, hdiagxyx] at h
  have hswap : V (U x y) z x = V x z (U x y) := by
    rw [triple_eq_V_apply, triple_eq_V_apply, jordanTriple_outer_comm]
  have hdiag2 : V x (jordanTriple y x z) x = U x (jordanTriple y x z) :=
    (triple_eq_V_apply x (jordanTriple y x z) x).trans
      (jordanTriple_diag x (jordanTriple y x z))
  rw [hswap, hdiag2] at h
  linear_combination (norm := module) h

lemma V_quadRep_eq_quadRep_triple (x y z : E) :
    V x y (U x z) = U x (jordanTriple y x z) := by
  have h1 := tripleOperator_quadRep_step x y z
  have h2 := tripleOperator_quadRep_step x z y
  have hswap :
      jordanTriple z x y = jordanTriple y x z := by
    rw [jordanTriple_outer_comm]
  rw [hswap] at h2
  linear_combination (norm := module)
    (-1 / 3 : ℝ) • h1 + (-2 / 3 : ℝ) • h2

lemma quadraticRepresentation_fundamental_apply (x y z : E) :
    U (U x y) z = U x (U y (U x z)) := by

  /-
  Step 1.

  Specialize the triple-operator commutator at
      (a,b,c,d,e) = (z,x,y,x,y).

  This gives an identity from which we solve for `U y (U x z)`.
  -/
  have hinner0 :=
    DFunLike.congr_fun (tripleOperator_comm z x y x) y

  simp only [
    LinearMap.sub_apply,
    LinearMap.comp_apply
  ] at hinner0

  have hxzx :
      jordanTriple x z x = U x z :=
    jordanTriple_diag x z

  have hright :
      V (jordanTriple y x z) x y =
        V y x (jordanTriple y x z) := by
    rw [
      triple_eq_V_apply,
      triple_eq_V_apply,
      jordanTriple_outer_comm
    ]

  have hdiag :
      V y (U x z) y = U y (U x z) :=
    (triple_eq_V_apply y (U x z) y).trans
      (jordanTriple_diag y (U x z))

  have houter :
      jordanTriple z x y = jordanTriple y x z := by
    exact jordanTriple_outer_comm z x y

  have hyxy :
      V y x y = U y x :=
    (triple_eq_V_apply y x y).trans
      (jordanTriple_diag y x)

  have hzxy :
      V z x y = jordanTriple y x z := by
    rw [
      triple_eq_V_apply,
      jordanTriple_outer_comm
    ]

  rw [
    houter,
    hxzx,
    hright,
    hdiag,
    hyxy,
    hzxy
  ] at hinner0

  /-
  Now:

      hinner0 :
        V z x (U y x) - V y x {y,x,z}
          =
        V y x {y,x,z} - U y (U x z).

  Solve additively for `U y (U x z)`.
  -/
  have hinner :
      U y (U x z) =
        V y x (jordanTriple y x z) +
          V y x (jordanTriple y x z) -
          V z x (U y x) := by
    calc
      U y (U x z) =
          V y x (jordanTriple y x z) -
            (V y x (jordanTriple y x z) -
              U y (U x z)) := by
        abel
      _ =
          V y x (jordanTriple y x z) -
            (V z x (U y x) -
              V y x (jordanTriple y x z)) := by
        rw [← hinner0]
      _ =
          V y x (jordanTriple y x z) +
            V y x (jordanTriple y x z) -
            V z x (U y x) := by
        abel

  /-
  Apply `U x` to the preceding identity.
  -/
  have hinnerUx0 :=
    congrArg (fun w => U x w) hinner

  have hinnerUx :
      U x (U y (U x z)) =
        U x (V y x (jordanTriple y x z)) +
          U x (V y x (jordanTriple y x z)) -
          U x (V z x (U y x)) := by
    simpa only [
      map_add,
      map_sub
    ] using hinnerUx0

  /-
  Step 2.

  Specialize the triple-operator commutator at
      (a,b,c,d,e) = (x,y,x,z,U_x y).
  -/
  have hmain :=
    DFunLike.congr_fun
      (tripleOperator_comm x y x z)
      (U x y)

  simp only [
    LinearMap.sub_apply,
    LinearMap.comp_apply
  ] at hmain

  have hdiagxy :
      jordanTriple x y x = U x y :=
    jordanTriple_diag x y

  rw [hdiagxy] at hmain

  /-
  Diagonal term:
      V_{U_x y,z}(U_x y) = U_{U_x y} z.
  -/
  have hUU :
      V (U x y) z (U x y) =
        U (U x y) z :=
    (triple_eq_V_apply (U x y) z (U x y)).trans
      (jordanTriple_diag (U x y) z)

  /-
  V_{x,z}(U_x y) = U_x {y,x,z}.
  -/
  have h1 :
      V x z (U x y) =
        U x (jordanTriple y x z) := by
    have h :=
      V_quadRep_eq_quadRep_triple x z y
    rwa [jordanTriple_outer_comm z x y] at h

  /-
  V_{x,y}(U_x {y,x,z})
    =
  U_x V_{y,x}({y,x,z}).
  -/
  have h2 :
      V x y (U x (jordanTriple y x z)) =
        U x (V y x (jordanTriple y x z)) := by
    have h :=
      V_quadRep_eq_quadRep_triple
        x y (jordanTriple y x z)
    simpa only [triple_eq_V_apply] using h

  /-
  V_{x,y}(U_x y) = U_x(U_y x).
  -/
  have h3 :
      V x y (U x y) =
        U x (U y x) := by
    have h :=
      V_quadRep_eq_quadRep_triple x y y
    have hyxy' :
        jordanTriple y x y = U y x :=
      jordanTriple_diag y x
    rwa [hyxy'] at h

  /-
  V_{x,z}(U_x(U_y x))
    =
  U_x V_{z,x}(U_y x).
  -/
  have h4 :
      V x z (U x (U y x)) =
        U x (V z x (U y x)) := by
    have h :=
      V_quadRep_eq_quadRep_triple
        x z (U y x)
    simpa only [triple_eq_V_apply] using h

  /-
  V_{x,{y,x,z}}(U_x y)
    =
  U_x V_{{y,x,z},x}(y).
  -/
  have h5 :
      V x (jordanTriple y x z) (U x y) =
        U x (V (jordanTriple y x z) x y) := by
    have h :=
      V_quadRep_eq_quadRep_triple
        x (jordanTriple y x z) y
    simpa only [triple_eq_V_apply] using h

  /-
  Outer symmetry:
      V_{{y,x,z},x}(y)
        =
      V_{y,x}({y,x,z}).
  -/
  have h6 :
      V (jordanTriple y x z) x y =
        V y x (jordanTriple y x z) := by
    rw [
      triple_eq_V_apply,
      triple_eq_V_apply,
      jordanTriple_outer_comm
    ]

  rw [
    h1,
    h2,
    h3,
    h4,
    hUU,
    h5,
    h6
  ] at hmain

  /-
  After the rewrites, hmain has the additive form

      P - Q = R - P,

  where

      P = U_x(V_{y,x}{y,x,z}),
      Q = U_x(V_{z,x}(U_y x)),
      R = U_{U_x y} z.

  Solve for R using only additive-group normalization.
  -/
  have hmain' :
      U (U x y) z =
        U x (V y x (jordanTriple y x z)) +
          U x (V y x (jordanTriple y x z)) -
          U x (V z x (U y x)) := by
    calc
      U (U x y) z =
          (U (U x y) z -
            U x (V y x (jordanTriple y x z))) +
            U x (V y x (jordanTriple y x z)) := by
        abel
      _ =
          (U x (V y x (jordanTriple y x z)) -
            U x (V z x (U y x))) +
            U x (V y x (jordanTriple y x z)) := by
        rw [← hmain]
      _ =
          U x (V y x (jordanTriple y x z)) +
            U x (V y x (jordanTriple y x z)) -
            U x (V z x (U y x)) := by
        abel

  exact hmain'.trans hinnerUx.symm

lemma quadraticRepresentation_fundamental (x y : E) :
    U (U x y) = (U x).comp ((U y).comp (U x)) := by
  ext z
  exact quadraticRepresentation_fundamental_apply x y z

end AlbertSequential.RealJordan
