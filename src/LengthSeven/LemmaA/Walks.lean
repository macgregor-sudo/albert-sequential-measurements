/- SPDX-License-Identifier: Apache-2.0
   Machine-generated file. -/
module

public import LengthSeven.LemmaA.Instances

/-! # Lemma A: walk lemmas

One lemma per walk value, for generic letters `x, y, z` (an ordering of `B, C, D`), proved from
`UsedRules` by replaying its rule steps: each step lemma (`stepR1`, `stepR2`, `stepL2`, `stepY`,
`stepD` of `Rules.lean`) gives one scalar relation among walk values, earlier walk lemmas at
permuted letters supply the known values, and `linear_combination` closes the goal.  Trace atoms
are first brought to the normal form `o a b`, `R a b c` with `0 < x < y < z` in argument order
(`walk_nf`). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.LemmaA

open AlbertSequential AlbertSequential.LengthSeven

set_option hygiene false in
/-- Unfold pattern evaluation and chains; sort the arguments of the trace atoms. -/
local macro "walk_nf" : tactic =>
  `(tactic| (try simp only [List.map_cons, List.map_nil, PL.ev_A, PL.ev_X, PL.ev_Y, PL.ev_Z,
    List.getLastD_cons, List.getLastD_nil, TraceData.chainProd, WalkForm.L_nil,
    τ.o_symm x 0,
    τ.o_symm y 0,
    τ.o_symm z 0,
    τ.o_symm y x,
    τ.o_symm z x,
    τ.o_symm z y,
    R_213 τ 0 x y,
    R_132 τ 0 x y,
    R_231 τ 0 x y,
    R_312 τ 0 x y,
    R_321 τ 0 x y,
    R_213 τ 0 x z,
    R_132 τ 0 x z,
    R_231 τ 0 x z,
    R_312 τ 0 x z,
    R_321 τ 0 x z,
    R_213 τ 0 y z,
    R_132 τ 0 y z,
    R_231 τ 0 y z,
    R_312 τ 0 y z,
    R_321 τ 0 y z,
    R_213 τ x y z,
    R_132 τ x y z,
    R_231 τ x y z,
    R_312 τ x y z,
    R_321 τ x y z] at *))

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V} {τ : TraceData}

/-- W01: `L(∅) = 1`; proved by a chain of rule steps. -/
theorem walk_W01 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [] = 1 := by
  exact W.L_nil

/-- W02: `L(x) = τ.o 0 x`; proved by a chain of rule steps. -/
theorem walk_W02 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x] = τ.o 0 x := by
  have s1 := stepY (u := [.X]) (h.inst x y z hxyz (.chain [.X]) (by decide)) [.X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W03: `L(xy) = τ.R 0 x y`; proved by a chain of rule steps. -/
theorem walk_W03 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y] = τ.R 0 x y := by
  have s1 := stepD (u := []) (a := .X) (n := .Y) (r := []) (h.inst x y z hxyz (.delete [] .X .Y []) (by decide)) [.X, .Y] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W04: `L(xyx) = τ.o 0 x * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W04 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, x] = τ.o 0 x * τ.o x y := by
  have s1 := stepY (u := [.X, .Y]) (h.inst x y z hxyz (.chain [.X, .Y]) (by decide)) [.X, .Y, .X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W05: `L(xyz) = τ.om y`; proved by a chain of rule steps. -/
theorem walk_W05 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z] = τ.om y := by
  have s1 := stepL2 (a := .Z) (b := .Y) (c := .X) (h.r3 _ _ _ (PL.ord hxyz .Z .Y .X rfl)) [] [.X, .Y, .Z] [.X, .Y, .Z] [] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination ((1 / 2)) * s1

/-- W10: `L(xyzx) = τ.R x y z * τ.o 0 x`; proved by a chain of rule steps. -/
theorem walk_W10 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x] = τ.R x y z * τ.o 0 x := by
  have s1 := stepD (u := [.X]) (a := .Y) (n := .Z) (r := []) (h.inst x y z hxyz (.delete [.X] .Y .Z []) (by decide)) [.X, .Y, .Z, .X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W16: `L(xyAyx) = τ.o 0 x * τ.o 0 y * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W16 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, y, x] = τ.o 0 x * τ.o 0 y * τ.o x y := by
  have s1 := stepY (u := [.X, .Y, .A]) (h.inst x y z hxyz (.chain [.X, .Y, .A]) (by decide)) [.X, .Y, .A, .Y, .X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W34: `L(xyAzAyx) = τ.o 0 x * τ.o 0 y * τ.o 0 z * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W34 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, 0, y, x] = τ.o 0 x * τ.o 0 y * τ.o 0 z * τ.o x y := by
  have s1 := stepY (u := [.X, .Y, .A, .Z]) (h.inst x y z hxyz (.chain [.X, .Y, .A, .Z]) (by decide)) [.X, .Y, .A, .Z, .A, .Y, .X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W23: `L(xyAyxz) = τ.R 0 x z * τ.o 0 y * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W23 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, y, x, z] = τ.R 0 x z * τ.o 0 y * τ.o x y := by
  have s1 := stepD (u := []) (a := .Z) (n := .X) (r := [.Y, .A]) (h.inst x y z hxyz (.delete [] .Z .X [.Y, .A]) (by decide)) [.X, .Y, .A, .Y, .X, .Z] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W24: `L(xyAyzx) = τ.R x y z * τ.o 0 x * τ.o 0 y`; proved by a chain of rule steps. -/
theorem walk_W24 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, y, z, x] = τ.R x y z * τ.o 0 x * τ.o 0 y := by
  have s1 := stepD (u := [.X]) (a := .Z) (n := .Y) (r := [.A]) (h.inst x y z hxyz (.delete [.X] .Z .Y [.A]) (by decide)) [.X, .Y, .A, .Y, .Z, .X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W27: `L(xyAzyx) = τ.R 0 y z * τ.o 0 x * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W27 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, y, x] = τ.R 0 y z * τ.o 0 x * τ.o x y := by
  have s1 := stepD (u := [.X, .Y]) (a := .A) (n := .Z) (r := []) (h.inst x y z hxyz (.delete [.X, .Y] .A .Z []) (by decide)) [.X, .Y, .A, .Z, .Y, .X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W41: `L(xyAzAyxz) = τ.R 0 x z * τ.o 0 y * τ.o 0 z * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W41 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, 0, y, x, z] = τ.R 0 x z * τ.o 0 y * τ.o 0 z * τ.o x y := by
  have s1 := stepD (u := []) (a := .Z) (n := .X) (r := [.Y, .A, .Z]) (h.inst x y z hxyz (.delete [] .Z .X [.Y, .A, .Z]) (by decide)) [.X, .Y, .A, .Z, .A, .Y, .X, .Z] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W42: `L(xyAzAyzx) = τ.R x y z * τ.o 0 x * τ.o 0 y * τ.o 0 z`; proved by a chain of rule steps. -/
theorem walk_W42 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, 0, y, z, x] = τ.R x y z * τ.o 0 x * τ.o 0 y * τ.o 0 z := by
  have s1 := stepD (u := [.X]) (a := .Z) (n := .Y) (r := [.A, .Z]) (h.inst x y z hxyz (.delete [.X] .Z .Y [.A, .Z]) (by decide)) [.X, .Y, .A, .Z, .A, .Y, .Z, .X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W44: `L(xyAzAzyx) = τ.R 0 y z * τ.o 0 x * τ.o 0 z * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W44 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, 0, z, y, x] = τ.R 0 y z * τ.o 0 x * τ.o 0 z * τ.o x y := by
  have s1 := stepD (u := [.X, .Y]) (a := .A) (n := .Z) (r := [.A]) (h.inst x y z hxyz (.delete [.X, .Y] .A .Z [.A]) (by decide)) [.X, .Y, .A, .Z, .A, .Z, .Y, .X] (by decide)
  walk_nf
  linear_combination (1) * s1

/-- W06: `L(xAxy) = τ.R 0 x y * τ.o 0 x`; proved by a chain of rule steps. -/
theorem walk_W06 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, 0, x, y] = τ.R 0 x y * τ.o 0 x := by
  have k1 := walk_W03 h x y z hxyz
  have s1 := stepR1 (t := []) (q := .A) (v := .X) (h.inst x y z hxyz (.r1 [] .A .X) (by decide)) [.X, .Y, .A] [.X, .A, .X, .Y] [.X, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 x) * k1 + (1) * s1

/-- W07: `L(xAyx) = τ.R 0 x y * τ.o 0 x`; proved by a chain of rule steps. -/
theorem walk_W07 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, 0, y, x] = τ.R 0 x y * τ.o 0 x := by
  have k1 := walk_W03 h x y z hxyz
  have s1 := stepR1 (t := []) (q := .A) (v := .X) (h.inst x y z hxyz (.r1 [] .A .X) (by decide)) [.Y, .X, .A] [.X, .A, .Y, .X] [.X, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 x) * k1 + (1) * s1

/-- W08: `L(xAyz) = τ.R 0 y z * τ.o 0 x`; proved by a chain of rule steps. -/
theorem walk_W08 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, 0, y, z] = τ.R 0 y z * τ.o 0 x := by
  have k1 := walk_W03 h y z x (PL.ord hxyz .Y .Z .X rfl)
  have s1 := stepR1 (t := []) (q := .A) (v := .X) (h.inst x y z hxyz (.r1 [] .A .X) (by decide)) [.Y, .Z, .A] [.X, .A, .Y, .Z] [.Y, .Z] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 x) * k1 + (1) * s1

/-- W11: `L(xAxyz) = τ.o 0 x * τ.om y`; proved by a chain of rule steps. -/
theorem walk_W11 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, 0, x, y, z] = τ.o 0 x * τ.om y := by
  have k1 := walk_W05 h x y z hxyz
  have s1 := stepR1 (t := []) (q := .A) (v := .X) (h.inst x y z hxyz (.r1 [] .A .X) (by decide)) [.X, .Y, .Z, .A] [.X, .A, .X, .Y, .Z] [.X, .Y, .Z] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 x) * k1 + (1) * s1

/-- W12: `L(xAyxz) = τ.o 0 x * τ.om x`; proved by a chain of rule steps. -/
theorem walk_W12 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, 0, y, x, z] = τ.o 0 x * τ.om x := by
  have k1 := walk_W05 h y x z (PL.ord hxyz .Y .X .Z rfl)
  have s1 := stepR1 (t := []) (q := .A) (v := .X) (h.inst x y z hxyz (.r1 [] .A .X) (by decide)) [.Y, .X, .Z, .A] [.X, .A, .Y, .X, .Z] [.Y, .X, .Z] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 x) * k1 + (1) * s1

/-- W13: `L(xAyzx) = τ.o 0 x * τ.om z`; proved by a chain of rule steps. -/
theorem walk_W13 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, 0, y, z, x] = τ.o 0 x * τ.om z := by
  have k1 := walk_W05 h x z y (PL.ord hxyz .X .Z .Y rfl)
  have s1 := stepR1 (t := []) (q := .A) (v := .X) (h.inst x y z hxyz (.r1 [] .A .X) (by decide)) [.Y, .Z, .X, .A] [.X, .A, .Y, .Z, .X] [.X, .Z, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 x) * k1 + (1) * s1

/-- W09: `L(xyxz) = τ.R 0 x z * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W09 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, x, z] = τ.R 0 x z * τ.o x y := by
  have k1 := walk_W03 h x z y (PL.ord hxyz .X .Z .Y rfl)
  have s1 := stepR1 (t := []) (q := .X) (v := .Y) (h.inst x y z hxyz (.r1 [] .X .Y) (by decide)) [.Z, .A] [.X, .Y, .X, .Z] [.X, .Z] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x y) * k1 + (1) * s1

/-- W19: `L(xyxzy) = τ.o x y * τ.om z`; proved by a chain of rule steps. -/
theorem walk_W19 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, x, z, y] = τ.o x y * τ.om z := by
  have k1 := walk_W05 h x z y (PL.ord hxyz .X .Z .Y rfl)
  have s1 := stepR1 (t := []) (q := .X) (v := .Y) (h.inst x y z hxyz (.r1 [] .X .Y) (by decide)) [.Z, .Y, .A] [.X, .Y, .X, .Z, .Y] [.X, .Z, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x y) * k1 + (1) * s1

/-- W14: `L(xyAxy) = 2 * τ.R 0 x y ^ 2 - τ.o 0 x * τ.o 0 y * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W14 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, x, y] = 2 * τ.R 0 x y ^ 2 - τ.o 0 x * τ.o 0 y * τ.o x y := by
  have k1 := walk_W03 h x y z hxyz
  have k2 := walk_W16 h y x z (PL.ord hxyz .Y .X .Z rfl)
  have s1 := stepR2 (t := []) (q := .A) (s := .Y) (m := .X) (h.inst x y z hxyz (.r2 [] .A .Y .X) (by decide)) [.X, .Y, .A] [.Y, .X, .A, .X, .Y] [.X, .Y, .A, .X, .Y] [.X, .Y] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 x y) * k1 + (-1) * k2 + (1) * s1

/-- W15: `L(xyAxz) = 2 * τ.R 0 x y * τ.R 0 x z - τ.o 0 x * τ.om x`; proved by a chain of rule steps. -/
theorem walk_W15 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, x, z] = 2 * τ.R 0 x y * τ.R 0 x z - τ.o 0 x * τ.om x := by
  have k1 := walk_W03 h x z y (PL.ord hxyz .X .Z .Y rfl)
  have k2 := walk_W12 h x y z hxyz
  have s1 := stepR2 (t := []) (q := .X) (s := .Y) (m := .A) (h.inst x y z hxyz (.r2 [] .X .Y .A) (by decide)) [.Z, .A] [.X, .Y, .A, .X, .Z] [.X, .A, .Y, .X, .Z] [.X, .Z] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 x y) * k1 + (-1) * k2 + (1) * s1

/-- W18: `L(xyAzx) = τ.o 0 x * τ.om x`; proved by a chain of rule steps. -/
theorem walk_W18 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, x] = τ.o 0 x * τ.om x := by
  have k1 := walk_W03 h x y z hxyz
  have k2 := walk_W15 h x y z hxyz
  have s1 := stepR2 (t := []) (q := .A) (s := .X) (m := .Z) (h.inst x y z hxyz (.r2 [] .A .X .Z) (by decide)) [.Y, .X, .A] [.X, .Y, .A, .Z, .X] [.X, .Y, .A, .X, .Z] [.X, .Y] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 x z) * k1 + (-1) * k2 + (1) * s1

/-- W20: `L(xyzxy) = 2 * τ.R 0 x y * τ.R x y z - τ.o x y * τ.om z`; proved by a chain of rule steps. -/
theorem walk_W20 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x, y] = 2 * τ.R 0 x y * τ.R x y z - τ.o x y * τ.om z := by
  have k1 := walk_W03 h x y z hxyz
  have k2 := walk_W19 h y x z (PL.ord hxyz .Y .X .Z rfl)
  have s1 := stepR2 (t := [.Y]) (q := .X) (s := .Z) (m := .Y) (h.inst x y z hxyz (.r2 [.Y] .X .Z .Y) (by decide)) [.A] [.X, .Y, .Z, .X, .Y] [.Y, .X, .Y, .Z, .X] [.X, .Y] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R x y z) * k1 + (-1) * k2 + (1) * s1

/-- X01: `L(xyzAyxz) = -2 * τ.R 0 x y * τ.R x y z * τ.o 0 z + τ.o 0 z * τ.o x y * τ.om z + 2 * τ.om x * τ.om y`; proved by a chain of rule steps. -/
theorem walk_X01 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, y, x, z] = -2 * τ.R 0 x y * τ.R x y z * τ.o 0 z + τ.o 0 z * τ.o x y * τ.om z + 2 * τ.om x * τ.om y := by
  have k1 := walk_W05 h x y z hxyz
  have k2 := walk_W20 h x y z hxyz
  have s1 := stepR1 (t := [.Y, .X]) (q := .Z) (v := .A) (h.inst x y z hxyz (.r1 [.Y, .X] .Z .A) (by decide)) [.Y, .X, .A] [.X, .Y, .Z, .A, .Z, .X, .Y] [.X, .Y, .Z, .X, .Y] (by decide) (by decide)
  have s2 := stepL2 (a := .Z) (b := .X) (c := .Y) (h.r3 _ _ _ (PL.ord hxyz .Z .X .Y rfl)) [.Z, .Y, .X, .A] [.X, .Y, .Z, .A, .Y, .X, .Z] [.X, .Y, .Z, .A, .Z, .X, .Y] [.X, .Y, .Z] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.om x) * k1 + (-τ.o 0 z) * k2 + (-1) * s1 + (1) * s2

/-- W17: `L(xyAyz) = τ.o 0 y * τ.om y`; proved by a chain of rule steps. -/
theorem walk_W17 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, y, z] = τ.o 0 y * τ.om y := by
  have k1 := walk_W05 h x y z hxyz
  have s1 := stepR1 (t := [.Z]) (q := .Y) (v := .A) (h.inst x y z hxyz (.r1 [.Z] .Y .A) (by decide)) [.X, .A] [.X, .Y, .A, .Y, .Z] [.X, .Y, .Z] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 y) * k1 + (1) * s1

/-- W26: `L(xyAzxz) = τ.R 0 x y * τ.o 0 z * τ.o x z`; proved by a chain of rule steps. -/
theorem walk_W26 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, x, z] = τ.R 0 x y * τ.o 0 z * τ.o x z := by
  have k1 := walk_W08 h z y x (PL.ord hxyz .Z .Y .X rfl)
  have s1 := stepR1 (t := []) (q := .Z) (v := .X) (h.inst x y z hxyz (.r1 [] .Z .X) (by decide)) [.A, .Y, .X, .A] [.X, .Y, .A, .Z, .X, .Z] [.Z, .A, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x z) * k1 + (1) * s1

/-- W28: `L(xyAzyz) = τ.R 0 x y * τ.o 0 z * τ.o y z`; proved by a chain of rule steps. -/
theorem walk_W28 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, y, z] = τ.R 0 x y * τ.o 0 z * τ.o y z := by
  have k1 := walk_W08 h z y x (PL.ord hxyz .Z .Y .X rfl)
  have s1 := stepR1 (t := []) (q := .Z) (v := .Y) (h.inst x y z hxyz (.r1 [] .Z .Y) (by decide)) [.A, .Y, .X, .A] [.X, .Y, .A, .Z, .Y, .Z] [.Z, .A, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o y z) * k1 + (1) * s1

/-- W29: `L(xyAxAyz) = τ.o 0 x * τ.o 0 y * τ.om y`; proved by a chain of rule steps. -/
theorem walk_W29 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, x, 0, y, z] = τ.o 0 x * τ.o 0 y * τ.om y := by
  have k1 := walk_W17 h x y z hxyz
  have s1 := stepR1 (t := [.X, .Y]) (q := .A) (v := .X) (h.inst x y z hxyz (.r1 [.X, .Y] .A .X) (by decide)) [.Y, .Z, .A] [.X, .Y, .A, .X, .A, .Y, .Z] [.X, .Y, .A, .Y, .Z] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 x) * k1 + (1) * s1

/-- W31: `L(xyAyAzx) = τ.o 0 x * τ.o 0 y * τ.om x`; proved by a chain of rule steps. -/
theorem walk_W31 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, y, 0, z, x] = τ.o 0 x * τ.o 0 y * τ.om x := by
  have k1 := walk_W18 h x y z hxyz
  have s1 := stepR1 (t := [.X]) (q := .Y) (v := .A) (h.inst x y z hxyz (.r1 [.X] .Y .A) (by decide)) [.A, .Z, .X, .A] [.X, .Y, .A, .Y, .A, .Z, .X] [.X, .Y, .A, .Z, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 y) * k1 + (1) * s1

/-- W32: `L(xyAyxzy) = τ.o 0 y * τ.o x y * τ.om z`; proved by a chain of rule steps. -/
theorem walk_W32 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, y, x, z, y] = τ.o 0 y * τ.o x y * τ.om z := by
  have k1 := walk_W19 h x y z hxyz
  have s1 := stepR1 (t := [.X]) (q := .Y) (v := .A) (h.inst x y z hxyz (.r1 [.X] .Y .A) (by decide)) [.X, .Z, .Y, .A] [.X, .Y, .A, .Y, .X, .Z, .Y] [.X, .Y, .X, .Z, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 y) * k1 + (1) * s1

/-- W33: `L(xyAzAxy) = 2 * τ.R 0 x y ^ 2 * τ.o 0 z - τ.o 0 x * τ.o 0 y * τ.o 0 z * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W33 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, 0, x, y] = 2 * τ.R 0 x y ^ 2 * τ.o 0 z - τ.o 0 x * τ.o 0 y * τ.o 0 z * τ.o x y := by
  have k1 := walk_W14 h x y z hxyz
  have s1 := stepR1 (t := [.X, .Y]) (q := .A) (v := .Z) (h.inst x y z hxyz (.r1 [.X, .Y] .A .Z) (by decide)) [.X, .Y, .A] [.X, .Y, .A, .Z, .A, .X, .Y] [.X, .Y, .A, .X, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 z) * k1 + (1) * s1

/-- W36: `L(xyAzxzy) = 2 * τ.R 0 x y * τ.R 0 y z * τ.o x z - τ.o 0 y * τ.o x z * τ.om y`; proved by a chain of rule steps. -/
theorem walk_W36 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, x, z, y] = 2 * τ.R 0 x y * τ.R 0 y z * τ.o x z - τ.o 0 y * τ.o x z * τ.om y := by
  have k1 := walk_W15 h y z x (PL.ord hxyz .Y .Z .X rfl)
  have s1 := stepR1 (t := [.Y]) (q := .Z) (v := .X) (h.inst x y z hxyz (.r1 [.Y] .Z .X) (by decide)) [.A, .Y, .X, .A] [.X, .Y, .A, .Z, .X, .Z, .Y] [.Y, .Z, .A, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x z) * k1 + (1) * s1

/-- W38: `L(xyAzyzx) = τ.o 0 x * τ.o y z * τ.om x`; proved by a chain of rule steps. -/
theorem walk_W38 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, y, z, x] = τ.o 0 x * τ.o y z * τ.om x := by
  have k1 := walk_W18 h x y z hxyz
  have s1 := stepR1 (t := [.X]) (q := .Z) (v := .Y) (h.inst x y z hxyz (.r1 [.X] .Z .Y) (by decide)) [.A, .Y, .X, .A] [.X, .Y, .A, .Z, .Y, .Z, .X] [.X, .Y, .A, .Z, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o y z) * k1 + (1) * s1

/-- W21: `L(xyAxyz) = 2 * τ.R 0 x y * τ.om y - τ.R 0 y z * τ.o 0 x * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W21 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, x, y, z] = 2 * τ.R 0 x y * τ.om y - τ.R 0 y z * τ.o 0 x * τ.o x y := by
  have k1 := walk_W03 h x y z hxyz
  have k2 := walk_W27 h x y z hxyz
  have s1 := stepL2 (a := .Z) (b := .Y) (c := .X) (h.r3 _ _ _ (PL.ord hxyz .Z .Y .X rfl)) [.Y, .X, .A] [.X, .Y, .A, .X, .Y, .Z] [.X, .Y, .A, .Z, .Y, .X] [.X, .Y] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.om y) * k1 + (-1) * k2 + (1) * s1

/-- W22: `L(xyAxzy) = 2 * τ.R 0 x y * τ.om z - τ.R x y z * τ.o 0 x * τ.o 0 y`; proved by a chain of rule steps. -/
theorem walk_W22 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, x, z, y] = 2 * τ.R 0 x y * τ.om z - τ.R x y z * τ.o 0 x * τ.o 0 y := by
  have k1 := walk_W03 h x y z hxyz
  have k2 := walk_W24 h x y z hxyz
  have s1 := stepL2 (a := .Y) (b := .Z) (c := .X) (h.r3 _ _ _ (PL.ord hxyz .Y .Z .X rfl)) [.Y, .X, .A] [.X, .Y, .A, .X, .Z, .Y] [.X, .Y, .A, .Y, .Z, .X] [.X, .Y] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.om z) * k1 + (-1) * k2 + (1) * s1

/-- W25: `L(xyAzxy) = 2 * τ.R 0 x y * τ.om x - τ.R 0 x z * τ.o 0 y * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W25 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, x, y] = 2 * τ.R 0 x y * τ.om x - τ.R 0 x z * τ.o 0 y * τ.o x y := by
  have k1 := walk_W03 h x y z hxyz
  have k2 := walk_W23 h x y z hxyz
  have s1 := stepL2 (a := .Y) (b := .X) (c := .Z) (h.r3 _ _ _ (PL.ord hxyz .Y .X .Z rfl)) [.Y, .X, .A] [.X, .Y, .A, .Z, .X, .Y] [.X, .Y, .A, .Y, .X, .Z] [.X, .Y] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.om x) * k1 + (-1) * k2 + (1) * s1

/-- W39: `L(xyAzAxyz) = 2 * τ.R 0 x y * τ.o 0 z * τ.om y - τ.R 0 y z * τ.o 0 x * τ.o 0 z * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W39 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, 0, x, y, z] = 2 * τ.R 0 x y * τ.o 0 z * τ.om y - τ.R 0 y z * τ.o 0 x * τ.o 0 z * τ.o x y := by
  have k1 := walk_W21 h x y z hxyz
  have s1 := stepR1 (t := [.X, .Y]) (q := .A) (v := .Z) (h.inst x y z hxyz (.r1 [.X, .Y] .A .Z) (by decide)) [.X, .Y, .Z, .A] [.X, .Y, .A, .Z, .A, .X, .Y, .Z] [.X, .Y, .A, .X, .Y, .Z] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 z) * k1 + (1) * s1

/-- W40: `L(xyAzAxzy) = 2 * τ.R 0 x y * τ.o 0 z * τ.om z - τ.R x y z * τ.o 0 x * τ.o 0 y * τ.o 0 z`; proved by a chain of rule steps. -/
theorem walk_W40 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, 0, x, z, y] = 2 * τ.R 0 x y * τ.o 0 z * τ.om z - τ.R x y z * τ.o 0 x * τ.o 0 y * τ.o 0 z := by
  have k1 := walk_W22 h x y z hxyz
  have s1 := stepR1 (t := [.X, .Y]) (q := .A) (v := .Z) (h.inst x y z hxyz (.r1 [.X, .Y] .A .Z) (by decide)) [.X, .Z, .Y, .A] [.X, .Y, .A, .Z, .A, .X, .Z, .Y] [.X, .Y, .A, .X, .Z, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 z) * k1 + (1) * s1

/-- W43: `L(xyAzAzxy) = 2 * τ.R 0 x y * τ.o 0 z * τ.om x - τ.R 0 x z * τ.o 0 y * τ.o 0 z * τ.o x y`; proved by a chain of rule steps. -/
theorem walk_W43 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, 0, z, x, y] = 2 * τ.R 0 x y * τ.o 0 z * τ.om x - τ.R 0 x z * τ.o 0 y * τ.o 0 z * τ.o x y := by
  have k1 := walk_W25 h x y z hxyz
  have s1 := stepR1 (t := [.X, .Y]) (q := .A) (v := .Z) (h.inst x y z hxyz (.r1 [.X, .Y] .A .Z) (by decide)) [.Z, .X, .Y, .A] [.X, .Y, .A, .Z, .A, .Z, .X, .Y] [.X, .Y, .A, .Z, .X, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 z) * k1 + (1) * s1

/-- W47: `L(xyAzyzxy) = 2 * τ.R 0 x y * τ.o y z * τ.om x - τ.R 0 x z * τ.o 0 y * τ.o x y * τ.o y z`; proved by a chain of rule steps. -/
theorem walk_W47 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, y, z, x, y] = 2 * τ.R 0 x y * τ.o y z * τ.om x - τ.R 0 x z * τ.o 0 y * τ.o x y * τ.o y z := by
  have k1 := walk_W25 h x y z hxyz
  have s1 := stepR1 (t := [.Y, .X]) (q := .Z) (v := .Y) (h.inst x y z hxyz (.r1 [.Y, .X] .Z .Y) (by decide)) [.A, .Y, .X, .A] [.X, .Y, .A, .Z, .Y, .Z, .X, .Y] [.X, .Y, .A, .Z, .X, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o y z) * k1 + (1) * s1

/-- W30: `L(xyAxzyx) = τ.o 0 x * τ.o x y * τ.om z`; proved by a chain of rule steps. -/
theorem walk_W30 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, x, z, y, x] = τ.o 0 x * τ.o x y * τ.om z := by
  have k1 := walk_W10 h x y z hxyz
  have k2 := walk_W20 h x y z hxyz
  have s1 := stepR1 (t := []) (q := .A) (v := .X) (h.inst x y z hxyz (.r1 [] .A .X) (by decide)) [.Y, .X, .Z, .Y, .X, .A] [.X, .A, .Y, .X, .Z, .Y, .X] [.X, .Y, .Z, .X, .Y] (by decide) (by decide)
  have s2 := stepR2 (t := []) (q := .X) (s := .A) (m := .Y) (h.inst x y z hxyz (.r2 [] .X .A .Y) (by decide)) [.Z, .Y, .X, .A] [.X, .A, .Y, .X, .Z, .Y, .X] [.X, .Y, .A, .X, .Z, .Y, .X] [.X, .Y, .Z, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 x y) * k1 + (-τ.o 0 x) * k2 + (-1) * s1 + (1) * s2

/-- W37: `L(xyAzyxz) = 2 * τ.R 0 x y * τ.R x y z * τ.o 0 z + 2 * τ.R 0 x z * τ.R 0 y z * τ.o x y - τ.o 0 z * τ.o x y * τ.om z - 2 * τ.om x * τ.om y`; proved by a chain of rule steps. -/
theorem walk_W37 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, y, x, z] = 2 * τ.R 0 x y * τ.R x y z * τ.o 0 z + 2 * τ.R 0 x z * τ.R 0 y z * τ.o x y - τ.o 0 z * τ.o x y * τ.om z - 2 * τ.om x * τ.om y := by
  have k1 := walk_W09 h x y z hxyz
  have k2 := walk_X01 h x y z hxyz
  have s1 := stepR2 (t := [.X]) (q := .Y) (s := .Z) (m := .A) (h.inst x y z hxyz (.r2 [.X] .Y .Z .A) (by decide)) [.X, .Z, .A] [.X, .Y, .Z, .A, .Y, .X, .Z] [.X, .Y, .A, .Z, .Y, .X, .Z] [.X, .Y, .X, .Z] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 y z) * k1 + (-1) * k2 + (1) * s1

/-- W35: `L(xyAzxyz) = -2 * τ.R 0 x z * τ.R 0 y z * τ.o x y + τ.o 0 z * τ.o x y * τ.om z + 2 * τ.om x * τ.om y`; proved by a chain of rule steps. -/
theorem walk_W35 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, x, y, z] = -2 * τ.R 0 x z * τ.R 0 y z * τ.o x y + τ.o 0 z * τ.o x y * τ.om z + 2 * τ.om x * τ.om y := by
  have k1 := walk_W08 h z y x (PL.ord hxyz .Z .Y .X rfl)
  have k2 := walk_W37 h x y z hxyz
  have s1 := stepR2 (t := []) (q := .Z) (s := .Y) (m := .X) (h.inst x y z hxyz (.r2 [] .Z .Y .X) (by decide)) [.A, .Y, .X, .A] [.X, .Y, .A, .Z, .X, .Y, .Z] [.X, .Y, .A, .Z, .Y, .X, .Z] [.Z, .A, .Y, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R x y z) * k1 + (-1) * k2 + (1) * s1

/-- W45: `L(xyAzxAzy) = 4 * τ.R 0 x y * τ.R 0 x z * τ.R 0 y z - 2 * τ.R 0 x y * τ.o 0 z * τ.om z - 2 * τ.R 0 x z * τ.o 0 y * τ.om y + τ.R x y z * τ.o 0 x * τ.o 0 y * τ.o 0 z`; proved by a chain of rule steps. -/
theorem walk_W45 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, x, 0, z, y] = 4 * τ.R 0 x y * τ.R 0 x z * τ.R 0 y z - 2 * τ.R 0 x y * τ.o 0 z * τ.om z - 2 * τ.R 0 x z * τ.o 0 y * τ.om y + τ.R x y z * τ.o 0 x * τ.o 0 y * τ.o 0 z := by
  have k1 := walk_W15 h y z x (PL.ord hxyz .Y .Z .X rfl)
  have k2 := walk_W40 h x y z hxyz
  have s1 := stepR2 (t := [.Y]) (q := .Z) (s := .X) (m := .A) (h.inst x y z hxyz (.r2 [.Y] .Z .X .A) (by decide)) [.A, .Y, .X, .A] [.X, .Y, .A, .Z, .A, .X, .Z, .Y] [.X, .Y, .A, .Z, .X, .A, .Z, .Y] [.Y, .Z, .A, .Y, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 x z) * k1 + (-1) * k2 + (1) * s1

/-- W46: `L(xyAzxyzx) = -τ.R 0 y z * τ.o 0 x * τ.o x y * τ.o x z + 2 * τ.R x y z * τ.o 0 x * τ.om x`; proved by a chain of rule steps. -/
theorem walk_W46 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, x, y, z, x] = -τ.R 0 y z * τ.o 0 x * τ.o x y * τ.o x z + 2 * τ.R x y z * τ.o 0 x * τ.om x := by
  have k1 := walk_W18 h x y z hxyz
  have s1 := stepD (u := [.X, .Y]) (a := .A) (n := .Z) (r := [.X]) (h.inst x y z hxyz (.delete [.X, .Y] .A .Z [.X]) (by decide)) [.X, .Y, .A, .Z, .X, .Z, .Y, .X] (by decide)
  have s2 := stepR2 (t := []) (q := .X) (s := .Z) (m := .Y) (h.inst x y z hxyz (.r2 [] .X .Z .Y) (by decide)) [.Z, .A, .Y, .X, .A] [.X, .Y, .A, .Z, .X, .Y, .Z, .X] [.X, .Y, .A, .Z, .X, .Z, .Y, .X] [.X, .Y, .A, .Z, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R x y z) * k1 + (-1) * s1 + (1) * s2

/-- S01: `L(xyxy) = τ.R 0 x y * τ.o x y`; proved by one rule step (forward chaining). -/
theorem walk_S01 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, x, y] = τ.R 0 x y * τ.o x y := by
  have k1 := walk_W03 h x y z hxyz
  have s1 := stepR1 (t := []) (q := .X) (v := .Y) (h.inst x y z hxyz (.r1 [] .X .Y) (by decide)) [.Y] [.X, .Y, .X, .Y] [.X, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x y) * k1 + (1) * s1

/-- S02: `L(xyxyz) = τ.o x y * τ.om y`; proved by one rule step (forward chaining). -/
theorem walk_S02 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, x, y, z] = τ.o x y * τ.om y := by
  have k1 := walk_W05 h x y z hxyz
  have s1 := stepR1 (t := []) (q := .X) (v := .Y) (h.inst x y z hxyz (.r1 [] .X .Y) (by decide)) [.Y, .Z] [.X, .Y, .X, .Y, .Z] [.X, .Y, .Z] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x y) * k1 + (1) * s1

/-- S03: `L(xyxyzx) = τ.R x y z * τ.o 0 x * τ.o x y`; proved by one rule step (forward chaining). -/
theorem walk_S03 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, x, y, z, x] = τ.R x y z * τ.o 0 x * τ.o x y := by
  have k1 := walk_W10 h x y z hxyz
  have s1 := stepR1 (t := []) (q := .X) (v := .Y) (h.inst x y z hxyz (.r1 [] .X .Y) (by decide)) [.Y, .Z, .X] [.X, .Y, .X, .Y, .Z, .X] [.X, .Y, .Z, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x y) * k1 + (1) * s1

/-- S04: `L(xyxzyx) = τ.R x y z * τ.o 0 x * τ.o x y`; proved by one rule step (forward chaining). -/
theorem walk_S04 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, x, z, y, x] = τ.R x y z * τ.o 0 x * τ.o x y := by
  have k1 := walk_W10 h x y z hxyz
  have s1 := stepR1 (t := []) (q := .X) (v := .Y) (h.inst x y z hxyz (.r1 [] .X .Y) (by decide)) [.Z, .Y, .X] [.X, .Y, .X, .Z, .Y, .X] [.X, .Y, .Z, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x y) * k1 + (1) * s1

/-- S05: `L(xyzyx) = τ.o 0 x * τ.o x y * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S05 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, y, x] = τ.o 0 x * τ.o x y * τ.o y z := by
  have k1 := walk_W04 h x y z hxyz
  have s1 := stepR1 (t := [.X]) (q := .Y) (v := .Z) (h.inst x y z hxyz (.r1 [.X] .Y .Z) (by decide)) [.X] [.X, .Y, .Z, .Y, .X] [.X, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o y z) * k1 + (1) * s1

/-- S06: `L(xyzxzy) = τ.R 0 x y * τ.o x z * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S06 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x, z, y] = τ.R 0 x y * τ.o x z * τ.o y z := by
  have k1 := walk_W09 h y z x (PL.ord hxyz .Y .Z .X rfl)
  have s1 := stepR1 (t := [.Y]) (q := .Z) (v := .X) (h.inst x y z hxyz (.r1 [.Y] .Z .X) (by decide)) [.Y, .X] [.X, .Y, .Z, .X, .Z, .Y] [.Y, .Z, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x z) * k1 + (1) * s1

/-- S07: `L(xyzyzx) = τ.R x y z * τ.o 0 x * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S07 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, y, z, x] = τ.R x y z * τ.o 0 x * τ.o y z := by
  have k1 := walk_W10 h x y z hxyz
  have s1 := stepR1 (t := [.X]) (q := .Y) (v := .Z) (h.inst x y z hxyz (.r1 [.X] .Y .Z) (by decide)) [.Z, .X] [.X, .Y, .Z, .Y, .Z, .X] [.X, .Y, .Z, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o y z) * k1 + (1) * s1

/-- S08: `L(xyzxyxz) = τ.o x y * τ.o x z * τ.om y`; proved by one rule step (forward chaining). -/
theorem walk_S08 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x, y, x, z] = τ.o x y * τ.o x z * τ.om y := by
  have k1 := walk_W19 h z x y (PL.ord hxyz .Z .X .Y rfl)
  have s1 := stepR1 (t := [.Z]) (q := .X) (v := .Y) (h.inst x y z hxyz (.r1 [.Z] .X .Y) (by decide)) [.Z, .Y, .X] [.X, .Y, .Z, .X, .Y, .X, .Z] [.Z, .X, .Z, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x y) * k1 + (1) * s1

/-- S09: `L(xyzxzxy) = 2 * τ.R 0 x y * τ.R x y z * τ.o x z - τ.o x y * τ.o x z * τ.om z`; proved by one rule step (forward chaining). -/
theorem walk_S09 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x, z, x, y] = 2 * τ.R 0 x y * τ.R x y z * τ.o x z - τ.o x y * τ.o x z * τ.om z := by
  have k1 := walk_W20 h x y z hxyz
  have s1 := stepR1 (t := [.Y]) (q := .X) (v := .Z) (h.inst x y z hxyz (.r1 [.Y] .X .Z) (by decide)) [.Z, .Y, .X] [.X, .Y, .Z, .X, .Z, .X, .Y] [.X, .Y, .Z, .X, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x z) * k1 + (1) * s1

/-- S10: `L(xyzAzxy) = 2 * τ.R 0 x y * τ.R x y z * τ.o 0 z - τ.o 0 z * τ.o x y * τ.om z`; proved by one rule step (forward chaining). -/
theorem walk_S10 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, z, x, y] = 2 * τ.R 0 x y * τ.R x y z * τ.o 0 z - τ.o 0 z * τ.o x y * τ.om z := by
  have k1 := walk_W20 h x y z hxyz
  have s1 := stepR1 (t := [.X, .Y]) (q := .Z) (v := .A) (h.inst x y z hxyz (.r1 [.X, .Y] .Z .A) (by decide)) [.X, .Y] [.X, .Y, .Z, .A, .Z, .X, .Y] [.X, .Y, .Z, .X, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 z) * k1 + (1) * s1

/-- S11: `L(xyzAzyx) = τ.o 0 x * τ.o 0 z * τ.o x y * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S11 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, z, y, x] = τ.o 0 x * τ.o 0 z * τ.o x y * τ.o y z := by
  have k1 := walk_S05 h x y z hxyz
  have s1 := stepR1 (t := [.X, .Y]) (q := .Z) (v := .A) (h.inst x y z hxyz (.r1 [.X, .Y] .Z .A) (by decide)) [.Y, .X] [.X, .Y, .Z, .A, .Z, .Y, .X] [.X, .Y, .Z, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 z) * k1 + (1) * s1

/-- S12: `L(xyzAzyxz) = τ.R 0 x z * τ.o 0 z * τ.o x y * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S12 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, z, y, x, z] = τ.R 0 x z * τ.o 0 z * τ.o x y * τ.o y z := by
  have k1 := walk_S06 h z x y (PL.ord hxyz .Z .X .Y rfl)
  have s1 := stepR1 (t := [.X, .Y]) (q := .Z) (v := .A) (h.inst x y z hxyz (.r1 [.X, .Y] .Z .A) (by decide)) [.Y, .X, .Z] [.X, .Y, .Z, .A, .Z, .Y, .X, .Z] [.Z, .X, .Y, .Z, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o 0 z) * k1 + (1) * s1

/-- S13: `L(xyzxzyx) = τ.o 0 x * τ.o x y * τ.o x z * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S13 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x, z, y, x] = τ.o 0 x * τ.o x y * τ.o x z * τ.o y z := by
  have k1 := walk_S05 h x y z hxyz
  have s1 := stepR1 (t := [.X, .Y]) (q := .Z) (v := .X) (h.inst x y z hxyz (.r1 [.X, .Y] .Z .X) (by decide)) [.Y, .X] [.X, .Y, .Z, .X, .Z, .Y, .X] [.X, .Y, .Z, .Y, .X] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x z) * k1 + (1) * s1

/-- S14: `L(xyzxyxzy) = τ.R 0 x y * τ.o x y * τ.o x z * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S14 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x, y, x, z, y] = τ.R 0 x y * τ.o x y * τ.o x z * τ.o y z := by
  have k1 := walk_S06 h x y z hxyz
  have s1 := stepR1 (t := [.Y, .Z]) (q := .X) (v := .Y) (h.inst x y z hxyz (.r1 [.Y, .Z] .X .Y) (by decide)) [.Z, .Y, .X] [.X, .Y, .Z, .X, .Y, .X, .Z, .Y] [.X, .Y, .Z, .X, .Z, .Y] (by decide) (by decide)
  walk_nf
  linear_combination (τ.o x y) * k1 + (1) * s1

/-- S15: `L(xyAzyxzy) = 4 * τ.R 0 x y * τ.R 0 y z * τ.R x y z - 2 * τ.R 0 x y * τ.o y z * τ.om x + τ.R 0 x z * τ.o 0 y * τ.o x y * τ.o y z - 2 * τ.R x y z * τ.o 0 y * τ.om y`; proved by one rule step (forward chaining). -/
theorem walk_S15 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, 0, z, y, x, z, y] = 4 * τ.R 0 x y * τ.R 0 y z * τ.R x y z - 2 * τ.R 0 x y * τ.o y z * τ.om x + τ.R 0 x z * τ.o 0 y * τ.o x y * τ.o y z - 2 * τ.R x y z * τ.o 0 y * τ.om y := by
  have k1 := walk_W20 h y z x (PL.ord hxyz .Y .Z .X rfl)
  have k2 := walk_W46 h y x z (PL.ord hxyz .Y .X .Z rfl)
  have s1 := stepR2 (t := []) (q := .A) (s := .Y) (m := .X) (h.inst x y z hxyz (.r2 [] .A .Y .X) (by decide)) [.Z, .Y, .X, .Z, .Y] [.Y, .X, .A, .Z, .Y, .X, .Z, .Y] [.X, .Y, .A, .Z, .Y, .X, .Z, .Y] [.Y, .Z, .X, .Y, .Z] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 x y) * k1 + (-1) * k2 + (1) * s1

/-- S16: `L(xyzxyz) = -τ.R 0 x z * τ.o x y * τ.o y z + 2 * τ.R x y z * τ.om y`; proved by one rule step (forward chaining). -/
theorem walk_S16 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x, y, z] = -τ.R 0 x z * τ.o x y * τ.o y z + 2 * τ.R x y z * τ.om y := by
  have k1 := walk_S06 h x z y (PL.ord hxyz .X .Z .Y rfl)
  have k2 := walk_W05 h x y z hxyz
  have s1 := stepR2 (t := []) (q := .X) (s := .Y) (m := .Z) (h.inst x y z hxyz (.r2 [] .X .Y .Z) (by decide)) [.Y, .Z] [.X, .Y, .Z, .X, .Y, .Z] [.X, .Z, .Y, .X, .Y, .Z] [.X, .Y, .Z] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (-1) * k1 + (2 * τ.R x y z) * k2 + (1) * s1

/-- S17: `L(xyzxyzx) = 2 * τ.R x y z ^ 2 * τ.o 0 x - τ.o 0 x * τ.o x y * τ.o x z * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S17 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, x, y, z, x] = 2 * τ.R x y z ^ 2 * τ.o 0 x - τ.o 0 x * τ.o x y * τ.o x z * τ.o y z := by
  have k1 := walk_S13 h x z y (PL.ord hxyz .X .Z .Y rfl)
  have k2 := walk_W10 h x y z hxyz
  have s1 := stepR2 (t := []) (q := .X) (s := .Y) (m := .Z) (h.inst x y z hxyz (.r2 [] .X .Y .Z) (by decide)) [.Y, .Z, .X] [.X, .Y, .Z, .X, .Y, .Z, .X] [.X, .Z, .Y, .X, .Y, .Z, .X] [.X, .Y, .Z, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (-1) * k1 + (2 * τ.R x y z) * k2 + (1) * s1

/-- S18: `L(xyzAzxyz) = -τ.R 0 x z * τ.o 0 z * τ.o x y * τ.o y z + 2 * τ.R x y z * τ.o 0 z * τ.om y`; proved by one rule step (forward chaining). -/
theorem walk_S18 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, z, x, y, z] = -τ.R 0 x z * τ.o 0 z * τ.o x y * τ.o y z + 2 * τ.R x y z * τ.o 0 z * τ.om y := by
  have k1 := walk_S12 h x y z hxyz
  have k2 := walk_W11 h z y x (PL.ord hxyz .Z .Y .X rfl)
  have s1 := stepR2 (t := []) (q := .Z) (s := .Y) (m := .X) (h.inst x y z hxyz (.r2 [] .Z .Y .X) (by decide)) [.A, .Z, .Y, .X] [.X, .Y, .Z, .A, .Z, .X, .Y, .Z] [.X, .Y, .Z, .A, .Z, .Y, .X, .Z] [.Z, .A, .Z, .Y, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (-1) * k1 + (2 * τ.R x y z) * k2 + (1) * s1

/-- S19: `L(xyzAyzx) = 2 * τ.R 0 y z * τ.R x y z * τ.o 0 x - τ.o 0 x * τ.o y z * τ.om x`; proved by one rule step (forward chaining). -/
theorem walk_S19 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, y, z, x] = 2 * τ.R 0 y z * τ.R x y z * τ.o 0 x - τ.o 0 x * τ.o y z * τ.om x := by
  have k1 := walk_W10 h x y z hxyz
  have k2 := walk_W38 h x y z hxyz
  have s1 := stepR2 (t := [.X]) (q := .Y) (s := .A) (m := .Z) (h.inst x y z hxyz (.r2 [.X] .Y .A .Z) (by decide)) [.Z, .X] [.X, .Y, .A, .Z, .Y, .Z, .X] [.X, .Y, .Z, .A, .Y, .Z, .X] [.X, .Y, .Z, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 y z) * k1 + (-1) * k2 + (1) * s1

/-- S20: `L(xyzAyxzy) = -4 * τ.R 0 x y * τ.R 0 y z * τ.R x y z + 2 * τ.R 0 x y * τ.o y z * τ.om x - τ.R 0 x z * τ.o 0 y * τ.o x y * τ.o y z + 2 * τ.R 0 y z * τ.o x y * τ.om z + 2 * τ.R x y z * τ.o 0 y * τ.om y`; proved by one rule step (forward chaining). -/
theorem walk_S20 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, y, x, z, y] = -4 * τ.R 0 x y * τ.R 0 y z * τ.R x y z + 2 * τ.R 0 x y * τ.o y z * τ.om x - τ.R 0 x z * τ.o 0 y * τ.o x y * τ.o y z + 2 * τ.R 0 y z * τ.o x y * τ.om z + 2 * τ.R x y z * τ.o 0 y * τ.om y := by
  have k1 := walk_S15 h x y z hxyz
  have k2 := walk_W19 h x y z hxyz
  have s1 := stepR2 (t := [.X]) (q := .Y) (s := .A) (m := .Z) (h.inst x y z hxyz (.r2 [.X] .Y .A .Z) (by decide)) [.X, .Z, .Y] [.X, .Y, .A, .Z, .Y, .X, .Z, .Y] [.X, .Y, .Z, .A, .Y, .X, .Z, .Y] [.X, .Y, .X, .Z, .Y] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (-1) * k1 + (2 * τ.R 0 y z) * k2 + (1) * s1

/-- S21: `L(xyzAyzxy) = 4 * τ.R 0 x y * τ.R 0 y z * τ.R x y z - 2 * τ.R 0 x y * τ.o y z * τ.om x + τ.R 0 x z * τ.o 0 y * τ.o x y * τ.o y z - 2 * τ.R 0 y z * τ.o x y * τ.om z`; proved by one rule step (forward chaining). -/
theorem walk_S21 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, y, z, x, y] = 4 * τ.R 0 x y * τ.R 0 y z * τ.R x y z - 2 * τ.R 0 x y * τ.o y z * τ.om x + τ.R 0 x z * τ.o 0 y * τ.o x y * τ.o y z - 2 * τ.R 0 y z * τ.o x y * τ.om z := by
  have k1 := walk_W20 h x y z hxyz
  have k2 := walk_W47 h x y z hxyz
  have s1 := stepR2 (t := [.X]) (q := .Y) (s := .A) (m := .Z) (h.inst x y z hxyz (.r2 [.X] .Y .A .Z) (by decide)) [.Z, .X, .Y] [.X, .Y, .A, .Z, .Y, .Z, .X, .Y] [.X, .Y, .Z, .A, .Y, .Z, .X, .Y] [.X, .Y, .Z, .X, .Y] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (2 * τ.R 0 y z) * k1 + (-1) * k2 + (1) * s1

/-- S22: `L(xyzAxyz) = -τ.o 0 x * τ.o 0 z * τ.o x y * τ.o y z + 2 * τ.om y ^ 2`; proved by one rule step (forward chaining). -/
theorem walk_S22 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, x, y, z] = -τ.o 0 x * τ.o 0 z * τ.o x y * τ.o y z + 2 * τ.om y ^ 2 := by
  have k1 := walk_S11 h z y x (PL.ord hxyz .Z .Y .X rfl)
  have k2 := walk_W05 h x y z hxyz
  have s1 := stepL2 (a := .X) (b := .Y) (c := .Z) (h.r3 _ _ _ (PL.ord hxyz .X .Y .Z rfl)) [.X, .Y, .Z] [.X, .Y, .Z, .A, .X, .Y, .Z] [.Z, .Y, .X, .A, .X, .Y, .Z] [.X, .Y, .Z] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (-1) * k1 + (2 * τ.om y) * k2 + (1) * s1

/-- S23: `L(xyzAxyzx) = -τ.R 0 x z * τ.o 0 x * τ.o x y * τ.o y z + 2 * τ.R x y z * τ.o 0 x * τ.om y`; proved by one rule step (forward chaining). -/
theorem walk_S23 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, x, y, z, x] = -τ.R 0 x z * τ.o 0 x * τ.o x y * τ.o y z + 2 * τ.R x y z * τ.o 0 x * τ.om y := by
  have k1 := walk_S12 h z y x (PL.ord hxyz .Z .Y .X rfl)
  have k2 := walk_W10 h x y z hxyz
  have s1 := stepL2 (a := .X) (b := .Y) (c := .Z) (h.r3 _ _ _ (PL.ord hxyz .X .Y .Z rfl)) [.X, .Y, .Z, .X] [.X, .Y, .Z, .A, .X, .Y, .Z, .X] [.Z, .Y, .X, .A, .X, .Y, .Z, .X] [.X, .Y, .Z, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (-1) * k1 + (2 * τ.om y) * k2 + (1) * s1

/-- S24: `L(xyzAxzyx) = τ.R 0 x z * τ.o 0 x * τ.o x y * τ.o y z`; proved by one rule step (forward chaining). -/
theorem walk_S24 (h : UsedRules W τ) (x y z : Letter) (hxyz : IsOrderingBCD x y z) :
    W.L [x, y, z, 0, x, z, y, x] = τ.R 0 x z * τ.o 0 x * τ.o x y * τ.o y z := by
  have k1 := walk_S18 h z y x (PL.ord hxyz .Z .Y .X rfl)
  have k2 := walk_W10 h x y z hxyz
  have s1 := stepL2 (a := .X) (b := .Y) (c := .Z) (h.r3 _ _ _ (PL.ord hxyz .X .Y .Z rfl)) [.X, .Z, .Y, .X] [.X, .Y, .Z, .A, .X, .Z, .Y, .X] [.Z, .Y, .X, .A, .X, .Z, .Y, .X] [.X, .Y, .Z, .X] (by decide) (by decide) (by decide)
  walk_nf
  linear_combination (-1) * k1 + (2 * τ.om y) * k2 + (1) * s1


end AlbertSequential.LengthSeven.LemmaA
