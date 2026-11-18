/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RobustCert.Formal
public import Mathlib.Tactic.FinCases

/-! # Octonionic table values on the words of the decompositions

`TraceTable` holds thirteen rational trace values; `TraceTable.Holds T τ` says `τ` has them.
`fvalQ` evaluates a table word by (W1)/(W2) (`TableValues.chain`, `TableValues.oneNo`), and
`Defect.xok` checks that a defect's constant is the purity constant of its shape, so that the
residual functional `X = g(t q v v̄ q) − 2c g(t q v) + c² g(t q)` vanishes on every table with
`TableValues` (`TableValues.mid*`/`long*`).  Soundness: `fvalQ_sound`, `xok_sound`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential AlbertSequential.LengthSeven

/-- Thirteen rational trace values, order of `traceVars`. -/
structure TraceTable where
  oAB : ℚ
  oAC : ℚ
  oAD : ℚ
  oBC : ℚ
  oBD : ℚ
  oCD : ℚ
  rABC : ℚ
  rABD : ℚ
  rACD : ℚ
  rBCD : ℚ
  wB : ℚ
  wC : ℚ
  wD : ℚ

/-- `τ` carries the trace values `T`. -/
structure TraceTable.Holds (T : TraceTable) (τ : TraceData) : Prop where
  oAB : τ.o 0 1 = T.oAB
  oAC : τ.o 0 2 = T.oAC
  oAD : τ.o 0 3 = T.oAD
  oBC : τ.o 1 2 = T.oBC
  oBD : τ.o 1 3 = T.oBD
  oCD : τ.o 2 3 = T.oCD
  rABC : τ.R 0 1 2 = T.rABC
  rABD : τ.R 0 1 3 = T.rABD
  rACD : τ.R 0 2 3 = T.rACD
  rBCD : τ.R 1 2 3 = T.rBCD
  wB : τ.om 1 = T.wB
  wC : τ.om 2 = T.wC
  wD : τ.om 3 = T.wD

namespace TraceTable

variable (T : TraceTable)

def oQ (a b : Letter) : ℚ :=
  match a.val, b.val with
  | 0, 1 => T.oAB | 1, 0 => T.oAB | 0, 2 => T.oAC | 2, 0 => T.oAC
  | 0, 3 => T.oAD | 3, 0 => T.oAD | 1, 2 => T.oBC | 2, 1 => T.oBC
  | 1, 3 => T.oBD | 3, 1 => T.oBD | 2, 3 => T.oCD | 3, 2 => T.oCD
  | _, _ => 0

/-- `R` for three distinct letters, by the missing letter. -/
def RQ (a b c : Letter) : ℚ :=
  match 6 - (a.val + b.val + c.val) with
  | 3 => T.rABC | 2 => T.rABD | 1 => T.rACD | 0 => T.rBCD | _ => 0

def omQ (y : Letter) : ℚ :=
  match y.val with
  | 1 => T.wB | 2 => T.wC | 3 => T.wD | _ => 0

def noConstQ (p a n : Letter) : ℚ := T.oQ p n - 2 * T.RQ p a n + T.oQ p a * T.oQ a n

def c2Q (b : Bool) (q v w : Letter) : ℚ := if b then T.oQ q v * T.oQ v w else T.noConstQ q v w

def c3Q (a b : Bool) (x y z : Letter) : ℚ :=
  match a, b with
  | true, true => T.oQ 0 x * T.oQ x y * T.oQ y z
  | true, false => T.oQ 0 x * T.noConstQ x y z
  | false, true => T.noConstQ 0 x y * T.oQ y z
  | false, false =>
      T.oQ 0 z - 2 * T.RQ 0 x z + T.oQ 0 x * T.oQ x z
        - 2 * (T.RQ 0 y z - 2 * ((T.omQ y + T.omQ z) / 2) + T.oQ 0 x * T.RQ x y z)
        + T.noConstQ 0 x y * T.oQ y z

variable {T} {τ : TraceData}

theorem Holds.o (h : T.Holds τ) (a b : Letter) (hab : a ≠ b) : τ.o a b = T.oQ a b := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact absurd rfl hab
    | (simp [oQ, h.oAB, h.oAC, h.oAD, h.oBC, h.oBD, h.oCD]; done)
    | (rw [τ.o_symm]; simp [oQ, h.oAB, h.oAC, h.oAD, h.oBC, h.oBD, h.oCD]; done)

theorem Holds.R (h : T.Holds τ) (a b c : Letter) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    τ.R a b c = T.RQ a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first
    | exact absurd rfl hab
    | exact absurd rfl hbc
    | exact absurd rfl hac
    | (simp [RQ, h.rABC, h.rABD, h.rACD, h.rBCD]; done)
    | (rw [τ.R_symm12]; simp [RQ, h.rABC, h.rABD, h.rACD, h.rBCD]; done)
    | (rw [τ.R_symm23]; simp [RQ, h.rABC, h.rABD, h.rACD, h.rBCD]; done)
    | (rw [τ.R_symm12, τ.R_symm23]; simp [RQ, h.rABC, h.rABD, h.rACD, h.rBCD]; done)
    | (rw [τ.R_symm23, τ.R_symm12]; simp [RQ, h.rABC, h.rABD, h.rACD, h.rBCD]; done)
    | (rw [τ.R_symm12, τ.R_symm23, τ.R_symm12]; simp [RQ, h.rABC, h.rABD, h.rACD, h.rBCD]; done)

theorem Holds.om (h : T.Holds τ) (y : Letter) (hy : y ≠ 0) : τ.om y = T.omQ y := by
  fin_cases y <;> first | exact absurd rfl hy | simp [omQ, h.wB, h.wC, h.wD]

theorem Holds.noConst (h : T.Holds τ) (p a n : Letter) (hpa : p ≠ a) (han : a ≠ n) (hpn : p ≠ n) :
    τ.noConst p a n = T.noConstQ p a n := by
  simp only [TraceData.noConst, noConstQ, h.o p n hpn, h.o p a hpa, h.o a n han, h.R p a n hpa han hpn]
  push_cast
  ring

theorem Holds.c2 (h : T.Holds τ) (b : Bool) (q v w : Letter) (hqv : q ≠ v) (hvw : v ≠ w)
    (hqw : q ≠ w) : τ.c2 b q v w = T.c2Q b q v w := by
  cases b
  · simp only [TraceData.c2, c2Q, Bool.false_eq_true, ite_false, h.noConst q v w hqv hvw hqw]
  · simp only [TraceData.c2, c2Q, ite_true, h.o q v hqv, h.o v w hvw]
    push_cast
    ring

theorem Holds.c3 (h : T.Holds τ) (a b : Bool) (x y z : Letter) (hord : IsOrderingBCD x y z) :
    τ.c3 a b x y z = T.c3Q a b x y z := by
  obtain ⟨hx, hy, hz, hxy, hyz, hxz⟩ := hord
  cases a <;> cases b <;>
    simp only [TraceData.c3, c3Q, TraceData.dpair, h.o 0 x (Ne.symm hx), h.o x y hxy, h.o y z hyz,
      h.o x z hxz, h.o 0 y (Ne.symm hy), h.o 0 z (Ne.symm hz),
      h.noConst x y z hxy hyz hxz, h.noConst 0 x y (Ne.symm hx) hxy (Ne.symm hy),
      h.R 0 x z (Ne.symm hx) hxz (Ne.symm hz), h.R 0 y z (Ne.symm hy) hyz (Ne.symm hz),
      h.R x y z hxy hyz hxz, h.om y hy, h.om z hz] <;>
    push_cast <;> ring

end TraceTable

/-! ## Table values -/

/-- Chain product `o_{a0 a1} o_{a1 a2} ⋯` (distinct neighbours required). -/
def chainQ (T : TraceTable) : List Letter → Option ℚ
  | [] => some 1
  | [_] => some 1
  | a :: b :: r => if a = b then none else (chainQ T (b :: r)).map (fun x => T.oQ a b * x)

theorem chainQ_sound {T : TraceTable} {τ : TraceData} (h : T.Holds τ) :
    ∀ (l : List Letter) (q : ℚ), chainQ T l = some q → τ.chainProd l = q
  | [], q, hq => by
    simp only [chainQ, Option.some.injEq] at hq
    subst hq; simp [TraceData.chainProd]
  | [_], q, hq => by
    simp only [chainQ, Option.some.injEq] at hq
    subst hq; simp [TraceData.chainProd]
  | a :: b :: r, q, hq => by
    simp only [chainQ] at hq
    split at hq
    · simp at hq
    · rename_i hab
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hq
      rw [TraceData.chainProd_cons_cons, chainQ_sound h (b :: r) x hx, h.o a b hab]
      push_cast
      ring

/-- Table value of a table word from `p_A`, by (W1)/(W2). -/
def fvalQ (T : TraceTable) : TabWord → Option ℚ
  | .yes u => chainQ T (0 :: u)
  | .one u a n r =>
    match chainQ T (0 :: u), chainQ T (n :: r) with
    | some c1, some c2 =>
      if u.getLastD 0 ≠ a ∧ a ≠ n ∧ u.getLastD 0 ≠ n then
        some (c1 * T.noConstQ (u.getLastD 0) a n * c2)
      else none
    | _, _ => none

theorem fvalQ_sound {T : TraceTable} {τ : TraceData} {f : Word Letter → ℝ} (h : T.Holds τ)
    (hT : TableValues τ f) (w : TabWord) (q : ℚ) (hq : fvalQ T w = some q) : f w.toWord = q := by
  cases w with
  | yes u =>
    simp only [fvalQ] at hq
    simp only [TabWord.toWord]
    rw [hT.chain u, chainQ_sound h _ q hq]
  | one u a n r =>
    simp only [fvalQ] at hq
    simp only [TabWord.toWord]
    rw [hT.oneNo u a n r]
    split at hq
    · rename_i c1 c2 h1 h2
      split at hq
      · rename_i hd
        obtain ⟨hpa, han, hpn⟩ := hd
        simp only [Option.some.injEq] at hq
        subst hq
        rw [chainQ_sound h _ c1 h1, chainQ_sound h _ c2 h2, h.noConst _ a n hpa han hpn]
        push_cast
        ring
      · simp at hq
    · simp at hq

/-! ## Defect constants -/

/-- The defect's constant is the purity constant of its shape (R1, R2 / two-letter, three-letter at `A`). -/
def Defect.xok (T : TraceTable) (d : Defect) : Bool :=
  match d.v with
  | [(v1, true)] => decide (d.q ≠ v1) && decide (d.c = T.oQ d.q v1)
  | [(v1, b), (w, true)] => decide (d.q ≠ v1 ∧ v1 ≠ w ∧ d.q ≠ w) && decide (d.c = T.c2Q b d.q v1 w)
  | [(x, a), (y, b), (z, true)] =>
      decide (d.q = 0) && decide (IsOrderingBCD x y z) && decide (d.c = T.c3Q a b x y z)
  | _ => false

theorem xok_sound {T : TraceTable} {τ : TraceData} {f : Word Letter → ℝ} (h : T.Holds τ)
    (hT : TableValues τ f) (d : Defect) (hx : d.xok T = true) :
    f d.long - 2 * (d.c : ℝ) * f d.mid + (d.c : ℝ) ^ 2 * f d.short = 0 := by
  unfold Defect.xok at hx
  split at hx
  · rename_i v1 hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨hq, hc⟩ := hx
    have e1 : d.long = d.t ++ [(d.q, true), (v1, true), (d.q, true)] := by
      simp [Defect.long, hv, purityMirror]
    have e2 : d.mid = d.t ++ [(d.q, true), (v1, true)] := by simp [Defect.mid, hv]
    rw [e1, e2, Defect.short, hT.long1, hT.mid1, h.o _ _ hq, hc]
    ring
  · rename_i v1 b w hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨hqv, hvw, hqw⟩, hc⟩ := hx
    have e1 : d.long = d.t ++ [(d.q, true), (v1, b), (w, true), (v1, b), (d.q, true)] := by
      simp [Defect.long, hv, purityMirror]
    have e2 : d.mid = d.t ++ [(d.q, true), (v1, b), (w, true)] := by simp [Defect.mid, hv]
    rw [e1, e2, Defect.short, hT.long2, hT.mid2, h.c2 b _ _ _ hqv hvw hqw, hc]
    ring
  · rename_i x a y b z hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨hq0, hord⟩, hc⟩ := hx
    have e1 : d.long = d.t ++ [(0, true), (x, a), (y, b), (z, true), (y, b), (x, a), (0, true)] := by
      simp [Defect.long, hv, purityMirror, hq0]
    have e2 : d.mid = d.t ++ [(0, true), (x, a), (y, b), (z, true)] := by
      simp [Defect.mid, hv, hq0]
    have e3 : d.short = d.t ++ [(0, true)] := by simp [Defect.short, hq0]
    rw [e1, e2, e3, hT.long3 _ _ _ _ _ _ hord, hT.mid3 _ _ _ _ _ _ hord, h.c3 a b x y z hord, hc]
    ring
  · simp at hx

end AlbertSequential.LengthSeven.Robust
