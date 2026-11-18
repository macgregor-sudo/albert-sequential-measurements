/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.WordsAndCertificates
public import PurityResiduals

/-! # Length seven: basic combinatorial and trace data

Letters `A, B, C, D` are `0, 1, 2, 3 : Fin 4` (the order of `fixedS` and
`maximizerConfig`).  Words of outcomes reuse
`Word (Fin 4) = List (Fin 4 × Bool)` in chronological order.

`TraceData` holds the thirteen traces of a quadruple of atoms as functions:
`o a b` (overlaps), `R a b c` (shape invariants), and `om y`, the invariant
`ω_y = Q_(A;xyz)` indexed by the MIDDLE letter `y` (paper lem:cer:short:
`ω_B = ω_1`, `ω_C = ω_2`, `ω_D = ω_3`).  `om 0` carries no meaning.  The double
pairing `t_(Ax|yz) = τ(p_A∘p_x, p_y∘p_z)` is not separate data: for `{x,y,z} =
{B,C,D}` it equals `(ω_y + ω_z)/2` (`TraceData.dpair`).  No positivity, no trace
relation and no genericity is assumed. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

open AlbertSequential

/-- The four test letters; `A = 0`, `B = 1`, `C = 2`, `D = 3`. -/
abbrev Letter := Fin 4

/-- The thirteen traces as functions on letters.  `om y` is `ω_y`, indexed by the
middle letter of the Jordan triple (lem:cer:short); `om 0` is unused. -/
structure TraceData where
  o : Letter → Letter → ℝ
  R : Letter → Letter → Letter → ℝ
  om : Letter → ℝ
  o_symm : ∀ a b, o a b = o b a
  R_symm12 : ∀ a b c, R a b c = R b a c
  R_symm23 : ∀ a b c, R a b c = R a c b

namespace TraceData

variable (τ : TraceData)

/-- Double pairing `t_(Ax|yz) = (ω_y + ω_z)/2` for an ordering `x,y,z` of `B,C,D`. -/
def dpair (y z : Letter) : ℝ := (τ.om y + τ.om z) / 2

/-- One interior "no": `⟨p_n, U_{e-p_a} p_p⟩ = o_pn − 2 R_pan + o_pa o_an` (paper (W2)). -/
def noConst (p a n : Letter) : ℝ := τ.o p n - 2 * τ.R p a n + τ.o p a * τ.o a n

/-- Purity constant after a yes on `q` for the two-outcome word `(v^b, w)`:
`⟨p_w, U_{v^b} p_q⟩`. -/
def c2 (b : Bool) (q v w : Letter) : ℝ :=
  if b then τ.o q v * τ.o v w else τ.noConst q v w

/-- Purity constant after a yes on `A` for the three-outcome word `(x^a, y^b, z)`:
`⟨p_z, U_{y^b} U_{x^a} p_A⟩`, for `x,y,z` an ordering of `B,C,D`. -/
def c3 (a b : Bool) (x y z : Letter) : ℝ :=
  match a, b with
  | true, true => τ.o 0 x * τ.o x y * τ.o y z
  | true, false => τ.o 0 x * τ.noConst x y z
  | false, true => τ.noConst 0 x y * τ.o y z
  | false, false =>
      τ.o 0 z - 2 * τ.R 0 x z + τ.o 0 x * τ.o x z
        - 2 * (τ.R 0 y z - 2 * τ.dpair y z + τ.o 0 x * τ.R x y z)
        + τ.noConst 0 x y * τ.o y z

/-- The (P3) constant `c_xyz = o_Az − 2R_Axz − 2R_Ayz + 4 t_(Ax|yz)`. -/
def p3Const (x y z : Letter) : ℝ :=
  τ.o 0 z - 2 * τ.R 0 x z - 2 * τ.R 0 y z + 4 * τ.dpair y z

/-- The signed sum of the four (P3) purity constants is the (P3) constant. -/
theorem c3_signed_sum (x y z : Letter) :
    τ.c3 false false x y z - τ.c3 false true x y z - τ.c3 true false x y z
      + τ.c3 true true x y z = τ.p3Const x y z := by
  simp only [c3, noConst, p3Const]
  ring

/-- Chain product `o_{a_0 a_1} o_{a_1 a_2} ⋯` of consecutive overlaps (paper (W1)). -/
def chainProd : List Letter → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: r => τ.o a b * chainProd (b :: r)

theorem chainProd_cons_cons (a b : Letter) (r : List Letter) :
    τ.chainProd (a :: b :: r) = τ.o a b * τ.chainProd (b :: r) := rfl

/-- Splitting a chain at an interior junction. -/
theorem chainProd_split (c : Letter) (u : List Letter) (b : Letter) (m : List Letter) :
    τ.chainProd (c :: (u ++ b :: m)) =
      τ.chainProd (c :: u) * τ.o (u.getLastD c) b * τ.chainProd (b :: m) := by
  induction u generalizing c with
  | nil => simp [chainProd]
  | cons d u ih =>
    rw [List.cons_append, chainProd_cons_cons, ih d, chainProd_cons_cons,
      List.getLastD_cons]
    ring

end TraceData

/-- All-yes outcome word of a letter list. -/
def yesWord (u : List Letter) : Word Letter := u.map (fun a => (a, true))

@[simp] theorem yesWord_nil : yesWord [] = [] := rfl
@[simp] theorem yesWord_cons (a : Letter) (u : List Letter) :
    yesWord (a :: u) = (a, true) :: yesWord u := rfl
@[simp] theorem yesWord_append (u v : List Letter) :
    yesWord (u ++ v) = yesWord u ++ yesWord v := List.map_append ..
@[simp] theorem yesWord_reverse (u : List Letter) :
    yesWord u.reverse = (yesWord u).reverse := List.map_reverse ..

/-- `x, y, z` is an ordering of `B, C, D`. -/
def IsOrderingBCD (x y z : Letter) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z

instance (x y z : Letter) : Decidable (IsOrderingBCD x y z) := by
  unfold IsOrderingBCD; infer_instance

/-- Words read from `p_A`: a leading "yes on `A`" costs nothing.  Forcing words are
listed in this normal form, so a word set `S` may omit the leading yes on `A`. -/
def dropYesA : Word Letter → Word Letter
  | [] => []
  | a :: u => if a = (0, true) then u else a :: u

theorem dropYesA_length_le (u : Word Letter) : (dropYesA u).length ≤ u.length := by
  cases u with
  | nil => simp [dropYesA]
  | cons a u => simp only [dropYesA]; split_ifs <;> simp

/-! ## The twenty-eight words of eq:cer:W28 (time order, frame = last letter) -/

/-- The 28 path words of eq:cer:W28 in the printed order: frame `A` (indices 0–6),
frame `B` (7–13), frame `C` (14–20), frame `D` (21–27). -/
def word28 : Fin 28 → List Letter :=
  ![[], [2, 1, 0], [3, 2, 0], [1, 3, 0], [3, 2, 1, 0], [2, 3, 1, 0], [3, 1, 2, 0],
    [1], [2, 1], [3, 1], [2, 3, 0, 1], [3, 2, 1], [2, 3, 1], [1, 3, 2, 1],
    [2], [3, 2], [1, 2], [3, 1, 0, 2], [1, 3, 2], [3, 1, 2], [2, 1, 3, 2],
    [3], [1, 3], [2, 3], [1, 2, 0, 3], [2, 1, 3], [1, 2, 3], [3, 2, 1, 3]]

/-- Frame of a 28-word: `A, B, C, D` for indices `0–6, 7–13, 14–20, 21–27`. -/
def frame28 (i : Fin 28) : Letter := ⟨i.val / 7, by omega⟩

/-- Frame = last letter (with `A` for the empty word). -/
theorem frame28_eq_last : ∀ i : Fin 28, (word28 i).getLastD 0 = frame28 i := by decide

/-! ## Computable walk normalisation -/

/-- Merge equal neighbours (`P_a P_a = P_a`). -/
def mergeAdj : List Letter → List Letter
  | [] => []
  | [a] => [a]
  | a :: b :: r => if a = b then mergeAdj (b :: r) else a :: mergeAdj (b :: r)

/-- Delete leading letters `A` (`L(A w) = L(w)`). -/
def stripLead : List Letter → List Letter
  | [] => []
  | a :: r => if a = 0 then stripLead r else a :: r

/-- Delete trailing letters `A`. -/
def stripTrail (w : List Letter) : List Letter := (stripLead w.reverse).reverse

/-- Lexicographic `≤` on letter lists (Boolean, computable). -/
def lexLE : List Letter → List Letter → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: r, b :: s => if a.val < b.val then true else if b.val < a.val then false else lexLE r s

/-- Canonical walk representative: merge equal neighbours, strip end `A`'s, then the
lexicographically smaller of the word and its reverse.  `L (canon w) = L w`
(`WalkForm.L_canon`); entries are matched to walk lemmas by evaluating `canon`. -/
def canon (w : List Letter) : List Letter :=
  let m := stripTrail (stripLead (mergeAdj w))
  if lexLE m m.reverse then m else m.reverse

example : canon [0, 1, 2, 2, 0] = [1, 2] := by decide
example : canon [3, 2, 1, 0] = [1, 2, 3] := by decide

end AlbertSequential.LengthSeven
