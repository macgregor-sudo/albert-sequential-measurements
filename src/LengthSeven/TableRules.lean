/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.WalkForm
public import Mathlib.Tactic.LinearCombination

/-! # Table hypotheses and the vector rules they force

Two separate inputs:

* `WalkForm.Reproduces W S f`: the walk form reproduces the table `f` on an
  ARBITRARY word set `S` (words read from `p_A`).  Both the e/3 length-seven form
  and the five-test budget form are instances; only the membership of the
  forcing words listed below is ever used (`Covers`).
* `TableValues τ f`: what the Albert table satisfies, stated for ALL words,
  with the purity constants as explicit polynomials in the thirteen traces.
  This is the Albert-side interface; it mentions no octonions.

From these, the vector identities of lem:cer:short are derived as `Eqv`
statements (equality after pairing), inside arbitrary longer words (suffix `r`):
(R1_t), (R2_t), the pair identity (P3), Lemma 2 / (R3_0) from three (P3)
instances, and Lemma D (one-no polarisation).  Each rule lists its forcing words;
`Covers S ws` says every forcing word, after deleting a leading yes on `A`, is in
`S`.  For concrete `S` and concrete letters, `Covers` is decidable. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

open AlbertSequential

/-! ## The two hypotheses -/

namespace WalkForm
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The walk form reproduces the table `f` (probabilities from `p_A`) on `S`. -/
def Reproduces (W : WalkForm V) (S : Set (Word Letter)) (f : Word Letter → ℝ) : Prop :=
  ∀ u ∈ S, W.normSq (W.vec u) = f u

end WalkForm

/-- Albert-side table values (from `p_A`), for all histories `t` and letters.  The
constants are those of lem:purity / lem:cer:short:
`⟨p_v, p_q⟩ = o_qv`, `⟨p_w, U_{v^b} p_q⟩ = c2 b q v w`,
`⟨p_z, U_{y^b} U_{x^a} p_A⟩ = c3 a b x y z`. -/
structure TableValues (τ : TraceData) (f : Word Letter → ℝ) : Prop where
  empty : f [] = 1
  yesA_head : ∀ u : Word Letter, f ((0, true) :: u) = f u
  mid1 : ∀ (t : Word Letter) (q v : Letter),
    f (t ++ [(q, true), (v, true)]) = τ.o q v * f (t ++ [(q, true)])
  long1 : ∀ (t : Word Letter) (q v : Letter),
    f (t ++ [(q, true), (v, true), (q, true)]) = τ.o q v ^ 2 * f (t ++ [(q, true)])
  mid2 : ∀ (t : Word Letter) (q v w : Letter) (b : Bool),
    f (t ++ [(q, true), (v, b), (w, true)]) = τ.c2 b q v w * f (t ++ [(q, true)])
  long2 : ∀ (t : Word Letter) (q v w : Letter) (b : Bool),
    f (t ++ [(q, true), (v, b), (w, true), (v, b), (q, true)]) =
      τ.c2 b q v w ^ 2 * f (t ++ [(q, true)])
  mid3 : ∀ (t : Word Letter) (x y z : Letter) (a b : Bool), IsOrderingBCD x y z →
    f (t ++ [(0, true), (x, a), (y, b), (z, true)]) = τ.c3 a b x y z * f (t ++ [(0, true)])
  long3 : ∀ (t : Word Letter) (x y z : Letter) (a b : Bool), IsOrderingBCD x y z →
    f (t ++ [(0, true), (x, a), (y, b), (z, true), (y, b), (x, a), (0, true)]) =
      τ.c3 a b x y z ^ 2 * f (t ++ [(0, true)])

namespace TableValues

variable {τ : TraceData} {f : Word Letter → ℝ} (hT : TableValues τ f)
include hT

theorem f_dropYesA (u : Word Letter) : f (dropYesA u) = f u := by
  cases u with
  | nil => rfl
  | cons a u =>
    simp only [dropYesA]
    split_ifs with h
    · subst h; exact (hT.yesA_head u).symm
    · rfl

/-- All-yes continuation of a word ending in a yes on `q`. -/
theorem yes_tail (w : Word Letter) (q : Letter) (r : List Letter) :
    f (w ++ (q, true) :: yesWord r) = f (w ++ [(q, true)]) * τ.chainProd (q :: r) := by
  induction r generalizing w q with
  | nil => simp [TraceData.chainProd]
  | cons n r ih =>
    have e1 : w ++ (q, true) :: yesWord (n :: r) = (w ++ [(q, true)]) ++ (n, true) :: yesWord r := by
      simp
    have e2 : (w ++ [(q, true)]) ++ [(n, true)] = w ++ [(q, true), (n, true)] := by simp
    rw [e1, ih, e2, hT.mid1, TraceData.chainProd_cons_cons]
    ring

/-- (W1): all-yes words from `p_A` have the chain value. -/
theorem chain (u : List Letter) : f (yesWord u) = τ.chainProd (0 :: u) := by
  have h := hT.yes_tail [] 0 u
  simp only [List.nil_append] at h
  rw [← hT.yesA_head, h, hT.yesA_head, hT.empty, one_mul]

omit hT in
theorem exists_init (c : Letter) (u : List Letter) : ∃ init, c :: u = init ++ [u.getLastD c] := by
  induction u generalizing c with
  | nil => exact ⟨[], rfl⟩
  | cons d u ih =>
    obtain ⟨init, h⟩ := ih d
    exact ⟨c :: init, by rw [List.getLastD_cons, h]; rfl⟩

/-- (W2): one interior no, `a_0 = A`, `p = a_{i−1}` the last letter of `0 :: u`. -/
theorem oneNo (u : List Letter) (a n : Letter) (r : List Letter) :
    f (yesWord u ++ (a, false) :: yesWord (n :: r)) =
      τ.chainProd (0 :: u) * τ.noConst (u.getLastD 0) a n * τ.chainProd (n :: r) := by
  obtain ⟨init, hi⟩ := exists_init 0 u
  set p := u.getLastD 0
  have hy : (0, true) :: yesWord u = yesWord init ++ [(p, true)] := by
    have := congrArg yesWord hi
    simpa using this
  have hpre : f (yesWord init ++ [(p, true)]) = τ.chainProd (0 :: u) := by
    rw [← hy, hT.yesA_head, hT.chain]
  have e1 : yesWord u ++ (a, false) :: yesWord (n :: r) =
      dropYesA ((yesWord init ++ [(p, true), (a, false)]) ++ (n, true) :: yesWord r) := by
    have : (yesWord init ++ [(p, true), (a, false)]) ++ (n, true) :: yesWord r =
        (0, true) :: (yesWord u ++ (a, false) :: yesWord (n :: r)) := by
      rw [← List.cons_append, hy]; simp
    rw [this]; simp [dropYesA]
  have e2 : (yesWord init ++ [(p, true), (a, false)]) ++ [(n, true)] =
      yesWord init ++ [(p, true), (a, false), (n, true)] := by simp
  rw [e1, hT.f_dropYesA, hT.yes_tail, e2, hT.mid2, hpre]
  simp only [TraceData.c2, Bool.false_eq_true, ↓reduceIte]
  ring

end TableValues

/-! ## Forcing words and coverage -/

/-- The three words of a purity instance `(t, q, v)`: `(t,q,v,v̄,q)`, `(t,q,v)`, `(t,q)`. -/
def purityWords (t : Word Letter) (q : Outcome Letter) (v : Word Letter) : List (Word Letter) :=
  [t ++ [q] ++ v ++ purityMirror v ++ [q], t ++ [q] ++ v, t ++ [q]]

/-- Every word of `ws`, after deleting a leading yes on `A`, lies in `S`. -/
def Covers (S : Set (Word Letter)) (ws : List (Word Letter)) : Prop :=
  ∀ u ∈ ws, dropYesA u ∈ S

instance (S : Set (Word Letter)) [DecidablePred (· ∈ S)] (ws : List (Word Letter)) :
    Decidable (Covers S ws) := by
  unfold Covers; infer_instance

theorem Covers.append {S : Set (Word Letter)} {ws ws' : List (Word Letter)}
    (h : Covers S ws) (h' : Covers S ws') : Covers S (ws ++ ws') := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact h u hu
  · exact h' u hu

theorem Covers.left {S : Set (Word Letter)} {ws ws' : List (Word Letter)}
    (h : Covers S (ws ++ ws')) : Covers S ws := fun u hu => h u (List.mem_append_left _ hu)

theorem Covers.right {S : Set (Word Letter)} {ws ws' : List (Word Letter)}
    (h : Covers S (ws ++ ws')) : Covers S ws' := fun u hu => h u (List.mem_append_right _ hu)

/-- (R1_t) at `q` with letter `v`. -/
def r1Words (t : Word Letter) (q v : Letter) : List (Word Letter) :=
  purityWords t (q, true) [(v, true)]

/-- (R2_t) at `q`, `s` the sandwiched letter (appears twice in the longest words),
`m` the other. -/
def r2Words (t : Word Letter) (q s m : Letter) : List (Word Letter) :=
  purityWords t (q, true) [(m, true)] ++ purityWords t (q, true) [(s, false), (m, true)] ++
    purityWords t (q, true) [(s, true), (m, true)]

/-- The four purity instances of (P3) at `A` on `ξ` for the ordering `(x, y, z)`. -/
def p3PurityWords (x y z : Letter) : List (Word Letter) :=
  purityWords [] (0, true) [(x, false), (y, false), (z, true)] ++
    purityWords [] (0, true) [(x, false), (y, true), (z, true)] ++
    purityWords [] (0, true) [(x, true), (y, false), (z, true)] ++
    purityWords [] (0, true) [(x, true), (y, true), (z, true)]

/-- All forcing words of (P3) for `(x, y, z)`, including (R1_0) at `A` with `z` and
(R2_0) at `A` with sandwiched `y` (letters `y, z`) and sandwiched `x` (letters `x, z`). -/
def p3Words (x y z : Letter) : List (Word Letter) :=
  p3PurityWords x y z ++ r1Words [] 0 z ++ r2Words [] 0 y z ++ r2Words [] 0 x z

/-- Lemma D: the all-yes word, the word with `a` deleted, and the one-no word. -/
def lemmaDWords (u : List Letter) (a n : Letter) (r : List Letter) : List (Word Letter) :=
  [yesWord (u ++ a :: n :: r), yesWord (u ++ n :: r), yesWord u ++ (a, false) :: yesWord (n :: r)]

/-! ## Rules as vector identities -/

namespace WalkForm
variable {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V) (τ : TraceData)

/-- (R1_t): `P_q P_v P_q η = o_qv η`, `η = [t, q]`, inside any suffix `r`. -/
def R1Holds (t : Word Letter) (q v : Letter) : Prop :=
  ∀ r : Word Letter, W.Eqv (W.vec (t ++ [(q, true), (v, true), (q, true)] ++ r))
    (τ.o q v • W.vec (t ++ [(q, true)] ++ r))

/-- (R2_t): `P_q (P_s P_m + P_m P_s) P_q η = 2 R_qsm η`, inside any suffix `r`. -/
def R2Holds (t : Word Letter) (q s m : Letter) : Prop :=
  ∀ r : Word Letter, W.Eqv
    (W.vec (t ++ [(q, true), (s, true), (m, true), (q, true)] ++ r) +
      W.vec (t ++ [(q, true), (m, true), (s, true), (q, true)] ++ r))
    ((2 * τ.R q s m) • W.vec (t ++ [(q, true)] ++ r))

/-- `η^C_{xyz} + η^C_{zyx}` followed by the suffix `r`. -/
def piC (x y z : Letter) (r : Word Letter) : V :=
  W.vec ([(x, true), (y, true), (z, true), (0, true)] ++ r) +
    W.vec ([(z, true), (y, true), (x, true), (0, true)] ++ r)

/-- (P3) for the ordering `(x,y,z)`: `Π_y + Π_z = 4 t_(Ax|yz) ξ = 2(ω_y + ω_z) ξ`. -/
def P3Holds (x y z : Letter) : Prop :=
  ∀ r : Word Letter, W.Eqv (W.piC x y z r + W.piC x z y r)
    ((2 * (τ.om y + τ.om z)) • W.vec r)

/-- (R3_0) = Lemma 2 = paper lem:cer:gram28 (iii): `η^C_{xyz} + η^C_{zyx} = 2 ω_y ξ`. -/
def R3Holds (x y z : Letter) : Prop :=
  ∀ r : Word Letter, W.Eqv (W.piC x y z r) ((2 * τ.om y) • W.vec r)

/-! ### Pure algebra: purity instances ⇒ rules -/

theorem vec_split (t : Word Letter) (a : Outcome Letter) (w r : Word Letter) :
    W.vec (t ++ a :: w ++ r) = W.seqL r (W.seqL w (W.vec (t ++ [a]))) := by
  rw [show t ++ a :: w ++ r = ((t ++ [a]) ++ w) ++ r by simp, vec_append, vec_append]

theorem purityHolds_iff (t : Word Letter) (q : Outcome Letter) (v : Word Letter) (c : ℝ) :
    W.PurityHolds t q v c ↔
      W.Eqv (W.seqL (v ++ purityMirror v ++ [q]) (W.vec (t ++ [q]))) (c • W.vec (t ++ [q])) := by
  unfold PurityHolds
  rw [show t ++ [q] ++ v ++ purityMirror v ++ [q] = (t ++ [q]) ++ (v ++ purityMirror v ++ [q])
    by simp, vec_append]

theorem eqv_tail {x y : V} (r : Word Letter) (h : W.Eqv x y) :
    W.Eqv (W.seqL r x) (W.seqL r y) := h.map_seqL r

theorem vec_prefix_q (t : Word Letter) (q : Outcome Letter) (r : Word Letter) :
    W.vec (t ++ [q] ++ r) = W.seqL r (W.vec (t ++ [q])) := vec_append ..

theorem r1_of_purity (t : Word Letter) (q v : Letter)
    (h : W.PurityHolds t (q, true) [(v, true)] (τ.o q v)) : W.R1Holds τ t q v := by
  intro r
  have h1 := (W.purityHolds_iff _ _ _ _).1 h
  have hl : [((v : Letter), true)] ++ purityMirror [((v : Letter), true)] ++ [((q : Letter), true)] =
      [(v, true), (q, true)] := by simp [purityMirror]
  rw [hl] at h1
  have h2 := h1.map_seqL r
  rw [W.vec_split t (q, true) [(v, true), (q, true)] r, W.vec_prefix_q, ← map_smul]
  exact h2

theorem r2_identity (q s m : Letter) (η : V) :
    W.seqL [(s, true), (m, true), (q, true)] η + W.seqL [(m, true), (s, true), (q, true)] η =
      W.seqL [(m, true), (q, true)] η - W.seqL [(s, false), (m, true), (s, false), (q, true)] η
        + W.seqL [(s, true), (m, true), (s, true), (q, true)] η := by
  simp only [seqL_cons_apply, seqL_nil_apply, op_yes_apply, op_no_apply, map_sub]
  abel

theorem r2_of_purity (t : Word Letter) (q s m : Letter)
    (h1 : W.PurityHolds t (q, true) [(m, true)] (τ.o q m))
    (h2 : W.PurityHolds t (q, true) [(s, false), (m, true)] (τ.c2 false q s m))
    (h3 : W.PurityHolds t (q, true) [(s, true), (m, true)] (τ.c2 true q s m)) :
    W.R2Holds τ t q s m := by
  intro r
  set η := W.vec (t ++ [(q, true)])
  have e1 := (W.purityHolds_iff _ _ _ _).1 h1
  have e2 := (W.purityHolds_iff _ _ _ _).1 h2
  have e3 := (W.purityHolds_iff _ _ _ _).1 h3
  have l1 : [((m : Letter), true)] ++ purityMirror [((m : Letter), true)] ++ [((q : Letter), true)] =
      [(m, true), (q, true)] := by simp [purityMirror]
  have l2 : [((s : Letter), false), ((m : Letter), true)] ++
      purityMirror [((s : Letter), false), ((m : Letter), true)] ++ [((q : Letter), true)] =
      [(s, false), (m, true), (s, false), (q, true)] := by simp [purityMirror]
  have l3 : [((s : Letter), true), ((m : Letter), true)] ++
      purityMirror [((s : Letter), true), ((m : Letter), true)] ++ [((q : Letter), true)] =
      [(s, true), (m, true), (s, true), (q, true)] := by simp [purityMirror]
  rw [l1] at e1
  rw [l2] at e2
  rw [l3] at e3
  have hsum := ((e1.sub e2).add e3).map_seqL r
  rw [W.vec_split t (q, true) [(s, true), (m, true), (q, true)] r,
    W.vec_split t (q, true) [(m, true), (s, true), (q, true)] r, W.vec_prefix_q,
    ← map_add, W.r2_identity]
  intro z
  rw [hsum z]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, TraceData.c2, TraceData.noConst, Bool.false_eq_true,
    ↓reduceIte]
  ring

theorem R2Holds.comm {t : Word Letter} {q s m : Letter} (h : W.R2Holds τ t q s m) :
    W.R2Holds τ t q m s := by
  intro r z
  rw [τ.R_symm23, add_comm]
  exact h r z

theorem p3_identity (x y z : Letter) (η : V) :
    W.seqL [(x, false), (y, false), (z, true), (y, false), (x, false), (0, true)] η
      - W.seqL [(x, false), (y, true), (z, true), (y, true), (x, false), (0, true)] η
      - W.seqL [(x, true), (y, false), (z, true), (y, false), (x, true), (0, true)] η
      + W.seqL [(x, true), (y, true), (z, true), (y, true), (x, true), (0, true)] η =
    W.seqL [(z, true), (0, true)] η
      - (W.seqL [(y, true), (z, true), (0, true)] η + W.seqL [(z, true), (y, true), (0, true)] η)
      - (W.seqL [(x, true), (z, true), (0, true)] η + W.seqL [(z, true), (x, true), (0, true)] η)
      + (W.seqL [(x, true), (y, true), (z, true), (0, true)] η
          + W.seqL [(z, true), (y, true), (x, true), (0, true)] η)
      + (W.seqL [(x, true), (z, true), (y, true), (0, true)] η
          + W.seqL [(y, true), (z, true), (x, true), (0, true)] η) := by
  simp only [seqL_cons_apply, seqL_nil_apply, op_yes_apply, op_no_apply, map_sub]
  abel

theorem piC_append (x y z : Letter) (r : Word Letter) :
    W.piC x y z r = W.seqL r (W.piC x y z []) := by
  simp only [piC, vec_append, map_add, List.append_nil]

theorem eqv_of_base {x y : V} (r : Word Letter) (h : W.Eqv x y) :
    W.Eqv (W.seqL r x) (W.seqL r y) := h.map_seqL r

/-- (P3) from its four purity instances, (R1_0) and two (R2_0) at `A`. -/
theorem p3_of_purity (x y z : Letter)
    (hFF : W.PurityHolds [] (0, true) [(x, false), (y, false), (z, true)] (τ.c3 false false x y z))
    (hFT : W.PurityHolds [] (0, true) [(x, false), (y, true), (z, true)] (τ.c3 false true x y z))
    (hTF : W.PurityHolds [] (0, true) [(x, true), (y, false), (z, true)] (τ.c3 true false x y z))
    (hTT : W.PurityHolds [] (0, true) [(x, true), (y, true), (z, true)] (τ.c3 true true x y z))
    (h1 : W.R1Holds τ [] 0 z) (h2y : W.R2Holds τ [] 0 y z) (h2x : W.R2Holds τ [] 0 x z) :
    W.P3Holds τ x y z := by
  have hη : W.vec ([] ++ [((0 : Letter), true)]) = W.vec [] := by simp
  have mirror : ∀ a b : Bool, [((x : Letter), a), ((y : Letter), b), ((z : Letter), true)] ++
      purityMirror [((x : Letter), a), ((y : Letter), b), ((z : Letter), true)] ++
        [((0 : Letter), true)] = [(x, a), (y, b), (z, true), (y, b), (x, a), (0, true)] := by
    intro a b; simp [purityMirror]
  have pur : ∀ (a b : Bool) (c : ℝ),
      W.PurityHolds [] (0, true) [(x, a), (y, b), (z, true)] c →
      W.Eqv (W.vec [(x, a), (y, b), (z, true), (y, b), (x, a), (0, true)]) (c • W.vec []) := by
    intro a b c h
    have h' := (W.purityHolds_iff _ _ _ _).1 h
    rw [mirror, hη] at h'
    exact h'
  have eFF := pur _ _ _ hFF
  have eFT := pur _ _ _ hFT
  have eTF := pur _ _ _ hTF
  have eTT := pur _ _ _ hTT
  have key : W.vec [(x, false), (y, false), (z, true), (y, false), (x, false), (0, true)]
      - W.vec [(x, false), (y, true), (z, true), (y, true), (x, false), (0, true)]
      - W.vec [(x, true), (y, false), (z, true), (y, false), (x, true), (0, true)]
      + W.vec [(x, true), (y, true), (z, true), (y, true), (x, true), (0, true)] =
    W.vec [(z, true), (0, true)]
      - (W.vec [(y, true), (z, true), (0, true)] + W.vec [(z, true), (y, true), (0, true)])
      - (W.vec [(x, true), (z, true), (0, true)] + W.vec [(z, true), (x, true), (0, true)])
      + (W.vec [(x, true), (y, true), (z, true), (0, true)]
          + W.vec [(z, true), (y, true), (x, true), (0, true)])
      + (W.vec [(x, true), (z, true), (y, true), (0, true)]
          + W.vec [(y, true), (z, true), (x, true), (0, true)]) :=
    W.p3_identity x y z W.ξ
  have hsum := τ.c3_signed_sum x y z
  simp only [TraceData.p3Const, TraceData.dpair] at hsum
  intro r
  rw [W.piC_append x y z r, W.piC_append x z y r, ← map_add,
    show W.vec r = W.seqL r (W.vec []) from rfl, ← map_smul]
  apply eqv_of_base
  intro w
  have k := congrArg (fun v => W.form v w) key
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at k
  have kFF := eFF w
  have kFT := eFT w
  have kTF := eTF w
  have kTT := eTT w
  have k1 := h1 [] w
  have k2y := h2y [] w
  have k2x := h2x [] w
  simp only [List.nil_append, List.append_nil, vec_cons_yesA, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at kFF kFT kTF kTT k1 k2y k2x
  simp only [piC, List.append_nil, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  linear_combination -k + kFF - kFT - kTF + kTT - k1 + k2y + k2x
    + (W.form (W.vec []) w) * hsum

/-- Canonical outer letters for a middle letter: `B ↦ (C, D)`, `C ↦ (B, D)`, `D ↦ (B, C)`. -/
def others (y : Letter) : Letter × Letter :=
  if y = 1 then (2, 3) else if y = 2 then (1, 3) else (1, 2)

/-- `Π_y` in canonical form. -/
def piMid (y : Letter) (r : Word Letter) : V := W.piC (others y).1 y (others y).2 r

theorem ordering_cases (x y z : Letter) (h : IsOrderingBCD x y z) :
    (x = 1 ∧ y = 2 ∧ z = 3) ∨ (x = 1 ∧ y = 3 ∧ z = 2) ∨ (x = 2 ∧ y = 1 ∧ z = 3) ∨
      (x = 2 ∧ y = 3 ∧ z = 1) ∨ (x = 3 ∧ y = 1 ∧ z = 2) ∨ (x = 3 ∧ y = 2 ∧ z = 1) := by
  revert h; revert x y z; decide

theorem piC_eq_piMid (x y z : Letter) (h : IsOrderingBCD x y z) (r : Word Letter) :
    W.piC x y z r = W.piMid y r := by
  rcases ordering_cases x y z h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [piMid, others, piC] <;> simp <;> abel

/-- Pair form of (P3), indexed by the unordered pair of middle letters. -/
def PairHolds (y z : Letter) : Prop :=
  ∀ r : Word Letter, W.Eqv (W.piMid y r + W.piMid z r) ((2 * (τ.om y + τ.om z)) • W.vec r)

theorem pairHolds_of_p3 (x y z : Letter) (h : IsOrderingBCD x y z) (hp : W.P3Holds τ x y z) :
    W.PairHolds τ y z := by
  intro r
  have hxzy : IsOrderingBCD x z y := by
    obtain ⟨a, b, c, d, e, g⟩ := h; exact ⟨a, c, b, g, Ne.symm e, d⟩
  rw [← W.piC_eq_piMid x y z h, ← W.piC_eq_piMid x z y hxzy]
  exact hp r

/-- Lemma 2 by the pair identity: three (P3) instances, one with each first letter
`B`, `C`, `D` (any of the two orders each), give (R3_0) for every ordering. -/
theorem r3_of_p3 (yB zB yC zC yD zD : Letter)
    (hoB : IsOrderingBCD 1 yB zB) (hoC : IsOrderingBCD 2 yC zC) (hoD : IsOrderingBCD 3 yD zD)
    (hB : W.P3Holds τ 1 yB zB) (hC : W.P3Holds τ 2 yC zC) (hD : W.P3Holds τ 3 yD zD) :
    ∀ x y z, IsOrderingBCD x y z → W.R3Holds τ x y z := by
  have pB := W.pairHolds_of_p3 τ _ _ _ hoB hB
  have pC := W.pairHolds_of_p3 τ _ _ _ hoC hC
  have pD := W.pairHolds_of_p3 τ _ _ _ hoD hD
  -- normalise each pair to (2,3), (1,3), (1,2)
  have norm : ∀ (a b : Letter), W.PairHolds τ a b → W.PairHolds τ b a := by
    intro a b h r w
    rw [add_comm, add_comm (τ.om b)]
    exact h r w
  have p23 : W.PairHolds τ 2 3 := by
    rcases ordering_cases 1 yB zB hoB with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨h, -⟩ | ⟨h, -⟩
    · exact pB
    · exact norm _ _ pB
    all_goals exact absurd h (by decide)
  have p13 : W.PairHolds τ 1 3 := by
    rcases ordering_cases 2 yC zC hoC with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ |
      ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact pC
    · exact norm _ _ pC
    all_goals exact absurd h (by decide)
  have p12 : W.PairHolds τ 1 2 := by
    rcases ordering_cases 3 yD zD hoD with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact pD
    · exact norm _ _ pD
  have mid : ∀ u : Letter, u ≠ 0 → ∀ r, W.Eqv (W.piMid u r) ((2 * τ.om u) • W.vec r) := by
    intro u hu r w
    have a := p23 r w
    have b := p13 r w
    have c := p12 r w
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at a b c ⊢
    have hu' : u = 1 ∨ u = 2 ∨ u = 3 := by revert hu; revert u; decide
    rcases hu' with rfl | rfl | rfl
    · linear_combination (-(1 : ℝ) / 2) * a + (1 / 2) * b + (1 / 2) * c
    · linear_combination (1 / 2) * a - (1 / 2) * b + (1 / 2) * c
    · linear_combination (1 / 2) * a + (1 / 2) * b - (1 / 2) * c
  intro x y z h r
  rw [W.piC_eq_piMid x y z h]
  exact mid y h.2.1 r

/-! ### Lemma D -/

/-- Lemma D in the form used (one-no polarisation), with
`J = [u]`, `X = P_{r_k} ⋯ P_{n}`, and `p = a_{i−1}` the last letter of `A u`:
`⟨[u a n r], [u n r]⟩ = (‖[u a n r]‖² + ‖[u n r]‖² − ‖[u ā n r]‖²)/2`. -/
theorem lemmaD_polar (u : List Letter) (a n : Letter) (r : List Letter) :
    2 * W.form (W.pathVec (u ++ a :: n :: r)) (W.pathVec (u ++ n :: r)) =
      W.normSq (W.pathVec (u ++ a :: n :: r)) + W.normSq (W.pathVec (u ++ n :: r))
        - W.normSq (W.vec (yesWord u ++ (a, false) :: yesWord (n :: r))) := by
  have e1 : W.pathVec (u ++ a :: n :: r) = W.vec (yesWord u ++ (a, true) :: yesWord (n :: r)) := by
    simp [pathVec]
  have e2 : W.pathVec (u ++ n :: r) = W.vec (yesWord u ++ yesWord (n :: r)) := by
    simp [pathVec]
  rw [e1, e2]
  exact W.polarisation _ _ _

/-! ### From the table: purity instances and rules -/

variable {W τ}
variable {S : Set (Word Letter)} {f : Word Letter → ℝ}

theorem Reproduces.apply (hrep : W.Reproduces S f) (hT : TableValues τ f) {u : Word Letter}
    (hu : dropYesA u ∈ S) : W.normSq (W.vec u) = f u := by
  rw [← W.normSq_vec_dropYesA, hrep _ hu, hT.f_dropYesA]

theorem purityHolds_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f)
    (t : Word Letter) (q : Outcome Letter) (v : Word Letter) (c : ℝ)
    (hS : Covers S (purityWords t q v))
    (hf : f (t ++ [q] ++ v ++ purityMirror v ++ [q]) - 2 * c * f (t ++ [q] ++ v)
        + c ^ 2 * f (t ++ [q]) = 0) :
    W.PurityHolds t q v c := by
  apply W.purityHolds_of_residual
  rw [hrep.apply hT (hS _ (by simp [purityWords])), hrep.apply hT (hS _ (by simp [purityWords])),
    hrep.apply hT (hS _ (by simp [purityWords]))]
  exact hf

theorem r1_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f) (t : Word Letter)
    (q v : Letter) (hS : Covers S (r1Words t q v)) : W.R1Holds τ t q v := by
  apply W.r1_of_purity
  apply purityHolds_of_table hrep hT _ _ _ _ hS
  have e1 : t ++ [(q, true)] ++ [(v, true)] ++ purityMirror [(v, true)] ++ [(q, true)] =
      t ++ [(q, true), (v, true), (q, true)] := by simp [purityMirror]
  have e2 : t ++ [(q, true)] ++ [(v, true)] = t ++ [(q, true), (v, true)] := by simp
  rw [e1, e2, hT.long1, hT.mid1]
  ring

theorem r2_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f) (t : Word Letter)
    (q s m : Letter) (hS : Covers S (r2Words t q s m)) : W.R2Holds τ t q s m := by
  have hS1 := hS.left.left
  have hS2 := hS.left.right
  have hS3 := hS.right
  apply W.r2_of_purity
  · apply purityHolds_of_table hrep hT _ _ _ _ hS1
    have e1 : t ++ [(q, true)] ++ [(m, true)] ++ purityMirror [(m, true)] ++ [(q, true)] =
        t ++ [(q, true), (m, true), (q, true)] := by simp [purityMirror]
    have e2 : t ++ [(q, true)] ++ [(m, true)] = t ++ [(q, true), (m, true)] := by simp
    rw [e1, e2, hT.long1, hT.mid1]; ring
  · apply purityHolds_of_table hrep hT _ _ _ _ hS2
    have e1 : t ++ [(q, true)] ++ [(s, false), (m, true)] ++ purityMirror [(s, false), (m, true)]
        ++ [(q, true)] = t ++ [(q, true), (s, false), (m, true), (s, false), (q, true)] := by
      simp [purityMirror]
    have e2 : t ++ [(q, true)] ++ [(s, false), (m, true)] =
        t ++ [(q, true), (s, false), (m, true)] := by simp
    rw [e1, e2, hT.long2, hT.mid2]; ring
  · apply purityHolds_of_table hrep hT _ _ _ _ hS3
    have e1 : t ++ [(q, true)] ++ [(s, true), (m, true)] ++ purityMirror [(s, true), (m, true)]
        ++ [(q, true)] = t ++ [(q, true), (s, true), (m, true), (s, true), (q, true)] := by
      simp [purityMirror]
    have e2 : t ++ [(q, true)] ++ [(s, true), (m, true)] =
        t ++ [(q, true), (s, true), (m, true)] := by simp
    rw [e1, e2, hT.long2, hT.mid2]; ring

theorem p3Purity_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f) (x y z : Letter)
    (h : IsOrderingBCD x y z) (a b : Bool)
    (hS : Covers S (purityWords [] (0, true) [(x, a), (y, b), (z, true)])) :
    W.PurityHolds [] (0, true) [(x, a), (y, b), (z, true)] (τ.c3 a b x y z) := by
  apply purityHolds_of_table hrep hT _ _ _ _ hS
  have e1 : ([] : Word Letter) ++ [((0 : Letter), true)] ++ [(x, a), (y, b), (z, true)] ++
      purityMirror [(x, a), (y, b), (z, true)] ++ [((0 : Letter), true)] =
      [] ++ [(0, true), (x, a), (y, b), (z, true), (y, b), (x, a), (0, true)] := by
    simp [purityMirror]
  have e2 : ([] : Word Letter) ++ [((0 : Letter), true)] ++ [(x, a), (y, b), (z, true)] =
      [] ++ [(0, true), (x, a), (y, b), (z, true)] := by simp
  rw [e1, e2, hT.long3 [] x y z a b h, hT.mid3 [] x y z a b h]
  ring

theorem p3_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f) (x y z : Letter)
    (h : IsOrderingBCD x y z) (hS : Covers S (p3Words x y z)) : W.P3Holds τ x y z := by
  unfold p3Words p3PurityWords at hS
  apply W.p3_of_purity
  · exact p3Purity_of_table hrep hT x y z h false false hS.left.left.left.left.left.left
  · exact p3Purity_of_table hrep hT x y z h false true hS.left.left.left.left.left.right
  · exact p3Purity_of_table hrep hT x y z h true false hS.left.left.left.left.right
  · exact p3Purity_of_table hrep hT x y z h true true hS.left.left.left.right
  · exact r1_of_table hrep hT [] 0 z hS.left.left.right
  · exact r2_of_table hrep hT [] 0 y z hS.left.right
  · exact r2_of_table hrep hT [] 0 x z hS.right

/-- Lemma 2 / (R3_0) from the table, through (P3) for one ordering per first letter. -/
theorem r3_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f)
    (yB zB yC zC yD zD : Letter)
    (hoB : IsOrderingBCD 1 yB zB) (hoC : IsOrderingBCD 2 yC zC) (hoD : IsOrderingBCD 3 yD zD)
    (hSB : Covers S (p3Words 1 yB zB)) (hSC : Covers S (p3Words 2 yC zC))
    (hSD : Covers S (p3Words 3 yD zD)) :
    ∀ x y z, IsOrderingBCD x y z → W.R3Holds τ x y z :=
  W.r3_of_p3 τ yB zB yC zC yD zD hoB hoC hoD (p3_of_table hrep hT _ _ _ hoB hSB)
    (p3_of_table hrep hT _ _ _ hoC hSC) (p3_of_table hrep hT _ _ _ hoD hSD)

/-- Lemma D (stronger than the printed polarisation: no restriction `a_{i−1} ≠ a_{i+1}` or
on letters or length): `⟨[u a n r], [u n r]⟩ = R_{p a n} · ∏ o` (all other consecutive overlaps of
`A u a n r`), `p` the last letter of `A u`. -/
theorem lemmaD_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f) (u : List Letter)
    (a n : Letter) (r : List Letter) (hS : Covers S (lemmaDWords u a n r)) :
    W.form (W.pathVec (u ++ a :: n :: r)) (W.pathVec (u ++ n :: r)) =
      τ.R (u.getLastD 0) a n * τ.chainProd (0 :: u) * τ.chainProd (n :: r) := by
  have h := W.lemmaD_polar u a n r
  have f1 : W.normSq (W.pathVec (u ++ a :: n :: r)) = f (yesWord (u ++ a :: n :: r)) :=
    hrep.apply hT (hS _ (by simp [lemmaDWords]))
  have f2 : W.normSq (W.pathVec (u ++ n :: r)) = f (yesWord (u ++ n :: r)) :=
    hrep.apply hT (hS _ (by simp [lemmaDWords]))
  have f3 : W.normSq (W.vec (yesWord u ++ (a, false) :: yesWord (n :: r))) =
      f (yesWord u ++ (a, false) :: yesWord (n :: r)) :=
    hrep.apply hT (hS _ (by simp [lemmaDWords]))
  rw [f1, f2, f3, hT.chain, hT.chain, hT.oneNo, τ.chainProd_split, τ.chainProd_split,
    TraceData.chainProd_cons_cons] at h
  simp only [TraceData.noConst] at h
  linear_combination h / 2

/-- (W1) on the walk form: `‖[u]‖² = ∏ o` along `A u`. -/
theorem chain_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f) (u : List Letter)
    (hS : dropYesA (yesWord u) ∈ S) : W.normSq (W.pathVec u) = τ.chainProd (0 :: u) := by
  rw [pathVec, hrep.apply hT hS, hT.chain]

end WalkForm

/-! ## Rule instances (finite lists, for budget forms) -/

/-- One rule instance of the chosen route. -/
inductive RuleInstance
  | r1 (t : Word Letter) (q v : Letter)
  | r2 (t : Word Letter) (q s m : Letter)
  | p3 (x y z : Letter)
  | delete (u : List Letter) (a n : Letter) (r : List Letter)
  | chain (u : List Letter)

namespace RuleInstance

/-- Forcing words of an instance (raw; `Covers` deletes a leading yes on `A`). -/
def forcingWords : RuleInstance → List (Word Letter)
  | r1 t q v => r1Words t q v
  | r2 t q s m => r2Words t q s m
  | p3 x y z => p3Words x y z
  | delete u a n r => lemmaDWords u a n r
  | chain u => [yesWord u]

/-- Side condition of an instance. -/
def Valid : RuleInstance → Prop
  | p3 x y z => IsOrderingBCD x y z
  | _ => True

/-- The identity an instance asserts. -/
def Holds {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V) (τ : TraceData) :
    RuleInstance → Prop
  | r1 t q v => W.R1Holds τ t q v
  | r2 t q s m => W.R2Holds τ t q s m
  | p3 x y z => W.P3Holds τ x y z
  | delete u a n r => W.form (W.pathVec (u ++ a :: n :: r)) (W.pathVec (u ++ n :: r)) =
      τ.R (u.getLastD 0) a n * τ.chainProd (0 :: u) * τ.chainProd (n :: r)
  | chain u => W.normSq (W.pathVec u) = τ.chainProd (0 :: u)

theorem holds_of_table {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V}
    {τ : TraceData} {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (hrep : W.Reproduces S f) (hT : TableValues τ f) :
    ∀ ρ : RuleInstance, ρ.Valid → Covers S ρ.forcingWords → ρ.Holds W τ
  | r1 t q v, _, h => WalkForm.r1_of_table hrep hT t q v h
  | r2 t q s m, _, h => WalkForm.r2_of_table hrep hT t q s m h
  | p3 x y z, hv, h => WalkForm.p3_of_table hrep hT x y z hv h
  | delete u a n r, _, h => WalkForm.lemmaD_of_table hrep hT u a n r h
  | chain u, _, h => WalkForm.chain_of_table hrep hT u (h _ (by simp [forcingWords]))

end RuleInstance

end AlbertSequential.LengthSeven
