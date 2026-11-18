/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.ShortRules
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-! # Formal defect identities for the robust certificates (thm:cer:seven(b))

A **defect decomposition** of a Gram entry `⟨[u₁],[u₂]⟩` is an identity, valid in every `WalkForm`,
```
⟨[u₁],[u₂]⟩ = Σ_k λ_k g(w_k) + Σ_j y_j ⟨[α_j], r_j⟩,   r_j = [t q v v̄ q] − c [t q],   g(w) = ‖[w]‖²,
```
where `[w] = vec w` (outcome words from `ξ`), `v̄ = purityMirror v`.  It records one application of the
paper's derivation of lem:cer:gram7 *without assuming any word is matched*: every use of (R1), (R2),
(R3) leaves the purity residual `r_j` paired with a left path vector `[α_j]`.

An `Entry` carries such a decomposition as data.  `Entry.ok` is a Boolean check (kernel `decide`):
both sides are expanded into walk values `L(w)` (`expand`: `1 − P` on "no" letters; `form_pathVec`),
walks are normalised by `canon`, and all coefficients must cancel.  `Entry.sound` turns `ok` into the
identity in every `WalkForm`.  Nothing about the route is trusted: only the check. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential AlbertSequential.LengthSeven

/-! ## Formal combinations of walks -/

/-- A formal rational combination of walks `Σ c L(w)`. -/
abbrev LC := List (ℚ × List Letter)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Value of a formal combination of walks in a `WalkForm`. -/
def LC.eval (W : WalkForm V) (p : LC) : ℝ := (p.map fun m => (m.1 : ℝ) * W.L m.2).sum

theorem LC.eval_nil (W : WalkForm V) : LC.eval W [] = 0 := by simp [LC.eval]

theorem LC.eval_cons (W : WalkForm V) (m : ℚ × List Letter) (p : LC) :
    LC.eval W (m :: p) = (m.1 : ℝ) * W.L m.2 + LC.eval W p := by simp [LC.eval]

theorem LC.eval_append (W : WalkForm V) (p q : LC) :
    LC.eval W (p ++ q) = LC.eval W p + LC.eval W q := by simp [LC.eval, List.sum_append]

/-- Scaling a combination. -/
def LC.scale (c : ℚ) (p : LC) : LC := p.map fun m => (c * m.1, m.2)

theorem LC.eval_scale (W : WalkForm V) (c : ℚ) (p : LC) :
    LC.eval W (LC.scale c p) = (c : ℝ) * LC.eval W p := by
  induction p with
  | nil => simp [LC.eval, LC.scale]
  | cons m p ih =>
    simp only [LC.scale, List.map_cons] at ih ⊢
    rw [LC.eval_cons, LC.eval_cons, ih]
    push_cast
    ring

theorem LC.eval_flatMap {α : Type} (W : WalkForm V) (l : List α) (f : α → LC) :
    LC.eval W (l.flatMap f) = (l.map fun a => LC.eval W (f a)).sum := by
  induction l with
  | nil => simp [LC.eval]
  | cons a l ih => rw [List.flatMap_cons, LC.eval_append, ih, List.map_cons, List.sum_cons]

/-! ## Expansion of outcome words into path vectors -/

/-- `vec u = Σ c [s]`: a "no" letter `i` contributes `1 − P_i`. -/
def expand : Word Letter → List (ℤ × List Letter)
  | [] => [(1, [])]
  | a :: u =>
    if a.2 then (expand u).map (fun m => (m.1, a.1 :: m.2))
    else expand u ++ (expand u).map (fun m => (-m.1, a.1 :: m.2))

theorem pathVec_concat (W : WalkForm V) (p : List Letter) (i : Letter) :
    W.pathVec (p ++ [i]) = W.P i (W.pathVec p) := by
  simp only [WalkForm.pathVec, yesWord, List.map_append, List.map_cons, List.map_nil,
    WalkForm.vec_append, WalkForm.seqL_singleton, WalkForm.op_yes]

theorem sum_neg_smul (l : List (ℤ × List Letter)) (g : ℤ × List Letter → V) :
    (l.map fun m => (((-m.1 : ℤ)) : ℝ) • g m).sum = -(l.map fun m => (m.1 : ℝ) • g m).sum := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    push_cast
    rw [neg_smul, neg_add]

theorem seqL_expand (W : WalkForm V) :
    ∀ (u : Word Letter) (p : List Letter),
      W.seqL u (W.pathVec p) = ((expand u).map fun m => (m.1 : ℝ) • W.pathVec (p ++ m.2)).sum
  | [], p => by simp [expand]
  | (i, b) :: u, p => by
    cases b with
    | true =>
      rw [WalkForm.seqL_cons_apply, WalkForm.op_yes_apply, ← pathVec_concat,
        seqL_expand W u (p ++ [i])]
      simp only [expand, ite_true, List.map_map, Function.comp_def, List.append_assoc,
        List.singleton_append]
    | false =>
      rw [WalkForm.seqL_cons_apply, WalkForm.op_no_apply, map_sub, seqL_expand W u p,
        ← pathVec_concat, seqL_expand W u (p ++ [i])]
      simp only [expand, Bool.false_eq_true, ite_false, List.map_append, List.sum_append,
        List.map_map, Function.comp_def]
      rw [sum_neg_smul (expand u) (fun m => W.pathVec (p ++ i :: m.2)), sub_eq_add_neg]
      simp only [List.append_assoc, List.singleton_append]

theorem vec_expand (W : WalkForm V) (u : Word Letter) :
    W.vec u = ((expand u).map fun m => (m.1 : ℝ) • W.pathVec m.2).sum := by
  have h := seqL_expand W u []
  simp only [List.nil_append] at h
  rw [← h]
  rfl

theorem form_sum_right (W : WalkForm V) (x : V) (l : List (ℤ × List Letter))
    (g : ℤ × List Letter → V) :
    W.form x ((l.map fun m => (m.1 : ℝ) • g m).sum) =
      (l.map fun m => (m.1 : ℝ) * W.form x (g m)).sum := by
  induction l with
  | nil => simp
  | cons m l ih => simp only [List.map_cons, List.sum_cons, map_add, map_smul, smul_eq_mul, ih]

theorem form_sum_left (W : WalkForm V) (y : V) (l : List (ℤ × List Letter))
    (g : ℤ × List Letter → V) :
    W.form ((l.map fun m => (m.1 : ℝ) • g m).sum) y =
      (l.map fun m => (m.1 : ℝ) * W.form (g m) y).sum := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.map_cons, List.sum_cons, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, ih]

/-- `⟨[α], vec u⟩` as a combination of walks. -/
def lcForm (α : List Letter) (u : Word Letter) : LC :=
  (expand u).map fun m => ((m.1 : ℚ), α ++ m.2.reverse)

theorem eval_lcForm (W : WalkForm V) (α : List Letter) (u : Word Letter) :
    LC.eval W (lcForm α u) = W.form (W.pathVec α) (W.vec u) := by
  rw [vec_expand, form_sum_right]
  unfold lcForm
  generalize expand u = l
  induction l with
  | nil => simp [LC.eval]
  | cons m l ih =>
    rw [List.map_cons, LC.eval_cons, ih, List.map_cons, List.sum_cons, WalkForm.form_pathVec]
    push_cast
    ring

/-- `g(u) = ‖vec u‖²` as a combination of walks. -/
def lcG (u : Word Letter) : LC :=
  (expand u).flatMap fun m => LC.scale (m.1 : ℚ) (lcForm m.2 u)

theorem eval_lcG (W : WalkForm V) (u : Word Letter) :
    LC.eval W (lcG u) = W.normSq (W.vec u) := by
  unfold lcG WalkForm.normSq
  rw [LC.eval_flatMap]
  conv_rhs => rw [vec_expand W u, form_sum_left]
  rw [← vec_expand W u]
  congr 1
  apply List.map_congr_left
  intro m _
  rw [LC.eval_scale, eval_lcForm]
  push_cast
  ring

/-! ## Zero test for combinations of walks -/

/-- Total coefficient of the walk `w`. -/
def coeffOf (w : List Letter) : LC → ℚ
  | [] => 0
  | m :: p => (if m.2 = w then m.1 else 0) + coeffOf w p

/-- Remove all terms with walk `w`. -/
def dropW (w : List Letter) : LC → LC
  | [] => []
  | m :: p => if m.2 = w then dropW w p else m :: dropW w p

theorem eval_split (W : WalkForm V) (w : List Letter) (p : LC) :
    LC.eval W p = (coeffOf w p : ℝ) * W.L w + LC.eval W (dropW w p) := by
  induction p with
  | nil => simp [LC.eval, coeffOf, dropW]
  | cons m p ih =>
    by_cases h : m.2 = w
    · simp only [coeffOf, dropW, h, ite_true, LC.eval_cons, ih]
      push_cast
      ring
    · simp only [coeffOf, dropW, h, ite_false, LC.eval_cons, ih]
      push_cast
      ring

/-- Every walk has total coefficient zero (fuel = number of terms). -/
def zeroCheck : ℕ → LC → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, m :: p => decide (m.1 + coeffOf m.2 p = 0) && zeroCheck n (dropW m.2 p)

theorem zeroCheck_sound (W : WalkForm V) : ∀ (n : ℕ) (p : LC), zeroCheck n p = true → LC.eval W p = 0
  | _, [], _ => by simp [LC.eval]
  | 0, _ :: _, h => by simp [zeroCheck] at h
  | n + 1, m :: p, h => by
    simp only [zeroCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [LC.eval_cons, eval_split W m.2 p, zeroCheck_sound W n _ h.2]
    have h1 : (m.1 : ℝ) + (coeffOf m.2 p : ℝ) = 0 := by exact_mod_cast h.1
    linear_combination W.L m.2 * h1

/-- Replace every walk by its canonical representative. -/
def canonize (p : LC) : LC := p.map fun m => (m.1, canon m.2)

theorem eval_canonize (W : WalkForm V) (p : LC) : LC.eval W (canonize p) = LC.eval W p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    simp only [canonize, List.map_cons] at ih ⊢
    rw [LC.eval_cons, LC.eval_cons, ih, WalkForm.L_canon]

/-! ## Table words, defects, entries -/

/-- Table words of the decompositions: all-"yes" words (W1) and words with one interior "no"
(W2, polarisation), both read from `p_A`. -/
inductive TabWord where
  | yes (u : List Letter)
  | one (u : List Letter) (a n : Letter) (r : List Letter)
  deriving DecidableEq

def TabWord.toWord : TabWord → Word Letter
  | .yes u => yesWord u
  | .one u a n r => yesWord u ++ (a, false) :: yesWord (n :: r)

/-- A purity defect `y ⟨[α], vec(t q v v̄ q) − c vec(t q)⟩`. -/
structure Defect where
  y : ℚ
  α : List Letter
  t : Word Letter
  q : Letter
  v : Word Letter
  c : ℚ

def Defect.long (d : Defect) : Word Letter :=
  d.t ++ [(d.q, true)] ++ d.v ++ purityMirror d.v ++ [(d.q, true)]
def Defect.mid (d : Defect) : Word Letter := d.t ++ [(d.q, true)] ++ d.v
def Defect.short (d : Defect) : Word Letter := d.t ++ [(d.q, true)]

/-- The defect vector `vec(t q v v̄ q) − c vec(t q)`. -/
def Defect.resid (W : WalkForm V) (d : Defect) : V := W.vec d.long - (d.c : ℝ) • W.vec d.short

/-- A defect decomposition of `⟨[u₁],[u₂]⟩`. -/
structure Entry where
  u1 : List Letter
  u2 : List Letter
  tabs : List (ℚ × TabWord)
  defs : List Defect

/-- `⟨[u₁],[u₂]⟩ − Σ λ g(w) − Σ y ⟨[α], r⟩` as a combination of walks. -/
def Entry.lc (e : Entry) : LC :=
  [((1 : ℚ), e.u1 ++ e.u2.reverse)] ++
    (e.tabs.flatMap fun m => LC.scale (-m.1) (lcG m.2.toWord)) ++
    (e.defs.flatMap fun d =>
      LC.scale (-d.y) (lcForm d.α d.long) ++ LC.scale (d.y * d.c) (lcForm d.α d.short))

/-- The kernel check of a decomposition. -/
def Entry.ok (e : Entry) : Bool := zeroCheck e.lc.length (canonize e.lc)

/-- Right-hand side of the decomposition in a `WalkForm`. -/
def Entry.rhs (W : WalkForm V) (e : Entry) : ℝ :=
  (e.tabs.map fun m => (m.1 : ℝ) * W.normSq (W.vec m.2.toWord)).sum +
    (e.defs.map fun d => (d.y : ℝ) * W.form (W.pathVec d.α) (d.resid W)).sum

theorem Entry.eval_lc (W : WalkForm V) (e : Entry) :
    LC.eval W e.lc = W.form (W.pathVec e.u1) (W.pathVec e.u2) - e.rhs W := by
  unfold Entry.lc Entry.rhs
  rw [LC.eval_append, LC.eval_append, LC.eval_flatMap, LC.eval_flatMap, LC.eval_cons,
    LC.eval_nil]
  have h1 : ∀ l : List (ℚ × TabWord),
      (l.map fun m => LC.eval W (LC.scale (-m.1) (lcG m.2.toWord))).sum =
        -(l.map fun m => (m.1 : ℝ) * W.normSq (W.vec m.2.toWord)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons m l ih =>
      rw [List.map_cons, List.sum_cons, ih, LC.eval_scale, eval_lcG, List.map_cons, List.sum_cons]
      push_cast
      ring
  have h2 : ∀ l : List Defect,
      (l.map fun d => LC.eval W (LC.scale (-d.y) (lcForm d.α d.long) ++
          LC.scale (d.y * d.c) (lcForm d.α d.short))).sum =
        -(l.map fun d => (d.y : ℝ) * W.form (W.pathVec d.α) (d.resid W)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons d l ih =>
      rw [List.map_cons, List.sum_cons, ih, LC.eval_append, LC.eval_scale, LC.eval_scale,
        eval_lcForm, eval_lcForm, List.map_cons, List.sum_cons]
      simp only [Defect.resid, map_sub, map_smul, smul_eq_mul]
      push_cast
      ring
  rw [h1, h2, WalkForm.form_pathVec]
  push_cast
  ring

/-- **Soundness**: a checked decomposition holds in every `WalkForm`. -/
theorem Entry.sound (W : WalkForm V) (e : Entry) (h : e.ok = true) :
    W.form (W.pathVec e.u1) (W.pathVec e.u2) = e.rhs W := by
  have h0 := zeroCheck_sound W _ _ h
  rw [eval_canonize, Entry.eval_lc] at h0
  linarith

end AlbertSequential.LengthSeven.Robust

namespace AlbertSequential.LengthSeven.Robust

/-! ## Compact constructors for generated data (letters as naturals `0..3`; `n + 4` = "no" on `n`) -/

def lt (n : ℕ) : Letter := ⟨n % 4, Nat.mod_lt _ (by decide)⟩
def ltb (n : ℕ) : Letter × Bool := (lt n, decide (n < 4))
def mkD (yn : ℤ) (yd : ℕ) (α t : List ℕ) (q : ℕ) (v : List ℕ) (cn : ℤ) (cd : ℕ) : Defect :=
  ⟨(yn : ℚ) / yd, α.map lt, t.map ltb, lt q, v.map ltb, (cn : ℚ) / cd⟩
def mkY (ln : ℤ) (ld : ℕ) (u : List ℕ) : ℚ × TabWord := ((ln : ℚ) / ld, .yes (u.map lt))
def mkO (ln : ℤ) (ld : ℕ) (u : List ℕ) (a n : ℕ) (r : List ℕ) : ℚ × TabWord :=
  ((ln : ℚ) / ld, .one (u.map lt) (lt a) (lt n) (r.map lt))
def mkE (u1 u2 : List ℕ) (tabs : List (ℚ × TabWord)) (defs : List Defect) : Entry :=
  ⟨u1.map lt, u2.map lt, tabs, defs⟩

end AlbertSequential.LengthSeven.Robust
