/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.ShortRules
public import Mathlib.Tactic.LinearCombination

/-! # Lemma A: the rule-step API for walk values

Walk values of Lemma A (lem:cer:gram28) are derived for generic letters `x, y, z` (an ordering
of `B, C, D`).  Walks are written in *pattern letters* `PL = {A, X, Y, Z}` and evaluated by
`PL.ev x y z` (`A ↦ 0`, `X ↦ x`, `Y ↦ y`, `Z ↦ z`).  A computable normalisation `pnorm`
(merge equal neighbours, strip end `A`'s) and `equivW` (equal after `pnorm`, possibly reversed)
transport walk values (`L_conv`); `equivW p q = true` is closed by `decide` on concrete
pattern lists, so no per-step list bookkeeping is needed.

Each rule step of the derivation data is one `step*` lemma: from one rule fact (an instance of
(R1_t), (R2_t), (R3_0), Lemma D or (W1)) it produces a scalar relation among walk values `L`
of explicitly listed pattern walks.  The rule facts are taken from `UsedRules`, whose finite
list `usedInsts` of pattern instances is generated (file `Instances.lean`).

Soundness of `pnorm` needs no injectivity of `ev`: merging equal pattern letters merges equal
letters, and stripping `A` strips `0`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.LemmaA

open AlbertSequential AlbertSequential.LengthSeven

/-! ## Pattern letters -/

/-- Pattern letters: `A` and three generic letters. -/
inductive PL
  | A
  | X
  | Y
  | Z
  deriving DecidableEq, Repr

/-- Evaluation of pattern letters at an assignment `(x, y, z)`. -/
def PL.ev (x y z : Letter) : PL → Letter
  | .A => 0
  | .X => x
  | .Y => y
  | .Z => z

@[simp] theorem PL.ev_A (x y z : Letter) : PL.ev x y z .A = 0 := rfl
@[simp] theorem PL.ev_X (x y z : Letter) : PL.ev x y z .X = x := rfl
@[simp] theorem PL.ev_Y (x y z : Letter) : PL.ev x y z .Y = y := rfl
@[simp] theorem PL.ev_Z (x y z : Letter) : PL.ev x y z .Z = z := rfl

/-- Distinct pattern letters evaluate to distinct letters at an ordering of `B, C, D`. -/
theorem PL.ev_ne {x y z : Letter} (h : IsOrderingBCD x y z) :
    ∀ a b : PL, a ≠ b → PL.ev x y z a ≠ PL.ev x y z b := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  intro a b hab
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false] at hab <;>
    simp only [PL.ev] <;>
    first
    | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6
    | exact h1.symm | exact h2.symm | exact h3.symm | exact h4.symm | exact h5.symm
    | exact h6.symm

/-- Pairwise distinct non-`A` pattern letters (decidable side condition). -/
def PL.isOrd (a b c : PL) : Bool :=
  a != .A && b != .A && c != .A && a != b && b != c && a != c

/-- A permutation of `X, Y, Z` evaluates to an ordering of `B, C, D`. -/
theorem PL.ord {x y z : Letter} (h : IsOrderingBCD x y z) (a b c : PL)
    (hab : PL.isOrd a b c = true) : IsOrderingBCD (PL.ev x y z a) (PL.ev x y z b) (PL.ev x y z c) := by
  simp only [PL.isOrd, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab'⟩, hbc⟩, hac⟩ := hab
  exact ⟨PL.ev_ne h a .A ha, PL.ev_ne h b .A hb, PL.ev_ne h c .A hc, PL.ev_ne h a b hab',
    PL.ev_ne h b c hbc, PL.ev_ne h a c hac⟩

/-! ## Sorting the arguments of `R` (normal form of trace atoms) -/

theorem R_213 (τ : TraceData) (a b c : Letter) : τ.R b a c = τ.R a b c := τ.R_symm12 b a c
theorem R_132 (τ : TraceData) (a b c : Letter) : τ.R a c b = τ.R a b c := τ.R_symm23 a c b
theorem R_231 (τ : TraceData) (a b c : Letter) : τ.R b c a = τ.R a b c :=
  (τ.R_symm23 b c a).trans (τ.R_symm12 b a c)
theorem R_312 (τ : TraceData) (a b c : Letter) : τ.R c a b = τ.R a b c :=
  (τ.R_symm12 c a b).trans (τ.R_symm23 a c b)
theorem R_321 (τ : TraceData) (a b c : Letter) : τ.R c b a = τ.R a b c :=
  (τ.R_symm12 c b a).trans (R_231 τ a b c)

/-! ## Computable walk normalisation on pattern words -/

/-- Merge equal neighbours. -/
def pmerge : List PL → List PL
  | [] => []
  | [a] => [a]
  | a :: b :: r => if a = b then pmerge (b :: r) else a :: pmerge (b :: r)

/-- Strip leading `A`'s. -/
def pstrip : List PL → List PL
  | [] => []
  | a :: r => if a = .A then pstrip r else a :: r

/-- Merge, then strip `A`'s at both ends. -/
def pnorm (w : List PL) : List PL := (pstrip (pstrip (pmerge w)).reverse).reverse

/-- Two pattern walks have the same walk value at every assignment: equal after `pnorm`,
possibly reversed. -/
def equivW (p q : List PL) : Bool := pnorm p == pnorm q || pnorm p == (pnorm q).reverse

section Walks

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V) (τ : TraceData)

theorem prodL_cons (a : Letter) (l : List Letter) : W.prodL (a :: l) = W.P a ∘ₗ W.prodL l := rfl

theorem prodL_map_pmerge (σ : PL → Letter) :
    ∀ w : List PL, W.prodL ((pmerge w).map σ) = W.prodL (w.map σ)
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => by
    have ih := prodL_map_pmerge σ (b :: r)
    rw [pmerge]
    split_ifs with hab
    · rw [ih]
      subst hab
      simp only [List.map_cons]
      exact (W.prodL_merge (σ a) (r.map σ)).symm
    · rw [List.map_cons, prodL_cons, ih]
      rfl

theorem L_map_pmerge (σ : PL → Letter) (w : List PL) :
    W.L ((pmerge w).map σ) = W.L (w.map σ) := by
  unfold WalkForm.L
  rw [prodL_map_pmerge]

theorem L_map_pstrip (σ : PL → Letter) (hσ : σ .A = 0) :
    ∀ w : List PL, W.L ((pstrip w).map σ) = W.L (w.map σ)
  | [] => rfl
  | a :: r => by
    rw [pstrip]
    split_ifs with h
    · subst h
      rw [L_map_pstrip σ hσ r, List.map_cons, hσ, W.L_cons_A]
    · rfl

theorem L_map_pnorm (σ : PL → Letter) (hσ : σ .A = 0) (w : List PL) :
    W.L ((pnorm w).map σ) = W.L (w.map σ) := by
  unfold pnorm
  rw [List.map_reverse, W.L_reverse, L_map_pstrip W σ hσ, List.map_reverse, W.L_reverse,
    L_map_pstrip W σ hσ, L_map_pmerge]

/-- Transport of walk values along `equivW`. -/
theorem L_conv (σ : PL → Letter) (hσ : σ .A = 0) (p q : List PL) (h : equivW p q = true) :
    W.L (p.map σ) = W.L (q.map σ) := by
  rw [← L_map_pnorm W σ hσ p, ← L_map_pnorm W σ hσ q]
  unfold equivW at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · rw [h]
  · rw [h, List.map_reverse, W.L_reverse]

/-! ## Rule facts as scalar relations among walk values (letters) -/

/-- Gram entries are matched to walk lemmas by evaluating `canon`. -/
theorem L_eq_of_canon {a b : List Letter} (h : canon a = canon b) : W.L a = W.L b := by
  rw [← W.L_canon a, h, W.L_canon]

theorem form_pathVec_xi (w : List Letter) : W.form (W.pathVec w) W.ξ = W.L w := by
  have h := W.form_pathVec w []
  simpa [WalkForm.pathVec] using h

theorem vec_yes (w : List Letter) : W.vec (yesWord w) = W.pathVec w := rfl

theorem L_of_R1 {t : List Letter} {q v : Letter} (hr : W.R1Holds τ (yesWord t) q v)
    (e : List Letter) : W.L (t ++ q :: v :: q :: e) = τ.o q v * W.L (t ++ q :: e) := by
  have h1 := hr (yesWord e) W.ξ
  have e1 : yesWord t ++ [(q, true), (v, true), (q, true)] ++ yesWord e =
      yesWord (t ++ q :: v :: q :: e) := by simp [yesWord]
  have e2 : yesWord t ++ [(q, true)] ++ yesWord e = yesWord (t ++ q :: e) := by simp [yesWord]
  rw [e1, e2, map_smul, LinearMap.smul_apply, smul_eq_mul, vec_yes, vec_yes, form_pathVec_xi,
    form_pathVec_xi] at h1
  exact h1

theorem L_of_R2 {t : List Letter} {q s m : Letter} (hr : W.R2Holds τ (yesWord t) q s m)
    (e : List Letter) :
    W.L (t ++ q :: s :: m :: q :: e) + W.L (t ++ q :: m :: s :: q :: e) =
      2 * τ.R q s m * W.L (t ++ q :: e) := by
  have h1 := hr (yesWord e) W.ξ
  have e1 : yesWord t ++ [(q, true), (s, true), (m, true), (q, true)] ++ yesWord e =
      yesWord (t ++ q :: s :: m :: q :: e) := by simp [yesWord]
  have e2 : yesWord t ++ [(q, true), (m, true), (s, true), (q, true)] ++ yesWord e =
      yesWord (t ++ q :: m :: s :: q :: e) := by simp [yesWord]
  have e3 : yesWord t ++ [(q, true)] ++ yesWord e = yesWord (t ++ q :: e) := by simp [yesWord]
  rw [e1, e2, e3, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    vec_yes, vec_yes, vec_yes, form_pathVec_xi, form_pathVec_xi, form_pathVec_xi] at h1
  exact h1

theorem L_of_R3 {a b c : Letter} (hr : W.R3Holds τ a b c) (e : List Letter) :
    W.L (a :: b :: c :: 0 :: e) + W.L (c :: b :: a :: 0 :: e) = 2 * τ.om b * W.L e := by
  have h1 := hr (yesWord e) W.ξ
  have e1 : [(a, true), (b, true), (c, true), ((0 : Letter), true)] ++ yesWord e =
      yesWord (a :: b :: c :: 0 :: e) := by simp [yesWord]
  have e2 : [(c, true), (b, true), (a, true), ((0 : Letter), true)] ++ yesWord e =
      yesWord (c :: b :: a :: 0 :: e) := by simp [yesWord]
  simp only [WalkForm.piC] at h1
  rw [e1, e2, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    vec_yes, vec_yes, vec_yes, form_pathVec_xi, form_pathVec_xi, form_pathVec_xi] at h1
  exact h1

theorem L_of_chain {u : List Letter} {c : ℝ} (hr : W.normSq (W.pathVec u) = c) :
    W.L (u ++ u.reverse) = c := by
  rw [← W.form_pathVec]
  exact hr

theorem L_of_delete {u : List Letter} {a n : Letter} {r : List Letter} {c : ℝ}
    (hr : W.form (W.pathVec (u ++ a :: n :: r)) (W.pathVec (u ++ n :: r)) = c) :
    W.L ((u ++ a :: n :: r) ++ (u ++ n :: r).reverse) = c := by
  rw [← W.form_pathVec]
  exact hr

/-! ## Pattern-level step lemmas -/

variable {W τ}
variable {x y z : Letter}

/-- (R1_t) as a step: `L(t q v q e) = o_qv L(t q e)`. -/
theorem stepR1 {t : List PL} {q v : PL}
    (hr : W.R1Holds τ (yesWord (t.map (PL.ev x y z))) (PL.ev x y z q) (PL.ev x y z v))
    (e w1 w2 : List PL) (h1 : equivW (t ++ q :: v :: q :: e) w1 = true)
    (h2 : equivW (t ++ q :: e) w2 = true) :
    W.L (w1.map (PL.ev x y z)) = τ.o (PL.ev x y z q) (PL.ev x y z v) * W.L (w2.map (PL.ev x y z)) := by
  rw [← L_conv W _ rfl _ _ h1, ← L_conv W _ rfl _ _ h2]
  simpa only [List.map_append, List.map_cons] using L_of_R1 W τ hr (e.map (PL.ev x y z))

/-- (R2_t) as a step: `L(t q s m q e) + L(t q m s q e) = 2 R_qsm L(t q e)`. -/
theorem stepR2 {t : List PL} {q s m : PL}
    (hr : W.R2Holds τ (yesWord (t.map (PL.ev x y z))) (PL.ev x y z q) (PL.ev x y z s)
      (PL.ev x y z m))
    (e w1 w2 w3 : List PL) (h1 : equivW (t ++ q :: s :: m :: q :: e) w1 = true)
    (h2 : equivW (t ++ q :: m :: s :: q :: e) w2 = true) (h3 : equivW (t ++ q :: e) w3 = true) :
    W.L (w1.map (PL.ev x y z)) + W.L (w2.map (PL.ev x y z)) =
      2 * τ.R (PL.ev x y z q) (PL.ev x y z s) (PL.ev x y z m) * W.L (w3.map (PL.ev x y z)) := by
  rw [← L_conv W _ rfl _ _ h1, ← L_conv W _ rfl _ _ h2, ← L_conv W _ rfl _ _ h3]
  simpa only [List.map_append, List.map_cons] using L_of_R2 W τ hr (e.map (PL.ev x y z))

/-- (R3_0) (Lemma 2) as a step: `L(a b c A e) + L(c b a A e) = 2 ω_b L(e)`. -/
theorem stepL2 {a b c : PL}
    (hr : W.R3Holds τ (PL.ev x y z a) (PL.ev x y z b) (PL.ev x y z c))
    (e w1 w2 w3 : List PL) (h1 : equivW (a :: b :: c :: .A :: e) w1 = true)
    (h2 : equivW (c :: b :: a :: .A :: e) w2 = true) (h3 : equivW e w3 = true) :
    W.L (w1.map (PL.ev x y z)) + W.L (w2.map (PL.ev x y z)) =
      2 * τ.om (PL.ev x y z b) * W.L (w3.map (PL.ev x y z)) := by
  rw [← L_conv W _ rfl _ _ h1, ← L_conv W _ rfl _ _ h2, ← L_conv W _ rfl _ _ h3]
  simpa only [List.map_append, List.map_cons, PL.ev_A] using L_of_R3 W τ hr (e.map (PL.ev x y z))

/-- (W1) as a step: `L(u ū) = ∏ o` along `A u`. -/
theorem stepY {u : List PL}
    (hr : W.normSq (W.pathVec (u.map (PL.ev x y z))) = τ.chainProd (0 :: u.map (PL.ev x y z)))
    (w : List PL) (h : equivW (u ++ u.reverse) w = true) :
    W.L (w.map (PL.ev x y z)) = τ.chainProd (0 :: u.map (PL.ev x y z)) := by
  rw [← L_conv W _ rfl _ _ h]
  simpa only [List.map_append, List.map_reverse] using L_of_chain W hr

/-- Lemma D as a step. -/
theorem stepD {u : List PL} {a n : PL} {r : List PL}
    (hr : W.form (W.pathVec (u.map (PL.ev x y z) ++ PL.ev x y z a :: PL.ev x y z n :: r.map (PL.ev x y z)))
        (W.pathVec (u.map (PL.ev x y z) ++ PL.ev x y z n :: r.map (PL.ev x y z))) =
      τ.R ((u.map (PL.ev x y z)).getLastD 0) (PL.ev x y z a) (PL.ev x y z n) *
        τ.chainProd (0 :: u.map (PL.ev x y z)) * τ.chainProd (PL.ev x y z n :: r.map (PL.ev x y z)))
    (w : List PL) (h : equivW ((u ++ a :: n :: r) ++ (u ++ n :: r).reverse) w = true) :
    W.L (w.map (PL.ev x y z)) =
      τ.R ((u.map (PL.ev x y z)).getLastD 0) (PL.ev x y z a) (PL.ev x y z n) *
        τ.chainProd (0 :: u.map (PL.ev x y z)) * τ.chainProd (PL.ev x y z n :: r.map (PL.ev x y z)) := by
  rw [← L_conv W _ rfl _ _ h]
  simpa only [List.map_append, List.map_cons, List.map_reverse] using L_of_delete W hr

end Walks

/-! ## Pattern rule instances and the rule package consumed by the walk lemmas -/

/-- A rule instance in pattern letters (for generic `x, y, z`).  (R3_0) is not listed: it is
the separate field `UsedRules.r3`. -/
inductive PatInst
  | r1 (t : List PL) (q v : PL)
  | r2 (t : List PL) (q s m : PL)
  | delete (u : List PL) (a n : PL) (r : List PL)
  | chain (u : List PL)
  deriving DecidableEq, Repr

namespace PatInst

/-- The interface rule instance at the assignment `(x, y, z)`.  For `r2` the first inner
letter `s` is the sandwiched one (`r2Words t q s m`). -/
def toRule (x y z : Letter) : PatInst → RuleInstance
  | r1 t q v => .r1 (yesWord (t.map (PL.ev x y z))) (PL.ev x y z q) (PL.ev x y z v)
  | r2 t q s m => .r2 (yesWord (t.map (PL.ev x y z))) (PL.ev x y z q) (PL.ev x y z s) (PL.ev x y z m)
  | delete u a n r => .delete (u.map (PL.ev x y z)) (PL.ev x y z a) (PL.ev x y z n) (r.map (PL.ev x y z))
  | chain u => .chain (u.map (PL.ev x y z))

/-- Side conditions of `Gram28Rules` for the instance (lengths; distinctness for (R2_1)). -/
def ok : PatInst → Bool
  | r1 t _ _ => decide (t.length ≤ 2)
  | r2 [] _ _ _ => true
  | r2 [c] q s m => c != q && q != s && s != m && q != m
  | r2 _ _ _ _ => false
  | delete u a n r => decide ((u ++ a :: n :: r).length ≤ 5)
  | chain u => decide (u.length ≤ 5)

/-- Coverage of the forcing words by a word set `S` (read from `p_A`).  For (R2) either choice
of the sandwiched letter will do (lem:cer:gram28 (ii)). -/
def Covered (S : Set (Word Letter)) (x y z : Letter) : PatInst → Prop
  | r2 t q s m =>
      Covers S (r2Words (yesWord (t.map (PL.ev x y z))) (PL.ev x y z q) (PL.ev x y z s) (PL.ev x y z m)) ∨
      Covers S (r2Words (yesWord (t.map (PL.ev x y z))) (PL.ev x y z q) (PL.ev x y z m) (PL.ev x y z s))
  | π => Covers S (π.toRule x y z).forcingWords

instance (S : Set (Word Letter)) [DecidablePred (· ∈ S)] (x y z : Letter) (π : PatInst) :
    Decidable (π.Covered S x y z) := by
  cases π <;> unfold Covered <;> infer_instance

end PatInst

end AlbertSequential.LengthSeven.LemmaA
