/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.TableRules

/-! # Paper-shaped rule packages

* `Gram28Hyp W τ S` is the hypothesis list (i)–(iii) of lem:cer:gram28 for a word
  set `S` read from `p_A`, with WEAKER hypotheses than printed (Lean scope broader):
  (ii) omits histories `c = q`, and (iii) holds up to null vectors.
* `Gram28Rules W τ` is the rule list that the Lemma A walk lemmas consume: pure
  vector/scalar identities on the walk form, with no table and no word set.
  `Gram28Hyp.rules` derives it from (i)–(iii), the table on `S` and `TableValues`.
* `ShortRules W τ` is STRONGER than lem:cer:short (arbitrary outcome histories,
  unrestricted letters, (W1) and Lemma D up to length six), with Lemma 2 obtained by a
  different route (the pair identity (P3)),
  derived from the table on all words of length at most six
  (`shortRules_of_table`), and it implies (i)–(iii) (`gram28Hyp_of_lengthSix`). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

open AlbertSequential

theorem covers_of_length {S : Set (Word Letter)} {N : ℕ}
    (hS : ∀ u : Word Letter, u.length ≤ N → u ∈ S) (ws : List (Word Letter))
    (h : ∀ u ∈ ws, (dropYesA u).length ≤ N) : Covers S ws :=
  fun u hu => hS _ (h u hu)

theorem dropYesA_le {u : Word Letter} {N : ℕ} (h : u.length ≤ N) : (dropYesA u).length ≤ N :=
  le_trans (dropYesA_length_le u) h

theorem r1Words_length (t : Word Letter) (q v : Letter) :
    ∀ u ∈ r1Words t q v, u.length ≤ t.length + 3 := by
  intro u hu
  simp only [r1Words, purityWords, purityMirror, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl <;> simp

theorem r2Words_length (t : Word Letter) (q s m : Letter) :
    ∀ u ∈ r2Words t q s m, u.length ≤ t.length + 5 := by
  intro u hu
  simp only [r2Words, purityWords, purityMirror, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hu
  rcases hu with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl) <;> simp

theorem lemmaDWords_length (u : List Letter) (a n : Letter) (r : List Letter) :
    ∀ w ∈ lemmaDWords u a n r, w.length ≤ (u ++ a :: n :: r).length := by
  intro w hw
  simp only [lemmaDWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> simp [yesWord]

theorem p3Words_length (x y z : Letter) : ∀ u ∈ p3Words x y z, (dropYesA u).length ≤ 6 := by
  simp [p3Words, p3PurityWords, r1Words, r2Words, purityWords, purityMirror, dropYesA]

/-- The rules consumed by the Lemma A walk lemmas (no table, no word set). -/
structure Gram28Rules {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) : Prop where
  chain : ∀ u : List Letter, u.length ≤ 5 → W.normSq (W.pathVec u) = τ.chainProd (0 :: u)
  r1 : ∀ (t : Word Letter) (q v : Letter), t.length ≤ 2 → W.R1Holds τ t q v
  r2zero : ∀ q s m : Letter, W.R2Holds τ [] q s m
  r2one : ∀ c q v w : Letter, c ≠ q → q ≠ v → v ≠ w → q ≠ w → W.R2Holds τ [(c, true)] q v w
  r3 : ∀ x y z : Letter, IsOrderingBCD x y z → W.R3Holds τ x y z
  delete : ∀ (u : List Letter) (a n : Letter) (r : List Letter), (u ++ a :: n :: r).length ≤ 5 →
    W.form (W.pathVec (u ++ a :: n :: r)) (W.pathVec (u ++ n :: r)) =
      τ.R (u.getLastD 0) a n * τ.chainProd (0 :: u) * τ.chainProd (n :: r)

/-- Hypotheses (i)–(iii) of lem:cer:gram28 for the word set `S` (words from `p_A`), weaker
than printed: in (ii) the histories `c = q` are omitted, since that instance is (R2_0)
(`P_q² = P_q`); (iii) is the paper's vector equation paired with every vector (`Eqv`). -/
structure Gram28Hyp {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) (S : Set (Word Letter)) : Prop where
  short : ∀ u : Word Letter, u.length ≤ 5 → u ∈ S
  r2one : ∀ c q v w : Letter, c ≠ q → q ≠ v → v ≠ w → q ≠ w →
    Covers S (r2Words [(c, true)] q v w) ∨ Covers S (r2Words [(c, true)] q w v)
  r3 : ∀ x y z : Letter, IsOrderingBCD x y z → W.R3Holds τ x y z

/-- Stronger than lem:cer:short (arbitrary outcome histories, no distinctness conditions,
(W1) and Lemma D up to length six); (R3_0) as a vector identity, reached by (P3). -/
structure ShortRules {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)
    (τ : TraceData) : Prop where
  chain : ∀ u : List Letter, u.length ≤ 6 → W.normSq (W.pathVec u) = τ.chainProd (0 :: u)
  r1 : ∀ (t : Word Letter) (q v : Letter), t.length ≤ 3 → W.R1Holds τ t q v
  r2 : ∀ (t : Word Letter) (q s m : Letter), t.length ≤ 1 → W.R2Holds τ t q s m
  r3 : ∀ x y z : Letter, IsOrderingBCD x y z → W.R3Holds τ x y z
  delete : ∀ (u : List Letter) (a n : Letter) (r : List Letter), (u ++ a :: n :: r).length ≤ 6 →
    W.form (W.pathVec (u ++ a :: n :: r)) (W.pathVec (u ++ n :: r)) =
      τ.R (u.getLastD 0) a n * τ.chainProd (0 :: u) * τ.chainProd (n :: r)

namespace WalkForm
variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V} {τ : TraceData}
  {S : Set (Word Letter)} {f : Word Letter → ℝ}

/-- (i)–(iii) of lem:cer:gram28, the table on `S` and the Albert table values give
the rule package of Lemma A. -/
theorem Gram28Hyp.rules (h : Gram28Hyp W τ S) (hrep : W.Reproduces S f)
    (hT : TableValues τ f) : Gram28Rules W τ where
  chain u hu := chain_of_table hrep hT u (h.short _ (dropYesA_le (by simpa [yesWord] using hu)))
  r1 t q v ht := r1_of_table hrep hT t q v
    (covers_of_length h.short _ fun u hu => dropYesA_le (by
      have := r1Words_length t q v u hu; omega))
  r2zero q s m := r2_of_table hrep hT [] q s m
    (covers_of_length h.short _ fun u hu => dropYesA_le (by
      have := r2Words_length [] q s m u hu; simpa using this))
  r2one c q v w hcq hqv hvw hqw := by
    rcases h.r2one c q v w hcq hqv hvw hqw with hc | hc
    · exact r2_of_table hrep hT _ q v w hc
    · exact (r2_of_table hrep hT _ q w v hc).comm
  r3 := h.r3
  delete u a n r hl := lemmaD_of_table hrep hT u a n r
    (covers_of_length h.short _ fun w hw => dropYesA_le (le_trans
      (lemmaDWords_length u a n r w hw) hl))

/-- The table on all words of length at most six from `p_A` gives lem:cer:short. -/
theorem shortRules_of_table (hrep : W.Reproduces S f) (hT : TableValues τ f)
    (hS : ∀ u : Word Letter, u.length ≤ 6 → u ∈ S) : ShortRules W τ where
  chain u hu := chain_of_table hrep hT u (hS _ (dropYesA_le (by simpa [yesWord] using hu)))
  r1 t q v ht := r1_of_table hrep hT t q v
    (covers_of_length hS _ fun u hu => dropYesA_le (by
      have := r1Words_length t q v u hu; omega))
  r2 t q s m ht := r2_of_table hrep hT t q s m
    (covers_of_length hS _ fun u hu => dropYesA_le (by
      have := r2Words_length t q s m u hu; omega))
  r3 := r3_of_table hrep hT 2 3 3 1 1 2 (by decide) (by decide) (by decide)
    (covers_of_length hS _ (p3Words_length _ _ _))
    (covers_of_length hS _ (p3Words_length _ _ _))
    (covers_of_length hS _ (p3Words_length _ _ _))
  delete u a n r hl := lemmaD_of_table hrep hT u a n r
    (covers_of_length hS _ fun w hw => dropYesA_le (le_trans
      (lemmaDWords_length u a n r w hw) hl))

/-- Hypothesis (H) (the table on all words of length at most six) implies (i)–(iii). -/
theorem gram28Hyp_of_lengthSix (hrep : W.Reproduces S f) (hT : TableValues τ f)
    (hS : ∀ u : Word Letter, u.length ≤ 6 → u ∈ S) : Gram28Hyp W τ S where
  short u hu := hS u (by omega)
  r2one c q v w _ _ _ _ := Or.inl (covers_of_length hS _ fun u hu => dropYesA_le (by
      have := r2Words_length [(c, true)] q v w u hu; simpa using this))
  r3 := (shortRules_of_table hrep hT hS).r3

end WalkForm
end AlbertSequential.LengthSeven
