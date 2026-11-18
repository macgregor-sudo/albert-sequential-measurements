/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Assembly

/-! # Infrastructure for lem:cer:h5:lift (recognition through length five)

* `RecognitionThroughFivePos`: the typed statement `RecognitionThroughFive` of `Lemmas.lean`
  restricted to `1 ≤ n`.  The unrestricted typed statement is unsatisfiable at `n = 0`
  (`not_recognitionThroughFive`): for `y = 0` it asks for a Jordan expression of degree `0` that
  is syntactically of degree one in `x_j`.  The paper's lemma reads "degree one in `x_j`" for the
  zero polynomial as vacuous; every use (the descent of lem:cer:h5:seven) has `n ≥ 2`.
* Notation for lifts (`jX`, `jM`, `jU`, `jT`) and their special values;
* Boolean checkers `linB`/`freeB` for `LinearIn`/`FreeOf` (decided by the kernel per lift);
* `LiftP l`: the per-word lift property, closed under reversal (`liftP_rev`);
* `allWords n` (all words of length at most `n`) and the filter `goodB`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## The statement used, and why the unrestricted typed one fails -/

/-- **lem:cer:h5:lift for `1 ≤ n ≤ 5`.** Identical to `RecognitionThroughFive` except for the
hypothesis `1 ≤ n`. -/
def RecognitionThroughFivePos : Prop :=
  ∀ (n : ℕ), 1 ≤ n → n ≤ 5 → ∀ (j : Test) (y : List Test →₀ ℝ),
    (∀ l ∈ y.support, reducedB l = true ∧ l.length ≤ n ∧ l.count j = 1) →
    (∀ l, y l.reverse = y l) →
    (y.sum fun l a => a * (cliffVol l : ℝ)) = 0 →
    ∃ K : JPoly Test, K.deg ≤ n ∧ K.LinearIn j ∧
      specialEval K = y.sum fun l a => a • groupElt l

theorem JPoly.LinearIn.deg_pos {j : Test} {K : JPoly Test} (h : K.LinearIn j) : 1 ≤ K.deg := by
  induction h with
  | var => simp [JPoly.deg]
  | add a b _ _ ha _ => simp only [JPoly.deg]; omega
  | smul r a _ ha => simpa [JPoly.deg] using ha
  | mulLeft a b _ _ ha => simp only [JPoly.deg]; omega
  | mulRight a b _ _ hb => simp only [JPoly.deg]; omega

/-- The typed statement `RecognitionThroughFive` is false (case `n = 0`, `y = 0`). -/
theorem not_recognitionThroughFive : ¬ RecognitionThroughFive := by
  intro h
  obtain ⟨K, hK, hlin, -⟩ := h 0 (by norm_num) 0 0 (by simp) (by simp) (by simp)
  have := hlin.deg_pos
  omega

/-! ## Notation for lifts and their special values -/

/-- The letter `x_i`. -/
def jX (i : Test) : JPoly Test := .var i
/-- The Jordan product `a ∘ b`. -/
def jM (a b : JPoly Test) : JPoly Test := .mul a b
/-- `U_a b`. -/
def jU (a b : JPoly Test) : JPoly Test := JPoly.U a b
/-- The triple product `{a, b, c}`. -/
def jT (a b c : JPoly Test) : JPoly Test := JPoly.triple a b c

theorem sE_X (i : Test) : specialEval (jX i) = specialSymmetry i := rfl

theorem sE_M (a b : JPoly Test) : specialEval (jM a b) =
    (1 / 2 : ℝ) • (specialEval a * specialEval b + specialEval b * specialEval a) := rfl

theorem sE_U (a b : JPoly Test) :
    specialEval (jU a b) = specialEval a * specialEval b * specialEval a := by
  change (specialTarget _).eval specialSymmetry (JPoly.U a b) = _
  rw [JTarget.eval_U, specialTarget_Uop]
  rfl

theorem sE_T (a b c : JPoly Test) : specialEval (jT a b c) =
    (1 / 2 : ℝ) • (specialEval a * specialEval b * specialEval c +
      specialEval c * specialEval b * specialEval a) := by
  change (specialTarget _).eval specialSymmetry (JPoly.triple a b c) = _
  rw [eval_triple, special_tripleOp]
  rfl

theorem sE_add (a b : JPoly Test) :
    specialEval (.add a b) = specialEval a + specialEval b := rfl

theorem sE_smul (r : ℝ) (a : JPoly Test) : specialEval (.smul r a) = r • specialEval a := rfl

theorem groupElt_nil' : groupElt ([] : List Test) = 1 := by simp [groupElt]

/-! ## Boolean checkers for `LinearIn` and `FreeOf` -/

/-- Boolean `FreeOf`. -/
def freeB (j : Test) : JPoly Test → Bool
  | .one => true
  | .var x => !decide (x = j)
  | .add a b => freeB j a && freeB j b
  | .smul _ a => freeB j a
  | .mul a b => freeB j a && freeB j b

/-- Boolean `LinearIn`. -/
def linB (j : Test) : JPoly Test → Bool
  | .one => false
  | .var x => decide (x = j)
  | .add a b => linB j a && linB j b
  | .smul _ a => linB j a
  | .mul a b => (linB j a && freeB j b) || (freeB j a && linB j b)

theorem linB_sound (j : Test) (K : JPoly Test) :
    (linB j K = true → K.LinearIn j) ∧ (freeB j K = true → K.FreeOf j) := by
  induction K with
  | one => exact ⟨fun h => by simp [linB] at h, fun _ => .one⟩
  | var x =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [linB, decide_eq_true_eq] at h
      subst h; exact .var
    · simp only [freeB, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact .var x h
  | add a b ha hb =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [linB, Bool.and_eq_true] at h
      exact .add _ _ (ha.1 h.1) (hb.1 h.2)
    · simp only [freeB, Bool.and_eq_true] at h
      exact .add _ _ (ha.2 h.1) (hb.2 h.2)
  | smul r a ha =>
    exact ⟨fun h => .smul _ _ (ha.1 h), fun h => .smul _ _ (ha.2 h)⟩
  | mul a b ha hb =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [linB, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | h
      · exact .mulLeft _ _ (ha.1 h.1) (hb.2 h.2)
      · exact .mulRight _ _ (ha.2 h.1) (hb.1 h.2)
    · simp only [freeB, Bool.and_eq_true] at h
      exact .mul _ _ (ha.2 h.1) (hb.2 h.2)

/-! ## The per-word lift property -/

/-- The reference four-letter word `r_0 r_1 r_2 r_3` (`ℓ = 1`). -/
def wordRef : List Test := [0, 1, 2, 3]

/-- `l` has a lift of degree at most `|l|`, of degree one in every letter occurring once in `l`,
with special value `[l] - ℓ(l) [r_0 r_1 r_2 r_3]`. -/
def LiftP (l : List Test) : Prop :=
  ∃ K : JPoly Test, K.deg ≤ l.length ∧ (∀ j, l.count j = 1 → K.LinearIn j) ∧
    specialEval K = classElt l - (cliffVol l : ℝ) • classElt wordRef

theorem liftP_of (l : List Test) (K : JPoly Test) (k : ℤ) (hk : cliffVol l = k)
    (hdeg : K.deg ≤ l.length) (hlin : ∀ j, l.count j = 1 → linB j K = true)
    (hspec : specialEval K = classElt l - (k : ℝ) • classElt wordRef) : LiftP l :=
  ⟨K, hdeg, fun j hj => (linB_sound j K).1 (hlin j hj), by rw [hk]; exact hspec⟩

theorem liftP_rev {l m : List Test} (h : LiftP l) (hm : l.reverse = m)
    (hk : cliffVol m = cliffVol l) : LiftP m := by
  subst hm
  obtain ⟨K, h1, h2, h3⟩ := h
  refine ⟨K, by rw [List.length_reverse]; exact h1, fun j hj => h2 j (by rwa [List.count_reverse] at hj), ?_⟩
  rw [hk, classElt_reverse]
  exact h3

/-- The proof of the special value of a lift: expand both sides in `ℝ[G]`. -/
macro "lift_spec" : tactic => `(tactic| (
  simp only [sE_X, sE_M, sE_U, sE_T, sE_add, sE_smul, classElt, wordRef, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append, groupElt_cons,
    groupElt_nil', mul_one, one_mul, mul_add, add_mul, smul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_assoc, specialSymmetry_mul_self, specialSymmetry_mul_self', Int.cast_zero,
    Int.cast_one, Int.cast_neg, zero_smul, sub_zero, neg_smul, one_smul, sub_neg_eq_add]
  try module))

/-! ## All words of length at most `n` -/

/-- All words of length at most `n`. -/
def allWords : ℕ → List (List Test)
  | 0 => [[]]
  | n + 1 => [] :: (allWords n).flatMap fun l => [0 :: l, 1 :: l, 2 :: l, 3 :: l]

theorem mem_allWords : ∀ (n : ℕ) (l : List Test), l.length ≤ n → l ∈ allWords n
  | 0, l, h => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]; simp [allWords]
  | n + 1, [], _ => by simp [allWords]
  | n + 1, a :: t, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    have ht := mem_allWords n t h
    simp only [allWords, List.mem_cons, List.mem_flatMap]
    right
    refine ⟨t, ht, ?_⟩
    fin_cases a <;> simp

/-- Reduced, with some letter occurring exactly once. -/
def goodB (l : List Test) : Bool :=
  reducedB l && (l.count 0 == 1 || l.count 1 == 1 || l.count 2 == 1 || l.count 3 == 1)

theorem goodB_of {l : List Test} {j : Test} (hr : reducedB l = true) (hj : l.count j = 1) :
    goodB l = true := by
  simp only [goodB, hr, Bool.true_and, Bool.or_eq_true, beq_iff_eq]
  fin_cases j <;> simp_all

end AlbertSequential.HorizonFive
