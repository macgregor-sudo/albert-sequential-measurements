/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.WalkReductionGuide
public import LengthSeven.WalkReductionGuideData

/-! Bounded finite coverage only for the walks with no repeated letters
within two places. The other walks are shortened symbolically. -/

set_option autoImplicit false
@[expose] public section

namespace AlbertSequential.LengthSeven

/-- No repetition at distance one or two. -/
def separatedWalk : List Letter → Bool
  | [] => true
  | i :: v => !(v.take 2).contains i && separatedWalk v

theorem separatedWalk_of_append (u v : List Letter) (h : separatedWalk (u ++ v) = true) :
    separatedWalk v = true := by
  induction u with
  | nil => exact h
  | cons i u ih => exact ih (Bool.and_eq_true_iff.mp h).2

theorem not_separatedWalk_pattern (w : List Letter) (h : separatedWalk w = false) :
    (∃ u i v, w = u ++ [i, i] ++ v) ∨ (∃ u i j v, i ≠ j ∧ w = u ++ [i, j, i] ++ v) := by
  induction w with
  | nil => contradiction
  | cons i w ih =>
    by_cases hr : (w.take 2).contains i
    · have hm := List.contains_iff_mem.mp hr
      cases w with
      | nil => simp at hm
      | cons j r =>
        by_cases hij : i = j
        · subst j; exact .inl ⟨[], i, r, rfl⟩
        · cases r with
          | nil => simp [hij] at hm
          | cons k v =>
            have hik : i = k := by simpa [hij] using hm
            subst k
            exact .inr ⟨[], i, j, v, hij, rfl⟩
    · have hwfalse : (w.take 2).contains i = false := by
        cases he : (w.take 2).contains i <;> simp_all
      have ht : separatedWalk w = false := by
        simpa only [separatedWalk, hwfalse, Bool.not_false, Bool.true_and] using h
      rcases ih ht with ⟨u, j, v, rfl⟩ | ⟨u, j, k, v, hjk, rfl⟩
      · exact .inl ⟨i :: u, j, v, rfl⟩
      · exact .inr ⟨i :: u, j, k, v, hjk, rfl⟩

/-- At an end, `A` in one of the first two places permits immediate shortening. -/
def headShortener : List Letter → Bool
  | [] => false
  | [i] => i == 0
  | i :: j :: _ => (i == 0) || (j == 0)

def finishSeparatedWalk (w : List Letter) : Option (WalkPolynomial × List ℕ) :=
  let codes := walkGuideData[w.length]?.getD []
  guidedWalk 9 w ((codes.lookup (encodeWalk w)).getD [])

def settledWalk (w : List Letter) : Bool :=
  (headShortener w || headShortener w.reverse) || (finishSeparatedWalk w).isSome

/-- Check the remaining prefix letters with only separated branches visited. -/
def checkSeparatedWalkReduction : ℕ → List Letter → Bool
  | 0, w => settledWalk w
  | n + 1, w => (List.ofFn (fun i : Letter => i)).all fun i =>
    if (w.take 2).contains i then true else checkSeparatedWalkReduction n (i :: w)

theorem checkSeparatedWalkReduction_sound (n : ℕ) (w : List Letter)
    (h : checkSeparatedWalkReduction n w = true)
    (v : List Letter) (hv : v.length = n) (hs : separatedWalk (v ++ w) = true) :
    settledWalk (v ++ w) = true := by
  induction n generalizing v w with
  | zero =>
    have hv' : v = [] := List.length_eq_zero_iff.mp hv
    subst v
    exact h
  | succ n ih =>
    change (List.ofFn (fun i : Letter => i)).all (fun i =>
      if (w.take 2).contains i then true else checkSeparatedWalkReduction n (i :: w)) = true at h
    have hall := List.all_eq_true.mp h
    cases hr : v.reverse with
    | nil =>
      have hv' := congrArg List.reverse hr
      simp only [List.reverse_reverse, List.reverse_nil] at hv'
      simp [hv'] at hv
    | cons i rest =>
      have hv' := congrArg List.reverse hr
      simp only [List.reverse_reverse, List.reverse_cons] at hv'
      have hi : i ∈ List.ofFn (fun i : Letter => i) := List.mem_ofFn.mpr ⟨i, rfl⟩
      rw [hv'] at hv hs ⊢
      simp only [List.append_assoc, List.singleton_append] at hs ⊢
      have hu : rest.reverse.length = n := by simpa using hv
      have ht := separatedWalk_of_append rest.reverse (i :: w) hs
      have hm : (w.take 2).contains i = false := by
        cases he : (w.take 2).contains i <;> simp_all [separatedWalk]
      exact ih (i :: w) (by simpa only [hm, Bool.false_eq_true, ↓reduceIte] using hall i hi)
        rest.reverse hu hs

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem checkSeparatedShort (n : Fin 6) : checkSeparatedWalkReduction n.val [] = true := by
  fin_cases n <;> decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem checkSeparatedSuffix (n : Fin 3) (i j : Letter) :
    (if i = j then true else checkSeparatedWalkReduction (n.val + 4) [i, j]) = true := by
  fin_cases n <;> fin_cases i <;> fin_cases j <;> decide +kernel

/-- Exhaustion is separate from the semantic soundness theorem. To keep peak
kernel working memory small, checks at lengths six through eight run by suffix. -/
theorem checkSeparatedWalkReduction_through_eight (n : Fin 9) :
    checkSeparatedWalkReduction n.val [] = true := by
  by_cases hn : n.val < 6
  · exact checkSeparatedShort ⟨n.val, hn⟩
  · let k : Fin 3 := ⟨n.val - 6, by omega⟩
    have hk : n.val = k.val + 4 + 1 + 1 := by change n.val = n.val - 6 + 4 + 1 + 1; omega
    rw [hk]
    change (List.ofFn (fun j : Letter => j)).all (fun j =>
      if (([] : List Letter).take 2).contains j then true
      else checkSeparatedWalkReduction (k.val + 4 + 1) [j]) = true
    apply List.all_eq_true.mpr
    intro j _
    change checkSeparatedWalkReduction (k.val + 4 + 1) [j] = true
    change (List.ofFn (fun i : Letter => i)).all (fun i =>
      if ([j].take 2).contains i then true else checkSeparatedWalkReduction (k.val + 4) [i, j]) = true
    apply List.all_eq_true.mpr
    intro i _
    simpa [List.contains_iff_mem] using checkSeparatedSuffix k i j

theorem settledWalk_complete_separated (w : List Letter) (hw : w.length ≤ 8)
    (hs : separatedWalk w = true) : settledWalk w = true := by
  have h := checkSeparatedWalkReduction_sound w.length []
    (checkSeparatedWalkReduction_through_eight ⟨w.length, by omega⟩) w rfl
    (by simpa only [List.append_nil] using hs)
  simpa only [List.append_nil] using h

/-- A universal symbolic polynomial, with all real data quantified after its choice. -/
def HasWalkPolynomial (w : List Letter) : Prop :=
  ∃ p : WalkPolynomial, ∀ τ L, AlgebraicWalkRules τ L → L w = p.eval (walkTraceCoordinates τ)

private theorem AlgebraicWalkRules.r1_left {τ : TraceData} {L : List Letter → ℝ}
    (h : AlgebraicWalkRules τ L) (u v : List Letter) (i j : Letter) (hij : i ≠ j) (hu : u.length ≤ 2) :
    L (u ++ [i, j, i] ++ v) = τ.o i j * L (u ++ [i] ++ v) := by
  have h' := h.r1 v.reverse u.reverse i j hij (by simpa using hu)
  have h1 : L (v.reverse ++ [i, j, i] ++ u.reverse) = L (u ++ [i, j, i] ++ v) := by
    have hr := h.reverse (u ++ [i, j, i] ++ v)
    simpa [List.reverse_append, List.append_assoc] using hr
  have h2 : L (v.reverse ++ [i] ++ u.reverse) = L (u ++ [i] ++ v) := by
    have hr := h.reverse (u ++ [i] ++ v)
    simpa [List.reverse_append, List.append_assoc] using hr
  rwa [h1, h2] at h'

private theorem headShortener_sound (w : List Letter) (h : headShortener w = true) :
    ∃ (u : List Letter) (c : WalkPolynomial), u.length < w.length ∧
      ∀ τ L, AlgebraicWalkRules τ L → L w = c.eval (walkTraceCoordinates τ) * L u := by
  cases w with
  | nil => contradiction
  | cons i w =>
    by_cases h0 : i = 0
    · subst i
      refine ⟨w, .integer 1, by simp, fun τ L hL => ?_⟩
      simpa [WalkPolynomial.eval] using hL.dropLeftA w
    · cases w with
      | nil => simp [headShortener, h0] at h
      | cons j w =>
        have hj : j = 0 := by simpa [headShortener, h0] using h
        subst j
        refine ⟨w, .overlap 0 i, by simp, fun τ L hL => ?_⟩
        simpa [WalkPolynomial.eval, WalkPolynomial.overlap, walkTraceCoordinates_overlap τ 0 i (Ne.symm h0)]
          using hL.secondA i h0 w

theorem hasWalkPolynomial_of_length_le_eight (w : List Letter) (hw : w.length ≤ 8) : HasWalkPolynomial w := by
  have general (n : ℕ) : ∀ w : List Letter, w.length = n → w.length ≤ 8 → HasWalkPolynomial w := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro w hn hw
      by_cases hs : separatedWalk w = true
      · have hsettled := settledWalk_complete_separated w hw hs
        unfold settledWalk at hsettled
        rcases Bool.or_eq_true_iff.mp hsettled with h | h
        · rcases Bool.or_eq_true_iff.mp h with h | h
          · obtain ⟨u, c, hu, hc⟩ := headShortener_sound w h
            have hn' : u.length < n := hn ▸ hu
            obtain ⟨q, hq⟩ := ih _ hn' u rfl (by omega)
            exact ⟨.mul c q, fun τ L hL => by rw [hc τ L hL, hq τ L hL]; rfl⟩
          · obtain ⟨u, c, hu, hc⟩ := headShortener_sound w.reverse h
            rw [List.length_reverse] at hu
            have hn' : u.length < n := hn ▸ hu
            obtain ⟨q, hq⟩ := ih _ hn' u rfl (by omega)
            exact ⟨.mul c q, fun τ L hL => by
              rw [← hL.reverse w, hc τ L hL, hq τ L hL]; rfl⟩
        · cases hp : finishSeparatedWalk w with
          | none => simp [hp] at h
          | some result =>
            obtain ⟨p, tail⟩ := result
            exact ⟨p, fun τ L hL => guidedWalk_sound τ L hL 9 w _ hp⟩
      · have hfalse : separatedWalk w = false := by
          cases he : separatedWalk w <;> simp_all
        rcases not_separatedWalk_pattern w hfalse with ⟨u, i, v, rfl⟩ | ⟨u, i, j, v, hij, rfl⟩
        · have hlt : (u ++ [i] ++ v).length < n := by simp at hn ⊢; omega
          have hb : (u ++ [i] ++ v).length ≤ 8 := by omega
          obtain ⟨p, hp⟩ := ih _ hlt _ rfl hb
          refine ⟨p, fun τ L h => ?_⟩
          have he := h.merge u i v
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            he.trans (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hp τ L h)
        · have hlt : (u ++ [i] ++ v).length < n := by simp at hn ⊢; omega
          have hb : (u ++ [i] ++ v).length ≤ 8 := by omega
          obtain ⟨p, hp⟩ := ih _ hlt _ rfl hb
          refine ⟨.mul (.overlap i j) p, fun τ L h => ?_⟩
          have hh : u.length ≤ 2 ∨ v.length ≤ 2 := by simp at hw; omega
          have he := hh.elim (fun hu => h.r1_left u v i j hij hu) (fun hv => h.r1 u v i j hij hv)
          rw [he, hp τ L h]
          simp [WalkPolynomial.eval, WalkPolynomial.overlap, walkTraceCoordinates_overlap τ i j hij]
  exact general w.length w rfl hw

/-- The integer polynomial for the given walk, independent of the real form
and the values of the thirteen parameters. -/
noncomputable def walkUpsilon (w : List Letter) : MvPolynomial (Fin 13) ℤ :=
  if hw : w.length ≤ 8 then (hasWalkPolynomial_of_length_le_eight w hw).choose.toMvPolynomial else 0

/-- Core Lemma 6.6 on an arbitrary symmetric bilinear walk space. -/
theorem algebraicWalk_L_eq_upsilon {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : AlgebraicWalkSpace V) (τ : TraceData) (h : AlgebraicWalkHypotheses W τ)
    (w : List Letter) (hw : w.length ≤ 8) :
    W.L w = MvPolynomial.eval₂ (Int.castRingHom ℝ) (walkTraceCoordinates τ) (walkUpsilon w) := by
  rw [walkUpsilon, dite_eq_left hw, WalkPolynomial.eval_toMvPolynomial]
  exact (hasWalkPolynomial_of_length_le_eight w hw).choose_spec τ W.L h.scalarRules

/-- The paper's Gram conclusion for every pair of paths of length at most four. -/
theorem algebraicWalk_gram_eq_upsilon {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : AlgebraicWalkSpace V) (τ : TraceData) (h : AlgebraicWalkHypotheses W τ)
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    W.form (W.pathVec u) (W.pathVec v) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (walkTraceCoordinates τ) (walkUpsilon (u ++ v.reverse)) := by
  rw [W.form_pathVec]
  apply algebraicWalk_L_eq_upsilon W τ h
  rw [List.length_append, List.length_reverse]
  omega

end AlbertSequential.LengthSeven
