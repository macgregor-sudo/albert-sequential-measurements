/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.WalkReductionComplete
public import LengthSeven.LemmaA.Main

@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven
namespace WalkForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V} {τ : TraceData}

private theorem r2_of_short_yes (hG : Gram28Rules W τ) (t : List Letter) (q v w : Letter)
    (hqv : q ≠ v) (hvw : v ≠ w) (hqw : q ≠ w) (ht : t.length ≤ 1) :
    W.R2Holds τ (yesWord t) q v w := by
  cases t with
  | nil => exact hG.r2zero q v w
  | cons c t =>
    have hnil : t = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_cons] at ht
      omega
    subst t
    by_cases hc : c = q
    · subst c
      intro r a
      have h := hG.r2zero q v w r a
      have hm (s : Word Letter) : W.vec ((q, true) :: (q, true) :: s) = W.vec ((q, true) :: s) :=
        W.vec_merge [] (q, true) s
      simpa only [List.nil_append, yesWord_cons, yesWord_nil, List.cons_append, hm] using h
    · exact hG.r2one c q v w hc hqv hvw hqw

private theorem L_reverse_context (u m v : List Letter) :
    W.L (v.reverse ++ m.reverse ++ u.reverse) = W.L (u ++ m ++ v) := by
  simpa only [List.reverse_append, List.append_assoc] using W.L_reverse (u ++ m ++ v)

private theorem L_r1_gram28 (hG : Gram28Rules W τ) (u v : List Letter) (i j : Letter)
    (hv : v.length ≤ 2) : W.L (u ++ [i, j, i] ++ v) = τ.o i j * W.L (u ++ [i] ++ v) := by
  have h := LemmaA.L_of_R1 W τ (hG.r1 (yesWord v.reverse) i j (by simpa [yesWord] using hv)) u.reverse
  have ha := L_reverse_context (W := W) u [i, j, i] v
  have hb := L_reverse_context (W := W) u [i] v
  simp only [List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.append_assoc] at ha hb ⊢
  rw [← ha, ← hb]
  exact h

private theorem L_r2_gram28 (hG : Gram28Rules W τ) (u v : List Letter) (i j k : Letter)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hv : v.length ≤ 1) :
    W.L (u ++ [i, j, k, i] ++ v) + W.L (u ++ [i, k, j, i] ++ v) =
      (2 * τ.R i j k) * W.L (u ++ [i] ++ v) := by
  have h := LemmaA.L_of_R2 W τ (r2_of_short_yes hG v.reverse i j k hij hjk hik (by simpa using hv)) u.reverse
  have ha := L_reverse_context (W := W) u [i, j, k, i] v
  have hb := L_reverse_context (W := W) u [i, k, j, i] v
  have hc := L_reverse_context (W := W) u [i] v
  simp only [List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.append_assoc] at ha hb hc ⊢
  rw [← ha, ← hb, ← hc, add_comm]
  exact h

private theorem L_r3_gram28 (hG : Gram28Rules W τ) (u : List Letter) (i j k : Letter)
    (hijk : IsOrderingBCD i j k) :
    W.L (u ++ [0, i, j, k]) + W.L (u ++ [0, k, j, i]) = (2 * τ.om j) * W.L (u ++ [0]) := by
  have h := LemmaA.L_of_R3 W τ (hG.r3 i j k hijk) u.reverse
  have he (a b c : Letter) : W.L (a :: b :: c :: 0 :: u.reverse) = W.L (u ++ [0, c, b, a]) := by
    simpa only [List.nil_append, List.append_nil, List.reverse_cons, List.reverse_nil, List.cons_append] using
      (L_reverse_context (W := W) u [0, c, b, a] [])
  rw [he, he, W.L_reverse, ← W.L_append_A u] at h
  simpa only [add_comm] using h

/-- The printed shorter-word hypotheses suffice for the scalar walk rules. -/
theorem scalarRules_of_gram28Rules (hG : Gram28Rules W τ) : AlgebraicWalkRules τ W.L where
  empty := W.L_nil
  reverse := W.L_reverse
  dropLeftA := W.L_cons_A
  dropRightA := W.L_append_A
  merge := W.L_merge
  singleton i hi := by
    have he : ∃ j k, IsOrderingBCD i j k := by
      fin_cases i <;> simp at hi
      · exact ⟨2, 3, by decide⟩
      · exact ⟨1, 3, by decide⟩
      · exact ⟨1, 2, by decide⟩
    obtain ⟨j, k, hijk⟩ := he
    exact LemmaA.walk_W02 (LemmaA.usedRules_of_gram28Rules hG) i j k hijk
  secondA i _ u := by
    have h := L_r1_gram28 hG u.reverse [] 0 i (by simp)
    have hr := L_reverse_context (W := W) [] [0, i, 0] u
    simp only [List.nil_append, List.append_nil, List.reverse_cons, List.reverse_nil,
      List.cons_append, W.L_cons_A, W.L_append_A, W.L_reverse] at hr h
    rw [← hr]
    exact h
  pair i j hi hj hij := by
    have he : ∃ k, IsOrderingBCD i j k := by
      fin_cases i <;> fin_cases j <;> simp at hi hj hij
      all_goals first | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩ | exact ⟨3, by decide⟩
    obtain ⟨k, hijk⟩ := he
    exact LemmaA.walk_W03 (LemmaA.usedRules_of_gram28Rules hG) i j k hijk
  six i j k hijk := by
    rw [LemmaA.walk_W27 (LemmaA.usedRules_of_gram28Rules hG) i j k hijk]
    ring
  r1 u v i j _ hv := L_r1_gram28 hG u v i j hv
  r2 u v i j k hij hjk hik hv := L_r2_gram28 hG u v i j k hij hjk hik hv
  r3Base i j k hijk := by
    have h := L_r3_gram28 hG [] i j k hijk
    simpa only [List.nil_append, W.L_cons_A, W.L_nil, mul_one] using h
  r3AfterA := L_r3_gram28 hG

theorem gram_eq_upsilon_of_gram28Hyp {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (h : Gram28Hyp W τ S) (hrep : W.Reproduces S f) (ht : TableValues τ f)
    (u v : List Letter) (hu : u.length ≤ 4) (hv : v.length ≤ 4) :
    W.form (W.pathVec u) (W.pathVec v) = MvPolynomial.eval₂ (Int.castRingHom ℝ)
      (walkTraceCoordinates τ) (walkUpsilon (u ++ v.reverse)) := by
  have hb : (u ++ v.reverse).length ≤ 8 := by rw [List.length_append, List.length_reverse]; omega
  rw [W.form_pathVec, walkUpsilon, dite_eq_left hb, WalkPolynomial.eval_toMvPolynomial]
  exact (hasWalkPolynomial_of_length_le_eight _ hb).choose_spec τ W.L
    (scalarRules_of_gram28Rules (WalkForm.Gram28Hyp.rules h hrep ht))

end WalkForm
end AlbertSequential.LengthSeven
