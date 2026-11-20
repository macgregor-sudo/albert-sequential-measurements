/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.AlgebraicWalkSpace
public import LengthSeven.LemmaA.Walks
public import Uniform.Main

/-! The scalar reduction rules on the conditioned walk form of a matching model. -/
set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven
open AlbertSequential

namespace WalkForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {W : WalkForm V} {τ : TraceData}

private theorem completesOrdering (i j : Letter) (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    ∃ k, IsOrderingBCD i j k := by
  fin_cases i <;> fin_cases j <;> simp at hi hj hij
  all_goals first | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩ | exact ⟨3, by decide⟩

private theorem startsOrdering (i : Letter) (hi : i ≠ 0) : ∃ j k, IsOrderingBCD i j k := by
  fin_cases i <;> simp at hi
  · exact ⟨2, 3, by decide⟩
  · exact ⟨1, 3, by decide⟩
  · exact ⟨1, 2, by decide⟩

private theorem L_reverse_context (u m v : List Letter) :
    W.L (v.reverse ++ m.reverse ++ u.reverse) = W.L (u ++ m ++ v) := by
  simpa only [List.reverse_append, List.append_assoc] using W.L_reverse (u ++ m ++ v)

private theorem L_r1_short (h : Gram28Rules W τ) (u v : List Letter) (i j : Letter)
    (hv : v.length ≤ 2) :
    W.L (u ++ [i, j, i] ++ v) = τ.o i j * W.L (u ++ [i] ++ v) := by
  have hr := LemmaA.L_of_R1 W τ
    (h.r1 (yesWord v.reverse) i j (by simpa [yesWord] using hv))
    u.reverse
  have hm := L_reverse_context (W := W) u [i, j, i] v
  have hs := L_reverse_context (W := W) u [i] v
  simp only [List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.append_assoc] at hm hs ⊢
  rw [← hm, ← hs]
  exact hr

private theorem L_r2_short (h : ShortRules W τ) (u v : List Letter) (i j k : Letter)
    (hv : v.length ≤ 1) :
    W.L (u ++ [i, j, k, i] ++ v) + W.L (u ++ [i, k, j, i] ++ v) =
      (2 * τ.R i j k) * W.L (u ++ [i] ++ v) := by
  have hr := LemmaA.L_of_R2 W τ
    (h.r2 (yesWord v.reverse) i j k (by simpa [yesWord] using hv)) u.reverse
  have hm := L_reverse_context (W := W) u [i, j, k, i] v
  have hn := L_reverse_context (W := W) u [i, k, j, i] v
  have hs := L_reverse_context (W := W) u [i] v
  simp only [List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.append_assoc] at hm hn hs ⊢
  rw [← hm, ← hn, ← hs, add_comm]
  exact hr

private theorem L_r3_short (h : ShortRules W τ) (u : List Letter) (i j k : Letter)
    (hijk : IsOrderingBCD i j k) :
    W.L (u ++ [0, i, j, k]) + W.L (u ++ [0, k, j, i]) =
      (2 * τ.om j) * W.L (u ++ [0]) := by
  have hr := LemmaA.L_of_R3 W τ (h.r3 i j k hijk) u.reverse
  have hm (a b c : Letter) :
      W.L (a :: b :: c :: 0 :: u.reverse) = W.L (u ++ [0, c, b, a]) := by
    simpa only [List.nil_append, List.append_nil, List.reverse_cons, List.reverse_nil, List.cons_append] using
      (L_reverse_context (W := W) u [0, c, b, a] [])
  rw [hm, hm, W.L_reverse, ← W.L_append_A u] at hr
  simpa only [add_comm] using hr

/-- The physical walk-form hypotheses supply the scalar interface of the
algebraic walk reducer. The rule caps also hold under reversal. -/
theorem scalarRules_of_short_and_gram28 (h : ShortRules W τ) (hG : Gram28Rules W τ) :
    AlgebraicWalkRules τ W.L where
  empty := W.L_nil
  reverse := W.L_reverse
  dropLeftA := W.L_cons_A
  dropRightA := W.L_append_A
  merge := W.L_merge
  singleton i hi := by
    obtain ⟨j,k,hijk⟩ := startsOrdering i hi
    exact LemmaA.walk_W02 (LemmaA.usedRules_of_gram28Rules hG) i j k hijk
  secondA i _ u := by
    have hr := L_r1_short hG u.reverse [] 0 i (by simp)
    have hm := L_reverse_context (W := W) [] [0, i, 0] u
    simp only [List.nil_append, List.append_nil, List.reverse_cons, List.reverse_nil,
      List.cons_append, W.L_cons_A, W.L_append_A, W.L_reverse] at hm hr
    rw [← hm]
    exact hr
  pair i j hi hj hij := by
    obtain ⟨k,hijk⟩ := completesOrdering i j hi hj hij
    exact LemmaA.walk_W03 (LemmaA.usedRules_of_gram28Rules hG) i j k hijk
  six i j k hijk := by
    rw [LemmaA.walk_W27 (LemmaA.usedRules_of_gram28Rules hG) i j k hijk]
    ring
  r1 u v i j _ hv := L_r1_short hG u v i j hv
  r2 u v i j k _ _ _ hv := L_r2_short h u v i j k hv
  r3Base i j k hijk := by
    have hr := L_r3_short h [] i j k hijk
    simp only [List.nil_append, W.L_cons_A, W.L_nil, mul_one] at hr
    exact hr
  r3AfterA := L_r3_short h

/-- A complete six-step table at the anchor yields the scalar walk rules. -/
theorem scalarRules_of_lengthSix_table {f : Word Letter → ℝ}
    (hrep : W.Reproduces {w | w.length ≤ 6} f) (hT : TableValues τ f) :
    AlgebraicWalkRules τ W.L := by
  have hS : ∀ w : Word Letter, w.length ≤ 6 → w ∈ {w | w.length ≤ 6} := fun _ h => h
  exact scalarRules_of_short_and_gram28
    (shortRules_of_table hrep hT hS)
    (Gram28Hyp.rules (gram28Hyp_of_lengthSix hrep hT hS) hrep hT)

end WalkForm

section Algebraic
variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- Seven-step matching with an initial yes on A gives the scalar rules on
the conditioned model, with the native trace data. -/
theorem lengthSeven_e3_scalarRules (M : AlgebraicProjectiveData Letter A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hm : ∀ w : Word Letter, w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :
    ∃ h : 0 < M.probability [(0, true)],
      AlgebraicWalkRules (nativeTraceData p) (WalkForm.ofAlgebraic M h).L := by
  obtain ⟨h, _, hs, _, hg⟩ := lengthSeven_e3_rules M p hp hm
  exact ⟨h, WalkForm.scalarRules_of_short_and_gram28 hs hg⟩

/-- Six-step matching from the atom at A gives the same scalar rules. -/
theorem lengthSix_pA_scalarRules (M : AlgebraicProjectiveData Letter A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hm : ∀ w : Word Letter, w.length ≤ 6 →
      M.probability w = nativeWordProbability p (p 0) w) :
    ∃ h : 0 < M.probability [(0, true)],
      AlgebraicWalkRules (nativeTraceData p) (WalkForm.ofAlgebraic M h).L := by
  have h1 : M.probability [(0, true)] = 1 := by
    rw [hm _ (by simp), val_one p hp 0 0]
    exact tracePairing_atom_self (p 0) (hp 0)
  have h : 0 < M.probability [(0, true)] := by rw [h1]; norm_num
  have hrep : (WalkForm.ofAlgebraic M h).Reproduces {w | w.length ≤ 6}
      (nativeWordProbability p (p 0)) :=
    WalkForm.ofAlgebraic_reproduces M h _ _ fun w hw => by
      rw [Uniform.probability_cons_yesA_of_certain M h1 w, h1, div_one]
      exact hm w hw
  exact ⟨h, WalkForm.scalarRules_of_lengthSix_table hrep (tableValues_native p hp)⟩

end Algebraic
end AlbertSequential.LengthSeven
