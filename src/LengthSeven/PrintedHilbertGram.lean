/- SPDX-License-Identifier: Apache-2.0 -/
module
public import LengthSeven.PrintedPhysicalGram
public import PaperRobustVectors

@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven
open scoped InnerProductSpace
open Robust

/-- Appendix C.1 at the literal Hilbert-space hypothesis (H). In the displayed
vector and scalar relations the histories are the actual chronological amplitudes. -/
theorem printedGram_of_H {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Letter → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i)) (ξ : H) (hfix : P 0 ξ = ξ)
    (hu : ‖ξ‖ = 1) (p : Fin 4 → Albert) (hat : ∀ i, IsAtom (p i))
    (hm : ∀ w : Word Letter, w.length ≤ 6 → ‖wordAmplitude P w ξ‖^2 = nativeWordProbability p (p 0) w) :
    let path := fun u => wordAmplitude P (yesWord u) ξ
    let τ := nativeTraceData p
    ∀ x y z, IsOrderingBCD x y z →
      (path [x,y,z,0] + path [z,y,x,0] = (2*τ.om y) • ξ) ∧
      (path [x,y,z,x] + path [x,z,y,x] = (2*τ.R x y z) • path [x]) ∧
      (∀ i j, let uv := printedHistories x y z i j
        ⟪path uv.1,path uv.2⟫_ℝ = printedGramTable (printedTraces τ x y z) i j) := by
  have hn : ξ ≠ 0 := by intro h; simp [h] at hu
  let W := cornerVectorWalk P hp ξ hfix hn
  have hv (w : Word Letter) : W.vec w = wordAmplitude P w ξ :=
    cornerVectorWalk_seqL P hp ξ hfix hn w ξ
  have hf (a b : H) : W.form a b = ⟪a,b⟫_ℝ := by
    change (‖ξ‖^2)⁻¹ * _ = _
    rw [hu]; norm_num
  have eq {a b : H} (h : W.Eqv a b) : a = b := by
    apply ext_inner_right ℝ
    intro z
    simpa only [← hf] using h z
  have hr : W.Reproduces {w | w.length ≤ 6} (nativeWordProbability p (p 0)) := by
    intro w hw
    rw [WalkForm.normSq,hf,hv,real_inner_self_eq_norm_sq]
    exact hm w hw
  have hT := tableValues_native p hat
  have hs := WalkForm.shortRules_of_table hr hT (fun _ hw => hw)
  intro path τ x y z hx
  refine ⟨?_,?_,?_⟩
  · have hh := eq (hs.r3 x y z hx [])
    simpa only [path,τ,yesWord_cons,yesWord_nil,WalkForm.piC,List.append_nil,hv,wordAmplitude_nil,one_apply_eq_self] using hh
  · have hh := eq (hs.r2 [] x y z (by simp) [])
    simpa only [path,τ,yesWord_cons,yesWord_nil,List.nil_append,List.append_nil,hv] using hh
  · intro i j
    have hh := hasPrintedGram_of_scalarRules (WalkForm.scalarRules_of_lengthSix_table hr hT) x y z hx i j
    simpa only [hf,WalkForm.pathVec,hv] using hh

end AlbertSequential.LengthSeven
