/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Interfaces.WordsAndCertificates
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section
noncomputable section
namespace AlbertSequential.FixedUnitary
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (U : E ≃ₗ[K] E) (P : I → Module.End K E)

def answer (q : Outcome I) : Module.End K E := if q.2 then P q.1 else 1 - P q.1

def trajectory (x : E) (w : Word I) : E := w.foldl (fun v q => U (answer P q v)) x

omit [FiniteDimensional K E] in
theorem trajectory_snoc (x : E) (w : Word I) (q : Outcome I) :
    trajectory U P x (w++[q]) = U (answer P q (trajectory U P x w)) := by
  simp [trajectory,List.foldl_append]

/-- In finite dimension, zero opposite-answer amplitudes imply that insertion
of a fixed reversible map alters each reachable word only by a final power. -/
theorem remove_between (x : E)
    (h : ∀ w i (b : Bool), answer P (i,!b) (U (answer P (i,b) (trajectory U P x w))) = 0)
    (w : Word I) :
    trajectory U P x w = (U.toLinearMap ^ w.length) (w.foldl (fun v q => answer P q v) x) := by
  classical
  let S := Submodule.span K (Set.range (trajectory U P x))
  have hroot : x ∈ S := Submodule.subset_span ⟨[],rfl⟩
  have advance (q : Outcome I) : S ≤ S.comap (U.toLinearMap.comp (answer P q)) := by
    apply Submodule.span_le.mpr
    rintro y ⟨v,rfl⟩
    exact Submodule.subset_span ⟨v++[q],trajectory_snoc U P x v q⟩
  have kill (i : I) (b : Bool) (y : E) (hy : y ∈ S) : answer P (i,!b) (U (answer P (i,b) y)) = 0 := by
    let B := (answer P (i,!b)).comp (U.toLinearMap.comp (answer P (i,b)))
    have hs : S ≤ LinearMap.ker B := Submodule.span_le.mpr (by rintro _ ⟨v,rfl⟩; exact h v i b)
    exact hs hy
  have Umem (i : I) {y : E} (hy : y ∈ S) : U y ∈ S := by
    have ht := advance (i,true) hy
    have hf := advance (i,false) hy
    change U (P i y) ∈ S at ht
    change U (y-P i y) ∈ S at hf
    rw [map_sub] at hf
    simpa using S.add_mem hf ht
  have Qmem (q : Outcome I) {y : E} (hy : y ∈ S) : answer P q y ∈ S := by
    have hm : S.map U.toLinearMap ≤ S := Submodule.map_le_iff_le_comap.mpr (fun _ hz => Umem q.1 hz)
    have he := Submodule.eq_of_le_of_finrank_eq hm (U.finrank_map_eq S)
    have hmem : U (answer P q y) ∈ S := advance q hy
    rw [← he] at hmem
    obtain ⟨z,hz,heq⟩ := hmem
    exact U.injective heq ▸ hz
  have commute (q : Outcome I) {y : E} (hy : y ∈ S) : answer P q (U y) = U (answer P q y) := by
    obtain ⟨i,b⟩ := q
    have hleft := kill i false y hy
    have hright := kill i true y hy
    change P i (U (y-P i y)) = 0 at hleft
    change U (P i y) - P i (U (P i y)) = 0 at hright
    rw [map_sub,map_sub] at hleft
    have hh : P i (U y) = U (P i y) := (sub_eq_zero.mp hleft).trans (sub_eq_zero.mp hright).symm
    cases b
    · change U y - P i (U y) = U (y-P i y); rw [map_sub,hh]
    · exact hh
  have iter (q : Outcome I) {y : E} (hy : y ∈ S) (n : ℕ) :
      (U.toLinearMap^n) y ∈ S ∧ answer P q ((U.toLinearMap^n) y) = (U.toLinearMap^n) (answer P q y) := by
    induction n with
    | zero => exact ⟨hy,rfl⟩
    | succ n ih =>
      rw [pow_succ']
      exact ⟨Umem q.1 ih.1,(commute q ih.1).trans (congrArg U ih.2)⟩
  suffices result : w.foldl (fun v q => answer P q v) x ∈ S ∧
      trajectory U P x w = (U.toLinearMap ^ w.length) (w.foldl (fun v q => answer P q v) x) from result.2
  induction w using List.reverseRecOn with
  | nil => exact ⟨hroot,rfl⟩
  | append_singleton w q ih =>
    rw [List.foldl_append,trajectory_snoc,List.length_append,List.length_singleton,pow_succ']
    refine ⟨Qmem q ih.1,?_⟩
    rw [ih.2,(iter q ih.1 w.length).2]
    rfl

end AlbertSequential.FixedUnitary
