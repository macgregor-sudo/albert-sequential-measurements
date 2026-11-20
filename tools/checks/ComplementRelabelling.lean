module

import Bridge.PrintedCriterion

open AlbertSequential

noncomputable section

namespace PrintedMixedMenuPeer

def orient {X : Type*} (flip : X → Bool) (p : X → Albert) (i : X) : Albert :=
  if flip i then albertUnit - p i else p i

def relabel {X : Type*} (flip : X → Bool) (a : Outcome X) : Outcome X :=
  (a.1, if flip a.1 then !a.2 else a.2)

theorem generated_orient {X : Type*} (flip : X → Bool) (p : X → Albert) :
    generatedSubalgebra (Set.range (orient flip p)) = generatedSubalgebra (Set.range p) := by
  apply le_antisymm <;> apply generatedSubalgebra_le
  · rintro _ ⟨i,rfl⟩
    have hp := subset_generatedSubalgebra (Set.range p) ⟨i,rfl⟩
    cases h : flip i with
    | false => simpa [orient,h] using hp
    | true => simpa [orient,h] using
        (generatedSubalgebra (Set.range p)).carrier.sub_mem (generatedSubalgebra (Set.range p)).unit_mem hp
  · rintro _ ⟨i,rfl⟩
    let B := generatedSubalgebra (Set.range (orient flip p))
    have hm : orient flip p i ∈ B.carrier := subset_generatedSubalgebra _ ⟨i,rfl⟩
    cases h : flip i with
    | false => simpa [orient,h] using hm
    | true => simpa [orient,h,sub_sub_cancel] using B.carrier.sub_mem B.unit_mem hm

theorem outcome_orient {X : Type*} (flip : X → Bool) (p : X → Albert) (a : Outcome X) :
    nativeOutcome (orient flip p) a = nativeOutcome p (relabel flip a) := by
  rcases a with ⟨i,b⟩
  cases h : flip i <;> cases b <;> simp [orient, relabel, nativeOutcome, h, sub_sub_cancel]

theorem probability_orient {X : Type*} (flip : X → Bool) (p : X → Albert) (ρ : Albert) (w : Word X) :
    nativeWordProbability (orient flip p) ρ w = nativeWordProbability p ρ (w.map (relabel flip)) := by
  unfold nativeWordProbability nativeBranchState
  rw [List.foldl_map]
  simp only [outcome_orient]

#print axioms generated_orient
#print axioms probability_orient

end PrintedMixedMenuPeer
