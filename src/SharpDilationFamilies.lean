/- SPDX-License-Identifier: Apache-2.0 -/
module
public import SharpDilationSemantics

/-! A common doubled space can be assembled from single-setting constructions.
The original state and first-block inclusion are unchanged; chronology is then
derived from all-matrix intertwining, rather than matched word by word. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

def BinaryKrausRealization.atSetting {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (x : X) : BinaryKrausRealization d Unit where
  initial := r.initial
  density := r.density
  kraus _ a := r.kraus x a
  normalized _ := r.normalized x

def assembleSharpDilation {d : ℕ} {X : Type*}
    (s : X → SharpDilationData d Unit) : SharpDilationData d X where
  projection x := (s x).projection ()
  channelKraus x a := (s x).channelKraus () a

theorem assembleSharpDilation_isSharpDilation {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (s : X → SharpDilationData d Unit)
    (hs : ∀ x, IsSharpDilation (r.atSetting x) (s x)) :
    IsSharpDilation r (assembleSharpDilation s) := by
  apply isSharpDilation_of_algebraic_construction
  · intro x
    exact (hs x).1 ()
  · intro x a
    exact (hs x).2.1 () a
  · intro x
    rcases hs x with ⟨_, _, _, _, hc, _, _, _, _⟩
    exact hc ()
  · intro x a Y
    rcases hs x with ⟨_, _, _, _, _, _, hi, _, _⟩
    exact hi () a Y
  · intro x a Z
    rcases hs x with ⟨_, _, _, _, _, _, _, hr, _⟩
    exact hr () a Z

theorem assembleSharpDilation_repeatable {d : ℕ} {X : Type*}
    (s : X → SharpDilationData d Unit)
    (hs : ∀ x, IsRepeatableSharpDilation (s x)) :
    IsRepeatableSharpDilation (assembleSharpDilation s) := by
  intro x a Z hZ
  exact hs x () a Z hZ

theorem assembleSharpDilation_real {d : ℕ} {X : Type*}
    (s : X → SharpDilationData d Unit) (hs : ∀ x, IsRealSharpDilation (s x)) :
    IsRealSharpDilation (assembleSharpDilation s) := by
  exact ⟨fun x => (hs x).1 (), fun x a K hK => (hs x).2 () a K hK⟩

#print axioms assembleSharpDilation_isSharpDilation
end AlbertSequential

