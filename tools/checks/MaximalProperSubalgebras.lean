module

import MaximalProperSubalgebras

open AlbertSequential

def IsAmbientAtomLine (k : CDLevel) (B : NativeJordanSubalgebra) : Prop :=
  ∃ (q : Albert) (hq : IsAtom q), q ∈ (H3Subalgebra k).carrier ∧
    B = relativeLine (H3Subalgebra k) q hq

example (B : NativeJordanSubalgebra) (hle : B.carrier ≤ (H3Subalgebra .R).carrier) :
    IsMaximalProperNative (H3Subalgebra .R) B ↔ IsAmbientAtomLine .R B := by
  have h := maximalProperNative_iff .R B hle
  have hc : ¬ IsPrecedingRankThreeCopy .R B := fun h => h.1 rfl
  exact h.trans (or_iff_left hc)

example (B : NativeJordanSubalgebra) (hle : B.carrier ≤ (H3Subalgebra .C).carrier) :
    IsMaximalProperNative (H3Subalgebra .C) B ↔
      IsAmbientAtomLine .C B ∨ Nonempty (JordanSubalgebraIso (H3Subalgebra .R) B) := by
  have h := maximalProperNative_iff .C B hle
  refine h.trans (or_congr Iff.rfl ?_)
  exact ⟨fun h => h.2, fun h => ⟨by decide,h⟩⟩

example (B : NativeJordanSubalgebra) (hle : B.carrier ≤ (H3Subalgebra .H).carrier) :
    IsMaximalProperNative (H3Subalgebra .H) B ↔
      IsAmbientAtomLine .H B ∨ Nonempty (JordanSubalgebraIso (H3Subalgebra .C) B) := by
  have h := maximalProperNative_iff .H B hle
  refine h.trans (or_congr Iff.rfl ?_)
  exact ⟨fun h => h.2, fun h => ⟨by decide,h⟩⟩

example (B : NativeJordanSubalgebra) :
    IsMaximalProperNative (H3Subalgebra .O) B ↔
      IsAmbientAtomLine .O B ∨ Nonempty (JordanSubalgebraIso (H3Subalgebra .H) B) := by
  have h := maximalProperNative_iff .O B (by rw [H3Subalgebra_O_eq_top]; exact fun _ _ => trivial)
  refine h.trans (or_congr Iff.rfl ?_)
  exact ⟨fun h => h.2, fun h => ⟨by decide,h⟩⟩

example (k : CDLevel) (q : Albert) (hq : IsAtom q) (h : q ∈ (H3Subalgebra k).carrier) :
    (relativeLine (H3Subalgebra k) q hq).carrier =
      Submodule.span ℝ {q} ⊔ relativePeirceZero (H3Subalgebra k) q ∧
    Disjoint (Submodule.span ℝ {q}) (relativePeirceZero (H3Subalgebra k) q) :=
  relativeLine_directSum _ hq h

#print axioms relativeLine_directSum
example (k : CDLevel) (q : Albert) (hq : IsAtom q) (h : q ∈ (H3Subalgebra k).carrier) :
    Nonempty (JordanSubalgebraIso (relativeLine (H3Subalgebra k) q hq)
      (relativeLine (H3Subalgebra k) (diagAtom 0) (diagAtom_isAtom 0))) :=
  relativeLine_standardIso k hq h

#print axioms relativeLine_standardIso
#print axioms relativeLine_finrank
#print axioms maximalProperNative_iff
