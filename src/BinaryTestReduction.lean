/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WordReduction
public import Interfaces.OperationalBoundaries

/-! Fixed outcome relabeling and deterministic binary settings. These modes
preserve the original setting index, so no memory or menu index is added. -/
@[expose] public section
namespace AlbertSequential

inductive BinaryTestReduction where
  | direct
  | complement
  | deterministic (outcome : Bool)

def BinaryTestReduction.outcomeStep {X : Type*} (m : X → BinaryTestReduction)
    (a : Outcome X) : WordReduction.Step (Outcome X) :=
  match m a.1 with
  | .direct => .letter a
  | .complement => .letter (a.1, !a.2)
  | .deterministic c => if a.2 = c then .skip else .impossible

def BinaryTestReduction.kraus {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (m : X → BinaryTestReduction) (x : X) (b : Bool) : List (ComplexMatrix d) :=
  match m x with
  | .direct => r.kraus x b
  | .complement => r.kraus x (!b)
  | .deterministic c => if b = c then [1] else []

end AlbertSequential
