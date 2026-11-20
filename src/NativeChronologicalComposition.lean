/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.SharpDisturbance
public import NativeAutomorphisms
public import NativeHankelRank

@[expose] public section
noncomputable section
namespace AlbertSequential
variable {ι : Type*}

/-- Chronological linear action of a signed word on the original Albert state. -/
def nativeChronologicalMap (p : ι → Albert) (w : Word ι) : Module.End ℝ Albert :=
  SharpDisturbance.wordMap (fun q => NativeAnalysis.quadraticMapLinear (nativeOutcome p q)) w

theorem nativeChronologicalMap_apply (p : ι → Albert) (w : Word ι) (x : Albert) :
    nativeChronologicalMap p w x = nativeBranchState p x w := by
  induction w generalizing x with
  | nil => rfl
  | cons q w ih => exact ih _

theorem nativeChronologicalMap_append (p : ι → Albert) (u v : Word ι) :
    nativeChronologicalMap p (u ++ v) = (nativeChronologicalMap p v).comp (nativeChronologicalMap p u) := by
  ext x
  simp only [LinearMap.comp_apply,nativeChronologicalMap_apply,nativeBranchState,List.foldl_append]

/-- Core Remark 4.2, including the state space dimension and the trace readout. -/
theorem native_chronological_composition (p : ι → Albert) :
    Module.finrank ℝ Albert = 27 ∧
    (∀ (u v w : Word ι), nativeChronologicalMap p (u++v++w) =
      (nativeChronologicalMap p w).comp ((nativeChronologicalMap p v).comp (nativeChronologicalMap p u))) ∧
    ∀ (w : Word ι) (ρ : Albert), nativeWordProbability p ρ w = albertTrace (nativeChronologicalMap p w ρ) :=
  ⟨native_finrank,fun u v w => by rw [nativeChronologicalMap_append,nativeChronologicalMap_append],
    fun w ρ => congrArg albertTrace (nativeChronologicalMap_apply p w ρ).symm⟩

end AlbertSequential
