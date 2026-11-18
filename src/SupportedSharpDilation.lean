/- SPDX-License-Identifier: Apache-2.0 -/
module
public import DegenerateSharpDilation

/-! Basic and repeatable existence with all zero/unit cases retained.
The real-data clause is treated separately, with a real factor selector
and real spectral bundle (`RealSupportedSharpDilation`). -/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential
open Matrix

theorem exists_supported_sharpDilation_oneSetting {d : ℕ}
    (r : BinaryKrausRealization d Unit) :
    ∃ s : SharpDilationData d Unit,
      IsSharpDilation r s ∧
      (HasCertaintySupportedOutputs r → IsRepeatableSharpDilation s) := by
  classical
  obtain ⟨B0,hB0⟩ := exists_complexPositiveFactor r.density.1
  have htB0 : Matrix.trace (B0*B0ᴴ) = 1 := hB0 ▸ r.density.2
  by_cases hy : krausEffect (r.kraus () true) = 0
  · have hE : ∀ a, krausEffect (r.kraus () a) = if a=false then 1 else 0 := by
      intro a
      cases a with
      | true => simpa using hy
      | false => rw [r.no_effect, hy, sub_zero]; rfl
    exact ⟨degenerateKrausDilation r false B0,
      degenerateKrausDilation_isSharpDilation r false B0 hE htB0,
      fun _ => degenerateKrausDilation_repeatable r false B0⟩
  by_cases hn : krausEffect (r.kraus () false) = 0
  · have hyes : krausEffect (r.kraus () true) = 1 := by
      simpa [hn] using r.normalized ()
    have hE : ∀ a, krausEffect (r.kraus () a) = if a=true then 1 else 0 := by
      intro a
      cases a with
      | true => simpa using hyes
      | false => simpa using hn
    exact ⟨degenerateKrausDilation r true B0,
      degenerateKrausDilation_isSharpDilation r true B0 hE htB0,
      fun _ => degenerateKrausDilation_repeatable r true B0⟩
  have hne (a : Bool) : krausEffect (r.kraus () a) ≠ 0 := by
    cases a
    · exact hn
    · exact hy
  have hd (a : Bool) := normalizedKrausOutput_density (r.kraus () a) (hne a)
  let B : Bool → ComplexMatrix d := fun a =>
    Classical.choose (exists_complexPositiveFactor (hd a).1)
  have hB (a : Bool) : B a * (B a)ᴴ = normalizedKrausOutput (r.kraus () a) :=
    (Classical.choose_spec (exists_complexPositiveFactor (hd a).1)).symm
  have hBC : Matrix.trace (embedFirstBlock B0 * (embedFirstBlock B0)ᴴ) = 1 := by
    rw [embedFirstBlock_conjTranspose, embedFirstBlock_mul, trace_embedFirstBlock, htB0]
  let s := binaryKrausDilation r (realizationBinarySupport r)
    (fun _ a => B a) (fun _ _ => embedFirstBlock B0)
  refine ⟨s, binaryKrausDilation_isSharpDilation r _ _ _ ?_ (fun _ _ => hBC), ?_⟩
  · intro x a
    exact hB a ▸ (hd a).2
  · intro hs
    apply binaryKrausDilation_repeatable_of_supported_resets r _ _ _ hs
    intro x a
    cases x
    rw [hB a]
    exact normalizedKrausOutput_supported _ _ (r.outcome_supported hs () a)

/-- A SINGLE chosen dilation is basic and, whenever the input has
certainty-supported outputs, repeatable on every positive enlarged input.
The real-data implication is not part of this statement; see `RealSupportedSharpDilation`. -/
theorem exists_supported_sharpDilation {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) :
    ∃ s : SharpDilationData d X, IsSharpDilation r s ∧
      (HasCertaintySupportedOutputs r → IsRepeatableSharpDilation s) := by
  classical
  let s : X → SharpDilationData d Unit := fun x =>
    Classical.choose (exists_supported_sharpDilation_oneSetting (r.atSetting x))
  have hs (x : X) : IsSharpDilation (r.atSetting x) (s x) ∧
      (HasCertaintySupportedOutputs (r.atSetting x) → IsRepeatableSharpDilation (s x)) :=
    Classical.choose_spec (exists_supported_sharpDilation_oneSetting (r.atSetting x))
  refine ⟨assembleSharpDilation s,
    assembleSharpDilation_isSharpDilation r s (fun x => (hs x).1), ?_⟩
  intro hr
  apply assembleSharpDilation_repeatable
  intro x
  apply (hs x).2
  intro u Y hY
  exact hr x Y hY

#print axioms exists_supported_sharpDilation_oneSetting
#print axioms exists_supported_sharpDilation
end AlbertSequential

