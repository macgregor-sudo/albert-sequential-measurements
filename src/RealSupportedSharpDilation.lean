/- SPDX-License-Identifier: Apache-2.0 -/
module
public import RealSharpDilation

/-! One chosen dilation satisfies basic simulation, conditional repeatability
and real-data preservation. Zero/unit effects and arbitrary setting families
are retained exactly. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ComplexOrder
namespace AlbertSequential
open Matrix

theorem exists_real_supported_sharpDilation_oneSetting {d : ℕ}
    (r : BinaryKrausRealization d Unit) (hr : IsRealKrausRealization r) :
    ∃ s : SharpDilationData d Unit, IsSharpDilation r s ∧
      (HasCertaintySupportedOutputs r → IsRepeatableSharpDilation s) ∧
      IsRealSharpDilation s := by
  classical
  obtain ⟨B0,hB0real,hB0⟩ := exists_real_positiveFactor r.density.1 hr.1
  have htB0 : Matrix.trace (B0*B0ᴴ)=1 := by rw [hB0]; exact r.density.2
  by_cases hy : krausEffect (r.kraus () true)=0
  · have hE : ∀ a, krausEffect (r.kraus () a) = if a=false then 1 else 0 := by
      intro a
      cases a with
      | true => simpa using hy
      | false => rw [r.no_effect,hy,sub_zero]; rfl
    exact ⟨degenerateKrausDilation r false B0,
      degenerateKrausDilation_isSharpDilation r false B0 hE htB0,
      fun _ => degenerateKrausDilation_repeatable r false B0,
      degenerateKrausDilation_real r hr false B0 hB0real⟩
  by_cases hn : krausEffect (r.kraus () false)=0
  · have hyes : krausEffect (r.kraus () true)=1 := by simpa [hn] using r.normalized ()
    have hE : ∀ a, krausEffect (r.kraus () a) = if a=true then 1 else 0 := by
      intro a
      cases a with
      | true => simpa using hyes
      | false => simpa using hn
    exact ⟨degenerateKrausDilation r true B0,
      degenerateKrausDilation_isSharpDilation r true B0 hE htB0,
      fun _ => degenerateKrausDilation_repeatable r true B0,
      degenerateKrausDilation_real r hr true B0 hB0real⟩
  have hne (a : Bool) : krausEffect (r.kraus () a)≠0 := by
    cases a
    · exact hn
    · exact hy
  have hd (a : Bool) := normalizedKrausOutput_density (r.kraus () a) (hne a)
  have hdreal (a : Bool) := normalizedKrausOutput_real (r.kraus () a) (hr.2 () a)
  let B : Bool → ComplexMatrix d := fun a =>
    Classical.choose (exists_real_positiveFactor (hd a).1 (hdreal a))
  have hBreal (a : Bool) : HasRealEntries (B a) :=
    (Classical.choose_spec (exists_real_positiveFactor (hd a).1 (hdreal a))).1
  have hB (a : Bool) : B a * (B a)ᴴ=normalizedKrausOutput (r.kraus () a) :=
    (Classical.choose_spec (exists_real_positiveFactor (hd a).1 (hdreal a))).2
  have hA := krausEffect_positive (r.kraus () true)
  have hAc : (1-krausEffect (r.kraus () true)).PosSemidef := by
    rw [←r.no_effect ()]
    exact krausEffect_positive _
  have hAr := krausEffect_hasRealEntries (r.kraus () true) (hr.2 () true)
  let s0 := realBinarySpectralSupport hA hAc hAr
  have hs0 := realBinarySpectralSupport_real hA hAc hAr
  have hBC : Matrix.trace (embedFirstBlock B0*(embedFirstBlock B0)ᴴ)=1 := by
    rw [embedFirstBlock_conjTranspose,embedFirstBlock_mul,trace_embedFirstBlock,htB0]
  let s := binaryKrausDilation r (fun _ => s0)
    (fun _ a => B a) (fun _ _ => embedFirstBlock B0)
  refine ⟨s,binaryKrausDilation_isSharpDilation r _ _ _ ?_ (fun _ _ => hBC),?_,?_⟩
  · intro x a
    rw [hB a]
    exact (hd a).2
  · intro hs
    apply binaryKrausDilation_repeatable_of_supported_resets r _ _ _ hs
    intro x a
    cases x
    rw [hB a]
    exact normalizedKrausOutput_supported _ _ (r.outcome_supported hs () a)
  · exact binaryKrausDilation_real r hr _ _ _ (fun _ => hs0)
      (fun _ a => hBreal a) (fun _ _ => embedFirstBlock_real B0 hB0real)

theorem exists_real_supported_sharpDilation {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (hr : IsRealKrausRealization r) :
    ∃ s : SharpDilationData d X, IsSharpDilation r s ∧
      (HasCertaintySupportedOutputs r → IsRepeatableSharpDilation s) ∧
      IsRealSharpDilation s := by
  classical
  have hrx (x : X) : IsRealKrausRealization (r.atSetting x) :=
    ⟨hr.1,fun _ a W hW => hr.2 x a W hW⟩
  let s : X → SharpDilationData d Unit := fun x =>
    Classical.choose (exists_real_supported_sharpDilation_oneSetting (r.atSetting x) (hrx x))
  have hs (x : X) : IsSharpDilation (r.atSetting x) (s x) ∧
      (HasCertaintySupportedOutputs (r.atSetting x) → IsRepeatableSharpDilation (s x)) ∧
      IsRealSharpDilation (s x) :=
    Classical.choose_spec (exists_real_supported_sharpDilation_oneSetting (r.atSetting x) (hrx x))
  refine ⟨assembleSharpDilation s,
    assembleSharpDilation_isSharpDilation r s (fun x => (hs x).1),?_,
    assembleSharpDilation_real s (fun x => (hs x).2.2)⟩
  intro hsupport
  apply assembleSharpDilation_repeatable
  intro x
  apply (hs x).2.1
  intro u Y hY
  exact hsupport x Y hY

/-- All three clauses concern this ONE chosen dilation. No nonzero-effect or
finite-setting assumption is used to select it. -/
theorem exists_same_choice_sharpDilation {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) :
    ∃ s : SharpDilationData d X, IsSharpDilation r s ∧
      (HasCertaintySupportedOutputs r → IsRepeatableSharpDilation s) ∧
      (IsRealKrausRealization r → IsRealSharpDilation s) := by
  classical
  by_cases hr : IsRealKrausRealization r
  · obtain ⟨s,hbasic,hsupported,hreal⟩ := exists_real_supported_sharpDilation r hr
    exact ⟨s,hbasic,hsupported,fun _ => hreal⟩
  · obtain ⟨s,hbasic,hsupported⟩ := exists_supported_sharpDilation r
    exact ⟨s,hbasic,hsupported,fun h => False.elim (hr h)⟩

theorem finiteSharpDilationObligations (d : ℕ) (X : Type*) : SharpDilationObligations d X where
  inclusion_isometry := firstBlockInclusion_isometry d
  existence := exists_same_choice_sharpDilation

end AlbertSequential
