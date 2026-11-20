/- SPDX-License-Identifier: Apache-2.0 -/
module
public import OptimalBinaryFrameChoice
public import ReducedSharpFrameCoordinates
public import ReducedSharpDilationRepeatability

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix

private theorem reindexComplement {o p : Type*} [DecidableEq o] [DecidableEq p]
    (P : Matrix o o ℂ) (e : p ≃ o) :
    (1-P).submatrix e e = 1-P.submatrix e e := by
  change (1 : Matrix o o ℂ).submatrix e e - P.submatrix e e = _
  rw [submatrix_one_equiv]

private theorem transportFrame {i o p : Type*} [Fintype i] [Fintype o] [Fintype p]
    {J : Matrix o i ℂ} {R : Matrix o o ℂ} {S : Matrix i i ℂ}
    (f : SharpDilationChannelFrame J R S) (e : p ≃ o)
    (R' : Matrix p p ℂ) (S' : Matrix i i ℂ)
    (hR : R.submatrix e e = R') (hS : S = S') :
    ∃ t : SharpDilationChannelFrame (J.submatrix e id) R' S',
      t.frame = f.frame.submatrix e id := by
  subst R' S'; exact ⟨f.reindexOutput e,rfl⟩

theorem exists_optimalSharpDilation_of_choices {d m : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (C : (x : X) → OptimalBinaryFrameChoice (m := m) (krausEffect (r.kraus x true))) :
    ∃ M : ReducedSharpDilationData d (d+m) X, M.inclusion = optimalCornerInclusion d m ∧
      IsReducedSharpDilation r M ∧
      (HasCertaintySupportedOutputs r → IsRepeatableReducedSharpDilation M) ∧
      (IsRealKrausRealization r → IsRealReducedSharpDilation M) := by
  classical
  let e := (finSumFinEquiv : Fin d ⊕ Fin m ≃ Fin (d+m)).symm
  let P := fun x => (C x).projection.submatrix e e
  let s := fun x => binaryOutcomeSupport r x (C x).spectral
  have frames (x : X) (a : Bool) :
      ∃ f : SharpDilationChannelFrame (optimalCornerInclusion d m)
          (sharpOutcomeProjection (P x) a) (s x a).root,
        HasRealEntries (krausEffect (r.kraus x true)) → ∀ i j, (f.frame i j).im = 0 := by
    cases a with
    | true =>
      obtain ⟨f,hf⟩ := transportFrame (C x).yesFrame e (P x) (s x true).root rfl rfl
      refine ⟨f,fun hr i j => ?_⟩
      rw [hf]; exact ((C x).real_data hr).2.1 (e i) j
    | false =>
      have hs : (C x).spectral.no.root = (s x false).root := by
        simp only [s, binaryOutcomeSupport, FiniteSpectralSupport.retarget_root]
      obtain ⟨f,hf⟩ := transportFrame (C x).noFrame e (1-P x) _ (reindexComplement _ _) hs
      refine ⟨f,fun hr i j => ?_⟩
      rw [hf]; exact ((C x).real_data hr).2.2.1 (e i) j
  choose f hf using frames
  have hp (x : X) : (P x)ᴴ = P x ∧ P x * P x = P x := by
    simp only [P, conjTranspose_submatrix, submatrix_mul_equiv, (C x).hermitian, (C x).idempotent,
      and_self]
  have hz (x : X) (a : Bool) (h : krausEffect (r.kraus x a) = 0) :
      sharpOutcomeProjection (P x) a = 0 := by
    cases a with
    | true =>
      change (C x).projection.submatrix e e = 0
      rw [(C x).zero_yes h]; rfl
    | false =>
      rw [r.no_effect] at h
      change 1 - (C x).projection.submatrix e e = 0
      rw [← reindexComplement, (C x).zero_no h]; rfl
  obtain ⟨M,hJ,_,hM,hrep,hreal⟩ := exists_reducedSharpDilation_of_frames r
    (optimalCornerInclusion d m) P s f (optimalCornerInclusion_isometry d m) hp hz
    (optimalCornerInclusion_real d m) (by
      intro hr
      have hA := fun x => krausEffect_hasRealEntries _ (hr.2 x true)
      refine ⟨fun x i j => ((C x).real_data (hA x)).1 (e i) (e j),
        fun x a => hf x a (hA x), ?_⟩
      intro x a
      obtain ⟨_,_,_,hy,hn,hsy,hsn⟩ := (C x).real_data (hA x)
      cases a with
      | true => exact ⟨hy,hsy⟩
      | false =>
        simpa only [s, binaryOutcomeSupport, FiniteSpectralSupport.retarget_inverseRoot,
          FiniteSpectralSupport.retarget_support] using And.intro hn hsn)
  exact ⟨M,hJ,hM,hrep,hreal⟩

end AlbertSequential
