/- SPDX-License-Identifier: Apache-2.0 -/
module
public import RealKrausBridge
public import SupportedSharpDilation

/-! Realness of the SAME literal doubled-space construction and degenerate
retraction channels. No new dilation algorithm or alternate matrix model. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
open Matrix

theorem firstBlockInclusion_real (d : ℕ) :
    ∀ i j, (firstBlockInclusion d i j).im=0 := by
  intro i j
  unfold firstBlockInclusion
  split <;> rfl

theorem embedFirstBlock_real {d : ℕ} (A : ComplexMatrix d) (hA : HasRealEntries A) :
    HasRealEntries (embedFirstBlock A) :=
  realEntries_mul _ _ (realEntries_mul _ _ (firstBlockInclusion_real d) hA)
    (realEntries_conjTranspose _ (firstBlockInclusion_real d))

theorem finiteBinaryYesIsometry_real {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (hy : HasRealEntries s.yes.root)
    (hn : HasRealEntries s.no.root) : ∀ i j, (finiteBinaryYesIsometry s i j).im=0 := by
  have h : ∀ i j, (binaryYesIsometry s i j).im=0 := by
    intro i j
    cases i with
    | inl i => exact hy i j
    | inr i => exact hn i j
  intro i j
  exact h _ _

theorem finiteBinaryNoIsometry_real {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (hy : HasRealEntries s.yes.root)
    (hn : HasRealEntries s.no.root) : ∀ i j, (finiteBinaryNoIsometry s i j).im=0 := by
  have h : ∀ i j, (binaryNoIsometry s i j).im=0 := by
    intro i j
    cases i with
    | inl i => exact hn i j
    | inr i => change (-s.yes.root i j).im=0; rw [Complex.neg_im, hy, neg_zero]
  intro i j
  exact h _ _

theorem finiteBinaryProjection_real {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (hy : HasRealEntries s.yes.root)
    (hn : HasRealEntries s.no.root) : HasRealEntries (finiteBinaryProjection s) :=
  realEntries_mul _ _ (finiteBinaryYesIsometry_real s hy hn)
    (realEntries_conjTranspose _ (finiteBinaryYesIsometry_real s hy hn))

theorem binaryOutcomeIsometry_real {d : ℕ} {A : ComplexMatrix d}
    (s : BinarySpectralSupport A) (hy : HasRealEntries s.yes.root)
    (hn : HasRealEntries s.no.root) (a : Bool) :
    ∀ i j, (binaryOutcomeIsometry s a i j).im=0 := by
  cases a with
  | false => exact finiteBinaryNoIsometry_real s hy hn
  | true => exact finiteBinaryYesIsometry_real s hy hn

theorem FiniteSpectralSupport.retarget_inverseRoot {d : ℕ} {A B : ComplexMatrix d}
    (s : FiniteSpectralSupport A) (h : A=B) : (s.retarget h).inverseRoot=s.inverseRoot := by
  cases h
  rfl

theorem FiniteSpectralSupport.retarget_support {d : ℕ} {A B : ComplexMatrix d}
    (s : FiniteSpectralSupport A) (h : A=B) : (s.retarget h).support=s.support := by
  cases h
  rfl

theorem binaryKrausDilation_real {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (hr : IsRealKrausRealization r)
    (s : ∀ x, BinarySpectralSupport (krausEffect (r.kraus x true)))
    (B : X → Bool → ComplexMatrix d) (C : X → Bool → ComplexMatrix (d+d))
    (hs : ∀ x, HasRealEntries (s x).yes.root ∧ HasRealEntries (s x).no.root ∧
      HasRealEntries (s x).yes.inverseRoot ∧ HasRealEntries (s x).no.inverseRoot ∧
      HasRealEntries (s x).yes.support ∧ HasRealEntries (s x).no.support)
    (hB : ∀ x a, HasRealEntries (B x a)) (hC : ∀ x a, HasRealEntries (C x a)) :
    IsRealSharpDilation (binaryKrausDilation r s B C) := by
  constructor
  · intro x
    exact finiteBinaryProjection_real _ (hs x).1 (hs x).2.1
  · intro x a W hW
    rcases hs x with ⟨hy,hn,hiy,hin,hpy,hpn⟩
    have hR : HasRealEntries (binaryOutcomeSupport r x (s x) a).inverseRoot := by
      cases a with
      | true => exact hiy
      | false => simpa only [binaryOutcomeSupport, FiniteSpectralSupport.retarget_inverseRoot] using hin
    have hP : HasRealEntries (binaryOutcomeSupport r x (s x) a).support := by
      cases a with
      | true => exact hpy
      | false => simpa only [binaryOutcomeSupport, FiniteSpectralSupport.retarget_support] using hpn
    exact isometricCompletion_list_hasRealEntries _ _ _ _
      (completedKraus_hasRealEntries _ _ _ (hr.2 x a) hR hP (hB x a))
      (firstBlockInclusion_real d) (binaryOutcomeIsometry_real _ hy hn a) (hC x a) W hW

theorem firstCornerChannelKraus_real {d : ℕ} (K : List (ComplexMatrix d))
    (B : ComplexMatrix d) (hK : ∀ W ∈ K, HasRealEntries W) (hB : HasRealEntries B) :
    ∀ W ∈ firstCornerChannelKraus K B, HasRealEntries W :=
  isometricCompletion_list_hasRealEntries K _ _ _ hK (firstBlockInclusion_real d)
    (firstBlockInclusion_real d) (embedFirstBlock_real B hB)

theorem degenerateKrausDilation_real {d : ℕ} (r : BinaryKrausRealization d Unit)
    (hr : IsRealKrausRealization r) (b : Bool) (B : ComplexMatrix d)
    (hB : HasRealEntries B) : IsRealSharpDilation (degenerateKrausDilation r b B) := by
  constructor
  · intro x
    cases b with
    | false => exact fun _ _ => rfl
    | true => exact hasRealEntries_one _
  · intro x a W hW
    exact firstCornerChannelKraus_real _ B (hr.2 () b) hB W hW

theorem normalizedKrausOutput_real {d : ℕ} (K : List (ComplexMatrix d))
    (hK : ∀ W ∈ K, HasRealEntries W) : HasRealEntries (normalizedKrausOutput K) :=
  real_smul_hasRealEntries _ _ (krausAction_hasRealEntries K 1 hK (hasRealEntries_one d))

end AlbertSequential
