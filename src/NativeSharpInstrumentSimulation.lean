/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeSupportedInstrumentSimulation
public import RealSupportedSharpDilation

/-! Thin join to the SAME-CHOICE sharp dilation. SharpDilationData d
has ambient dimension d+d: base69 gives138 and base68 gives136. The maps are
sharp projection updates followed by channels, not ideal projective updates. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem exists_nativeSharp_of_supported {n d : ℕ} (p : Fin n → Albert) (ρ : Albert)
    (r : BinaryKrausRealization d (Fin n)) (hreal : IsRealKrausRealization r)
    (hsupport : HasCertaintySupportedOutputs r)
    (hwords : ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w) :
    ∃ s : SharpDilationData d (Fin n), IsSharpDilation r s ∧
      HasRealEntries (embedFirstBlock r.initial) ∧ IsRepeatableSharpDilation s ∧
      IsRealSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w := by
  obtain ⟨s,hbasic,hsup,hrealD⟩ := (finiteSharpDilationObligations d (Fin n)).existence r
  refine ⟨s,hbasic,embedFirstBlock_real r.initial hreal.1,hsup hsupport,hrealD hreal,?_⟩
  intro w
  exact (hbasic.2.2.2.2.2.2.2.2 w).trans (hwords w)

theorem exists_nativeSharp_instrument_2_17n_add_one {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : BinaryKrausRealization (17*n+1) (Fin n),
    ∃ s : SharpDilationData (17*n+1) (Fin n),
      IsRealKrausRealization r ∧ IsSharpDilation r s ∧ HasRealEntries (embedFirstBlock r.initial) ∧
      IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w := by
  obtain ⟨r,hr,hsup,hw⟩ := nativeSupportedSimulationObligations.general n p hp ρ hρ
  obtain ⟨s,hs,hinit,hrep,hsreal,hwords⟩ := exists_nativeSharp_of_supported p ρ r hr hsup hw
  exact ⟨r,s,hr,hs,hinit,hrep,hsreal,hwords⟩

theorem exists_nativeNoHalf_sharp_instrument_34n {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ)
    (hno : ∃ (i : Fin n) (t : ℝ) (y : Albert), 0 ≤ t ∧ IsPositive y ∧
      jordanMul (p i) y = 0 ∧ ρ = t • p i + y) :
    ∃ r : BinaryKrausRealization (17*n) (Fin n),
    ∃ s : SharpDilationData (17*n) (Fin n),
      IsRealKrausRealization r ∧ IsSharpDilation r s ∧ HasRealEntries (embedFirstBlock r.initial) ∧
      IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w := by
  obtain ⟨r,hr,hsup,hw⟩ := nativeSupportedSimulationObligations.no_half_component n p hp ρ hρ hno
  obtain ⟨s,hs,hinit,hrep,hsreal,hwords⟩ := exists_nativeSharp_of_supported p ρ r hr hsup hw
  exact ⟨r,s,hr,hs,hinit,hrep,hsreal,hwords⟩

theorem exists_nativeMixed_sharp_instrument_34n {n : ℕ} (hn : 0 < n)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization (17*n) (Fin n),
    ∃ s : SharpDilationData (17*n) (Fin n),
      IsRealKrausRealization r ∧ IsSharpDilation r s ∧ HasRealEntries (embedFirstBlock r.initial) ∧
      IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ((1/3 : ℝ) • albertUnit) w := by
  obtain ⟨r,hr,hsup,hw⟩ := exists_nativeMixed_supported_instrument_17n hn p hp
  obtain ⟨s,hs,hinit,hrep,hsreal,hwords⟩ :=
    exists_nativeSharp_of_supported p ((1/3 : ℝ) • albertUnit) r hr hsup hw
  exact ⟨r,s,hr,hs,hinit,hrep,hsreal,hwords⟩

/-- Base69, hence the literal projection/channel matrices have ambient138. -/
theorem exists_nativeFour_sharp_instrument_138 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : BinaryKrausRealization 69 (Fin 4), ∃ s : SharpDilationData 69 (Fin 4),
      IsRealKrausRealization r ∧ IsSharpDilation r s ∧ HasRealEntries (embedFirstBlock r.initial) ∧
      IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w :=
  exists_nativeSharp_instrument_2_17n_add_one p hp ρ hρ

/-- Base68, hence the literal projection/channel matrices have ambient136. -/
theorem exists_nativeFour_mixed_sharp_instrument_136 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization 68 (Fin 4), ∃ s : SharpDilationData 68 (Fin 4),
      IsRealKrausRealization r ∧ IsSharpDilation r s ∧ HasRealEntries (embedFirstBlock r.initial) ∧
      IsRepeatableSharpDilation s ∧ IsRealSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ((1/3 : ℝ) • albertUnit) w :=
  exists_nativeMixed_sharp_instrument_34n (by decide) p hp

end AlbertSequential.NativeAnalysis
