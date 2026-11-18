/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeFiniteInstrumentSimulation
public import NativeTaggedCertaintySupport
public import FiniteKrausSupportTransport

/-! The same real finite-menu simulators can be chosen with certainty-supported
outputs. This is the construction-level premise for a separate sharp dilation. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem exists_nativeGeneral_supported_real_simulation {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : RealFiniteKrausModel
      (Sigma (fun s : Option (Fin n) ⊕ Fin n => nativeTaggedBlock s)) (Fin n),
      HasKrausCertaintySupport r.kraus ∧
      ∀ w, realFiniteKrausProbability _ _ r w = nativeWordProbability p ρ w := by
  let z := nativeGeneralScalarStates p ρ
  let hz := nativeGeneralScalarStates_density p hp ρ hρ
  let xs : Option (Fin n) ⊕ Fin n → Albert := Pi.single (.inl none) ρ
  have hxs : ∀ s, IsPositive (xs s) := native_positive_single _ ρ hρ.1
  have hd : taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs = ρ :=
    nativeGeneralPieces_decoding p ρ hρ
  have ht : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p z) xs) = 1 := by rw [hd, hρ.2]
  refine ⟨nativeTaggedRealModel p hp z hz Option.some xs hxs ht,
    nativeTaggedRealModel_certainty p hp z hz Option.some (fun _ => rfl) xs hxs ht, ?_⟩
  intro w
  rw [nativeTaggedRealModel_probability p hp z hz Option.some (fun _ => rfl) xs hxs ht, hd]

theorem exists_nativeNoHalf_supported_real_simulation {n : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) (y : Albert) (hy : IsPositive y)
    (hpy : jordanMul (p i) y = 0) (hdecomp : ρ = t • p i + y) :
    ∃ r : RealFiniteKrausModel
      (Sigma (fun s : Fin n ⊕ Fin n => nativeTaggedBlock s)) (Fin n),
      HasKrausCertaintySupport r.kraus ∧
      ∀ w, realFiniteKrausProbability _ _ r w = nativeWordProbability p ρ w := by
  let hz := fun j => native_atom_density (p j) (hp j)
  let xs := nativeNoHalfPieces p i t y
  have hxs : ∀ s, IsPositive (xs s) := nativeNoHalfPieces_positive p hp i t ht y hy
  have hd : taggedLinearDecoding (nativeTaggedPieceDecoder p p) xs = ρ :=
    (nativeNoHalfPieces_decoding p hp i t y hpy).trans hdecomp.symm
  have ht' : albertTrace (taggedLinearDecoding (nativeTaggedPieceDecoder p p) xs) = 1 := by rw [hd, hρ.2]
  refine ⟨nativeTaggedRealModel p hp p hz id xs hxs ht',
    nativeTaggedRealModel_certainty p hp p hz id (fun _ => rfl) xs hxs ht', ?_⟩
  intro w
  rw [nativeTaggedRealModel_probability p hp p hz id (fun _ => rfl) xs hxs ht', hd]

theorem nativeSupportedSimulationObligations : NativeSupportedSimulationObligations where
  general n p hp ρ hρ := by
    obtain ⟨r, hr, hw⟩ := exists_nativeGeneral_supported_real_simulation p hp ρ hρ
    have hd : Fintype.card (Sigma (fun s : Option (Fin n) ⊕ Fin n => nativeTaggedBlock s)) =
        17 * n + 1 := by
      rw [nativeTaggedBlock_card]
      simp only [Fintype.card_option, Fintype.card_fin]
      omega
    obtain ⟨s, hs, hsup, hprob⟩ := exists_supported_complexFiniteKrausModel_of_card hd r hr
    exact ⟨s, hs, hsup, fun w => (hprob w).trans (hw w)⟩
  no_half_component n p hp ρ hρ hno := by
    obtain ⟨i,t,y,ht,hy,hpy,hdecomp⟩ := hno
    obtain ⟨r, hr, hw⟩ := exists_nativeNoHalf_supported_real_simulation p hp ρ hρ i t ht y hy hpy hdecomp
    have hd : Fintype.card (Sigma (fun s : Fin n ⊕ Fin n => nativeTaggedBlock s)) = 17 * n := by
      rw [nativeTaggedBlock_card, Fintype.card_fin]
      omega
    obtain ⟨s, hs, hsup, hprob⟩ := exists_supported_complexFiniteKrausModel_of_card hd r hr
    exact ⟨s, hs, hsup, fun w => (hprob w).trans (hw w)⟩

theorem exists_nativeMixed_supported_instrument_17n {n : ℕ} (hn : 0 < n)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization (17 * n) (Fin n), IsRealKrausRealization r ∧
      HasCertaintySupportedOutputs r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ((1/3 : ℝ) • albertUnit) w := by
  let i : Fin n := ⟨0,hn⟩
  apply nativeSupportedSimulationObligations.no_half_component n p hp _ nativeMixedDensity
  refine ⟨i, 1/3, (1/3 : ℝ) • (albertUnit - p i), by norm_num,
    isPositive_smul _ _ (by norm_num) (isPositive_idempotent _ (complementary_idempotent _ (hp i).1)), ?_, ?_⟩
  · rw [jordanMul_smul_right, jordanMul_sub_right, jordanMul_albertUnit_right, (hp i).1,
      sub_self, smul_zero]
  · module

theorem exists_nativeFour_supported_instrument_68 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization 68 (Fin 4), IsRealKrausRealization r ∧ HasCertaintySupportedOutputs r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ((1/3 : ℝ) • albertUnit) w :=
  exists_nativeMixed_supported_instrument_17n (by decide) p hp

end AlbertSequential.NativeAnalysis
