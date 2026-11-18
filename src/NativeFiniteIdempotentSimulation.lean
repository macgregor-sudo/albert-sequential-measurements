/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeTestReduction
public import NativeSupportedInstrumentSimulation

/-! Every finite native idempotent menu admits one real supported stationary
finite CP model. Trivial settings and duplicates keep the original n indices. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem exists_nativeIdempotent_instrument_17n_add_one {n : ℕ} (q : Fin n → Albert)
    (hq : ∀ i, jordanMul (q i) (q i) = q i) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : BinaryKrausRealization (17*n+1) (Fin n), IsRealKrausRealization r ∧
      HasCertaintySupportedOutputs r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability q ρ w := by
  obtain ⟨p,hp,m,hm⟩ := exists_atom_menu_reduction q hq
  obtain ⟨r,hr,hsup,hwords⟩ := nativeSupportedSimulationObligations.general n p hp ρ hρ
  refine ⟨BinaryTestReduction.model r m, BinaryTestReduction.model_real r m hr,
    BinaryTestReduction.model_supported r m hsup, ?_⟩
  intro w
  rw [hm]
  exact BinaryTestReduction.matches_native r p m ρ hwords w

theorem exists_nativeIdempotent_mixed_instrument_17n {n : ℕ} (hn : 0 < n)
    (q : Fin n → Albert) (hq : ∀ i, jordanMul (q i) (q i) = q i) :
    ∃ r : BinaryKrausRealization (17*n) (Fin n), IsRealKrausRealization r ∧
      HasCertaintySupportedOutputs r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability q ((1/3 : ℝ) • albertUnit) w := by
  obtain ⟨p,hp,m,hm⟩ := exists_atom_menu_reduction q hq
  obtain ⟨r,hr,hsup,hwords⟩ := exists_nativeMixed_supported_instrument_17n hn p hp
  refine ⟨BinaryTestReduction.model r m, BinaryTestReduction.model_real r m hr,
    BinaryTestReduction.model_supported r m hsup, ?_⟩
  intro w
  rw [hm]
  exact BinaryTestReduction.matches_native r p m _ hwords w

theorem exists_nativeFourIdempotent_mixed_instrument_68 (q : Fin 4 → Albert)
    (hq : ∀ i, jordanMul (q i) (q i) = q i) :
    ∃ r : BinaryKrausRealization 68 (Fin 4), IsRealKrausRealization r ∧
      HasCertaintySupportedOutputs r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability q ((1/3 : ℝ) • albertUnit) w :=
  exists_nativeIdempotent_mixed_instrument_17n (by decide) q hq

end AlbertSequential.NativeAnalysis
