/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NativeTaggedInitialModels
public import RealFiniteKrausComplexification

/-! Exact finite-menu real instrument simulation in dimensions17n+1 and17n.
These are stationary all-word constructions for the specified initial density.
Arbitrary quantum instruments are distinct from ideal projective updates. -/
@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem nativeFiniteSimulationObligations : NativeFiniteSimulationObligations where
  general n p hp ρ hρ := by
    obtain ⟨r, hr⟩ := exists_nativeGeneral_real_simulation p hp ρ hρ
    have hd : Fintype.card (Sigma (fun s : Option (Fin n) ⊕ Fin n => nativeTaggedBlock s)) =
        17 * n + 1 := by
      rw [nativeTaggedBlock_card]
      simp only [Fintype.card_option, Fintype.card_fin]
      omega
    obtain ⟨s, hs, hw⟩ := exists_complexFiniteKrausModel_of_card hd r
    exact ⟨s, hs, fun w => (hw w).trans (hr w)⟩
  no_half_component n p hp ρ hρ hno := by
    obtain ⟨i,t,y,ht,hy,hpy,heq⟩ := hno
    obtain ⟨r, hr⟩ := exists_nativeNoHalf_real_simulation p hp ρ hρ i t ht y hy hpy heq
    have hd : Fintype.card (Sigma (fun s : Fin n ⊕ Fin n => nativeTaggedBlock s)) = 17 * n := by
      rw [nativeTaggedBlock_card, Fintype.card_fin]
      omega
    obtain ⟨s, hs, hw⟩ := exists_complexFiniteKrausModel_of_card hd r
    exact ⟨s, hs, fun w => (hw w).trans (hr w)⟩

theorem nativeMixedDensity : IsDensity ((1 / 3 : ℝ) • albertUnit) := by
  constructor
  · exact isPositive_smul _ _ (by norm_num)
      (isPositive_idempotent _ (jordanMul_albertUnit_left albertUnit))
  · rw [albertTrace_smul]
    have he : albertTrace albertUnit = 3 := by simp [albertTrace, albertUnit]
    rw [he]
    norm_num

theorem exists_nativeMixed_instrument_17n {n : ℕ} (hn : 0 < n) (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization (17 * n) (Fin n), IsRealKrausRealization r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w := by
  let i : Fin n := ⟨0,hn⟩
  apply nativeFiniteSimulationObligations.no_half_component n p hp _ nativeMixedDensity
  refine ⟨i, 1/3, (1/3 : ℝ) • (albertUnit - p i), by norm_num,
    isPositive_smul _ _ (by norm_num) (isPositive_idempotent _ (complementary_idempotent _ (hp i).1)), ?_, ?_⟩
  · rw [jordanMul_smul_right, jordanMul_sub_right, jordanMul_albertUnit_right, (hp i).1,
      sub_self, smul_zero]
  · module

theorem exists_nativeFour_instrument_68 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization 68 (Fin 4), IsRealKrausRealization r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w :=
  exists_nativeMixed_instrument_17n (by decide) p hp

end AlbertSequential.NativeAnalysis
