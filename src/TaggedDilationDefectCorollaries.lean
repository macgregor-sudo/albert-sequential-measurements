/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TaggedDilationDefect
public import OptimalSharpDilation

@[expose] public section

noncomputable section

namespace AlbertSequential.NativeAnalysis

private theorem exists_nativeSharp_of_defect_bound {n d m : ℕ}
    (p : Fin n → Albert) (ρ : Albert)
    (r : BinaryKrausRealization d (Fin n)) (hreal : IsRealKrausRealization r)
    (hsupport : HasCertaintySupportedOutputs r)
    (hrank : ∀ j, let A := krausEffect (r.kraus j true); (A - A * A).rank ≤ m)
    (hwords : ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w) :
    ∃ s : ReducedSharpDilationData d (d+m) (Fin n), IsReducedSharpDilation r s ∧
      HasRealEntries (sharpFrameEmbed s.inclusion r.initial) ∧
      IsRealReducedSharpDilation s ∧ IsRepeatableReducedSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w := by
  obtain ⟨s,hJ,hsharp,hrepeat,hsreal⟩ := exists_sharpDilation_of_defect_bound r
    (fun j => by simpa only [pow_two] using hrank j)
  have hJn : ∀ i j, (s.inclusion i j).im = 0 := hJ ▸ optimalCornerInclusion_real d m
  refine ⟨s, hsharp, ?_, hsreal hreal, hrepeat hsupport, fun w =>
    (hsharp.word_probability w).trans (hwords w)⟩
  exact realEntries_mul _ _ (realEntries_mul _ _ hJn hreal.1)
    (realEntries_conjTranspose _ hJn)

/-- Real sharp projections and channels with certainty-supported outputs in the
dimension of companion Corollary 6.5. -/
theorem exists_nativeSharp_instrument_26n_sub_seven {n : ℕ} (hn : 0 < n)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : BinaryKrausRealization (17*n+1) (Fin n),
    ∃ s : ReducedSharpDilationData (17*n+1) (26*n-7) (Fin n),
      IsReducedSharpDilation r s ∧ HasRealEntries (sharpFrameEmbed s.inclusion r.initial) ∧
      IsRealReducedSharpDilation s ∧ IsRepeatableReducedSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w := by
  obtain ⟨r,hreal,hsupport,hrank,hwords⟩ := exists_nativeGeneral_supported_defect_17n_add_one hn p hp ρ hρ
  have hd : 17*n+1+(9*n-8) = 26*n-7 := by omega
  rw [← hd]
  exact ⟨r, exists_nativeSharp_of_defect_bound p ρ r hreal hsupport hrank hwords⟩

/-- Companion Corollary 6.6 with the actual no-Peirce-half condition. -/
theorem exists_nativeNoHalf_sharp_instrument_26n_sub_nine {n : ℕ} (hn : 0 < n)
    (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) (hρ : IsDensity ρ)
    (hno : ∃ (i : Fin n) (t : ℝ) (y : Albert), 0 ≤ t ∧ IsPositive y ∧
      jordanMul (p i) y = 0 ∧ ρ = t • p i + y) :
    ∃ r : BinaryKrausRealization (17*n) (Fin n),
    ∃ s : ReducedSharpDilationData (17*n) (26*n-9) (Fin n),
      IsReducedSharpDilation r s ∧ HasRealEntries (sharpFrameEmbed s.inclusion r.initial) ∧
      IsRealReducedSharpDilation s ∧ IsRepeatableReducedSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w := by
  obtain ⟨r,hreal,hsupport,hrank,hwords⟩ := exists_nativeNoHalf_supported_defect_17n p hp ρ hρ hno
  have hd : 17*n+9*(n-1) = 26*n-9 := by omega
  rw [← hd]
  exact ⟨r, exists_nativeSharp_of_defect_bound p ρ r hreal hsupport hrank hwords⟩

theorem exists_nativeFour_sharp_instrument_97 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (ρ : Albert) (hρ : IsDensity ρ) :
    ∃ r : BinaryKrausRealization 69 (Fin 4), ∃ s : ReducedSharpDilationData 69 97 (Fin 4),
      IsReducedSharpDilation r s ∧ HasRealEntries (sharpFrameEmbed s.inclusion r.initial) ∧
      IsRealReducedSharpDilation s ∧ IsRepeatableReducedSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ρ w :=
  exists_nativeSharp_instrument_26n_sub_seven (by decide) p hp ρ hρ

theorem exists_nativeFour_mixed_sharp_instrument_95 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ∃ r : BinaryKrausRealization 68 (Fin 4), ∃ s : ReducedSharpDilationData 68 95 (Fin 4),
      IsReducedSharpDilation r s ∧ HasRealEntries (sharpFrameEmbed s.inclusion r.initial) ∧
      IsRealReducedSharpDilation s ∧ IsRepeatableReducedSharpDilation s ∧
      ∀ w, s.wordProbability r.initial w = nativeWordProbability p ((1/3 : ℝ) • albertUnit) w := by
  apply exists_nativeNoHalf_sharp_instrument_26n_sub_nine (by decide) p hp _ nativeMixedDensity
  refine ⟨0, 1/3, (1/3 : ℝ) • (albertUnit - p 0), by norm_num,
    isPositive_smul _ _ (by norm_num) (isPositive_idempotent _ (complementary_idempotent _ (hp 0).1)), ?_, ?_⟩
  · rw [jordanMul_smul_right, jordanMul_sub_right, jordanMul_albertUnit_right, (hp 0).1,
      sub_self, smul_zero]
  · module

end AlbertSequential.NativeAnalysis
