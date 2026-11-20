/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OppositeCliffordVolumes
import Mathlib.Tactic.NormNum

public section
noncomputable section

namespace AlbertSequential

/-- Each summand in the opposite-volume example is irreducible over the reals.
The first two generators already suffice. -/
theorem oppositeCliffordSector_irreducible (V : Submodule ℝ (Quaternion ℝ))
    (hI : ∀ u ∈ V, (⟨0,1,0,0⟩ : Quaternion ℝ) * u ∈ V)
    (hJ : ∀ u ∈ V, (⟨0,0,1,0⟩ : Quaternion ℝ) * u ∈ V) :
    V = ⊥ ∨ V = ⊤ := by
  by_cases hV : V = ⊥
  · exact Or.inl hV
  · right
    obtain ⟨u, hu, hune⟩ := V.ne_bot_iff.mp hV
    apply Submodule.eq_top_iff'.mpr
    intro v
    let I : Quaternion ℝ := ⟨0,1,0,0⟩
    let J : Quaternion ℝ := ⟨0,0,1,0⟩
    let K : Quaternion ℝ := ⟨0,0,0,1⟩
    have hK : I * J = K := by
      apply Quaternion.ext <;>
        norm_num [I, J, K, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    have huI : I * u ∈ V := hI u hu
    have huJ : J * u ∈ V := hJ u hu
    have huK : K * u ∈ V := by rw [← hK, mul_assoc]; exact hI _ huJ
    have hmul (w : Quaternion ℝ) : w * u ∈ V := by
      have hw : w = w.re • (1 : Quaternion ℝ) + w.imI • I + w.imJ • J + w.imK • K := by
        apply Quaternion.ext <;> simp [I,J,K]
      have hw' := congrArg (fun a : Quaternion ℝ => a * u) hw
      rw [hw', add_mul, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
        smul_mul_assoc, smul_mul_assoc, one_mul]
      exact V.add_mem (V.add_mem (V.add_mem (V.smul_mem _ hu) (V.smul_mem _ huI))
        (V.smul_mem _ huJ)) (V.smul_mem _ huK)
    have hv := hmul (v * u⁻¹)
    rwa [mul_assoc, inv_mul_cancel₀ hune, mul_one] at hv

end AlbertSequential
