/- SPDX-License-Identifier: Apache-2.0 -/
module
public import OptimalSharpMenu
public import OptimalProjectionFamily
public import ReducedRealSpectralFrames

@[expose] public section
noncomputable section
namespace AlbertSequential
open Matrix
open scoped ComplexOrder

/-- A simultaneous first-corner dilation at any common upper bound for the defect ranks.
The same witness is real on real data and repeatable for certainty-supported outputs. -/
theorem exists_sharpDilation_of_defect_bound {d m : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X)
    (bound : ∀ x, let A := krausEffect (r.kraus x true); (A-A^2).rank ≤ m) :
    ∃ M : ReducedSharpDilationData d (d+m) X, M.inclusion = optimalCornerInclusion d m ∧
      IsReducedSharpDilation r M ∧
      (HasCertaintySupportedOutputs r → IsRepeatableReducedSharpDilation M) ∧
      (IsRealKrausRealization r → IsRealReducedSharpDilation M) := by
  classical
  have hd : 0 < d := by
    by_contra! hz
    have he : d = 0 := by omega
    subst d
    have ht := r.density.2
    simp [Matrix.trace] at ht
  apply exists_optimalSharpDilation_of_choices
  intro x
  exact Classical.choice (exists_optimalBinaryFrameChoice (krausEffect_positive _)
    (by rw [← r.no_effect]; exact krausEffect_positive _) (bound x) hd)

/-- Companion Proposition 6.4, with the maximum over the actual menu. -/
theorem exists_optimalSharpDilation {d : ℕ} {X : Type*} [Fintype X]
    (r : BinaryKrausRealization d X) :
    let m := menuDefectRank (fun x => krausEffect (r.kraus x true))
    ∃ M : ReducedSharpDilationData d (d+m) X, M.inclusion = optimalCornerInclusion d m ∧
      IsReducedSharpDilation r M ∧
      (HasCertaintySupportedOutputs r → IsRepeatableReducedSharpDilation M) ∧
      (IsRealKrausRealization r → IsRealReducedSharpDilation M) := by
  apply exists_sharpDilation_of_defect_bound
  intro x
  exact Finset.le_sup (f := fun x =>
    (krausEffect (r.kraus x true) - krausEffect (r.kraus x true)^2).rank) (Finset.mem_univ x)

end AlbertSequential
