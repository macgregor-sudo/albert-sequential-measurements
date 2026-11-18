module

public import ChoiCompletePositivity

/-! Exact basis bridge for arbitrary complex-linear maps, not only actions
already presented in Choi or Kraus form. The complete-positivity criterion is
ordinary positivity of every finite matrix amplification.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

def choiLinearMap {d : ℕ} (C : ChoiMatrix d) :
    ComplexMatrix d →ₗ[ℂ] ComplexMatrix d where
  toFun := choiAction C
  map_add' := (choiAction_linear C).1
  map_smul' := (choiAction_linear C).2

def linearMapChoi {d : ℕ} (Phi : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d) :
    ChoiMatrix d := fun ik jl => Phi (Matrix.single ik.1 jl.1 1) ik.2 jl.2

set_option backward.isDefEq.respectTransparency false in
theorem matrixUnitExpansion {d : ℕ} (Y : ComplexMatrix d) :
    Y = ∑ i, ∑ j, Y i j • Matrix.single i j 1 := by
  classical
  ext k l
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

theorem choiAction_linearMapChoi {d : ℕ}
    (Phi : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d) (Y : ComplexMatrix d) :
    choiAction (linearMapChoi Phi) Y = Phi Y := by
  have hm := congrArg Phi (matrixUnitExpansion Y)
  simp only [map_sum, map_smul] at hm
  ext k l
  have hkl := congrFun (congrFun hm k) l
  simpa [choiAction, linearMapChoi, Matrix.sum_apply] using hkl.symm

theorem linearMapChoi_choiLinearMap {d : ℕ} (C : ChoiMatrix d) :
    linearMapChoi (choiLinearMap C) = C := by
  ext ⟨i, k⟩ ⟨j, l⟩
  exact choiAction_single C i j k l

theorem choiLinearMap_linearMapChoi {d : ℕ}
    (Phi : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d) :
    choiLinearMap (linearMapChoi Phi) = Phi := by
  ext Y k l
  exact congrFun (congrFun (choiAction_linearMapChoi Phi Y) k) l

theorem linearMapChoi_positive_iff {d : ℕ}
    (Phi : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d) :
    (linearMapChoi Phi).PosSemidef ↔ IsCompletelyPositiveMatrixMap Phi := by
  have heq : choiAction (linearMapChoi Phi) = Phi :=
    funext (choiAction_linearMapChoi Phi)
  simpa only [heq] using choi_positive_iff_completelyPositive (linearMapChoi Phi)

theorem linearMapChoi_trace_preservation_iff {d : ℕ}
    (Phi : ComplexMatrix d →ₗ[ℂ] ComplexMatrix d) :
    choiOutputTrace (linearMapChoi Phi) = 1 ↔
      ∀ Y, Matrix.trace (Phi Y) = Matrix.trace Y := by
  simpa only [choiAction_linearMapChoi] using
    choi_trace_preservation_iff (linearMapChoi Phi)

end AlbertSequential
