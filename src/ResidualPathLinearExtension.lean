/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HolonomyPrimitiveVectors

/-! Extend a literal path builder linearly to actual finite path combinations.
No state-dependent coefficients or supplied telescope field occur. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace CornerResidualBuilder
open PurityVectorExpression

def extendPaths (d : CornerNumericalData)
    (f : List (Fin 6) → PurityVectorExpression 4) (e : HolonomyPath.Combination) :
    PurityVectorExpression 4 :=
  e.flatMap (fun t => scale (t.1 * HolonomyPath.coefficient d t.2) (f t.2))

theorem extendPaths_value {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (P : Fin 4 → A) (d : CornerNumericalData)
    (f : List (Fin 6) → PurityVectorExpression 4) (F : A →ₗ[ℝ] A)
    (hf : ∀ p, evaluate P (f p) = F (wordAmplitude P (HolonomyPath.word p)))
    (e : HolonomyPath.Combination) :
    evaluate P (extendPaths d f e) = F (HolonomyPath.combinationValue P d e) := by
  induction e with
  | nil => simp only [extendPaths, List.flatMap_nil, evaluate_nil,
      HolonomyPath.combinationValue_nil, map_zero]
  | cons t e ih =>
      rcases t with ⟨r, p⟩
      simp only [extendPaths, List.flatMap_cons, evaluate_append, evaluate_scale] at ih ⊢
      rw [hf, ih, HolonomyPath.combinationValue_cons, HolonomyPath.polynomial_value,
        map_add, map_smul, map_smul, mul_smul]

theorem extendPaths_horizon (d : CornerNumericalData)
    (f : List (Fin 6) → PurityVectorExpression 4) (e : HolonomyPath.Combination)
    (depth L : ℕ) (hdepth : HolonomyPath.HasDepth e depth)
    (hf : ∀ p, p.length ≤ depth → (f p).HasHorizon L) :
    (extendPaths d f e).HasHorizon L := by
  intro t ht
  rcases List.mem_flatMap.mp ht with ⟨x, hx, htx⟩
  exact hasHorizon_scale _ _ _ (hf x.2 (hdepth x hx)) t htx

def leftAction {A : Type*} [Ring A] [Module ℝ A] [SMulCommClass ℝ A A] (x : A) : A →ₗ[ℝ] A where
  toFun := fun y => x * y
  map_add' := mul_add x
  map_smul' := fun r y => by simp only [mul_smul_comm, RingHom.id_apply]

end CornerResidualBuilder
end AlbertSequential
