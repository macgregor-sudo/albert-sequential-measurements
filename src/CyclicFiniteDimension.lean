/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicHilbertModel
public import QuaternionicProjectiveData
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.RCLike.Lemmas

/-! A finite real word algebra gives an actual finite-dimensional completed
cyclic space. Finiteness of a dense subspace alone is not the conclusion. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace AlbertSequential
section
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm
variable (M : AlgebraicProjectiveData ι A)

instance cyclicPreHilbert_finiteDimensional [FiniteDimensional ℝ (wordSubalgebra M.projection)] :
    FiniteDimensional ℝ (CyclicPreHilbert M) :=
  FiniteDimensional.of_injective (cyclicPreHilbertLinearEquiv M).toLinearMap
    (cyclicPreHilbertLinearEquiv M).injective

theorem cyclicHilbert_embedding_surjective [FiniteDimensional ℝ (wordSubalgebra M.projection)] :
    Function.Surjective ((↑) : CyclicPreHilbert M → CyclicHilbert M) := by
  let : CompleteSpace (CyclicPreHilbert M) := FiniteDimensional.completeSpace ℝ (CyclicPreHilbert M)
  let e : CyclicPreHilbert M →ₗᵢ[ℝ] CyclicHilbert M := UniformSpace.Completion.toComplₗᵢ
  have hclosed : IsClosed (Set.range e) := e.isometry.isClosedEmbedding.isClosed_range
  have hdense : DenseRange e := UniformSpace.Completion.denseRange_coe
  have hrange : Set.range e=Set.univ := by
    rw [←hclosed.closure_eq]
    exact hdense.closure_range
  exact Set.range_eq_univ.mp hrange

instance cyclicHilbert_finiteDimensional [FiniteDimensional ℝ (wordSubalgebra M.projection)] :
    FiniteDimensional ℝ (CyclicHilbert M) :=
  FiniteDimensional.of_surjective
    (UniformSpace.Completion.toComplₗᵢ : CyclicPreHilbert M →ₗᵢ[ℝ] CyclicHilbert M).toLinearMap
    (cyclicHilbert_embedding_surjective M)

theorem cyclicHilbert_finrank_le [FiniteDimensional ℝ (wordSubalgebra M.projection)] :
    Module.finrank ℝ (CyclicHilbert M) ≤ Module.finrank ℝ (wordSubalgebra M.projection) := by
  have hH : Module.finrank ℝ (CyclicHilbert M) ≤ Module.finrank ℝ (CyclicPreHilbert M) :=
    LinearMap.finrank_le_finrank_of_surjective
      (f := (UniformSpace.Completion.toComplₗᵢ :
        CyclicPreHilbert M →ₗᵢ[ℝ] CyclicHilbert M).toLinearMap)
      (cyclicHilbert_embedding_surjective M)
  rw [(cyclicPreHilbertLinearEquiv M).finrank_eq] at hH
  exact hH.trans (Submodule.finrank_quotient_le (cyclicNullSubmodule M))

theorem cyclicHilbert_finite_of_ambient [FiniteDimensional ℝ A] :
    FiniteDimensional ℝ (CyclicHilbert M) := by
  let : FiniteDimensional ℝ (wordSubalgebra M.projection) :=
    FiniteDimensional.of_injective (wordSubalgebra M.projection).val.toLinearMap Subtype.val_injective
  infer_instance

theorem cyclicHilbert_finrank_le_ambient [FiniteDimensional ℝ A] :
    Module.finrank ℝ (CyclicHilbert M) ≤ Module.finrank ℝ A := by
  let : FiniteDimensional ℝ (wordSubalgebra M.projection) :=
    FiniteDimensional.of_injective (wordSubalgebra M.projection).val.toLinearMap Subtype.val_injective
  exact (cyclicHilbert_finrank_le M).trans
    (LinearMap.finrank_le_finrank_of_injective (f := (wordSubalgebra M.projection).val.toLinearMap)
      Subtype.val_injective)
end

section ActualFiniteModels
variable {ι 𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H] [FiniteDimensional 𝕜 H]

-- Preserve exactly the additive and real-module paths used by the
-- bounded-operator algebra, even after finite-dimensional norm imports.
local instance : AddCommGroup (HilbertOperatorAlgebra 𝕜 H) :=
  hilbertOperatorAddCommGroup 𝕜 H
local instance : Module ℝ (HilbertOperatorAlgebra 𝕜 H) :=
  hilbertOperatorRealModule 𝕜 H

omit [CompleteSpace H] in
theorem hilbertOperatorAlgebra_finiteReal : FiniteDimensional ℝ (HilbertOperatorAlgebra 𝕜 H) := by
  -- Native basis coordinates give a real-linear injection without installing
  -- a second scalar-module instance on the real operator carrier.
  let b := Module.finBasis 𝕜 H
  let F : HilbertOperatorAlgebra 𝕜 H →ₗ[ℝ]
      (Fin (Module.finrank 𝕜 H) × Fin (Module.finrank 𝕜 H) → 𝕜) :=
    { toFun T ij := b.repr (operatorValue 𝕜 H T (b ij.2)) ij.1
      map_add' T U := by
        funext ij
        change b.repr (operatorValue 𝕜 H T (b ij.2)+operatorValue 𝕜 H U (b ij.2)) ij.1 = _
        rw [map_add]
        rfl
      map_smul' r T := by
        funext ij
        change b.repr ((r : 𝕜) • (operatorValue 𝕜 H T (b ij.2))) ij.1 =
          r • (b.repr (operatorValue 𝕜 H T (b ij.2)) ij.1)
        simp only [map_smul,Finsupp.smul_apply,smul_eq_mul,RCLike.real_smul_eq_coe_mul] }
  apply FiniteDimensional.of_injective F
  intro T U hTU
  apply (operatorValue 𝕜 H).injective
  have hlin : (operatorValue 𝕜 H T).toLinearMap=(operatorValue 𝕜 H U).toLinearMap := by
    apply b.ext
    intro j
    apply b.repr.injective
    ext i
    exact congrFun hTU (i,j)
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun hlin x

theorem HilbertProjectiveData.cyclicHilbert_finite (M : HilbertProjectiveData ι 𝕜 H) :
    FiniteDimensional ℝ (CyclicHilbert M.toAlgebraic) := by
  exact @cyclicHilbert_finite_of_ambient ι (HilbertOperatorAlgebra 𝕜 H)
    _ _ _ _ _ _ M.toAlgebraic (hilbertOperatorAlgebra_finiteReal (𝕜 := 𝕜) (H := H))
end ActualFiniteModels

section ActualFiniteQuaternionicModel
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H] {Q : QuaternionicOperatorStructure H}

/-- The premise here is explicitly finite UNDERLYING REAL H. The separate
finite right-quaternionic-module to real-dimension bridge is not assumed. -/
theorem QuaternionicProjectiveData.cyclicHilbert_finite_of_real
    (M : QuaternionicProjectiveData ι Q) : FiniteDimensional ℝ (CyclicHilbert M.toAlgebraic) := by
  let : FiniteDimensional ℝ Q.operatorAlgebra :=
    FiniteDimensional.of_injective Q.operatorValue.toAlgHom.toLinearMap Q.operatorValue_injective
  exact cyclicHilbert_finite_of_ambient M.toAlgebraic
end ActualFiniteQuaternionicModel
end AlbertSequential
