/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CyclicWordVectors
public import BlockA.SecondOrderResidual
public import NativeWordPurity

/-! Core Lemma 4.4 with the named finite word combination and a restricted set of histories. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open NativeAnalysis
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem cyclic_null_on_histories (M : AlgebraicProjectiveData ι A)
    (p : ι → Albert) (ρ : Albert) (c : Word ι →₀ ℝ) (Z : CyclicWordAlgebra M)
    (hself : star (Z : A) = Z)
    (hE : c.sum (fun w a => a • wordOperator M.projection w) = (Z : A) * Z)
    (hθ : AppF.nativeWordCombinationEffect c p = 0) (T : Set (Word ι))
    (hmatch : ∀ t ∈ T, ∀ w ∈ c.support, M.probability (t ++ w) = nativeWordProbability p ρ (t ++ w))
    (t : Word ι) (ht : t ∈ T) :
    cyclicHilbertRepresentation M Z
      (wordAmplitude (cyclicHilbertProjection M) t (cyclicHilbertVector M)) = 0 := by
  classical
  let B := wordAmplitude M.projection t
  have hn : M.state (star B * ((Z : A) * Z) * B) = 0 := by
    rw [← hE, Finsupp.sum, Finset.mul_sum, Finset.sum_mul, map_sum]
    calc
      _ = ∑ w ∈ c.support, c w * M.probability (t ++ w) := by
        apply Finset.sum_congr rfl
        intro w _
        simp only [B, AlgebraicProjectiveData.probability, wordOperator_append, mul_smul_comm,
          smul_mul_assoc, map_smul, smul_eq_mul]
      _ = c.sum (fun w a => a * nativeWordProbability p (nativeBranchState p ρ t) w) := by
        exact Finset.sum_congr rfl (fun w hw => congrArg (c w * ·)
          ((hmatch t ht w hw).trans (native_probability_append p ρ t w)))
      _ = 0 := by rw [← AppF.tracePairing_nativeWordCombinationEffect, hθ, ← AppF.tracePairingLM_apply, map_zero]
  rw [← cyclicHilbertRepresentation_word]
  change cyclicHilbertRepresentation M Z
    (cyclicHilbertRepresentation M (cyclicWordElement M t) (cyclicHilbertVector M)) = 0
  rw [← mul_apply_eq_comp, ← map_mul, cyclicHilbertAction_vector]
  apply norm_eq_zero.mp
  have hsq := cyclicPreHilbert_norm_sq M (cyclicWordAlgebraEquiv M (Z * cyclicWordElement M t))
  change ‖_‖ ^ 2 = M.state (star ((Z : A) * B) * ((Z : A) * B)) at hsq
  rw [star_mul, hself] at hsq
  rw [mul_assoc, mul_assoc] at hn
  simp only [mul_assoc] at hsq
  rw [hn] at hsq
  rw [UniformSpace.Completion.norm_coe]
  exact pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp hsq

theorem cyclic_null_operator_of_matches (M : AlgebraicProjectiveData ι A)
    (p : ι → Albert) (ρ : Albert) (c : Word ι →₀ ℝ) (Z : CyclicWordAlgebra M)
    (hself : star (Z : A) = Z)
    (hE : c.sum (fun w a => a • wordOperator M.projection w) = (Z : A) * Z)
    (hθ : AppF.nativeWordCombinationEffect c p = 0)
    (hmatch : ∀ w, M.probability w = nativeWordProbability p ρ w) :
    cyclicHilbertRepresentation M Z = 0 := by
  let F := cyclicHilbertRepresentation M Z
  have hk : Dense (LinearMap.ker F.toLinearMap : Set (CyclicHilbert M)) := by
    apply (cyclicHilbert_cyclic M).mono
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact cyclic_null_on_histories M p ρ c Z hself hE hθ Set.univ
      (fun t _ w _ => hmatch (t ++ w)) t (Set.mem_univ t)
  have hall := hk.closure_eq
  rw [F.isClosed_ker.closure_eq] at hall
  ext x
  exact (Set.eq_univ_iff_forall.mp hall) x

end AlbertSequential
