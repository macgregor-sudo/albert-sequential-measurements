/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FixedSNativeLeaves
public import FixedSCornerDiscriminants
public import FixedSSumBounds

/-! The explicit fixed-S separating functional built by the constructor. This is a
proved eleven-letter upper bound for the literal constructor, with all-state
native margin. It is not identified with any array or word count of the paper. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace AlbertSequential
open NativeAnalysis
open scoped BigOperators

def fixedSConstructedWitness : FiniteRealWordFunctional 4 :=
  combinedCornerWitness fixedSCornerData fixedSCornerScalar
    (fun j a => fixedSCornerRelabelling j a) (fun _ => 1) (7 / 414)

theorem fixedS_combinedBase_evaluate (g : Word (Fin 4) → ℝ) :
    (combinedCornerBase fixedSCornerData (fun j a => fixedSCornerRelabelling j a)
      (fun _ => 1)).evaluate g = (1 / 12 : ℝ) * ∑ j : Fin 4, g [(j, true)] := by
  simp only [combinedCornerBase, FiniteRealWordFunctional.evaluate_combine,
    List.map_ofFn, Function.comp_def, FiniteRealWordFunctional.evaluate_scale,
    FiniteRealWordFunctional.evaluate_relabel, cornerBaseFunctional_evaluate,
    fixedSCorner_discriminant, one_mul, relabelWord_cons, relabelWord_nil,
    relabelOutcome, fixedSCornerRelabelling_base, List.sum_ofFn]
  rw [Finset.mul_sum]

theorem fixedS_native_singleton (ρ : Albert) (j : Fin 4) :
    nativeWordProbability fixedS ρ [(j, true)] = tracePairing ρ (fixedS j) := by
  rw [nativeWordProbability_eq_pairing,
    nativeWordEffect_singleton fixedS (fun i => (fixedS_isAtom i).1)]
  rfl

theorem fixedS_allState_base_mass (ρ : Albert) (hρ : IsDensity ρ) :
    (7 / 414 : ℝ) ≤
      (combinedCornerBase fixedSCornerData (fun j a => fixedSCornerRelabelling j a)
        (fun _ => 1)).evaluate (nativeWordProbability fixedS ρ) := by
  rw [fixedS_combinedBase_evaluate]
  have hsum : (∑ j : Fin 4, nativeWordProbability fixedS ρ [(j, true)]) =
      tracePairing ρ fixedSAtomSum := by
    simp only [fixedS_native_singleton, fixedSAtomSum, Fin.sum_univ_four, tracePairing_add_right]
  rw [hsum]
  have h := fixedSAtomSum_density_mass ρ hρ
  linarith

theorem fixedSConstructedWitness_model_nonnegative
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) :
    0 ≤ fixedSConstructedWitness.evaluate M.probability :=
  combinedCornerWitness_model_nonnegative fixedSCornerData fixedSCornerScalar
    (fun j a => fixedSCornerRelabelling j a) (fun _ => 1) fixedSCorner_conditions M
    (7 / 414) (by norm_num)

theorem fixedSConstructedWitness_horizon : fixedSConstructedWitness.HasHorizon 11 :=
  combinedCornerWitness_horizon fixedSCornerData fixedSCornerScalar
    (fun j a => fixedSCornerRelabelling j a) (fun _ => 1) (7 / 414)

theorem fixedSConstructedWitness_native_le (ρ : Albert) (hρ : IsDensity ρ) :
    fixedSConstructedWitness.evaluate (nativeWordProbability fixedS ρ) ≤ -(7 / 828) := by
  have hu : nativeWordProbability fixedS ρ [] = 1 := hρ.2
  have h := combinedCornerWitness_target_margin fixedSCornerData fixedSCornerScalar
    (fun j a => fixedSCornerRelabelling j a) (fun _ => 1) (7 / 414) (by norm_num)
    (nativeWordProbability fixedS ρ) hu (fixedS_combined_leaves_native_zero ρ)
    (fixedS_allState_base_mass ρ hρ)
  norm_num at h
  exact h

/-- A uniform finite-table error lower bound using the actual merged coefficient
norm of this literal witness. No numerical norm or optimality claim is made. -/
theorem fixedSConstructedWitness_forces_error
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin 4) A) (ρ : Albert) (hρ : IsDensity ρ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ w, w.length ≤ 11 → |M.probability w - nativeWordProbability fixedS ρ w| ≤ ε) :
    (7 / 828 : ℝ) ≤ fixedSConstructedWitness.coefficientNorm * ε :=
  fixedSConstructedWitness.separation_forces_error M.probability
    (nativeWordProbability fixedS ρ) ε (7 / 828) hε
    (fun w hw => herr w (fixedSConstructedWitness.coefficient_support_hasHorizon 11
      fixedSConstructedWitness_horizon w hw))
    (fixedSConstructedWitness_model_nonnegative M) (fixedSConstructedWitness_native_le ρ hρ)

end AlbertSequential
