/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.Models
public import MatchingModels.UniversalSix

/-!
# The ℂ¹² six-step model in the Challenge's terms (state complexification)

The development's complex models (`AlbertSequential.HilbertProjectiveData _ ℂ H`) carry a real
functional `φ` on the self-adjoint bounded operators. The Challenge's `ProjectiveRepresentation`
asks for a `ℂ`-linear state on all bounded operators. Extension: with `g` the real-linear,
Hermitian extension of `φ` to all operators (the development's `toAlgebraic.state`, i.e. `φ` of the
self-adjoint part), put `ψ(T) = g(T) − i g(iT)`. This is `ℂ`-linear, `ψ(1) = 1`, and on a
self-adjoint `T` the operator `iT` is skew so `g(iT) = 0` and `ψ(T) = φ(T)`; in particular `ψ` is
real and nonnegative on positive operators, and `Re ψ` agrees with `φ` on word operators.
Then `MatchingModels.UniversalSix.prop_cer_universalsix_c12` gives the theorem.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge.Bridge

open AlbertChallenge AlbertSequential

section Complexify

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}

/-- `g(T) = φ(self-adjoint part of T)`: real-linear and Hermitian. -/
def realPart (M : HilbertProjectiveData (Fin n) ℂ H) (T : H →L[ℂ] H) : ℝ :=
  M.toAlgebraic.state ((operatorValue ℂ H).symm T)

variable (M : HilbertProjectiveData (Fin n) ℂ H)

theorem realPart_add (S T : H →L[ℂ] H) : realPart M (S + T) = realPart M S + realPart M T := by
  unfold realPart
  rw [map_add, map_add]

omit [CompleteSpace H] in
theorem symm_real_smul (r : ℝ) (T : H →L[ℂ] H) :
    (operatorValue ℂ H).symm ((r : ℂ) • T) = r • (operatorValue ℂ H).symm T := by
  rw [RingEquiv.symm_apply_eq, operatorValue_real_smul, RingEquiv.apply_symm_apply]
  rfl

theorem realPart_real_smul (r : ℝ) (T : H →L[ℂ] H) :
    realPart M ((r : ℂ) • T) = r * realPart M T := by
  unfold realPart
  rw [symm_real_smul, map_smul, smul_eq_mul]

theorem realPart_neg (T : H →L[ℂ] H) : realPart M (-T) = -realPart M T := by
  unfold realPart
  rw [map_neg, map_neg]

theorem symm_star (T : H →L[ℂ] H) :
    (operatorValue ℂ H).symm (star T) = star ((operatorValue ℂ H).symm T) := by
  rw [RingEquiv.symm_apply_eq, operatorValue_star, RingEquiv.apply_symm_apply,
    ContinuousLinearMap.star_eq_adjoint]

theorem realPart_star (T : H →L[ℂ] H) : realPart M (star T) = realPart M T := by
  unfold realPart
  rw [symm_star, M.toAlgebraic.state_star]

theorem realPart_skew (T : H →L[ℂ] H) (hT : star T = -T) : realPart M T = 0 := by
  have h := realPart_star M T
  rw [hT, realPart_neg] at h
  linarith

theorem star_I_smul (T : H →L[ℂ] H) (hT : star T = T) :
    star (Complex.I • T) = -(Complex.I • T) := by
  rw [star_smul, hT, Complex.star_def, Complex.conj_I, neg_smul]

/-- The complexified state `ψ(T) = g(T) − i g(iT)`. -/
def complexState : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun T := (realPart M T : ℂ) - Complex.I * (realPart M (Complex.I • T) : ℂ)
  map_add' S T := by
    rw [smul_add, realPart_add, realPart_add]
    push_cast
    ring
  map_smul' c T := by
    have expand : ∀ X : H →L[ℂ] H,
        c • X = (c.re : ℂ) • X + (c.im : ℂ) • (Complex.I • X) := by
      intro X
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul]
    have hc := expand T
    have hIc : Complex.I • (c • T) = (c.re : ℂ) • (Complex.I • T) + (c.im : ℂ) • (-T) := by
      rw [smul_comm, expand, smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul]
    have h1 : realPart M (c • T) = c.re * realPart M T + c.im * realPart M (Complex.I • T) := by
      rw [hc, realPart_add, realPart_real_smul, realPart_real_smul]
    have h2 : realPart M (Complex.I • (c • T)) =
        c.re * realPart M (Complex.I • T) - c.im * realPart M T := by
      rw [hIc, realPart_add, realPart_real_smul, realPart_real_smul, realPart_neg]
      ring
    rw [RingHom.id_apply, smul_eq_mul, h1, h2]
    apply Complex.ext <;> simp <;> ring

theorem complexState_apply (T : H →L[ℂ] H) :
    complexState M T = (realPart M T : ℂ) - Complex.I * (realPart M (Complex.I • T) : ℂ) := rfl

theorem complexState_selfAdjoint (T : H →L[ℂ] H) (hT : star T = T) :
    complexState M T = (realPart M T : ℂ) := by
  rw [complexState_apply, realPart_skew M _ (star_I_smul T hT)]
  simp

/-- The development's complex model as a Challenge representation. -/
def toChallenge : ProjectiveRepresentation n ℂ H where
  projection i := operatorValue ℂ H (M.projection i)
  isStarProjection i := M.operatorProjection_isStarProjection i
  state := complexState M
  state_one := by
    rw [complexState_selfAdjoint M 1 (star_one _)]
    unfold realPart
    rw [map_one, M.toAlgebraic.state_unit]
    simp
  state_nonneg T hT := by
    have hsa : star T = T := hT.isSelfAdjoint.star_eq
    refine ⟨realPart M T, ?_, complexState_selfAdjoint M T hsa⟩
    have hsa' : IsSelfAdjoint ((operatorValue ℂ H).symm T) := by
      change star ((operatorValue ℂ H).symm T) = _
      rw [← symm_star, hsa]
    unfold realPart
    rw [show (operatorValue ℂ H).symm T = (⟨_, hsa'⟩ : selfAdjoint (HilbertOperatorAlgebra ℂ H)).val
      from rfl, M.toAlgebraic_state_selfAdjoint]
    apply M.positive
    change (operatorValue ℂ H ((operatorValue ℂ H).symm T)).IsPositive
    rw [RingEquiv.apply_symm_apply]
    exact hT

theorem toChallenge_probability (w : Word n) : (toChallenge M).probability w = M.probability w := by
  have hidem : ∀ i, M.projection i * M.projection i = M.projection i :=
    fun i => (M.isStarProjection i).isIdempotentElem.eq
  have hstar : ∀ i, star (M.projection i) = M.projection i :=
    fun i => (M.isStarProjection i).isSelfAdjoint.star_eq
  have hop : AlbertChallenge.wordOperator (toChallenge M).projection w =
      operatorValue ℂ H (AlbertSequential.wordOperator M.projection w) := by
    rw [← wordOperator_palindrome M.projection hidem hstar, wordOperator_map]
    rfl
  have hre : ∀ x y : ℝ, ((x : ℂ) - Complex.I * (y : ℂ)).re = x := by intro x y; simp
  unfold ProjectiveRepresentation.probability
  rw [hop]
  change Complex.re (complexState M _) = _
  rw [complexState_apply, hre]
  unfold realPart
  rw [RingEquiv.symm_apply_apply]
  exact M.toAlgebraic_probability w

end Complexify

theorem six_step_model_bridge (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hg : Generates p) :
    ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w ∈ wordsUpTo 4 6, M.probability w = wordProbability p maximallyMixed w := by
  obtain ⟨M, hM⟩ := MatchingModels.prop_cer_universalsix_c12 (fun i => toT (p i)) (atoms_toT hp)
    (fourPointInvariant_pos_of_generates hp hg)
  refine ⟨toChallenge M, fun w hw => ?_⟩
  rw [toChallenge_probability, hM w hw, maximallyMixed_toT, wordProbability_toT]

end AlbertChallenge.Bridge
