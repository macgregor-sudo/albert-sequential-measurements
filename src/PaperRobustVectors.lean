/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PaperRobustResiduals
public import PaperResidualVectors

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential AlbertSequential.LengthSeven

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem apply_product (T U : H →L[ℝ] H) (x : H) : (T * U) x = T (U x) := rfl

def cornerVectorWalk (P : Letter → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i))
    (ζ : H) (hfix : P 0 ζ = ζ) (hζ : ζ ≠ 0) : WalkForm H where
  form := LinearMap.mk₂ ℝ (fun x y => (‖ζ‖^2)⁻¹ * ⟪x,y⟫_ℝ)
    (fun x y z => by rw [inner_add_left, mul_add])
    (fun r x y => by simp only [real_inner_smul_left, smul_eq_mul]; ring)
    (fun x y z => by rw [inner_add_right, mul_add])
    (fun r x y => by simp only [real_inner_smul_right, smul_eq_mul]; ring)
  symm x y := by
    change (‖ζ‖^2)⁻¹ * ⟪x,y⟫_ℝ = (‖ζ‖^2)⁻¹ * ⟪y,x⟫_ℝ
    rw [real_inner_comm x y]
  psd x := mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) real_inner_self_nonneg
  P i := (P i).toLinearMap
  idem i x := congrArg (fun T : H →L[ℝ] H => T x) (hp i).isIdempotentElem
  selfAdj i x y := by
    change (‖ζ‖^2)⁻¹ * ⟪P i x,y⟫_ℝ = (‖ζ‖^2)⁻¹ * ⟪x,P i y⟫_ℝ
    congr 1
    have h := (P i).adjoint_inner_right x y
    change ⟪x,(star (P i)) y⟫_ℝ = ⟪P i x,y⟫_ℝ at h
    rw [show star (P i) = P i from (hp i).isSelfAdjoint] at h
    exact h.symm
  ξ := ζ
  fixA := hfix
  unit := by
    change (‖ζ‖^2)⁻¹ * ⟪ζ,ζ⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hζ))]

theorem cornerVectorWalk_seqL (P : Letter → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i))
    (ζ : H) (hfix : P 0 ζ = ζ) (hζ : ζ ≠ 0) (u : Word Letter) (x : H) :
    (cornerVectorWalk P hp ζ hfix hζ).seqL u x = wordAmplitude P u x := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih =>
    rw [WalkForm.seqL_cons_apply, ih, wordAmplitude_cons, apply_product]
    rcases a with ⟨i,b⟩
    cases b <;> rfl

omit [CompleteSpace H] in
/-- The signed certificate vector formed from actual chronological words. -/
def residualGramVector (P : Letter → H →L[ℝ] H) (ζ : H)
    (vecs : List (ℚ × List Letter)) : H :=
  (vecs.map fun a => (a.1 : ℝ) • wordAmplitude P (yesWord a.2) ζ).sum

def robustResidualVector (P : Letter → H →L[ℝ] H) (ζ : H) (d : Defect) : H :=
  outcomePurityElement P (d.q,true) d.v (d.c : ℝ) (wordAmplitude P d.t ζ)

private theorem robustResidualVector_eq_paths (P : Letter → H →L[ℝ] H)
    (hp : ∀ i, IsStarProjection (P i)) (ζ : H) (d : Defect) :
    robustResidualVector P ζ d =
      wordAmplitude P d.long ζ - (d.c : ℝ) • wordAmplitude P d.short ζ := by
  rw [Defect.long, Defect.short,
    purityLong_amplitude P (fun i => (hp i).isIdempotentElem) (fun i => (hp i).isSelfAdjoint),
    wordAmplitude_append_singleton]
  simp only [robustResidualVector, outcomePurityElement, apply_product,
    sub_apply, smul_apply]

/-- In a real vector model the residual is exactly the printed three-word
quadratic expression; no nonzero preparation probability is required. -/
theorem robustResidualVector_square (P : Letter → H →L[ℝ] H)
    (hp : ∀ i, IsStarProjection (P i)) (ζ : H) (d : Defect) :
    let g := residualVectorProbability P ζ
    ‖robustResidualVector P ζ d‖^2 = g d.long - 2*d.c*g d.mid + (d.c : ℝ)^2*g d.short :=
  purityResidualVector_threeHistories P hp ζ (d.q,true) d.v d.t d.c

/-- The Appendix A.2 decomposition as a real inner-product identity for
the actual word amplitudes and purity residuals. -/
theorem gram_norm_realVector_eq_table_add_residuals
    (P : Letter → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i))
    (ζ : H) (hfix : P 0 ζ = ζ) (vecs : List (ℚ × List Letter)) (pairs : List (ℚ × Entry))
    (hPairs : pairs.map (fun p => (p.1, p.2.u1, p.2.u2)) = pairSpec vecs)
    (hok : pairs.all (fun p => p.2.ok) = true) :
    ‖residualGramVector P ζ vecs‖^2 =
      evalF (residualVectorProbability P ζ) (gramTableTerms pairs) +
      ((gramResidualOccurrences pairs).map fun o =>
        (o.1 : ℝ) * ⟪wordAmplitude P (yesWord o.2.α) ζ,robustResidualVector P ζ o.2⟫_ℝ).sum := by
  by_cases hζ : ζ = 0
  · subst ζ
    simp [residualGramVector, evalF, residualVectorProbability, robustResidualVector]
  let W := cornerVectorWalk P hp ζ hfix hζ
  let k := (‖ζ‖^2)⁻¹
  have hf (x y : H) : W.form x y = k * ⟪x,y⟫_ℝ := rfl
  have hvec (w : Word Letter) : W.vec w = wordAmplitude P w ζ :=
    cornerVectorWalk_seqL P hp ζ hfix hζ w ζ
  have hL : phiVec W vecs = residualGramVector P ζ vecs := by
    simp only [phiVec, residualGramVector, WalkForm.pathVec, hvec]
  have hnorm (x : H) : W.normSq x = k * ‖x‖^2 := by
    rw [WalkForm.normSq, hf, real_inner_self_eq_norm_sq]
  have hd (d : Defect) : d.resid W = robustResidualVector P ζ d := by
    rw [robustResidualVector_eq_paths P hp, Defect.resid, hvec, hvec]
  have hR (w : Word Letter) : W.normSq (W.vec w) = k * residualVectorProbability P ζ w := by
    rw [hnorm,hvec]
    rfl
  have htable : evalF (fun w => W.normSq (W.vec w)) (gramTableTerms pairs) =
      k * evalF (residualVectorProbability P ζ) (gramTableTerms pairs) := by
    simp only [evalF, hR, mul_sum_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro m _
    ring
  have h := gram_norm_eq_table_add_residuals W vecs pairs hPairs hok
  rw [hL, hnorm, htable] at h
  have hres : ((gramResidualOccurrences pairs).map fun o =>
        (o.1 : ℝ) * W.form (W.pathVec o.2.α) (o.2.resid W)).sum =
      k * ((gramResidualOccurrences pairs).map fun o =>
        (o.1 : ℝ) * ⟪wordAmplitude P (yesWord o.2.α) ζ,robustResidualVector P ζ o.2⟫_ℝ).sum := by
    rw [mul_sum_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro o _
    rw [WalkForm.pathVec, hvec, hd, hf]
    ring
  rw [hres, ← mul_add] at h
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hζ))) h

omit [CompleteSpace H] in
/-- The probability at the unnormalized corner vector is the unconditioned
probability after a leading yes on A in the original vector model. -/
theorem residualVectorProbability_prefix (P : Letter → H →L[ℝ] H) (Ω : H) (w : Word Letter) :
    residualVectorProbability P (P 0 Ω) w = residualVectorProbability P Ω ((0,true)::w) := by
  simp only [residualVectorProbability, wordAmplitude_cons, apply_product, algebraicOutcome, ite_true]

/-- The exact table and pairing decomposition in the original, unconditioned
probabilities after prepending the yes on A. -/
theorem gram_norm_unconditioned_eq_table_add_residuals
    (P : Letter → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i))
    (Ω : H) (vecs : List (ℚ × List Letter)) (pairs : List (ℚ × Entry))
    (hPairs : pairs.map (fun p => (p.1, p.2.u1, p.2.u2)) = pairSpec vecs)
    (hok : pairs.all (fun p => p.2.ok) = true) :
    let ζ := P 0 Ω
    ‖residualGramVector P ζ vecs‖^2 =
      evalF (fun w => residualVectorProbability P Ω ((0,true)::w)) (gramTableTerms pairs) +
      ((gramResidualOccurrences pairs).map fun o =>
        (o.1 : ℝ) * ⟪wordAmplitude P (yesWord o.2.α) ζ,robustResidualVector P ζ o.2⟫_ℝ).sum := by
  have hfix : P 0 (P 0 Ω) = P 0 Ω :=
    congrArg (fun T : H →L[ℝ] H => T Ω) (hp 0).isIdempotentElem
  have htable : residualVectorProbability P (P 0 Ω) =
      fun w => residualVectorProbability P Ω ((0,true)::w) :=
    funext (residualVectorProbability_prefix P Ω)
  rw [← htable]
  exact gram_norm_realVector_eq_table_add_residuals P hp _ hfix vecs pairs hPairs hok

end AlbertSequential.LengthSeven.Robust
