/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Bridge.EJAFixedUnitary
public import Robustness.RealTraceProjectiveWords
public import Robustness.QuaternionicTraceProjectiveWords

@[expose] public section
noncomputable section

namespace AlbertSequential.FixedUnitary

open HilbertTrace

def preTestAmplitude {I A : Type*} [Ring A] (Y : A) (P : I → A) (w : Word I) : A :=
  w.foldl (fun A q => algebraicOutcome P q * (Y * A)) 1

private theorem preTestAmplitude_snoc {I A : Type*} [Ring A] (Y : A) (P : I → A)
    (w : Word I) (q : Outcome I) :
    preTestAmplitude Y P (w ++ [q]) = algebraicOutcome P q * (Y * preTestAmplitude Y P w) := by
  simp [preTestAmplitude, List.foldl_append]

private theorem mapOutcome {I A B : Type*} [Ring A] [Ring B]
    (F : A →+* B) (P : I → A) (q : Outcome I) :
    F (algebraicOutcome P q) = algebraicOutcome (fun i => F (P i)) q := by
  cases q with
  | mk i b => cases b <;> simp [algebraicOutcome]

private theorem mapPreTestAmplitude {I A B : Type*} [Ring A] [Ring B]
    (F : A →+* B) (Y : A) (P : I → A) (w : Word I) :
    F (preTestAmplitude Y P w) = preTestAmplitude (F Y) (fun i => F (P i)) w := by
  induction w using List.reverseRecOn with
  | nil => exact map_one F
  | append_singleton w q ih =>
    rw [preTestAmplitude_snoc, preTestAmplitude_snoc, map_mul, map_mul, mapOutcome, ih]

section Real

variable {H I B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local notation "Op" => (H →L[ℝ] H)
variable (b : HilbertBasis B ℝ H)

private def leftUnitary (Y : Op) (hYl : star Y * Y = 1) (hYr : Y * star Y = 1) :
    Op ≃ₗ[ℝ] Op where
  toLinearMap := LinearMap.mulLeft ℝ Y
  invFun X := star Y * X
  left_inv X := by
    change star Y * (Y * X) = X
    rw [← mul_assoc, hYl, one_mul]
  right_inv X := by
    change Y * (star Y * X) = X
    rw [← mul_assoc, hYr, one_mul]

omit [CompleteSpace H] in
private theorem leftAnswer (P : I → Op) (q : Outcome I) (X : Op) :
    answer (fun i => LinearMap.mulLeft ℝ (P i)) q X = algebraicOutcome P q * X := by
  obtain ⟨i, a⟩ := q
  cases a
  · change X - P i * X = (1 - P i) * X
    rw [sub_mul, one_mul]
  · rfl

private theorem sandwich_mul (A C : Op) (X : signedFiniteTrace b) :
    realSandwich b A (realSandwich b C X) = realSandwich b (A * C) X := by
  apply Subtype.ext
  change A * (C * X.val * star C) * star A = (A * C) * X.val * star (A * C)
  simp only [star_mul, mul_assoc]

private theorem sandwich_factor (A F : Op) (X : signedFiniteTrace b) (hF : F * star F = X.val) :
    (realSandwich b A X).val = (A * F) * star (A * F) := by
  change A * X.val * star A = (A * F) * star (A * F)
  rw [← hF, star_mul]
  simp only [mul_assoc]

private theorem trace_conjugation (Y : Op) (hY : star Y * Y = 1) (X : signedFiniteTrace b) :
    signedTrace b (realSandwich b Y X) = signedTrace b X := by
  rw [signedTrace_realSandwich, hY]
  rfl

private theorem trace_conjugation_power (Y : Op) (hY : star Y * Y = 1) (k : ℕ)
    (X : signedFiniteTrace b) : signedTrace b (realSandwich b (Y ^ k) X) = signedTrace b X := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact trace_conjugation b 1 (by simp) X
  | succ k ih =>
    rw [pow_succ', ← sandwich_mul, trace_conjugation b Y hY, ih]

variable [FiniteDimensional ℝ H]

private theorem real_remove_preTest (Y : Op) (hYl : star Y * Y = 1) (hYr : Y * star Y = 1)
    (P : I → Op) (X : signedFiniteTrace b) (hX : X.val.IsPositive)
    (hzero : ∀ w i (a : Bool), signedTrace b
      (realSandwich b (preTestAmplitude Y P (w ++ [(i, a), (i, !a)])) X) = 0)
    (w : Word I) :
    signedTrace b (realSandwich b (wordAmplitude P w) (realSandwich b Y X)) =
      signedTrace b (realSandwich b (preTestAmplitude Y P w) X) := by
  have : FiniteDimensional ℝ Op :=
    FiniteDimensional.of_injective (ContinuousLinearMap.coeLM ℝ) ContinuousLinearMap.coe_injective
  obtain ⟨F, hF, hFF⟩ := exists_real_positive_square_root hX
  have hfac : F * star F = X.val := by rw [hF.isSelfAdjoint.star_eq, hFF]
  let U := leftUnitary Y hYl hYr
  let T := fun i => LinearMap.mulLeft ℝ (P i)
  have form (v : Word I) : trajectory U T (Y * F) v = (Y * preTestAmplitude Y P v) * F := by
    induction v using List.reverseRecOn with
    | nil => simp [trajectory, preTestAmplitude]
    | append_singleton v q ih =>
      rw [trajectory_snoc, ih, preTestAmplitude_snoc]
      rw [show answer T q _ = algebraicOutcome P q * _ from leftAnswer P q _]
      change Y * (algebraicOutcome P q * ((Y * preTestAmplitude Y P v) * F)) = _
      simp only [mul_assoc]
  have kill (v : Word I) (i : I) (a : Bool) :
      answer T (i, !a) (U (answer T (i, a) (trajectory U T (Y * F) v))) = 0 := by
    let z := v ++ [(i, a), (i, !a)]
    let A := preTestAmplitude Y P z
    have hv : (realSandwich b A X).val = 0 := by
      by_contra hn
      have hp := (real_signedTrace_pos_iff b (realSandwich_positive b A X hX)).mpr hn
      exact (ne_of_gt hp) (hzero v i a)
    rw [sandwich_factor b A F X hfac, mul_star_self_eq_zero] at hv
    have hz : trajectory U T (Y * F) z = 0 := by
      rw [form, mul_assoc, hv, mul_zero]
    have he : z = (v ++ [(i, a)]) ++ [(i, !a)] := by simp [z]
    rw [he, trajectory_snoc, trajectory_snoc] at hz
    exact U.injective (hz.trans U.map_zero.symm)
  have powers (k : ℕ) (A : Op) : (U.toLinearMap ^ k) A = Y ^ k * A := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_succ' Y]
      change Y * ((U.toLinearMap ^ k) A) = (Y * Y ^ k) * A
      rw [ih, mul_assoc]
  have htrajectory := remove_between U T (Y * F) kill w
  rw [form, powers] at htrajectory
  simp only [T, leftAnswer, wordAmplitude_foldl] at htrajectory
  have hfactor : (Y * preTestAmplitude Y P w) * F =
      (Y ^ w.length * (wordAmplitude P w * Y)) * F := by
    simpa only [mul_assoc] using htrajectory
  have hsandwich : realSandwich b (Y * preTestAmplitude Y P w) X =
      realSandwich b (Y ^ w.length * (wordAmplitude P w * Y)) X := by
    apply Subtype.ext
    rw [sandwich_factor b _ F X hfac, sandwich_factor b _ F X hfac, hfactor]
  have htrace := congrArg (signedTrace b) hsandwich
  simpa only [← sandwich_mul, trace_conjugation b Y hYl, trace_conjugation_power b Y hYl]
    using htrace.symm

/-- Rotating only the initial real density removes the fixed pre-test unitary
when all opposite-repeat weights vanish. -/
theorem real_projective_of_fixedUnitary_noSwitch (Y : unitary Op) (P : I → Op)
    (hP : ∀ i, IsStarProjection (P i)) (X : signedFiniteTrace b) (hX : IsRealDensity b X)
    (f : Word I → ℝ) (hzero : ∀ w i (a : Bool), f (w ++ [(i, a), (i, !a)]) = 0)
    (hm : ∀ w, signedTrace b (realSandwich b (preTestAmplitude (Y : Op) P w) X) = f w) :
    ∃ hrot : IsRealDensity b (realSandwich b (Y : Op) X), ∀ w,
      (realTraceProjectiveModel b P hP _ hrot).probability w = f w := by
  obtain ⟨hpos, htr⟩ := hX
  have hY := Unitary.coe_star_mul_self Y
  have hrot : IsRealDensity b (realSandwich b (Y : Op) X) :=
    ⟨realSandwich_positive b _ X hpos, (trace_conjugation b _ hY X).trans htr⟩
  refine ⟨hrot, ?_⟩
  intro w
  rw [realTraceProjectiveModel_probability, real_sandwich_word, ← hm]
  exact real_remove_preTest b _ hY (Unitary.coe_mul_star_self Y) P X hpos
    (fun v i a => (hm _).trans (hzero v i a)) w

end Real

section Quaternionic

variable {H I B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]
variable (b : HilbertBasis B ℝ H) (S : RightQuaternionicHilbertStructure H)
local notation "Op" => S.toOperatorStructure.operatorAlgebra
local notation "Carrier" => quaternionicSignedFiniteTrace b S
local notation "qTrace" => quaternionicSignedTrace b S

/-- All amplitudes and the rotated density belong to the right-quaternionic
operator algebra. Its physical trace is used on both sides. -/
theorem quaternionic_projective_of_fixedUnitary_noSwitch (Y : unitary Op) (P : I → Op)
    (hP : ∀ i, IsStarProjection (P i)) (X : Carrier) (hX : IsQuaternionicDensity b S X)
    (f : Word I → ℝ) (hzero : ∀ w i (a : Bool), f (w ++ [(i, a), (i, !a)]) = 0)
    (hm : ∀ w, qTrace (quaternionicSandwich b S (preTestAmplitude (Y : Op) P w) X) = f w) :
    ∃ hrot : IsQuaternionicDensity b S (quaternionicSandwich b S (Y : Op) X), ∀ w,
      let M := quaternionicTraceProjectiveModel b S P hP _ hrot
      M.state (M.wordEffect w) = f w := by
  obtain ⟨hpos, htr⟩ := hX
  let Yr := (Y : Op).val
  let Pr (i : I) := (P i).val
  let Xr := quaternionicCarrierInclusion b S X
  have hYl : star Yr * Yr = 1 := congrArg Subtype.val (Unitary.coe_star_mul_self Y)
  have hYr : Yr * star Yr = 1 := congrArg Subtype.val (Unitary.coe_mul_star_self Y)
  have hA (w : Word I) : (preTestAmplitude (Y : Op) P w).val = preTestAmplitude Yr Pr w :=
    mapPreTestAmplitude S.toOperatorStructure.operatorValue.toRingHom _ _ w
  have hW (w : Word I) : (wordAmplitude P w).val = wordAmplitude Pr w := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w a ih =>
      rw [wordAmplitude_append_singleton, wordAmplitude_append_singleton]
      change (algebraicOutcome P a).val * (wordAmplitude P w).val = _
      rw [ih, show (algebraicOutcome P a).val = algebraicOutcome Pr a from
        mapOutcome S.toOperatorStructure.operatorValue.toRingHom P a]
  have hmr (w : Word I) :
      (1 / 4 : ℝ) * signedTrace b (realSandwich b (preTestAmplitude Yr Pr w) Xr) = f w := by
    rw [← hA]
    exact hm w
  have hz (w : Word I) (i : I) (a : Bool) : signedTrace b
      (realSandwich b (preTestAmplitude Yr Pr (w ++ [(i, a), (i, !a)])) Xr) = 0 := by
    rcases mul_eq_zero.mp ((hmr _).trans (hzero w i a)) with he | he
    · norm_num at he
    · exact he
  have hnorm : qTrace (quaternionicSandwich b S (Y : Op) X) = 1 := by
    change (1 / 4 : ℝ) * signedTrace b (realSandwich b Yr Xr) = 1
    rw [trace_conjugation b Yr hYl]
    exact htr
  have hrot : IsQuaternionicDensity b S (quaternionicSandwich b S (Y : Op) X) :=
    ⟨quaternionicSandwich_positive b S _ X hpos, hnorm⟩
  refine ⟨hrot, ?_⟩
  intro w
  dsimp only
  rw [quaternionicTraceProjectiveModel_probability, quaternionic_sandwich_word]
  change (1 / 4 : ℝ) * signedTrace b
    (realSandwich b (wordAmplitude P w).val (realSandwich b Yr Xr)) = f w
  rw [hW, real_remove_preTest b Yr hYl hYr Pr Xr hpos hz]
  exact hmr w

end Quaternionic

section JordanTable

variable {E I H B : Type*} [AddCommGroup E] [Module ℝ E]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]
variable (J : UnitalJordanProduct E) (b : HilbertBasis B ℝ H)

theorem real_projective_of_fixedUnitary_jordanTable (p : I → E)
    (hp : ∀ i, J.product (p i) (p i) = p i) (s : E) (tr : E →ₗ[ℝ] ℝ)
    (Y : unitary (H →L[ℝ] H)) (P : I → H →L[ℝ] H) (hP : ∀ i, IsStarProjection (P i))
    (X : signedFiniteTrace b) (hX : IsRealDensity b X)
    (hm : ∀ w, signedTrace b (realSandwich b (preTestAmplitude (Y : H →L[ℝ] H) P w) X) =
      tr (J.sequentialBranchState p s w)) :
    ∃ hrot : IsRealDensity b (realSandwich b (Y : H →L[ℝ] H) X), ∀ w,
      (realTraceProjectiveModel b P hP _ hrot).probability w = tr (J.sequentialBranchState p s w) :=
  real_projective_of_fixedUnitary_noSwitch b Y P hP X hX _
    (fun w i a => by rw [J.sequentialBranchState_opposite p hp s w i a, map_zero]) hm

variable (S : RightQuaternionicHilbertStructure H)
local notation "Op" => S.toOperatorStructure.operatorAlgebra
local notation "Carrier" => quaternionicSignedFiniteTrace b S

theorem quaternionic_projective_of_fixedUnitary_jordanTable (p : I → E)
    (hp : ∀ i, J.product (p i) (p i) = p i) (s : E) (tr : E →ₗ[ℝ] ℝ)
    (Y : unitary Op) (P : I → Op) (hP : ∀ i, IsStarProjection (P i))
    (X : Carrier) (hX : IsQuaternionicDensity b S X)
    (hm : ∀ w, quaternionicSignedTrace b S
      (quaternionicSandwich b S (preTestAmplitude (Y : Op) P w) X) = tr (J.sequentialBranchState p s w)) :
    ∃ hrot : IsQuaternionicDensity b S (quaternionicSandwich b S (Y : Op) X), ∀ w,
      let M := quaternionicTraceProjectiveModel b S P hP _ hrot
      M.state (M.wordEffect w) = tr (J.sequentialBranchState p s w) :=
  quaternionic_projective_of_fixedUnitary_noSwitch b S Y P hP X hX _
    (fun w i a => by rw [J.sequentialBranchState_opposite p hp s w i a, map_zero]) hm

end JordanTable

end AlbertSequential.FixedUnitary
