/- SPDX-License-Identifier: Apache-2.0 -/
module

public import MatchingModels.QuatPair
public import MatchingModels.MatrixClassIBridge
public import NativeWordSpan
public import NativePeirceIdentities
import BlockB.StateSupport
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.MatchingModels

open NativeAnalysis
open scoped BigOperators

/-- The round trip through a final affirmative outcome retraces the preceding signed word. -/
def scheduleRoundTrip {ι : Type*} (front : Word ι) (j : ι) : Word ι :=
  front ++ [(j, true)] ++ front.reverse

/-- Rank-one compression at the turn gives the square law from the tracial state. -/
theorem scheduleRoundTrip_probability {ι : Type*} (p : ι → Albert)
    (front : Word ι) (j : ι) (hj : IsAtom (p j)) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (scheduleRoundTrip front j) =
      3 * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (front ++ [(j, true)]) ^ 2 := by
  let x := nativeWordEffect p front.reverse
  have hRev : nativeWordEffect p (front ++ [(j, true)]).reverse = quadraticMap (p j) x := by
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    rfl
  have htrip : nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (scheduleRoundTrip front j) =
      (1 / 3 : ℝ) * tracePairing (quadraticMap (p j) x) x := by
    rw [scheduleRoundTrip, nativeHankel_e3_pairing, hRev]
  have hu : nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (front ++ [(j, true)]) =
      (1 / 3 : ℝ) * tracePairing (p j) x := by
    conv_lhs => rw [← List.append_nil (front ++ [(j, true)]), nativeHankel_e3_pairing, hRev]
    change (1 / 3 : ℝ) * tracePairing (quadraticMap (p j) x) albertUnit = _
    rw [quadraticMap_atom _ _ hj, tracePairing_smul_left, tracePairing_unit_right, hj.2, mul_one]
  rw [htrip, hu, quadraticMap_atom _ _ hj, tracePairing_smul_left]
  ring

private theorem scalar_mixture_eq_of_moments {m : ℕ} (weights x : Fin m → ℝ) (r : ℝ)
    (hw : ∀ k, 0 < weights k) (hnorm : ∑ k, weights k = 1)
    (hfirst : ∑ k, weights k * x k = r)
    (hsecond : ∑ k, weights k * x k ^ 2 = r ^ 2) (k : Fin m) :
    x k = r := by
  have hzero : ∑ j, weights j * (x j - r) ^ 2 = 0 := by
    calc
      _ = (∑ j, weights j * x j ^ 2)
          - (∑ j, weights j * x j) * (2 * r) + (∑ j, weights j) * r ^ 2 := by
        simp only [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 0 := by rw [hsecond, hfirst, hnorm]; ring
  have hsmall : weights k * (x k - r) ^ 2 ≤ 0 := by
    rw [← hzero]
    exact Finset.single_le_sum
      (f := fun j => weights j * (x j - r) ^ 2)
      (fun j _ => mul_nonneg (hw j).le (sq_nonneg _)) (Finset.mem_univ k)
  have heq := le_antisymm hsmall (mul_nonneg (hw k).le (sq_nonneg _))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp heq).resolve_left (ne_of_gt (hw k))))

/-- Matching a word and its round trip forces the word's probability in each positive-weight block. -/
theorem scheduleRoundTrip_mixture_eq {ι : Type*} {m : ℕ}
    (p : ι → Albert) (q : Fin m → ι → Albert) (weights : Fin m → ℝ)
    (hw : ∀ k, 0 < weights k) (hnorm : ∑ k, weights k = 1)
    (front : Word ι) (j : ι) (hp : IsAtom (p j)) (hq : ∀ k, IsAtom (q k j))
    (hword : ∑ k, weights k * nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit)
      (front ++ [(j, true)]) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
      (front ++ [(j, true)]))
    (htrip : ∑ k, weights k * nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit)
      (scheduleRoundTrip front j) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
      (scheduleRoundTrip front j)) (k : Fin m) :
    nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit) (front ++ [(j, true)]) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (front ++ [(j, true)]) := by
  let x := fun k => nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit) (front ++ [(j, true)])
  let r := nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (front ++ [(j, true)])
  have hsecond : ∑ k, weights k * x k ^ 2 = r ^ 2 := by
    simp only [fun a => scheduleRoundTrip_probability (q a) front j (hq a),
      scheduleRoundTrip_probability p front j hp] at htrip
    change (∑ k, weights k * (3 * x k ^ 2)) = 3 * r ^ 2 at htrip
    simp only [show ∀ a b : ℝ, a * (3 * b) = 3 * (a * b) by intro a b; ring,
      ← Finset.mul_sum] at htrip
    linarith
  exact scalar_mixture_eq_of_moments weights x r hw hnorm hword hsecond k

private theorem probability_cons_update {ι : Type*} (p : ι → Albert) (x : Albert)
    (a : Outcome ι) (w : Word ι) :
    nativeWordProbability p x (a :: w) =
      nativeWordProbability p (quadraticMap (nativeOutcome p a) x) w := rfl

private theorem probability_pair (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (i j : Fin 4) :
    3 * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) [(i, true), (j, true)] =
      fpOverlap p i j := by
  rw [BlockB.nativeWordProbability_cons_yes_e3 p i (hp i),
    BlockB.nativeWordProbability_singleton_yes p (p i) j (hp j)]
  unfold fpOverlap
  ring

private theorem probability_triangle (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (i j k : Fin 4) :
    3 * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
        [(i, true), (j, false), (k, true)] =
      fpOverlap p i k - 2 * fpTriangle p i j k + fpOverlap p i j * fpOverlap p j k := by
  rw [BlockB.nativeWordProbability_cons_yes_e3 p i (hp i), probability_cons_update,
    BlockB.nativeWordProbability_singleton_yes p _ k (hp k)]
  change 3 * ((1 / 3 : ℝ) * tracePairing (quadraticMap (albertUnit - p j) (p i)) (p k)) = _
  rw [quadraticMap_complement, quadraticMap_atom _ _ (hp j)]
  simp only [tracePairing_add_left, tracePairing_sub_left, tracePairing_smul_left,
    jordanMul_comm (p j) (p i), tracePairing_comm (p j) (p i), fpTriangle, fpOverlap]
  ring

/-- The only length-four trace in the signed word is the indicated double-pair trace. -/
theorem schedule_signed_four_probability (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (i j k l : Fin 4) :
    3 * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
        [(i, true), (j, false), (k, false), (l, true)] =
      4 * tracePairing (jordanMul (p i) (p j)) (jordanMul (p k) (p l)) +
        (fpOverlap p i l - 2 * fpTriangle p i j l + fpOverlap p j i * fpOverlap p j l
          - 2 * fpTriangle p k i l - 2 * fpOverlap p j i * fpTriangle p k j l
          + fpOverlap p k i * fpOverlap p k l - 2 * fpTriangle p j i k * fpOverlap p k l
          + fpOverlap p j i * fpOverlap p k j * fpOverlap p k l) := by
  rw [BlockB.nativeWordProbability_cons_yes_e3 p i (hp i),
    probability_cons_update, probability_cons_update,
    BlockB.nativeWordProbability_singleton_yes p _ l (hp l)]
  change 3 * ((1 / 3 : ℝ) * tracePairing
    (quadraticMap (albertUnit - p k) (quadraticMap (albertUnit - p j) (p i))) (p l)) = _
  rw [quadraticMap_complement (p j), quadraticMap_complement (p k),
    quadraticMap_atom _ _ (hp j), quadraticMap_atom _ _ (hp k)]
  simp only [tracePairing_add_left, tracePairing_sub_left, tracePairing_smul_left,
    tracePairing_add_right, tracePairing_sub_right, tracePairing_smul_right,
    jordanMul_add_right, jordanMul_sub_right, jordanMul_smul_right]
  have hpair : tracePairing (jordanMul (p k) (jordanMul (p j) (p i))) (p l) =
      tracePairing (jordanMul (p i) (p j)) (jordanMul (p k) (p l)) := by
    rw [jordanMul_comm (p k), tracePairing_associative, jordanMul_comm (p j) (p i)]
  rw [hpair, tracePairing_comm (p k) (jordanMul (p j) (p i))]
  -- Keep the repeated-index case as well: the identities used here apply to all indices.
  simp only [fpTriangle, fpOverlap]
  rw [jordanMul_comm (p j) (p i)]
  ring

/-- The first seven-letter word of Proposition 6.13(b). -/
def scheduleFirstRoundTrip : Word (Fin 4) :=
  scheduleRoundTrip [(0, true), (2, false), (1, false)] 3

/-- The second seven-letter word of Proposition 6.13(b). -/
def scheduleSecondRoundTrip : Word (Fin 4) :=
  scheduleRoundTrip [(0, true), (1, false), (2, false)] 3

/-- Finite normalized positive-weight mixtures of quaternionic tracial blocks cannot
match every signed word through length five and the two specified round trips. -/
theorem prop_cer_schedule_b_native {m : ℕ} (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (q : Fin m → Fin 4 → Albert) (Q : Fin m → QuaternionicWindow) (weights : Fin m → ℝ)
    (hq : ∀ k i, IsAtom (q k i)) (hmem : ∀ k i, q k i ∈ (Q k).subalgebra.carrier)
    (hw : ∀ k, 0 < weights k) (hnorm : ∑ k, weights k = 1) :
    ¬ (∀ w : Word (Fin 4), w.length ≤ 5 ∨ w = scheduleFirstRoundTrip ∨ w = scheduleSecondRoundTrip →
        ∑ k, weights k * nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit) w =
          nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) := by
  intro hmatch
  have hm : m ≠ 0 := by
    intro hm
    subst m
    simp at hnorm
  let k : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  have hblock (front : Word (Fin 4)) (j : Fin 4) (hlen : front.length + 1 ≤ 5)
      (htrip : (scheduleRoundTrip front j).length ≤ 5 ∨
        scheduleRoundTrip front j = scheduleFirstRoundTrip ∨
        scheduleRoundTrip front j = scheduleSecondRoundTrip) :
      nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit) (front ++ [(j, true)]) =
        nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) (front ++ [(j, true)]) :=
    scheduleRoundTrip_mixture_eq p q weights hw hnorm front j (hp j) (fun k => hq k j)
      (hmatch _ (.inl (by simpa using hlen))) (hmatch _ htrip) k
  have ho (i j : Fin 4) : fpOverlap (q k) i j = fpOverlap p i j := by
    have he := hblock [(i, true)] j (by simp) (.inl (by simp [scheduleRoundTrip]))
    rw [← probability_pair _ (hq k) i j, ← probability_pair _ hp i j]
    exact congrArg (fun x : ℝ => 3 * x) he
  have hR (i j l : Fin 4) : fpTriangle (q k) i j l = fpTriangle p i j l := by
    have he := congrArg (fun x : ℝ => 3 * x) (hblock [(i, true), (j, false)] l
      (by simp) (.inl (by simp [scheduleRoundTrip])))
    change 3 * nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit)
        [(i, true), (j, false), (l, true)] =
      3 * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
        [(i, true), (j, false), (l, true)] at he
    rw [probability_triangle _ (hq k), probability_triangle _ hp] at he
    simp only [ho] at he
    linarith
  have ht1 : fpDoublePair1 (q k) = fpDoublePair1 p := by
    have he := congrArg (fun x : ℝ => 3 * x) (hblock [(0, true), (1, false), (2, false)] 3
      (by decide) (.inr (.inr rfl)))
    change 3 * nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit)
        [(0, true), (1, false), (2, false), (3, true)] =
      3 * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
        [(0, true), (1, false), (2, false), (3, true)] at he
    rw [schedule_signed_four_probability _ (hq k), schedule_signed_four_probability _ hp] at he
    simp only [ho, hR] at he
    change 4 * fpDoublePair1 (q k) + _ = 4 * fpDoublePair1 p + _ at he
    linarith
  have ht2 : fpDoublePair2 (q k) = fpDoublePair2 p := by
    have he := congrArg (fun x : ℝ => 3 * x) (hblock [(0, true), (2, false), (1, false)] 3
      (by decide) (.inr (.inl rfl)))
    change 3 * nativeWordProbability (q k) ((1 / 3 : ℝ) • albertUnit)
        [(0, true), (2, false), (1, false), (3, true)] =
      3 * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)
        [(0, true), (2, false), (1, false), (3, true)] at he
    rw [schedule_signed_four_probability _ (hq k), schedule_signed_four_probability _ hp] at he
    simp only [ho, hR] at he
    change 4 * fpDoublePair2 (q k) + _ = 4 * fpDoublePair2 p + _ at he
    linarith
  have ht3 : fpDoublePair3 (q k) = fpDoublePair3 p := by
    have hqRel := tVec_mem_planePi (q k) (hq k)
    have hpRel := tVec_mem_planePi p hp
    change fpDoublePair1 (q k) + fpDoublePair2 (q k) + fpDoublePair3 (q k) =
      tauOf (fpOverlap (q k)) (fpTriangle (q k)) at hqRel
    change fpDoublePair1 p + fpDoublePair2 p + fpDoublePair3 p =
      tauOf (fpOverlap p) (fpTriangle p) at hpRel
    simp only [ht1, ht2, tauOf, ho, hR] at hqRel
    unfold tauOf at hpRel
    linarith
  have hAp : fourPointInvariant (q k) = fourPointInvariant p := by
    simp only [fourPointInvariant, fpOmega1, fpOmega2, fpOmega3, ho, hR, ht1, ht2, ht3]
  have hzero := (fourPointInvariant_eq_zero_iff (q k) (hq k)).2 ⟨Q k, hmem k⟩
  linarith

/-- Proposition 6.13(b) for the standard C6 representations with state Tr/6. -/
theorem prop_cer_schedule_b {m : ℕ} (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (q : Fin m → Fin 4 → Albert) (Q : Fin m → QuaternionicWindow) (weights : Fin m → ℝ)
    (hq : ∀ k i, IsAtom (q k i)) (hmem : ∀ k i, q k i ∈ (Q k).subalgebra.carrier)
    (hw : ∀ k, 0 < weights k) (hnorm : ∑ k, weights k = 1) :
    ¬ (∀ w : Word (Fin 4), w.length ≤ 5 ∨ w = scheduleFirstRoundTrip ∨ w = scheduleSecondRoundTrip →
      ∑ k, weights k * ((1 / 6 : ℝ) *
        (Matrix.trace (wordOperator (quatProj6 (Q k) (q k) (hmem k)) w)).re) =
        nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) := by
  intro h
  apply prop_cer_schedule_b_native p hp hA q Q weights hq hmem hw hnorm
  intro w hwrd
  simpa only [fun k => quatProj6_wordProb_e3 (Q k) (q k) (hmem k) w] using h w hwrd

end AlbertSequential.MatchingModels
