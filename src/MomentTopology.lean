/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.SeparationAndConverse
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.BigOperators.Ring.List

/-! Topology of the exact projection-moment domain. This module constructs no
representation and assumes no matching or no-go theorem. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

private theorem continuous_finite_sum {X α : Type*} [TopologicalSpace X]
    (l : List α) (f : α → X → ℝ) (hf : ∀ x, Continuous (f x)) :
    Continuous (fun z => (l.map (fun x => f x z)).sum) := by
  induction l with
  | nil => simpa using (continuous_const : Continuous (fun _ : X => (0 : ℝ)))
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact continuous_add.comp ((hf x).prodMk ih)

private theorem finite_sum_combination {X α : Type*} [AddCommMonoid X] [Module ℝ X]
    (l : List α) (f : α → X → ℝ) (a b : ℝ) (x y : X)
    (hf : ∀ t, f t (a • x + b • y) = a * f t x + b * f t y) :
    (l.map (fun t => f t (a • x + b • y))).sum =
      a * (l.map (fun t => f t x)).sum + b * (l.map (fun t => f t y)).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hf, ih]
    ring

/-- The exact polynomial-square expression in the shared admissibility definition. -/
def projectionMomentSquare {n : ℕ} (m : ProjectionMoments n)
    (c : ProjectionPolynomial n) : ℝ :=
  (c.map (fun a => (c.map (fun b =>
    a.1 * b.1 * m (a.2.reverse ++ b.2))).sum)).sum

theorem continuous_projectionMomentSquare {n : ℕ} (c : ProjectionPolynomial n) :
    Continuous (fun m : ProjectionMoments n => projectionMomentSquare m c) := by
  apply continuous_finite_sum
  intro a
  apply continuous_finite_sum
  intro b
  exact continuous_const.mul (continuous_apply _)

theorem projectionMomentSquare_combination {n : ℕ} (c : ProjectionPolynomial n)
    (a b : ℝ) (m k : ProjectionMoments n) :
    projectionMomentSquare (a • m + b • k) c =
      a * projectionMomentSquare m c + b * projectionMomentSquare k c := by
  unfold projectionMomentSquare
  apply finite_sum_combination c
    (fun x m => (c.map (fun y => x.1 * y.1 * m (x.2.reverse ++ y.2))).sum) a b m k
  intro x
  apply finite_sum_combination c (fun y m => x.1 * y.1 * m (x.2.reverse ++ y.2)) a b m k
  intro y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_polynomialMoment {n : ℕ} (c : ProjectionPolynomial n) :
    Continuous (fun m : ProjectionMoments n => polynomialMoment m c) := by
  apply continuous_finite_sum
  intro a
  exact continuous_const.mul (continuous_apply _)

theorem polynomialMoment_combination {n : ℕ} (c : ProjectionPolynomial n)
    (a b : ℝ) (m k : ProjectionMoments n) :
    polynomialMoment (a • m + b • k) c =
      a * polynomialMoment m c + b * polynomialMoment k c := by
  unfold polynomialMoment
  apply finite_sum_combination c (fun x m => x.1 * m x.2) a b m k
  intro x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_momentWordProbability {n : ℕ} (w : Word (Fin n)) :
    Continuous (fun m : ProjectionMoments n => momentWordProbability m w) :=
  continuous_polynomialMoment (effectPolynomial w)

private theorem admissibleProjectionMoments_iff {n : ℕ} (m : ProjectionMoments n) :
    AdmissibleProjectionMoments n m ↔
      m [] = 1 ∧ (∀ w, m w.reverse = m w) ∧
      (∀ u v i, m (u ++ [i, i] ++ v) = m (u ++ [i] ++ v)) ∧
      (∀ c, 0 ≤ projectionMomentSquare m c) ∧
      (∀ w, -1 ≤ m w ∧ m w ≤ 1) := by
  constructor
  · intro h
    exact ⟨h.normalized, h.reversal, h.idempotent_context,
      h.positive_polynomial_squares, h.bounded⟩
  · rintro ⟨h0, hr, hi, hp, hb⟩
    exact ⟨h0, hr, hi, hp, hb⟩

theorem isClosed_projectionMomentDomain (n : ℕ) :
    IsClosed (projectionMomentDomain n) := by
  change IsClosed {m : ProjectionMoments n | AdmissibleProjectionMoments n m}
  simp_rw [admissibleProjectionMoments_iff]
  simp only [Set.ofPred_and]
  refine (isClosed_eq (continuous_apply []) continuous_const).inter ?_
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · change IsClosed {m : ProjectionMoments n | ∀ w, m w.reverse = m w}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun w => isClosed_eq (continuous_apply _) (continuous_apply _)
  · change IsClosed {m : ProjectionMoments n |
      ∀ u v i, m (u ++ [i, i] ++ v) = m (u ++ [i] ++ v)}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u => isClosed_iInter fun v => isClosed_iInter fun i =>
      isClosed_eq (continuous_apply _) (continuous_apply _)
  · change IsClosed {m : ProjectionMoments n | ∀ c, 0 ≤ projectionMomentSquare m c}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun c =>
      isClosed_le continuous_const (continuous_projectionMomentSquare c)
  · change IsClosed {m : ProjectionMoments n | ∀ w, -1 ≤ m w ∧ m w ≤ 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun w =>
      (isClosed_le continuous_const (continuous_apply w)).inter
        (isClosed_le (continuous_apply w) continuous_const)

theorem isCompact_projectionMomentDomain (n : ℕ) :
    IsCompact (projectionMomentDomain n) := by
  have hbox : IsCompact (Set.pi Set.univ
      (fun _ : ProjectionMonomial n => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset (isClosed_projectionMomentDomain n)
  intro m hm w _
  exact hm.bounded w

theorem convex_projectionMomentDomain (n : ℕ) :
    Convex ℝ (projectionMomentDomain n) := by
  intro m hm k hk a b ha hb hab
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm.normalized,
      hk.normalized, mul_one]
    exact hab
  · intro w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm.reversal, hk.reversal]
  · intro u v i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hm.idempotent_context, hk.idempotent_context]
  · intro c
    change 0 ≤ projectionMomentSquare (a • m + b • k) c
    rw [projectionMomentSquare_combination]
    exact add_nonneg (mul_nonneg ha (hm.positive_polynomial_squares c))
      (mul_nonneg hb (hk.positive_polynomial_squares c))
  · intro w
    change -1 ≤ a * m w + b * k w ∧ a * m w + b * k w ≤ 1
    have hmlo := mul_le_mul_of_nonneg_left (hm.bounded w).1 ha
    have hklo := mul_le_mul_of_nonneg_left (hk.bounded w).1 hb
    have hmhi := mul_le_mul_of_nonneg_left (hm.bounded w).2 ha
    have hkhi := mul_le_mul_of_nonneg_left (hk.bounded w).2 hb
    constructor <;> nlinarith

/-- All three fields are proved for the current, untruncated moment domain. -/
theorem momentDomainTopology (n : ℕ) : MomentDomainTopology n :=
  ⟨isCompact_projectionMomentDomain n, convex_projectionMomentDomain n,
    continuous_momentWordProbability⟩

/-- All generators represented by the identity give a genuine point of the
domain, also when there are no generators. -/
theorem constantOne_projectionMoments (n : ℕ) :
    AdmissibleProjectionMoments n (fun _ => 1) := by
  constructor
  · rfl
  · intro w; rfl
  · intro u v i; rfl
  · intro c
    simpa only [mul_one, List.sum_map_mul_left, List.sum_map_mul_right, pow_two]
      using sq_nonneg ((c.map Prod.fst).sum)
  · intro w; norm_num

theorem projectionMomentDomain_nonempty (n : ℕ) :
    (projectionMomentDomain n).Nonempty :=
  ⟨fun _ => 1, constantOne_projectionMoments n⟩

end AlbertSequential
