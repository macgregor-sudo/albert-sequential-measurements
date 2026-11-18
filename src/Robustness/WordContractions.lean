module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Linarith

/-! Dimension- and field-independent word telescopes. The generic hypotheses
are explicit; actual R/C/H operator, trace-class and spectral bindings remain
separate. Chronological words always apply their first letter first.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

def chronologicalProduct {A I : Type*} [Mul A] [One A]
    (a : I → A) (w : List I) : A := w.foldl (fun x i => a i * x) 1

theorem chronologicalProduct_append_singleton {A I : Type*} [Mul A] [One A]
    (a : I → A) (w : List I) (i : I) :
    chronologicalProduct a (w ++ [i]) = a i * chronologicalProduct a w := by
  simp only [chronologicalProduct, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem norm_chronologicalProduct_le_one {A I : Type*} [NormedRing A]
    (hunit : ‖(1 : A)‖ ≤ 1) (a : I → A) (ha : ∀ i, ‖a i‖ ≤ 1) (w : List I) :
    ‖chronologicalProduct a w‖ ≤ 1 := by
  induction w using List.reverseRecOn with
  | nil => exact hunit
  | append_singleton w i ih =>
      rw [chronologicalProduct_append_singleton]
      exact (norm_mul_le _ _).trans ((mul_le_mul (ha i) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem norm_chronologicalProduct_sub_le {A I : Type*} [NormedRing A]
    (hunit : ‖(1 : A)‖ ≤ 1) (a b : I → A)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hab : ∀ i, ‖a i - b i‖ ≤ epsilon)
    (w : List I) :
    ‖chronologicalProduct a w - chronologicalProduct b w‖ ≤ (w.length : ℝ) * epsilon := by
  induction w using List.reverseRecOn with
  | nil => simp [chronologicalProduct]
  | append_singleton w i ih =>
      rw [chronologicalProduct_append_singleton, chronologicalProduct_append_singleton]
      have hB := norm_chronologicalProduct_le_one hunit b hb w
      have hid : a i * chronologicalProduct a w - b i * chronologicalProduct b w =
          a i * (chronologicalProduct a w - chronologicalProduct b w) +
            (a i - b i) * chronologicalProduct b w := by noncomm_ring
      rw [hid]
      calc
        _ ≤ ‖a i * (chronologicalProduct a w - chronologicalProduct b w)‖ +
              ‖(a i - b i) * chronologicalProduct b w‖ := norm_add_le _ _
        _ ≤ ‖a i‖ * ‖chronologicalProduct a w - chronologicalProduct b w‖ +
              ‖a i - b i‖ * ‖chronologicalProduct b w‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * ((w.length : ℝ) * epsilon) + epsilon * 1 := by
          exact add_le_add (mul_le_mul (ha i) ih (norm_nonneg _) zero_le_one)
            (mul_le_mul (hab i) hB (norm_nonneg _) hepsilon)
        _ = ((w ++ [i]).length : ℝ) * epsilon := by simp; ring

def chronologicalState {E I : Type*} (f : I → E → E) (x : E) (w : List I) : E :=
  w.foldl (fun y i => f i y) x

theorem chronologicalState_append_singleton {E I : Type*}
    (f : I → E → E) (x : E) (w : List I) (i : I) :
    chronologicalState f x (w ++ [i]) = f i (chronologicalState f x w) := by
  simp only [chronologicalState, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem chronologicalState_mem {E I : Type*} (C : Set E) (g : I → E → E)
    (hg : ∀ i y, y ∈ C → g i y ∈ C) {x : E} (hx : x ∈ C) (w : List I) :
    chronologicalState g x w ∈ C := by
  induction w using List.reverseRecOn with
  | nil => exact hx
  | append_singleton w i ih =>
      simpa only [chronologicalState_append_singleton] using hg i _ ih

theorem norm_chronologicalState_sub_le {E I : Type*} [NormedAddCommGroup E]
    (C : Set E) (f g : I → E → E)
    (hf : ∀ i x y, ‖f i x - f i y‖ ≤ ‖x - y‖)
    (hg : ∀ i y, y ∈ C → g i y ∈ C)
    {beta : ℝ} (_hbeta : 0 ≤ beta) (hfg : ∀ i y, y ∈ C → ‖f i y - g i y‖ ≤ beta)
    {x : E} (hx : x ∈ C) (w : List I) :
    ‖chronologicalState f x w - chronologicalState g x w‖ ≤ (w.length : ℝ) * beta := by
  induction w using List.reverseRecOn with
  | nil => simp [chronologicalState]
  | append_singleton w i ih =>
      rw [chronologicalState_append_singleton, chronologicalState_append_singleton]
      have hc := chronologicalState_mem C g hg hx w
      calc
        _ ≤ ‖f i (chronologicalState f x w) - f i (chronologicalState g x w)‖ +
              ‖f i (chronologicalState g x w) - g i (chronologicalState g x w)‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (f i (chronologicalState f x w)) (f i (chronologicalState g x w))
            (g i (chronologicalState g x w))
        _ ≤ ‖chronologicalState f x w - chronologicalState g x w‖ + beta :=
          add_le_add (hf i _ _) (hfg i _ hc)
        _ ≤ (w.length : ℝ) * beta + beta := add_le_add ih (le_refl beta)
        _ = ((w ++ [i]).length : ℝ) * beta := by simp; ring

end AlbertSequential
