/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WordAmplitudeCombinations
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Ring.List

/-! Existing real word functionals, with explicit finite constructors and a
canonical merged coefficient norm. Duplicate list terms are added first. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
namespace FiniteRealWordFunctional
variable {n : ℕ}

def scale (a : ℝ) (c : FiniteRealWordFunctional n) : FiniteRealWordFunctional n where
  terms := c.terms.map (fun t => (a * t.1, t.2))

def append (c d : FiniteRealWordFunctional n) : FiniteRealWordFunctional n where
  terms := c.terms ++ d.terms

def combine (cs : List (FiniteRealWordFunctional n)) : FiniteRealWordFunctional n where
  terms := cs.flatMap (fun c => c.terms)

def emptyWordTerm (a : ℝ) : FiniteRealWordFunctional n where
  terms := [(a, [])]

theorem evaluate_scale (a : ℝ) (c : FiniteRealWordFunctional n) (f : Word (Fin n) → ℝ) :
    (scale a c).evaluate f = a * c.evaluate f := by
  simp only [scale, evaluate, List.map_map, Function.comp_def, mul_assoc,
    List.sum_map_mul_left]

theorem evaluate_append (c d : FiniteRealWordFunctional n) (f : Word (Fin n) → ℝ) :
    (append c d).evaluate f = c.evaluate f + d.evaluate f := by
  simp only [append, evaluate, List.map_append, List.sum_append]

theorem evaluate_combine (cs : List (FiniteRealWordFunctional n)) (f : Word (Fin n) → ℝ) :
    (combine cs).evaluate f = (cs.map (fun c => c.evaluate f)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      change (append c (combine cs)).evaluate f = _
      rw [evaluate_append, ih]
      rfl

theorem evaluate_emptyWordTerm (a : ℝ) (f : Word (Fin n) → ℝ) :
    (emptyWordTerm a).evaluate f = a * f [] := by
  simp only [emptyWordTerm, evaluate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem hasHorizon_scale (a : ℝ) (c : FiniteRealWordFunctional n) (L : ℕ)
    (h : c.HasHorizon L) : (scale a c).HasHorizon L := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact h u hu

theorem hasHorizon_append (c d : FiniteRealWordFunctional n) (L : ℕ)
    (hc : c.HasHorizon L) (hd : d.HasHorizon L) : (append c d).HasHorizon L := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hc t h
  · exact hd t h

theorem hasHorizon_combine (cs : List (FiniteRealWordFunctional n)) (L : ℕ)
    (h : ∀ c ∈ cs, c.HasHorizon L) : (combine cs).HasHorizon L := by
  intro t ht
  rcases List.mem_flatMap.mp ht with ⟨c, hc, ht⟩
  exact h c hc t ht

theorem hasHorizon_emptyWordTerm (a : ℝ) (L : ℕ) :
    (emptyWordTerm a : FiniteRealWordFunctional n).HasHorizon L := by
  intro t ht
  have h : t = (a, []) := List.mem_singleton.mp ht
  rw [h]
  exact Nat.zero_le L

theorem rawCoefficientBound_scale (a : ℝ) (c : FiniteRealWordFunctional n) :
    (scale a c).rawCoefficientBound = |a| * c.rawCoefficientBound := by
  simp only [rawCoefficientBound, wordAmplitudeCoefficientBound, scale,
    List.map_map, Function.comp_def, abs_mul, List.sum_map_mul_left]

theorem rawCoefficientBound_append (c d : FiniteRealWordFunctional n) :
    (append c d).rawCoefficientBound = c.rawCoefficientBound + d.rawCoefficientBound := by
  simp only [rawCoefficientBound, wordAmplitudeCoefficientBound, append,
    List.map_append, List.sum_append]

theorem rawCoefficientBound_combine (cs : List (FiniteRealWordFunctional n)) :
    (combine cs).rawCoefficientBound = (cs.map rawCoefficientBound).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      change (append c (combine cs)).rawCoefficientBound = _
      rw [rawCoefficientBound_append, ih]
      rfl

theorem rawCoefficientBound_emptyWordTerm (a : ℝ) :
    (emptyWordTerm a : FiniteRealWordFunctional n).rawCoefficientBound = |a| := by
  simp only [rawCoefficientBound, wordAmplitudeCoefficientBound, emptyWordTerm,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

def coefficientsOfTerms (ts : List (ℝ × Word (Fin n))) : Word (Fin n) →₀ ℝ :=
  (ts.map (fun t => Finsupp.single t.2 t.1)).sum

def coefficients (c : FiniteRealWordFunctional n) : Word (Fin n) →₀ ℝ :=
  coefficientsOfTerms c.terms

def coefficientAbsSum (f : Word (Fin n) →₀ ℝ) : ℝ := f.sum (fun _ a => |a|)

/-- Sum of absolute coefficients after combining all coincident words. -/
def coefficientNorm (c : FiniteRealWordFunctional n) : ℝ := coefficientAbsSum c.coefficients

theorem coefficientsOfTerms_nil : coefficientsOfTerms ([] : List (ℝ × Word (Fin n))) = 0 := rfl

theorem coefficientsOfTerms_cons (r : ℝ) (w : Word (Fin n)) (ts : List (ℝ × Word (Fin n))) :
    coefficientsOfTerms ((r, w) :: ts) = Finsupp.single w r + coefficientsOfTerms ts := rfl

theorem evaluateTerms_eq_coefficients (ts : List (ℝ × Word (Fin n))) (f : Word (Fin n) → ℝ) :
    (ts.map (fun t => t.1 * f t.2)).sum =
      (coefficientsOfTerms ts).sum (fun w a => a * f w) := by
  induction ts with
  | nil => simp only [List.map_nil, List.sum_nil, coefficientsOfTerms_nil, Finsupp.sum_zero_index]
  | cons t ts ih =>
      rcases t with ⟨r, w⟩
      rw [coefficientsOfTerms_cons]
      rw [Finsupp.sum_add_index' (h := fun w a => a * f w)
        (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
      rw [Finsupp.sum_single_index (h := fun w a => a * f w) (zero_mul _)]
      simp only [List.map_cons, List.sum_cons, ih]

theorem evaluate_eq_coefficients (c : FiniteRealWordFunctional n) (f : Word (Fin n) → ℝ) :
    c.evaluate f = c.coefficients.sum (fun w a => a * f w) :=
  evaluateTerms_eq_coefficients c.terms f

theorem coefficientAbsSum_add_le (f g : Word (Fin n) →₀ ℝ) :
    coefficientAbsSum (f + g) ≤ coefficientAbsSum f + coefficientAbsSum g := by
  classical
  have enlarge (h : Word (Fin n) →₀ ℝ) (s : Finset (Word (Fin n)))
      (hs : h.support ⊆ s) : coefficientAbsSum h = ∑ w ∈ s, |h w| :=
    Finsupp.sum_of_support_subset h hs (fun _ a => |a|) (fun _ _ => abs_zero)
  rw [enlarge (f + g) (f.support ∪ g.support) Finsupp.support_add]
  calc
    (∑ w ∈ f.support ∪ g.support, |(f + g) w|) ≤
        ∑ w ∈ f.support ∪ g.support, (|f w| + |g w|) := by
      exact Finset.sum_le_sum (fun _ _ => abs_add_le _ _)
    _ = coefficientAbsSum f + coefficientAbsSum g := by
      rw [Finset.sum_add_distrib, ← enlarge f _ Finset.subset_union_left,
        ← enlarge g _ Finset.subset_union_right]

theorem coefficientAbsSum_single (w : Word (Fin n)) (r : ℝ) :
    coefficientAbsSum (Finsupp.single w r) = |r| :=
  Finsupp.sum_single_index (h := fun _ a => |a|) abs_zero

theorem coefficientAbsSum_terms_le (ts : List (ℝ × Word (Fin n))) :
    coefficientAbsSum (coefficientsOfTerms ts) ≤ wordAmplitudeCoefficientBound ts := by
  induction ts with
  | nil => simp only [coefficientsOfTerms_nil, coefficientAbsSum,
      Finsupp.sum_zero_index, wordAmplitudeCoefficientBound_nil, le_refl]
  | cons t ts ih =>
      rcases t with ⟨r, w⟩
      rw [coefficientsOfTerms_cons, wordAmplitudeCoefficientBound_cons]
      exact (coefficientAbsSum_add_le _ _).trans (add_le_add (le_of_eq (coefficientAbsSum_single w r)) ih)

theorem coefficientNorm_le_rawCoefficientBound (c : FiniteRealWordFunctional n) :
    c.coefficientNorm ≤ c.rawCoefficientBound := coefficientAbsSum_terms_le c.terms

theorem coefficientNorm_nonneg (c : FiniteRealWordFunctional n) : 0 ≤ c.coefficientNorm := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem coefficientsOfTerms_apply_eq_zero_of_absent (ts : List (ℝ × Word (Fin n)))
    (w : Word (Fin n)) (h : ∀ t ∈ ts, t.2 ≠ w) : coefficientsOfTerms ts w = 0 := by
  classical
  induction ts with
  | nil => simp only [coefficientsOfTerms_nil, Finsupp.zero_apply]
  | cons t ts ih =>
      rw [coefficientsOfTerms_cons, Finsupp.add_apply,
        ih (fun u hu => h u (List.mem_cons_of_mem _ hu)), add_zero]
      exact Finsupp.single_eq_of_ne (h t List.mem_cons_self).symm

theorem coefficient_support_hasHorizon (c : FiniteRealWordFunctional n) (L : ℕ)
    (h : c.HasHorizon L) : ∀ w ∈ c.coefficients.support, w.length ≤ L := by
  classical
  intro w hw
  by_contra hlen
  have hzero : c.coefficients w = 0 := by
    apply coefficientsOfTerms_apply_eq_zero_of_absent
    intro t ht heq
    exact hlen (heq ▸ h t ht)
  exact (Finsupp.mem_support_iff.mp hw) hzero

theorem evaluate_error_bound (c : FiniteRealWordFunctional n) (f g : Word (Fin n) → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (h : ∀ w ∈ c.coefficients.support, |f w - g w| ≤ ε) :
    |c.evaluate f - c.evaluate g| ≤ c.coefficientNorm * ε := by
  classical
  rw [evaluate_eq_coefficients, evaluate_eq_coefficients]
  change |(∑ w ∈ c.coefficients.support, c.coefficients w * f w) -
      (∑ w ∈ c.coefficients.support, c.coefficients w * g w)| ≤
    (∑ w ∈ c.coefficients.support, |c.coefficients w|) * ε
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ w ∈ c.coefficients.support, (c.coefficients w * f w - c.coefficients w * g w)| ≤
        ∑ w ∈ c.coefficients.support, |c.coefficients w * f w - c.coefficients w * g w| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w ∈ c.coefficients.support, |c.coefficients w| * |f w - g w| := by
      simp only [← mul_sub, abs_mul]
    _ ≤ ∑ w ∈ c.coefficients.support, |c.coefficients w| * ε :=
      Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_left (h w hw) (abs_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

theorem separation_forces_error (c : FiniteRealWordFunctional n) (f g : Word (Fin n) → ℝ)
    (ε γ : ℝ) (hε : 0 ≤ ε)
    (h : ∀ w ∈ c.coefficients.support, |f w - g w| ≤ ε)
    (hmodel : 0 ≤ c.evaluate f) (htarget : c.evaluate g ≤ -γ) :
    γ ≤ c.coefficientNorm * ε := by
  calc
    γ ≤ c.evaluate f - c.evaluate g := by linarith
    _ ≤ |c.evaluate f - c.evaluate g| := le_abs_self _
    _ ≤ _ := evaluate_error_bound c f g ε hε h

theorem evaluate_error_bound_of_horizon (c : FiniteRealWordFunctional n)
    (L : ℕ) (hL : c.HasHorizon L) (f g : Word (Fin n) → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ w, w.length ≤ L → |f w - g w| ≤ ε) :
    |c.evaluate f - c.evaluate g| ≤ c.coefficientNorm * ε := by
  exact c.evaluate_error_bound f g ε hε
    (fun w hw => h w (c.coefficient_support_hasHorizon L hL w hw))

end FiniteRealWordFunctional
end AlbertSequential
