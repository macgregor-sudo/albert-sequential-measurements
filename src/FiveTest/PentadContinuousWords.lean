/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.PentadPeirceAction
public import Mathlib.Algebra.Polynomial.Degree.Defs
import NativePeirceIdentities
import NativeWordDuality

@[expose] public section

namespace AlbertSequential.FiveTest

open MatchingModels NativeAnalysis Polynomial

noncomputable section

/-- The chronological probability polynomial from a connected-history state.
Each rank-one update resets the history to the just-measured atom. -/
def pentadWordPolynomial : Word (Fin 5) → List (Fin 5) → Polynomial ℚ
  | [], L => pentadConnectedTracePolynomial L
  | (r,b) :: w, L =>
    let reset := pentadConnectedTracePolynomial (r :: L) * pentadWordPolynomial w [r]
    if b then reset else
      pentadWordPolynomial w L + C (-2) * pentadWordPolynomial w (r :: L) + reset

private theorem nativeWord_cons (F : Fin 5 → Albert) (ρ : Albert) (a : Outcome (Fin 5))
    (w : Word (Fin 5)) :
    nativeWordProbability F ρ (a :: w) =
      nativeWordProbability F (quadraticMap (nativeOutcome F a) ρ) w := rfl

theorem continuousPentad_connectedWord (u : Octonion) (hu : octNormSq u = 1)
    (hre : octonionReal u = 0) (hI : octDot u octI = 0) (hJ : octDot u octJ = 0)
    (w : Word (Fin 5)) (L : List (Fin 5)) :
    nativeWordProbability (continuousPentad u) (pentadChain (continuousPentad u) L) w =
      parameterEval (octDot u octK) (pentadWordPolynomial w L) := by
  let F := continuousPentad u
  let e := parameterEval (octDot u octK)
  induction w generalizing L with
  | nil => exact continuousPentad_connectedTrace u hu hre hI hJ L
  | cons a w ih =>
    obtain ⟨r,b⟩ := a
    let ρ := pentadChain F L
    have htr : tracePairing (F r) ρ = e (pentadConnectedTracePolynomial (r :: L)) :=
      continuousPentad_connectedTrace u hu hre hI hJ (r :: L)
    have hsingle : pentadChain F [r] = F r := jordanMul_albertUnit_right _
    have hmem : IsAtom (F r) := continuousPentad_isAtom u hu r
    have hreset : nativeWordProbability F (quadraticMap (F r) ρ) w =
        e (pentadConnectedTracePolynomial (r :: L) * pentadWordPolynomial w [r]) := by
      rw [quadraticMap_atom _ _ hmem, nativeWordProbability_smul, htr, ← hsingle, ih, map_mul]
    cases b
    · change nativeWordProbability F ρ ((r,false) :: w) = _
      rw [nativeWord_cons, show nativeOutcome F (r,false) = albertUnit - F r from rfl,
        quadraticMap_complement, sub_eq_add_neg, ← neg_smul,
        nativeWordProbability_add, nativeWordProbability_add, nativeWordProbability_smul, hreset]
      have hL : jordanMul (F r) ρ = pentadChain F (r :: L) := rfl
      rw [hL]
      change nativeWordProbability F (pentadChain F L) w + (-2 : ℝ) *
        nativeWordProbability F (pentadChain F (r :: L)) w + _ = _
      rw [ih, ih]
      simp [pentadWordPolynomial, e, parameterEval]
    · change nativeWordProbability F ρ ((r,true) :: w) = _
      rw [nativeWord_cons, show nativeOutcome F (r,true) = F r from rfl, hreset]
      rfl

theorem pentadConnectedTracePolynomial_degree (L : List (Fin 5)) {n : ℕ}
    (h : L.length < 6*(n+1)) :
    (pentadConnectedTracePolynomial L).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro d hd
  by_contra hn
  have hf := pentadConnectedTracePolynomial_coeff_length L hn
  omega

private theorem tracePolynomial_topCoefficient (L : List (Fin 5))
    (h : pentadConnectedTracePolynomial L ≠ 0) :
    (pentadConnectedTracePolynomial L).coeff (pentadConnectedTracePolynomial L).natDegree ≠ 0 := by
  rw [coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr h

/-- The continuous connected trace has a native polynomial with every
occurrence and length restriction stated in the deposited proof. -/
theorem continuousPentad_connectedTrace_degree_bounds (L : List (Fin 5)) :
    ∃ p : Polynomial ℚ,
      (∀ a : Fin 5, a ≠ 2 → p.natDegree ≤ L.count a) ∧
      2 * p.natDegree ≤ L.count (2 : Fin 5) ∧
      6 * p.natDegree ≤ L.length ∧
      (∀ u : Octonion, octNormSq u = 1 → octonionReal u = 0 →
        octDot u octI = 0 → octDot u octJ = 0 →
        albertTrace (pentadChain (continuousPentad u) L) = parameterEval (octDot u octK) p) := by
  let p := pentadConnectedTracePolynomial L
  refine ⟨p, ?_, ?_, ?_, fun u hu hre hI hJ => continuousPentad_connectedTrace u hu hre hI hJ L⟩
  · intro a ha
    by_cases h : p = 0
    · simp [h]
    · simpa [occurrenceCost, ha] using
        pentadConnectedTracePolynomial_coeff_frequency L a (tracePolynomial_topCoefficient L h)
  · by_cases h : p = 0
    · simp [h]
    · simpa [occurrenceCost] using
        pentadConnectedTracePolynomial_coeff_frequency L 2 (tracePolynomial_topCoefficient L h)
  · by_cases h : p = 0
    · simp [h]
    · exact pentadConnectedTracePolynomial_coeff_length L (tracePolynomial_topCoefficient L h)

theorem pentadWordPolynomial_degree (w : Word (Fin 5)) (L : List (Fin 5))
    (h : L.length + w.length ≤ 10) :
    (pentadWordPolynomial w L).natDegree ≤ 1 ∧
      (L.length+w.length≤5 → (pentadWordPolynomial w L).natDegree ≤ 0) := by
  induction w generalizing L with
  | nil =>
    exact ⟨pentadConnectedTracePolynomial_degree L (by simp at h; omega),
      fun h0 => pentadConnectedTracePolynomial_degree L (by simp at h0; omega)⟩
  | cons a w ih =>
    obtain ⟨r,b⟩ := a
    have ha := ih L (by simp only [List.length_cons] at h; omega)
    have hb := ih (r :: L) (by simp only [List.length_cons] at h ⊢; omega)
    have hc := ih [r] (by simp [List.length_cons] at h ⊢; omega)
    let t := pentadConnectedTracePolynomial (r :: L)
    let q := pentadWordPolynomial w [r]
    have ht : t.natDegree ≤ 1 := pentadConnectedTracePolynomial_degree _ (by
      simp only [List.length_cons] at h ⊢
      omega)
    have hr : (t*q).natDegree ≤ 1 := by
      by_cases hs : (r :: L).length ≤ 5
      · have hf : t.natDegree ≤ 0 := pentadConnectedTracePolynomial_degree _ (by omega)
        exact (natDegree_mul_le_of_le hf hc.1).trans (by simp)
      · have hq : q.natDegree ≤ 0 := hc.2 (by simp only [List.length_cons, List.length_nil] at h hs ⊢; omega)
        exact (natDegree_mul_le_of_le ht hq).trans (by simp)
    have assemble (n : ℕ) (h1 : (pentadWordPolynomial w L).natDegree ≤ n)
        (h2 : (pentadWordPolynomial w (r :: L)).natDegree ≤ n) (h3 : (t*q).natDegree ≤ n) :
        (pentadWordPolynomial ((r,b) :: w) L).natDegree ≤ n := by
      have hm : (C (-2 : ℚ) * pentadWordPolynomial w (r :: L)).natDegree ≤ n :=
        (natDegree_mul_le_of_le (natDegree_C _).le h2).trans (by simp)
      cases b
      · exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 hm) h3
      · exact h3
    refine ⟨assemble 1 ha.1 hb.1 hr, fun hlow => ?_⟩
    have h1 := ha.2 (by simp only [List.length_cons] at hlow; omega)
    have h2 := hb.2 (by simp only [List.length_cons] at hlow ⊢; omega)
    have h3 := hc.2 (by simp [List.length_cons] at hlow ⊢; omega)
    have ht0 : t.natDegree ≤ 0 := pentadConnectedTracePolynomial_degree _ (by
      simp only [List.length_cons] at hlow ⊢
      omega)
    exact assemble 0 h1 h2 ((natDegree_mul_le_of_le ht0 h3).trans (by simp))

/-- Each short chronological probability from p₀ is one affine polynomial
in the Cayley coordinate of the actual arbitrary unit imaginary axis. -/
theorem continuousPentad_p0_word_affine (w : Word (Fin 5)) (h : w.length ≤ 9) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ 1 ∧
      ∀ (u : Octonion), octNormSq u = 1 → octonionReal u = 0 →
        octDot u octI = 0 → octDot u octJ = 0 →
        nativeWordProbability (continuousPentad u) (pentadF 0) w =
          parameterEval (octDot u octK) p := by
  refine ⟨pentadWordPolynomial w [0], (pentadWordPolynomial_degree w [0] (by simp; omega)).1,
    fun u hu hre hI hJ => ?_⟩
  have he : pentadChain (continuousPentad u) [0] = pentadF 0 :=
    jordanMul_albertUnit_right _
  rw [← he]
  exact continuousPentad_connectedWord u hu hre hI hJ w [0]

/-- The corresponding full continuous affinity from the maximally mixed state. -/
theorem continuousPentad_e3_word_affine (w : Word (Fin 5)) (h : w.length ≤ 10) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ 1 ∧
      ∀ (u : Octonion), octNormSq u = 1 → octonionReal u = 0 →
        octDot u octI = 0 → octDot u octJ = 0 →
        nativeWordProbability (continuousPentad u) ((1/3 : ℝ) • albertUnit) w =
          parameterEval (octDot u octK) p := by
  let p := pentadWordPolynomial w []
  have hdeg : p.natDegree ≤ 1 := (pentadWordPolynomial_degree w [] (by simpa using h)).1
  refine ⟨C (1/3) * p, (natDegree_mul_le_of_le (natDegree_C _).le hdeg).trans (by simp),
    fun u hu hre hI hJ => ?_⟩
  have he := continuousPentad_connectedWord u hu hre hI hJ w []
  change nativeWordProbability (continuousPentad u) albertUnit w = _ at he
  rw [nativeWordProbability_smul, he, map_mul]
  simp [parameterEval, p]

end

end AlbertSequential.FiveTest
