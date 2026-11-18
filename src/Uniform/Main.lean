/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.Main
public import LengthSeven.TableValues
public import ThirteenTracesAndAform
public import BoundedWordEffects
public import QuaternionicProjectiveData
public import PositiveFunctionalNull
public import ProjectiveWordProbabilities

/-! # Uniform length seven (paper thm:cer:uniform (a)), native assembly

For four atoms `p_A, …, p_D` of the Albert algebra with four-point invariant `𝒜 > 0`
(`0 < fourPointInvariant p`), no sequential projective
representation reproduces from `e/3` the octonionic probability of every word of length at
most seven that begins with "yes" on `A`; none reproduces from `p_A` the probability of every
word of length at most six.

Assembly (no new mathematics beyond three short native facts):

* native facts: the trace relation (`albert_fourAtom_trace_relation`, prop:fp:tracerel)
  and `𝒜` (`fourPointInvariant`) read through the table-model dictionary `toTraces`
  (`native_traceRelation`, `native_Acal`); `0 < o_Ax < 1` from
  `nativeTraceData_overlap_bounds`;
* `uniform_walkForm`: the table-model package's `no_walkForm_of_gram28Rules`
  (Lemma A + table-model identity + Lemma B) at `τ = nativeTraceData p`;
* `uniform_of_reproduces_pA`: hypothesis (H) of the paper (a walk form reproducing the
  table from `p_A` on all words of length ≤ 6) via
  (`gram28Hyp_of_lengthSix`, `Gram28Hyp.rules`) and `tableValues_native`;
* representations: `AlgebraicProjectiveData` (comparator class) through
  `lengthSeven_e3_rules` (e/3, length ≤ 7) or through the certainty lemma
  `probability_cons_yesA_of_certain` (p_A, length ≤ 6); real/complex Hilbert and quaternionic
  models through the `toAlgebraic` bridges (the adapters `WalkForm.ofHilbert`,
  `WalkForm.ofQuaternionic` are definitionally `WalkForm.ofAlgebraic ∘ toAlgebraic`).
-/

@[expose] public section

namespace AlbertSequential.LengthSeven.Uniform

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.TableModel

/-! ## Native facts read through the table-model dictionary -/

theorem toTraces_native_t1 (p : Fin 4 → Albert) :
    (toTraces (nativeTraceData p)).t1 = fpDoublePair1 p := by
  show ((nativeTraceData p).om 2 + (nativeTraceData p).om 3) / 2 = _
  rw [(nativeTraceData_om p).2.1, (nativeTraceData_om p).2.2]
  unfold fpOmega2 fpOmega3
  ring

theorem toTraces_native_t2 (p : Fin 4 → Albert) :
    (toTraces (nativeTraceData p)).t2 = fpDoublePair2 p := by
  show ((nativeTraceData p).om 1 + (nativeTraceData p).om 3) / 2 = _
  rw [(nativeTraceData_om p).1, (nativeTraceData_om p).2.2]
  unfold fpOmega1 fpOmega3
  ring

theorem toTraces_native_t3 (p : Fin 4 → Albert) :
    (toTraces (nativeTraceData p)).t3 = fpDoublePair3 p := by
  show ((nativeTraceData p).om 1 + (nativeTraceData p).om 2) / 2 = _
  rw [(nativeTraceData_om p).1, (nativeTraceData_om p).2.1]
  unfold fpOmega1 fpOmega2
  ring

/-- prop:fp:tracerel for the native trace data, in Lemma B's form. -/
theorem native_traceRelation (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    (toTraces (nativeTraceData p)).TraceRelation := by
  unfold LemmaB.Traces.TraceRelation
  rw [toTraces_native_t1, toTraces_native_t2, toTraces_native_t3]
  have h := albert_fourAtom_trace_relation p hp
  -- Lemma B sums the overlaps in the order AB, AC, AD, BC, CD, BD
  change _ = 1 / 2 - 1 / 2 * (fpOverlap p 0 1 + fpOverlap p 0 2 + fpOverlap p 0 3
      + fpOverlap p 1 2 + fpOverlap p 2 3 + fpOverlap p 1 3)
    + 1 / 2 * (fpOverlap p 0 1 * fpOverlap p 2 3 + fpOverlap p 0 2 * fpOverlap p 1 3
      + fpOverlap p 0 3 * fpOverlap p 1 2)
    + fpTriangle p 0 1 2 + fpTriangle p 0 1 3 + fpTriangle p 0 2 3 + fpTriangle p 1 2 3
  linarith

/-- Lemma B's sixteen-term `𝒜` at the native trace data is `fourPointInvariant`. -/
theorem native_Acal (p : Fin 4 → Albert) :
    (toTraces (nativeTraceData p)).Acal = fourPointInvariant p := by
  have e1 : (toTraces (nativeTraceData p)).ω1 = fpOmega1 p := toTraces_ω1 _
  have e2 : (toTraces (nativeTraceData p)).ω2 = fpOmega2 p := toTraces_ω2 _
  have e3 : (toTraces (nativeTraceData p)).ω3 = fpOmega3 p := toTraces_ω3 _
  unfold LemmaB.Traces.Acal
  rw [e1, e2, e3]
  rfl

/- Lean 4.36 / Mathlib v4.36.0: `Real.lt` is no longer an `irreducible_def` but a plain (no_expose) def,
which this non-module file can unfold; defeq checks of `0 < fourPointInvariant p` then evaluate the
invariant. Below this point nothing needs its body, so it is made irreducible here (proof-irrelevant). -/
attribute [local irreducible] fourPointInvariant

/-! ## The walk-form theorems -/

/-- No walk form satisfies Lemma A's rule package with the native trace data of four atoms
with `𝒜 > 0`. -/
theorem uniform_walkForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (W : WalkForm V) (h : Gram28Rules W (nativeTraceData p)) : False := by
  have hB := nativeTraceData_overlap_bounds p hp hA 1 (by decide)
  have hC := nativeTraceData_overlap_bounds p hp hA 2 (by decide)
  have hD := nativeTraceData_overlap_bounds p hp hA 3 (by decide)
  exact no_walkForm_of_gram28Rules W (nativeTraceData p) h (native_traceRelation p hp)
    (by rw [native_Acal]; exact hA) hB.1 hB.2 hC.1 hC.2 hD.1 hD.2

/-- Hypothesis (H) of the paper, walk-form carrier: no PSD walk form reproduces, from `p_A`,
the octonionic probability of every word of length at most six. -/
theorem uniform_of_reproduces_pA {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (W : WalkForm V)
    (hrep : W.Reproduces {u | u.length ≤ 6} (nativeWordProbability p (p 0))) : False := by
  have hT := tableValues_native p hp
  have hS : ∀ u : Word Letter, u.length ≤ 6 → u ∈ {u : Word Letter | u.length ≤ 6} :=
    fun _ hu => hu
  have hG := WalkForm.gram28Hyp_of_lengthSix hrep hT hS
  exact uniform_walkForm p hp hA W (WalkForm.Gram28Hyp.rules hG hrep hT)

/-! ## Algebraic representations (comparator class) -/

section Algebraic

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- If `Pr(A) = 1` then a leading "yes" on `A` changes no probability (the complement
`1 - P_A` is null for the state, and the null set is a left ideal). -/
theorem probability_cons_yesA_of_certain (M : AlgebraicProjectiveData Letter A)
    (h1 : M.probability [(0, true)] = 1) (u : Word Letter) :
    M.probability ((0, true) :: u) = M.probability u := by
  have hstar : ∀ x, M.state (star x) = M.state x := M.state_star
  have hpos : ∀ x, 0 ≤ M.state (star x * x) := M.state_positive
  have hsq : star (1 - M.projection 0) * (1 - M.projection 0) =
      1 - star (M.projection 0) * M.projection 0 := by
    rw [star_sub, star_one, M.selfAdjoint 0, sub_mul, one_mul, mul_sub, mul_one, M.idempotent 0]
    abel
  have hnull : NullFor M.state (1 - M.projection 0) := by
    change M.state (star (1 - M.projection 0) * (1 - M.projection 0)) = 0
    rw [hsq, map_sub, M.state_unit, ← probability_yesA, h1, sub_self]
  obtain ⟨a, ha⟩ : ∃ a, a = wordAmplitude M.projection u := ⟨_, rfl⟩
  have hy : NullFor M.state (a * (1 - M.projection 0)) :=
    nullFor_left_invariant M.state hstar hpos a _ hnull
  have hsplit : a = a * M.projection 0 + a * (1 - M.projection 0) := by
    rw [mul_sub, mul_one]; abel
  have h1' := nullFor_pair_zero M.state hstar hpos _ hy (a * M.projection 0)
  have h2' := positiveForm_symmetric M.state hstar (a * M.projection 0) (a * (1 - M.projection 0))
  have h3' : M.state (star (a * (1 - M.projection 0)) * (a * (1 - M.projection 0))) = 0 := hy
  have key : M.state (star a * a) =
      M.state (star (a * M.projection 0) * (a * M.projection 0)) := by
    have e : M.state (star a * a) =
        M.state (star (a * M.projection 0 + a * (1 - M.projection 0)) *
          (a * M.projection 0 + a * (1 - M.projection 0))) := by
      rw [← hsplit]
    rw [e]
    simp only [star_add, add_mul, mul_add, map_add]
    linarith
  rw [AlgebraicProjectiveData.probability_eq_squareMass,
    AlgebraicProjectiveData.probability_eq_squareMass, wordAmplitude_cons, ← ha]
  unfold AlgebraicProjectiveData.squareMass
  rw [key]
  simp [algebraicOutcome]

/-- **thm:cer:uniform (a), first sentence, algebraic comparator class.** -/
theorem uniform_lengthSeven_e3_algebraic
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : AlgebraicProjectiveData Letter A)
    (hM : ∀ w : Word Letter, w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) : False := by
  obtain ⟨h, -, -, -, hR⟩ := lengthSeven_e3_rules M p hp hM
  exact uniform_walkForm p hp hA _ hR

/-- **thm:cer:uniform (a), second sentence, algebraic comparator class.** -/
theorem uniform_lengthSix_pA_algebraic
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : AlgebraicProjectiveData Letter A)
    (hM : ∀ u : Word Letter, u.length ≤ 6 →
      M.probability u = nativeWordProbability p (p 0) u) : False := by
  have h1 : M.probability [(0, true)] = 1 := by
    rw [hM _ (by simp), val_one p hp 0 0]
    exact tracePairing_atom_self (p 0) (hp 0)
  have h : 0 < M.probability [(0, true)] := by rw [h1]; norm_num
  have hrep : (WalkForm.ofAlgebraic M h).Reproduces {u | u.length ≤ 6}
      (nativeWordProbability p (p 0)) :=
    WalkForm.ofAlgebraic_reproduces M h _ _ fun u hu => by
      rw [probability_cons_yesA_of_certain M h1 u, h1, div_one]
      exact hM u hu
  exact uniform_of_reproduces_pA p hp hA _ hrep

end Algebraic

/-! ## Real and complex Hilbert models -/

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **thm:cer:uniform (a), first sentence, real or complex Hilbert space.** -/
theorem uniform_lengthSeven_e3_hilbert
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : HilbertProjectiveData Letter 𝕜 H)
    (hM : ∀ w : Word Letter, w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) : False :=
  uniform_lengthSeven_e3_algebraic p hp hA M.toAlgebraic fun w hw h0 => by
    rw [M.toAlgebraic_probability]; exact hM w hw h0

/-- **thm:cer:uniform (a), second sentence, real or complex Hilbert space.** -/
theorem uniform_lengthSix_pA_hilbert
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : HilbertProjectiveData Letter 𝕜 H)
    (hM : ∀ u : Word Letter, u.length ≤ 6 →
      M.probability u = nativeWordProbability p (p 0) u) : False :=
  uniform_lengthSix_pA_algebraic p hp hA M.toAlgebraic fun u hu => by
    rw [M.toAlgebraic_probability]; exact hM u hu

/-- The adapter `WalkForm.ofHilbert` is the algebraic one on the `toAlgebraic` bridge. -/
example (M : HilbertProjectiveData Letter 𝕜 H) (h : 0 < M.toAlgebraic.probability [(0, true)]) :
    WalkForm.ofHilbert M h = WalkForm.ofAlgebraic M.toAlgebraic h := rfl

end Hilbert

/-! ## Quaternionic models -/

section Quaternionic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Q : QuaternionicOperatorStructure H}

/-- **thm:cer:uniform (a), first sentence, quaternionic model** (any
`QuaternionicOperatorStructure`, in particular the right quaternionic Hilbert spaces
`S.toOperatorStructure`). -/
theorem uniform_lengthSeven_e3_quaternionic
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : QuaternionicProjectiveData Letter Q)
    (hM : ∀ w : Word Letter, w.length ≤ 7 → w.head? = some (0, true) →
      M.state (M.wordEffect w) = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :
    False :=
  uniform_lengthSeven_e3_algebraic p hp hA M.toAlgebraic fun w hw h0 => by
    rw [M.toAlgebraic_probability]; exact hM w hw h0

/-- **thm:cer:uniform (a), second sentence, quaternionic model.** -/
theorem uniform_lengthSix_pA_quaternionic
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (M : QuaternionicProjectiveData Letter Q)
    (hM : ∀ u : Word Letter, u.length ≤ 6 →
      M.state (M.wordEffect u) = nativeWordProbability p (p 0) u) : False :=
  uniform_lengthSix_pA_algebraic p hp hA M.toAlgebraic fun u hu => by
    rw [M.toAlgebraic_probability]; exact hM u hu

example (M : QuaternionicProjectiveData Letter Q)
    (h : 0 < M.toAlgebraic.probability [(0, true)]) :
    WalkForm.ofQuaternionic M h = WalkForm.ofAlgebraic M.toAlgebraic h := rfl

end Quaternionic

end AlbertSequential.LengthSeven.Uniform
