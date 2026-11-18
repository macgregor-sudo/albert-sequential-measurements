/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.Budget
public import FiveTest.Compose
public import LengthSeven.TableValues
public import TableModel.Main
public import LemmaB.Conclusion
public import Mathlib.Tactic.NormNum

/-! # thm:five:refl and prop:five:short(a)

Not a `module` file: it joins the `module` files (`FiveTest.*`, `LengthSeven.*` and their imports)
with the Mathlib-only Lemma B package (namespace `LemmaB`, plain imports).

Statements (model class (I) in the algebraic form `AlgebraicProjectiveData`, which the
bridges `HilbertProjectiveData.toAlgebraic` (ℝ, ℂ) and `QuaternionicProjectiveData.toAlgebraic`
(ℍ) instantiate; corollaries below):

* `thm_five_refl`: no representation of `(A,B,C,D) = (p₀, p₁, U_r p₃, U_r p₄)` reproduces from
  `p₀` every word `u` with `|u| + ν(u) ≤ 10`.
* `five_short_p0`: no representation of the five tests reproduces from `p₀` every five-test
  word of length `≤ 10` (prop:five:short(a), first half).
* `five_short_e3`: none reproduces from `e/3` every five-test word of length `≤ 11` that begins
  with "yes" on `p₀` (prop:five:short(a), second half).

**Unconditional.** The two hypotheses `ReflTableValues` and `ReflTableModel` are discharged here:
`reflTableValues` (`tableValues_native` at `reflQuad`, with `reflQuad_isAtom`) and
`reflTableModel` (`tableModel_lemmaB`; its `toTraces` at the native traces is
`reflTraces`, `toTraces_reflQuad`). Everything else (traces, 𝒜 = 1/11664, trace relation,
`0 < o_Ax < 1`, transfer with cost, budget, Lemma A, Lemma B) is proved. -/

@[expose] public section

set_option autoImplicit false

namespace AlbertSequential.FiveTest

open AlbertSequential AlbertSequential.LengthSeven AlbertSequential.LengthSeven.LemmaA
open AlbertSequential.NativeAnalysis

/-! ## The thirteen traces in Lemma B's format -/

/-- Lemma B's trace record for the reflected quadruple (field `oCD` precedes `oBD`; `t_k` are the
double pairings `AB|CD, AC|BD, AD|BC`). -/
noncomputable def reflTraces : LemmaB.Traces where
  oAB := 1 / 2
  oAC := 5 / 18
  oAD := 5 / 18
  oBC := 5 / 18
  oCD := 1 / 2
  oBD := 5 / 18
  RABC := 5 / 36
  RABD := 5 / 36
  RACD := 5 / 36
  RBCD := 5 / 36
  t1 := 5 / 72
  t2 := 43 / 648
  t3 := 43 / 648

/-- Dictionary: `reflTraces` are the native traces of `reflQuad` (interface `nativeTraceData`,
ω by middle letter, and Lemma B's `ω_r = t₁ + t₂ + t₃ − 2t_r`). -/
theorem reflTraces_native :
    reflTraces.oAB = (nativeTraceData reflQuad).o 0 1 ∧ reflTraces.oAC = (nativeTraceData reflQuad).o 0 2 ∧
    reflTraces.oAD = (nativeTraceData reflQuad).o 0 3 ∧ reflTraces.oBC = (nativeTraceData reflQuad).o 1 2 ∧
    reflTraces.oCD = (nativeTraceData reflQuad).o 2 3 ∧ reflTraces.oBD = (nativeTraceData reflQuad).o 1 3 ∧
    reflTraces.RABC = (nativeTraceData reflQuad).R 0 1 2 ∧ reflTraces.RABD = (nativeTraceData reflQuad).R 0 1 3 ∧
    reflTraces.RACD = (nativeTraceData reflQuad).R 0 2 3 ∧ reflTraces.RBCD = (nativeTraceData reflQuad).R 1 2 3 ∧
    reflTraces.t1 = fpDoublePair1 reflQuad ∧ reflTraces.t2 = fpDoublePair2 reflQuad ∧
    reflTraces.t3 = fpDoublePair3 reflQuad ∧
    reflTraces.ω1 = (nativeTraceData reflQuad).om 1 ∧ reflTraces.ω2 = (nativeTraceData reflQuad).om 2 ∧
    reflTraces.ω3 = (nativeTraceData reflQuad).om 3 := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := reflQuad_overlaps
  obtain ⟨r1, r2, r3, r4⟩ := reflQuad_triangles
  obtain ⟨t1, t2, t3⟩ := reflQuad_doublePairs
  obtain ⟨w1, w2, w3⟩ := reflQuad_omegas
  obtain ⟨n1, n2, n3⟩ := nativeTraceData_om reflQuad
  simp only [nativeTraceData_o, nativeTraceData_R, n1, n2, n3]
  simp only [fpOverlap, fpTriangle] at o1 o2 o3 o4 o5 o6 r1 r2 r3 r4
  rw [o1, o2, o3, o4, o5, o6, r1, r2, r3, r4, t1, t2, t3, w1, w2, w3]
  simp only [reflTraces, LemmaB.Traces.ω1, LemmaB.Traces.ω2, LemmaB.Traces.ω3]
  norm_num

theorem reflTraces_traceRelation : reflTraces.TraceRelation := by
  simp only [LemmaB.Traces.TraceRelation, reflTraces]; norm_num

/-- Lemma B's sixteen-term `𝒜` at these traces is `1/11664`, equal to the native
`fourPointInvariant reflQuad`. -/
theorem reflTraces_Acal : reflTraces.Acal = 1 / 11664 := by
  simp only [LemmaB.Traces.Acal, LemmaB.Traces.ω1, LemmaB.Traces.ω2, LemmaB.Traces.ω3, reflTraces]
  norm_num

theorem reflTraces_Acal_eq_native : reflTraces.Acal = fourPointInvariant reflQuad := by
  rw [reflTraces_Acal, fourPointInvariant_reflQuad]

/-- The 28 words of Lemma A (interface `word28`) and of Lemma B (`LemmaB.word28`) coincide. -/
theorem word28_agree : ∀ k : Fin 28, LengthSeven.word28 k = LemmaB.word28 k := by decide

/-- lem:cer:tablemodel at the reflected quadruple, as a statement (proved below as `reflTableModel`). -/
def ReflTableModel : Prop :=
  ∀ k l : Fin 28, gram28 (nativeTraceData reflQuad) k l =
    LemmaB.Q reflTraces.toParams (LemmaB.uhat reflTraces.toParams (LemmaB.word28 k))
      (LemmaB.uhat reflTraces.toParams (LemmaB.word28 l))

/-- The native table values at the reflected quadruple, as a statement (proved below as `reflTableValues`). -/
def ReflTableValues : Prop :=
  TableValues (nativeTraceData reflQuad) (nativeWordProbability reflQuad (reflQuad 0))

/-- **Discharged** (`tableValues_native` at `reflQuad`). -/
theorem reflTableValues : ReflTableValues := tableValues_native reflQuad reflQuad_isAtom

/-- The table–model package's `toTraces` at the native traces is `reflTraces`
(`t₁ = (ω_C+ω_D)/2`, `t₂ = (ω_B+ω_D)/2`, `t₃ = (ω_B+ω_C)/2`). -/
theorem toTraces_reflQuad : TableModel.toTraces (nativeTraceData reflQuad) = reflTraces := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := reflQuad_overlaps
  obtain ⟨r1, r2, r3, r4⟩ := reflQuad_triangles
  obtain ⟨w1, w2, w3⟩ := reflQuad_omegas
  obtain ⟨n1, n2, n3⟩ := nativeTraceData_om reflQuad
  simp only [fpOverlap, fpTriangle] at o1 o2 o3 o4 o5 o6 r1 r2 r3 r4
  simp only [TableModel.toTraces, TraceData.dpair, nativeTraceData_o, nativeTraceData_R, n1, n2, n3,
    o1, o2, o3, o4, o5, o6, r1, r2, r3, r4, w1, w2, w3, reflTraces]
  norm_num

/-- **Discharged** (`tableModel_lemmaB`; `o_AB, o_AC, o_AD ≠ 0`). -/
theorem reflTableModel : ReflTableModel := by
  intro k l
  have hB : (nativeTraceData reflQuad).o 0 1 ≠ 0 := by
    rw [nativeTraceData_o]; rw [show tracePairing (reflQuad 0) (reflQuad 1) = fpOverlap reflQuad 0 1
      from rfl, reflQuad_overlaps.1]; norm_num
  have hC : (nativeTraceData reflQuad).o 0 2 ≠ 0 := by
    rw [nativeTraceData_o]; rw [show tracePairing (reflQuad 0) (reflQuad 2) = fpOverlap reflQuad 0 2
      from rfl, reflQuad_overlaps.2.1]; norm_num
  have hD : (nativeTraceData reflQuad).o 0 3 ≠ 0 := by
    rw [nativeTraceData_o]; rw [show tracePairing (reflQuad 0) (reflQuad 3) = fpOverlap reflQuad 0 3
      from rfl, reflQuad_overlaps.2.2.1]; norm_num
  have h := TableModel.tableModel_lemmaB (nativeTraceData reflQuad) hB hC hD k l
  rw [toTraces_reflQuad] at h
  exact h

section Algebraic

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- **thm:five:refl.** No sequential projective representation of the four tests
`(A,B,C,D) = (p₀, p₁, U_r p₃, U_r p₄)` reproduces from `p₀` the probability of every word `u` with
`|u| + ν(u) ≤ 10`. -/
theorem thm_five_refl (M : AlgebraicProjectiveData Letter A)
    (hM : ∀ u ∈ wordsBudget, M.probability u = nativeWordProbability reflQuad (reflQuad 0) u) :
    False := by
  have hTM := reflTableModel
  obtain ⟨h, hg⟩ := reflQuad_lemmaA reflTableValues M hM
  let W := WalkForm.ofAlgebraic M h
  refine LemmaB.no_psd_realisation_traces reflTraces reflTraces_traceRelation
    (by rw [reflTraces_Acal]; norm_num)
    (by simp only [reflTraces]; norm_num) (by simp only [reflTraces]; norm_num)
    (by simp only [reflTraces]; norm_num) (by simp only [reflTraces]; norm_num)
    (by simp only [reflTraces]; norm_num) (by simp only [reflTraces]; norm_num)
    W.form W.symm W.psd (fun k => W.pathVec (word28 k)) ?_
  intro k l
  exact (hg k l).trans (hTM k l)

/-- **prop:five:short(a), from `p₀`.** No sequential projective representation of the five
tests of `𝖥` reproduces from `p₀` the probability of every word of length at most ten. -/
theorem five_short_p0 (M : AlgebraicProjectiveData (Fin 5) A)
    (hM : ∀ w : Word (Fin 5), w.length ≤ 10 →
      M.probability w = nativeWordProbability pentadF (pentadF 0) w) : False :=
  thm_five_refl (quadModel M) (fun u hu => quadModel_probability M (pentadF 0) 10 hM u hu)

/-! ### Conditioning `e/3 → p₀` -/

theorem pentad_e3_conditioning (u : Word (Fin 5)) :
    nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) ((0, true) :: u) =
      (1 / 3) * nativeWordProbability pentadF (pentadF 0) u := by
  change nativeWordProbability pentadF
      (quadraticMap (nativeOutcome pentadF (0, true)) ((1 / 3 : ℝ) • albertUnit)) u = _
  have ho : nativeOutcome pentadF (0, true) = pentadF 0 := rfl
  rw [ho, quadraticMap_smul_right, quadraticMap_unit_argument, (pentadF_isAtom 0).1,
    nativeWordProbability_smul]

/-- The conditioned state `X ↦ 3 φ(P₀ X P₀)`. -/
noncomputable def condState (M : AlgebraicProjectiveData (Fin 5) A) : A →ₗ[ℝ] ℝ :=
  (3 : ℝ) • (M.state.comp ((LinearMap.mulLeft ℝ (M.projection 0)).comp
    (LinearMap.mulRight ℝ (M.projection 0))))

theorem condState_apply (M : AlgebraicProjectiveData (Fin 5) A) (X : A) :
    condState M X = 3 * M.state (M.projection 0 * (X * M.projection 0)) := rfl

/-- Conditioning a representation on "yes" on `p₀` (needs `Pr(p₀) = 1/3`). -/
noncomputable def condModel (M : AlgebraicProjectiveData (Fin 5) A)
    (h13 : M.probability [(0, true)] = 1 / 3) : AlgebraicProjectiveData (Fin 5) A where
  projection := M.projection
  idempotent := M.idempotent
  selfAdjoint := M.selfAdjoint
  state := condState M
  state_unit := by
    have h : M.probability [(0, true)] = M.state (M.projection 0) := by
      change M.state (wordOperator M.projection [(0, true)]) = _
      rw [wordOperator_cons M.projection M.selfAdjoint, wordOperator_nil]
      change M.state (M.projection 0 * 1 * M.projection 0) = _
      rw [mul_one, M.idempotent]
    rw [condState_apply, one_mul, M.idempotent, ← h, h13]; norm_num
  state_star X := by
    rw [condState_apply, condState_apply, ← M.state_star (M.projection 0 * (X * M.projection 0)),
      star_mul, star_mul, M.selfAdjoint, mul_assoc]
  state_positive X := by
    rw [condState_apply]
    have h := M.state_positive (X * M.projection 0)
    rw [star_mul, M.selfAdjoint] at h
    have e : M.projection 0 * (star X * X * M.projection 0) =
        M.projection 0 * star X * (X * M.projection 0) := by simp only [mul_assoc]
    rw [e]; positivity

/-- **prop:five:short(a), from `e/3`.** No sequential projective representation of the five
tests reproduces from `e/3` the probability of every word of length at most eleven that begins
with "yes" on `p₀`. -/
theorem five_short_e3 (M : AlgebraicProjectiveData (Fin 5) A)
    (hM : ∀ w : Word (Fin 5), w.length ≤ 11 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w) : False := by
  have h13 : M.probability [(0, true)] = 1 / 3 := by
    rw [hM [(0, true)] (by simp) rfl, pentad_e3_conditioning]
    change (1 / 3 : ℝ) * albertTrace (pentadF 0) = 1 / 3
    rw [(pentadF_isAtom 0).2, mul_one]
  refine five_short_p0 (condModel M h13) (fun w hw => ?_)
  change condState M (wordOperator M.projection w) = _
  rw [condState_apply]
  have e : M.projection 0 * (wordOperator M.projection w * M.projection 0) =
      wordOperator M.projection ((0, true) :: w) := by
    rw [wordOperator_cons M.projection M.selfAdjoint]
    change _ = M.projection 0 * _ * M.projection 0
    simp only [mul_assoc]
  rw [e]
  change 3 * M.probability ((0, true) :: w) = _
  rw [hM _ (by simp only [List.length_cons]; omega) rfl, pentad_e3_conditioning]
  ring

/-- **cor:five:minimum, upper bounds** (`L_min(p₀) ≤ 10`): for every `L ≥ 10`, no representation
reproduces from `p₀` all five-test words through length `L`. The printed lower bounds are not
formalized. -/
theorem cor_five_minimum_upper_p0 (L : ℕ)
    (hL : 10 ≤ L) (M : AlgebraicProjectiveData (Fin 5) A)
    (hM : ∀ w : Word (Fin 5), w.length ≤ L →
      M.probability w = nativeWordProbability pentadF (pentadF 0) w) : False :=
  five_short_p0 M (fun w hw => hM w (hw.trans hL))

/-- **cor:five:minimum, upper bounds** (`L_min(e/3) ≤ 11`), in the form "words beginning with yes
on `p₀`" (the words the proof uses); a fortiori for all words through length `L ≥ 11`. -/
theorem cor_five_minimum_upper_e3 (L : ℕ)
    (hL : 11 ≤ L) (M : AlgebraicProjectiveData (Fin 5) A)
    (hM : ∀ w : Word (Fin 5), w.length ≤ L →
      M.probability w = nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w) : False :=
  five_short_e3 M (fun w hw _ => hM w (hw.trans hL))

end Algebraic

/-! ## Hilbert-space corollaries (ℝ, ℂ via `RCLike`; right-quaternionic) -/

theorem five_short_p0_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData (Fin 5) 𝕜 H)
    (hM : ∀ w : Word (Fin 5), w.length ≤ 10 →
      M.toAlgebraic.probability w = nativeWordProbability pentadF (pentadF 0) w) : False :=
  five_short_p0 M.toAlgebraic hM

theorem five_short_e3_hilbert {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : HilbertProjectiveData (Fin 5) 𝕜 H)
    (hM : ∀ w : Word (Fin 5), w.length ≤ 11 → w.head? = some (0, true) →
      M.toAlgebraic.probability w = nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w) :
    False :=
  five_short_e3 M.toAlgebraic hM

theorem five_short_p0_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 5) Q)
    (hM : ∀ w : Word (Fin 5), w.length ≤ 10 →
      M.toAlgebraic.probability w = nativeWordProbability pentadF (pentadF 0) w) : False :=
  five_short_p0 M.toAlgebraic hM

theorem five_short_e3_quaternionic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Q : QuaternionicOperatorStructure H}
    (M : QuaternionicProjectiveData (Fin 5) Q)
    (hM : ∀ w : Word (Fin 5), w.length ≤ 11 → w.head? = some (0, true) →
      M.toAlgebraic.probability w = nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit) w) :
    False :=
  five_short_e3 M.toAlgebraic hM

end AlbertSequential.FiveTest

#print axioms AlbertSequential.FiveTest.thm_five_refl
#print axioms AlbertSequential.FiveTest.five_short_p0
#print axioms AlbertSequential.FiveTest.five_short_e3
#print axioms AlbertSequential.FiveTest.five_short_e3_hilbert
#print axioms AlbertSequential.FiveTest.five_short_e3_quaternionic
#print axioms AlbertSequential.FiveTest.fourPointInvariant_reflQuad
#print axioms AlbertSequential.FiveTest.reflTraces_native
#print axioms AlbertSequential.FiveTest.word28_agree
#print axioms AlbertSequential.FiveTest.wordsBudget_short
#print axioms AlbertSequential.FiveTest.cor_five_minimum_upper_p0
#print axioms AlbertSequential.FiveTest.cor_five_minimum_upper_e3
#print axioms AlbertSequential.FiveTest.cor_fp_noideal
#print axioms AlbertSequential.FiveTest.cor_fp_noideal_quaternionic
#print axioms AlbertSequential.FiveTest.thm_pentad_b
#print axioms AlbertSequential.FiveTest.thm_pentad_b_quaternionic
#print axioms AlbertSequential.FiveTest.quadModel_probability
#print axioms AlbertSequential.FiveTest.reflQuad_generatesAlbert
#print axioms AlbertSequential.FiveTest.reflTableValues
#print axioms AlbertSequential.FiveTest.reflTableModel
#print axioms AlbertSequential.FiveTest.five_short_p0_hilbert
#print axioms AlbertSequential.FiveTest.five_short_p0_quaternionic
