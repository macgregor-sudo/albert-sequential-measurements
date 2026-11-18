/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.JordanPoly

/-! # From words to operator words (companion `app:cert:h5`, "From words to symbols", first half)

For a word `w = (q_1, …, q_k)` the paper writes `f(w) = U_{q_1} ⋯ U_{q_k} 1` (first measurement
outermost) and `q = (1 ± x)/2` in the symmetry letters.  Here:

* `wordPoly w` is that Jordan expression; its special value is the Lüders effect
  `wordOperator P w` (`specialEval_wordPoly`) and its Albert value is
  `nativeWordEffect p w` (`albertEval_wordPoly`);
* `expand w` is the expansion `U_{(e±s)/2} = (id ± A_s + C_s)/4` of every factor, a combination
  of operator words `X_1 ⋯ X_m 1`, `X_t ∈ {A_{x_i}, C_{x_i}}`, `m ≤ |w|`; it has the same value as
  `wordPoly w` in every unital commutative target in which the letters are symmetries
  (`eval_wordPoly_eq_expand`), in particular in both targets.

Consequently (`horizonFive_of_operatorTransfer`) the horizon-five clause follows from the kernel
inclusion for combinations of operator words with at most five operators,
`OperatorWordTransfer5`.  The paper then shortens these operator words to canonical symbols by
(eq:cer:h5:canon); that step and the kernel inclusion for symbols are in `HorizonFive.Lemmas`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-- The letter `q = (1 + x_i)/2` (yes) or `(1 - x_i)/2` (no) of an outcome. -/
def outcomeLetter : Outcome Test → JPoly Test
  | (i, true) => .smul (1 / 2) (.add .one (.var i))
  | (i, false) => .smul (1 / 2) (.add .one (.smul (-1) (.var i)))

/-- `f(w) = U_{q_1} ⋯ U_{q_k} 1`, first outcome outermost. -/
def wordPoly : Word Test → JPoly Test
  | [] => .one
  | a :: w => .U (outcomeLetter a) (wordPoly w)

/-! ## Special value of a word is its Lüders effect -/

theorem wordAmplitude_foldl {ι R : Type*} [Ring R] (P : ι → R) (w : Word ι) (y : R) :
    w.foldl (fun x a => algebraicOutcome P a * x) y = wordAmplitude P w * y := by
  induction w generalizing y with
  | nil => simp [wordAmplitude]
  | cons b w ih =>
    simp only [List.foldl_cons, wordAmplitude]
    rw [ih, ih (algebraicOutcome P b * 1), mul_assoc, _root_.mul_one]

theorem wordAmplitude_cons {ι R : Type*} [Ring R] (P : ι → R) (a : Outcome ι) (w : Word ι) :
    wordAmplitude P (a :: w) = wordAmplitude P w * algebraicOutcome P a := by
  change w.foldl _ (algebraicOutcome P a * 1) = _
  rw [wordAmplitude_foldl, _root_.mul_one]

theorem wordOperator_cons {ι R : Type*} [Ring R] [StarRing R] (P : ι → R)
    (hP : ∀ i, star (P i) = P i) (a : Outcome ι) (w : Word ι) :
    wordOperator P (a :: w) =
      algebraicOutcome P a * wordOperator P w * algebraicOutcome P a := by
  have hq : star (algebraicOutcome P a) = algebraicOutcome P a := by
    rcases a with ⟨i, b⟩
    cases b <;> simp [algebraicOutcome, hP]
  simp only [wordOperator, wordAmplitude_cons, star_mul, hq, mul_assoc]

theorem specialEval_outcomeLetter (a : Outcome Test) :
    specialEval (outcomeLetter a) = algebraicOutcome universalTests a := by
  rcases a with ⟨i, b⟩
  cases b <;>
  · simp only [outcomeLetter, specialEval, JTarget.eval, specialSymmetry, algebraicOutcome]
    change _ = if _ then _ else _
    simp only [Bool.false_eq_true, ite_false, ite_true]
    change (1 / 2 : ℝ) • ((1 : UniversalProjectionAlgebra 4) + _) = _
    module

theorem specialEval_wordPoly (w : Word Test) :
    specialEval (wordPoly w) = wordOperator universalTests w := by
  induction w with
  | nil =>
    simp only [wordPoly, specialEval, JTarget.eval, wordOperator, wordAmplitude, List.foldl_nil,
      star_one, _root_.mul_one]
    rfl
  | cons a w ih =>
    rw [wordOperator_cons universalTests (fun i => universalProjection_selfAdjoint i)]
    simp only [wordPoly]
    unfold specialEval
    rw [JTarget.eval_U, specialTarget_Uop]
    change specialEval _ * specialEval _ * specialEval _ = _
    rw [ih, specialEval_outcomeLetter]

/-! ## Albert value of a word is its native effect -/

theorem albertEval_outcomeLetter (p : Test → Albert) (a : Outcome Test) :
    albertEval p (outcomeLetter a) = nativeOutcome p a := by
  rcases a with ⟨i, b⟩
  cases b <;>
  · simp only [outcomeLetter, albertEval, JTarget.eval, nativeSymmetry, nativeOutcome]
    change _ = if _ then _ else _
    simp only [Bool.false_eq_true, ite_false, ite_true]
    change (1 / 2 : ℝ) • (albertUnit + _) = _
    module

theorem albertEval_wordPoly (p : Test → Albert) (w : Word Test) :
    albertEval p (wordPoly w) = nativeWordEffect p w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [wordPoly, nativeWordEffect]
    unfold albertEval
    rw [JTarget.eval_U, albertTarget_Uop]
    change quadraticMap (albertEval p _) (albertEval p _) = _
    rw [ih, albertEval_outcomeLetter]

/-! ## Operator words -/

/-- The operators `A_{x_i} = 2L_{x_i}` and `C_{x_i} = U_{x_i}`. -/
inductive Op : Type where
  | A : Test → Op
  | C : Test → Op
  deriving DecidableEq

/-- The operator word `X_1 ⋯ X_m 1` as a Jordan expression. -/
def opPoly : List Op → JPoly Test
  | [] => .one
  | .A i :: l => .A (.var i) (opPoly l)
  | .C i :: l => .U (.var i) (opPoly l)

/-- Sign of the `A`-term in `U_{(e ± s)/2} = (id ± A_s + C_s)/4`. -/
def outcomeSign : Bool → ℝ
  | true => 1
  | false => -1

/-- Expansion of a word into operator words. -/
def expand : Word Test → (List Op →₀ ℝ)
  | [] => Finsupp.single [] 1
  | (i, b) :: w =>
      (1 / 4 : ℝ) • (expand w + outcomeSign b • Finsupp.mapDomain (List.cons (Op.A i)) (expand w)
        + Finsupp.mapDomain (List.cons (Op.C i)) (expand w))

theorem expand_mem_supported (w : Word Test) :
    expand w ∈ Finsupp.supported ℝ ℝ {l : List Op | l.length ≤ w.length} := by
  induction w with
  | nil =>
    simp only [expand]
    exact Finsupp.single_mem_supported ℝ 1 (by simp)
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    simp only [expand]
    have hmono : Finsupp.supported ℝ ℝ {l : List Op | l.length ≤ w.length} ≤
        Finsupp.supported ℝ ℝ {l : List Op | l.length ≤ ((i, b) :: w).length} :=
      Finsupp.supported_mono (fun l (hl : l.length ≤ w.length) => by
        simp only [Set.mem_ofPred_eq, List.length_cons]; omega)
    have hmap : ∀ o : Op, Finsupp.mapDomain (List.cons o) (expand w) ∈
        Finsupp.supported ℝ ℝ {l : List Op | l.length ≤ ((i, b) :: w).length} := by
      intro o
      rw [Finsupp.mem_supported] at ih ⊢
      intro l hl
      have h1 : l ∈ (expand w).support.image (List.cons o) := Finsupp.mapDomain_support hl
      rw [Finset.mem_image] at h1
      obtain ⟨m, hm, rfl⟩ := h1
      have := ih hm
      simp only [Set.mem_ofPred_eq, List.length_cons] at this ⊢
      omega
    refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ (hmono ih) ?_) ?_)
    · exact Submodule.smul_mem _ _ (hmap _)
    · exact hmap _

namespace JTarget
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E)

/-- `A_s` as a linear map. -/
def AopLin (s : E) : E →ₗ[ℝ] E where
  toFun := T.Aop s
  map_add' y z := by simp only [Aop, T.mul_add, smul_add]
  map_smul' r y := by simp only [Aop, T.mul_smul, RingHom.id_apply]; module

/-- `U_s` as a linear map. -/
def UopLin (s : E) : E →ₗ[ℝ] E where
  toFun := T.Uop s
  map_add' y z := by simp only [Uop, T.mul_add]; module
  map_smul' r y := by simp only [Uop, T.mul_smul, RingHom.id_apply]; module

/-- Value of a combination of operator words. -/
def evalOps (v : Test → E) : (List Op →₀ ℝ) →ₗ[ℝ] E :=
  Finsupp.linearCombination ℝ (fun l => T.eval v (opPoly l))

theorem eval_opPoly_A (v : Test → E) (i : Test) (l : List Op) :
    T.eval v (opPoly (Op.A i :: l)) = T.AopLin (v i) (T.eval v (opPoly l)) := rfl

theorem eval_opPoly_C (v : Test → E) (i : Test) (l : List Op) :
    T.eval v (opPoly (Op.C i :: l)) = T.UopLin (v i) (T.eval v (opPoly l)) := by
  change T.eval v (JPoly.U _ _) = _
  rw [T.eval_U]; rfl

/-- The expansion has the same value as the word, whenever the letters are symmetries. -/
theorem eval_wordPoly_eq_expand (v : Test → E) (hv : ∀ i, T.mul (v i) (v i) = T.one)
    (w : Word Test) :
    T.eval v (wordPoly w) = T.evalOps v (expand w) := by
  induction w with
  | nil =>
    simp only [wordPoly, expand, evalOps, Finsupp.linearCombination_single, one_smul, opPoly]
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    simp only [wordPoly, expand, evalOps, map_smul, map_add, Finsupp.linearCombination_mapDomain]
    rw [T.eval_U]
    have hA : Finsupp.linearCombination ℝ ((fun l => T.eval v (opPoly l)) ∘ List.cons (Op.A i))
        (expand w) = T.Aop (v i) (T.eval v (wordPoly w)) := by
      rw [ih]
      change _ = T.AopLin (v i) (Finsupp.linearCombination ℝ _ (expand w))
      rw [Finsupp.apply_linearCombination]
      rfl
    have hC : Finsupp.linearCombination ℝ ((fun l => T.eval v (opPoly l)) ∘ List.cons (Op.C i))
        (expand w) = T.Uop (v i) (T.eval v (wordPoly w)) := by
      rw [ih]
      change _ = T.UopLin (v i) (Finsupp.linearCombination ℝ _ (expand w))
      rw [Finsupp.apply_linearCombination]
      exact congrArg (fun f => Finsupp.linearCombination ℝ f (expand w))
        (funext fun l => T.eval_opPoly_C v i l)
    rw [hA, hC, show (Finsupp.linearCombination ℝ fun l => T.eval v (opPoly l)) (expand w) =
      T.eval v (wordPoly w) from ih.symm]
    cases b
    · change T.Uop ((1 / 2 : ℝ) • (T.one + (-1 : ℝ) • v i)) _ = _
      rw [T.Uop_half_minus _ _ (hv i)]
      simp only [outcomeSign]
      module
    · change T.Uop ((1 / 2 : ℝ) • (T.one + v i)) _ = _
      rw [T.Uop_half_plus _ _ (hv i)]
      simp only [outcomeSign]
      module

end JTarget

/-- Special value of a combination of operator words. -/
def opSpecial (F : List Op →₀ ℝ) : UniversalProjectionAlgebra 4 :=
  (specialTarget (UniversalProjectionAlgebra 4)).evalOps specialSymmetry F

/-- Albert value of a combination of operator words. -/
def opAlbert (p : Test → Albert) (F : List Op →₀ ℝ) : Albert :=
  albertTarget.evalOps (nativeSymmetry p) F

/-- Kernel inclusion for combinations of operator words with at most five operators
(the paper's (eq:cer:h5:goal) before shortening to canonical symbols). -/
def OperatorWordTransfer5 : Prop :=
  ∀ p : Test → Albert, (∀ i, IsAtom (p i)) →
    ∀ F : List Op →₀ ℝ, F ∈ Finsupp.supported ℝ ℝ {l : List Op | l.length ≤ 5} →
      opSpecial F = 0 → opAlbert p F = 0

/-- The total expansion of a word combination. -/
def expandC (c : WordCombination) : List Op →₀ ℝ :=
  Finsupp.linearCombination ℝ expand c

theorem opSpecial_expandC (c : WordCombination) : opSpecial (expandC c) = specialValue c := by
  unfold opSpecial expandC specialValue
  rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun w _ => ?_
  congr 1
  simp only [Function.comp_apply]
  rw [← (specialTarget _).eval_wordPoly_eq_expand _ specialSymmetry_sq]
  exact specialEval_wordPoly w

theorem opAlbert_expandC (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (c : WordCombination) : opAlbert p (expandC c) = nativeEffectValue p c := by
  unfold opAlbert expandC nativeEffectValue
  rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun w _ => ?_
  congr 1
  simp only [Function.comp_apply]
  rw [← albertTarget.eval_wordPoly_eq_expand _ (nativeSymmetry_sq p hp)]
  exact albertEval_wordPoly p w

theorem expandC_mem_supported (c : WordCombination) (hc : SupportedWithin c 5) :
    expandC c ∈ Finsupp.supported ℝ ℝ {l : List Op | l.length ≤ 5} := by
  unfold expandC
  rw [Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun w hw => Submodule.smul_mem _ _ ?_
  exact Finsupp.supported_mono (s := {l : List Op | l.length ≤ w.length})
    (t := {l : List Op | l.length ≤ 5}) (fun l (hl : l.length ≤ w.length) => by
    have := hc w hw
    simp only [Set.mem_ofPred_eq]; omega) (expand_mem_supported w)

/-- **Reduction proved**: the horizon-five clause follows from the operator-word kernel inclusion. -/
theorem horizonFiveEffect_of_operatorTransfer (h : OperatorWordTransfer5) :
    HorizonFiveEffectClause := by
  intro p hp c hc hE
  rw [← opAlbert_expandC p (fun i => (hp i).1)]
  exact h p hp _ (expandC_mem_supported c hc) (by rw [opSpecial_expandC]; exact hE)

theorem horizonFive_of_operatorTransfer (h : OperatorWordTransfer5) : HorizonFiveClause :=
  horizonFiveClause_of_effectClause (horizonFiveEffect_of_operatorTransfer h)

end AlbertSequential.HorizonFive
