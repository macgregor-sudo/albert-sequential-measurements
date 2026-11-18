/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.WordBridge
public import JordanPeircePositiveMultiplication

/-! # Canonical relations and canonical symbols (companion `app:cert:h5`, "From words to symbols", second half)

For a symmetry `s` of a unital Jordan algebra, `A_s = 2L_s`, `C_s = U_s` satisfy
(eq:cer:h5:canon): `A_s² = 2(id + C_s)`, `A_s C_s = C_s A_s = A_s`, `C_s² = id`, `C_s e = e`.
All of them follow from `s ∘ s = e` and the Peirce cubic `L_s³ = L_s` (`CanonRelations.ofCube`).
`L_s³ = L_s` is proved in both targets: in the special target from `r² = 1` by ring arithmetic,
and natively from the Peirce cubic of an idempotent (`idempotent_leftMultiplication_cubic`)
applied to `p_i`, with `s_i = 2p_i - e`.

A *symbol* (`isSymbol`) is an operator word with adjacent operators on different letters whose
last operator is an `A` (or the empty word).  `normalize` rewrites every operator word into a
combination of symbols with no more operators, preserving the value in every target satisfying
the canonical relations (`evalOps_normalize`).  Hence the paper's (eq:cer:h5:goal)
(`SymbolTransfer5`) implies `OperatorWordTransfer5`, hence the horizon-five clause
(`horizonFive_of_symbolTransfer`).

Also proved: the contraction identity `L_s U_s = L_s` used in lem:cer:h5:refl(b), in the form
`ς(tut) ∘ ς(t) = ς(u) ∘ ς(t)` (`native_reflection_contraction`). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

namespace JTarget
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E)

/-- The canonical relations (eq:cer:h5:canon) for the letter values `v`. -/
structure CanonRelations (v : Test → E) : Prop where
  AA : ∀ i y, T.Aop (v i) (T.Aop (v i) y) = (2 : ℝ) • (y + T.Uop (v i) y)
  AC : ∀ i y, T.Aop (v i) (T.Uop (v i) y) = T.Aop (v i) y
  CA : ∀ i y, T.Uop (v i) (T.Aop (v i) y) = T.Aop (v i) y
  CC : ∀ i y, T.Uop (v i) (T.Uop (v i) y) = y
  Cone : ∀ i, T.Uop (v i) T.one = T.one

/-- `s ∘ s = e` and `L_s³ = L_s` give all canonical relations. -/
theorem CanonRelations.ofCube (v : Test → E) (hsq : ∀ i, T.mul (v i) (v i) = T.one)
    (hcube : ∀ i y, T.mul (v i) (T.mul (v i) (T.mul (v i) y)) = T.mul (v i) y) :
    T.CanonRelations v where
  AA i y := by
    simp only [Aop, Uop, T.mul_smul, hsq, T.one_mul]
    module
  AC i y := by
    simp only [Aop, Uop, T.mul_smul, T.mul_sub, hsq, T.one_mul, hcube]
    module
  CA i y := by
    simp only [Aop, Uop, T.mul_smul, T.mul_sub, hsq, T.one_mul, hcube]
    module
  CC i y := by
    have h4 := hcube i (T.mul (v i) y)
    simp only [Uop, T.mul_smul, T.mul_sub, hsq, T.one_mul, hcube]
    module
  Cone i := by
    simp only [Uop, T.mul_one, hsq]
    module

end JTarget

/-! ## The relations in both targets -/

theorem specialSymmetry_mul_self (i : Test) :
    specialSymmetry i * specialSymmetry i = 1 := by
  have hP : universalTests i * universalTests i = universalTests i :=
    universalProjection_idempotent i
  simp only [specialSymmetry, sub_mul, _root_.mul_sub, smul_mul_assoc, mul_smul_comm, hP, one_mul,
    _root_.mul_one, smul_sub, smul_smul]
  module

theorem specialSymmetry_cube (i : Test) (y : UniversalProjectionAlgebra 4) :
    (specialTarget _).mul (specialSymmetry i) ((specialTarget _).mul (specialSymmetry i)
      ((specialTarget _).mul (specialSymmetry i) y)) =
      (specialTarget _).mul (specialSymmetry i) y := by
  have hr := specialSymmetry_mul_self i
  have hr' : ∀ z, specialSymmetry i * (specialSymmetry i * z) = z := fun z => by
    rw [← mul_assoc, hr, one_mul]
  simp only [specialTarget_mul, smul_mul_assoc, mul_smul_comm, _root_.mul_add, add_mul, mul_assoc,
    hr, hr', _root_.mul_one, smul_add, smul_smul]
  module

theorem special_canonRelations :
    (specialTarget (UniversalProjectionAlgebra 4)).CanonRelations specialSymmetry :=
  JTarget.CanonRelations.ofCube _ _ specialSymmetry_sq specialSymmetry_cube

/-- The native product as a `UnitalJordanProduct`. -/
def albertJordanProduct : UnitalJordanProduct Albert where
  product := LinearMap.mk₂ ℝ jordanMul jordanMul_add_left jordanMul_smul_left
    jordanMul_add_right jordanMul_smul_right
  unit := albertUnit
  commutative := jordanMul_comm
  unit_left := jordanMul_albertUnit_left
  jordan_identity x y := jordan_identity x y

theorem nativeSymmetry_cube (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (i : Test) (y : Albert) :
    jordanMul (nativeSymmetry p i) (jordanMul (nativeSymmetry p i)
      (jordanMul (nativeSymmetry p i) y)) = jordanMul (nativeSymmetry p i) y := by
  have h := albertJordanProduct.idempotent_leftMultiplication_cubic (p i) y (hp i)
  change (2 : ℝ) • jordanMul (p i) (jordanMul (p i) (jordanMul (p i) y)) -
    (3 : ℝ) • jordanMul (p i) (jordanMul (p i) y) + jordanMul (p i) y = 0 at h
  simp only [nativeSymmetry, jordanMul_sub_left, jordanMul_sub_right, jordanMul_smul_left,
    jordanMul_smul_right, jordanMul_albertUnit_left, jordanMul_albertUnit_right]
  linear_combination (norm := module) (4 : ℝ) • h

theorem native_canonRelations (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i) :
    albertTarget.CanonRelations (nativeSymmetry p) :=
  JTarget.CanonRelations.ofCube _ _ (nativeSymmetry_sq p hp) (nativeSymmetry_cube p hp)

/-- Contraction identity of lem:cer:h5:refl(b): for a symmetry `s`, `L_s U_s = L_s`, i.e.
`(U_s y) ∘ s = y ∘ s`.  With `s = ς(t)`, `y = ς(u)` and `ς(tut) = U_{ς(t)} ς(u)` this is
`ς(tut) ∘ ς(t) = ς(u) ∘ ς(t)`. -/
theorem native_reflection_contraction (p : Test → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (i : Test) (y : Albert) :
    jordanMul (quadraticMap (nativeSymmetry p i) y) (nativeSymmetry p i) =
      jordanMul y (nativeSymmetry p i) := by
  have h := (native_canonRelations p hp).AC i y
  simp only [JTarget.Aop, albertTarget_Uop] at h
  change (2 : ℝ) • jordanMul (nativeSymmetry p i) (quadraticMap (nativeSymmetry p i) y) =
    (2 : ℝ) • jordanMul (nativeSymmetry p i) y at h
  rw [jordanMul_comm, jordanMul_comm y]
  exact smul_right_injective Albert (two_ne_zero) h

/-- The same contraction for an arbitrary native symmetry `s` (`s ∘ s = e`, `L_s³ = L_s`),
e.g. `s = ς(t)` for any reflection `t`. -/
theorem native_symmetry_contraction (s y : Albert) (hs : jordanMul s s = albertUnit)
    (hcube : ∀ z, jordanMul s (jordanMul s (jordanMul s z)) = jordanMul s z) :
    jordanMul (quadraticMap s y) s = jordanMul y s := by
  rw [jordanMul_comm, jordanMul_comm y]
  unfold quadraticMap
  simp only [hs, jordanMul_albertUnit_left, jordanMul_sub_right, two_smul, jordanMul_add_right,
    hcube]
  abel

/-! ## Canonical symbols and normalization -/

/-- The letter of an operator. -/
def Op.letter : Op → Test
  | .A i => i
  | .C i => i

/-- Canonical symbols: adjacent operators on different letters, last operator an `A`. -/
def isSymbol : List Op → Bool
  | [] => true
  | [.A _] => true
  | [.C _] => false
  | o :: o' :: s => decide (o.letter ≠ o'.letter) && isSymbol (o' :: s)

/-- `C_i` applied to a canonical symbol whose first letter is not `i`. -/
def capC (i : Test) : List Op → (List Op →₀ ℝ)
  | [] => Finsupp.single [] 1
  | s => Finsupp.single (.C i :: s) 1

/-- One rewriting step: prepend an operator to a word, applying (eq:cer:h5:canon) if it meets an
operator on the same letter. -/
def prependOp (o : Op) : List Op → (List Op →₀ ℝ)
  | [] => match o with
    | .A i => Finsupp.single [.A i] 1
    | .C _ => Finsupp.single [] 1
  | o' :: s =>
    if o.letter = o'.letter then
      match o, o' with
      | .A i, .A _ => (2 : ℝ) • (Finsupp.single s 1 + capC i s)
      | .A i, .C _ => Finsupp.single (.A i :: s) 1
      | .C i, .A _ => Finsupp.single (.A i :: s) 1
      | .C _, .C _ => Finsupp.single s 1
    else Finsupp.single (o :: o' :: s) 1

/-- Normal form: a combination of canonical symbols. -/
def normalize : List Op → (List Op →₀ ℝ)
  | [] => Finsupp.single [] 1
  | o :: l => Finsupp.linearCombination ℝ (prependOp o) (normalize l)

namespace JTarget
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E)

/-- The operator `X_o` in the target. -/
def opAct (v : Test → E) : Op → E →ₗ[ℝ] E
  | .A i => T.AopLin (v i)
  | .C i => T.UopLin (v i)

theorem eval_opPoly_cons (v : Test → E) (o : Op) (l : List Op) :
    T.eval v (opPoly (o :: l)) = T.opAct v o (T.eval v (opPoly l)) := by
  cases o with
  | A i => rfl
  | C i => exact T.eval_opPoly_C v i l

theorem evalOps_single (v : Test → E) (l : List Op) :
    T.evalOps v (Finsupp.single l 1) = T.eval v (opPoly l) := by
  simp [evalOps]

theorem evalOps_capC (v : Test → E) (hR : T.CanonRelations v) (i : Test) (s : List Op) :
    T.evalOps v (capC i s) = T.Uop (v i) (T.eval v (opPoly s)) := by
  cases s with
  | nil =>
    simp only [capC, evalOps_single, opPoly, eval]
    exact (hR.Cone i).symm
  | cons o s =>
    change T.evalOps v (Finsupp.single (.C i :: o :: s) 1) = _
    rw [evalOps_single, T.eval_opPoly_C]
    rfl

theorem evalOps_prependOp (v : Test → E) (hR : T.CanonRelations v) (o : Op) (s : List Op) :
    T.evalOps v (prependOp o s) = T.opAct v o (T.eval v (opPoly s)) := by
  cases s with
  | nil =>
    cases o with
    | A i => simp only [prependOp, evalOps_single]; rfl
    | C i =>
      simp only [prependOp, evalOps_single, opPoly, eval]
      exact (hR.Cone i).symm
  | cons o' s =>
    by_cases h : o.letter = o'.letter
    · cases o with
      | A i =>
        cases o' with
        | A j =>
          simp only [Op.letter] at h; subst h
          simp only [prependOp, Op.letter, ite_true, map_smul, map_add, evalOps_single,
            T.evalOps_capC v hR]
          try simp only [T.eval_opPoly_cons]
          exact (hR.AA i _).symm
        | C j =>
          simp only [Op.letter] at h; subst h
          simp only [prependOp, Op.letter, ite_true, evalOps_single]
          try simp only [T.eval_opPoly_cons]
          exact (hR.AC i _).symm
      | C i =>
        cases o' with
        | A j =>
          simp only [Op.letter] at h; subst h
          simp only [prependOp, Op.letter, ite_true, evalOps_single]
          try simp only [T.eval_opPoly_cons]
          exact (hR.CA i _).symm
        | C j =>
          simp only [Op.letter] at h; subst h
          simp only [prependOp, Op.letter, ite_true, evalOps_single]
          try simp only [T.eval_opPoly_cons]
          exact (hR.CC i _).symm
    · simp only [prependOp, h, ite_false, evalOps_single]
      exact T.eval_opPoly_cons v o _

theorem evalOps_linearCombination_prependOp (v : Test → E) (hR : T.CanonRelations v) (o : Op)
    (F : List Op →₀ ℝ) :
    T.evalOps v (Finsupp.linearCombination ℝ (prependOp o) F) = T.opAct v o (T.evalOps v F) := by
  rw [Finsupp.apply_linearCombination]
  unfold evalOps
  rw [Finsupp.apply_linearCombination]
  exact congrArg (fun f => Finsupp.linearCombination ℝ f F)
    (funext fun s => T.evalOps_prependOp v hR o s)

/-- Normalization preserves the value. -/
theorem evalOps_normalize (v : Test → E) (hR : T.CanonRelations v) (l : List Op) :
    T.evalOps v (normalize l) = T.eval v (opPoly l) := by
  induction l with
  | nil => exact T.evalOps_single v []
  | cons o l ih =>
    simp only [normalize]
    rw [T.evalOps_linearCombination_prependOp v hR, ih, T.eval_opPoly_cons]

/-- Normalizing a combination preserves its value. -/
theorem evalOps_normalizeC (v : Test → E) (hR : T.CanonRelations v) (F : List Op →₀ ℝ) :
    T.evalOps v (Finsupp.linearCombination ℝ normalize F) = T.evalOps v F := by
  rw [Finsupp.apply_linearCombination]
  unfold evalOps
  exact congrArg (fun f => Finsupp.linearCombination ℝ f F)
    (funext fun l => T.evalOps_normalize v hR l)

end JTarget

/-! ## Normal forms are symbols with no more operators -/

/-- The set of canonical symbols with at most `n` operators. -/
def symbolsUpTo (n : ℕ) : Set (List Op) := {s | isSymbol s = true ∧ s.length ≤ n}

theorem isSymbol_tail (o : Op) (s : List Op) (h : isSymbol (o :: s) = true) : isSymbol s = true := by
  cases s with
  | nil => rfl
  | cons o' s =>
    simp only [isSymbol, Bool.and_eq_true] at h
    exact h.2

theorem single_mem_symbolsUpTo {s : List Op} {n : ℕ} (hs : isSymbol s = true) (hn : s.length ≤ n) :
    Finsupp.single s (1 : ℝ) ∈ Finsupp.supported ℝ ℝ (symbolsUpTo n) :=
  Finsupp.single_mem_supported ℝ 1 ⟨hs, hn⟩

theorem prependOp_mem (o : Op) (s : List Op) (hs : isSymbol s = true) :
    prependOp o s ∈ Finsupp.supported ℝ ℝ (symbolsUpTo (s.length + 1)) := by
  cases s with
  | nil =>
    cases o with
    | A i => exact single_mem_symbolsUpTo rfl (by simp)
    | C i => exact single_mem_symbolsUpTo rfl (by simp)
  | cons o' s =>
    have hs' : isSymbol s = true := isSymbol_tail o' s hs
    -- the first letter of `s` differs from the letter of `o'`
    have hfirst : ∀ o'' s', s = o'' :: s' → o'.letter ≠ o''.letter := by
      intro o'' s' hss
      subst hss
      simp only [isSymbol, Bool.and_eq_true, decide_eq_true_eq] at hs
      exact hs.1
    by_cases h : o.letter = o'.letter
    · cases o with
      | A i =>
        cases o' with
        | A j =>
          simp only [Op.letter] at h; subst h
          simp only [prependOp, Op.letter, ite_true]
          refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
          · exact single_mem_symbolsUpTo hs' (by simp; omega)
          · cases s with
            | nil => exact single_mem_symbolsUpTo rfl (by simp)
            | cons o'' s' =>
              have hne := hfirst o'' s' rfl
              refine single_mem_symbolsUpTo ?_ (by simp)
              simp only [isSymbol, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨by simpa [Op.letter] using hne, hs'⟩
        | C j =>
          simp only [Op.letter] at h; subst h
          simp only [prependOp, Op.letter, ite_true]
          cases s with
          | nil => exact single_mem_symbolsUpTo rfl (by simp)
          | cons o'' s' =>
            have hne := hfirst o'' s' rfl
            refine single_mem_symbolsUpTo ?_ (by simp)
            simp only [isSymbol, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨by simpa [Op.letter] using hne, hs'⟩
      | C i =>
        cases o' with
        | A j =>
          simp only [Op.letter] at h; subst h
          simp only [prependOp, Op.letter, ite_true]
          cases s with
          | nil => exact single_mem_symbolsUpTo rfl (by simp)
          | cons o'' s' =>
            have hne := hfirst o'' s' rfl
            refine single_mem_symbolsUpTo ?_ (by simp)
            simp only [isSymbol, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨by simpa [Op.letter] using hne, hs'⟩
        | C j =>
          simp only [Op.letter] at h; subst h
          simp only [prependOp, Op.letter, ite_true]
          exact single_mem_symbolsUpTo hs' (by simp; omega)
    · simp only [prependOp, h, ite_false]
      refine single_mem_symbolsUpTo ?_ (by simp)
      simp only [isSymbol, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h, hs⟩

theorem normalize_mem (l : List Op) :
    normalize l ∈ Finsupp.supported ℝ ℝ (symbolsUpTo l.length) := by
  induction l with
  | nil => exact single_mem_symbolsUpTo rfl le_rfl
  | cons o l ih =>
    simp only [normalize]
    rw [Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ ?_
    have hsl := (Finsupp.mem_supported ℝ _).1 ih hs
    refine Finsupp.supported_mono (s := symbolsUpTo (s.length + 1)) ?_ (prependOp_mem o s hsl.1)
    intro t ht
    have ht' : isSymbol t = true ∧ t.length ≤ s.length + 1 := ht
    have hsl' : isSymbol s = true ∧ s.length ≤ l.length := hsl
    show isSymbol t = true ∧ t.length ≤ (o :: l).length
    exact ⟨ht'.1, by simp only [List.length_cons]; omega⟩

/-- **(eq:cer:h5:goal)**: if `F` is a combination of canonical symbols with at most five
operators and `σ̂(F) = 0`, then `ν̂(F) = 0`, for any four atoms. -/
def SymbolTransfer5 : Prop :=
  ∀ p : Test → Albert, (∀ i, IsAtom (p i)) →
    ∀ F : List Op →₀ ℝ, F ∈ Finsupp.supported ℝ ℝ (symbolsUpTo 5) →
      opSpecial F = 0 → opAlbert p F = 0

/-- **Reduction proved**: the paper's goal for canonical symbols implies the goal for all operator
words with at most five operators. -/
theorem operatorTransfer_of_symbolTransfer (h : SymbolTransfer5) : OperatorWordTransfer5 := by
  intro p hp F hF h0
  have hpI : ∀ i, jordanMul (p i) (p i) = p i := fun i => (hp i).1
  set G := Finsupp.linearCombination ℝ normalize F with hG
  have hGmem : G ∈ Finsupp.supported ℝ ℝ (symbolsUpTo 5) := by
    rw [hG, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
    have hl5 : l.length ≤ 5 := (Finsupp.mem_supported ℝ _).1 hF hl
    exact Finsupp.supported_mono (s := symbolsUpTo l.length)
      (fun t (ht : t ∈ symbolsUpTo l.length) =>
        (⟨ht.1, le_trans ht.2 hl5⟩ : t ∈ symbolsUpTo 5)) (normalize_mem l)
  have hs : opSpecial G = opSpecial F :=
    (specialTarget _).evalOps_normalizeC specialSymmetry special_canonRelations F
  have ha : opAlbert p G = opAlbert p F :=
    albertTarget.evalOps_normalizeC (nativeSymmetry p) (native_canonRelations p hpI) F
  rw [← ha]
  exact h p hp G hGmem (by rw [hs]; exact h0)

/-- **Reduction proved**: the paper's (eq:cer:h5:goal) implies the horizon-five clause. -/
theorem horizonFive_of_symbolTransfer (h : SymbolTransfer5) : HorizonFiveClause :=
  horizonFive_of_operatorTransfer (operatorTransfer_of_symbolTransfer h)

end AlbertSequential.HorizonFive
