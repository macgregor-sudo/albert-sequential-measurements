/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Lemmas
public import NativeAtomReflections

/-! # Shapes and values of the top-degree symbols (for the final assembly of companion `app:cert:h5`)

* reduced-word combinatorics: `reducedB_append`, `reducedB_reverse`, `groupElt` and `reduceRW`
  facts (`groupElt_reduceRW`, `reduceRW_append`, cancellation of `v^R v`);
* symbol shapes: a symbol of length at most five has degree at most nine; degree nine means
  `C_{u_1}⋯C_{u_4}A_x 1`; degree eight means `C_U A_x C_V A_y 1` with `|U| + |V| = 3`; the
  computable words `palWord` and `gWord` and reflections `topRefls`;
* values (eq:cer:h5:twoA): `σ̂(C_U A_x 1) = 2·UxU^R`, `σ̂(C_U A_x C_V A_y 1) = 4[g]` with
  `g = U x V y V^R U^R`, and `ν̂(C_U A_x C_V A_y 1) = 4 ς(U,x) ∘ ς(UV, y)` (by covariance of the
  native reflections `U_{s_i}`, which are Jordan automorphisms). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## Reduced words -/

theorem reducedB_append (l m : List Test) :
    reducedB (l ++ m) = true ↔
      reducedB l = true ∧ reducedB m = true ∧
        ∀ a b, l.getLast? = some a → m.head? = some b → a ≠ b := by
  induction l with
  | nil => simp [reducedB]
  | cons a l ih =>
    cases l with
    | nil =>
      cases m with
      | nil => simp [reducedB]
      | cons b m =>
        simp only [List.cons_append, List.nil_append, reducedB, Bool.and_eq_true,
          decide_eq_true_eq, List.getLast?_singleton, List.head?_cons, Option.some.injEq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨trivial, h2, fun x y hx hy => hx ▸ hy ▸ h1⟩
        · rintro ⟨-, h2, h3⟩; exact ⟨h3 a b rfl rfl, h2⟩
    | cons b l =>
      simp only [List.cons_append, reducedB, Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
      rw [ih]
      simp only [List.getLast?_cons_cons]
      tauto

theorem reducedB_reverse (l : List Test) (h : reducedB l = true) : reducedB l.reverse = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, reducedB_append]
    refine ⟨ih (reducedB_tail a l h), rfl, ?_⟩
    intro x y hx hy
    simp only [List.head?_cons, Option.some.injEq] at hy
    subst hy
    rw [List.getLast?_reverse] at hx
    cases l with
    | nil => simp at hx
    | cons b l =>
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx
      simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact fun e => h.1 e.symm

theorem reducedB_reverse_iff (l : List Test) : reducedB l.reverse = true ↔ reducedB l = true :=
  ⟨fun h => by simpa using reducedB_reverse _ h, reducedB_reverse l⟩

/-- An even reduced word of length eight is not a palindrome. -/
theorem reduced_length_eight_ne_reverse (l : List Test) (h : reducedB l = true)
    (hl : l.length = 8) : l.reverse ≠ l := by
  match l, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
    intro hr
    simp only [reducedB, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.cons.injEq] at hr
    exact h.2.2.2.1 hr.2.2.2.1.symm

theorem specialSymmetry_mul_self' (i : Test) (z : UniversalProjectionAlgebra 4) :
    specialSymmetry i * (specialSymmetry i * z) = z := by
  rw [← mul_assoc, specialSymmetry_mul_self, one_mul]

theorem groupElt_flipWord (i : Test) (g : RW) :
    groupElt (flipWord i g).1 = specialSymmetry i * groupElt g.1 := by
  unfold flipWord
  split
  · rename_i h
    obtain ⟨l, hl⟩ := g
    cases l with
    | nil => simp at h
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      simp only [List.tail_cons, groupElt_cons, specialSymmetry_mul_self']
  · simp only [groupElt_cons]

/-- The group element only depends on the reduced form. -/
theorem groupElt_reduceRW (l : List Test) : groupElt (reduceRW l).1 = groupElt l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [reduceRW, groupElt_flipWord, ih, groupElt_cons]

theorem groupElt_reverse_mul (l : List Test) : groupElt l.reverse * groupElt l = 1 := by
  induction l with
  | nil => simp [groupElt]
  | cons a l ih =>
    rw [List.reverse_cons, groupElt_append, groupElt_cons]
    simp only [groupElt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      _root_.mul_one] at ih ⊢
    rw [mul_assoc, ← mul_assoc (specialSymmetry a), specialSymmetry_mul_self, one_mul, ih]

theorem reduceRW_append (l m : List Test) : reduceRW (l ++ m) = l.foldr flipWord (reduceRW m) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append, reduceRW, ih, List.foldr_cons]

theorem foldr_flipWord_reverse_cancel (l : List Test) (z : RW) :
    l.reverse.foldr flipWord (l.foldr flipWord z) = z := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_cons, List.foldr_nil,
      flipWord_flipWord, ih]

theorem flipWord_length_cases (i : Test) (g : RW) :
    (flipWord i g).1.length + 1 = g.1.length ∨
      ((flipWord i g).1 = i :: g.1 ∧ g.1.head? ≠ some i) := by
  unfold flipWord
  split
  · rename_i h
    left
    obtain ⟨l, hl⟩ := g
    cases l with
    | nil => simp at h
    | cons a l => simp
  · rename_i h
    right
    exact ⟨rfl, h⟩

/-- A word whose reduced form is as long as the word is reduced. -/
theorem reducedB_of_reduceRW_length (l : List Test) (h : (reduceRW l).1.length = l.length) :
    reducedB l = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hle := reduceRW_length l
    rw [reduceRW] at h
    rcases flipWord_length_cases a (reduceRW l) with h1 | ⟨h1, h2⟩
    · simp only [List.length_cons] at h; omega
    · rw [h1] at h
      simp only [List.length_cons, add_left_inj] at h
      have hl := ih h
      rw [reduceRW_of_reduced l hl] at h2
      exact reducedB_cons a l hl h2

/-! ## Symbol shapes -/

/-- Letters of the leading `C`-operators. -/
def cPrefix : List Op → List Test
  | .C i :: l => i :: cPrefix l
  | _ => []

/-- What follows the leading `C`-operators. -/
def afterC : List Op → List Op
  | .C _ :: l => afterC l
  | l => l

theorem cPrefix_afterC (l : List Op) : (cPrefix l).map Op.C ++ afterC l = l := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o with
    | A i => rfl
    | C i => simp only [cPrefix, afterC, List.map_cons, List.cons_append, ih]

theorem opDeg_append (l m : List Op) : opDeg (l ++ m) = opDeg l + opDeg m := by
  induction l with
  | nil => simp [opDeg]
  | cons o l ih => cases o <;> simp only [List.cons_append, opDeg, ih] <;> omega

theorem opDeg_mapC (U : List Test) : opDeg (U.map Op.C) = 2 * U.length := by
  induction U with
  | nil => rfl
  | cons a U ih => simp only [List.map_cons, opDeg, ih, List.length_cons]; omega

theorem opDeg_le (l : List Op) : opDeg l ≤ 2 * l.length := by
  induction l with
  | nil => simp [opDeg]
  | cons o l ih => cases o <;> simp only [opDeg, List.length_cons] <;> omega

/-- Decomposition of a nonempty symbol as `C_U A_x (rest)`. -/
theorem symbol_decomp (s : List Op) (hs : isSymbol s = true) (hne : s ≠ []) :
    ∃ U x rest, s = U.map Op.C ++ Op.A x :: rest ∧ isSymbol rest = true ∧
      reducedB (U ++ [x]) = true ∧ ∀ o r, rest = o :: r → o.letter ≠ x := by
  induction s with
  | nil => exact absurd rfl hne
  | cons o s ih =>
    cases o with
    | A x =>
      refine ⟨[], x, s, rfl, isSymbol_tail _ s hs, rfl, ?_⟩
      rintro o r rfl
      simp only [isSymbol, Bool.and_eq_true, decide_eq_true_eq] at hs
      exact fun e => hs.1 (by simpa [Op.letter] using e.symm)
    | C u =>
      cases s with
      | nil => simp [isSymbol] at hs
      | cons o' s' =>
        have hs' := isSymbol_tail _ _ hs
        obtain ⟨U, x, rest, hU, hrest, hred, hx⟩ := ih hs' (by simp)
        have hfirst : (U ++ [x]).head? = some o'.letter := by
          cases U with
          | nil =>
            simp only [List.map_nil, List.nil_append, List.cons.injEq] at hU
            rw [hU.1]; simp [Op.letter]
          | cons b U =>
            simp only [List.map_cons, List.cons_append, List.cons.injEq] at hU
            rw [hU.1]; simp [Op.letter]
        refine ⟨u :: U, x, rest, by rw [hU]; rfl, hrest, ?_, hx⟩
        simp only [isSymbol, Bool.and_eq_true, decide_eq_true_eq] at hs
        rw [List.cons_append]
        refine reducedB_cons u _ hred ?_
        rw [hfirst]
        simpa [Op.letter] using fun e => hs.1 e.symm

theorem symbol_opDeg_le (s : List Op) (hs : isSymbol s = true) (hne : s ≠ []) :
    opDeg s + 1 ≤ 2 * s.length := by
  obtain ⟨U, x, rest, rfl, -, -, -⟩ := symbol_decomp s hs hne
  have := opDeg_le rest
  simp only [opDeg_append, opDeg_mapC, opDeg, List.length_append, List.length_map,
    List.length_cons]
  omega

/-- Degree-nine symbols have the shape `C_{u_1}⋯C_{u_4} A_x`. -/
theorem symbol_deg_nine (s : List Op) (hs : isSymbol s = true) (hl : s.length ≤ 5)
    (h9 : opDeg s = 9) :
    ∃ (U : List Test) (x : Test), s = U.map Op.C ++ [Op.A x] ∧ U.length = 4 ∧ reducedB (U ++ [x]) = true := by
  have hne : s ≠ [] := by rintro rfl; simp [opDeg] at h9
  obtain ⟨U, x, rest, rfl, hrest, hred, -⟩ := symbol_decomp s hs hne
  simp only [opDeg_append, opDeg_mapC, opDeg, List.length_append, List.length_map,
    List.length_cons] at h9 hl
  cases rest with
  | nil => exact ⟨U, x, rfl, by simp [opDeg] at h9; omega, hred⟩
  | cons o r =>
    have := symbol_opDeg_le (o :: r) hrest (by simp)
    simp only [List.length_cons] at this hl
    omega

/-- Degree-eight symbols have the shape `C_U A_x C_V A_y` with `|U| + |V| = 3`. -/
theorem symbol_deg_eight (s : List Op) (hs : isSymbol s = true) (hl : s.length ≤ 5)
    (h8 : opDeg s = 8) :
    ∃ (U : List Test) (x : Test) (V : List Test) (y : Test),
      s = U.map Op.C ++ Op.A x :: (V.map Op.C ++ [Op.A y]) ∧
      U.length + V.length = 3 := by
  have hne : s ≠ [] := by rintro rfl; simp [opDeg] at h8
  obtain ⟨U, x, rest, rfl, hrest, -, -⟩ := symbol_decomp s hs hne
  simp only [opDeg_append, opDeg_mapC, opDeg, List.length_append, List.length_map,
    List.length_cons] at h8 hl
  cases rest with
  | nil => simp [opDeg] at h8; omega
  | cons o r =>
    simp only [List.length_cons] at hl
    obtain ⟨V, y, rest2, hV, hrest2, -, -⟩ := symbol_decomp (o :: r) hrest (by simp)
    have hlen := congrArg List.length hV
    rw [hV] at h8 ⊢
    simp only [opDeg_append, opDeg_mapC, opDeg, List.length_append, List.length_map,
      List.length_cons] at h8 hlen
    cases rest2 with
    | nil => exact ⟨U, x, V, y, rfl, by simp [opDeg] at h8; omega⟩
    | cons o2 r2 =>
      have := symbol_opDeg_le (o2 :: r2) hrest2 (by simp)
      simp only [List.length_cons] at this hlen
      omega

/-- Symbols of length at most five have degree at most nine. -/
theorem symbol_opDeg_le_nine (s : List Op) (hs : isSymbol s = true) (hl : s.length ≤ 5) :
    opDeg s ≤ 9 := by
  by_cases hne : s = []
  · subst hne; simp [opDeg]
  · have := symbol_opDeg_le s hs hne; omega

/-! ## Values of top-degree symbols -/

theorem specialEval_opPoly_Cprefix (U : List Test) (l : List Op) :
    specialEval (opPoly (U.map Op.C ++ l)) =
      groupElt U * specialEval (opPoly l) * groupElt U.reverse := by
  induction U with
  | nil => simp [groupElt]
  | cons a U ih =>
    change (specialTarget _).eval specialSymmetry (JPoly.U _ _) = _
    rw [JTarget.eval_U, specialTarget_Uop]
    change specialSymmetry a * specialEval (opPoly (U.map Op.C ++ l)) * specialSymmetry a = _
    rw [ih, List.reverse_cons, groupElt_append, groupElt_cons]
    simp only [groupElt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      _root_.mul_one, mul_assoc]

theorem specialEval_opPoly_A (x : Test) (l : List Op) :
    specialEval (opPoly (Op.A x :: l)) =
      specialSymmetry x * specialEval (opPoly l) + specialEval (opPoly l) * specialSymmetry x := by
  change (specialTarget _).Aop (specialSymmetry x) (specialEval (opPoly l)) = _
  rw [specialTarget_Aop_eq]

/-- The palindrome `U x U^R` of a degree-nine symbol. -/
def palWord (U : List Test) (x : Test) : List Test := U ++ [x] ++ U.reverse

theorem specialEval_deg_nine (U : List Test) (x : Test) :
    specialEval (opPoly (U.map Op.C ++ [Op.A x])) = (2 : ℝ) • groupElt (palWord U x) := by
  rw [specialEval_opPoly_Cprefix, specialEval_opPoly_A]
  change groupElt U * (specialSymmetry x * 1 + 1 * specialSymmetry x) * groupElt U.reverse = _
  simp only [_root_.mul_one, one_mul, palWord, groupElt_append]
  simp only [groupElt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    _root_.mul_one, _root_.mul_add, add_mul]
  module

theorem palWord_reduced (U : List Test) (x : Test) (h : reducedB (U ++ [x]) = true) :
    reducedB (palWord U x) = true := by
  unfold palWord
  rw [reducedB_append]
  refine ⟨h, reducedB_reverse U ((reducedB_append U [x]).1 h).1, ?_⟩
  intro a b ha hb
  have hax : x = a := by simpa using ha
  subst hax
  rw [List.head?_reverse] at hb
  have h3 := ((reducedB_append U [x]).1 h).2.2
  exact fun e => h3 b x hb rfl e.symm

theorem palWord_injective (U U' : List Test) (x x' : Test) (hU : U.length = 4)
    (hU' : U'.length = 4) (h : palWord U x = palWord U' x') : U = U' ∧ x = x' := by
  match U, U', hU, hU' with
  | [a, b, c, d], [a', b', c', d'], _, _ =>
    simp only [palWord, List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
      List.cons.injEq] at h
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
    subst h1 h2 h3 h4 h5
    exact ⟨rfl, rfl⟩

/-- The word `g = U x V y V^R U^R` of a degree-eight symbol. -/
def gWord (U : List Test) (x : Test) (V : List Test) (y : Test) : List Test :=
  U ++ [x] ++ V ++ [y] ++ V.reverse ++ U.reverse

theorem specialEval_deg_eight (U : List Test) (x : Test) (V : List Test) (y : Test) :
    specialEval (opPoly (U.map Op.C ++ Op.A x :: (V.map Op.C ++ [Op.A y]))) =
      (4 : ℝ) • classElt (gWord U x V y) := by
  rw [specialEval_opPoly_Cprefix, specialEval_opPoly_A, specialEval_opPoly_Cprefix,
    specialEval_opPoly_A]
  change groupElt U * (specialSymmetry x * (groupElt V * (specialSymmetry y * 1 +
      1 * specialSymmetry y) * groupElt V.reverse) + (groupElt V * (specialSymmetry y * 1 +
      1 * specialSymmetry y) * groupElt V.reverse) * specialSymmetry x) * groupElt U.reverse = _
  simp only [classElt, gWord, List.reverse_append, List.reverse_reverse, List.reverse_cons,
    List.reverse_nil, List.nil_append, groupElt_append, List.append_assoc]
  simp only [groupElt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    _root_.mul_one, one_mul, _root_.mul_add, add_mul, mul_assoc, smul_add, smul_smul]
  module

/-! ## Native values -/

/-- `ρ(U) y = U_{s_{u_1}} ⋯ U_{s_{u_k}} y`. -/
def nativeRho (p : Test → Albert) (U : List Test) (y : Albert) : Albert :=
  U.foldr (fun a z => quadraticMap (nativeSymmetry p a) z) y

theorem varsigma_eq (p : Test → Albert) (t : Refl) :
    varsigma p t = nativeRho p t.v (nativeSymmetry p t.i) := rfl

theorem nativeRho_append (p : Test → Albert) (U V : List Test) (y : Albert) :
    nativeRho p (U ++ V) y = nativeRho p U (nativeRho p V y) := by
  simp [nativeRho, List.foldr_append]

theorem nativeRho_jordanMul (p : Test → Albert) (hp : ∀ i, IsAtom (p i)) (U : List Test)
    (a b : Albert) :
    nativeRho p U (jordanMul a b) = jordanMul (nativeRho p U a) (nativeRho p U b) := by
  induction U with
  | nil => rfl
  | cons u U ih =>
    simp only [nativeRho, List.foldr_cons] at ih ⊢
    rw [ih]
    have h := (atomReflectionAutomorphism (p u) (hp u)).preserves_product
      (U.foldr (fun a z => quadraticMap (nativeSymmetry p a) z) a)
      (U.foldr (fun a z => quadraticMap (nativeSymmetry p a) z) b)
    simp only [atomReflectionAutomorphism_apply] at h
    exact h

theorem quadraticMap_smul_right (a : Albert) (r : ℝ) (y : Albert) :
    quadraticMap a (r • y) = r • quadraticMap a y := by
  unfold quadraticMap
  simp only [jordanMul_smul_right, two_smul]
  module

theorem nativeRho_smul (p : Test → Albert) (U : List Test) (r : ℝ) (y : Albert) :
    nativeRho p U (r • y) = r • nativeRho p U y := by
  induction U with
  | nil => rfl
  | cons u U ih =>
    simp only [nativeRho, List.foldr_cons] at ih ⊢
    rw [ih, quadraticMap_smul_right]

theorem albertEval_opPoly_Cprefix (p : Test → Albert) (U : List Test) (l : List Op) :
    albertEval p (opPoly (U.map Op.C ++ l)) = nativeRho p U (albertEval p (opPoly l)) := by
  induction U with
  | nil => rfl
  | cons a U ih =>
    change albertTarget.eval (nativeSymmetry p) (JPoly.U _ _) = _
    rw [JTarget.eval_U, albertTarget_Uop]
    change quadraticMap (nativeSymmetry p a) (albertEval p (opPoly (U.map Op.C ++ l))) = _
    rw [ih]
    rfl

/-- The two reflections `(U, x)` and `(UV, y)` of a degree-eight symbol. -/
def topRefls (U : List Test) (x : Test) (V : List Test) (y : Test) : Refl × Refl :=
  (⟨U, x⟩, ⟨U ++ V, y⟩)

theorem albertEval_deg_eight (p : Test → Albert) (hp : ∀ i, IsAtom (p i)) (U : List Test)
    (x : Test) (V : List Test) (y : Test) :
    albertEval p (opPoly (U.map Op.C ++ Op.A x :: (V.map Op.C ++ [Op.A y]))) =
      (4 : ℝ) • jordanMul (varsigma p (topRefls U x V y).1) (varsigma p (topRefls U x V y).2) := by
  rw [albertEval_opPoly_Cprefix]
  change nativeRho p U (albertTarget.Aop (nativeSymmetry p x)
    (albertEval p (opPoly (V.map Op.C ++ [Op.A y])))) = _
  rw [albertEval_opPoly_Cprefix]
  change nativeRho p U ((2 : ℝ) • jordanMul (nativeSymmetry p x)
    (nativeRho p V ((2 : ℝ) • jordanMul (nativeSymmetry p y) albertUnit))) = _
  simp only [jordanMul_albertUnit_right, nativeRho_smul, jordanMul_smul_right, smul_smul]
  rw [nativeRho_jordanMul p hp, topRefls, varsigma_eq, varsigma_eq, nativeRho_append]
  norm_num

theorem reduceRW_cancel (A U B : List Test) :
    reduceRW (A ++ (U.reverse ++ (U ++ B))) = reduceRW (A ++ B) := by
  rw [reduceRW_append, reduceRW_append U.reverse, reduceRW_append U,
    foldr_flipWord_reverse_cancel, ← reduceRW_append]

/-- The product of the two reflections is `g` in `G`, and its inverse is `g^R`. -/
theorem topRefls_word (U : List Test) (x : Test) (V : List Test) (y : Test) :
    reduceRW ((topRefls U x V y).1.word ++ (topRefls U x V y).2.word) =
        reduceRW (gWord U x V y) ∧
    reduceRW ((topRefls U x V y).1.word ++ (topRefls U x V y).2.word).reverse =
        reduceRW (gWord U x V y).reverse := by
  constructor
  · have h := reduceRW_cancel (U ++ [x]) U (V ++ [y] ++ V.reverse ++ U.reverse)
    simp only [topRefls, Refl.word, gWord, List.reverse_append, List.append_assoc,
      List.singleton_append, List.cons_append] at h ⊢
    exact h
  · have h := reduceRW_cancel (U ++ V ++ [y] ++ V.reverse) U ([x] ++ U.reverse)
    simp only [topRefls, Refl.word, gWord, List.reverse_append, List.reverse_reverse,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc,
      List.singleton_append, List.cons_append] at h ⊢
    exact h

theorem classElt_topRefls (U : List Test) (x : Test) (V : List Test) (y : Test) :
    classElt ((topRefls U x V y).1.word ++ (topRefls U x V y).2.word) = classElt (gWord U x V y) := by
  have h := topRefls_word U x V y
  unfold classElt
  rw [← groupElt_reduceRW ((topRefls U x V y).1.word ++ _), h.1, groupElt_reduceRW,
    ← groupElt_reduceRW (List.reverse _), h.2, groupElt_reduceRW]

end AlbertSequential.HorizonFive
