/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ScheduleMatchingRationalInvolution
public import ComplexWindowDeterminantAndMax
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! The sign-graded rational Albert form in Appendix C.5 and the exact rational
probabilities of M for arbitrary signed histories. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlbertSequential.MatchingModels

open FiveTest NativeAnalysis

def horizonRationalCoordinates (x : Albert) : Prop := ∃ q : QA, castA q = x

/-- True denotes the odd eigenspace, and false the even eigenspace. -/
def horizonRationalParity (odd : Bool) (x : Albert) : Prop :=
  horizonRationalCoordinates x ∧ horizonRationalBeta.linearEquiv x = if odd then -x else x

/-- The exact rational form `J₊ + √2 J₋` inside the native real Albert algebra. -/
def horizonRationalForm (x : Albert) : Prop :=
  ∃ u v : Albert, horizonRationalParity false u ∧ horizonRationalParity true v ∧
    u + Real.sqrt 2 • v = x

private theorem coordinate_add {x y : Albert} (hx : horizonRationalCoordinates x)
    (hy : horizonRationalCoordinates y) : horizonRationalCoordinates (x + y) := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨r, rfl⟩ := hy
  exact ⟨q.add r, castA_add q r⟩

private theorem coordinate_smul {x : Albert} (hx : horizonRationalCoordinates x) (r : ℚ) :
    horizonRationalCoordinates ((r : ℝ) • x) := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨q.smul r, castA_smul r q⟩

private theorem coordinate_jordan {x y : Albert} (hx : horizonRationalCoordinates x)
    (hy : horizonRationalCoordinates y) : horizonRationalCoordinates (jordanMul x y) := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨r, rfl⟩ := hy
  exact ⟨q.jmul r, castA_jmul q r⟩

private theorem castA_zero_horizon : castA QA.zero = 0 := by
  apply albert_ext' <;> simp [castA, QA.zero, castO_zero] <;> rfl

private theorem parity_zero (a : Bool) : horizonRationalParity a 0 := by
  refine ⟨⟨QA.zero, castA_zero_horizon⟩, ?_⟩
  cases a <;> simp

theorem horizonRationalParity_add {a : Bool} {x y : Albert}
    (hx : horizonRationalParity a x) (hy : horizonRationalParity a y) :
    horizonRationalParity a (x + y) := by
  refine ⟨coordinate_add hx.1 hy.1, ?_⟩
  rw [map_add, hx.2, hy.2]
  cases a <;> simp [add_comm]

theorem horizonRationalParity_smul {a : Bool} {x : Albert} (hx : horizonRationalParity a x) (r : ℚ) :
    horizonRationalParity a ((r : ℝ) • x) := by
  refine ⟨coordinate_smul hx.1 r, ?_⟩
  rw [map_smul, hx.2]
  cases a <;> simp

theorem horizonRationalParity_jordan {a b : Bool} {x y : Albert}
    (hx : horizonRationalParity a x) (hy : horizonRationalParity b y) :
    horizonRationalParity (Bool.xor a b) (jordanMul x y) := by
  refine ⟨coordinate_jordan hx.1 hy.1, ?_⟩
  rw [horizonRationalBeta.preserves_product, hx.2, hy.2]
  cases a <;> cases b <;> simp [jordanMul_neg_left, jordanMul_neg_right]

theorem horizonRationalForm_of_even {x : Albert} (hx : horizonRationalParity false x) :
    horizonRationalForm x :=
  ⟨x, 0, hx, parity_zero true, by simp⟩

theorem horizonRationalForm_add {x y : Albert} (hx : horizonRationalForm x) (hy : horizonRationalForm y) :
    horizonRationalForm (x + y) := by
  obtain ⟨u,v,hu,hv,rfl⟩ := hx
  obtain ⟨z,w,hz,hw,rfl⟩ := hy
  refine ⟨u + z, v + w, horizonRationalParity_add hu hz, horizonRationalParity_add hv hw, ?_⟩
  rw [smul_add]
  abel

theorem horizonRationalForm_smul {x : Albert} (hx : horizonRationalForm x) (r : ℚ) :
    horizonRationalForm ((r : ℝ) • x) := by
  obtain ⟨u,v,hu,hv,rfl⟩ := hx
  refine ⟨_, _, horizonRationalParity_smul hu r, horizonRationalParity_smul hv r, ?_⟩
  rw [smul_add, smul_smul, smul_smul, mul_comm (Real.sqrt 2)]

theorem horizonRationalForm_sub {x y : Albert} (hx : horizonRationalForm x) (hy : horizonRationalForm y) :
    horizonRationalForm (x - y) := by
  have hn := horizonRationalForm_smul hy (-1)
  have hneg : horizonRationalForm (-y) := by simpa using hn
  simpa only [sub_eq_add_neg] using horizonRationalForm_add hx hneg

/-- Parities multiply and the square of the odd scale is the rational number 2. -/
theorem horizonRationalForm_jordan {x y : Albert}
    (hx : horizonRationalForm x) (hy : horizonRationalForm y) :
    horizonRationalForm (jordanMul x y) := by
  obtain ⟨u,v,hu,hv,rfl⟩ := hx
  obtain ⟨z,w,hz,hw,rfl⟩ := hy
  have h2 := horizonRationalParity_smul (horizonRationalParity_jordan hv hw) 2
  have he : horizonRationalParity false (jordanMul u z + (2 : ℝ) • jordanMul v w) :=
    horizonRationalParity_add (horizonRationalParity_jordan hu hz) (by simpa using h2)
  have ho : horizonRationalParity true (jordanMul u w + jordanMul v z) :=
    horizonRationalParity_add (horizonRationalParity_jordan hu hw) (horizonRationalParity_jordan hv hz)
  refine ⟨_, _, he, ho, ?_⟩
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [jordanMul_add_left, jordanMul_add_right, jordanMul_smul_left, jordanMul_smul_right,
    smul_smul, hsq, smul_add]
  abel

theorem horizonRationalForm_quadratic {x y : Albert}
    (hx : horizonRationalForm x) (hy : horizonRationalForm y) :
    horizonRationalForm (quadraticMap x y) := by
  rw [quadraticMap, two_nsmul]
  have hxy := horizonRationalForm_jordan hx (horizonRationalForm_jordan hx hy)
  exact horizonRationalForm_sub (horizonRationalForm_add hxy hxy)
    (horizonRationalForm_jordan (horizonRationalForm_jordan hx hx) hy)

theorem horizonRationalForm_unit : horizonRationalForm albertUnit :=
  horizonRationalForm_of_even ⟨⟨QA.unit, castA_unit⟩, horizonRationalBeta.preserves_unit⟩

theorem horizonRationalForm_trace {x : Albert} (hx : horizonRationalForm x) :
    ∃ r : ℚ, (r : ℝ) = albertTrace x := by
  obtain ⟨u,v,hu,hv,rfl⟩ := hx
  obtain ⟨q,rfl⟩ := hu.1
  have hneg : horizonRationalBeta.linearEquiv v = -v := hv.2
  have hvzero : albertTrace v = 0 := by
    have he := horizonRationalBeta.preserves_trace v
    rw [hneg, ← neg_one_smul ℝ v, albertTrace_smul] at he
    linarith
  exact ⟨q.tr, by rw [albertTrace_add, albertTrace_smul, hvzero, mul_zero, add_zero, castA_tr]⟩

theorem horizonRationalForm_e3 : horizonRationalForm ((1 / 3 : ℝ) • albertUnit) := by
  simpa using horizonRationalForm_smul horizonRationalForm_unit (1 / 3)

theorem horizonRationalForm_nativeBranchState {ι : Type*} (p : ι → Albert)
    (hp : ∀ i, horizonRationalForm (p i)) {ρ : Albert} (hρ : horizonRationalForm ρ) (w : Word ι) :
    horizonRationalForm (nativeBranchState p ρ w) := by
  induction w generalizing ρ with
  | nil => exact hρ
  | cons a w ih =>
    rw [nativeBranchState_cons]
    apply ih
    apply horizonRationalForm_quadratic _ hρ
    rcases a with ⟨i,b⟩
    cases b
    · exact horizonRationalForm_sub horizonRationalForm_unit (hp i)
    · exact hp i

/-- The rational coordinates of the even parts of the four paper atoms. -/
def horizonMRationalEven : Fin 4 → QA :=
  ![QA.diag0,
    ⟨1/3, 2/3, 0, QO.zero, QO.zero, QO.zero⟩,
    (QA.dyad QO.one QO.I QO.one).smul (1/3),
    (QA.dyad QO.one QO.J QO.L).smul (1/3)]

/-- The rational, unscaled odd part occurs only in the B upper off-diagonal slot. -/
def horizonMRationalOdd : Fin 4 → QA :=
  ![QA.zero, ⟨0,0,0,QO.scalar (1/3),QO.zero,QO.zero⟩, QA.zero, QA.zero]

theorem horizonMRationalEven_parity (i : Fin 4) :
    horizonRationalParity false (castA (horizonMRationalEven i)) := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  have h : rationalHorizonBeta (horizonMRationalEven i) = horizonMRationalEven i := by
    fin_cases i <;> decide +kernel
  simpa only [castA_horizonBeta, Bool.false_eq_true, ↓reduceIte] using congrArg castA h

theorem horizonMRationalOdd_parity (i : Fin 4) :
    horizonRationalParity true (castA (horizonMRationalOdd i)) := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  have h : rationalHorizonBeta (horizonMRationalOdd i) = (horizonMRationalOdd i).smul (-1) := by
    fin_cases i <;> decide +kernel
  simpa [castA_horizonBeta, castA_smul] using congrArg castA h

private theorem octDyad_scaled (r : ℝ) (v : Fin 3 → Octonion) :
    octDyad (fun i => r • v i) = r ^ 2 • octDyad v := by
  have hd (i : Fin 3) :
      (octDyad (fun i => r • v i)).1 i = (r ^ 2 • octDyad v).1 i := by
    rw [albert_smul_fst']
    exact octNormSq_smul r (v i)
  have ho (x y : Octonion) :
      octonionMul (r • x) (octonionConj (r • y)) = r ^ 2 • octonionMul x (octonionConj y) := by
    rw [octonionConj_smul, octonionMul_smul_left, octonionMul_smul_right, smul_smul, pow_two]
  apply albert_ext' (hd 0) (hd 1) (hd 2)
  · rw [albert_smul_snd']; exact ho (v 0) (v 1)
  · rw [albert_smul_snd']; exact ho (v 0) (v 2)
  · rw [albert_smul_snd']; exact ho (v 1) (v 2)

private theorem max_normalization_square : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]

private theorem max_scalarOne (r : ℝ) : octonionScalar r = r • octOne := by
  rw [octonionScalar_eq_smul r, octOne_eq_scalar]

private theorem maxConfig_B :
    maximizerConfig 1 = (1 / 3 : ℝ) • octDyad ![octOne, octonionScalar (Real.sqrt 2), 0] := by
  change octDyad ![octonionScalar (1 / Real.sqrt 3), octonionScalar (Real.sqrt 2 / Real.sqrt 3), 0] = _
  have hvec :
      (![octonionScalar (1 / Real.sqrt 3), octonionScalar (Real.sqrt 2 / Real.sqrt 3), 0] :
        Fin 3 → Octonion) =
      fun i => (1 / Real.sqrt 3) • (![octOne, octonionScalar (Real.sqrt 2), 0] : Fin 3 → Octonion) i := by
    funext i
    fin_cases i
    · exact max_scalarOne _
    · change octonionScalar (Real.sqrt 2 / Real.sqrt 3) =
        (1 / Real.sqrt 3) • octonionScalar (Real.sqrt 2)
      rw [max_scalarOne (Real.sqrt 2 / Real.sqrt 3), max_scalarOne (Real.sqrt 2),
        smul_smul, mul_comm, mul_one_div]
    · exact (smul_zero _).symm
  rw [hvec, octDyad_scaled, max_normalization_square]

private theorem maxConfig_C :
    maximizerConfig 2 = (1 / 3 : ℝ) • octDyad ![octOne, octI, octOne] := by
  change octDyad ![octonionScalar (1 / Real.sqrt 3), octonionScalar 0 + (1 / Real.sqrt 3) • octI,
    octonionScalar (1 / Real.sqrt 3)] = _
  rw [octonionScalar_zero, zero_add, max_scalarOne (1 / Real.sqrt 3)]
  have hvec :
      (![ (1 / Real.sqrt 3) • octOne, (1 / Real.sqrt 3) • octI, (1 / Real.sqrt 3) • octOne ] :
        Fin 3 → Octonion) =
      fun i => (1 / Real.sqrt 3) • (![octOne, octI, octOne] : Fin 3 → Octonion) i := by
    funext i; fin_cases i <;> rfl
  rw [hvec, octDyad_scaled, max_normalization_square]

private theorem maxConfig_D :
    maximizerConfig 3 = (1 / 3 : ℝ) • octDyad ![octOne, octJ, octL] := by
  change octDyad ![octonionScalar (1 / Real.sqrt 3),
    octonionScalar 0 + (0 : ℝ) • octI + (1 / Real.sqrt 3) • octJ, (1 / Real.sqrt 3) • octL] = _
  simp only [octonionScalar_zero, zero_smul, zero_add, max_scalarOne (1 / Real.sqrt 3)]
  have hvec :
      (![ (1 / Real.sqrt 3) • octOne, (1 / Real.sqrt 3) • octJ, (1 / Real.sqrt 3) • octL ] :
        Fin 3 → Octonion) =
      fun i => (1 / Real.sqrt 3) • (![octOne, octJ, octL] : Fin 3 → Octonion) i := by
    funext i; fin_cases i <;> rfl
  rw [hvec, octDyad_scaled, max_normalization_square]

private theorem maxConfig_B_coordinates :
    maximizerConfig 1 =
      ((![1/3,2/3,0], ![octonionScalar (Real.sqrt 2 / 3),0,0]) : Albert) := by
  rw [maxConfig_B]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply albert_ext'
  · rw [albert_smul_fst']; change (1/3 : ℝ) * octNormSq octOne = _
    rw [octNormSq_one, mul_one]; rfl
  · rw [albert_smul_fst']; change (1/3 : ℝ) * octNormSq (octonionScalar (Real.sqrt 2)) = 2/3
    rw [max_scalarOne, octNormSq_smul, octNormSq_one, mul_one, hsq]; norm_num
  · rw [albert_smul_fst']; change (1/3 : ℝ) * octNormSq 0 = 0
    rw [← octonionScalar_zero, max_scalarOne, octNormSq_smul, octNormSq_one]
    norm_num
  · rw [albert_smul_snd']; change (1/3 : ℝ) •
       octonionMul octOne (octonionConj (octonionScalar (Real.sqrt 2))) = octonionScalar (Real.sqrt 2 / 3)
    rw [octonionConj_scalar, octonionMul_one_left, max_scalarOne (Real.sqrt 2),
      max_scalarOne (Real.sqrt 2 / 3), smul_smul, mul_comm, mul_one_div]
  · rw [albert_smul_snd']; change (1/3 : ℝ) • octonionMul octOne (octonionConj 0) = 0
    rw [octonionConj_zero, octonionMul_zero_right, smul_zero]
  · rw [albert_smul_snd']; change (1/3 : ℝ) • octonionMul (octonionScalar (Real.sqrt 2)) (octonionConj 0) = 0
    rw [octonionConj_zero, octonionMul_zero_right, smul_zero]

private theorem horizonAlgebraAddDiagonal (x y : Albert) (i : Fin 3) :
    (x + y).1 i = x.1 i + y.1 i := rfl

private theorem horizonAlgebraAddOffDiagonal (x y : Albert) (i : Fin 3) :
    (x + y).2 i = x.2 i + y.2 i := rfl

/-- The two rational-coordinate pieces give the exact native maximizer atoms. -/
theorem horizonMRational_coordinate_binding (i : Fin 4) :
    maximizerConfig i = castA (horizonMRationalEven i) + Real.sqrt 2 • castA (horizonMRationalOdd i) := by
  fin_cases i
  · have hq : QA.dyad QO.one QO.zero QO.zero = QA.diag0 := by decide +kernel
    have h := castA_dyad QO.one QO.zero QO.zero
    rw [hq, castO_one, castO_zero] at h
    change octDyad ![octOne,0,0] = castA QA.diag0 + Real.sqrt 2 • castA QA.zero
    rw [← h, castA_zero_horizon, smul_zero, add_zero]
  · change maximizerConfig (1 : Fin 4) =
      castA ⟨1/3,2/3,0,QO.zero,QO.zero,QO.zero⟩ +
      Real.sqrt 2 • castA ⟨0,0,0,QO.scalar (1/3),QO.zero,QO.zero⟩
    rw [maxConfig_B_coordinates]
    apply albert_ext'
    · rw [horizonAlgebraAddDiagonal, albert_smul_fst']; norm_num [castA]
    · rw [horizonAlgebraAddDiagonal, albert_smul_fst']; norm_num [castA]
    · rw [horizonAlgebraAddDiagonal, albert_smul_fst']; norm_num [castA]
    · rw [horizonAlgebraAddOffDiagonal, albert_smul_snd']
      change octonionScalar (Real.sqrt 2 / 3) =
        castO QO.zero + Real.sqrt 2 • castO (QO.scalar (1/3))
      rw [castO_zero, zero_add, castO_scalar]
      norm_num [max_scalarOne, smul_smul, div_eq_mul_inv]
    · rw [horizonAlgebraAddOffDiagonal, albert_smul_snd']
      change (0 : Octonion) = castO QO.zero + Real.sqrt 2 • castO QO.zero
      simp [castO_zero]
    · rw [horizonAlgebraAddOffDiagonal, albert_smul_snd']
      change (0 : Octonion) = castO QO.zero + Real.sqrt 2 • castO QO.zero
      simp [castO_zero]
  · change maximizerConfig (2 : Fin 4) =
      castA ((QA.dyad QO.one QO.I QO.one).smul (1/3)) + Real.sqrt 2 • castA QA.zero
    rw [castA_smul, castA_dyad, castO_one, castO_I, castA_zero_horizon, smul_zero, add_zero,
      maxConfig_C]
    norm_num
  · change maximizerConfig (3 : Fin 4) =
      castA ((QA.dyad QO.one QO.J QO.L).smul (1/3)) + Real.sqrt 2 • castA QA.zero
    rw [castA_smul, castA_dyad, castO_one, castO_J, castO_L, castA_zero_horizon, smul_zero, add_zero,
      maxConfig_D]
    norm_num

theorem horizonMRational_atoms (i : Fin 4) : horizonRationalForm (maximizerConfig i) :=
  ⟨_, _, horizonMRationalEven_parity i, horizonMRationalOdd_parity i,
    (horizonMRational_coordinate_binding i).symm⟩

/-- Every signed-word probability for M from the native tracial state is rational. -/
theorem horizon_M_probability_rational_e3 (w : Word (Fin 4)) :
    ∃ r : ℚ, (r : ℝ) = nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit) w :=
  horizonRationalForm_trace (horizonRationalForm_nativeBranchState maximizerConfig
    horizonMRational_atoms horizonRationalForm_e3 w)

/-- Every signed-word probability for M from its atom A is rational. -/
theorem horizon_M_probability_rational_A (w : Word (Fin 4)) :
    ∃ r : ℚ, (r : ℝ) = nativeWordProbability maximizerConfig (maximizerConfig 0) w :=
  horizonRationalForm_trace (horizonRationalForm_nativeBranchState maximizerConfig
    horizonMRational_atoms (horizonMRational_atoms 0) w)

end AlbertSequential.MatchingModels
