/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiveTest.PentadCircleInterpolation
public import FiveTest.PentadContinuousCoordinates
public import FiveTest.PentadPeirceFrequency
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace AlbertSequential.FiveTest

open MatchingModels MatchingModels.IntMirror

def movingPentadColumn (k : Fin 27) : Bool :=
  [6,11,14,16,17,19,20,21,22,24,25,26].contains k.val

def zLinearPentad (c d n : ℤ) (r : Fin 5) : ZA :=
  if r = 4 then
    ⟨3*n, 3*n, 0, ⟨⟨0,0,0,-3*c⟩, ⟨-3*d,0,0,0⟩⟩, ZO.zero, ZO.zero⟩
  else (qPentadZ6 ZO.L r).smul n

def zPentadBasis (c d n : ℤ) (k : Fin 27) : ZA :=
  if movingPentadColumn k then ((basisLit_K k).smul c).add ((basisLit_L k).smul d)
  else (basisLit_L k).smul n

def zPentadRowTarget (c d n : ℤ) (r : Fin 5) (k : Fin 27) : ZA :=
  let B := zPentadBasis c d n
  ((sumTermsZA (m0RowZ12 r k) B).smul n).add ((sumTermsZA (m1RowZ12 r k) B).smul c)

def zPentadProbe (c d n : ℤ) : Prop :=
  ∀ (r : Fin 5) (k : Fin 27), (zLinearPentad c d n r).jmul2 (zPentadBasis c d n k) =
    zPentadRowTarget c d n r k

def zPentadProbeCheck (c d n : ℤ) : Bool :=
  (List.finRange 5).all fun r => (List.finRange 27).all fun k =>
    decide ((zLinearPentad c d n r).jmul2 (zPentadBasis c d n k) = zPentadRowTarget c d n r k)

theorem zPentadProbe_of_check {c d n : ℤ} (h : zPentadProbeCheck c d n = true) :
    zPentadProbe c d n := by
  intro r k
  have hr := List.all_eq_true.mp h r (List.mem_finRange r)
  exact of_decide_eq_true (List.all_eq_true.mp hr k (List.mem_finRange k))

theorem zPentadProbe_xpos : zPentadProbe 1 0 1 := zPentadProbe_of_check (by decide +kernel)
theorem zPentadProbe_xneg : zPentadProbe (-1) 0 1 := zPentadProbe_of_check (by decide +kernel)
theorem zPentadProbe_ypos : zPentadProbe 0 1 1 := zPentadProbe_of_check (by decide +kernel)
theorem zPentadProbe_yneg : zPentadProbe 0 (-1) 1 := zPentadProbe_of_check (by decide +kernel)
theorem zPentadProbe_mixed : zPentadProbe 3 4 5 := zPentadProbe_of_check (by decide +kernel)

end AlbertSequential.FiveTest

namespace AlbertSequential.FiveTest

open NativeAnalysis MatchingModels MatchingModels.IntMirror
open WindowProbability

noncomputable section

def basisPlane (k : Fin 27) : AffinePlane Albert :=
  if movingPentadColumn k then ⟨0, castZA (basisLit_K k), castZA (basisLit_L k)⟩
  else ⟨castZA (basisLit_L k), 0, 0⟩

def parameterBasis (c d : ℝ) (k : Fin 27) : Albert := (basisPlane k).eval c d

private def menuPlane (r : Fin 5) : AffinePlane Albert :=
  if r = 4 then
    ⟨(![1/2,1/2,0], fun _ => 0), (0, ![(-1/2 : ℝ) • octK,0,0]),
      (0, ![(-1/2 : ℝ) • octL,0,0])⟩
  else ⟨pentadF r, 0, 0⟩

private def rowPlane (l : List (Fin 27 × ℤ)) : AffinePlane Albert :=
  l.foldr (fun t p => ((basisPlane t.1).scale ((t.2 : ℝ)/12)).add p) ⟨0,0,0⟩

private def rowAt (l : List (Fin 27 × ℤ)) (c d : ℝ) : Albert := (rowPlane l).eval c d

private theorem rowAt_nil (c d : ℝ) : rowAt [] c d = 0 := by
  simp [rowAt, rowPlane, AffinePlane.eval]

private theorem rowAt_cons (c d : ℝ) (t : Fin 27 × ℤ) (l : List (Fin 27 × ℤ)) :
    rowAt (t :: l) c d = ((t.2 : ℝ)/12) • parameterBasis c d t.1 + rowAt l c d := by
  simp only [rowAt, rowPlane, List.foldr_cons, AffinePlane.eval_add, AffinePlane.eval_scale,
    parameterBasis]

private theorem cast_basis (c d n : ℤ) (hn : (n : ℝ) ≠ 0) (k : Fin 27) :
    castZA (zPentadBasis c d n k) =
      (n : ℝ) • parameterBasis ((c : ℝ)/n) ((d : ℝ)/n) k := by
  have hC : (n : ℝ) * ((c : ℝ)/n) = c := by field_simp
  have hD : (n : ℝ) * ((d : ℝ)/n) = d := by field_simp
  by_cases h : movingPentadColumn k
  · simp [zPentadBasis, parameterBasis, basisPlane, h, AffinePlane.eval, castZA_add, castZA_smul,
      smul_add, smul_smul, hC, hD]
  · simp [zPentadBasis, parameterBasis, basisPlane, h, AffinePlane.eval, castZA_smul]

private theorem menuPlane_four (c d : ℝ) :
    (menuPlane 4).eval c d = (![1/2,1/2,0], ![(-1/2 : ℝ) • (c • octK + d • octL),0,0]) := by
  apply Prod.ext <;> funext i <;> fin_cases i
  · change (1/2 : ℝ) + c * 0 + d * 0 = 1/2
    ring
  · change (1/2 : ℝ) + c * 0 + d * 0 = 1/2
    ring
  · change (0 : ℝ) + c * 0 + d * 0 = 0
    ring
  · change (0 : Octonion) + c • ((-1/2 : ℝ) • octK) + d • ((-1/2 : ℝ) • octL) =
      (-1/2 : ℝ) • (c • octK + d • octL)
    module
  · change (0 : Octonion) + c • (0 : Octonion) + d • (0 : Octonion) = 0
    simp
  · change (0 : Octonion) + c • (0 : Octonion) + d • (0 : Octonion) = 0
    simp

private theorem cast_menu (c d n : ℤ) (hn : (n : ℝ) ≠ 0) (r : Fin 5) :
    castZA (zLinearPentad c d n r) =
      (6 * (n : ℝ)) • (menuPlane r).eval ((c : ℝ)/n) ((d : ℝ)/n) := by
  by_cases hr : r = 4
  · subst r
    rw [menuPlane_four]
    simp only [zLinearPentad, ↓reduceIte]
    apply Prod.ext
    · funext i
      fin_cases i
      · change ((3*n : ℤ) : ℝ) = (6 * (n : ℝ)) * (1/2)
        push_cast
        ring
      · change ((3*n : ℤ) : ℝ) = (6 * (n : ℝ)) * (1/2)
        push_cast
        ring
      · change ((0 : ℤ) : ℝ) = (6 * (n : ℝ)) * 0
        simp
    · funext i
      fin_cases i
      · change castZO (⟨⟨0,0,0,-3*c⟩, ⟨-3*d,0,0,0⟩⟩ : ZO) =
          (6 * (n : ℝ)) • ((-1/2 : ℝ) • (((c : ℝ)/n) • octK + ((d : ℝ)/n) • octL))
        have hC : (6 * (n : ℝ)) * (-1/2) * ((c : ℝ)/n) = -3 * c := by field_simp; ring
        have hD : (6 * (n : ℝ)) * (-1/2) * ((d : ℝ)/n) = -3 * d := by field_simp; ring
        rw [smul_smul, smul_add, smul_smul, smul_smul, hC, hD]
        have ha (z : ℝ) (u : Octonion) : (z • u).1 = z • u.1 := rfl
        have hb (z : ℝ) (u : Octonion) : (z • u).2 = z • u.2 := rfl
        have hc (u v : Octonion) : (u+v).1 = u.1+v.1 := rfl
        have hd (u v : Octonion) : (u+v).2 = u.2+v.2 := rfl
        apply Prod.ext
        · rw [hc,ha,ha]
          apply Quaternion.ext <;> simp [castZO, castZQ, octK, octL]
        · rw [hd,hb,hb]
          apply Quaternion.ext <;> simp [castZO, castZQ, octK, octL]
      · change castZO ZO.zero = (6 * (n : ℝ)) • (0 : Octonion)
        rw [castZO_zero, smul_zero]
      · change castZO ZO.zero = (6 * (n : ℝ)) • (0 : Octonion)
        rw [castZO_zero, smul_zero]
  · simp [zLinearPentad, menuPlane, AffinePlane.eval, hr, castZA_smul, pentadF_eq_castZ6,
      smul_smul, mul_comm]

private theorem cast_row (c d n : ℤ) (hn : (n : ℝ) ≠ 0) (l : List (Fin 27 × ℤ)) :
    castZA (sumTermsZA l (zPentadBasis c d n)) =
      (12 * (n : ℝ)) • rowAt l ((c : ℝ)/n) ((d : ℝ)/n) := by
  induction l with
  | nil =>
    simp [sumTermsZA, castZA_zero, rowAt_nil]
  | cons t l ih =>
    simp only [sumTermsZA, List.foldr_cons, castZA_add, castZA_smul] at ih ⊢
    rw [ih, cast_basis c d n hn t.1, rowAt_cons]
    module

private theorem action_at_probe (c d n : ℤ) (hn : (n : ℝ) ≠ 0)
    (hp : zPentadProbe c d n) (r : Fin 5) (k : Fin 27) :
    let a := (c : ℝ)/n
    let b := (d : ℝ)/n
    jordanMul ((menuPlane r).eval a b) (parameterBasis a b k) =
      rowAt (m0RowZ12 r k) a b + a • rowAt (m1RowZ12 r k) a b := by
  let a := (c : ℝ)/n
  let b := (d : ℝ)/n
  let J := jordanMul ((menuPlane r).eval a b) (parameterBasis a b k)
  let v := rowAt (m0RowZ12 r k) a b
  let w := rowAt (m1RowZ12 r k) a b
  have h := congrArg castZA (hp r k)
  simp only [zPentadRowTarget, castZA_jmul2, cast_menu c d n hn r,
    cast_basis c d n hn k, castZA_add, castZA_smul, cast_row c d n hn,
    jordanMul_smul_left, jordanMul_smul_right] at h
  change (2 : ℝ) • ((n : ℝ) • (6 * (n : ℝ)) • J) =
    (n : ℝ) • ((12 * (n : ℝ)) • v) + (c : ℝ) • ((12 * (n : ℝ)) • w) at h
  have ha : (12 * (n : ℝ)^2) * a = (c : ℝ) * (12 * (n : ℝ)) := by
    dsimp only [a]
    field_simp
  have hm : (12 * (n : ℝ)^2) • J = (12 * (n : ℝ)^2) • (v + a • w) := by
    rw [smul_add, smul_smul, ha]
    calc
      _ = (2 : ℝ) • ((n : ℝ) • (6 * (n : ℝ)) • J) := by module
      _ = (n : ℝ) • ((12 * (n : ℝ)) • v) + (c : ℝ) • ((12 * (n : ℝ)) • w) := h
      _ = _ := by module
  exact (smul_right_inj (by positivity : 12 * (n : ℝ)^2 ≠ 0)).mp hm

private def jordanBilinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert :=
  LinearMap.mk₂' ℝ ℝ jordanMul jordanMul_add_left jordanMul_smul_left
    jordanMul_add_right jordanMul_smul_right

private def actionDifference (r : Fin 5) (k : Fin 27) : QuadraticPlane Albert :=
  (QuadraticPlane.bind jordanBilinear (menuPlane r) (basisPlane k)).sub
    (QuadraticPlane.sumAndScaleFirst (rowPlane (m0RowZ12 r k)) (rowPlane (m1RowZ12 r k)))

private theorem actionDifference_eval (r : Fin 5) (k : Fin 27) (a b : ℝ) :
    (actionDifference r k).eval a b = jordanMul ((menuPlane r).eval a b) (parameterBasis a b k) -
      (rowAt (m0RowZ12 r k) a b + a • rowAt (m1RowZ12 r k) a b) := by
  rw [actionDifference, QuadraticPlane.eval_sub, QuadraticPlane.eval_bind,
    QuadraticPlane.eval_sumAndScaleFirst]
  rfl

private theorem parameterized_sparsePeirce_action (a b : ℝ) (hunit : a^2+b^2=1) (r : Fin 5) (k : Fin 27) :
    jordanMul ((menuPlane r).eval a b) (parameterBasis a b k) =
      rowAt (m0RowZ12 r k) a b + a • rowAt (m1RowZ12 r k) a b := by
  have hzero (c d n : ℤ) (hn : (n : ℝ) ≠ 0) (hp : zPentadProbe c d n) :
      (actionDifference r k).eval ((c : ℝ)/n) ((d : ℝ)/n) = 0 := by
    rw [actionDifference_eval, action_at_probe c d n hn hp r k, sub_self]
  have h1 : (actionDifference r k).eval 1 0 = 0 := by
    simpa using hzero 1 0 1 (by norm_num) zPentadProbe_xpos
  have h2 : (actionDifference r k).eval (-1) 0 = 0 := by
    simpa using hzero (-1) 0 1 (by norm_num) zPentadProbe_xneg
  have h3 : (actionDifference r k).eval 0 1 = 0 := by
    simpa using hzero 0 1 1 (by norm_num) zPentadProbe_ypos
  have h4 : (actionDifference r k).eval 0 (-1) = 0 := by
    simpa using hzero 0 (-1) 1 (by norm_num) zPentadProbe_yneg
  have h5 : (actionDifference r k).eval (3/5) (4/5) = 0 := by
    simpa using hzero 3 4 5 (by norm_num) zPentadProbe_mixed
  have h := (actionDifference r k).zero_on_circle h1 h2 h3 h4 h5 a b hunit
  rw [actionDifference_eval] at h
  exact sub_eq_zero.mp h

private theorem rowAt_fin (l : List (Fin 27 × ℤ)) (c d : ℝ) :
    rowAt l c d = ∑ j, ((listCoeffZ l j : ℝ) / 12) • parameterBasis c d j := by
  induction l with
  | nil => simp [rowAt_nil, listCoeffZ]
  | cons p l ih =>
    rw [rowAt_cons, ih]
    have he (j : Fin 27) : listCoeffZ (p :: l) j =
        (if p.1 = j then p.2 else 0) + listCoeffZ l j := rfl
    simp only [he, Int.cast_add, add_div, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single p.1]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

private theorem circle_axis_properties (c d : ℝ) (h : c^2 + d^2 = 1) :
    let u := c • octK + d • octL
    octNormSq u = 1 ∧ octonionReal u = 0 := by
  have hk : octNormSq octK = 1 := by rw [octNormSq_eq_coords]; norm_num [octK]
  have hl : octNormSq octL = 1 := by rw [octNormSq_eq_coords]; norm_num [octL]
  have hd : octDot octK octL = 0 := by rw [octDot_eq_coords]; norm_num [octK, octL]
  constructor
  · rw [octNormSq_add, octNormSq_smul, octNormSq_smul, octDot_smul_left, octDot_smul_right,
      hk, hl, hd]
    simpa using h
  · rw [octonionReal_add, octonionReal_smul, octonionReal_smul,
      show octonionReal octK = 0 from rfl, show octonionReal octL = 0 from rfl]
    simp

private theorem circle_menu_agrees (c d : ℝ) (h : c^2 + d^2 = 1) (r : Fin 5) :
    (menuPlane r).eval c d = continuousPentad (c • octK + d • octL) r := by
  by_cases hr : r = 4
  · subst r
    rw [menuPlane_four]
    let u : Octonion := c • octK + d • octL
    change (![1/2,1/2,0], ![(-1/2 : ℝ) • u,0,0]) = (1/2 : ℝ) • chartDyad u 0
    obtain ⟨hu, hre⟩ := circle_axis_properties c d h
    have hzero : octNormSq 0 = 0 := (octNormSq_eq_zero _).mpr rfl
    apply Prod.ext <;> funext i <;> fin_cases i
    · change (1/2 : ℝ) = (1/2) * octNormSq octOne
      rw [octNormSq_one,mul_one]
    · change (1/2 : ℝ) = (1/2) * octNormSq u
      rw [hu,mul_one]
    · change (0 : ℝ) = (1/2) * octNormSq 0
      rw [hzero,mul_zero]
    · change (-1/2 : ℝ) • u = (1/2 : ℝ) • octonionMul octOne (octonionConj u)
      rw [octonionMul_one_left, octonionConj_eq_neg_of_real_zero hre, smul_neg]
      change (-1/2 : ℝ) • u = -((1/2 : ℝ) • u)
      module
    · change (0 : Octonion) = (1/2 : ℝ) • octonionMul octOne (octonionConj 0)
      rw [octonionConj_zero, octonionMul_zero_right, smul_zero]
    · change (0 : Octonion) = (1/2 : ℝ) • octonionMul u (octonionConj 0)
      rw [octonionConj_zero, octonionMul_zero_right, smul_zero]
  · simp [menuPlane, continuousPentad, AffinePlane.eval, hr]

theorem parameterizedPeirce_action (c d : ℝ) (h : c^2 + d^2 = 1) (r : Fin 5) (k : Fin 27) :
    jordanMul (continuousPentad (c • octK + d • octL) r) (parameterBasis c d k) =
      ∑ j, ((m0Coeff r k j : ℝ) + c * (m1Coeff r k j : ℝ)) • parameterBasis c d j := by
  rw [← circle_menu_agrees c d h r, parameterized_sparsePeirce_action c d h r k, rowAt_fin, rowAt_fin]
  simp only [m0Coeff, m1Coeff, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat,
    Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, add_smul]

private theorem basis_trace_data :
    ∀ k : Fin 27, (basisLit_L k).tr = trVecZ k ∧ (basisLit_K k).tr = trVecZ k ∧
      (movingPentadColumn k = true → trVecZ k = 0) := by decide +kernel

private theorem parameterBasis_trace (c d : ℝ) (k : Fin 27) :
    albertTrace (parameterBasis c d k) = trVecZ k := by
  obtain ⟨hL,hK,hmove⟩ := basis_trace_data k
  by_cases h : movingPentadColumn k
  · simp [parameterBasis, basisPlane, h, AffinePlane.eval, albertTrace_add, albertTrace_smul,
      ← castZA_tr, hL, hK, hmove h]
  · simp [parameterBasis, basisPlane, h, AffinePlane.eval, ← castZA_tr, hL]

private theorem parameterBasis_unit (c d : ℝ) :
    parameterBasis c d 0 + parameterBasis c d 1 = albertUnit := by
  have h : (basisLit_L 0).add (basisLit_L 1) = ZA.unit := by decide +kernel
  have h0 : movingPentadColumn 0 = false := by decide +kernel
  have h1 : movingPentadColumn 1 = false := by decide +kernel
  simp [parameterBasis, basisPlane, h0, h1, AffinePlane.eval]
  rw [← castZA_add, h, castZA_unit]

/-- Evaluation of the rational coefficient polynomial at the actual Cayley coordinate. -/
def parameterEval (c : ℝ) : Polynomial ℚ →+* ℝ :=
  Polynomial.eval₂RingHom (Rat.castHom ℝ) c

private theorem evaluate_chain (L : List (Fin 5)) (c d : ℝ) (h : c^2 + d^2 = 1) :
    pentadChain (continuousPentad (c • octK + d • octL)) L =
      ∑ j, parameterEval c (pentadChainPolynomial L j) • parameterBasis c d j := by
  let B := parameterBasis c d
  let e := parameterEval c
  induction L with
  | nil =>
    change albertUnit = ∑ j, e (Polynomial.C (unitVec j)) • B j
    have hc (j : Fin 27) : e (Polynomial.C (unitVec j)) • B j =
        (if j = 0 then B 0 else 0) + (if j = 1 then B 1 else 0) := by
      fin_cases j <;> simp [e, parameterEval, unitVec]
    simp only [hc, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact (parameterBasis_unit c d).symm
  | cons r L ih =>
    let A := continuousPentad (c • octK + d • octL) r
    change jordanMul A (pentadChain (continuousPentad (c • octK + d • octL)) L) = _
    rw [ih]
    change (jordanBilinear A) (∑ j, e (pentadChainPolynomial L j) • B j) = _
    simp only [map_sum, map_smul]
    change (∑ k, e (pentadChainPolynomial L k) • jordanMul A (B k)) = _
    simp_rw [A, B, parameterizedPeirce_action c d h r, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [pentadChainPolynomial, map_sum, map_add, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [e, parameterEval]
    ring

/-- A single rational polynomial, with the proved occurrence bounds, evaluates
to the actual connected trace for every allowed imaginary unit axis. -/
theorem continuousPentad_connectedTrace (u : Octonion) (hu : octNormSq u = 1)
    (hre : octonionReal u = 0) (hI : octDot u octI = 0) (hJ : octDot u octJ = 0)
    (L : List (Fin 5)) :
    albertTrace (pentadChain (continuousPentad u) L) =
      parameterEval (octDot u octK) (pentadConnectedTracePolynomial L) := by
  obtain ⟨g, d, _, hcd, hg⟩ := exists_rotate_continuousPentad u hu hre hI hJ
  let c := octDot u octK
  have he : g.linearEquiv (pentadChain (continuousPentad u) L) =
      pentadChain (continuousPentad (c • octK + d • octL)) L := by
    induction L with
    | nil => exact g.preserves_unit
    | cons r L ih =>
      change g.linearEquiv (jordanMul (continuousPentad u r) (pentadChain (continuousPentad u) L)) =
        jordanMul (continuousPentad (c • octK + d • octL) r)
          (pentadChain (continuousPentad (c • octK + d • octL)) L)
      rw [g.preserves_product, hg, ih]
  rw [← g.preserves_trace, he, evaluate_chain L c d hcd, pentadConnectedTracePolynomial, map_sum]
  have ht : albertTrace (∑ j, parameterEval c (pentadChainPolynomial L j) • parameterBasis c d j) =
      ∑ j, parameterEval c (pentadChainPolynomial L j) * albertTrace (parameterBasis c d j) := by
    let tr : Albert →ₗ[ℝ] ℝ :=
      { toFun := albertTrace, map_add' := albertTrace_add, map_smul' := albertTrace_smul }
    change tr (∑ j, parameterEval c (pentadChainPolynomial L j) • parameterBasis c d j) = _
    simp only [map_sum, map_smul]
    rfl
  rw [ht]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [parameterBasis_trace]
  simp only [map_mul, map_intCast, mul_comm, c]

end

end AlbertSequential.FiveTest
