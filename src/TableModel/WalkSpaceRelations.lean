/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TableModel.WalkSpace

@[expose] public section
noncomputable section

namespace AlbertSequential.LengthSeven.TableModel

open LemmaB

private def faceCoeff (p : Params ℝ) (q v w : Letter) : ℝ :=
  match q.val + v.val + w.val with
  | 3 => p.c1
  | 4 => p.c3
  | 5 => p.c2
  | _ => p.b + p.c1*p.c2*p.c3 - p.c1*p.M23 - p.c2*p.M13 - p.c3*p.M12

private def sideCoeff (p : Params ℝ) (x y : Letter) : ℝ :=
  match x.val + y.val with
  | 3 => p.c1^2 + p.M11
  | 4 => p.c3^2 + p.M33
  | _ => p.c2^2 + p.M22

private def middleCoeff (p : Params ℝ) (i : Letter) : ℝ :=
  match i.val with
  | 1 => p.c1*p.c3 - p.M13
  | 2 => p.c1*p.c2 - p.M12
  | _ => p.c2*p.c3 - p.M23

private theorem T_A_left (p : Params ℝ) (i : Letter) (a : C8 ℝ) : T p 0 i a = a := by
  fin_cases i <;> rfl

private theorem T_A_right (p : Params ℝ) (i : Letter) (a : C8 ℝ) : T p i 0 a = a := by
  fin_cases i <;> rfl

private def loop (p : Params ℝ) (q v w : Letter) (a : C8 ℝ) : C8 ℝ :=
  T p q v (T p v w (T p w q a))

set_option maxHeartbeats 10000000 in
private theorem rawR2_ordered (p : Params ℝ) (q v w c : Letter)
    (hqv : q ≠ v) (hqw : q ≠ w) (hvw : v < w) :
    loop p q v w (T p q c one8) + loop p q w v (T p q c one8) =
      (2 * faceCoeff p q v w) • T p q c one8 := by
  fin_cases q <;> fin_cases v <;> fin_cases w <;> try contradiction
  all_goals simp [Fin.lt_def] at hvw
  all_goals
    fin_cases c <;> funext i <;> fin_cases i <;>
      simp [loop, T, faceCoeff, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8,
        Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem rawR2 (p : Params ℝ) (q v w c : Letter)
    (hqv : q ≠ v) (hqw : q ≠ w) (hvw : v ≠ w) :
    loop p q v w (T p q c one8) + loop p q w v (T p q c one8) =
      (2 * faceCoeff p q v w) • T p q c one8 := by
  rcases lt_or_gt_of_ne hvw with h | h
  · exact rawR2_ordered p q v w c hqv hqw h
  · have hface : faceCoeff p q w v = faceCoeff p q v w := by
      unfold faceCoeff
      rw [Nat.add_right_comm q.val w.val v.val]
    rw [add_comm, ← hface]
    exact rawR2_ordered p q w v c hqw hqv h

set_option maxHeartbeats 2000000 in
private theorem rawR3 (p : Params ℝ) (x y z : Letter) (h : IsOrderingBCD x y z) :
    T p x y (T p y z one8) + T p z y (T p y x one8) =
      (2 * middleCoeff p y) • one8 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [IsOrderingBCD] at h
  all_goals
    funext i
    fin_cases i <;> simp [T, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8,
      middleCoeff, Matrix.vecHead, Matrix.vecTail]
  all_goals ring

private theorem rawSix (p : Params ℝ) (x y z : Letter) (h : IsOrderingBCD x y z) :
    W p (T p y x one8) (T p z y (T p y x one8)) = faceCoeff p 0 y z * sideCoeff p x y := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [IsOrderingBCD] at h
  all_goals
    simp [W, T, faceCoeff, sideCoeff, h1, h2, h3, h1s, h2s, h3s, sig, eps1, eps2, eps3, one8,
      Matrix.vecHead, Matrix.vecTail]
  all_goals ring

variable (τ : TraceData)
local notation "p" => comparisonParams τ

private def sortedFaceTrace (q v w : Letter) : ℝ :=
  match q.val + v.val + w.val with
  | 3 => τ.R 0 1 2
  | 4 => τ.R 0 1 3
  | 5 => τ.R 0 2 3
  | _ => τ.R 1 2 3

private theorem face_trace_symm (q v w : Letter) (hqv : q ≠ v) (hqw : q ≠ w) (hvw : v ≠ w) :
    τ.R q v w = sortedFaceTrace τ q v w := by
  fin_cases q <;> fin_cases v <;> fin_cases w <;> try contradiction
  all_goals
    dsimp [sortedFaceTrace]
    first
    | rfl
    | exact τ.R_symm12 _ _ _
    | exact τ.R_symm23 _ _ _
    | exact (τ.R_symm12 _ _ _).trans (τ.R_symm23 _ _ _)
    | exact (τ.R_symm23 _ _ _).trans (τ.R_symm12 _ _ _)
    | exact (τ.R_symm12 _ _ _).trans ((τ.R_symm23 _ _ _).trans (τ.R_symm12 _ _ _))

private theorem faceCoeff_trace (q v w : Letter) (hqv : q ≠ v) (hqw : q ≠ w) (hvw : v ≠ w) :
    faceCoeff p q v w = τ.R q v w * mOf p q * mOf p v * mOf p w := by
  rw [face_trace_symm τ q v w hqv hqw hvw]
  fin_cases q <;> fin_cases v <;> fin_cases w <;> try contradiction
  all_goals
    simp [faceCoeff, sortedFaceTrace, mOf, Traces.toParams, toTraces]
  all_goals ring

private theorem sideCoeff_trace (x y z : Letter) (h : IsOrderingBCD x y z) :
    sideCoeff p x y = τ.o x y * mOf p x * mOf p y := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [IsOrderingBCD] at h
  all_goals
    simp [sideCoeff, mOf, Traces.toParams, toTraces, τ.o_symm]
  all_goals ring

private theorem middleCoeff_trace (y : Letter) (hy : y ≠ 0) :
    middleCoeff p y = τ.om y * ((mOf p 1) * (mOf p 2) * (mOf p 3)) := by
  fin_cases y <;> try contradiction
  all_goals simp [middleCoeff, mOf, Traces.toParams, toTraces_ω1, toTraces_ω2, toTraces_ω3]

private theorem triple_projection (q v w : Letter) (a : C8 ℝ) :
    comparisonProjection τ q (comparisonProjection τ v (comparisonProjection τ w (Pi.single q a))) =
      ((mOf p q)⁻¹ * (mOf p v)⁻¹ * (mOf p w)⁻¹) • Pi.single q (loop p q v w a) := by
  simp only [comparisonProjection_single, T_smul, smul_smul, loop, mul_assoc]
  rw [Pi.single_smul]

variable (hB : τ.o 0 1 ≠ 0) (hC : τ.o 0 2 ≠ 0) (hD : τ.o 0 3 ≠ 0)
local notation "CW" => comparisonWalkSpace τ hB hC hD

private theorem short_history (t : List Letter) (q : Letter) (ht : t.length ≤ 1) :
    ∃ c : Letter, ∃ d : ℝ, comparisonProjection τ q ((CW).pathVec t) =
      d • Pi.single q (T p q c one8) := by
  cases t with
  | nil =>
    refine ⟨0, (mOf p q)⁻¹, ?_⟩
    change comparisonProjection τ q (Pi.single 0 one8) = _
    rw [comparisonProjection_single, Pi.single_smul]
  | cons c t =>
    have hn : t = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_cons] at ht
      omega
    subst t
    refine ⟨c, (mOf p q)⁻¹ * (mOf p c)⁻¹, ?_⟩
    change comparisonProjection τ q (comparisonProjection τ c (Pi.single 0 one8)) = _
    simp only [comparisonProjection_single, T_A_right, T_smul, smul_smul]
    rw [Pi.single_smul]

theorem comparison_R2 (t : List Letter) (q v w : Letter) (hqv : q ≠ v) (hvw : v ≠ w) (hqw : q ≠ w)
    (ht : t.length ≤ 1) :
    let η := (CW).P q ((CW).pathVec t)
    (CW).P q ((CW).P v ((CW).P w ((CW).P q η))) +
      (CW).P q ((CW).P w ((CW).P v ((CW).P q η))) = (2 * τ.R q v w) • η := by
  dsimp only
  rw [(CW).idem]
  change _ = (2 * τ.R q v w) • comparisonProjection τ q ((CW).pathVec t)
  obtain ⟨c, d, h⟩ := short_history τ hB hC hD t q ht
  simp only [comparisonWalkSpace] at h ⊢
  rw [h]
  simp only [map_smul, triple_projection, smul_smul]
  have hc : (mOf p q)⁻¹ * (mOf p w)⁻¹ * (mOf p v)⁻¹ =
      (mOf p q)⁻¹ * (mOf p v)⁻¹ * (mOf p w)⁻¹ := by ring
  rw [hc, ← smul_add, ← Pi.single_add, rawR2 p q v w c hqv hqw hvw, Pi.single_smul,
    faceCoeff_trace τ q v w hqv hqw hvw, smul_smul]
  congr 1
  have hq := comparison_m_ne_zero τ hB hC hD q
  have hv := comparison_m_ne_zero τ hB hC hD v
  have hw := comparison_m_ne_zero τ hB hC hD w
  field_simp

private theorem inverse_mOf (x : Letter) (hx : x ≠ 0) : (mOf p x)⁻¹ = τ.o 0 x := by
  fin_cases x <;> try contradiction
  all_goals simp [mOf, Traces.toParams, toTraces]

theorem comparison_singleton (x : Letter) (hx : x ≠ 0) : (CW).L [x] = τ.o 0 x := by
  change Q p (Pi.single 0 one8) (comparisonProjection τ x (Pi.single 0 one8)) = _
  rw [comparisonProjection_single, comparison_form_single, T_A_right, T_A_left,
    W_smul_right, W_one, show one8 (0 : Fin 8) = (1 : ℝ) from rfl, mul_one, inverse_mOf τ x hx]

private theorem pair_path (x y : Letter) : (CW).pathVec [x, y] =
    Pi.single y (((mOf p y)⁻¹ * (mOf p x)⁻¹) • T p y x one8) := by
  change comparisonProjection τ y (comparisonProjection τ x (Pi.single 0 one8)) = _
  simp only [comparisonProjection_single, T_A_right, T_smul, smul_smul]

theorem comparison_six (x y z : Letter) (h : IsOrderingBCD x y z) :
    (CW).L [x, y, 0, z, y, x] = τ.o 0 x * τ.o x y * τ.R 0 y z := by
  have he := (CW).form_pathVec [x, y, 0] [x, y, z]
  change _ = (CW).L [x, y, 0, z, y, x] at he
  rw [← he]
  have hp (i : Letter) : (CW).pathVec [x, y, i] = comparisonProjection τ i ((CW).pathVec [x, y]) := rfl
  rw [hp, hp, pair_path, comparisonProjection_single, comparisonProjection_single]
  change Q p _ _ = _
  rw [comparison_form_single, T_A_left, T_A_left, show mOf p 0 = 1 from rfl, inv_one, one_smul]
  simp only [T_smul, W_smul_left, W_smul_right, rawSix p x y z h,
    faceCoeff_trace τ 0 y z h.2.1.symm h.2.2.1.symm h.2.2.2.2.1, sideCoeff_trace τ x y z h,
    show mOf p 0 = 1 from rfl, mul_one]
  rw [← inverse_mOf τ x h.1]
  have hx := comparison_m_ne_zero τ hB hC hD x
  have hy := comparison_m_ne_zero τ hB hC hD y
  have hz := comparison_m_ne_zero τ hB hC hD z
  field_simp

private theorem anchor_triple_projection (x y z : Letter) :
    comparisonProjection τ 0 (comparisonProjection τ x (comparisonProjection τ y
      (comparisonProjection τ z (Pi.single (0 : Letter) (one8 : C8 ℝ))))) =
      ((mOf p x)⁻¹ * (mOf p y)⁻¹ * (mOf p z)⁻¹) • Pi.single (0 : Letter) (T p x y (T p y z one8)) := by
  simp only [comparisonProjection_single, T_A_left, T_A_right,
    show mOf p 0 = 1 from rfl, inv_one, T_smul, smul_smul, mul_assoc, one_mul]
  rw [Pi.single_smul]

theorem comparison_R3 (x y z : Letter) (h : IsOrderingBCD x y z) :
    (CW).P 0 ((CW).P x ((CW).P y ((CW).P z ((CW).P 0 (CW).ξ)))) +
      (CW).P 0 ((CW).P z ((CW).P y ((CW).P x ((CW).P 0 (CW).ξ)))) = (2 * τ.om y) • (CW).ξ := by
  rw [(CW).fixA]
  change comparisonProjection τ 0 (comparisonProjection τ x (comparisonProjection τ y
      (comparisonProjection τ z (Pi.single (0 : Letter) (one8 : C8 ℝ))))) +
    comparisonProjection τ 0 (comparisonProjection τ z (comparisonProjection τ y
      (comparisonProjection τ x (Pi.single (0 : Letter) (one8 : C8 ℝ))))) =
      (2 * τ.om y) • Pi.single (0 : Letter) (one8 : C8 ℝ)
  rw [anchor_triple_projection, anchor_triple_projection]
  have he : (mOf p z)⁻¹ * (mOf p y)⁻¹ * (mOf p x)⁻¹ =
      (mOf p x)⁻¹ * (mOf p y)⁻¹ * (mOf p z)⁻¹ := by ring
  rw [he, ← smul_add, ← Pi.single_add, rawR3 p x y z h, Pi.single_smul,
    middleCoeff_trace τ y h.2.1, smul_smul]
  have hr : mOf p 1 * mOf p 2 * mOf p 3 = mOf p x * mOf p y * mOf p z := by
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [IsOrderingBCD] at h
    all_goals simp [mOf, mul_comm, mul_left_comm]
  rw [hr]
  congr 1
  have hx := comparison_m_ne_zero τ hB hC hD x
  have hy := comparison_m_ne_zero τ hB hC hD y
  have hz := comparison_m_ne_zero τ hB hC hD z
  field_simp

/-- The actual, potentially indefinite comparison form satisfies all the
paper's short vector relations. -/
theorem comparison_hypotheses : AlgebraicWalkHypotheses CW τ where
  singleton := comparison_singleton τ hB hC hD
  six := comparison_six τ hB hC hD
  r1 t q v hqv _ := (comparison_R1 τ hB hC hD q v hqv ((CW).P q ((CW).pathVec t))).trans
    (congrArg (fun F : V ℝ => τ.o q v • F) ((CW).idem q ((CW).pathVec t)))
  r2 := comparison_R2 τ hB hC hD
  r3 := comparison_R3 τ hB hC hD

end AlbertSequential.LengthSeven.TableModel
