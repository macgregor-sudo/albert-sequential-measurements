/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteVectorTetrahedronPaper
public import BlockB.ElevenCore

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace AlbertSequential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The real vector functional on bounded operators, with no normalization. -/
def residualVectorFunctional (Ω : H) : (H →L[ℝ] H) →ₗ[ℝ] ℝ where
  toFun T := ⟪Ω,T Ω⟫_ℝ
  map_add' T U := by simp [inner_add_right]
  map_smul' c T := by simp [real_inner_smul_right]

theorem residualVectorFunctional_star (Ω : H) (T : H →L[ℝ] H) :
    residualVectorFunctional Ω (star T) = residualVectorFunctional Ω T :=
  (T.adjoint_inner_right Ω Ω).trans (real_inner_comm _ _)

theorem residualVectorFunctional_starMul (Ω : H) (T U : H →L[ℝ] H) :
    residualVectorFunctional Ω (star T * U) = ⟪T Ω,U Ω⟫_ℝ :=
  T.adjoint_inner_right Ω (U Ω)

omit [CompleteSpace H] in
def residualVectorProbability {ι : Type*} (P : ι → H →L[ℝ] H) (Ω : H) (w : Word ι) : ℝ :=
  ‖wordAmplitude P w Ω‖^2

theorem residualVectorFunctional_wordOperator {ι : Type*}
    (P : ι → H →L[ℝ] H) (Ω : H) (w : Word ι) :
    residualVectorFunctional Ω (wordOperator P w) = residualVectorProbability P Ω w := by
  rw [wordOperator, residualVectorFunctional_starMul, real_inner_self_eq_norm_sq]
  rfl

/-- The unconditioned three-history residual identity on actual Hilbert vectors. -/
theorem purityResidualVector_threeHistories {ι : Type*}
    (P : ι → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i))
    (Ω : H) (q : Outcome ι) (v t : Word ι) (c : ℝ) :
    let g := residualVectorProbability P Ω
    ‖outcomePurityElement P q v c (wordAmplitude P t Ω)‖^2 =
      g (t ++ [q] ++ v ++ purityMirror v ++ [q]) - 2*c * g (t ++ [q] ++ v) +
        c^2 * g (t ++ [q]) := by
  have e := congrArg (residualVectorFunctional Ω)
    (purityResidual_operator P (fun i => (hp i).isIdempotentElem)
      (fun i => (hp i).isSelfAdjoint) q v t c)
  change ‖(outcomePurityElement P q v c * wordAmplitude P t) Ω‖^2 = _
  simpa only [residualVectorFunctional_starMul, real_inner_self_eq_norm_sq,
    map_add, map_sub, map_smul, smul_eq_mul, residualVectorFunctional_wordOperator] using e

theorem CliffordScalarParameters.discriminant_eq_det (s : CliffordScalarParameters) :
    s.discriminant = (Matrix.of s.gramMatrix).det - s.d0^2 := by
  simp only [CliffordScalarParameters.discriminant, Matrix.det_fin_three, Matrix.of_apply,
    CliffordScalarParameters.gramMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Appendix A.4's residual telescope for actual vectors, with the same
three-by-three determinant as the finite-vector theorem. -/
theorem cornerResidualTelescope_vectorIdentity (d : CornerNumericalData)
    (C : Fin 4 → Word (Fin 4) → ℝ) (hc : CornerScalarConditions d C)
    (P : Fin 4 → H →L[ℝ] H) (hp : ∀ i, IsStarProjection (P i)) (Ω : H) :
    let s := d.scalarParameters
    let occ := cornerResidualTelescopeOccurrences d C
    ((Matrix.of s.gramMatrix).det - s.d0^2) * ‖P 0 Ω‖^2 =
      (occ.map fun o => ⟪o.leftElement P Ω,o.leaf.residualElement P Ω⟫_ℝ).sum := by
  have h := cornerResidualTelescope_linearIdentity d C hc P
    (fun i => (hp i).isIdempotentElem) (fun i => (hp i).isSelfAdjoint)
    (residualVectorFunctional Ω) (residualVectorFunctional_star Ω)
  have hP := residualVectorFunctional_starMul Ω (P 0) (P 0)
  rw [show star (P 0) = P 0 from (hp 0).isSelfAdjoint,
    show P 0 * P 0 = P 0 from (hp 0).isIdempotentElem, real_inner_self_eq_norm_sq] at hP
  simpa only [CliffordScalarParameters.discriminant_eq_det, hP,
    ResidualOccurrenceExpression.value, residualVectorFunctional_starMul] using h

namespace BlockB
open CornerHolonomy

private theorem sqrt_common_factor (a x y : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    Real.sqrt (a * x) * Real.sqrt (a * y) = a * Real.sqrt (x * y) := by
  rw [← Real.sqrt_mul (mul_nonneg ha hx),
    show (a*x)*(a*y) = a^2*(x*y) by ring, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- The normalized coefficients of the native residual telescope are exactly
the coefficients of the finite-vector tetrahedron on the same native data. -/
theorem atomCornerData_scalarParameters_eq_finiteTetrahedron
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p) :
    (atomCornerData p).scalarParameters =
      CornerHolonomy.finiteTetrahedronParameters (nativeOverlaps p) (nativeTriangles p)
        (nativeCornerQ p) := by
  let d := atomCornerData p
  let o := nativeOverlaps p
  let R := nativeTriangles p
  let Q := nativeCornerQ p
  let a := o 0 1
  let b := o 0 2
  let c := o 0 3
  let u := o 1 2
  let v := o 2 3
  let w := o 3 1
  have ha : 0 < a := atom_overlap_pos p hp hA 0 1 (by decide)
  have hb : 0 < b := atom_overlap_pos p hp hA 0 2 (by decide)
  have hc : 0 < c := atom_overlap_pos p hp hA 0 3 (by decide)
  have hu : 0 < u := atom_overlap_pos p hp hA 1 2 (by decide)
  have hv : 0 < v := atom_overlap_pos p hp hA 2 3 (by decide)
  have hw : 0 < w := atom_overlap_pos p hp hA 3 1 (by decide)
  have h10 : o 1 0 = a := tracePairing_comm _ _
  have h20 : o 2 0 = b := tracePairing_comm _ _
  have h30 : o 3 0 = c := tracePairing_comm _ _
  have h0 : d.ν0 = Real.sqrt (a*u*b) := rfl
  have h1 : d.ν1 = Real.sqrt (b*v*c) := rfl
  have h2 : d.ν2 = Real.sqrt (c*w*a) := rfl
  have hcos : d.hermitianConstants = finiteTetrahedronCosines o R := by
    funext i
    fin_cases i
    · change d.r012 / d.ν0 = d.r012 / Real.sqrt (a*u*o 2 0)
      rw [h0,h20]
    · change d.r023 / d.ν1 = d.r023 / Real.sqrt (b*v*o 3 0)
      rw [h1,h30]
    · change d.r031 / d.ν2 = d.r031 / Real.sqrt (c*w*o 1 0)
      rw [h2,h10]
  have h01 : d.ν0 * d.ν1 = b * Real.sqrt (a*u*v*c) := by
    rw [h0,h1, show a*u*b = b*(a*u) by ring, show b*v*c = b*(v*c) by ring,
      sqrt_common_factor b _ _ hb.le (by positivity), show (a*u)*(v*c) = a*u*v*c by ring]
  have h02 : d.ν0 * d.ν2 = a * Real.sqrt (c*w*u*b) := by
    rw [h0,h2, show a*u*b = a*(u*b) by ring, show c*w*a = a*(c*w) by ring,
      sqrt_common_factor a _ _ ha.le (by positivity), show (u*b)*(c*w) = c*w*u*b by ring]
  have h12 : d.ν1 * d.ν2 = c * Real.sqrt (b*v*w*a) := by
    rw [h1,h2, show b*v*c = c*(b*v) by ring, show c*w*a = c*(w*a) by ring,
      sqrt_common_factor c _ _ hc.le (by positivity), show (b*v)*(w*a) = b*v*w*a by ring]
  have h012 : d.ν0 * d.ν1 * d.ν2 = (a*b*c) * Real.sqrt (u*v*w) := by
    rw [h0,h1,h2, ← Real.sqrt_mul (by positivity : 0 ≤ a*u*b),
      ← Real.sqrt_mul (by positivity : 0 ≤ (a*u*b)*(b*v*c)),
      show (a*u*b)*(b*v*c)*(c*w*a) = (a*b*c)^2*(u*v*w) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ a*b*c)]
  have hk12 : d.mixed12 = finiteTetrahedronMixed o Q 0 := by
    change b * Q 0 / (d.ν0*d.ν1) = Q 0 / Real.sqrt (a*u*v*o 3 0)
    rw [h01,h30]
    field_simp [hb.ne', ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < a*u*v*c))]
  have hk13 : d.mixed13 = finiteTetrahedronMixed o Q 2 := by
    change a * Q 2 / (d.ν0*d.ν2) = Q 2 / Real.sqrt (c*w*u*o 2 0)
    rw [h02,h20]
    field_simp [ha.ne', ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < c*w*u*b))]
  have hk23 : d.mixed23 = finiteTetrahedronMixed o Q 1 := by
    change c * Q 1 / (d.ν1*d.ν2) = Q 1 / Real.sqrt (b*v*w*o 1 0)
    rw [h12,h10]
    field_simp [hc.ne', ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < b*v*w*a))]
  have hc4 : d.cubicConstant = finiteTetrahedronFarCosine o R := by
    change a*b*c*R 1 2 3 / (d.ν0*d.ν1*d.ν2) = R 1 2 3 / Real.sqrt (u*v*w)
    rw [h012]
    field_simp [ha.ne',hb.ne',hc.ne',ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < u*v*w))]
  change cornerCliffordParameters d.hermitianConstants d.mixed12 d.mixed13 d.mixed23
    d.cubicConstant = cornerCliffordParameters _ _ _ _ _
  rw [hcos,hk12,hk13,hk23,hc4]

/-- For the native data the Hilbert telescope uses the literal determinant
of Lemma 2.1, with the actual Appendix A.4 residual occurrences. -/
theorem atomCornerResidualTelescope_vectorIdentity
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (P : Fin 4 → H →L[ℝ] H) (hP : ∀ i, IsStarProjection (P i)) (Ω : H) :
    let s := CornerHolonomy.finiteTetrahedronParameters (nativeOverlaps p) (nativeTriangles p)
      (nativeCornerQ p)
    let occ := cornerResidualTelescopeOccurrences (atomCornerData p) (atomCornerScalar p)
    ((Matrix.of s.gramMatrix).det - s.d0^2) * ‖P 0 Ω‖^2 =
      (occ.map fun o => ⟪o.leftElement P Ω,o.leaf.residualElement P Ω⟫_ℝ).sum := by
  have h := cornerResidualTelescope_vectorIdentity (atomCornerData p) (atomCornerScalar p)
    (atomCorner_conditions p hp hA) P hP Ω
  simpa only [atomCornerData_scalarParameters_eq_finiteTetrahedron p hp hA] using h

end BlockB

end AlbertSequential
