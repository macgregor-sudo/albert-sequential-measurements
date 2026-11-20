/- SPDX-License-Identifier: Apache-2.0 -/
module

public import TetrahedronRelabeling
public import ThirteenTracesAndAform
public import CornerNumericalData
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The normalized tetrahedron identity on an arbitrary real Hilbert space. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
open scoped Matrix

namespace AlbertSequential

/-- The positive normalizing radius of an ordered triangle. -/
def tetrahedronTriangleRadius (o : OverlapData) (j k l : Fin 4) : ℝ :=
  Real.sqrt (o j k * o k l * o l j)

/-- Product of the three triangle radii at the selected base. -/
def tetrahedronRadiusProduct (o : OverlapData) (j k l m : Fin 4) : ℝ :=
  tetrahedronTriangleRadius o j k l * tetrahedronTriangleRadius o j l m *
    tetrahedronTriangleRadius o j m k

/-- The printed normalized statistic, for the actual three ordered
quadruple scalars (Q_{j;klm},Q_{j;lmk},Q_{j;mkl}). -/
def tetrahedronNormalizedAtOrder (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ) : ℝ :=
  let c1 := R j k l / tetrahedronTriangleRadius o j k l
  let c2 := R j l m / tetrahedronTriangleRadius o j l m
  let c3 := R j m k / tetrahedronTriangleRadius o j m k
  let c4 := R k l m / tetrahedronTriangleRadius o k l m
  let K12 := Q 0 / Real.sqrt (o j k * o k l * o l m * o m j)
  let K23 := Q 1 / Real.sqrt (o j l * o l m * o m k * o k j)
  let K31 := Q 2 / Real.sqrt (o j m * o m k * o k l * o l j)
  let M11 := 1 - c1 ^ 2
  let M22 := 1 - c2 ^ 2
  let M33 := 1 - c3 ^ 2
  let M12 := c1 * c2 - K12
  let M23 := c2 * c3 - K23
  let M13 := c3 * c1 - K31
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![![M11,M12,M13],![M12,M22,M23],![M13,M23,M33]]
  let S := c1 * c2 * c3 - c1 * M23 - c2 * M13 - c3 * M12
  M.det - (c4 - S) ^ 2

theorem fpTetraDtet_eq_normalizedAtOrder (σ : Equiv.Perm (Fin 4))
    (o : OverlapData) (R : TriangleData) (t : Fin 3 → ℝ) :
    fpTetraDtet σ o R t =
      tetrahedronNormalizedAtOrder o R (σ 0) (σ 1) (σ 2) (σ 3)
        ![tetraQOfTraces t (σ 0) (σ 1) (σ 2) (σ 3),
          tetraQOfTraces t (σ 0) (σ 2) (σ 3) (σ 1),
          tetraQOfTraces t (σ 0) (σ 3) (σ 1) (σ 2)] := rfl

private theorem sqrt_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a*b*c) = Real.sqrt a * Real.sqrt b * Real.sqrt c := by
  rw [Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_mul ha]

private theorem sqrt_four (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a*b*c*d) = Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg ha hb) hc), sqrt_three a b c ha hb]

private theorem tetrahedron_order_edges {j k l m : Fin 4}
    (h : Function.Injective (![j,k,l,m] : Fin 4 → Fin 4)) :
    j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m := by
  refine ⟨fun h' => (by decide : (0 : Fin 4) ≠ 1) (h h'),
    fun h' => (by decide : (0 : Fin 4) ≠ 2) (h h'),
    fun h' => (by decide : (0 : Fin 4) ≠ 3) (h h'),
    fun h' => (by decide : (1 : Fin 4) ≠ 2) (h h'),
    fun h' => (by decide : (1 : Fin 4) ≠ 3) (h h'),
    fun h' => (by decide : (2 : Fin 4) ≠ 3) (h h')⟩

/-- The printed scale identity (\Delta_j=(\nu_1\nu_2\nu_3)^2D_{tet}), for
arbitrary symmetric strictly positive off-diagonal overlaps and ordered scalar data. -/
theorem tetrahedronDiscriminant_eq_radius_sq_mul_normalized
    (o : OverlapData) (R : TriangleData) (j k l m : Fin 4) (Q : Fin 3 → ℝ)
    (ho : ∀ x y, o x y = o y x) (hpos : ∀ x y, x ≠ y → 0 < o x y)
    (horder : Function.Injective (![j,k,l,m] : Fin 4 → Fin 4)) :
    tetrahedronDiscriminantAtOrder o R j k l m Q =
      tetrahedronRadiusProduct o j k l m ^ 2 * tetrahedronNormalizedAtOrder o R j k l m Q := by
  obtain ⟨hjk,hjl,hjm,hkl,hkm,hlm⟩ := tetrahedron_order_edges horder
  have h01 := hpos j k hjk
  have h02 := hpos j l hjl
  have h03 := hpos j m hjm
  have h12 := hpos k l hkl
  have h13 := hpos k m hkm
  have h23 := hpos l m hlm
  unfold tetrahedronDiscriminantAtOrder tetrahedronRadiusProduct tetrahedronNormalizedAtOrder
    tetrahedronTriangleRadius
  simp only [ho l j, ho m j, ho m k, ho k j]
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [sqrt_three _ _ _ h01.le h12.le, sqrt_three _ _ _ h02.le h23.le,
    sqrt_three _ _ _ h03.le h13.le, sqrt_three _ _ _ h12.le h23.le,
    sqrt_four _ _ _ _ h01.le h12.le h23.le, sqrt_four _ _ _ _ h02.le h23.le h13.le,
    sqrt_four _ _ _ _ h03.le h13.le h12.le]
  rw [← Real.sq_sqrt h01.le, ← Real.sq_sqrt h02.le, ← Real.sq_sqrt h03.le,
    ← Real.sq_sqrt h12.le, ← Real.sq_sqrt h13.le, ← Real.sq_sqrt h23.le]
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  field_simp [Real.sqrt_ne_zero'.mpr h01, Real.sqrt_ne_zero'.mpr h02,
    Real.sqrt_ne_zero'.mpr h03, Real.sqrt_ne_zero'.mpr h12,
    Real.sqrt_ne_zero'.mpr h13, Real.sqrt_ne_zero'.mpr h23]
  ring

theorem tetrahedronRadiusProduct_pos
    (o : OverlapData) (j k l m : Fin 4)
    (hpos : ∀ x y, x ≠ y → 0 < o x y)
    (horder : Function.Injective (![j,k,l,m] : Fin 4 → Fin 4)) :
    0 < tetrahedronRadiusProduct o j k l m := by
  obtain ⟨hjk,hjl,hjm,hkl,hkm,hlm⟩ := tetrahedron_order_edges horder
  have hr {a b c : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
      0 < tetrahedronTriangleRadius o a b c :=
    Real.sqrt_pos.2 (mul_pos (mul_pos (hpos _ _ hab) (hpos _ _ hbc)) (hpos _ _ hca))
  exact mul_pos (mul_pos (hr hjk hkl hjl.symm) (hr hjl hlm hjm.symm))
    (hr hjm hkm.symm hjk.symm)

universe u

/-- Core Theorem 5.9 on the bounded real operators of any real Hilbert space.
The supplied R1–R3 bundle records the four idempotents, four triangles, and
three ordered quadruples. The proof applies even without self-adjointness. -/
theorem hilbert_tetrahedronNormalized_eq_zero
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Fin 4 → H →L[ℝ] H) (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ)
    (hR : CornerRelationsAtOrder P o R j k l m Q)
    (hpos : ∀ x y, x ≠ y → 0 < o x y) (hP : P j ≠ 0) :
    tetrahedronNormalizedAtOrder o R j k l m Q = 0 := by
  have hd := tetrahedron_annihilates_at_order P o R j k l m Q hR
  have hΔ : tetrahedronDiscriminantAtOrder o R j k l m Q = 0 :=
    (smul_eq_zero.mp hd).resolve_right hP
  rw [tetrahedronDiscriminant_eq_radius_sq_mul_normalized o R j k l m Q
    hR.overlap_symmetric hpos hR.distinct] at hΔ
  exact (mul_eq_zero.mp hΔ).resolve_left
    (pow_ne_zero 2 (tetrahedronRadiusProduct_pos o j k l m hpos hR.distinct).ne')

/-- Trace-input form of the same identity, using the existing four-point
statistic and the literal ordered (Q) computed from the double-pair traces. -/
theorem hilbert_fpTetraDtet_eq_zero
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Fin 4 → H →L[ℝ] H) (o : OverlapData) (R : TriangleData)
    (σ : Equiv.Perm (Fin 4)) (t : Fin 3 → ℝ)
    (hR : CornerRelationsAtOrder P o R (σ 0) (σ 1) (σ 2) (σ 3)
      ![tetraQOfTraces t (σ 0) (σ 1) (σ 2) (σ 3),
        tetraQOfTraces t (σ 0) (σ 2) (σ 3) (σ 1),
        tetraQOfTraces t (σ 0) (σ 3) (σ 1) (σ 2)])
    (hpos : ∀ x y, x ≠ y → 0 < o x y) (hP : P (σ 0) ≠ 0) :
    fpTetraDtet σ o R t = 0 := by
  rw [fpTetraDtet_eq_normalizedAtOrder]
  exact hilbert_tetrahedronNormalized_eq_zero P o R _ _ _ _ _ hR hpos hP

/-- Inputs to the existing normalized holonomy API, in the same cyclic order
as the displayed normalized statistic. -/
def tetrahedronHolonomyData (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ) : CornerNumericalData where
  o01 := o j k
  o02 := o j l
  o03 := o j m
  o12 := o k l
  o23 := o l m
  o31 := o m k
  r012 := R j k l
  r023 := R j l m
  r031 := R j m k
  r123 := R k l m
  q123 := Q 0
  q231 := Q 1
  q312 := Q 2
  ν0 := tetrahedronTriangleRadius o j k l
  ν1 := tetrahedronTriangleRadius o j l m
  ν2 := tetrahedronTriangleRadius o j m k

/-- The scaled contraction constants used by the existing corner API agree
exactly with the printed square-root denominators. -/
theorem tetrahedronHolonomyData_constants
    (o : OverlapData) (R : TriangleData) (j k l m : Fin 4) (Q : Fin 3 → ℝ)
    (ho : ∀ x y, o x y = o y x) (hpos : ∀ x y, x ≠ y → 0 < o x y)
    (horder : Function.Injective (![j,k,l,m] : Fin 4 → Fin 4)) :
    let d := tetrahedronHolonomyData o R j k l m Q
    d.mixed12 = Q 0 / Real.sqrt (o j k * o k l * o l m * o m j) ∧
    d.mixed23 = Q 1 / Real.sqrt (o j l * o l m * o m k * o k j) ∧
    d.mixed13 = Q 2 / Real.sqrt (o j m * o m k * o k l * o l j) ∧
    d.cubicConstant = R k l m / tetrahedronTriangleRadius o k l m := by
  obtain ⟨hjk,hjl,hjm,hkl,hkm,hlm⟩ := tetrahedron_order_edges horder
  have h01 := hpos j k hjk
  have h02 := hpos j l hjl
  have h03 := hpos j m hjm
  have h12 := hpos k l hkl
  have h13 := hpos k m hkm
  have h23 := hpos l m hlm
  dsimp only [tetrahedronHolonomyData, tetrahedronTriangleRadius, CornerNumericalData.mixed12,
    CornerNumericalData.mixed23, CornerNumericalData.mixed13, CornerNumericalData.cubicConstant]
  simp only [ho l j, ho m j, ho m k, ho k j]
  simp only [sqrt_three _ _ _ h01.le h12.le, sqrt_three _ _ _ h02.le h23.le,
    sqrt_three _ _ _ h03.le h13.le, sqrt_three _ _ _ h12.le h23.le,
    sqrt_four _ _ _ _ h01.le h12.le h23.le, sqrt_four _ _ _ _ h02.le h23.le h13.le,
    sqrt_four _ _ _ _ h03.le h13.le h12.le]
  rw [← Real.sq_sqrt h01.le, ← Real.sq_sqrt h02.le, ← Real.sq_sqrt h03.le]
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    field_simp [Real.sqrt_ne_zero'.mpr h01, Real.sqrt_ne_zero'.mpr h02, Real.sqrt_ne_zero'.mpr h03,
      Real.sqrt_ne_zero'.mpr h12, Real.sqrt_ne_zero'.mpr h13, Real.sqrt_ne_zero'.mpr h23]

theorem tetrahedronNormalized_eq_holonomy_discriminant
    (o : OverlapData) (R : TriangleData) (j k l m : Fin 4) (Q : Fin 3 → ℝ)
    (ho : ∀ x y, o x y = o y x) (hpos : ∀ x y, x ≠ y → 0 < o x y)
    (horder : Function.Injective (![j,k,l,m] : Fin 4 → Fin 4)) :
    tetrahedronNormalizedAtOrder o R j k l m Q =
      (tetrahedronHolonomyData o R j k l m Q).scalarParameters.discriminant := by
  let d := tetrahedronHolonomyData o R j k l m Q
  obtain ⟨h12,h23,h13,h4⟩ := tetrahedronHolonomyData_constants o R j k l m Q ho hpos horder
  change _ = d.scalarParameters.discriminant
  dsimp only [tetrahedronNormalizedAtOrder]
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [CornerNumericalData.scalarParameters, CornerHolonomy.cornerCliffordParameters,
    CliffordScalarParameters.discriminant, CornerHolonomy.cornerScalarPart]
  rw [show d.mixed12 = _ from h12, show d.mixed23 = _ from h23,
    show d.mixed13 = _ from h13, show d.cubicConstant = _ from h4]
  simp only [d, tetrahedronHolonomyData, CornerNumericalData.hermitianConstants, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

section Holonomies

open CornerHolonomy

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

private theorem normalized_triangle_defects_zero (P : Fin 4 → A) (o : OverlapData)
    (hp : ∀ i, star (P i) = P i) (he : ∀ i, P i * P i = P i)
    (ho : ∀ i i', o i i' = o i' i) (hpos : ∀ i i', i ≠ i' → 0 < o i i')
    (hr : ∀ i i', i ≠ i' → P i * P i' * P i = o i i' • P i)
    (j k l : Fin 4) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (r : ℝ)
    (htri : P j * (P k * P l + P l * P k) * P j = (2 * r) • P j) :
    let ν := tetrahedronTriangleRadius o j k l
    let h := normalizedCornerWord (P j) (P k) (P l) ν
    hermitianDefect (P j) h (r/ν) = 0 ∧
      leftUnitarityDefect (P j) h = 0 ∧ rightUnitarityDefect (P j) h = 0 := by
  let ν := tetrahedronTriangleRadius o j k l
  have hν : 0 < ν :=
    Real.sqrt_pos.2 (mul_pos (mul_pos (hpos j k hjk) (hpos k l hkl)) (hpos l j hjl.symm))
  have hνsq : ν ^ 2 = o k j * o k l * o j l := by
    change (Real.sqrt (o j k * o k l * o l j)) ^ 2 = _
    rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (hpos j k hjk).le (hpos k l hkl).le) (hpos l j hjl.symm).le), ho j k, ho l j]
  have hH := normalizedHermitian_defect_expansion
    (P j) (P k) (P l) (hp j) (hp k) (hp l) r ν hν.ne'
  have hU := normalizedLeftUnitarity_defect_expansion
    (P j) (P k) (P l) (he j) (hp j) (hp k) (hp l)
    (o k j) (o k l) (o j l) ν hν.ne' hνsq
  have hV := normalizedRightUnitarity_defect_expansion
    (P j) (P k) (P l) (he j) (hp j) (hp k) (hp l)
    (o k j) (o k l) (o j l) ν hν.ne' hνsq
  simp only [triangleDefectElement, htri, sub_self] at hH
  have hLK : P l * P k * P l = o k l • P l := by rw [ho k l]; exact hr l k hkl.symm
  have hLJ : P l * P j * P l = o j l • P l := by rw [ho j l]; exact hr l j hjl.symm
  have hJK : P j * P k * P j = o k j • P j := by rw [ho k j]; exact hr j k hjk
  simp only [pairDefectElement, hr k j hjk.symm, hLK, hr j l hjl, sub_self,
    mul_zero, zero_mul, smul_zero, add_zero] at hU
  simp only [pairDefectElement, hLJ, hr k l hkl, hJK,
    sub_self, mul_zero, zero_mul, smul_zero, add_zero] at hV
  exact ⟨(smul_eq_zero.mp hH).resolve_left (by positivity),
    (smul_eq_zero.mp hU).resolve_left (pow_ne_zero 2 hν.ne'),
    (smul_eq_zero.mp hV).resolve_left (pow_ne_zero 2 hν.ne')⟩

private theorem normalized_pair_defect_zero (J K L M : A)
    (hJJ : J * J = J) (hJ : star J = J) (hK : star K = K)
    (hL : star L = L) (hM : star M = M) {b q ν μ : ℝ}
    (hν : 0 < ν) (hμ : 0 < μ)
    (hpair : L * J * L = b • L)
    (hquad : J * (K * L * M + M * L * K) * J = (2*q) • J) :
    pairProductDefect J (normalizedCornerWord J K L ν) (normalizedCornerWord J L M μ)
      (b*q/(ν*μ)) = 0 := by
  have h := normalizedPairProduct_defect_expansion J K L M hJJ hJ hK hL hM b q ν μ hν.ne' hμ.ne'
  simp only [pairDefectElement, tripleDefectElement, hpair, hquad, sub_self,
    mul_zero, zero_mul, smul_zero, add_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by positivity)

/-- The normalized corner holonomies are supported and unitary in the base
corner, with the printed scalar Hermitian parts, mixed products and far face. -/
theorem tetrahedronNormalizedHolonomy_defects_zero
    (P : Fin 4 → A) (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ)
    (hR : CornerRelationsAtOrder P o R j k l m Q)
    (hp : ∀ i, star (P i) = P i) (hpos : ∀ x y, x ≠ y → 0 < o x y) :
    let d := tetrahedronHolonomyData o R j k l m Q
    let h := normalizedCyclicHolonomies (P j) (P k) (P l) (P m) d.ν0 d.ν1 d.ν2
    (∀ i, CornerSupported (P j) (h i)) ∧
    (∀ i, hermitianDefect (P j) (h i) (d.hermitianConstants i) = 0 ∧
      leftUnitarityDefect (P j) (h i) = 0 ∧ rightUnitarityDefect (P j) (h i) = 0) ∧
    pairProductDefect (P j) (h 0) (h 1) d.mixed12 = 0 ∧
    pairProductDefect (P j) (h 1) (h 2) d.mixed23 = 0 ∧
    pairProductDefect (P j) (h 2) (h 0) d.mixed13 = 0 ∧
    cornerCubicDefect (P j) h d.cubicConstant = 0 := by
  let d := tetrahedronHolonomyData o R j k l m Q
  let h := normalizedCyclicHolonomies (P j) (P k) (P l) (P m) d.ν0 d.ν1 d.ν2
  obtain ⟨hjk,hjl,hjm,hkl,hkm,hlm⟩ := tetrahedron_order_edges hR.distinct
  have h0 : 0 < d.ν0 :=
    Real.sqrt_pos.2 (mul_pos (mul_pos (hpos j k hjk) (hpos k l hkl)) (hpos l j hjl.symm))
  have h1 : 0 < d.ν1 :=
    Real.sqrt_pos.2 (mul_pos (mul_pos (hpos j l hjl) (hpos l m hlm)) (hpos m j hjm.symm))
  have h2 : 0 < d.ν2 :=
    Real.sqrt_pos.2 (mul_pos (mul_pos (hpos j m hjm) (hpos m k hkm.symm)) (hpos k j hjk.symm))
  have pair (i : Fin 4) (hi : i ≠ j) : P i * P j * P i = o j i • P i := by
    rw [hR.overlap_symmetric j i]
    exact hR.pair i j hi
  refine ⟨normalizedCyclicHolonomies_supported _ _ _ _ (hR.idempotent j) _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact normalized_triangle_defects_zero P o hp hR.idempotent hR.overlap_symmetric hpos
        hR.pair j k l hjk hjl hkl _ hR.triangle_jkl
    · exact normalized_triangle_defects_zero P o hp hR.idempotent hR.overlap_symmetric hpos
        hR.pair j l m hjl hjm hlm _ hR.triangle_jlm
    · exact normalized_triangle_defects_zero P o hp hR.idempotent hR.overlap_symmetric hpos
        hR.pair j m k hjm hjk hkm.symm _ hR.triangle_jmk
  · exact normalized_pair_defect_zero _ _ _ _ (hR.idempotent j) (hp j) (hp k) (hp l) (hp m)
      h0 h1 (pair l hjl.symm) hR.quadruple_klm
  · exact normalized_pair_defect_zero _ _ _ _ (hR.idempotent j) (hp j) (hp l) (hp m) (hp k)
      h1 h2 (pair m hjm.symm) hR.quadruple_lmk
  · change pairProductDefect (P j) (h 2) (h 0) d.mixed13 = 0
    rw [d.mixed13_reverse_denominator]
    exact normalized_pair_defect_zero _ _ _ _ (hR.idempotent j) (hp j) (hp m) (hp k) (hp l)
      h2 h0 (pair k hjk.symm) hR.quadruple_mkl
  · have hc := normalizedCubic_defect_expansion
      (P j) (P k) (P l) (P m) (hR.idempotent j) (hp j) (hp k) (hp l) (hp m)
      (o j k) (o j l) (o j m) (R k l m) d.ν0 d.ν1 d.ν2 h0.ne' h1.ne' h2.ne'
    simp only [pairDefectElement, triangleDefectElement, pair m hjm.symm, pair l hjl.symm,
      hR.triangle_klm, hR.pair j k hjk, sub_self, mul_zero, zero_mul, smul_zero, add_zero] at hc
    exact (smul_eq_zero.mp hc).resolve_left (by positivity)

/-- The normalized Clifford and volume identities on the actual base corner.
The base projection is the unit on that corner, so it appears in the
ambient operator equalities. -/
theorem tetrahedronNormalizedHolonomy_clifford
    (P : Fin 4 → A) (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ)
    (hR : CornerRelationsAtOrder P o R j k l m Q)
    (hp : ∀ i, star (P i) = P i) (hpos : ∀ x y, x ≠ y → 0 < o x y) :
    let d := tetrahedronHolonomyData o R j k l m Q
    let h := normalizedCyclicHolonomies (P j) (P k) (P l) (P m) d.ν0 d.ν1 d.ν2
    let N := fun i => skewHermitianPart (h i)
    let s := d.scalarParameters
    let Γ := cliffordVolume N
    (∀ a b, N a * N b + N b * N a = (-2 * s.gramMatrix a b) • P j) ∧
    Γ = N 0 * N 1 * N 2 + s.w • N 0 - s.v • N 1 + s.u • N 2 ∧
    Γ = s.d0 • P j ∧ Γ * Γ = (Matrix.of s.gramMatrix).det • P j := by
  let d := tetrahedronHolonomyData o R j k l m Q
  let h := normalizedCyclicHolonomies (P j) (P k) (P l) (P m) d.ν0 d.ν1 d.ν2
  let N := fun i => skewHermitianPart (h i)
  let s := d.scalarParameters
  let Γ := cliffordVolume N
  let E := P j
  let c := d.hermitianConstants
  obtain ⟨hsup,hdiag,h01,h12,h20,hfar⟩ :=
    tetrahedronNormalizedHolonomy_defects_zero P o R j k l m Q hR hp hpos
  have hN (i : Fin 3) : CornerSupported E (N i) :=
    skewHermitianPart_supported E (h i) (hp j) (hsup i)
  have hH (i : Fin 3) : hermitianDefect E (h i) (c i) = 0 := (hdiag i).1
  have hsquare (i : Fin 3) : N i * N i = (-s.diagonal i) • E := by
    have hz := squareDefect_reduction E (h i) (hR.idempotent j) (hp j) (hsup i) (c i)
    have hL : leftUnitarityDefect E (h i) = 0 := (hdiag i).2.1
    have hR' : rightUnitarityDefect E (h i) = 0 := (hdiag i).2.2
    rw [hH i, hL, hR', mul_zero, add_zero, smul_zero, sub_zero] at hz
    change N i * N i + (1 - c i ^ 2) • E = 0 at hz
    have hsi : s.diagonal i = 1 - c i ^ 2 := by fin_cases i <;> rfl
    rw [hsi, neg_smul]
    linear_combination (norm := module) hz
  have hpair (a b : Fin 3) (K : ℝ) (hK : pairProductDefect E (h a) (h b) K = 0) :
       pairCliffordDefect E (h a) (h b) (c a) (c b) K = 0 := by
    rw [pairDefect_reduction E (h a) (h b) (hR.idempotent j) (hp j)
      (hsup a) (hsup b), hK, hH a, hH b]
    simp
  have hp01 := hpair 0 1 d.mixed12 h01
  have hp12 := hpair 1 2 d.mixed23 h12
  have hp20 := hpair 2 0 d.mixed13 h20
  have hp02 : pairCliffordDefect E (h 0) (h 2) (c 0) (c 2) d.mixed13 = 0 := by
    unfold pairCliffordDefect at hp20 ⊢
    rw [mul_comm (c 0) (c 2), add_comm (N 0 * N 2) (N 2 * N 0)]
    exact hp20
  have hc01 : N 0 * N 1 + N 1 * N 0 = (-2 * s.u) • E := by
    change N 0 * N 1 + N 1 * N 0 + (2 * s.u) • E = 0 at hp01
    linear_combination (norm := module) hp01
  have hc02 : N 0 * N 2 + N 2 * N 0 = (-2 * s.v) • E := by
    change N 0 * N 2 + N 2 * N 0 + (2 * s.v) • E = 0 at hp02
    linear_combination (norm := module) hp02
  have hc12 : N 1 * N 2 + N 2 * N 1 = (-2 * s.w) • E := by
    change N 1 * N 2 + N 2 * N 1 + (2 * s.w) • E = 0 at hp12
    linear_combination (norm := module) hp12
  have hc (a b : Fin 3) : N a * N b + N b * N a = (-2 * s.gramMatrix a b) • E := by
    by_cases hab : a = b
    · subst b
      rw [s.gramMatrix_diagonal, hsquare]
      module
    · fin_cases a <;> fin_cases b <;> try exact (hab rfl).elim
      · exact hc01
      · exact hc02
      · exact (add_comm _ _).trans hc01
      · exact hc12
      · exact (add_comm _ _).trans hc02
      · exact (add_comm _ _).trans hc12
  have hu : N 0 * N 1 + N 1 * N 0 = (2 * (-s.u)) • E := by
    rw [show 2 * -s.u = -2 * s.u by ring]
    exact hc01
  have hv : N 0 * N 2 + N 2 * N 0 = (2 * (-s.v)) • E := by
    rw [show 2 * -s.v = -2 * s.v by ring]
    exact hc02
  have hw : N 1 * N 2 + N 2 * N 1 = (2 * (-s.w)) • E := by
    rw [show 2 * -s.w = -2 * s.w by ring]
    exact hc12
  have hΓ : Γ = N 0 * N 1 * N 2 + s.w • N 0 - s.v • N 1 + s.u • N 2 := by
    have e := (localUnit_volume_eq_half_reverse E (N 0) (N 1) (N 2) (-s.u) (-s.v) (-s.w)
      (hN 0).1 (hN 1).2 (hN 2).1 hu hv hw).symm
    change Γ = _ at e
    rw [e]
    module
  have hdata := cornerDataError_element E (hR.idempotent j) (hp j) h hsup
    c d.mixed12 d.mixed13 d.mixed23 d.cubicConstant
  have hT : hermitianProductTelescope E h c = 0 := by
    simp only [hermitianProductTelescope, hH, mul_zero, zero_mul, zero_add, smul_zero]
  have hF : cornerCubicDefect E h d.cubicConstant = 0 := hfar
  have hΓscalar : Γ = s.d0 • E := by
    rw [hF, hT, hp01, hp02, hp12] at hdata
    simp only [smul_zero, add_zero, sub_zero] at hdata
    exact sub_eq_zero.mp hdata
  refine ⟨hc, hΓ, hΓscalar, ?_⟩
  have hs := localUnit_volume_square E (N 0) (N 1) (N 2)
    (-s.m1) (-s.m2) (-s.m3) (-s.u) (-s.v) (-s.w)
    (hN 0).2 (hN 1).1 (hN 1).2 (hN 2).1 (hsquare 0) (hsquare 1) (hsquare 2) hu hv hw
  have he : Γ = N 0 * N 1 * N 2 - (-s.w) • N 0 + (-s.v) • N 1 - (-s.u) • N 2 := by
    rw [hΓ]
    module
  dsimp only at hs
  rw [← he] at hs
  rw [hs, Matrix.det_fin_three]
  simp only [Matrix.of_apply, CliffordScalarParameters.gramMatrix, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  congr 1
  ring

end Holonomies

end AlbertSequential
