module

public import NativeAnalysis

/-! Real-part trace association for the actual compact Cayley–Dickson product.
Only quaternion associativity is used. Octonion associativity is never assumed.
Finite matrix trace then transfers this scalar identity to the Albert product. -/

@[expose] public section
noncomputable section
namespace AlbertSequential.NativeAnalysis

theorem quaternion_real_mul_comm (a b : Quaternion ℝ) : (a * b).re = (b * a).re := by
  rw [Quaternion.re_mul, Quaternion.re_mul]
  ring

theorem quaternion_real_triple_cyclic (a b c : Quaternion ℝ) :
    (a * (b * c)).re = (b * (c * a)).re := by
  rw [quaternion_real_mul_comm a (b * c), mul_assoc]

/-- The octonion associator has zero real part in the literal shared convention. -/
theorem octonionReal_mul_associative (x y z : Octonion) :
    octonionReal (octonionMul (octonionMul x y) z) =
      octonionReal (octonionMul x (octonionMul y z)) := by
  change ((x.1 * y.1 - star y.2 * x.2) * z.1 -
      star z.2 * (y.2 * x.1 + x.2 * star y.1)).re =
    (x.1 * (y.1 * z.1 - star z.2 * y.2) -
      star (z.2 * y.1 + y.2 * star z.1) * x.2).re
  simp only [sub_mul, mul_sub, mul_add, add_mul, star_add, star_mul, star_star,
    Quaternion.re_add, Quaternion.re_sub, mul_assoc]
  rw [← quaternion_real_triple_cyclic z.1 (star y.2) x.2,
    ← quaternion_real_triple_cyclic x.1 (star z.2) y.2,
    ← quaternion_real_triple_cyclic (star y.1) (star z.2) x.2]
  ring

theorem octonionMul_finsetSum_left {ι : Type*} (s : Finset ι)
    (f : ι → Octonion) (y : Octonion) :
    octonionMul (∑ i ∈ s, f i) y = ∑ i ∈ s, octonionMul (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [octonionMul_zero_left]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, octonionMul_add_left, ih]

theorem octonionMul_finsetSum_right {ι : Type*} (s : Finset ι)
    (x : Octonion) (f : ι → Octonion) :
    octonionMul x (∑ i ∈ s, f i) = ∑ i ∈ s, octonionMul x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [octonionMul_zero_right]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, octonionMul_add_right, ih]

theorem octonionReal_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Octonion) :
    octonionReal (∑ i ∈ s, f i) = ∑ i ∈ s, octonionReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [octonionReal_zero]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, octonionReal_add, ih]

theorem octonionConj_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Octonion) :
    octonionConj (∑ i ∈ s, f i) = ∑ i ∈ s, octonionConj (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [octonionConj_zero]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, octonionConj_add, ih]

abbrev NativeOctonionMatrix := Fin 3 → Fin 3 → Octonion

def matrixRealTrace (M : NativeOctonionMatrix) : ℝ :=
  ∑ i : Fin 3, octonionReal (M i i)

theorem matrixRealTrace_mul_comm (M N : NativeOctonionMatrix) :
    matrixRealTrace (octonionMatrixMul M N) = matrixRealTrace (octonionMatrixMul N M) := by
  unfold matrixRealTrace octonionMatrixMul
  simp_rw [octonionReal_finsetSum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  exact octonionReal_mul_comm _ _

theorem matrixRealTrace_mul_associative (M N P : NativeOctonionMatrix) :
    matrixRealTrace (octonionMatrixMul (octonionMatrixMul M N) P) =
      matrixRealTrace (octonionMatrixMul M (octonionMatrixMul N P)) := by
  unfold matrixRealTrace octonionMatrixMul
  simp_rw [octonionMul_finsetSum_left, octonionMul_finsetSum_right,
    octonionReal_finsetSum, octonionReal_mul_associative]
  congr 1
  funext i
  exact Finset.sum_comm

private theorem scalar_real_of_conjugate_fixed (z : Octonion)
    (h : octonionConj z = z) : octonionScalar (octonionReal z) = z := by
  have ha := congrArg (fun z : Octonion => z.1) h
  have hb := congrArg (fun z : Octonion => z.2) h
  change star z.1 = z.1 at ha
  change -z.2 = z.2 at hb
  apply Prod.ext
  · exact (Quaternion.star_eq_self.mp ha).symm
  · change (0 : Quaternion ℝ) = z.2
    apply Quaternion.ext
    all_goals
      first
      | have hh := congrArg (fun q : Quaternion ℝ => q.re) hb
        change -z.2.re = z.2.re at hh
        change 0 = z.2.re
        linarith
      | have hh := congrArg (fun q : Quaternion ℝ => q.imI) hb
        change -z.2.imI = z.2.imI at hh
        change 0 = z.2.imI
        linarith
      | have hh := congrArg (fun q : Quaternion ℝ => q.imJ) hb
        change -z.2.imJ = z.2.imJ at hh
        change 0 = z.2.imJ
        linarith
      | have hh := congrArg (fun q : Quaternion ℝ => q.imK) hb
        change -z.2.imK = z.2.imK at hh
        change 0 = z.2.imK
        linarith

theorem albertMatrix_conjugate (x : Albert) (i j : Fin 3) :
    octonionConj (albertMatrix x i j) = albertMatrix x j i := by
  fin_cases i <;> fin_cases j <;>
    simp [albertMatrix, octonionConj_scalar, octonionConj_conj]

theorem albertMatrix_reconstruct (M : NativeOctonionMatrix)
    (h : ∀ i j, octonionConj (M i j) = M j i) :
    albertMatrix (albertCoordinates M) = M := by
  funext i j
  fin_cases i <;> fin_cases j
  · exact scalar_real_of_conjugate_fixed (M 0 0) (h 0 0)
  · rfl
  · rfl
  · exact h 0 1
  · exact scalar_real_of_conjugate_fixed (M 1 1) (h 1 1)
  · rfl
  · exact h 0 2
  · exact h 1 2
  · exact scalar_real_of_conjugate_fixed (M 2 2) (h 2 2)

theorem octonionMatrixMul_conjugate (M N : NativeOctonionMatrix)
    (hM : ∀ i j, octonionConj (M i j) = M j i)
    (hN : ∀ i j, octonionConj (N i j) = N j i) (i j : Fin 3) :
    octonionConj (octonionMatrixMul M N i j) = octonionMatrixMul N M j i := by
  unfold octonionMatrixMul
  rw [octonionConj_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [octonionConj_mul, hM, hN]

theorem albertMatrix_jordanMul (x y : Albert) :
    albertMatrix (jordanMul x y) = (1 / 2 : ℝ) •
      (octonionMatrixMul (albertMatrix x) (albertMatrix y) +
       octonionMatrixMul (albertMatrix y) (albertMatrix x)) := by
  let R := octonionMatrixMul (albertMatrix x) (albertMatrix y) +
       octonionMatrixMul (albertMatrix y) (albertMatrix x)
  have hR : ∀ i j, octonionConj (R i j) = R j i := by
    intro i j
    change octonionConj (octonionMatrixMul (albertMatrix x) (albertMatrix y) i j +
      octonionMatrixMul (albertMatrix y) (albertMatrix x) i j) = _
    rw [octonionConj_add,
      octonionMatrixMul_conjugate _ _ (albertMatrix_conjugate x) (albertMatrix_conjugate y),
      octonionMatrixMul_conjugate _ _ (albertMatrix_conjugate y) (albertMatrix_conjugate x)]
    exact add_comm _ _
  have hs : jordanMul x y = albertCoordinates ((1 / 2 : ℝ) • R) := by
    apply Prod.ext
    · funext i
      change (1 / 2 : ℝ) * octonionReal (R i i) =
        octonionReal ((1 / 2 : ℝ) • R i i)
      exact (octonionReal_smul _ _).symm
    · funext i
      fin_cases i <;> rfl
  rw [hs]
  apply albertMatrix_reconstruct
  intro i j
  change octonionConj ((1 / 2 : ℝ) • R i j) = (1 / 2 : ℝ) • R j i
  rw [octonionConj_smul, hR]

theorem matrixRealTrace_albertMatrix (x : Albert) :
    matrixRealTrace (albertMatrix x) = albertTrace x := by
  unfold matrixRealTrace albertTrace
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> rfl

private theorem matrixRealTrace_add (M N : NativeOctonionMatrix) :
    matrixRealTrace (M + N) = matrixRealTrace M + matrixRealTrace N := by
  unfold matrixRealTrace
  change (∑ i : Fin 3, octonionReal (M i i + N i i)) = _
  simp_rw [octonionReal_add]
  exact Finset.sum_add_distrib

private theorem matrixRealTrace_smul (r : ℝ) (M : NativeOctonionMatrix) :
    matrixRealTrace (r • M) = r * matrixRealTrace M := by
  unfold matrixRealTrace
  change (∑ i : Fin 3, octonionReal (r • M i i)) = _
  simp_rw [octonionReal_smul]
  exact (Finset.mul_sum _ _ _).symm

private theorem matrixMul_add_left (M N P : NativeOctonionMatrix) :
    octonionMatrixMul (M + N) P = octonionMatrixMul M P + octonionMatrixMul N P := by
  funext i j
  unfold octonionMatrixMul
  change (∑ k : Fin 3, octonionMul (M i k + N i k) (P k j)) = _
  simp_rw [octonionMul_add_left]
  exact Finset.sum_add_distrib

private theorem matrixMul_add_right (M N P : NativeOctonionMatrix) :
    octonionMatrixMul M (N + P) = octonionMatrixMul M N + octonionMatrixMul M P := by
  funext i j
  unfold octonionMatrixMul
  change (∑ k : Fin 3, octonionMul (M i k) (N k j + P k j)) = _
  simp_rw [octonionMul_add_right]
  exact Finset.sum_add_distrib

private theorem matrixMul_smul_left (r : ℝ) (M N : NativeOctonionMatrix) :
    octonionMatrixMul (r • M) N = r • octonionMatrixMul M N := by
  funext i j
  unfold octonionMatrixMul
  change (∑ k : Fin 3, octonionMul (r • M i k) (N k j)) = _
  simp_rw [octonionMul_smul_left]
  exact Finset.smul_sum.symm

private theorem matrixMul_smul_right (r : ℝ) (M N : NativeOctonionMatrix) :
    octonionMatrixMul M (r • N) = r • octonionMatrixMul M N := by
  funext i j
  unfold octonionMatrixMul
  change (∑ k : Fin 3, octonionMul (M i k) (r • N k j)) = _
  simp_rw [octonionMul_smul_right]
  exact Finset.smul_sum.symm

theorem tracePairing_matrix_formula (x y : Albert) :
    tracePairing x y = matrixRealTrace (octonionMatrixMul (albertMatrix x) (albertMatrix y)) := by
  unfold tracePairing
  rw [← matrixRealTrace_albertMatrix, albertMatrix_jordanMul,
    matrixRealTrace_smul, matrixRealTrace_add,
    matrixRealTrace_mul_comm (albertMatrix y) (albertMatrix x)]
  ring

/-- Associativity belongs to the real trace form, not to octonion multiplication. -/
theorem tracePairing_associative (x y z : Albert) :
    tracePairing (jordanMul x y) z = tracePairing x (jordanMul y z) := by
  have hcyc : matrixRealTrace (octonionMatrixMul
      (octonionMatrixMul (albertMatrix y) (albertMatrix x)) (albertMatrix z)) =
      matrixRealTrace (octonionMatrixMul (albertMatrix x)
        (octonionMatrixMul (albertMatrix z) (albertMatrix y))) := by
    rw [matrixRealTrace_mul_associative,
      matrixRealTrace_mul_comm (albertMatrix y), matrixRealTrace_mul_associative]
  rw [tracePairing_matrix_formula, tracePairing_matrix_formula,
    albertMatrix_jordanMul, albertMatrix_jordanMul,
    matrixMul_smul_left, matrixMul_smul_right, matrixMul_add_left, matrixMul_add_right,
    matrixRealTrace_smul, matrixRealTrace_smul,
    matrixRealTrace_add, matrixRealTrace_add,
    matrixRealTrace_mul_associative, hcyc]

theorem jordanMul_self_adjoint (x y z : Albert) :
    tracePairing (jordanMul x y) z = tracePairing y (jordanMul x z) := by
  rw [jordanMul_comm x y, tracePairing_associative]

theorem quadraticMap_self_adjoint (x y z : Albert) :
    tracePairing (quadraticMap x y) z = tracePairing y (quadraticMap x z) := by
  unfold quadraticMap
  simp only [two_smul, tracePairing_sub_left, tracePairing_sub_right,
    tracePairing_add_left, tracePairing_add_right]
  rw [jordanMul_self_adjoint x (jordanMul x y) z,
    jordanMul_self_adjoint x y (jordanMul x z),
    jordanMul_self_adjoint (jordanMul x x) y z]

end AlbertSequential.NativeAnalysis
