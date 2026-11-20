/- SPDX-License-Identifier: Apache-2.0 -/
module

public import WindowProbabilityQuaternionicSample
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section
noncomputable section

open scoped Matrix ComplexOrder

namespace AlbertSequential.WindowProbability

/-- A positive semidefinite complex matrix has a Gram factor of any width at least its rank. -/
theorem exists_rectangularComplexGram {m n : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (hM : M.PosSemidef) (hr : M.rank ≤ n) :
    ∃ Z : Matrix (Fin m) (Fin n) ℂ, Z * Zᴴ = M := by
  classical
  let h := hM.isHermitian
  let U := h.eigenvectorUnitary
  let eigenvalue : Fin m → ℂ := fun i => (h.eigenvalues i : ℂ)
  let D := Matrix.diagonal eigenvalue
  let S := {i : Fin m // eigenvalue i ≠ 0}
  have hspec : M = (U : Matrix (Fin m) (Fin m) ℂ) * D * star (U : Matrix (Fin m) (Fin m) ℂ) :=
    h.spectral_theorem
  have hu : star (U : Matrix (Fin m) (Fin m) ℂ) * (U : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hD : D = star (U : Matrix (Fin m) (Fin m) ℂ) * M * (U : Matrix (Fin m) (Fin m) ℂ) := by
    symm
    calc
      _ = (star (U : Matrix (Fin m) (Fin m) ℂ) * U.val) * D * (star U.val * U.val) := by
        rw [hspec]
        simp only [Matrix.mul_assoc]
      _ = D := by rw [hu, one_mul, mul_one]
  have hcard : Fintype.card S ≤ n := by
    change Fintype.card {i : Fin m // eigenvalue i ≠ 0} ≤ n
    rw [← Matrix.rank_diagonal eigenvalue, show Matrix.diagonal eigenvalue = D from rfl, hD]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hr)
  let f : S ↪ Fin n := (Fintype.equivFin S).toEmbedding.trans (Fin.castLEEmb hcard)
  let R : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun i j =>
    if hi : eigenvalue i ≠ 0 then if f ⟨i, hi⟩ = j then (Real.sqrt (h.eigenvalues i) : ℂ) else 0 else 0
  have he : R * Rᴴ = D := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [show D i i = eigenvalue i from Matrix.diagonal_apply_eq _ _]
      by_cases hi : eigenvalue i = 0
      · simp [R, hi]
      · rw [Finset.sum_eq_single (f ⟨i, hi⟩)]
        · have hR : R i (f ⟨i, hi⟩) = (Real.sqrt (h.eigenvalues i) : ℂ) := by simp [R, hi]
          rw [hR, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← pow_two,
            Real.sq_sqrt (hM.eigenvalues_nonneg i)]
        · intro k _ hk
          simp [R, hi, Ne.symm hk]
        · simp
    · rw [show D i j = 0 from Matrix.diagonal_apply_ne _ hij]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hi : eigenvalue i = 0
      · simp [R, hi]
      by_cases hj : eigenvalue j = 0
      · simp [R, hj]
      by_cases hik : f ⟨i, hi⟩ = k
      · have hjk : f ⟨j, hj⟩ ≠ k := by
          intro heq
          exact hij (congrArg Subtype.val (f.injective (hik.trans heq.symm)))
        simp [R, hj, hjk]
      · simp [R, hi, hik]
  refine ⟨(U : Matrix (Fin m) (Fin m) ℂ) * R, ?_⟩
  simp only [Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc R Rᴴ, he, ← Matrix.mul_assoc]
  exact hspec.symm

theorem twoColumnComplexGram_eq_dyads {m : ℕ} (Z : Matrix (Fin m) (Fin 2) ℂ) :
    Z * Zᴴ = Matrix.vecMulVec (fun i => Z i 0) (star fun i => Z i 0) +
      Matrix.vecMulVec (fun i => Z i 1) (star fun i => Z i 1) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Pi.star_apply]

theorem quaternionOfComplexPair_eq_add_mul_j (x y : ℂ) :
    quaternionOfComplexPair x y =
      quaternionOfComplexPair x 0 + quaternionOfComplexPair y 0 * (⟨0, 0, 1, 0⟩ : Quaternion ℝ) := by
  apply Quaternion.ext <;> simp [quaternionOfComplexPair]

private theorem quaternionNorm_eq_re_mul_star (q : Quaternion ℝ) :
    quatNormSq q = (q * star q).re := by
  rw [← Quaternion.normSq_def, Quaternion.normSq_def', quatNormSq]

private theorem twoColumnGram_trace_re {m : ℕ} (Z : Matrix (Fin m) (Fin 2) ℂ) :
    (Matrix.trace (Z * Zᴴ)).re = ∑ i, quatNormSq (quaternionOfComplexPair (Z i 0) (Z i 1)) := by
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.conjTranspose_apply, quaternionNorm_eq_re_mul_star]
  exact (congrArg Complex.re (quaternionOfComplexPair_product_complexPart
    (Z i 0) (Z i 1) (Z i 0) (Z i 1))).symm

/-- The same quaternionic unit-dyad construction works in every finite matrix size. -/
theorem complexDensity_rank_le_two_quaternionicMatrixLift {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℂ) (hM : M.PosSemidef) (ht : M.trace = 1) (hr : M.rank ≤ 2) :
    ∃ Z : Matrix (Fin m) (Fin 2) ℂ, Z * Zᴴ = M ∧
      let u := fun i : Fin m => quaternionOfComplexPair (Z i 0) (Z i 1)
      let Q := Matrix.vecMulVec u (star u)
      (∑ i, quatNormSq (u i)) = 1 ∧ Q.IsHermitian ∧ Q * Q = Q ∧
      (∀ i j, (⟨(Q i j).re, (Q i j).imI⟩ : ℂ) = M i j) ∧
      Set.range Q.mulVec = Set.range (fun a : Quaternion ℝ => fun i => u i * a) := by
  obtain ⟨Z, hz⟩ := exists_rectangularComplexGram M hM hr
  let u := fun i : Fin m => quaternionOfComplexPair (Z i 0) (Z i 1)
  let Q := Matrix.vecMulVec u (star u)
  have hu : (∑ i, quatNormSq (u i)) = 1 := by
    rw [← twoColumnGram_trace_re Z, hz, ht, Complex.one_re]
  have hnorm (i : Fin m) : Quaternion.normSq (u i) = quatNormSq (u i) := by
    rw [Quaternion.normSq_def', quatNormSq]
  have hd : star u ⬝ᵥ u = (1 : Quaternion ℝ) := by
    calc
      _ = ∑ i, algebraMap ℝ (Quaternion ℝ) (quatNormSq (u i)) := by
        simp only [dotProduct, Pi.star_apply, Quaternion.star_mul_self, hnorm, Quaternion.algebraMap_def]
      _ = _ := by rw [← map_sum, hu, map_one]
  have hm (v : Fin m → Quaternion ℝ) (i : Fin m) : (Q *ᵥ v) i = u i * (star u ⬝ᵥ v) := by
    simp only [Q, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_assoc]
  refine ⟨Z, hz, hu, ?_, ?_, ?_, ?_⟩
  · change Qᴴ = Q
    apply Matrix.ext
    intro i j
    simp only [Matrix.conjTranspose_apply, Q, Matrix.vecMulVec_apply, Pi.star_apply, star_mul, star_star]
  · change Matrix.vecMulVec u (star u) * Matrix.vecMulVec u (star u) = Matrix.vecMulVec u (star u)
    rw [Matrix.vecMulVec_mul_vecMulVec, hd]
    apply Matrix.ext
    intro i j
    simp
  · intro i j
    rw [← hz]
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, quaternionOfComplexPair_product_complexPart,
       Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨star u ⬝ᵥ a, (funext (hm a)).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨fun i => u i * a, ?_⟩
      have ha : star u ⬝ᵥ (fun i => u i * a) = a := by
        unfold dotProduct at hd ⊢
        simp only [← mul_assoc, ← Finset.sum_mul, hd, one_mul]
      funext i
      rw [hm, ha]

private theorem twoColumnDyad_lifts_traceOne (Z : Matrix (Fin 3) (Fin 2) ℂ)
    (ht : Matrix.trace (Z * Zᴴ) = 1) :
    (∑ i, quatNormSq (quaternionOfComplexPair (Z i 0) (Z i 1))) = 1 ∧
      IsAtom (quaternionicDyadFromTwoColumns Z) ∧
      quaternionicDyadFromTwoColumns Z ∈ standardQuaternionicWindow.subalgebra.carrier := by
  let q := quaternionicDyadFromTwoColumns Z
  have htq : albertTrace q = 1 := by
    apply Complex.ofReal_injective
    rw [← trace_projectedMatrix standardComplexWindow, projectedMatrix_quaternionicDyadFromTwoColumns, ht]
    norm_num
  have hu : (∑ i, quatNormSq (quaternionOfComplexPair (Z i 0) (Z i 1))) = 1 := by
    rw [← twoColumnGram_trace_re Z, ht, Complex.one_re]
  have ha : IsAtom q := quatDyad_isAtom quatEmbed1 quatEmbed1_isQuatEmbedding _ 1 one_ne_zero hu
  have hm := normalizedQuaternionicDyadFromTwoColumns_mem Z
  change normalizeAlbert q ∈ standardQuaternionicWindow.subalgebra.carrier at hm
  rw [normalizeAlbert, htq, inv_one, one_smul] at hm
  exact ⟨hu, ha, hm⟩

/-- The two unit-column components yield the exact native quaternionic pure-state lift. -/
theorem complexDensity_rank_le_two_quaternionicLift (M : ComplexMatrix3) (hM : M.PosSemidef)
    (ht : M.trace = 1) (hr : M.rank ≤ 2) :
    ∃ Z : Matrix (Fin 3) (Fin 2) ℂ, Z * Zᴴ = M ∧
      (∑ i, quatNormSq (quaternionOfComplexPair (Z i 0) (Z i 1))) = 1 ∧
      IsAtom (quaternionicDyadFromTwoColumns Z) ∧
      quaternionicDyadFromTwoColumns Z ∈ standardQuaternionicWindow.subalgebra.carrier ∧
      projectedMatrix standardComplexWindow (quaternionicDyadFromTwoColumns Z) = M := by
  obtain ⟨Z, hz⟩ := exists_rectangularComplexGram M hM hr
  have htrace : (Z * Zᴴ).trace = 1 := hz ▸ ht
  obtain ⟨hn, ha, hm⟩ := twoColumnDyad_lifts_traceOne Z htrace
  exact ⟨Z, hz, hn, ha, hm, (projectedMatrix_quaternionicDyadFromTwoColumns Z).trans hz⟩

/-- In rank one the second column of the pure-state lift can be taken to be identically zero. -/
theorem complexDensity_rank_le_one_quaternionicLift (M : ComplexMatrix3) (hM : M.PosSemidef)
    (ht : M.trace = 1) (hr : M.rank ≤ 1) :
    ∃ Z : Matrix (Fin 3) (Fin 2) ℂ, (∀ i, Z i 1 = 0) ∧ Z * Zᴴ = M ∧
      (∑ i, quatNormSq (quaternionOfComplexPair (Z i 0) (Z i 1))) = 1 ∧
      IsAtom (quaternionicDyadFromTwoColumns Z) ∧
      quaternionicDyadFromTwoColumns Z ∈ standardQuaternionicWindow.subalgebra.carrier ∧
      projectedMatrix standardComplexWindow (quaternionicDyadFromTwoColumns Z) = M := by
  obtain ⟨X, hX⟩ := exists_rectangularComplexGram M hM hr
  let Z : Matrix (Fin 3) (Fin 2) ℂ := Matrix.of fun i => ![X i 0, 0]
  have hz : Z * Zᴴ = M := by
    rw [← hX]
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [Z, Fin.sum_univ_two]
  have htrace : (Z * Zᴴ).trace = 1 := hz ▸ ht
  obtain ⟨hn, ha, hm⟩ := twoColumnDyad_lifts_traceOne Z htrace
  exact ⟨Z, fun _ => rfl, hz, hn, ha, hm, (projectedMatrix_quaternionicDyadFromTwoColumns Z).trans hz⟩

end AlbertSequential.WindowProbability
