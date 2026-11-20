/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RealPairJordanBlock
public import RealMatrixComplexification
public import ThreeAtomAndFourPoint

public section
noncomputable section

namespace AlbertSequential

open scoped Matrix ComplexOrder BigOperators

abbrev RealPairMatrix3 := Matrix (Fin 3) (Fin 3) ℝ

def realPairQutritMatrix (x : RealPairCoordinates) : RealPairMatrix3 :=
  !![x 0,x 3,0;x 3,x 1,0;0,0,x 2]

private theorem realPairQutritMatrix_transpose (x : RealPairCoordinates) :
    (realPairQutritMatrix x).transpose = realPairQutritMatrix x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def realPairHermitian (x : RealPairCoordinates) : Hermitian3 :=
  ⟨complexifyMatrix (realPairQutritMatrix x), by
    change (complexifyMatrix (realPairQutritMatrix x)).conjTranspose =
      complexifyMatrix (realPairQutritMatrix x)
    rw [← complexifyMatrix_transpose, realPairQutritMatrix_transpose]⟩

private theorem realPairHermitian_embedding (x : RealPairCoordinates) :
    standardComplexWindow.embedding (realPairHermitian x) = realPairBlockElement x := by
  change complexHermToAlbert (realPairHermitian x) = realPairBlockElement x
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private theorem complexDensity_realPart (σ : ComplexMatrix3) (hσ : IsComplexDensity3 σ) :
    (realPartMatrix σ).PosSemidef ∧ (realPartMatrix σ).trace = 1 := by
  have hs : σ.conjTranspose = σ := hσ.1.isHermitian.eq
  have he : complexifyMatrix (realPartMatrix σ) = (1 / 2 : ℝ) • (σ + σ.transpose) := by
    ext i j
    have hc : σ j i = star (σ i j) := by
      simpa only [Matrix.conjTranspose_apply] using (congrFun (congrFun hs j) i).symm
    simp only [complexifyMatrix, realPartMatrix, Matrix.map_apply, Complex.ofRealHom_eq_coe,
      Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, hc, Complex.real_smul]
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  refine ⟨(complexifyMatrix_posSemidef_iff _).mp ?_, ?_⟩
  · rw [he]
    exact (hσ.1.add hσ.1.transpose).smul (by norm_num : (0 : ℝ) ≤ 1/2)
  · simpa [realPartMatrix, Matrix.trace, Complex.re_sum] using congrArg Complex.re hσ.2

private theorem pairAmplitude_complexify (P : Fin 2 → RealPairMatrix3) (w : Word (Fin 2)) :
    wordAmplitude (fun i => complexifyMatrix (P i)) w =
      complexifyMatrix (wordAmplitude P w) := by
  induction w using List.reverseRecOn with
  | nil => simp [wordAmplitude, complexifyMatrix_one]
  | append_singleton w a ih =>
    simp only [wordAmplitude, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih, complexifyMatrix_mul]
    obtain ⟨i,b⟩ := a
    cases b <;> simp [algebraicOutcome, complexifyMatrix_one, complexifyMatrix_sub]

private theorem pairOperator_complexify (P : Fin 2 → RealPairMatrix3) (w : Word (Fin 2)) :
    wordOperator (fun i => complexifyMatrix (P i)) w = complexifyMatrix (wordOperator P w) := by
  unfold wordOperator
  rw [pairAmplitude_complexify, complexifyMatrix_mul]
  change (complexifyMatrix (wordAmplitude P w)).conjTranspose * _ =
    complexifyMatrix (wordAmplitude P w).transpose * _
  rw [complexifyMatrix_transpose]

private theorem realPart_trace_complex_mul (σ : ComplexMatrix3) (A : RealPairMatrix3) :
    (σ * complexifyMatrix A).trace.re = (realPartMatrix σ * A).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.re_sum, Complex.mul_re, complexifyMatrix, realPartMatrix]

private theorem pair_probability_covariant (g : NativeAlbertAutomorphism)
    (p : Fin 2 → Albert) (ρ : Albert) (w : Word (Fin 2)) :
    nativeWordProbability (fun i => g.linearEquiv (p i)) (g.linearEquiv ρ) w =
      nativeWordProbability p ρ w := by
  have hOutcome (a : Outcome (Fin 2)) :
      g.linearEquiv (nativeOutcome p a) = nativeOutcome (fun i => g.linearEquiv (p i)) a := by
    obtain ⟨i,b⟩ := a
    cases b <;> simp [nativeOutcome, map_sub, g.preserves_unit]
  have hEffect (u : Word (Fin 2)) : g.linearEquiv (nativeWordEffect p u) =
      nativeWordEffect (fun i => g.linearEquiv (p i)) u := by
    induction u with
    | nil => exact g.preserves_unit
    | cons a u ih => simp only [nativeWordEffect, g.map_quadraticMap, hOutcome, ih]
  rw [NativeAnalysis.nativeWordProbability_eq_pairing, NativeAnalysis.nativeWordProbability_eq_pairing,
    ← hEffect w, g.map_tracePairing]

private theorem realPairDyad_projection (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1) :
    let P := Matrix.vecMulVec v v
    P.transpose = P ∧ P * P = P ∧ P.rank = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]
  · rw [Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]
  · have hex : ∃ i, v i ≠ 0 := by
      by_contra! h
      simp [dotProduct, h] at hv
    obtain ⟨i, hi⟩ := hex
    let row : Fin 1 → Fin 3 := fun _ => i
    have hd : ((Matrix.vecMulVec v v).submatrix row row).det ≠ 0 := by
      rw [Matrix.det_unique]
      exact mul_ne_zero hi hi
    have hl := Matrix.rank_submatrix_le (Matrix.vecMulVec v v) row row
    rw [Matrix.rank_of_det_ne_zero hd] at hl
    exact le_antisymm (Matrix.rank_vecMulVec_le _ _) (by simpa using hl)

/-- Ordinary real qutrit projective reproduction for the two native atoms.
The two rank-one projections can be kept fixed while the density varies. -/
theorem realPair_qutrit_word_model (p q : Albert) (hp : IsAtom p) (hq : IsAtom q) :
    ∃ P : Fin 2 → RealPairMatrix3,
      (∀ i, (P i).transpose = P i ∧ P i * P i = P i ∧ (P i).rank = 1) ∧
      (P 0 * P 1).trace = tracePairing p q ∧
      ∀ ρ : Albert, IsDensity ρ → ∃ τ : RealPairMatrix3, τ.PosSemidef ∧ τ.trace = 1 ∧
        ∀ w : Word (Fin 2), (τ * wordOperator P w).trace = nativeWordProbability ![p,q] ρ w := by
  obtain ⟨g,a,b,c,ha,hb,hc,hab,habc,hp',hq'⟩ := realPair_normal_form p q hp hq
  let X : Fin 2 → RealPairCoordinates := ![![1,0,0,0], ![a,b,0,c]]
  let u : Fin 2 → Fin 3 → ℝ := ![![1,0,0], ![Real.sqrt a, Real.sqrt b,0]]
  let P : Fin 2 → RealPairMatrix3 := fun i => realPairQutritMatrix (X i)
  have hsqr : Real.sqrt a * Real.sqrt b = c := by
    apply (sq_eq_sq₀ (by positivity) hc).mp
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, habc]
  have hu (i : Fin 2) : u i ⬝ᵥ u i = 1 := by
    fin_cases i <;> simp [u, dotProduct, Fin.sum_univ_three]
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hP (i : Fin 2) : P i = Matrix.vecMulVec (u i) (u i) := by
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [P, X, u, realPairQutritMatrix, Matrix.vecMulVec_apply, ← sq, Real.sq_sqrt ha,
        Real.sq_sqrt hb, hsqr, mul_comm (Real.sqrt b) (Real.sqrt a)]
  have hoverlap : (P 0 * P 1).trace = tracePairing p q := by
    have h := g.map_tracePairing p q
    rw [hp', hq', tracePairing_diagAtom 0] at h
    change a = tracePairing p q at h
    rw [← h]
    simp [P, X, realPairQutritMatrix, Matrix.trace, Fin.sum_univ_three]
  refine ⟨P, fun i => (hP i).symm ▸ realPairDyad_projection (u i) (hu i), hoverlap, ?_⟩
  intro ρ hρ
  let p' : Fin 2 → Albert := fun i => g.linearEquiv ((![p,q] : Fin 2 → Albert) i)
  let Q : Fin 2 → Hermitian3 := fun i => realPairHermitian (X i)
  have hρ' : IsDensity (g.linearEquiv ρ) := g.map_isDensity hρ
  have hpa : ∀ i, IsAtom (p' i) := by
    intro i
    fin_cases i
    · exact g.map_isAtom hp
    · exact g.map_isAtom hq
  have hQ : ∀ i, standardComplexWindow.embedding (Q i) = p' i := by
    intro i
    change standardComplexWindow.embedding (realPairHermitian (X i)) = _
    rw [realPairHermitian_embedding]
    fin_cases i
    · change realPairBlockElement ![1,0,0,0] = g.linearEquiv p
      rw [hp']
      apply Prod.ext <;> funext j <;> fin_cases j <;> simp [diagAtom, realPairBlockElement, octonionScalar_zero]
    · exact hq'.symm
  obtain ⟨σ,hσ,_,hwords⟩ := complexRestrictionContract_holds.common_density_transport
    standardComplexWindow (g.linearEquiv ρ) hρ'
  obtain ⟨_,hwords'⟩ := hwords (Fin 2) p' Q hpa hQ
  obtain ⟨hposτ,htrτ⟩ := complexDensity_realPart σ hσ
  refine ⟨realPartMatrix σ, hposτ, htrτ, fun w => ?_⟩
  have h := hwords' w
  change (σ * wordOperator (fun i => complexifyMatrix (P i)) w).trace.re =
    nativeWordProbability p' (g.linearEquiv ρ) w at h
  rw [pairOperator_complexify, realPart_trace_complex_mul, pair_probability_covariant] at h
  exact h

end AlbertSequential
