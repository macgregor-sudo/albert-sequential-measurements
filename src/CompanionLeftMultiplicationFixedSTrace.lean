/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CompanionLeftMultiplicationFixedS
public import Mathlib.LinearAlgebra.Trace

/-! Normalized trace transport for the literal fixed-S complex representation. -/
@[expose] public section
noncomputable section
open scoped Matrix BigOperators
namespace AlbertSequential.NativeAnalysis
open MatchingModels

private theorem fixedSRealStackOf_add (x y : AlbertColumnCoordinate → ℝ) (j : Fin 3) :
    fixedSRealStackOf (x + y) j = fixedSRealStackOf x j + fixedSRealStackOf y j := by
  unfold fixedSRealStackOf
  rw [← map_add]
  rfl

private theorem fixedSRealStackOf_smul (r : ℝ) (x : AlbertColumnCoordinate → ℝ) (j : Fin 3) :
    fixedSRealStackOf (r • x) j = r • fixedSRealStackOf x j := by
  unfold fixedSRealStackOf
  rw [← map_smul]
  rfl

def fixedSComplexModelEquiv : (AlbertColumnCoordinate → ℝ) ≃ₗ[ℝ] (Fin 12 → ℂ) where
  toFun x := fixedSComplexStack (fixedSRealStackOf x)
  invFun z := fixedSRealStack (fun j =>
    fixedSComplexCoordinates.symm (fun k => z (fin3ProdFin4Equiv12 (j,k))))
  left_inv x := by
    have h : (fun j => fixedSComplexCoordinates.symm (fun k =>
        fixedSComplexStack (fixedSRealStackOf x) (fin3ProdFin4Equiv12 (j,k)))) = fixedSRealStackOf x := by
      funext j
      simp only [fixedSComplexStack, Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    change fixedSRealStack (fun j => fixedSComplexCoordinates.symm (fun k =>
      fixedSComplexStack (fixedSRealStackOf x) (fin3ProdFin4Equiv12 (j,k)))) = x
    rw [h, fixedSRealStack_of]
  right_inv z := by
    funext r
    obtain ⟨⟨j,k⟩,rfl⟩ := fin3ProdFin4Equiv12.surjective r
    simp only [fixedSRealStackOf_stack, fixedSComplexStack, Equiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  map_add' x y := by
    funext r
    let jk := fin3ProdFin4Equiv12.symm r
    change fixedSComplexCoordinates (fixedSRealStackOf (x+y) jk.1) jk.2 =
      fixedSComplexCoordinates (fixedSRealStackOf x jk.1) jk.2 +
      fixedSComplexCoordinates (fixedSRealStackOf y jk.1) jk.2
    rw [fixedSRealStackOf_add, map_add]
    rfl
  map_smul' r x := by
    funext j
    let jk := fin3ProdFin4Equiv12.symm j
    change fixedSComplexCoordinates (fixedSRealStackOf (r • x) jk.1) jk.2 =
      r • fixedSComplexCoordinates (fixedSRealStackOf x jk.1) jk.2
    rw [fixedSRealStackOf_smul, map_smul]
    rfl

private def complexCoordinates12 : (Fin 2 × Fin 12 → ℝ) ≃ₗ[ℝ] (Fin 12 → ℂ) where
  toFun x i := ⟨x (0,i), x (1,i)⟩
  invFun z i := if i.1 = 0 then (z i.2).re else (z i.2).im
  left_inv x := by
    funext i
    obtain ⟨t,j⟩ := i
    fin_cases t <;> rfl
  right_inv z := by funext i; apply Complex.ext <;> rfl
  map_add' x y := by funext i; apply Complex.ext <;> rfl
  map_smul' r x := by
    funext i
    apply Complex.ext <;> simp

private theorem complexCoordinates12_single (t : Fin 2) (i : Fin 12) :
    complexCoordinates12 (Pi.single (t,i) 1) = Pi.single i (if t = 0 then 1 else Complex.I) := by
  funext j
  by_cases hj : j = i
  · subst j
    fin_cases t <;> apply Complex.ext <;> simp [complexCoordinates12]
  · fin_cases t <;> apply Complex.ext <;> simp [complexCoordinates12, hj]

private theorem fixedSRealTrace_complexTrace (M : Matrix (Fin 12) (Fin 12) ℂ) :
    LinearMap.trace ℝ (Fin 12 → ℂ) ((Matrix.toLin' M).restrictScalars ℝ) = 2 * M.trace.re := by
  let A := (Matrix.toLin' M).restrictScalars ℝ
  let B := complexCoordinates12.symm.conj A
  have hd (t : Fin 2) (i : Fin 12) : LinearMap.toMatrix' B (t,i) (t,i) = (M i i).re := by
    rw [LinearMap.toMatrix'_apply]
    change complexCoordinates12.symm (M *ᵥ complexCoordinates12 (Pi.single (t,i) 1)) (t,i) = _
    rw [complexCoordinates12_single, Matrix.mulVec_single]
    fin_cases t <;>
      simp [complexCoordinates12, Complex.mul_im, Matrix.col_apply]
  calc
    LinearMap.trace ℝ (Fin 12 → ℂ) A = LinearMap.trace ℝ (Fin 2 × Fin 12 → ℝ) B :=
      (LinearMap.trace_conj' A complexCoordinates12.symm).symm
    _ = (LinearMap.toMatrix' B).trace :=
      LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ _) B
    _ = (2 : ℝ) * M.trace.re := by
      unfold Matrix.trace
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diag_apply, hd, Complex.re_sum, two_mul]

def fixedSLeftProjections (i : Fin 4) : Matrix AlbertColumnCoordinate AlbertColumnCoordinate ℝ :=
  octonionLeftProjection (fixedSLeftColumns i)

theorem fixedSLeftProjections_intertwine (i : Fin 4) (x : AlbertColumnCoordinate → ℝ) :
    fixedSComplexModelEquiv (fixedSLeftProjections i *ᵥ x) =
      dfailsProj i *ᵥ fixedSComplexModelEquiv x := by
  change fixedSComplexStack (fixedSRealStackOf (fixedSLeftProjections i *ᵥ x)) =
    dfailsProj i *ᵥ fixedSComplexStack (fixedSRealStackOf x)
  simpa only [fixedSRealStack_of, fixedSLeftProjections] using
    fixedSLeftProjection_complex i (fixedSRealStackOf x)

private theorem fixedSLeftWord_intertwine (w : Word (Fin 4)) (x : AlbertColumnCoordinate → ℝ) :
    fixedSComplexModelEquiv (wordOperator fixedSLeftProjections w *ᵥ x) =
      wordOperator dfailsProj w *ᵥ fixedSComplexModelEquiv x := by
  have hs i : star (fixedSLeftProjections i) = fixedSLeftProjections i := by
    change (fixedSLeftProjections i)ᴴ = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact octonionLeftProjection_transpose (fixedSLeftColumns i)
  have ht i : star (dfailsProj i) = dfailsProj i := (dfailsProj_hermitian i).eq
  have hr (u : Outcome (Fin 4)) (y : AlbertColumnCoordinate → ℝ) :
      fixedSComplexModelEquiv (algebraicOutcome fixedSLeftProjections u *ᵥ y) =
        algebraicOutcome dfailsProj u *ᵥ fixedSComplexModelEquiv y := by
    obtain ⟨i,b⟩ := u
    cases b
    · simp only [algebraicOutcome, Bool.false_eq_true, ↓reduceIte, Matrix.sub_mulVec,
        Matrix.one_mulVec, map_sub, fixedSLeftProjections_intertwine]
    · exact fixedSLeftProjections_intertwine i y
  induction w generalizing x with
  | nil => simp
  | cons u w ih =>
    rw [wordOperator_cons _ hs, wordOperator_cons _ ht, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hr, ih, hr, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem fixedSLeftProbability_eq_dfails (w : Word (Fin 4)) :
    (wordOperator fixedSLeftProjections w).trace / 24 = dfailsModel.probability w := by
  let A := Matrix.toLin' (wordOperator fixedSLeftProjections w)
  let B := (Matrix.toLin' (wordOperator dfailsProj w)).restrictScalars ℝ
  have hAB : fixedSComplexModelEquiv.conj A = B := by
    apply LinearMap.ext
    intro z
    change fixedSComplexModelEquiv
        (wordOperator fixedSLeftProjections w *ᵥ fixedSComplexModelEquiv.symm z) =
      wordOperator dfailsProj w *ᵥ z
    rw [fixedSLeftWord_intertwine, LinearEquiv.apply_symm_apply]
  have hTrace :
      (wordOperator fixedSLeftProjections w).trace = 2 * (wordOperator dfailsProj w).trace.re := by
    rw [← Matrix.trace_toLin'_eq, ← LinearMap.trace_conj' A fixedSComplexModelEquiv, hAB]
    exact fixedSRealTrace_complexTrace (wordOperator dfailsProj w)
  rw [hTrace, dfailsModel_probability]
  ring


theorem fixedSLeftDensityProbability_eq_dfails (VPlus VMinus : LeftModelSectorFrame)
    (hsplit : leftModelSectorProjection VPlus + leftModelSectorProjection VMinus = 1)
    (w : Word (Fin 4)) :
    (leftModelDensity 0 VPlus VMinus * wordOperator fixedSLeftProjections w).trace =
      dfailsModel.probability w := by
  rw [leftModelDensity_tracial VPlus VMinus hsplit, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul, ← fixedSLeftProbability_eq_dfails]
  ring

theorem fixedSLeftProbability_three_deviation :
    (wordOperator fixedSLeftProjections [(2,true),(3,true),(2,true)]).trace / 24 -
      nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit) [(2,true),(3,true),(2,true)] = 4 / 243 := by
  rw [fixedSLeftProbability_eq_dfails]
  simpa using dfails_length_three_exact 2 3 2 true true true

end AlbertSequential.NativeAnalysis
