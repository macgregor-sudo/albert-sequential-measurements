/- SPDX-License-Identifier: Apache-2.0 -/
module

public import NormalizedHolonomyDefects
public import CliffordDefectPairings
public import CliffordVolumeDefect
public import ScalarCliffordTelescope
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

noncomputable section

open scoped InnerProductSpace BigOperators
open ContinuousLinearMap

namespace AlbertSequential
namespace CornerHolonomy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem operator_mul_apply (T U : H →L[ℝ] H) (x : H) : (T * U) x = T (U x) :=
  rfl

def signedHolonomy (h : Fin 3 → H →L[ℝ] H) (a : Fin 3 × Bool) : H →L[ℝ] H :=
  if a.2 then h a.1 else star (h a.1)

/-- Degree at most d in the holonomies and their adjoints, evaluated at ξ. -/
def holonomyDegreeSpan (h : Fin 3 → H →L[ℝ] H) (ξ : H) (d : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ {v | ∃ w : List (Fin 3 × Bool), w.length ≤ d ∧
    w.foldr (fun a x => signedHolonomy h a x) ξ = v}

private theorem holonomyDegreeSpan_mono (h : Fin 3 → H →L[ℝ] H) (ξ : H)
    {d e : ℕ} (hde : d ≤ e) : holonomyDegreeSpan h ξ d ≤ holonomyDegreeSpan h ξ e :=
  Submodule.span_mono (fun _ ⟨w,hw,heq⟩ => ⟨w,hw.trans hde,heq⟩)

private theorem holonomyDegreeSpan_base (h : Fin 3 → H →L[ℝ] H) (ξ : H) (d : ℕ) :
    ξ ∈ holonomyDegreeSpan h ξ d :=
  Submodule.subset_span ⟨[],Nat.zero_le _,rfl⟩

private theorem signedHolonomy_mem_succ (h : Fin 3 → H →L[ℝ] H) (ξ : H)
    (a : Fin 3 × Bool) {d : ℕ} {v : H} (hv : v ∈ holonomyDegreeSpan h ξ d) :
    signedHolonomy h a v ∈ holonomyDegreeSpan h ξ (d+1) := by
  have hm : holonomyDegreeSpan h ξ d ≤
      (holonomyDegreeSpan h ξ (d+1)).comap (signedHolonomy h a).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    apply Submodule.subset_span
    exact ⟨a::w, Nat.succ_le_succ hw, rfl⟩
  exact hm hv

private theorem skewHolonomy_mem_succ (h : Fin 3 → H →L[ℝ] H) (ξ : H)
    (i : Fin 3) {d : ℕ} {v : H} (hv : v ∈ holonomyDegreeSpan h ξ d) :
    skewHermitianPart (h i) v ∈ holonomyDegreeSpan h ξ (d+1) := by
  change (1/2 : ℝ) • (h i v - (star (h i)) v) ∈ _
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact signedHolonomy_mem_succ h ξ (i,true) hv
  · exact signedHolonomy_mem_succ h ξ (i,false) hv

private theorem holonomyDegreeSpan_fixed (J : H →L[ℝ] H) (h : Fin 3 → H →L[ℝ] H) (ξ : H)
    (hJ : star J = J) (hsupport : ∀ i, CornerSupported J (h i)) (hξ : J ξ = ξ)
    {d : ℕ} {v : H} (hv : v ∈ holonomyDegreeSpan h ξ d) : J v = v := by
  have hm : holonomyDegreeSpan h ξ d ≤ (J.toLinearMap - (LinearMap.id : H →ₗ[ℝ] H)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,_,rfl⟩
    let x := w.foldr (fun a x => signedHolonomy h a x) ξ
    change J x - x = 0
    apply sub_eq_zero.mpr
    cases w with
    | nil => exact hξ
    | cons a w =>
      rcases a with ⟨i,b⟩
      have hleft : J * signedHolonomy h (i,b) = signedHolonomy h (i,b) := by
        cases b
        · exact (supported_star J (h i) hJ (hsupport i)).1
        · exact (hsupport i).1
      exact congrArg (fun T : H →L[ℝ] H => T (w.foldr (fun a x => signedHolonomy h a x) ξ)) hleft
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hm hv))

private def operatorVectorFunctional (Ω : H) : (H →L[ℝ] H) →ₗ[ℝ] ℝ where
  toFun T := ⟪Ω,T Ω⟫_ℝ
  map_add' T U := by simp [inner_add_right]
  map_smul' c T := by simp [real_inner_smul_right]

private theorem operatorVectorFunctional_star (Ω : H) (T : H →L[ℝ] H) :
    operatorVectorFunctional Ω (star T) = operatorVectorFunctional Ω T := by
  exact (T.adjoint_inner_right Ω Ω).trans (real_inner_comm _ _)

private theorem operatorVectorPairing (Ω : H) (T U : H →L[ℝ] H) :
    realStarPairing (operatorVectorFunctional Ω) T U = ⟪T Ω,U Ω⟫_ℝ :=
  T.adjoint_inner_right Ω (U Ω)

private theorem holonomy_dataError_zero (J : H →L[ℝ] H) (h : Fin 3 → H →L[ℝ] H)
    (hJJ : J * J = J) (hJ : star J = J) (hsupport : ∀ i, CornerSupported J (h i))
    (c : Fin 3 → ℝ) (K12 K13 K23 c4 : ℝ) (Ω : H)
    (hH : ∀ i η, η ∈ holonomyDegreeSpan h (J Ω) 2 → hermitianPart (h i) η = c i • η)
    (hC : hermitianPart (h 0 * h 1 * h 2) (J Ω) = c4 • J Ω)
    (hP : ∀ i j, i ≠ j →
      (cliffordPairDefect (fun i => skewHermitianPart (h i))
        (cornerCliffordParameters c K12 K13 K23 c4) i j J) Ω = 0) :
    (cliffordDataError (fun i => skewHermitianPart (h i))
      J (cornerCliffordParameters c K12 K13 K23 c4)) Ω = 0 := by
  let ξ := J Ω
  let K := holonomyDegreeSpan h ξ
  have hξ : J ξ = ξ := congrArg (fun T : H →L[ℝ] H => T Ω) hJJ
  have hd (i : Fin 3) (η : H) (hη : η ∈ K 2) : hermitianDefect J (h i) (c i) η = 0 := by
    change hermitianPart (h i) η - c i • J η = 0
    rw [hH i η hη, holonomyDegreeSpan_fixed J h ξ hJ hsupport hξ hη, sub_self]
  have hbase (d : ℕ) : ξ ∈ K d := holonomyDegreeSpan_base h ξ d
  have hact (i : Fin 3) (b : Bool) {d : ℕ} {η : H} (hη : η ∈ K d) :
      signedHolonomy h (i,b) η ∈ K (d+1) := signedHolonomy_mem_succ h ξ (i,b) hη
  have hF0 : h 2 ξ ∈ K 1 := hact 2 true (hbase 0)
  have hF1 : h 1 (h 2 ξ) ∈ K 2 := hact 1 true hF0
  have hB0 : (star (h 0)) ξ ∈ K 1 := hact 0 false (hbase 0)
  have hB1 : (star (h 1)) ((star (h 0)) ξ) ∈ K 2 := hact 1 false hB0
  have hT : hermitianProductTelescope J h c ξ = 0 := by
    simp only [hermitianProductTelescope, smul_apply, add_apply, operator_mul_apply, hd 0 _ hF1,
      hd 1 _ (holonomyDegreeSpan_mono h ξ (by decide : 1 ≤ 2) hF0), hd 2 _ (hbase 2),
      hd 2 _ hB1, hd 1 _ (holonomyDegreeSpan_mono h ξ (by decide : 1 ≤ 2) hB0),
      hd 0 _ (hbase 2), map_zero, add_zero, smul_zero]
  have hC0 : cornerCubicDefect J h c4 ξ = 0 := by
    change hermitianPart (h 0 * h 1 * h 2) (J Ω) - c4 • J ξ = 0
    rw [hC, hξ, sub_self]
  have he := congrArg (fun T : H →L[ℝ] H => T Ω)
    (cornerDataError_expansion J hJJ hJ h hsupport c K12 K13 K23 c4 J hJJ)
  simp only [sub_apply, operator_mul_apply, smul_apply, add_apply,
    hP 1 2 (by decide), hP 0 2 (by decide), hP 0 1 (by decide),
    smul_zero, add_zero, sub_zero] at he
  change _ = cornerCubicDefect J h c4 ξ - hermitianProductTelescope J h c ξ at he
  rw [hC0, hT, sub_self] at he
  exact he

/-- The normalized tetrahedron calculation with only the degree-two,
degree-one and base-vector relations. Corner support records the four
projection words' shared initial and final projection. -/
theorem finiteVectorTetrahedron_of_corner
    (J : H →L[ℝ] H) (h : Fin 3 → H →L[ℝ] H)
    (hJJ : J * J = J) (hJ : star J = J) (hsupport : ∀ i, CornerSupported J (h i))
    (c : Fin 3 → ℝ) (K12 K13 K23 c4 : ℝ) (Ω : H)
    (hH : ∀ i η, η ∈ holonomyDegreeSpan h (J Ω) 2 → hermitianPart (h i) η = c i • η)
    (hU : ∀ i η, η ∈ holonomyDegreeSpan h (J Ω) 2 →
      (star (h i) * h i) η = η ∧ (h i * star (h i)) η = η)
    (hP : ∀ i j, i ≠ j → ∀ η, η ∈ holonomyDegreeSpan h (J Ω) 1 →
      let N := fun i => skewHermitianPart (h i)
      let s := cornerCliffordParameters c K12 K13 K23 c4
      (N i * N j + N j * N i) η = (-2 * s.gramMatrix i j) • η)
    (hC : hermitianPart (h 0 * h 1 * h 2) (J Ω) = c4 • J Ω) :
    let ξ := J Ω
    let N := fun i => skewHermitianPart (h i)
    let s := cornerCliffordParameters c K12 K13 K23 c4
    let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of s.gramMatrix
    cliffordVolume N ξ = s.d0 • ξ ∧
      ‖cliffordVolume N ξ‖^2 = M.det * ‖ξ‖^2 ∧
      (M.det - s.d0^2) * ‖ξ‖^2 = 0 := by
  let ξ := J Ω
  let K := holonomyDegreeSpan h ξ
  let N := fun i => skewHermitianPart (h i)
  let s := cornerCliffordParameters c K12 K13 K23 c4
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of s.gramMatrix
  let φ := operatorVectorFunctional Ω
  have hφ := operatorVectorFunctional_star Ω
  have hN (i : Fin 3) : star (N i) = -N i := skewHermitianPart_skew (h i)
  have hbase (d : ℕ) : ξ ∈ K d := holonomyDegreeSpan_base h ξ d
  have hξ : J ξ = ξ := congrArg (fun T : H →L[ℝ] H => T Ω) hJJ
  have hfix {d : ℕ} {η : H} (hη : η ∈ K d) : J η = η :=
    holonomyDegreeSpan_fixed J h ξ hJ hsupport hξ hη
  have hNs (i : Fin 3) {d : ℕ} {η : H} (hη : η ∈ K d) : N i η ∈ K (d+1) :=
    skewHolonomy_mem_succ h ξ i hη
  have hsquare (i : Fin 3) (T : H →L[ℝ] H) (hT : T Ω ∈ K 2) :
      (cliffordSquareDefect N s i T) Ω = 0 := by
    let η := T Ω
    have hd : hermitianDefect J (h i) (c i) η = 0 := by
      change hermitianPart (h i) η - c i • J η = 0
      rw [hH i η hT, hfix hT, sub_self]
    have hun := hU i η hT
    have he := congrArg (fun F : H →L[ℝ] H => F η)
      (squareDefect_reduction J (h i) hJJ hJ (hsupport i) (c i))
    have hdia : s.diagonal i = 1 - c i ^ 2 := by fin_cases i <;> rfl
    simpa only [squareCliffordDefect, cliffordSquareDefect, leftUnitarityDefect,
      rightUnitarityDefect, hdia, add_apply, sub_apply, operator_mul_apply, smul_apply, N, η,
      hfix hT, hd, hun.1, hun.2, sub_self, map_zero, add_zero, smul_zero, sub_zero] using he
  have hpair (i j : Fin 3) (hij : i ≠ j) (T : H →L[ℝ] H) (hT : T Ω ∈ K 1) :
      (cliffordPairDefect N s i j T) Ω = 0 := by
    have he : (N i * N j + N j * N i) (T Ω) = (-2 * s.gramMatrix i j) • T Ω := hP i j hij _ hT
    simp only [operator_mul_apply, add_apply] at he
    simp only [cliffordPairDefect, add_apply, operator_mul_apply, smul_apply, he, neg_mul, neg_smul,
      neg_add_cancel]
  have hVolError : cliffordVolumeError N J s Ω = 0 := by
    rw [cliffordVolumeError_expansion]
    simp only [smul_apply, sub_apply, add_apply, operator_mul_apply, hpair 1 2 (by decide) (N 0 * J) (hNs 0 (hbase 0)),
      hpair 0 2 (by decide) J (hbase 1), hpair 0 1 (by decide) (N 2 * J) (hNs 2 (hbase 0)), map_zero,
      smul_zero, zero_add, sub_self]
  have hVolAction : (cliffordVolume N * J) Ω = cliffordGramVector N J s Ω :=
    sub_eq_zero.mp hVolError
  have hG (i j : Fin 3) : cliffordGramDefect φ N J s i j = 0 := by
    by_cases hij : i = j
    · subst j
      rw [cliffordGramDefect_diagonal φ N hN, operatorVectorPairing, hsquare i J (hbase 2),
        inner_zero_right, neg_zero]
    · rw [cliffordGramDefect_pair φ hφ N hN, operatorVectorPairing, hpair i j hij J (hbase 1),
        inner_zero_right, mul_zero]
  have hCross (i : Fin 3) : cliffordCrossDefect φ N J s i = 0 := by
    fin_cases i
    · change cliffordCrossDefect φ N J s 0 = 0
      rw [cliffordCrossDefect_first φ hφ N hN]
      simp only [hG, mul_zero, φ, operatorVectorPairing, hsquare 0 J (hbase 2), inner_zero_right, sub_zero]
    · change cliffordCrossDefect φ N J s 1 = 0
      rw [cliffordCrossDefect_second φ hφ N hN]
      simp only [hG, mul_zero, φ, operatorVectorPairing, hsquare 1 (N 0 * J) (hNs 0 (hbase 1)),
        hpair 0 1 (by decide) J (hbase 1), inner_zero_right, sub_zero]
    · change cliffordCrossDefect φ N J s 2 = 0
      rw [cliffordCrossDefect_third φ hφ N hN]
      simp only [hG, mul_zero, φ, operatorVectorPairing, hsquare 2 J (hbase 2),
        hpair 1 2 (by decide) J (hbase 1), hpair 0 2 (by decide) (N 1 * J) (hNs 1 (hbase 0)),
        inner_zero_right, operator_mul_apply, sub_apply, map_zero, sub_self, inner_zero_left, add_zero]
  have hNorm : cliffordNormDefect φ N J s = 0 := by
    rw [cliffordNormDefect_reduction φ N hN]
    simp only [φ, operatorVectorPairing, hsquare 0 (N 1 * N 2 * J) (hNs 1 (hNs 2 (hbase 0))),
      hsquare 1 (N 2 * J) (hNs 2 (hbase 1)), hsquare 2 J (hbase 2), inner_zero_right, neg_zero,
      mul_zero, sub_self]
  have hGval (i j : Fin 3) := sub_eq_zero.mp (hG i j)
  have hCval (i : Fin 3) := sub_eq_zero.mp (hCross i)
  have hNval := sub_eq_zero.mp hNorm
  have hVolumeNorm : realStarPairing φ (cliffordGramVector N J s) (cliffordGramVector N J s) =
      M.det * realStarPairing φ J J := by
    rw [cliffordGramVector_square φ hφ, hNval]
    simp_rw [hGval, hCval]
    simp only [M, Matrix.det_fin_three, Matrix.of_apply, Fin.sum_univ_three, CliffordScalarParameters.q,
      CliffordScalarParameters.gramMatrix, CliffordScalarParameters.expectedCross,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hL : ‖cliffordVolume N ξ‖^2 = M.det * ‖ξ‖^2 := by
    simpa only [φ, operatorVectorPairing, real_inner_self_eq_norm_sq, ← hVolAction, operator_mul_apply, ξ]
      using hVolumeNorm
  have hD : cliffordVolume N ξ = s.d0 • ξ :=
    sub_eq_zero.mp (holonomy_dataError_zero J h hJJ hJ hsupport c K12 K13 K23 c4 Ω hH hC
      (fun i j hij => hpair i j hij J (hbase 1)))
  have hDnorm : ‖cliffordVolume N ξ‖^2 = s.d0^2 * ‖ξ‖^2 := by
    rw [hD, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  change cliffordVolume N ξ = s.d0 • ξ ∧ ‖cliffordVolume N ξ‖^2 = M.det * ‖ξ‖^2 ∧ _
  exact ⟨hD, hL, by rw [sub_mul, ← hL, ← hDnorm, sub_self]⟩

end CornerHolonomy
end AlbertSequential
