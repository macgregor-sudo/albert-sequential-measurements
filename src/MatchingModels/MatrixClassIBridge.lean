/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HilbertProjectiveData
public import HilbertClassIConstructor
public import BoundedWordEffects
public import ComplexStateCompression
public import QuaternionicProjectiveExtension
public import RightQuaternionicHilbert
public import CyclicHilbertModel
public import SubalgebraCoordsAndLine
public import SuppliedEmbeddingStateTransport
public import NativeReachableDensity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Matrix-to-Class-I Bridge and Explicit C^12 / Quaternionic-Window Models

Provides:
1. `matToCLM`: embeds `Matrix (Fin d) (Fin d) ℂ` into bounded operators on
   `EuclideanSpace ℂ (Fin d)` as a `*`-homomorphism taking Hermitian projections to
   `IsStarProjection` and `wordOperator` to `boundedWordEffect`, together with
   diagonal matrix-element / trace formulas.
2. `matrixWeightedModel` and `matrixTraceModel` / `c12TraceModel`:
   constructs `HilbertProjectiveData` from Hermitian projection matrices and
   finite vector mixtures or normalized matrix trace states.
3. `blockMat12`, `c12BlockMixtureModel`, and `c12Proj0MixtureModel`:
   block-diagonal `ℂ^12 = ℂ^6 ⊕ ℂ^6` projective mixtures matching convex
   combinations of trace-word probabilities from `e/3` or `P_i0`.
4. `quatProj6`: maps `QuaternionicWindow` atoms into rank-2 projections in `M_6(ℂ)`
   via `symplecticQuatEmbed` and equates their trace-word probabilities with
   `nativeWordProbability` from `e/3` and from an atom `q i0`.
5. `hilbertComplexToReal` and `hilbertComplexToQuaternionic`:
   transports any complex `HilbertProjectiveData` model to real Hilbert and
   quaternionic projective models preserving all word probabilities.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace AlbertSequential.MatchingModels

open scoped ComplexOrder InnerProductSpace Matrix

/-! ## Section 1: `matToCLM` on `EuclideanSpace ℂ (Fin d)` -/

section MatToCLM

def matToCLM {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

theorem matToCLM_apply_vec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    matToCLM A x i = ∑ j : Fin d, A i j * x j := by
  change (A *ᵥ x.ofLp) i = _
  simp [Matrix.mulVec, dotProduct]

theorem matToCLM_zero {d : ℕ} :
    matToCLM (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp [matToCLM_apply_vec]

theorem matToCLM_one {d : ℕ} :
    matToCLM (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp [matToCLM_apply_vec, Matrix.one_apply]

theorem matToCLM_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matToCLM (A + B) = matToCLM A + matToCLM B := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp only [matToCLM_apply_vec, FunLike.coe_add, Pi.add_apply,
    PiLp.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem matToCLM_sub {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matToCLM (A - B) = matToCLM A - matToCLM B := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp only [matToCLM_apply_vec, FunLike.coe_sub, Pi.sub_apply,
    PiLp.sub_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem matToCLM_smul {d : ℕ} (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    matToCLM (c • A) = c • matToCLM A := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp only [matToCLM_apply_vec, FunLike.coe_smul, Pi.smul_apply,
    PiLp.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem matToCLM_real_smul {d : ℕ} (r : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    matToCLM (r • A) = (r : ℂ) • matToCLM A := by
  rw [← Complex.coe_smul, matToCLM_smul]

theorem matToCLM_mul {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matToCLM (A * B) = (matToCLM A).comp (matToCLM B) := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp only [matToCLM_apply_vec, ContinuousLinearMap.comp_apply, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem matToCLM_adjoint {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ContinuousLinearMap.adjoint (matToCLM A) = matToCLM A.conjTranspose := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, matToCLM_apply_vec,
    Matrix.conjTranspose_apply, map_sum, map_mul, Complex.star_def, Complex.conj_conj,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem matToCLM_star {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    star (matToCLM A) = matToCLM A.conjTranspose :=
  matToCLM_adjoint A

theorem matToCLM_isSelfAdjoint {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) : IsSelfAdjoint (matToCLM A) := by
  change star (matToCLM A) = matToCLM A
  rw [matToCLM_star, hA.eq]

theorem matToCLM_isStarProjection {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P) :
    IsStarProjection (matToCLM P) := by
  constructor
  · change (matToCLM P) * (matToCLM P) = matToCLM P
    change (matToCLM P).comp (matToCLM P) = matToCLM P
    rw [← matToCLM_mul, hP_idem]
  · exact matToCLM_isSelfAdjoint hP_herm

theorem matToCLM_boundedOutcome {ι : Type*} {d : ℕ}
    (P : ι → Matrix (Fin d) (Fin d) ℂ) (a : Outcome ι) :
    boundedOutcome (fun i => matToCLM (P i)) a =
      matToCLM (algebraicOutcome P a) := by
  rcases a with ⟨i, b⟩
  cases b
  · simp [boundedOutcome, algebraicOutcome, matToCLM_one, matToCLM_sub]
    rfl
  · simp [boundedOutcome, algebraicOutcome]

theorem matToCLM_boundedWordAmplitude {ι : Type*} {d : ℕ}
    (P : ι → Matrix (Fin d) (Fin d) ℂ) (w : Word ι) :
    boundedWordAmplitude (fun i => matToCLM (P i)) w =
      matToCLM (wordAmplitude P w) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp only [boundedWordAmplitude, wordAmplitude, List.foldl_nil, matToCLM_one]
    rfl
  | append_singleton w a ih =>
    rw [boundedWordAmplitude_append, wordAmplitude_append,
      matToCLM_mul, ih]
    simp only [boundedWordAmplitude, wordAmplitude, List.foldl_cons, List.foldl_nil,
      ContinuousLinearMap.comp_id, mul_one, matToCLM_boundedOutcome]

theorem matToCLM_boundedWordEffect {ι : Type*} {d : ℕ}
    (P : ι → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, (P i).IsHermitian) (w : Word ι) :
    boundedWordEffect (fun i => matToCLM (P i)) w =
      matToCLM (wordOperator P w) := by
  rw [boundedWordEffect_eq_star_mul _ (fun i => matToCLM_isSelfAdjoint (hP i)),
    matToCLM_boundedWordAmplitude, matToCLM_adjoint]
  change (matToCLM (wordAmplitude P w).conjTranspose).comp (matToCLM (wordAmplitude P w)) = _
  rw [← matToCLM_mul]
  rfl

def basisVec {d : ℕ} (j : Fin d) : EuclideanSpace ℂ (Fin d) :=
  EuclideanSpace.single j (1 : ℂ)

theorem basisVec_apply {d : ℕ} (j i : Fin d) :
    basisVec j i = if i = j then 1 else 0 := by
  simp [basisVec, PiLp.single_apply]

theorem matToCLM_basisVec_apply {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j i : Fin d) :
    matToCLM A (basisVec j) i = A i j := by
  rw [matToCLM_apply_vec]
  simp [basisVec_apply]

theorem inner_basisVec_matToCLM {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    inner ℂ (basisVec j) (matToCLM A (basisVec j)) = A j j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, basisVec_apply, matToCLM_basisVec_apply]

theorem inner_matToCLM_basisVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    inner ℂ (matToCLM A (basisVec j)) (basisVec j) = star (A j j) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, basisVec_apply, matToCLM_basisVec_apply]

theorem inner_matToCLM_basisVec_hermitian {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (j : Fin d) :
    inner ℂ (matToCLM A (basisVec j)) (basisVec j) = A j j := by
  rw [inner_matToCLM_basisVec]
  exact congrFun (congrFun hA.eq j) j

theorem inner_matToCLM_basisVec_re {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    (inner ℂ (matToCLM A (basisVec j)) (basisVec j)).re = (A j j).re := by
  rw [inner_matToCLM_basisVec]
  simp

theorem sum_inner_basisVec_matToCLM {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j : Fin d, inner ℂ (basisVec j) (matToCLM A (basisVec j)) = Matrix.trace A := by
  simp [inner_basisVec_matToCLM, Matrix.trace]

theorem sum_inner_matToCLM_basisVec_re {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ∑ j : Fin d, (inner ℂ (matToCLM A (basisVec j)) (basisVec j)).re = (Matrix.trace A).re := by
  simp [inner_matToCLM_basisVec_re, Matrix.trace, Complex.re_sum]

theorem inner_matToCLM_proj_basisVec_re {d : ℕ} (Q A : Matrix (Fin d) (Fin d) ℂ)
    (hQ : Q.IsHermitian) (j : Fin d) :
    (inner ℂ (matToCLM A (matToCLM Q (basisVec j))) (matToCLM Q (basisVec j))).re =
      (inner ℂ (matToCLM (Q * A * Q) (basisVec j)) (basisVec j)).re := by
  have hadj : ContinuousLinearMap.adjoint (matToCLM Q) = matToCLM Q := by
    rw [matToCLM_adjoint, hQ.eq]
  rw [← ContinuousLinearMap.adjoint_inner_left (matToCLM Q), hadj]
  change (inner ℂ (((matToCLM Q).comp (matToCLM A)).comp (matToCLM Q) (basisVec j))
      (basisVec j)).re = _
  rw [← matToCLM_mul, ← matToCLM_mul]

end MatToCLM

/-! ## Section 2: Weighted Vector State & Trace State Models -/

section WeightedModel

def weightedVectorState {d m : ℕ} (μ : Fin m → ℝ)
    (v : Fin m → EuclideanSpace ℂ (Fin d)) :
    selfAdjoint (HilbertOperatorAlgebra ℂ (EuclideanSpace ℂ (Fin d))) →ₗ[ℝ] ℝ where
  toFun T := ∑ k : Fin m, μ k * (inner ℂ ((operatorValue ℂ _ T.val) (v k)) (v k)).re
  map_add' T S := by
    have hadd : operatorValue ℂ (EuclideanSpace ℂ (Fin d)) (T + S).val =
        operatorValue ℂ (EuclideanSpace ℂ (Fin d)) T.val +
          operatorValue ℂ (EuclideanSpace ℂ (Fin d)) S.val := by
      change operatorValue ℂ _ (T.val + S.val) = _
      exact map_add _ T.val S.val
    rw [hadd]
    simp only [FunLike.coe_add, Pi.add_apply, inner_add_left, Complex.add_re,
      mul_add, Finset.sum_add_distrib]
  map_smul' r T := by
    have hsmul : operatorValue ℂ (EuclideanSpace ℂ (Fin d)) (r • T).val =
        (r : ℂ) • operatorValue ℂ (EuclideanSpace ℂ (Fin d)) T.val := by
      change operatorValue ℂ _ (r • T.val) = _
      exact operatorValue_real_smul ℂ (EuclideanSpace ℂ (Fin d)) r T.val
    rw [hsmul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change μ k * (inner ℂ ((r : ℂ) • operatorValue ℂ _ T.val (v k)) (v k)).re =
      r * (μ k * (inner ℂ (operatorValue ℂ _ T.val (v k)) (v k)).re)
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring

private theorem re_inner_self_eq_norm_sq {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) :
    (inner ℂ x x).re = ‖x‖ ^ 2 := by
  change RCLike.re (inner ℂ x x) = ‖x‖ ^ 2
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm

theorem weightedVectorState_normalized {d m : ℕ} (μ : Fin m → ℝ)
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∑ k : Fin m, μ k * ‖v k‖ ^ 2 = 1) :
    weightedVectorState μ v 1 = 1 := by
  change ∑ k : Fin m, μ k * (inner ℂ (v k) (v k)).re = 1
  simp only [re_inner_self_eq_norm_sq]
  exact hnorm

theorem weightedVectorState_positive {d m : ℕ} (μ : Fin m → ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (v : Fin m → EuclideanSpace ℂ (Fin d))
    (T : selfAdjoint (HilbertOperatorAlgebra ℂ (EuclideanSpace ℂ (Fin d))))
    (hT : (operatorValue ℂ _ T.val).IsPositive) :
    0 ≤ weightedVectorState μ v T := by
  change 0 ≤ ∑ k : Fin m, μ k * (inner ℂ ((operatorValue ℂ _ T.val) (v k)) (v k)).re
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hμ k) (hT.re_inner_nonneg_left (v k))

def matrixWeightedModel {ι : Type*} {d m : ℕ}
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hP_herm : ∀ i, (P i).IsHermitian) (hP_idem : ∀ i, P i * P i = P i)
    (μ : Fin m → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∑ k : Fin m, μ k * ‖v k‖ ^ 2 = 1) :
    HilbertProjectiveData ι ℂ (EuclideanSpace ℂ (Fin d)) :=
  HilbertProjectiveData.ofBoundedProjections
    (fun i => matToCLM (P i))
    (fun i => matToCLM_isStarProjection (hP_herm i) (hP_idem i))
    (weightedVectorState μ v)
    (weightedVectorState_normalized μ v hnorm)
    (weightedVectorState_positive μ hμ v)

theorem matrixWeightedModel_operatorProjection {ι : Type*} {d m : ℕ}
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hP_herm : ∀ i, (P i).IsHermitian) (hP_idem : ∀ i, P i * P i = P i)
    (μ : Fin m → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∑ k : Fin m, μ k * ‖v k‖ ^ 2 = 1) (i : ι) :
    (matrixWeightedModel P hP_herm hP_idem μ hμ v hnorm).operatorProjection i =
      matToCLM (P i) :=
  HilbertProjectiveData.ofBoundedProjections_operatorProjection _ _ _ _ _ i

theorem matrixWeightedModel_probability {ι : Type*} {d m : ℕ}
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hP_herm : ∀ i, (P i).IsHermitian) (hP_idem : ∀ i, P i * P i = P i)
    (μ : Fin m → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (v : Fin m → EuclideanSpace ℂ (Fin d))
    (hnorm : ∑ k : Fin m, μ k * ‖v k‖ ^ 2 = 1) (w : Word ι) :
    (matrixWeightedModel P hP_herm hP_idem μ hμ v hnorm).probability w =
      ∑ k : Fin m, μ k * (inner ℂ (matToCLM (wordOperator P w) (v k)) (v k)).re := by
  rw [← HilbertProjectiveData.toAlgebraic_probability, matrixWeightedModel,
    HilbertProjectiveData.ofBoundedProjections_probability]
  change ∑ k : Fin m, μ k * (inner ℂ (operatorValue ℂ _
      ((operatorValue ℂ _).symm (boundedWordEffect (fun i => matToCLM (P i)) w)) (v k)) (v k)).re = _
  have hop : operatorValue ℂ (EuclideanSpace ℂ (Fin d))
      ((operatorValue ℂ (EuclideanSpace ℂ (Fin d))).symm (boundedWordEffect (fun i => matToCLM (P i)) w)) =
      matToCLM (wordOperator P w) := by
    rw [RingEquiv.apply_symm_apply, matToCLM_boundedWordEffect P hP_herm w]
  rw [hop]

def matrixTraceModel {ι : Type*} {d : ℕ} (hd : 0 < d)
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hP_herm : ∀ i, (P i).IsHermitian) (hP_idem : ∀ i, P i * P i = P i) :
    HilbertProjectiveData ι ℂ (EuclideanSpace ℂ (Fin d)) :=
  matrixWeightedModel P hP_herm hP_idem
    (fun _ => (1 / (d : ℝ)))
    (fun _ => by positivity)
    basisVec
    (by
      have hnorm_bv : ∀ k : Fin d, ‖basisVec k‖ ^ 2 = 1 := fun k => by
        simp [basisVec, PiLp.norm_single]
      simp only [hnorm_bv, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, one_div]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'))

theorem matrixTraceModel_probability {ι : Type*} {d : ℕ} (hd : 0 < d)
    (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hP_herm : ∀ i, (P i).IsHermitian) (hP_idem : ∀ i, P i * P i = P i) (w : Word ι) :
    (matrixTraceModel hd P hP_herm hP_idem).probability w =
      (1 / (d : ℝ)) * (Matrix.trace (wordOperator P w)).re := by
  unfold matrixTraceModel
  rw [matrixWeightedModel_probability, ← Finset.mul_sum, sum_inner_matToCLM_basisVec_re]

def c12TraceModel {ι : Type*}
    (P : ι → Matrix (Fin 12) (Fin 12) ℂ)
    (hP_herm : ∀ i, (P i).IsHermitian) (hP_idem : ∀ i, P i * P i = P i) :
    HilbertProjectiveData ι ℂ (EuclideanSpace ℂ (Fin 12)) :=
  matrixTraceModel (by decide : 0 < 12) P hP_herm hP_idem

theorem c12TraceModel_probability {ι : Type*}
    (P : ι → Matrix (Fin 12) (Fin 12) ℂ)
    (hP_herm : ∀ i, (P i).IsHermitian) (hP_idem : ∀ i, P i * P i = P i) (w : Word ι) :
    (c12TraceModel P hP_herm hP_idem).probability w =
      (1 / 12 : ℝ) * (Matrix.trace (wordOperator P w)).re := by
  unfold c12TraceModel
  simpa using matrixTraceModel_probability (by decide : 0 < 12) P hP_herm hP_idem w

end WeightedModel

/-! ## Section 3: `ℂ^12 = ℂ^6 ⊕ ℂ^6` Block-Diagonal Models -/

section C12Models

abbrev equiv6Sum6 : Fin 6 ⊕ Fin 6 ≃ Fin 12 := finSumFinEquiv (m := 6) (n := 6)

def blockMat12 (A B : Matrix (Fin 6) (Fin 6) ℂ) : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.reindex equiv6Sum6 equiv6Sum6 (Matrix.fromBlocks A 0 0 B)

theorem blockMat12_one :
    blockMat12 (1 : Matrix (Fin 6) (Fin 6) ℂ) (1 : Matrix (Fin 6) (Fin 6) ℂ) = 1 := by
  unfold blockMat12
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem blockMat12_add (A₁ A₂ B₁ B₂ : Matrix (Fin 6) (Fin 6) ℂ) :
    blockMat12 (A₁ + A₂) (B₁ + B₂) = blockMat12 A₁ B₁ + blockMat12 A₂ B₂ := by
  ext i j
  simp only [blockMat12, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
  cases equiv6Sum6.symm i <;> cases equiv6Sum6.symm j <;> simp

theorem blockMat12_sub (A₁ A₂ B₁ B₂ : Matrix (Fin 6) (Fin 6) ℂ) :
    blockMat12 (A₁ - A₂) (B₁ - B₂) = blockMat12 A₁ B₁ - blockMat12 A₂ B₂ := by
  ext i j
  simp only [blockMat12, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]
  cases equiv6Sum6.symm i <;> cases equiv6Sum6.symm j <;> simp

theorem blockMat12_smul (c : ℂ) (A B : Matrix (Fin 6) (Fin 6) ℂ) :
    blockMat12 (c • A) (c • B) = c • blockMat12 A B := by
  ext i j
  simp only [blockMat12, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    smul_eq_mul]
  cases equiv6Sum6.symm i <;> cases equiv6Sum6.symm j <;> simp

theorem blockMat12_mul (A₁ A₂ B₁ B₂ : Matrix (Fin 6) (Fin 6) ℂ) :
    blockMat12 (A₁ * A₂) (B₁ * B₂) = blockMat12 A₁ B₁ * blockMat12 A₂ B₂ := by
  unfold blockMat12
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem blockMat12_conjTranspose (A B : Matrix (Fin 6) (Fin 6) ℂ) :
    (blockMat12 A B).conjTranspose = blockMat12 A.conjTranspose B.conjTranspose := by
  unfold blockMat12
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  simp

theorem blockMat12_isHermitian {A B : Matrix (Fin 6) (Fin 6) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (blockMat12 A B).IsHermitian := by
  rw [Matrix.IsHermitian, blockMat12_conjTranspose, hA.eq, hB.eq]

theorem blockMat12_idempotent {A B : Matrix (Fin 6) (Fin 6) ℂ}
    (hA : A * A = A) (hB : B * B = B) :
    blockMat12 A B * blockMat12 A B = blockMat12 A B := by
  rw [← blockMat12_mul, hA, hB]

theorem blockMat12_diag_inl (A B : Matrix (Fin 6) (Fin 6) ℂ) (j : Fin 6) :
    blockMat12 A B (equiv6Sum6 (Sum.inl j)) (equiv6Sum6 (Sum.inl j)) = A j j := by
  simp [blockMat12, Matrix.reindex_apply]

theorem blockMat12_diag_inr (A B : Matrix (Fin 6) (Fin 6) ℂ) (j : Fin 6) :
    blockMat12 A B (equiv6Sum6 (Sum.inr j)) (equiv6Sum6 (Sum.inr j)) = B j j := by
  simp [blockMat12, Matrix.reindex_apply]

theorem blockMat12_trace (A B : Matrix (Fin 6) (Fin 6) ℂ) :
    Matrix.trace (blockMat12 A B) = Matrix.trace A + Matrix.trace B := by
  change ∑ k : Fin 12, blockMat12 A B k k = Matrix.trace A + Matrix.trace B
  rw [← Equiv.sum_comp equiv6Sum6, Fintype.sum_sum_type]
  simp [blockMat12_diag_inl, blockMat12_diag_inr, Matrix.trace]

theorem blockMat12_algebraicOutcome {ι : Type*}
    (Pplus Pminus : ι → Matrix (Fin 6) (Fin 6) ℂ) (a : Outcome ι) :
    algebraicOutcome (fun i => blockMat12 (Pplus i) (Pminus i)) a =
      blockMat12 (algebraicOutcome Pplus a) (algebraicOutcome Pminus a) := by
  rcases a with ⟨i, b⟩
  cases b
  · simp [algebraicOutcome, blockMat12_one, blockMat12_sub]
  · simp [algebraicOutcome]

theorem blockMat12_wordAmplitude {ι : Type*}
    (Pplus Pminus : ι → Matrix (Fin 6) (Fin 6) ℂ) (w : Word ι) :
    wordAmplitude (fun i => blockMat12 (Pplus i) (Pminus i)) w =
      blockMat12 (wordAmplitude Pplus w) (wordAmplitude Pminus w) := by
  induction w using List.reverseRecOn with
  | nil => simp [wordAmplitude, blockMat12_one]
  | append_singleton w a ih =>
    rw [wordAmplitude_append, wordAmplitude_append, wordAmplitude_append,
      ih, wordAmplitude_singleton, wordAmplitude_singleton, wordAmplitude_singleton,
      blockMat12_algebraicOutcome, blockMat12_mul]

theorem blockMat12_wordOperator {ι : Type*}
    (Pplus Pminus : ι → Matrix (Fin 6) (Fin 6) ℂ) (w : Word ι) :
    wordOperator (fun i => blockMat12 (Pplus i) (Pminus i)) w =
      blockMat12 (wordOperator Pplus w) (wordOperator Pminus w) := by
  unfold wordOperator
  rw [blockMat12_wordAmplitude, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, blockMat12_conjTranspose, blockMat12_mul]

def blockMixWeight (lam : ℝ) (k : Fin 12) : ℝ :=
  match equiv6Sum6.symm k with
  | Sum.inl _ => lam / 6
  | Sum.inr _ => (1 - lam) / 6

theorem blockMixWeight_nonneg {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (k : Fin 12) : 0 ≤ blockMixWeight lam k := by
  unfold blockMixWeight
  cases equiv6Sum6.symm k with
  | inl _ => linarith [hlam.1]
  | inr _ => linarith [hlam.2]

theorem blockMixWeight_norm (lam : ℝ) :
    ∑ k : Fin 12, blockMixWeight lam k * ‖basisVec k‖ ^ 2 = 1 := by
  have hnorm_bv : ∀ k : Fin 12, ‖basisVec k‖ ^ 2 = 1 := fun k => by
    simp [basisVec, PiLp.norm_single]
  simp only [hnorm_bv, mul_one]
  change ∑ k : Fin 12, blockMixWeight lam k = 1
  rw [← Equiv.sum_comp equiv6Sum6, Fintype.sum_sum_type]
  simp [blockMixWeight]
  ring

def c12BlockMixtureModel {ι : Type*}
    (Pplus Pminus : ι → Matrix (Fin 6) (Fin 6) ℂ)
    (hplus_herm : ∀ i, (Pplus i).IsHermitian) (hplus_idem : ∀ i, Pplus i * Pplus i = Pplus i)
    (hminus_herm : ∀ i, (Pminus i).IsHermitian) (hminus_idem : ∀ i, Pminus i * Pminus i = Pminus i)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    HilbertProjectiveData ι ℂ (EuclideanSpace ℂ (Fin 12)) :=
  matrixWeightedModel
    (fun i => blockMat12 (Pplus i) (Pminus i))
    (fun i => blockMat12_isHermitian (hplus_herm i) (hminus_herm i))
    (fun i => blockMat12_idempotent (hplus_idem i) (hminus_idem i))
    (blockMixWeight lam)
    (blockMixWeight_nonneg hlam)
    basisVec
    (blockMixWeight_norm lam)

theorem c12BlockMixtureModel_probability {ι : Type*}
    (Pplus Pminus : ι → Matrix (Fin 6) (Fin 6) ℂ)
    (hplus_herm : ∀ i, (Pplus i).IsHermitian) (hplus_idem : ∀ i, Pplus i * Pplus i = Pplus i)
    (hminus_herm : ∀ i, (Pminus i).IsHermitian) (hminus_idem : ∀ i, Pminus i * Pminus i = Pminus i)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (w : Word ι) :
    (c12BlockMixtureModel Pplus Pminus hplus_herm hplus_idem hminus_herm hminus_idem lam hlam).probability w =
      lam * ((1 / 6 : ℝ) * (Matrix.trace (wordOperator Pplus w)).re) +
        (1 - lam) * ((1 / 6 : ℝ) * (Matrix.trace (wordOperator Pminus w)).re) := by
  unfold c12BlockMixtureModel
  rw [matrixWeightedModel_probability, blockMat12_wordOperator]
  simp only [inner_matToCLM_basisVec_re]
  change ∑ k : Fin 12, blockMixWeight lam k *
      (blockMat12 (wordOperator Pplus w) (wordOperator Pminus w) k k).re = _
  rw [← Equiv.sum_comp equiv6Sum6, Fintype.sum_sum_type]
  simp only [blockMixWeight, Equiv.symm_apply_apply, blockMat12_diag_inl, blockMat12_diag_inr]
  have hre : ∀ A : Matrix (Fin 6) (Fin 6) ℂ,
      (Matrix.trace A).re = ∑ j : Fin 6, (A j j).re := fun A => by
    simp [Matrix.trace, Complex.re_sum]
  rw [hre (wordOperator Pplus w), hre (wordOperator Pminus w)]
  simp only [← Finset.mul_sum]
  ring

theorem proj0_mixture_norm
    (Pplus Pminus : Matrix (Fin 6) (Fin 6) ℂ)
    (hplus_herm : Pplus.IsHermitian) (hplus_idem : Pplus * Pplus = Pplus)
    (hminus_herm : Pminus.IsHermitian) (hminus_idem : Pminus * Pminus = Pminus)
    (htr_plus : Matrix.trace Pplus = 2) (htr_minus : Matrix.trace Pminus = 2) :
    ∑ k : Fin 12, (1 / 4 : ℝ) * ‖matToCLM (blockMat12 Pplus Pminus) (basisVec k)‖ ^ 2 = 1 := by
  let P := blockMat12 Pplus Pminus
  have hP_herm : P.IsHermitian := blockMat12_isHermitian hplus_herm hminus_herm
  have hP_idem : P * P = P := blockMat12_idempotent hplus_idem hminus_idem
  have hterm : ∀ k : Fin 12,
      ‖matToCLM P (basisVec k)‖ ^ 2 = (P k k).re := fun k => by
    have h1 : inner ℂ (matToCLM P (basisVec k)) (matToCLM P (basisVec k)) =
        inner ℂ (matToCLM (1 : Matrix (Fin 12) (Fin 12) ℂ) (matToCLM P (basisVec k)))
          (matToCLM P (basisVec k)) := by
      rw [matToCLM_one]
      rfl
    rw [← re_inner_self_eq_norm_sq, h1,
      inner_matToCLM_proj_basisVec_re P 1 hP_herm k, Matrix.mul_one, hP_idem,
      inner_matToCLM_basisVec_re]
  change ∑ k : Fin 12, (1 / 4 : ℝ) * ‖matToCLM P (basisVec k)‖ ^ 2 = 1
  simp only [hterm, ← Finset.mul_sum]
  have htr : ∑ k : Fin 12, (P k k).re = (Matrix.trace P).re := by
    simp [Matrix.trace, Complex.re_sum]
  rw [htr]
  have hP_tr : Matrix.trace P = 4 := by
    dsimp [P]
    rw [blockMat12_trace, htr_plus, htr_minus]
    norm_num
  rw [hP_tr]
  norm_num

def c12Proj0MixtureModel {ι : Type*}
    (Pplus Pminus : ι → Matrix (Fin 6) (Fin 6) ℂ)
    (hplus_herm : ∀ i, (Pplus i).IsHermitian) (hplus_idem : ∀ i, Pplus i * Pplus i = Pplus i)
    (hminus_herm : ∀ i, (Pminus i).IsHermitian) (hminus_idem : ∀ i, Pminus i * Pminus i = Pminus i)
    (i0 : ι) (htr_plus : Matrix.trace (Pplus i0) = 2)
    (htr_minus : Matrix.trace (Pminus i0) = 2) :
    HilbertProjectiveData ι ℂ (EuclideanSpace ℂ (Fin 12)) :=
  matrixWeightedModel
    (fun i => blockMat12 (Pplus i) (Pminus i))
    (fun i => blockMat12_isHermitian (hplus_herm i) (hminus_herm i))
    (fun i => blockMat12_idempotent (hplus_idem i) (hminus_idem i))
    (fun _ => (1 / 4 : ℝ))
    (fun _ => by norm_num)
    (fun k => matToCLM (blockMat12 (Pplus i0) (Pminus i0)) (basisVec k))
    (proj0_mixture_norm (Pplus i0) (Pminus i0) (hplus_herm i0) (hplus_idem i0)
      (hminus_herm i0) (hminus_idem i0) htr_plus htr_minus)

theorem c12Proj0MixtureModel_probability {ι : Type*}
    (Pplus Pminus : ι → Matrix (Fin 6) (Fin 6) ℂ)
    (hplus_herm : ∀ i, (Pplus i).IsHermitian) (hplus_idem : ∀ i, Pplus i * Pplus i = Pplus i)
    (hminus_herm : ∀ i, (Pminus i).IsHermitian) (hminus_idem : ∀ i, Pminus i * Pminus i = Pminus i)
    (i0 : ι) (htr_plus : Matrix.trace (Pplus i0) = 2)
    (htr_minus : Matrix.trace (Pminus i0) = 2) (w : Word ι) :
    (c12Proj0MixtureModel Pplus Pminus hplus_herm hplus_idem hminus_herm hminus_idem
      i0 htr_plus htr_minus).probability w =
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (Matrix.trace (Pplus i0 * wordOperator Pplus w)).re) +
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (Matrix.trace (Pminus i0 * wordOperator Pminus w)).re) := by
  let P0 := blockMat12 (Pplus i0) (Pminus i0)
  have hP0_herm : P0.IsHermitian := blockMat12_isHermitian (hplus_herm i0) (hminus_herm i0)
  have hP0_idem : P0 * P0 = P0 := blockMat12_idempotent (hplus_idem i0) (hminus_idem i0)
  unfold c12Proj0MixtureModel
  rw [matrixWeightedModel_probability]
  change ∑ k : Fin 12, (1 / 4 : ℝ) * (inner ℂ
      (matToCLM (wordOperator (fun i => blockMat12 (Pplus i) (Pminus i)) w)
        (matToCLM P0 (basisVec k))) (matToCLM P0 (basisVec k))).re = _
  simp only [inner_matToCLM_proj_basisVec_re P0 _ hP0_herm, ← Finset.mul_sum,
    sum_inner_matToCLM_basisVec_re]
  have htr : Matrix.trace (P0 * wordOperator (fun i => blockMat12 (Pplus i) (Pminus i)) w * P0) =
      Matrix.trace (Pplus i0 * wordOperator Pplus w) +
        Matrix.trace (Pminus i0 * wordOperator Pminus w) := by
    rw [Matrix.trace_mul_cycle, Matrix.mul_assoc, ← Matrix.mul_assoc P0 P0, hP0_idem,
      blockMat12_wordOperator]
    change Matrix.trace (blockMat12 (Pplus i0) (Pminus i0) *
      blockMat12 (wordOperator Pplus w) (wordOperator Pminus w)) = _
    rw [← blockMat12_mul, blockMat12_trace]
  rw [htr, Complex.add_re]
  ring

end C12Models

/-! ## Section 4: `QuaternionicWindow` Bridge Lemmas -/

section QuatWindowBridge

private theorem tracePairing_unit_right_bridge (x : Albert) :
    tracePairing x albertUnit = albertTrace x := by
  unfold tracePairing
  rw [jordanMul_albertUnit_right]

def quatProj6 (Q : QuaternionicWindow) {ι : Type*}
    (q : ι → Albert) (hq : ∀ i, q i ∈ Q.subalgebra.carrier) :
    ι → Matrix (Fin 6) (Fin 6) ℂ :=
  fun i => (symplecticQuatEmbed Q).map ⟨q i, hq i⟩

theorem quatProj6_hermitian (Q : QuaternionicWindow) {ι : Type*}
    (q : ι → Albert) (hq : ∀ i, q i ∈ Q.subalgebra.carrier) (i : ι) :
    (quatProj6 Q q hq i).IsHermitian :=
  (symplecticQuatEmbed Q).hermitian ⟨q i, hq i⟩

theorem quatProj6_idempotent (Q : QuaternionicWindow) {ι : Type*}
    (q : ι → Albert) (hq : ∀ i, q i ∈ Q.subalgebra.carrier)
    (hq_atom : ∀ i, IsAtom (q i)) (i : ι) :
    quatProj6 Q q hq i * quatProj6 Q q hq i = quatProj6 Q q hq i := by
  have hj := (symplecticQuatEmbed Q).jordan ⟨q i, hq i⟩ ⟨q i, hq i⟩
  have hq1 : (⟨jordanMul (q i) (q i), Q.subalgebra.product_mem _ (hq i) _ (hq i)⟩ :
      Q.subalgebra.carrier) = ⟨q i, hq i⟩ := Subtype.ext (hq_atom i).1
  rw [hq1] at hj
  change quatProj6 Q q hq i = (1 / 2 : ℝ) •
    (quatProj6 Q q hq i * quatProj6 Q q hq i + quatProj6 Q q hq i * quatProj6 Q q hq i) at hj
  have h2 : (1 / 2 : ℝ) •
      (quatProj6 Q q hq i * quatProj6 Q q hq i + quatProj6 Q q hq i * quatProj6 Q q hq i) =
      quatProj6 Q q hq i * quatProj6 Q q hq i := by module
  rw [h2] at hj
  exact hj.symm

theorem quatProj6_trace (Q : QuaternionicWindow) {ι : Type*}
    (q : ι → Albert) (hq : ∀ i, q i ∈ Q.subalgebra.carrier)
    (hq_atom : ∀ i, IsAtom (q i)) (i : ι) :
    Matrix.trace (quatProj6 Q q hq i) = 2 := by
  have hre : (Matrix.trace (quatProj6 Q q hq i)).re = 2 := by
    have h1 := symplecticQuatEmbed_tracePairing Q ⟨q i, hq i⟩
      ⟨albertUnit, Q.subalgebra.unit_mem⟩
    rw [(symplecticQuatEmbed Q).unit, Matrix.mul_one, tracePairing_unit_right_bridge,
      (hq_atom i).2, mul_one] at h1
    exact h1
  have him : (Matrix.trace (quatProj6 Q q hq i)).im = 0 := by
    rw [Matrix.trace, Complex.im_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk := congrArg Complex.im
      (congrFun (congrFun (quatProj6_hermitian Q q hq i).eq k) k)
    simp only [Matrix.conjTranspose_apply, Matrix.diag_apply, Complex.star_def,
      Complex.conj_im] at hk ⊢
    linarith
  exact Complex.ext hre him

theorem quatProj6_wordProb_e3 (Q : QuaternionicWindow) {ι : Type*}
    (q : ι → Albert) (hq : ∀ i, q i ∈ Q.subalgebra.carrier) (w : Word ι) :
    (1 / 6 : ℝ) * (Matrix.trace (wordOperator (quatProj6 Q q hq) w)).re =
      nativeWordProbability q ((1 / 3 : ℝ) • albertUnit) w := by
  let z : Q.subalgebra.carrier := (1 / 6 : ℝ) • ⟨albertUnit, Q.subalgebra.unit_mem⟩
  have hz : ∀ x : Q.subalgebra.carrier,
      (Matrix.trace ((symplecticQuatEmbed Q).map z * (symplecticQuatEmbed Q).map x)).re =
        tracePairing ((1 / 3 : ℝ) • albertUnit) x.1 := by
    intro x
    change (Matrix.trace ((symplecticQuatEmbed Q).map
      ((1 / 6 : ℝ) • ⟨albertUnit, Q.subalgebra.unit_mem⟩) *
      (symplecticQuatEmbed Q).map x)).re = _
    rw [map_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      symplecticQuatEmbed_tracePairing, tracePairing_smul_left]
    ring
  have hp := (symplecticQuatEmbed Q).pairing_words ((1 / 3 : ℝ) • albertUnit) z hz
    (fun i => ⟨q i, hq i⟩) w
  have hz1 : (symplecticQuatEmbed Q).map z = (1 / 6 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
    change (symplecticQuatEmbed Q).map ((1 / 6 : ℝ) • ⟨albertUnit, Q.subalgebra.unit_mem⟩) = _
    rw [map_smul, (symplecticQuatEmbed Q).unit]
  rw [hz1, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  exact hp

theorem quatProj6_wordProb_atom (Q : QuaternionicWindow) {ι : Type*}
    (q : ι → Albert) (hq : ∀ i, q i ∈ Q.subalgebra.carrier)
    (i0 : ι) (w : Word ι) :
    (1 / 2 : ℝ) * (Matrix.trace (quatProj6 Q q hq i0 * wordOperator (quatProj6 Q q hq) w)).re =
      nativeWordProbability q (q i0) w := by
  let z : Q.subalgebra.carrier := (1 / 2 : ℝ) • ⟨q i0, hq i0⟩
  have hz : ∀ x : Q.subalgebra.carrier,
      (Matrix.trace ((symplecticQuatEmbed Q).map z * (symplecticQuatEmbed Q).map x)).re =
        tracePairing (q i0) x.1 := by
    intro x
    change (Matrix.trace ((symplecticQuatEmbed Q).map ((1 / 2 : ℝ) • ⟨q i0, hq i0⟩) *
      (symplecticQuatEmbed Q).map x)).re = _
    rw [map_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      symplecticQuatEmbed_tracePairing]
    ring
  have hp := (symplecticQuatEmbed Q).pairing_words (q i0) z hz (fun i => ⟨q i, hq i⟩) w
  have hz1 : (symplecticQuatEmbed Q).map z = (1 / 2 : ℝ) • quatProj6 Q q hq i0 := by
    change (symplecticQuatEmbed Q).map ((1 / 2 : ℝ) • ⟨q i0, hq i0⟩) = _
    rw [map_smul]
    rfl
  rw [hz1, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  exact hp

end QuatWindowBridge

/-! ## Section 5: Class-(I) Real and Quaternionic Model Conversions -/

section ClassIConversions

def hilbertComplexToReal {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : HilbertProjectiveData ι ℂ H) :
    HilbertProjectiveData ι ℝ (CyclicHilbert M.toAlgebraic) :=
  cyclicHilbertModel M.toAlgebraic

theorem hilbertComplexToReal_probability {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : HilbertProjectiveData ι ℂ H) (w : Word ι) :
    (hilbertComplexToReal M).probability w = M.probability w := by
  let MR := hilbertComplexToReal M
  have h1 : MR.probability w = MR.toAlgebraic.probability w :=
    (MR.toAlgebraic_probability w).symm
  have h2 : MR.toAlgebraic.probability w = M.toAlgebraic.probability w :=
    cyclicHilbertModel_probability M.toAlgebraic w
  have h3 : M.toAlgebraic.probability w = M.probability w :=
    M.toAlgebraic_probability w
  exact h1.trans (h2.trans h3)

def hilbertComplexToQuaternionic {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : HilbertProjectiveData ι ℂ H) :
    QuaternionicProjectiveData ι
      (fourCopyQuaternionicStructure (H := CyclicHilbert M.toAlgebraic)) :=
  (hilbertComplexToReal M).quaternionExtensionModel

theorem hilbertComplexToQuaternionic_probability {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : HilbertProjectiveData ι ℂ H) (w : Word ι) :
    (hilbertComplexToQuaternionic M).toAlgebraic.probability w = M.probability w := by
  let MR := hilbertComplexToReal M
  have h1 : MR.quaternionExtensionModel.toAlgebraic.probability w = MR.toAlgebraic.probability w :=
    MR.quaternionExtensionModel_probability w
  have h2 : MR.toAlgebraic.probability w = MR.probability w :=
    MR.toAlgebraic_probability w
  have h3 : MR.probability w = M.probability w :=
    hilbertComplexToReal_probability M w
  exact h1.trans (h2.trans h3)

theorem hilbertComplexToQuaternionic_state_wordEffect {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : HilbertProjectiveData ι ℂ H) (w : Word ι) :
    (hilbertComplexToQuaternionic M).state ((hilbertComplexToQuaternionic M).wordEffect w) =
      M.probability w := by
  rw [← (hilbertComplexToQuaternionic M).toAlgebraic_probability w]
  exact hilbertComplexToQuaternionic_probability M w

end ClassIConversions

end AlbertSequential.MatchingModels
