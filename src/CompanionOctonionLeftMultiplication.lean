/- SPDX-License-Identifier: Apache-2.0 -/
module

public import OctonionRealCoordinates
public import OctonionGeometry
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! The real left-multiplication matrices in companion Proposition 2.7. -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix
namespace AlbertSequential.NativeAnalysis

abbrev AlbertColumnCoordinate := Fin 3 × OctonionCoordinate

theorem albertColumnCoordinate_card : Fintype.card AlbertColumnCoordinate = 24 := by decide

theorem octonionCoordinate_card : Fintype.card OctonionCoordinate = 8 := by decide

def octonionLeftColumnMap (v : Fin 3 → Octonion) :
    (OctonionCoordinate → ℝ) →ₗ[ℝ] AlbertColumnCoordinate → ℝ where
  toFun h i := octonionRealCoordinates
    (octonionMul (v i.1) (octonionRealCoordinates.symm h)) i.2
  map_add' h k := by
    funext i
    simp only [map_add, octonionMul_add_right, Pi.add_apply]
  map_smul' r h := by
    funext i
    simp only [map_smul, octonionMul_smul_right, Pi.smul_apply, RingHom.id_apply]

def octonionLeftColumn (v : Fin 3 → Octonion) :
    Matrix AlbertColumnCoordinate OctonionCoordinate ℝ :=
  LinearMap.toMatrix' (octonionLeftColumnMap v)

theorem octonionLeftColumn_mulVec (v : Fin 3 → Octonion) (h : Octonion) :
    octonionLeftColumn v *ᵥ octonionRealCoordinates h =
      fun i => octonionRealCoordinates (octonionMul (v i.1) h) i.2 := by
  rw [octonionLeftColumn, LinearMap.toMatrix'_mulVec]
  funext i
  change octonionRealCoordinates
    (octonionMul (v i.1) (octonionRealCoordinates.symm (octonionRealCoordinates h))) i.2 = _
  rw [LinearEquiv.symm_apply_apply]

theorem octonionLeftColumn_apply (v : Fin 3 → Octonion) (i : AlbertColumnCoordinate)
    (j : OctonionCoordinate) :
    octonionLeftColumn v i j =
      octonionRealCoordinates
        (octonionMul (v i.1) (octonionRealCoordinates.symm (Pi.single j 1))) i.2 := rfl

def octonionColumnNormSq (v : Fin 3 → Octonion) : ℝ :=
  ∑ i, octNormSq (v i)

theorem octDot_mul_left_self (x h k : Octonion) :
    octDot (octonionMul x h) (octonionMul x k) =
      octNormSq x * octDot h k := by
  rw [octDot_mul_left, octMul_conj_left_cancel, octDot_smul_right]

theorem octonionLeftColumn_gram (v : Fin 3 → Octonion) :
    (octonionLeftColumn v)ᵀ * octonionLeftColumn v =
      octonionColumnNormSq v • (1 : Matrix OctonionCoordinate OctonionCoordinate ℝ) := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.transpose_apply, octonionLeftColumn_apply, Matrix.smul_apply, smul_eq_mul,
    octonionColumnNormSq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [← octonionRealCoordinates_pairing, octDot_mul_left_self, octonionRealCoordinates_pairing]
  simp only [LinearEquiv.apply_symm_apply]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

def octonionLeftProjection (v : Fin 3 → Octonion) :
    Matrix AlbertColumnCoordinate AlbertColumnCoordinate ℝ :=
  (octonionColumnNormSq v)⁻¹ • (octonionLeftColumn v * (octonionLeftColumn v)ᵀ)

theorem octonionLeftProjection_transpose (v : Fin 3 → Octonion) :
    (octonionLeftProjection v)ᵀ = octonionLeftProjection v := by
  simp [octonionLeftProjection, Matrix.transpose_mul]

theorem octonionLeftProjection_idempotent (v : Fin 3 → Octonion)
    (hv : 0 < octonionColumnNormSq v) :
    octonionLeftProjection v * octonionLeftProjection v = octonionLeftProjection v := by
  let n := octonionColumnNormSq v
  let L := octonionLeftColumn v
  change (n⁻¹ • (L * Lᵀ)) * (n⁻¹ • (L * Lᵀ)) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc Lᵀ,
    octonionLeftColumn_gram, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  change n⁻¹ • (n⁻¹ • (n • (L * Lᵀ))) = n⁻¹ • (L * Lᵀ)
  rw [smul_smul n⁻¹ n, inv_mul_cancel₀ hv.ne', one_smul]

theorem octonionLeftProjection_rank (v : Fin 3 → Octonion)
    (hv : 0 < octonionColumnNormSq v) : (octonionLeftProjection v).rank = 8 := by
  let n := octonionColumnNormSq v
  let L := octonionLeftColumn v
  let N := (Real.sqrt n)⁻¹ • L
  have hn : 0 < n := hv
  have hs : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = n⁻¹ := by
    rw [← pow_two, inv_pow, Real.sq_sqrt hn.le]
  have hg : Nᵀ * N = 1 := by
    dsimp only [N]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, octonionLeftColumn_gram]
    change (Real.sqrt n)⁻¹ • ((Real.sqrt n)⁻¹ • (n • _)) = _
    rw [smul_smul _ _ (n • _), hs, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
  have hp : N * Nᵀ = octonionLeftProjection v := by
    dsimp only [N]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
    rfl
  rw [← hp, Matrix.rank_self_mul_transpose, ← Matrix.rank_transpose_mul_self, hg,
    Matrix.rank_one, octonionCoordinate_card]

theorem octonionLeftProjection_trace (v : Fin 3 → Octonion)
    (hv : 0 < octonionColumnNormSq v) : (octonionLeftProjection v).trace = 8 := by
  rw [octonionLeftProjection, Matrix.trace_smul, Matrix.trace_mul_comm, octonionLeftColumn_gram,
    Matrix.trace_smul, smul_smul, inv_mul_cancel₀ hv.ne', one_smul, Matrix.trace_one,
    octonionCoordinate_card]
  norm_num

end AlbertSequential.NativeAnalysis
