/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QutritFourierBases
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic

/-! Four actual orthonormal qutrit bases and their literal rank-one projections.
The first is the coordinate basis and the other three are quadratic Fourier.
All inner products follow the explicit finite convention in QutritFourierBases. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped BigOperators Matrix ComplexOrder

def qutritStandardVector (b : Fin 3) : Fin 3 → ℂ := Pi.single b 1

def qutritBasisVector (k : Fin 4) (b : Fin 3) : Fin 3 → ℂ :=
  Fin.cases (qutritStandardVector b)
    (fun a => qutritFourierVector (qutritCharacter a) b) k

theorem qutritInner_star (v w : Fin 3 → ℂ) : star (qutritInner v w) = qutritInner w v := by
  simp only [qutritInner, star_sum, star_mul, star_star]

theorem qutritStandardVector_inner_left (b : Fin 3) (v : Fin 3 → ℂ) :
    qutritInner (qutritStandardVector b) v = v b := by
  simp [qutritInner, qutritStandardVector, Pi.single_apply]

theorem qutritStandardVector_inner (b c : Fin 3) :
    qutritInner (qutritStandardVector b) (qutritStandardVector c) = if b = c then 1 else 0 := by
  rw [qutritStandardVector_inner_left]
  simp [qutritStandardVector, Pi.single_apply, eq_comm]

theorem qutritBasisVector_orthonormal (k : Fin 4) (b c : Fin 3) :
    qutritInner (qutritBasisVector k b) (qutritBasisVector k c) = if b = c then 1 else 0 := by
  refine Fin.cases ?_ (fun a => ?_) k
  · exact qutritStandardVector_inner b c
  · exact qutritFourierVector_orthonormal a b c

theorem qutritBasisVector_unbiased (k l : Fin 4) (hkl : k ≠ l) (b c : Fin 3) :
    Complex.normSq (qutritInner (qutritBasisVector k b) (qutritBasisVector l c)) = 1 / 3 := by
  revert l
  refine Fin.cases ?_ (fun a => ?_) k
  · intro l
    refine Fin.cases ?_ (fun a' => ?_) l
    all_goals intro hkl
    · exact False.elim (hkl rfl)
    · change Complex.normSq (qutritInner (qutritStandardVector b)
        (qutritFourierVector (qutritCharacter a') c)) = _
      rw [qutritStandardVector_inner_left]
      exact qutritFourierVector_coordinate_normSq a' c b
  · intro l
    refine Fin.cases ?_ (fun a' => ?_) l
    all_goals intro hkl
    · change Complex.normSq (qutritInner (qutritFourierVector (qutritCharacter a) b)
        (qutritStandardVector c)) = _
      rw [← qutritInner_star]
      simp only [Complex.star_def, Complex.normSq_conj, qutritStandardVector_inner_left]
      exact qutritFourierVector_coordinate_normSq a b c
    · exact qutritFourierVector_unbiased a a' (fun h => hkl (congrArg Fin.succ h)) b c

def qutritBasisMatrix (k : Fin 4) : ComplexMatrix3 := fun x b => qutritBasisVector k b x

theorem qutritBasisMatrix_orthonormal (k : Fin 4) :
    (qutritBasisMatrix k).conjTranspose * qutritBasisMatrix k = 1 := by
  ext b c
  change qutritInner (qutritBasisVector k b) (qutritBasisVector k c) = _
  rw [qutritBasisVector_orthonormal]
  by_cases h : b = c <;> simp [h, Matrix.one_apply]

theorem qutritBasisMatrix_complete (k : Fin 4) :
    qutritBasisMatrix k * (qutritBasisMatrix k).conjTranspose = 1 :=
  mul_eq_one_comm.mp (qutritBasisMatrix_orthonormal k)

def qutritRankOneProjection (v : Fin 3 → ℂ) : ComplexMatrix3 :=
  fun i j => v i * star (v j)

theorem qutritRankOneProjection_trace (v : Fin 3 → ℂ) :
    Matrix.trace (qutritRankOneProjection v) = qutritInner v v := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem qutritRankOneProjection_positive (v : Fin 3 → ℂ) :
    (qutritRankOneProjection v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem qutritRankOneProjection_mul_apply (v w : Fin 3 → ℂ) (i j : Fin 3) :
    (qutritRankOneProjection v * qutritRankOneProjection w) i j =
      v i * qutritInner v w * star (w j) := by
  simp only [Matrix.mul_apply, qutritRankOneProjection, qutritInner,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem qutritRankOneProjection_idempotent (v : Fin 3 → ℂ) (hv : qutritInner v v = 1) :
    qutritRankOneProjection v * qutritRankOneProjection v = qutritRankOneProjection v := by
  ext i j
  rw [qutritRankOneProjection_mul_apply, hv, mul_one]
  rfl

def qutritMUBProjection (k : Fin 4) (b : Fin 3) : ComplexMatrix3 :=
  qutritRankOneProjection (qutritBasisVector k b)

theorem qutritMUBProjection_rankOne (k : Fin 4) (b : Fin 3) :
    IsComplexRankOneProjection (qutritMUBProjection k b) :=
  ⟨qutritBasisVector k b, by simpa only [qutritInner, ↓reduceIte] using qutritBasisVector_orthonormal k b b,
    fun _ _ => rfl⟩

theorem qutritMUBProjection_positive (k : Fin 4) (b : Fin 3) :
    (qutritMUBProjection k b).PosSemidef := qutritRankOneProjection_positive _

theorem qutritMUBProjection_idempotent (k : Fin 4) (b : Fin 3) :
    qutritMUBProjection k b * qutritMUBProjection k b = qutritMUBProjection k b :=
  qutritRankOneProjection_idempotent _ (by simpa using qutritBasisVector_orthonormal k b b)

theorem qutritMUBProjection_sum (k : Fin 4) : ∑ b, qutritMUBProjection k b = 1 := by
  rw [← qutritBasisMatrix_complete k]
  ext i j
  rfl

theorem qutritMUBProjection_trace (k : Fin 4) (b : Fin 3) :
    Matrix.trace (qutritMUBProjection k b) = 1 := by
  exact (qutritRankOneProjection_trace _).trans (by simpa using qutritBasisVector_orthonormal k b b)

end AlbertSequential
