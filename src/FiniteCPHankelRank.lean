/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HermitianCoordinates
public import CPWordProbabilities
public import NativeHankelRank
public import Interfaces.OperationalBoundaries

/-! The finite complex CP rank bound uses d² real coordinates of Hermitian
branch states. No faithfulness, conditioning or nonzero branch is assumed. -/
@[expose] public section
noncomputable section
namespace AlbertSequential
open scoped BigOperators Matrix ComplexOrder

def realHermitianCoordinateUnit {d : ℕ} (k : Fin d × Fin d) : HermitianCoordinates d :=
  Matrix.single k.1 k.2 1

theorem realHermitianCoordinateExpansion {d : ℕ} (r : HermitianCoordinates d) :
    r = ∑ k : Fin d × Fin d, r k.1 k.2 • realHermitianCoordinateUnit k := by
  classical
  ext i j
  simp [realHermitianCoordinateUnit, Fintype.sum_prod_type, Matrix.sum_apply,
    Matrix.single_apply, ite_and]

theorem hermitian_expansion {d : ℕ} (X : ComplexMatrix d) (hX : X.IsHermitian) :
    X = ∑ k : Fin d × Fin d, hermitianCoordinates X k.1 k.2 •
      matrixFromHermitianCoordinates (realHermitianCoordinateUnit k) := by
  have h := congrArg (matrixFromHermitianCoordinatesLinear d)
    (realHermitianCoordinateExpansion (hermitianCoordinates X))
  simpa only [matrixFromHermitianCoordinatesLinear, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_smul, matrixFromHermitianCoordinates_inverse X hX] using h

theorem hermitian_readout_rank_le {d m n : ℕ} (s : Fin m → ComplexMatrix d)
    (hs : ∀ i, (s i).IsHermitian) (L : Fin n → (ComplexMatrix d →ₗ[ℝ] ℝ)) :
    Matrix.rank (fun i j => L j (s i) : Matrix (Fin m) (Fin n) ℝ) ≤ d ^ 2 := by
  let A : Matrix (Fin m) (Fin d × Fin d) ℝ :=
    fun i k => hermitianCoordinates (s i) k.1 k.2
  let B : Matrix (Fin d × Fin d) (Fin n) ℝ :=
    fun k j => L j (matrixFromHermitianCoordinates (realHermitianCoordinateUnit k))
  have heq : (fun i j => L j (s i) : Matrix (Fin m) (Fin n) ℝ) = A * B := by
    ext i j
    change L j (s i) = ∑ k, A i k * B k j
    have h := congrArg (L j) (hermitian_expansion (s i) (hs i))
    simpa only [map_sum, map_smul, smul_eq_mul, A, B] using h
  rw [heq]
  exact (Matrix.rank_mul_le_left A B).trans
    (by simpa [Fintype.card_prod, pow_two] using Matrix.rank_le_card_width A)

def finiteCPWordUpdate {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) : InstrumentWord A →
      (ComplexMatrix d →ₗ[ℝ] ComplexMatrix d)
  | [] => LinearMap.id
  | a :: w => (finiteCPWordUpdate r w).comp ((choiLinearMap (r.2 a.1 a.2)).restrictScalars ℝ)

theorem finiteCPWordUpdate_apply {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (w : InstrumentWord A) (Y : ComplexMatrix d) :
    finiteCPWordUpdate r w Y = w.foldl (fun Z a => choiAction (r.2 a.1 a.2) Z) Y := by
  induction w generalizing Y with
  | nil => rfl
  | cons a w ih => exact ih _

def finiteCPSuffixReadout {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (w : InstrumentWord A) : ComplexMatrix d →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp
    ((Matrix.traceLinearMap (Fin d) ℝ ℂ).comp (finiteCPWordUpdate r w))

theorem finiteCP_suffix_pairing {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (p : P) (u v : InstrumentWord A) :
    finiteCPWordProbability r p (u ++ v) =
      finiteCPSuffixReadout r v (finiteCPWordState r p u) := by
  simp only [finiteCPWordProbability, finiteCPWordState, List.foldl_append,
    finiteCPSuffixReadout, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Complex.reCLM_apply, Matrix.traceLinearMap_apply, finiteCPWordUpdate_apply]

theorem finiteCP_hankel_rank_le {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A)
    (hr : IsNormalizedFiniteCPModel r) (p : P) {m n : ℕ}
    (u : Fin m → InstrumentWord A) (v : Fin n → InstrumentWord A) :
    Matrix.rank (fun i j => finiteCPWordProbability r p (u i ++ v j) :
      Matrix (Fin m) (Fin n) ℝ) ≤ d ^ 2 := by
  have heq : (fun i j => finiteCPWordProbability r p (u i ++ v j) :
      Matrix (Fin m) (Fin n) ℝ) =
      (fun i j => finiteCPSuffixReadout r (v j) (finiteCPWordState r p (u i))) := by
    ext i j
    exact finiteCP_suffix_pairing r p (u i) (v j)
  rw [heq]
  exact hermitian_readout_rank_le _
    (fun i => (finiteCPWordState_positive r hr p (u i)).isHermitian) _

theorem finiteBinaryCP_hankel_rank_le (d : ℕ) (X : Type*)
    (r : RawFiniteCPModel d Unit X (fun _ => Bool)) (hr : IsNormalizedFiniteCPModel r)
    (m n : ℕ) (u : Fin m → Word X) (v : Fin n → Word X) :
    (finiteHankelMatrix
      (fun w => finiteCPWordProbability r () (generalizeBinaryWord w)) u v).rank ≤ d ^ 2 := by
  change Matrix.rank (fun i j => finiteCPWordProbability r ()
    (generalizeBinaryWord (u i ++ v j))) ≤ d ^ 2
  simpa only [generalizeBinaryWord, List.map_append] using
    finiteCP_hankel_rank_le r hr ()
      (fun i => generalizeBinaryWord (u i)) (fun j => generalizeBinaryWord (v j))

theorem native_CP_dimension_at_least_six {n d : ℕ} (p : Fin n → Albert)
    (hp : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p)
    (r : RawFiniteCPModel d Unit (Fin n) (fun _ => Bool)) (hr : IsNormalizedFiniteCPModel r)
    (hmatch : ∀ w, finiteCPWordProbability r () (generalizeBinaryWord w) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) : 6 ≤ d := by
  obtain ⟨u, v, huv⟩ := exists_native_hankel_rank27 p hp hg
  have hrank := finiteBinaryCP_hankel_rank_le d (Fin n) r hr 27 27 u v
  have heq : finiteHankelMatrix
      (fun w => finiteCPWordProbability r () (generalizeBinaryWord w)) u v =
      nativeFiniteHankel p ((1 / 3 : ℝ) • albertUnit) u v := by
    ext i j
    exact hmatch _
  rw [heq, huv] at hrank
  by_contra hd
  have hd5 : d ≤ 5 := by omega
  have hsq : d ^ 2 ≤ 25 := by nlinarith
  omega

def nativeHankelDimensionObligations : HankelDimensionObligations where
  finite_CP_bound := finiteBinaryCP_hankel_rank_le
  native_rank_witness n p hp hg := by
    obtain ⟨u, v, h⟩ := exists_native_hankel_rank27 p hp hg
    exact ⟨u, v, h⟩
  native_lower_bound n d p hp hg r hr hm := native_CP_dimension_at_least_six p hp hg r hr hm

end AlbertSequential
