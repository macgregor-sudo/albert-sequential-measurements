/- SPDX-License-Identifier: Apache-2.0 -/
module
public import GeneralEJACoefficientRegular
public import HermitianJordanEmbedding
public import RealMatrixComplexification
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal) {n : ℕ} (c : Fin n → E)
    {r s t : Fin n} (C : P.PeirceTriangleCoordinates hfr c r s t)

local notation "W" => P.frameOffDiagonalSpace c
local notation "A" => W r t
local notation "Mat" => Matrix (Fin n) (Fin n) A

section RegularBlocks

variable {d : ℕ} (R : P.PeirceCoefficientRegularRepresentation hfr c C d)

local notation "Idx" => Fin n × Fin d

def peirceCoefficientRegularBlock : Mat →ₗ[ℝ] Matrix Idx Idx ℝ where
  toFun X i j := R.map (X i.1 j.1) i.2 j.2
  map_add' X Y := Matrix.ext fun i j =>
    congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i.2 j.2)
      (R.map.map_add (X i.1 j.1) (Y i.1 j.1))
  map_smul' a X := Matrix.ext fun i j =>
    congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i.2 j.2) (R.map.map_smul a (X i.1 j.1))

local notation "blk" => P.peirceCoefficientRegularBlock hfr c C R

theorem peirceCoefficientRegularBlock_injective : Function.Injective blk := by
  intro X Y h
  apply Matrix.ext
  intro i j
  apply R.injective
  apply Matrix.ext
  intro a b
  exact congrArg (fun M : Matrix Idx Idx ℝ => M (i,a) (j,b)) h

theorem peirceCoefficientRegularBlock_unit :
    blk (Matrix.diagonal (fun _ : Fin n => C.unit)) = 1 := by
  apply Matrix.ext
  intro i j
  change R.map (Matrix.diagonal (fun _ : Fin n => C.unit) i.1 j.1) i.2 j.2 = _
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i.1 = j.1
  · rw [ite_eq_left h, R.unit, Matrix.one_apply]
    have he : i = j ↔ i.2 = j.2 := ⟨congrArg Prod.snd, Prod.ext h⟩
    simp only [he]
  · have hn : i ≠ j := fun hij => h (congrArg Prod.fst hij)
    rw [ite_eq_right h, map_zero, Matrix.zero_apply, ite_eq_right hn]

theorem peirceCoefficientRegularBlock_mul (X Y : Mat) :
    blk (P.peirceCoefficientMatrixMul hfr c C X Y) = blk X * blk Y := by
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change R.map (P.peirceCoefficientMatrixMul hfr c C X Y i.1 k.1) i.2 k.2 =
    ∑ j : Fin n, ∑ b : Fin d, R.map (X i.1 j) i.2 b * R.map (Y j k.1) b k.2
  rw [P.peirceCoefficientMatrixMul_apply, map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [R.mul, Matrix.mul_apply]

theorem peirceCoefficientRegularBlock_transpose (X : Mat) (hX : P.PeirceCoefficientHermitian hfr c C X) :
    (blk X).transpose = blk X := by
  apply Matrix.ext
  intro i j
  change R.map (X j.1 i.1) j.2 i.2 = R.map (X i.1 j.1) i.2 j.2
  rw [hX i.1 j.1, ← R.conj, Matrix.transpose_apply]

end RegularBlocks

theorem exists_faithfulHermitianJordanEmbedding_of_peirceAssociative
    (H : P.FaithfulPeirceHermitianMatrixMap hfr c C)
    (hAssoc : ∀ x y z, C.product (C.product x y) z = C.product x (C.product y z)) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
  obtain ⟨d, ⟨R⟩⟩ := P.exists_peirceCoefficientRegularRepresentation hfr c C hAssoc
  let I := Fin n × Fin d
  let Nreal := (P.peirceCoefficientRegularBlock hfr c C R).comp H.map
  have hsmul (a : ℝ) (X : Matrix I I ℝ) : complexifyMatrix (a • X) = a • complexifyMatrix X :=
    complexifyMatrix_real_smul a X
  let N : E →ₗ[ℝ] Matrix I I ℂ := {
    toFun := fun x => complexifyMatrix (Nreal x)
    map_add' := fun x y => by rw [map_add, complexifyMatrix_add]
    map_smul' := fun a x => by rw [map_smul, hsmul, RingHom.id_apply] }
  let reindex := Matrix.reindexStarAlgEquiv ℝ ℂ (Fintype.equivFin I)
  refine ⟨Fintype.card I, ⟨{
    map := reindex.toAlgEquiv.toLinearMap.comp N
    injective := ?_
    hermitian := ?_
    unit := ?_
    jordan := ?_ }⟩⟩
  · exact reindex.injective.comp (complexifyMatrix_injective.comp
      ((P.peirceCoefficientRegularBlock_injective hfr c C R).comp H.injective))
  · intro x
    change star (reindex (complexifyMatrix (Nreal x))) = reindex (complexifyMatrix (Nreal x))
    rw [← map_star]
    congr 1
    change (complexifyMatrix (Nreal x)).conjTranspose = complexifyMatrix (Nreal x)
    have ht : (Nreal x).transpose = Nreal x :=
      P.peirceCoefficientRegularBlock_transpose hfr c C R _ (H.hermitian x)
    rw [← complexifyMatrix_transpose, ht]
  · change reindex (complexifyMatrix (P.peirceCoefficientRegularBlock hfr c C R (H.map P.unit))) = 1
    rw [H.unit, P.peirceCoefficientRegularBlock_unit hfr c C R, complexifyMatrix_one, map_one]
  · intro x y
    have hm : Nreal (P.product x y) =
        (1 / 2 : ℝ) • (Nreal x * Nreal y + Nreal y * Nreal x) := by
      change P.peirceCoefficientRegularBlock hfr c C R (H.map (P.product x y)) = _
      rw [H.jordan, P.peirceCoefficientMatrixJordan_apply, map_smul, map_add,
        P.peirceCoefficientRegularBlock_mul hfr c C R, P.peirceCoefficientRegularBlock_mul hfr c C R]
      rfl
    change reindex (complexifyMatrix (Nreal (P.product x y))) =
      (1 / 2 : ℝ) • (reindex (complexifyMatrix (Nreal x)) * reindex (complexifyMatrix (Nreal y)) +
        reindex (complexifyMatrix (Nreal y)) * reindex (complexifyMatrix (Nreal x)))
    rw [hm, hsmul, complexifyMatrix_add, complexifyMatrix_mul, complexifyMatrix_mul]
    simp only [map_smul, map_add, map_mul]

theorem exists_faithfulHermitianJordanEmbedding_of_simple_four_frame
    (hc : ∀ j, P.IsPrimitive (c j)) (hor : ∀ i j, i ≠ j → P.product (c i) (c j) = 0)
    (hunit : ∑ j, c j = P.unit)
    (hinner : ∀ x y z, inner ℝ (P.product x y) z = inner ℝ x (P.product y z))
    (hsimple : P.IsSimpleJordan) (hrs : r < s) (hst : s < t) {u : Fin n} (htu : t < u)
    (hfirst : ∀ j, j ≠ r → j ≠ s → j ≠ t → t < j) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding P d) := by
  let hfr₀ := P.formallyReal_of_associative_inner hinner
  obtain ⟨Q, hQ⟩ := P.exists_associative_peirceTriangleCoordinates_of_simple_four c hc hor hunit hinner
    hsimple (ne_of_lt hrs) (ne_of_lt (lt_trans hrs hst)) (ne_of_lt (lt_trans hrs (lt_trans hst htu)))
    (ne_of_lt hst) (ne_of_lt (lt_trans hst htu)) (ne_of_lt htu)
  have hconn (i j : Fin n) (hij : i < j) : W i j ≠ ⊥ :=
    P.frameOffDiagonal_ne_bot_of_simple c hc hor hunit hinner hsimple i j (ne_of_lt hij)
  obtain ⟨Q', hprod, _, D, hform⟩ := P.exists_peirceIncreasingFrameChart_normalized hfr₀ c Q
    hc hor hunit hrs hst hfirst hconn
  obtain ⟨H⟩ := P.exists_faithfulPeirceHermitianMatrixMap hfr₀ c Q' hc hor hunit hinner hrs hst D hform
  apply P.exists_faithfulHermitianJordanEmbedding_of_peirceAssociative hfr₀ c Q' H
  rw [hprod]
  exact hQ

end AlbertSequential.UnitalJordanProduct
