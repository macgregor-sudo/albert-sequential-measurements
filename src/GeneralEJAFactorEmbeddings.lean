/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HermitianJordanEmbedding
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Finite products of faithfully represented Jordan algebras have faithful
Hermitian embeddings with one diagonal block per factor. -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.UnitalJordanProduct

variable {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Pointwise Jordan product of a family of unital real Jordan algebras. -/
def factorProduct (P : (i : ι) → UnitalJordanProduct (E i)) : UnitalJordanProduct (∀ i, E i) where
  unit i := (P i).unit
  product := LinearMap.mk₂ ℝ (fun x y i => (P i).product (x i) (y i))
    (fun x y z => funext fun i => LinearMap.congr_fun ((P i).product.map_add (x i) (y i)) (z i))
    (fun c x y => funext fun i => LinearMap.congr_fun ((P i).product.map_smul c (x i)) (y i))
    (fun x y z => funext fun i => ((P i).product (x i)).map_add (y i) (z i))
    (fun c x y => funext fun i => ((P i).product (x i)).map_smul c (y i))
  commutative x y := funext fun i => (P i).commutative (x i) (y i)
  unit_left x := funext fun i => (P i).unit_left (x i)
  jordan_identity x y := funext fun i => (P i).jordan_identity (x i) (y i)

@[simp] theorem factorProduct_apply (P : (i : ι) → UnitalJordanProduct (E i))
    (x y : ∀ i, E i) (i : ι) : (factorProduct P).product x y i = (P i).product (x i) (y i) := rfl

@[simp] theorem factorProduct_unit (P : (i : ι) → UnitalJordanProduct (E i)) (i : ι) :
    (factorProduct P).unit i = (P i).unit := rfl

/-- Combine faithful Hermitian matrix representations of a finite family of
Jordan algebras into a single faithful Hermitian matrix representation. -/
theorem exists_faithfulHermitianJordanEmbedding_of_factors [Fintype ι]
    (P : (i : ι) → UnitalJordanProduct (E i))
    (h : ∀ i, ∃ d, Nonempty (FaithfulHermitianJordanEmbedding (P i) d)) :
    ∃ d, Nonempty (FaithfulHermitianJordanEmbedding (factorProduct P) d) := by
  classical
  choose d hd using h
  let embedding (i : ι) := (hd i).some
  let m (x : ∀ i, E i) (i : ι) := (embedding i).map (x i)
  let ι' := Σ i, Fin (d i)
  let e := Matrix.reindexStarAlgEquiv ℝ ℂ (Fintype.equivFin ι')
  let block : ((i : ι) → E i) →ₗ[ℝ] Matrix ι' ι' ℂ :=
    { toFun := fun x => Matrix.blockDiagonal' (m x)
      map_add' := by
        intro x y
        have hm : m (x + y) = m x + m y := funext fun i => (embedding i).map.map_add _ _
        simp only [hm, Matrix.blockDiagonal'_add]
      map_smul' := by
        intro c x
        have hm : m (c • x) = c • m x := funext fun i => (embedding i).map.map_smul c _
        simp only [hm, Matrix.blockDiagonal'_smul, RingHom.id_apply] }
  refine ⟨Fintype.card ι', ⟨{
    map := e.toAlgEquiv.toLinearMap.comp block
    injective := ?_
    hermitian := ?_
    unit := ?_
    jordan := ?_ }⟩⟩
  · intro x y hxy
    have hblock : block x = block y := e.toAlgEquiv.injective hxy
    funext i
    apply (embedding i).injective
    ext a b
    have hb : Matrix.blockDiagonal' (m x) ⟨i, a⟩ ⟨i, b⟩ =
        Matrix.blockDiagonal' (m y) ⟨i, a⟩ ⟨i, b⟩ := congrArg (fun M => M ⟨i, a⟩ ⟨i, b⟩) hblock
    simpa using hb
  · intro x
    change star (e (Matrix.blockDiagonal' (m x))) = e (Matrix.blockDiagonal' (m x))
    rw [← map_star]
    congr 1
    change (Matrix.blockDiagonal' (m x)).conjTranspose = _
    rw [Matrix.blockDiagonal'_conjTranspose]
    congr 1
    funext i
    exact (embedding i).hermitian (x i)
  · have hone : m (factorProduct P).unit = 1 := funext fun i => (embedding i).unit
    change e (Matrix.blockDiagonal' (m (factorProduct P).unit)) = 1
    rw [hone, Matrix.blockDiagonal'_one, map_one]
  · intro x y
    have hprod : m ((factorProduct P).product x y) =
        (1 / 2 : ℝ) • ((fun i => m x i * m y i) + fun i => m y i * m x i) :=
      funext fun i => (embedding i).jordan (x i) (y i)
    change e (Matrix.blockDiagonal' (m ((factorProduct P).product x y))) =
      (1 / 2 : ℝ) • (e (Matrix.blockDiagonal' (m x)) * e (Matrix.blockDiagonal' (m y)) +
        e (Matrix.blockDiagonal' (m y)) * e (Matrix.blockDiagonal' (m x)))
    rw [hprod, Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_add,
      Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_mul]
    simp only [map_smul, map_add, map_mul]

end AlbertSequential.UnitalJordanProduct
