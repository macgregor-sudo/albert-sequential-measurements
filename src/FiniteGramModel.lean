/- SPDX-License-Identifier: Apache-2.0
   Mathematical source: core lem:cer:recon. -/
module

public import Interfaces.WordsAndCertificates
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual real vector-state projection data; no matching assertion is a field.
The source table is matched only on its explicitly complete finite word set. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

structure RealVectorProjectiveData (ι E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  projection : ι → E →ₗ[ℝ] E
  idempotent : ∀ i x, projection i (projection i x) = projection i x
  symmetric : ∀ i x y, inner ℝ (projection i x) y = inner ℝ x (projection i y)
  initial : E
  normalized : inner ℝ initial initial = 1

namespace RealVectorProjectiveData

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def outcome (M : RealVectorProjectiveData ι E) (a : Outcome ι) : E →ₗ[ℝ] E :=
  if a.2 then M.projection a.1 else LinearMap.id - M.projection a.1

def branchVector (M : RealVectorProjectiveData ι E) (w : Word ι) : E :=
  w.foldl (fun x a => M.outcome a x) M.initial

def probability (M : RealVectorProjectiveData ι E) (w : Word ι) : ℝ :=
  inner ℝ (M.branchVector w) (M.branchVector w)

@[simp] theorem branchVector_nil (M : RealVectorProjectiveData ι E) :
    M.branchVector [] = M.initial := rfl

theorem branchVector_append_singleton (M : RealVectorProjectiveData ι E)
    (w : Word ι) (a : Outcome ι) :
    M.branchVector (w ++ [a]) = M.outcome a (M.branchVector w) := by
  simp only [branchVector, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem probability_nil (M : RealVectorProjectiveData ι E) :
    M.probability [] = 1 := M.normalized

end RealVectorProjectiveData

abbrev FiniteRealVectorProjectiveModel (n d : ℕ) :=
  RealVectorProjectiveData (Fin n) (EuclideanSpace ℝ (Fin d))

end AlbertSequential
