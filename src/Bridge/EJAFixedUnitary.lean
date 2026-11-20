/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FixedUnitaryMatrix
public import GeneralEJAWordTransport

@[expose] public section
noncomputable section
namespace AlbertSequential.UnitalJordanProduct
open Matrix
open scoped ComplexOrder
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] (P : UnitalJordanProduct E)

private theorem complement_square {q : E} (hq : P.product q q = q) :
    P.product (P.unit-q) (P.unit-q) = P.unit-q := by
  have hu : P.product q P.unit = q := (P.commutative _ _).trans (P.unit_left q)
  simp only [map_sub,LinearMap.sub_apply,P.unit_left,hu,hq]; abel

private theorem opposite_quadratic {q : E} (hq : P.product q q = q) (x : E) :
    P.quadraticRepresentation (P.unit-q) (P.quadraticRepresentation q x) = 0 := by
  let y := P.quadraticRepresentation q x
  have hy : P.product q y = y := (P.mem_peirceOne q y).mp (P.quadraticRepresentation_mem_peirceOne q x hq)
  have hc : P.product (P.unit-q) y = 0 := by rw [map_sub,LinearMap.sub_apply,P.unit_left,hy,sub_self]
  change P.quadraticRepresentation (P.unit-q) y = 0
  rw [P.quadraticRepresentation_apply,P.complement_square hq,hc,map_zero,smul_zero,sub_zero]

theorem sequentialBranchState_opposite (p : ι → E) (hp : ∀ i, P.product (p i) (p i) = p i)
    (s : E) (w : Word ι) (i : ι) (b : Bool) :
    P.sequentialBranchState p s (w++[(i,b),(i,!b)]) = 0 := by
  unfold sequentialBranchState
  rw [List.foldl_append]
  cases b
  · change P.quadraticRepresentation (p i) (P.quadraticRepresentation (P.unit-p i) _) = 0
    simpa only [sub_sub_cancel,sequentialBranchState] using P.opposite_quadratic (P.complement_square (hp i)) (P.sequentialBranchState p s w)
  · exact P.opposite_quadratic (hp i) _

/-- The native chronological table of any real Jordan system has no opposite
repeats. A finite-dimensional complex matrix model with a pre-test unitary
therefore has a projective representation in the same dimension. -/
theorem exists_projective_of_interleaved {n d : ℕ} (p : Fin n → E)
    (hp : ∀ i, P.product (p i) (p i) = p i) (s : E) (tr : E →ₗ[ℝ] ℝ)
    (Y : unitary (Matrix (Fin d) (Fin d) ℂ)) (Q : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hQ : ∀ i, (Q i).IsHermitian) (hQQ : ∀ i, Q i * Q i = Q i)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hm : ∀ w, ((FixedUnitary.interleaved Y Q w * ρ) * (FixedUnitary.interleaved Y Q w)ᴴ).trace =
      (tr (P.sequentialBranchState p s w) : ℂ)) :
    ∃ M : AlbertChallenge.ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)),
      ∀ w, M.probability w = tr (P.sequentialBranchState p s w) :=
  FixedUnitary.exists_projective_of_fixedUnitary_noSwitch Y Q hQ hQQ ρ hρ htr _
    (fun w i b => by rw [P.sequentialBranchState_opposite p hp s w i b,map_zero]) hm

end AlbertSequential.UnitalJordanProduct
