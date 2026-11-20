/- SPDX-License-Identifier: Apache-2.0 -/
module

public import QutritMutuallyUnbiasedBases
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Ring

/-! Double-pair traces and the real parts of the four-vector Bargmann cycles. -/

@[expose] public section
noncomputable section

namespace AlbertSequential.Bargmann

open Matrix
open scoped ComplexOrder

private theorem projection_eq_vecMulVec (u : Fin 3 → ℂ) :
    qutritRankOneProjection u = vecMulVec u (star u) := rfl

private theorem inner_eq_dotProduct (u v : Fin 3 → ℂ) : qutritInner u v = star u ⬝ᵥ v := rfl

/-- The Bargmann cycle with its indicated four-vector order. -/
def cycle (a b c d : Fin 3 → ℂ) : ℂ :=
  qutritInner a b * qutritInner b c * qutritInner c d * qutritInner d a

/-- The real trace pairing of the two symmetrized matrix products. -/
def doublePairTrace (A B C D : ComplexMatrix3) : ℝ :=
  (trace (((1 / 2 : ℝ) • (A * B + B * A)) *
    ((1 / 2 : ℝ) • (C * D + D * C)))).re

private theorem mul_dyad (u v w : Fin 3 → ℂ) :
    vecMulVec u (star v) * qutritRankOneProjection w =
      qutritInner v w • vecMulVec u (star w) := by
  rw [projection_eq_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_smul, inner_eq_dotProduct]

private theorem dyad_mulVec (u v : Fin 3 → ℂ) :
    qutritRankOneProjection u *ᵥ v = qutritInner u v • u := by
  rw [projection_eq_vecMulVec, vecMulVec_mulVec]
  funext i
  exact mul_comm (u i) (qutritInner u v)

/-- A unit column gives a Hermitian idempotent of matrix rank one. -/
theorem dyad_isRankOneProjection (u : Fin 3 → ℂ) (hu : qutritInner u u = 1) :
    (qutritRankOneProjection u).IsHermitian ∧
    qutritRankOneProjection u * qutritRankOneProjection u = qutritRankOneProjection u ∧
    (qutritRankOneProjection u).rank = 1 := by
  refine ⟨(qutritRankOneProjection_positive u).isHermitian,
    qutritRankOneProjection_idempotent u hu, ?_⟩
  have hne : u ≠ 0 := by
    intro h
    subst u
    simp [qutritInner] at hu
  have hrange : LinearMap.range (qutritRankOneProjection u).mulVecLin = Submodule.span ℂ {u} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [mulVecLin_apply, dyad_mulVec]
      exact (Submodule.span ℂ {u}).smul_mem _ (Submodule.subset_span (Set.mem_singleton u))
    · rw [Submodule.span_le]
      intro v hv
      have huv : v = u := hv
      subst v
      refine ⟨u, ?_⟩
      rw [mulVecLin_apply, dyad_mulVec, hu, one_smul]
  rw [Matrix.rank, hrange, finrank_span_singleton hne]

/-- The ordered complex trace of four dyads is precisely the Bargmann cycle. -/
theorem trace_dyad_cycle (a b c d : Fin 3 → ℂ) :
    trace (qutritRankOneProjection a * qutritRankOneProjection b *
      qutritRankOneProjection c * qutritRankOneProjection d) = cycle a b c d := by
  rw [projection_eq_vecMulVec a]
  simp only [mul_dyad, smul_mul_assoc, trace_smul, trace_vecMulVec, smul_eq_mul,
    cycle, inner_eq_dotProduct]
  rw [dotProduct_comm a (star d)]
  ring

private theorem cycle_rotate (a b c d : Fin 3 → ℂ) :
    cycle b c d a = cycle a b c d := by
  unfold cycle
  ring

private theorem cycle_reverse_re (a b c d : Fin 3 → ℂ) :
    (cycle a d c b).re = (cycle a b c d).re := by
  have h : cycle a d c b = star (cycle a b c d) := by
    unfold cycle
    simp only [star_mul, qutritInner_star]
    ring
  rw [h, Complex.star_def, Complex.conj_re]

/-- A double-pair trace is the average of the real parts of its two four-cycles. -/
theorem doublePairTrace_dyads (a b c d : Fin 3 → ℂ) :
    doublePairTrace (qutritRankOneProjection a) (qutritRankOneProjection b)
      (qutritRankOneProjection c) (qutritRankOneProjection d) =
      ((cycle a b c d).re + (cycle a b d c).re) / 2 := by
  unfold doublePairTrace
  rw [smul_mul_smul, add_mul, mul_add, mul_add]
  simp only [trace_smul, trace_add, Complex.smul_re, smul_eq_mul, Complex.add_re,
    ← mul_assoc, trace_dyad_cycle]
  rw [← cycle_rotate b a c d, ← cycle_rotate b a d c, cycle_reverse_re a b c d,
    cycle_reverse_re a b d c]
  ring

/-- Each signed combination of the three double-pair traces recovers one real cycle. -/
theorem omega_dyads (a b c d : Fin 3 → ℂ) :
    let A := qutritRankOneProjection a
    let B := qutritRankOneProjection b
    let C := qutritRankOneProjection c
    let D := qutritRankOneProjection d
    let t₁ := doublePairTrace A B C D
    let t₂ := doublePairTrace A C B D
    let t₃ := doublePairTrace A D B C
    t₂ + t₃ - t₁ = (cycle a c b d).re ∧
    t₁ + t₃ - t₂ = (cycle a b c d).re ∧
    t₁ + t₂ - t₃ = (cycle a b d c).re := by
  dsimp only
  simp only [doublePairTrace_dyads, cycle_reverse_re a b d c,
    cycle_reverse_re a c b d, cycle_reverse_re a b c d]
  constructor
  · ring
  constructor <;> ring

end AlbertSequential.Bargmann
