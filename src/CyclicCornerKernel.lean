/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CyclicWordVectors
public import CornerHolonomyDefects
public import TracialCornerKernel

@[expose] public section
noncomputable section

open scoped InnerProductSpace

namespace AlbertSequential

open CornerHolonomy

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

local instance cyclicCornerKernelSourceAlgebra : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

variable (M : AlgebraicProjectiveData (Fin 4) A)

abbrev CyclicBoundedOperator := CyclicHilbert M →L[ℝ] CyclicHilbert M

/-- Membership in the actual bounded image of the generated word algebra. -/
def InCyclicOperatorAlgebra (T : CyclicBoundedOperator M) : Prop :=
  T ∈ Set.range (cyclicHilbertRepresentation M)

/-- The supported corner of the actual bounded algebra at affirmative A. -/
def InCyclicAnchorCorner (T : CyclicBoundedOperator M) : Prop :=
  InCyclicOperatorAlgebra M T ∧ CornerSupported (cyclicHilbertProjection M 0) T

def CyclicAnchorOrbit : Set (CyclicHilbert M) :=
  {v | ∃ T : CyclicBoundedOperator M, InCyclicAnchorCorner M T ∧
    T (cyclicHilbertProjection M 0 (cyclicHilbertVector M)) = v}

def CyclicWordStateFaithful : Prop :=
  ∀ T : CyclicBoundedOperator M, InCyclicOperatorAlgebra M T →
    ⟪cyclicHilbertVector M, (star T * T) (cyclicHilbertVector M)⟫_ℝ = 0 → T = 0

def CyclicAnchorStateTracial : Prop :=
  ∀ T S : CyclicBoundedOperator M, InCyclicAnchorCorner M T → InCyclicAnchorCorner M S →
    let ξ := cyclicHilbertProjection M 0 (cyclicHilbertVector M)
    ⟪ξ, (T * S) ξ⟫_ℝ = ⟪ξ, (S * T) ξ⟫_ℝ

local notation "J" => cyclicHilbertProjection M 0
local notation "Ω" => cyclicHilbertVector M
local notation "ξ" => J Ω

theorem cyclicProjection_in_operatorAlgebra (i : Fin 4) :
    InCyclicOperatorAlgebra M (cyclicHilbertProjection M i) :=
  ⟨cyclicGenerator M i, rfl⟩

theorem inCyclicOperatorAlgebra_mul {T S : CyclicBoundedOperator M}
    (hT : InCyclicOperatorAlgebra M T) (hS : InCyclicOperatorAlgebra M S) :
    InCyclicOperatorAlgebra M (T * S) := by
  rcases hT with ⟨t, rfl⟩
  rcases hS with ⟨s, rfl⟩
  exact ⟨t * s, map_mul _ _ _⟩

theorem inCyclicOperatorAlgebra_star {T : CyclicBoundedOperator M}
    (hT : InCyclicOperatorAlgebra M T) : InCyclicOperatorAlgebra M (star T) := by
  rcases hT with ⟨t, rfl⟩
  exact ⟨star t, map_star _ _⟩

theorem inCyclicOperatorAlgebra_add {T S : CyclicBoundedOperator M}
    (hT : InCyclicOperatorAlgebra M T) (hS : InCyclicOperatorAlgebra M S) :
    InCyclicOperatorAlgebra M (T + S) := by
  rcases hT with ⟨t, rfl⟩
  rcases hS with ⟨s, rfl⟩
  exact ⟨t + s, map_add _ _ _⟩

theorem inCyclicOperatorAlgebra_sub {T S : CyclicBoundedOperator M}
    (hT : InCyclicOperatorAlgebra M T) (hS : InCyclicOperatorAlgebra M S) :
    InCyclicOperatorAlgebra M (T - S) := by
  rcases hT with ⟨t, rfl⟩
  rcases hS with ⟨s, rfl⟩
  exact ⟨t - s, map_sub _ _ _⟩

theorem inCyclicOperatorAlgebra_smul {T : CyclicBoundedOperator M}
    (hT : InCyclicOperatorAlgebra M T) (r : ℝ) : InCyclicOperatorAlgebra M (r • T) := by
  rcases hT with ⟨t, rfl⟩
  exact ⟨r • t, map_smul _ _ _⟩

theorem cyclicAnchor_in_ownCorner : InCyclicAnchorCorner M J :=
  ⟨cyclicProjection_in_operatorAlgebra M 0, (cyclicHilbertProjection_isStarProjection M 0).isIdempotentElem.eq,
    (cyclicHilbertProjection_isStarProjection M 0).isIdempotentElem.eq⟩

theorem inCyclicAnchorCorner_mul {T S : CyclicBoundedOperator M}
    (hT : InCyclicAnchorCorner M T) (hS : InCyclicAnchorCorner M S) :
    InCyclicAnchorCorner M (T * S) :=
  ⟨inCyclicOperatorAlgebra_mul M hT.1 hS.1, supported_mul J T S hT.2 hS.2⟩

theorem inCyclicAnchorCorner_star {T : CyclicBoundedOperator M}
    (hT : InCyclicAnchorCorner M T) : InCyclicAnchorCorner M (star T) :=
  ⟨inCyclicOperatorAlgebra_star M hT.1, supported_star J T
    (cyclicHilbertProjection_isStarProjection M 0).isSelfAdjoint.star_eq hT.2⟩

theorem inCyclicAnchorCorner_add {T S : CyclicBoundedOperator M}
    (hT : InCyclicAnchorCorner M T) (hS : InCyclicAnchorCorner M S) :
    InCyclicAnchorCorner M (T + S) :=
  ⟨inCyclicOperatorAlgebra_add M hT.1 hS.1, supported_add J T S hT.2 hS.2⟩

theorem inCyclicAnchorCorner_sub {T S : CyclicBoundedOperator M}
    (hT : InCyclicAnchorCorner M T) (hS : InCyclicAnchorCorner M S) :
    InCyclicAnchorCorner M (T - S) :=
  ⟨inCyclicOperatorAlgebra_sub M hT.1 hS.1, supported_sub J T S hT.2 hS.2⟩

theorem inCyclicAnchorCorner_smul {T : CyclicBoundedOperator M}
    (hT : InCyclicAnchorCorner M T) (r : ℝ) : InCyclicAnchorCorner M (r • T) :=
  ⟨inCyclicOperatorAlgebra_smul M hT.1 r, supported_smul J T hT.2 r⟩

theorem inCyclicAnchorCorner_iff_compression (T : CyclicBoundedOperator M) :
    InCyclicAnchorCorner M T ↔ ∃ S : CyclicBoundedOperator M, InCyclicOperatorAlgebra M S ∧ T = J * S * J := by
  constructor
  · intro h
    exact ⟨T, h.1, (by rw [h.2.1, h.2.2])⟩
  · rintro ⟨S, hS, rfl⟩
    have hJ := (cyclicAnchor_in_ownCorner M)
    exact ⟨inCyclicOperatorAlgebra_mul M (inCyclicOperatorAlgebra_mul M hJ.1 hS) hJ.1,
      ⟨by rw [← mul_assoc J, ← mul_assoc J, hJ.2.1], by rw [mul_assoc, hJ.2.1]⟩⟩

def cyclicAnchorOrbitSubmodule : Submodule ℝ (CyclicHilbert M) where
  carrier := CyclicAnchorOrbit M
  zero_mem' := by
    refine ⟨0, ⟨⟨0, map_zero _⟩, by simp [CornerSupported]⟩, rfl⟩
  add_mem' := by
    rintro _ _ ⟨T, hT, rfl⟩ ⟨S, hS, rfl⟩
    exact ⟨T + S, inCyclicAnchorCorner_add M hT hS, rfl⟩
  smul_mem' := by
    rintro r _ ⟨T, hT, rfl⟩
    exact ⟨r • T, inCyclicAnchorCorner_smul M hT r, rfl⟩

theorem cyclicAnchor_closed_orbit_invariant (T : CyclicBoundedOperator M) (hT : InCyclicAnchorCorner M T)
    (v : CyclicHilbert M) (hv : v ∈ closure (CyclicAnchorOrbit M)) :
    T v ∈ closure (CyclicAnchorOrbit M) := by
  have hc : IsClosed (T ⁻¹' closure (CyclicAnchorOrbit M)) := isClosed_closure.preimage T.continuous
  have hi : CyclicAnchorOrbit M ⊆ T ⁻¹' closure (CyclicAnchorOrbit M) := by
    rintro _ ⟨S, hS, rfl⟩
    exact subset_closure ⟨T * S, inCyclicAnchorCorner_mul M hT hS, rfl⟩
  exact closure_minimal hi hc hv

theorem cyclicAnchor_closed_orbit_fixed (v : CyclicHilbert M) (hv : v ∈ closure (CyclicAnchorOrbit M)) :
    J v = v := by
  let K := (J - 1 : CyclicBoundedOperator M)
  have hi : CyclicAnchorOrbit M ⊆ (LinearMap.ker K.toLinearMap : Set (CyclicHilbert M)) := by
    rintro _ ⟨S, hS, rfl⟩
    change J (S ξ) - S ξ = 0
    exact sub_eq_zero.mpr (congrArg (fun T : CyclicBoundedOperator M => T ξ) hS.2.1)
  have h := closure_minimal hi K.isClosed_ker hv
  change J v - v = 0 at h
  exact sub_eq_zero.mp h

theorem cyclicAnchorStateTracial_of_source_trace
    (h : ∀ x y : A, M.state (x * y) = M.state (y * x)) : CyclicAnchorStateTracial M := by
  have hJ : star J = J := (cyclicHilbertProjection_isStarProjection M 0).isSelfAdjoint.star_eq
  have anchor_shift (T : CyclicBoundedOperator M) (hT : InCyclicAnchorCorner M T) :
      ⟪ξ, T ξ⟫_ℝ = ⟪Ω, T Ω⟫_ℝ := by
    calc
      _ = ⟪Ω, (star J * T * J) Ω⟫_ℝ := (ContinuousLinearMap.adjoint_inner_right J Ω (T ξ)).symm
      _ = _ := by rw [hJ, hT.2.1, hT.2.2]
  intro T S hT hS
  dsimp only
  rw [anchor_shift _ (inCyclicAnchorCorner_mul M hT hS),
      anchor_shift _ (inCyclicAnchorCorner_mul M hS hT)]
  obtain ⟨t, rfl⟩ := hT.1
  obtain ⟨s, rfl⟩ := hS.1
  rw [← map_mul, ← map_mul, cyclicHilbert_vector_state, cyclicHilbert_vector_state]
  exact h t s

theorem cyclicAnchor_null_of_faithful (h : CyclicWordStateFaithful M)
    (T : CyclicBoundedOperator M) (hT : InCyclicAnchorCorner M T)
    (hz : T ξ = 0) : T = 0 := by
  have hv : T Ω = 0 := (congrArg (fun S : CyclicBoundedOperator M => S Ω) hT.2.2).symm.trans hz
  exact faithfulCorner_annihilator_zero Ω {S | InCyclicOperatorAlgebra M S}
    (fun S hS hnull => h S hS hnull) hT.1 hv

private theorem cyclicAnchor_null_on_closed_orbit_of_tracial (h : CyclicAnchorStateTracial M)
    (T : CyclicBoundedOperator M) (hT : InCyclicAnchorCorner M T) (hz : T ξ = 0)
    (v : CyclicHilbert M) (hv : v ∈ closure (CyclicAnchorOrbit M)) : T v = 0 := by
  have hzero := tracialCorner_annihilates_orbitClosure ξ {S | InCyclicAnchorCorner M S}
    (fun S hS => inCyclicAnchorCorner_star M hS) (fun S hS R hR => inCyclicAnchorCorner_mul M hS hR)
    (fun S hS R hR => h S R hS hR) hT hz
  apply hzero
  change v ∈ closure ((Submodule.span ℝ (CyclicAnchorOrbit M)) : Set (CyclicHilbert M))
  exact closure_mono Submodule.subset_span hv

/-- Trace makes the left kernel at ξ stable under right multiplication in the corner. -/
theorem cyclicAnchor_null_right_of_tracial (h : CyclicAnchorStateTracial M)
    (T S : CyclicBoundedOperator M) (hT : InCyclicAnchorCorner M T)
    (hS : InCyclicAnchorCorner M S) (hz : T ξ = 0) : T (S ξ) = 0 :=
  cyclicAnchor_null_on_closed_orbit_of_tracial M h T hT hz (S ξ) (subset_closure ⟨S, hS, rfl⟩)

/-- Either state hypothesis extends nullity to the closed orbit of the actual corner. -/
theorem cyclicAnchor_null_on_closed_orbit (h : CyclicWordStateFaithful M ∨ CyclicAnchorStateTracial M)
    (T : CyclicBoundedOperator M) (hT : InCyclicAnchorCorner M T) (hz : T ξ = 0)
    (v : CyclicHilbert M) (hv : v ∈ closure (CyclicAnchorOrbit M)) : T v = 0 := by
  rcases h with hf | ht
  · rw [cyclicAnchor_null_of_faithful M hf T hT hz]
    rfl
  · exact cyclicAnchor_null_on_closed_orbit_of_tracial M ht T hT hz v hv

end AlbertSequential
