/- SPDX-License-Identifier: Apache-2.0 -/
module

public import CyclicCornerKernel
public import CyclicCornerSevenResiduals
public import FiniteVectorTetrahedron
public import PaperResidualVectors
public import LengthSeven.TableValues

@[expose] public section
noncomputable section

namespace AlbertSequential

open CornerHolonomy CornerResidualBuilder NativeAnalysis

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

local instance cyclicCornerSevenObstructionSourceAlgebra : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

variable (M : AlgebraicProjectiveData (Fin 4) A)

local notation "J" => cyclicHilbertProjection M 0
local notation "Ω" => cyclicHilbertVector M
local notation "ξ" => J Ω
local notation "V" => closure (CyclicAnchorOrbit M)

private theorem normalizedHolonomies_in_cyclicCorner (d : CornerNumericalData) (i : Fin 3) :
    let P := cyclicHilbertProjection M
    InCyclicAnchorCorner M (normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2 i) := by
  let P := cyclicHilbertProjection M
  have hj := (cyclicHilbertProjection_isStarProjection M 0).isIdempotentElem.eq
  refine ⟨?_, normalizedCyclicHolonomies_supported (P 0) (P 1) (P 2) (P 3) hj d.ν0 d.ν1 d.ν2 i⟩
  fin_cases i <;> apply inCyclicOperatorAlgebra_smul M <;>
    repeat' apply inCyclicOperatorAlgebra_mul M
  all_goals exact cyclicProjection_in_operatorAlgebra M _

private theorem cyclicCorner_hermitianPart {T : CyclicBoundedOperator M}
    (hT : InCyclicAnchorCorner M T) : InCyclicAnchorCorner M (hermitianPart T) :=
  inCyclicAnchorCorner_smul M
    (inCyclicAnchorCorner_add M hT (inCyclicAnchorCorner_star M hT)) (1 / 2)

private theorem cyclicCorner_pairProductDefect {T S : CyclicBoundedOperator M}
    (hT : InCyclicAnchorCorner M T) (hS : InCyclicAnchorCorner M S) (K : ℝ) :
    InCyclicAnchorCorner M (pairProductDefect J T S K) := by
  unfold pairProductDefect
  rw [← star_mul]
  exact inCyclicAnchorCorner_sub M (cyclicCorner_hermitianPart M (inCyclicAnchorCorner_mul M hT hS))
    (inCyclicAnchorCorner_smul M (cyclicAnchor_in_ownCorner M) K)

private theorem cyclicDegreeSpan_subset_closed_orbit (h : Fin 3 → CyclicBoundedOperator M)
    (hh : ∀ i, InCyclicAnchorCorner M (h i)) (d : ℕ) :
    (holonomyDegreeSpan h ξ d : Set (CyclicHilbert M)) ⊆ V := by
  have hspan : holonomyDegreeSpan h ξ d ≤ cyclicAnchorOrbitSubmodule M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    clear hw
    induction w with
    | nil =>
      exact ⟨J, cyclicAnchor_in_ownCorner M,
        congrArg (fun T : CyclicBoundedOperator M => T Ω) (cyclicAnchor_in_ownCorner M).2.1⟩
    | cons a w ih =>
      rcases ih with ⟨T, hT, hval⟩
      have ha : InCyclicAnchorCorner M (signedHolonomy h a) := by
        rcases a with ⟨i, b⟩
        cases b
        · exact inCyclicAnchorCorner_star M (hh i)
        · exact hh i
      refine ⟨signedHolonomy h a * T, inCyclicAnchorCorner_mul M ha hT, ?_⟩
      exact congrArg (signedHolonomy h a) hval
  exact fun _ hv => subset_closure (hspan hv)

attribute [local irreducible] fourPointInvariant

theorem cyclic_seven_corner_defects_on_closed_orbit (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (ρ : Albert) (hm : CyclicAnchoredSevenMatch M p ρ)
    (hstate : CyclicWordStateFaithful M ∨ CyclicAnchorStateTracial M)
    (v : CyclicHilbert M) (hv : v ∈ V) :
    let P := cyclicHilbertProjection M
    let d := BlockB.atomCornerData p
    let h := normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2
    (∀ i, hermitianDefect J (h i) (d.hermitianConstants i) v = 0 ∧
      leftUnitarityDefect J (h i) v = 0 ∧ rightUnitarityDefect J (h i) v = 0) ∧
    (∀ i, pairProductDefect J (h i) (h (nextHolonomy i)) (mixedConstant d i) v = 0) ∧
    cornerCubicDefect J h d.cubicConstant v = 0 := by
  let P := cyclicHilbertProjection M
  let d := BlockB.atomCornerData p
  let h := normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2
  have hh (i : Fin 3) : InCyclicAnchorCorner M (h i) := normalizedHolonomies_in_cyclicCorner M d i
  have hJ := cyclicAnchor_in_ownCorner M
  obtain ⟨hfirst, hmixed, hcubic⟩ := cyclic_seven_corner_defects M p hp hA ρ hm
  have lift (T : CyclicBoundedOperator M) (hT : InCyclicAnchorCorner M T) (hz : T ξ = 0) :
      T v = 0 := cyclicAnchor_null_on_closed_orbit M hstate T hT hz v hv
  refine ⟨fun i => ⟨?_, ?_, ?_⟩, fun i => ?_, ?_⟩
  · exact lift _ (inCyclicAnchorCorner_sub M (cyclicCorner_hermitianPart M (hh i))
      (inCyclicAnchorCorner_smul M hJ _)) (hfirst i).1
  · exact lift _ (inCyclicAnchorCorner_sub M
      (inCyclicAnchorCorner_mul M (inCyclicAnchorCorner_star M (hh i)) (hh i)) hJ) (hfirst i).2.1
  · exact lift _ (inCyclicAnchorCorner_sub M
      (inCyclicAnchorCorner_mul M (hh i) (inCyclicAnchorCorner_star M (hh i))) hJ) (hfirst i).2.2
  · exact lift _ (cyclicCorner_pairProductDefect M (hh i) (hh (nextHolonomy i)) _) (hmixed i)
  · have hTriple := inCyclicAnchorCorner_mul M (inCyclicAnchorCorner_mul M (hh 0) (hh 1)) (hh 2)
    exact lift _ (inCyclicAnchorCorner_sub M (cyclicCorner_hermitianPart M hTriple)
      (inCyclicAnchorCorner_smul M hJ _)) hcubic

/-- The corner-tracial or faithful argument uses only the anchored seven-letter
probabilities. It yields the discriminant identity without dividing by the preparation mass. -/
theorem cyclic_anchoredSeven_corner_discriminant (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (ρ : Albert) (hm : CyclicAnchoredSevenMatch M p ρ)
    (hstate : CyclicWordStateFaithful M ∨ CyclicAnchorStateTracial M) :
    (BlockB.atomCornerData p).scalarParameters.discriminant * ‖ξ‖ ^ 2 = 0 := by
  let P := cyclicHilbertProjection M
  let d := BlockB.atomCornerData p
  let h := normalizedCyclicHolonomies (P 0) (P 1) (P 2) (P 3) d.ν0 d.ν1 d.ν2
  let c := d.hermitianConstants
  let N := fun i => skewHermitianPart (h i)
  have hh (i : Fin 3) : InCyclicAnchorCorner M (h i) := normalizedHolonomies_in_cyclicCorner M d i
  have hJ := cyclicAnchor_in_ownCorner M
  have hi : J * J = J := hJ.2.1
  have hj : star J = J := (cyclicHilbertProjection_isStarProjection M 0).isSelfAdjoint.star_eq
  have hcubic := (cyclic_seven_corner_defects M p hp hA ρ hm).2.2
  have hclosed (v : CyclicHilbert M) (hv : v ∈ V) :=
    cyclic_seven_corner_defects_on_closed_orbit M p hp hA ρ hm hstate v hv
  have hHerm (i : Fin 3) (v : CyclicHilbert M) (hv : v ∈ V) :
      hermitianDefect J (h i) (c i) v = 0 := ((hclosed v hv).1 i).1
  have hLeft (i : Fin 3) (v : CyclicHilbert M) (hv : v ∈ V) :
      leftUnitarityDefect J (h i) v = 0 := ((hclosed v hv).1 i).2.1
  have hRight (i : Fin 3) (v : CyclicHilbert M) (hv : v ∈ V) :
      rightUnitarityDefect J (h i) v = 0 := ((hclosed v hv).1 i).2.2
  have hMix (i : Fin 3) (v : CyclicHilbert M) (hv : v ∈ V) :
      pairProductDefect J (h i) (h (nextHolonomy i)) (mixedConstant d i) v = 0 := (hclosed v hv).2.1 i
  have hCycle (i : Fin 3) (v : CyclicHilbert M) (hv : v ∈ V) :
      (N i * N (nextHolonomy i) + N (nextHolonomy i) * N i) v =
        (-2 * d.scalarParameters.gramMatrix i (nextHolonomy i)) • v := by
    let j := nextHolonomy i
    have hk := hHerm i _ (cyclicAnchor_closed_orbit_invariant M (h j) (hh j) v hv)
    have hs := hHerm j _ (cyclicAnchor_closed_orbit_invariant M (star (h i))
      (inCyclicAnchorCorner_star M (hh i)) v hv)
    have hmixed : pairProductDefect J (h i) (h j) (mixedConstant d i) v = 0 := hMix i v hv
    have hz : pairCliffordDefect J (h i) (h j) (c i) (c j) (mixedConstant d i) v = 0 := by
      rw [pairDefect_reduction J (h i) (h j) hi hj (hh i).2 (hh j).2]
      simp only [sub_apply, smul_apply, add_apply, mul_apply_eq_comp, hmixed,
        hk, hs, hHerm i v hv, hHerm j v hv, map_zero, smul_zero, add_zero, sub_zero]
    change (N i * N j + N j * N i) v +
      (2 * (c i * c j - mixedConstant d i)) • J v = 0 at hz
    rw [cyclicAnchor_closed_orbit_fixed M v hv, ← gramMatrix_cycle d i] at hz
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg, neg_smul, neg_mul, neg_neg] using hz
  have hPair (i j : Fin 3) (hij : i ≠ j) (v : CyclicHilbert M) (hv : v ∈ V) :
      (N i * N j + N j * N i) v = (-2 * d.scalarParameters.gramMatrix i j) • v := by
    have horder : j = nextHolonomy i ∨ i = nextHolonomy j := by
      fin_cases i <;> fin_cases j <;> first | contradiction | decide
    rcases horder with rfl | rfl
    · exact hCycle i v hv
    · simpa only [add_comm (N j * N (nextHolonomy j)),
        CliffordScalarParameters.gramMatrix_symmetric d.scalarParameters j (nextHolonomy j)] using hCycle j v hv
  have hC : hermitianPart (h 0 * h 1 * h 2) ξ = d.cubicConstant • ξ := by
    change hermitianPart (h 0 * h 1 * h 2) ξ - d.cubicConstant • J ξ = 0 at hcubic
    rw [show J ξ = ξ from congrArg (fun T : CyclicBoundedOperator M => T Ω) hi] at hcubic
    exact sub_eq_zero.mp hcubic
  have hdegree (n : ℕ) (v : CyclicHilbert M) (hv : v ∈ holonomyDegreeSpan h ξ n) : v ∈ V :=
    cyclicDegreeSpan_subset_closed_orbit M h hh n hv
  have hH (i : Fin 3) (v : CyclicHilbert M) (hv : v ∈ holonomyDegreeSpan h ξ 2) :
      hermitianPart (h i) v = c i • v := by
    have hm := hHerm i v (hdegree 2 v hv)
    change hermitianPart (h i) v - c i • J v = 0 at hm
    rw [cyclicAnchor_closed_orbit_fixed M v (hdegree 2 v hv)] at hm
    exact sub_eq_zero.mp hm
  have hU (i : Fin 3) (v : CyclicHilbert M) (hv : v ∈ holonomyDegreeSpan h ξ 2) :
      (star (h i) * h i) v = v ∧ (h i * star (h i)) v = v := by
    have hl := hLeft i v (hdegree 2 v hv)
    have hr := hRight i v (hdegree 2 v hv)
    change (star (h i) * h i) v - J v = 0 at hl
    change (h i * star (h i)) v - J v = 0 at hr
    rw [cyclicAnchor_closed_orbit_fixed M v (hdegree 2 v hv)] at hl hr
    exact ⟨sub_eq_zero.mp hl, sub_eq_zero.mp hr⟩
  have hd := finiteVectorTetrahedron_of_corner J h hi hj (fun i => (hh i).2) c
    d.mixed12 d.mixed13 d.mixed23 d.cubicConstant Ω hH hU
    (fun i j hij v hv => hPair i j hij v (hdegree 1 v hv)) hC
  rw [CliffordScalarParameters.discriminant_eq_det]
  exact hd.2.2

/-- The core Remark 6.14 exclusion obtained from the two-sided corner kernel. -/
theorem cyclic_anchoredSeven_e3_not_match_of_faithful_or_tracial (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (hA : 0 < fourPointInvariant p)
    (hstate : CyclicWordStateFaithful M ∨ CyclicAnchorStateTracial M) :
    ¬ CyclicAnchoredSevenMatch M p ((1 / 3 : ℝ) • albertUnit) := by
  intro hm
  have h := cyclic_anchoredSeven_corner_discriminant M p hp hA _ hm hstate
  have hmass : ‖ξ‖ ^ 2 = 1 / 3 := by
    rw [show ‖ξ‖ ^ 2 = M.probability [(0, true)] by
      simpa only [wordAmplitude_singleton, algebraicOutcome, ite_true] using
        cyclicHilbert_word_probability M [(0, true)],
      hm _ (by decide) rfl, LengthSeven.e3_conditioning p hp []]
    change (1 / 3 : ℝ) * albertTrace (p 0) = 1 / 3
    rw [(hp 0).2, mul_one]
  rw [hmass] at h
  exact (ne_of_gt (mul_pos (BlockB.atomCorner_discriminant_pos p hp hA) (by norm_num))) h

end AlbertSequential
