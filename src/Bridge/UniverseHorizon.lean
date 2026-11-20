/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Bridge.UniverseCriterion
public import Bridge.C12
public import BlockB.EveryState
public import HilbertTraceComplex
public import FiveTest.Main
public import MatchingModels.FiveTestLowerBound
public import ScheduleMatchingSectorMatrices

@[expose] public section
noncomputable section

namespace AlbertSequential.MatchingModels

open AlbertChallenge (ProjectiveRepresentation QuaternionicRepresentation RightQuaternionicStructure)
open AlbertChallenge.Bridge
open AlbertSequential.LengthSeven AlbertSequential.LengthSeven.Uniform
open AlbertSequential.FiveTest

universe v

/-- The class-(I) models on Hilbert carriers in universe `v`, tested on all words
through the indicated horizon. The algebraic comparator is used only for proofs. -/
def ClassISeparatesAt {n : ℕ} (f : Word (Fin n) → ℝ) (L : ℕ) : Prop :=
  (∀ (𝕜 : Type) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [CompleteSpace H] (M : ProjectiveRepresentation n 𝕜 H),
      ¬ ∀ w : Word (Fin n), w.length ≤ L → M.probability w = f w) ∧
  (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation n S),
      ¬ ∀ w : Word (Fin n), w.length ≤ L → M.probability w = f w)

theorem ClassISeparatesAt.mono {n : ℕ} {f : Word (Fin n) → ℝ} {k L : ℕ}
    (h : ClassISeparatesAt.{v} f k) (hk : k ≤ L) : ClassISeparatesAt.{v} f L := by
  refine ⟨fun 𝕜 H _ _ _ _ M hm => ?_, fun H _ _ _ S M hm => ?_⟩
  · exact h.1 𝕜 H M fun w hw => hm w (hw.trans hk)
  · exact h.2 H S M fun w hw => hm w (hw.trans hk)

theorem classISeparatesAt_of_algebraic {n L : ℕ} {f : Word (Fin n) → ℝ}
    (h : ∀ {A : Type v} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
      [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin n) A),
      ¬ ∀ w : Word (Fin n), w.length ≤ L → M.probability w = f w) :
    ClassISeparatesAt.{v} f L := by
  refine ⟨fun _ _ _ _ _ _ M hm => ?_, fun _ _ _ _ _ M hm => ?_⟩
  · exact h (ofProjectiveRepresentation M) fun w hw =>
      (ofProjectiveRepresentation_probability M w).trans (hm w hw)
  · exact h (ofQuaternionicRepresentation M) fun w hw =>
      (ofQuaternionicRepresentation_probability M w).trans (hm w hw)

/-- The actual finite complex witness survives in every Hilbert carrier universe
and retains every word probability outside and inside the matching horizon. -/
theorem exists_liftedFiniteComplexModel {n d : ℕ}
    (M : HilbertProjectiveData (Fin n) ℂ (EuclideanSpace ℂ (Fin d))) :
    ∃ N : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (ULift.{v} (Fin d))),
      ∀ w : Word (Fin n), N.probability w = M.probability w := by
  obtain ⟨N, hN⟩ := exists_liftFiniteProjectiveRepresentation.{v} (toChallenge M)
  exact ⟨N, fun w => (hN w).trans (toChallenge_probability M w)⟩

theorem classISeparatesAt_iff_of_finite_witness {n k d : ℕ} (f : Word (Fin n) → ℝ)
    (hsep : ClassISeparatesAt.{v} f k)
    (M : HilbertProjectiveData (Fin n) ℂ (EuclideanSpace ℂ (Fin d)))
    (hm : ∀ w : Word (Fin n), w.length ≤ k - 1 → M.probability w = f w) (L : ℕ) :
    ClassISeparatesAt.{v} f L ↔ k ≤ L := by
  refine ⟨fun h => ?_, hsep.mono⟩
  by_contra hk
  have hL : L ≤ k - 1 := by omega
  obtain ⟨N, hN⟩ := exists_liftedFiniteComplexModel.{v} M
  exact h.1 ℂ (EuclideanSpace ℂ (ULift.{v} (Fin d))) N
    (fun w hw => (hN w).trans (hm w (hw.trans hL)))

theorem classISeparatesAt_isLeast_of_finite_witness {n k d : ℕ} (f : Word (Fin n) → ℝ)
    (hsep : ClassISeparatesAt.{v} f k)
    (M : HilbertProjectiveData (Fin n) ℂ (EuclideanSpace ℂ (Fin d)))
    (hm : ∀ w : Word (Fin n), w.length ≤ k - 1 → M.probability w = f w) :
    IsLeast {L : ℕ | ClassISeparatesAt.{v} f L} k :=
  ⟨hsep, fun L hL => (classISeparatesAt_iff_of_finite_witness f hsep M hm L).mp hL⟩

def classIMinimum {n : ℕ} (f : Word (Fin n) → ℝ) : ℕ :=
  sInf {L : ℕ | ClassISeparatesAt.{v} f L}

theorem classIMinimum_eq_of_isLeast {n k : ℕ} {f : Word (Fin n) → ℝ}
    (h : IsLeast {L : ℕ | ClassISeparatesAt.{v} f L} k) : classIMinimum.{v} f = k :=
  le_antisymm (Nat.sInf_le h.1) (le_csInf ⟨k, h.1⟩ h.2)

private theorem classI_e3_seven (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ClassISeparatesAt.{v} (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) 7 :=
  classISeparatesAt_of_algebraic fun M hm =>
    uniform_lengthSeven_e3_algebraic p hp hA M fun w hw _ => hm w hw

theorem classI_minimum_e3_isLeast (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    IsLeast {L : ℕ | ClassISeparatesAt.{v} (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) L} 7 := by
  obtain ⟨M, hm⟩ := prop_cer_universalsix_c12 p hp hA
  exact classISeparatesAt_isLeast_of_finite_witness _ (classI_e3_seven p hp hA) M hm

theorem classI_minimum_e3 (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    classIMinimum.{v} (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) = 7 :=
  classIMinimum_eq_of_isLeast (classI_minimum_e3_isLeast p hp hA)

section Conditioning

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def conditionComplexOnYes (M : HilbertProjectiveData I ℂ H) (i : I)
    (h : 0 < M.toAlgebraic.probability [(i, true)]) : HilbertProjectiveData I ℂ H :=
  let S := BlockB.conditionOnYes M.toAlgebraic i h
  { projection := M.projection
    isStarProjection := M.isStarProjection
    state :=
      { toFun := fun T => S.state T.val
        map_add' := fun X Y => S.state.map_add X.val Y.val
        map_smul' := fun r X => S.state.map_smul r X.val }
    normalized := by
      change S.state 1 = 1
      exact S.state_unit
    positive := by
      intro T hT
      obtain ⟨B, _, hB, _⟩ := HilbertTrace.exists_selfAdjoint_factor hT
      let C := (operatorValue ℂ H).symm B
      have he : star C * C = T.val := by
        apply (operatorValue ℂ H).injective
        rw [map_mul, operatorValue_star, RingEquiv.apply_symm_apply]
        exact hB
      change 0 ≤ S.state T.val
      rw [← he]
      exact S.state_positive C }

private theorem conditionComplexOnYes_probability (M : HilbertProjectiveData I ℂ H)
    (i : I) (h : 0 < M.toAlgebraic.probability [(i, true)]) (w : Word I) :
    (conditionComplexOnYes M i h).probability w = M.probability ((i, true) :: w) /
      M.probability [(i, true)] := by
  change (BlockB.conditionOnYes M.toAlgebraic i h).probability w = _
  rw [BlockB.conditionOnYes_probability, M.toAlgebraic_probability, M.toAlgebraic_probability]

end Conditioning

/-- The paper's one-press conditioning of the finite six-step witness. -/
theorem classI_pA_five_step_model (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    ∃ M : HilbertProjectiveData (Fin 4) ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w : Word (Fin 4), w.length ≤ 5 → M.probability w = nativeWordProbability p (p 0) w := by
  obtain ⟨M, hm⟩ := prop_cer_universalsix_c12 p hp hA
  have hy : M.probability [(0, true)] = 1 / 3 := by
    rw [hm _ (by simp)]
    rw [e3_conditioning p hp]
    change (1 / 3 : ℝ) * albertTrace (p 0) = _
    rw [(hp 0).2, mul_one]
  have hy' : 0 < M.toAlgebraic.probability [(0, true)] := by
    rw [M.toAlgebraic_probability, hy]; norm_num
  refine ⟨conditionComplexOnYes M 0 hy', fun w hw => ?_⟩
  rw [conditionComplexOnYes_probability, hm _ (by simpa using Nat.succ_le_succ hw),
    e3_conditioning p hp, hy]
  ring

theorem classI_minimum_pA_isLeast (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    IsLeast {L : ℕ | ClassISeparatesAt.{v} (nativeWordProbability p (p 0)) L} 6 := by
  obtain ⟨M, hm⟩ := classI_pA_five_step_model p hp hA
  exact classISeparatesAt_isLeast_of_finite_witness _
    (classISeparatesAt_of_algebraic (uniform_lengthSix_pA_algebraic p hp hA)) M hm

theorem classI_minimum_pA (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) : classIMinimum.{v} (nativeWordProbability p (p 0)) = 6 :=
  classIMinimum_eq_of_isLeast (classI_minimum_pA_isLeast p hp hA)

theorem classI_minimum_F_p0_isLeast :
    IsLeast {L : ℕ | ClassISeparatesAt.{v} (nativeWordProbability pentadF (pentadF 0)) L} 10 :=
  classISeparatesAt_isLeast_of_finite_witness _
    (classISeparatesAt_of_algebraic (cor_five_minimum_upper_p0 10 le_rfl))
    fiveTestComparator_p0 fiveTestComparator_p0_matches

theorem classI_minimum_F_e3_isLeast :
    IsLeast {L : ℕ | ClassISeparatesAt.{v}
      (nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit)) L} 11 :=
  classISeparatesAt_isLeast_of_finite_witness _
    (classISeparatesAt_of_algebraic (cor_five_minimum_upper_e3 11 le_rfl))
    fiveTestComparator_e3 fiveTestComparator_e3_matches

theorem classI_minimum_F_p0 : classIMinimum.{v} (nativeWordProbability pentadF (pentadF 0)) = 10 :=
  classIMinimum_eq_of_isLeast classI_minimum_F_p0_isLeast

theorem classI_minimum_F_e3 :
    classIMinimum.{v} (nativeWordProbability pentadF ((1 / 3 : ℝ) • albertUnit)) = 11 :=
  classIMinimum_eq_of_isLeast classI_minimum_F_e3_isLeast

theorem classI_minimum_M_isLeast :
    IsLeast {L : ℕ | ClassISeparatesAt.{v}
      (nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit)) L} 7 := by
  have hA : 0 < fourPointInvariant maximizerConfig := by rw [fourPointInvariant_maximizerConfig]; norm_num
  exact classISeparatesAt_isLeast_of_finite_witness _ (classI_e3_seven _ maximizerConfig_isAtom hA)
    _ horizon_M_matrix

theorem classI_minimum_S_isLeast :
    IsLeast {L : ℕ | ClassISeparatesAt.{v}
      (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) L} 7 := by
  have hA : 0 < fourPointInvariant fixedS := by rw [fourPointInvariant_fixedS]; norm_num
  exact classISeparatesAt_isLeast_of_finite_witness _ (classI_e3_seven _ fixedS_isAtom hA)
    _ horizon_S_matrix

theorem classI_minimum_MS :
    classIMinimum.{v} (nativeWordProbability maximizerConfig ((1 / 3 : ℝ) • albertUnit)) = 7 ∧
    classIMinimum.{v} (nativeWordProbability fixedS ((1 / 3 : ℝ) • albertUnit)) = 7 :=
  ⟨classIMinimum_eq_of_isLeast classI_minimum_M_isLeast,
    classIMinimum_eq_of_isLeast classI_minimum_S_isLeast⟩

end AlbertSequential.MatchingModels

namespace AlbertChallenge.Bridge

open AlbertSequential.MatchingModels

/-- The public challenge's minimum with the same model conditions in every
Hilbert carrier universe. -/
theorem least_separating_length_all_universes (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) :
    IsLeast {L : ℕ | ClassISeparatesAt.{v} (wordProbability p maximallyMixed) L} 7 := by
  have table : wordProbability p maximallyMixed =
      AlbertSequential.nativeWordProbability (fun i => toT (p i))
        ((1 / 3 : ℝ) • AlbertSequential.albertUnit) := by
    funext w
    simpa only [maximallyMixed_toT] using (wordProbability_toT p maximallyMixed w).symm
  rw [table]
  exact classI_minimum_e3_isLeast _ (atoms_toT hp) (fourPointInvariant_pos_of_generates hp hg)

end AlbertChallenge.Bridge
