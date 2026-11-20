/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Ends.UniformB
public import BlockB.ElevenSupport
public import Bridge.UniverseHorizon
public import FieldDimensionTableEquivalence
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.Set.Finite.List

/-! The positive attained maximum-error minimum of Theorem 6.1(b). -/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.Ends

open BlockB
open LengthSeven.Uniform

attribute [local irreducible] fourPointInvariant

/-- All signed words through length seven whose first letter is A-yes. -/
def sevenAYesWords : Finset (Word (Fin 4)) :=
  ((List.finite_length_le (Outcome (Fin 4)) 7).subset (fun _ (hw : _ ∈ wordsE3Seven) => hw.1)).toFinset

@[simp] theorem mem_sevenAYesWords (w : Word (Fin 4)) :
    w ∈ sevenAYesWords ↔ w ∈ wordsE3Seven := by
  unfold sevenAYesWords
  exact Set.Finite.mem_toFinset _

/-- The exact set used in the proof of Theorem 6.1(b). -/
def reducedSevenAYesWords : Finset (Word (Fin 4)) := by
  classical
  exact sevenAYesWords.filter IsReducedWord

@[simp] theorem mem_reducedSevenAYesWords (w : Word (Fin 4)) :
    w ∈ reducedSevenAYesWords ↔ w ∈ wordsE3Seven ∧ IsReducedWord w := by
  classical
  simp [reducedSevenAYesWords]

theorem reducedSevenAYesWords_nonempty : reducedSevenAYesWords.Nonempty :=
  ⟨[(0, true)], (mem_reducedSevenAYesWords _).mpr ⟨⟨by decide, rfl⟩, trivial⟩⟩

theorem sevenAYesWords_nonempty : sevenAYesWords.Nonempty :=
  ⟨[(0, true)], (mem_sevenAYesWords _).mpr ⟨by decide, rfl⟩⟩

/-- Maximum of the absolute coordinate errors on an actual finite table. -/
def finiteWordError {I : Type*} (F : Finset (Word I)) (hF : F.Nonempty)
    (g t : Word I → ℝ) : ℝ := F.sup' hF (fun w => |g w - t w|)

theorem finiteWordError_nonnegative {I : Type*} (F : Finset (Word I)) (hF : F.Nonempty)
    (g t : Word I → ℝ) : 0 ≤ finiteWordError F hF g t := by
  obtain ⟨w, hw⟩ := hF
  exact (abs_nonneg (g w - t w)).trans (Finset.le_sup' (fun w => |g w - t w|) hw)

theorem finiteWordError_eq_zero_of_agree {I : Type*} (F : Finset (Word I)) (hF : F.Nonempty)
    (g t : Word I → ℝ) (h : ∀ w ∈ F, g w = t w) : finiteWordError F hF g t = 0 := by
  refine le_antisymm ?_ (finiteWordError_nonnegative F hF g t)
  apply Finset.sup'_le
  intro w hw
  rw [h w hw, sub_self, abs_zero]

/-- The maximum error on all eligible words equals the maximum on the reduced
ones. Incompatible adjacent outcomes contribute zero for both tables. -/
theorem sevenAYesWordError_eq_reduced
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin 4) A)
    (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (ρ : Albert) :
    finiteWordError sevenAYesWords sevenAYesWords_nonempty M.probability (nativeWordProbability p ρ) =
      finiteWordError reducedSevenAYesWords reducedSevenAYesWords_nonempty
        M.probability (nativeWordProbability p ρ) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro w hw
    obtain ⟨hlen,hhead⟩ := (mem_sevenAYesWords _).mp hw
    have hM := reduceWord_probability M w
    have hn := reduceWord_nativeWordProbability_atoms p hp ρ w
    cases hr : reduceWord w with
    | none =>
      rw [hr] at hM hn
      rw [hM, hn, sub_self, abs_zero]
      exact finiteWordError_nonnegative _ _ _ _
    | some v =>
      rw [hr] at hM hn
      rw [hM, hn]
      have hvHead : v.head? = some (0,true) := by
        cases w with
        | nil => simp at hhead
        | cons a w =>
          rw [reduceWord_head? hr]
          exact hhead
      have hv : v ∈ reducedSevenAYesWords := (mem_reducedSevenAYesWords _).mpr
        ⟨⟨(reduceWord_length_le hr).trans hlen, hvHead⟩, reduceWord_isReduced hr⟩
      exact Finset.le_sup' (fun v => |M.probability v - nativeWordProbability p ρ v|) hv
  · apply Finset.sup'_le
    intro w hw
    exact Finset.le_sup' (fun v => |M.probability v - nativeWordProbability p ρ v|)
      ((mem_sevenAYesWords _).mpr ((mem_reducedSevenAYesWords _).mp hw).1)

/-- The unrounded maximum error on the printed reduced word set. -/
def uniformSevenError (p : Fin 4 → Albert) (g : Word (Fin 4) → ℝ) : ℝ :=
  finiteWordError reducedSevenAYesWords reducedSevenAYesWords_nonempty g
    (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit))

/-- The paper's named gap, as an infimum of these errors on the all-word
moment domain. Attainment and positivity are proved below. -/
def uniformSevenMargin (p : Fin 4 → Albert) : ℝ :=
  sInf ((fun m => uniformSevenError p (momentWordProbability m)) '' projectionMomentDomain 4)

theorem continuous_uniformSevenMomentError (p : Fin 4 → Albert) :
    Continuous (fun m : ProjectionMoments 4 => uniformSevenError p (momentWordProbability m)) := by
  unfold uniformSevenError finiteWordError
  exact Continuous.finset_sup'_apply reducedSevenAYesWords_nonempty
    (fun w _ => ((continuous_momentWordProbability w).sub continuous_const).abs)

theorem uniformSevenMargin_moment_minimum (p : Fin 4 → Albert) :
    IsLeast ((fun m => uniformSevenError p (momentWordProbability m)) '' projectionMomentDomain 4)
      (uniformSevenMargin p) := by
  let g (m : ProjectionMoments 4) := uniformSevenError p (momentWordProbability m)
  obtain ⟨m,hm,hmin⟩ := (isCompact_projectionMomentDomain 4).exists_isMinOn
    (projectionMomentDomain_nonempty 4) (continuous_uniformSevenMomentError p).continuousOn
  have hleast : IsLeast (g '' projectionMomentDomain 4) (g m) :=
    ⟨⟨m,hm,rfl⟩,by rintro _ ⟨k,hk,rfl⟩; exact hmin hk⟩
  change IsLeast (g '' projectionMomentDomain 4) (sInf (g '' projectionMomentDomain 4))
  rwa [hleast.csInf_eq]

theorem uniformSevenMargin_pos (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) : 0 < uniformSevenMargin p := by
  let ρ := (1 / 3 : ℝ) • albertUnit
  obtain ⟨m,hm,hmin⟩ := (uniformSevenMargin_moment_minimum p).1
  let M := momentsToProjectiveData m hm
  have he : uniformSevenMargin p = finiteWordError reducedSevenAYesWords
      reducedSevenAYesWords_nonempty M.probability (nativeWordProbability p ρ) := by
    rw [show M.probability = momentWordProbability m from funext (realizedMoments_probability m hm)]
    exact hmin.symm
  rw [he, ← sevenAYesWordError_eq_reduced M p hp ρ]
  by_contra! h
  apply uniform_lengthSeven_e3_algebraic p hp hA M
  intro w hlen hhead
  have hw := (mem_sevenAYesWords w).mpr ⟨hlen,hhead⟩
  have he' := Finset.le_sup' (fun w => |M.probability w - nativeWordProbability p ρ w|) hw
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (he'.trans h))

/-- The attained value works on the exact reduced set in every algebra universe. -/
theorem uniformSevenMargin_witness (p : Fin 4 → Albert)
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData (Fin 4) A) :
    ∃ w ∈ reducedSevenAYesWords,
      uniformSevenMargin p ≤ |M.probability w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w| := by
  let m := momentsOfProjectiveData M
  have hm := momentsOfProjectiveData_admissible M
  have h := (uniformSevenMargin_moment_minimum p).2 (show uniformSevenError p (momentWordProbability m) ∈
      (fun m => uniformSevenError p (momentWordProbability m)) '' projectionMomentDomain 4
    from ⟨m,hm,rfl⟩)
  obtain ⟨w,hw,hmax⟩ := Finset.exists_mem_eq_sup' reducedSevenAYesWords_nonempty
      (fun w => |momentWordProbability m w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w|)
  change uniformSevenMargin p ≤ finiteWordError _ _ _ _ at h
  rw [finiteWordError, hmax, momentWordProbability_eq_probability M] at h
  exact ⟨w,hw,h⟩

section LiftModel

universe u v

variable {I : Type*} {A : Type v} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

local instance : StarRing (ULift.{u} A) where
  star x := ⟨star x.down⟩
  star_involutive x := ULift.ext (star_star x.down)
  star_mul x y := ULift.ext (star_mul x.down y.down)
  star_add x y := ULift.ext (star_add x.down y.down)

local instance : StarModule ℝ (ULift.{u} A) where
  star_smul r x := ULift.ext (star_smul r x.down)

local instance : IsScalarTower ℝ (ULift.{u} A) (ULift.{u} A) where
  smul_assoc r x y := ULift.ext (smul_assoc r x.down y.down)

local instance : SMulCommClass ℝ (ULift.{u} A) (ULift.{u} A) where
  smul_comm r x y := ULift.ext (smul_comm r x.down y.down)

private def liftAlgebraicProjectiveData (M : AlgebraicProjectiveData I A) :
    AlgebraicProjectiveData I (ULift.{u} A) where
  projection i := ⟨M.projection i⟩
  idempotent i := ULift.ext (M.idempotent i)
  selfAdjoint i := ULift.ext (M.selfAdjoint i)
  state :=
    { toFun := fun x => M.state x.down
      map_add' x y := M.state.map_add x.down y.down
      map_smul' r x := M.state.map_smul r x.down }
  state_unit := M.state_unit
  state_star x := M.state_star x.down
  state_positive x := M.state_positive x.down

private theorem liftAlgebraicProjectiveData_probability (M : AlgebraicProjectiveData I A) (w : Word I) :
    (liftAlgebraicProjectiveData M : AlgebraicProjectiveData I (ULift.{u} A)).probability w = M.probability w := by
  let P : I → ULift.{u} A := (liftAlgebraicProjectiveData M).projection
  have hamp (w : Word I) : (wordAmplitude P w).down = wordAmplitude M.projection w := by
    induction w with
    | nil => rfl
    | cons q w ih =>
      have hq : (algebraicOutcome P q).down = algebraicOutcome M.projection q := by
        cases q with
        | mk i a => cases a <;> rfl
      rw [wordAmplitude_cons, wordAmplitude_cons]
      change (wordAmplitude P w).down * (algebraicOutcome P q).down = _
      rw [ih, hq]
  change M.state (star ((wordAmplitude P w).down) * (wordAmplitude P w).down) = _
  rw [hamp]
  rfl

/-- All admissible moment tables are physically realizable in every carrier
universe, by lifting the algebraic carrier before real cyclic completion. -/
theorem hilbertProjectiveTables_real_eq_moment_image (n : ℕ) :
    hilbertProjectiveTables.{u} ℝ n =
      (fun m => momentWordProbability m) '' projectionMomentDomain n := by
  ext g
  constructor
  · rintro ⟨H,hN,hI,hC,M,hg⟩
    let := hN
    let := hI
    let := hC
    refine ⟨momentsOfProjectiveData M.toAlgebraic, momentsOfProjectiveData_admissible M.toAlgebraic, ?_⟩
    funext w
    change momentWordProbability (momentsOfProjectiveData M.toAlgebraic) w = _
    rw [momentWordProbability_eq_probability M.toAlgebraic, hg w]
  · rintro ⟨m,hm,rfl⟩
    let M := momentsToProjectiveData m hm
    let L : AlgebraicProjectiveData (Fin n) (ULift.{u} (UniversalProjectionAlgebra n)) :=
      liftAlgebraicProjectiveData M
    apply mem_hilbertProjectiveTables_of_model (cyclicHilbertModel L)
    intro w
    rw [cyclicHilbertModel_probability, liftAlgebraicProjectiveData_probability]
    exact realizedMoments_probability m hm w

end LiftModel

universe u

/-- The same positive optimum is attained in each physical field and carrier
universe. The set of words is exactly the one specified in the proof. -/
theorem uniformSevenMargin_physical_minima (p : Fin 4 → Albert) :
    IsLeast (uniformSevenError p '' hilbertProjectiveTables.{u} ℝ 4) (uniformSevenMargin p) ∧
    IsLeast (uniformSevenError p '' hilbertProjectiveTables.{u} ℂ 4) (uniformSevenMargin p) ∧
    IsLeast (uniformSevenError p '' quaternionicProjectiveTables.{u} 4) (uniformSevenMargin p) := by
  have hreal : IsLeast (uniformSevenError p '' hilbertProjectiveTables.{u} ℝ 4)
      (uniformSevenMargin p) := by
    rw [hilbertProjectiveTables_real_eq_moment_image, Set.image_image]
    exact uniformSevenMargin_moment_minimum p
  exact ⟨hreal, by rwa [← real_complex_projectiveTables_eq], by rwa [← real_quaternionic_projectiveTables_eq]⟩

/-- Characterization of the anonymous finite-set witnesses: a number is a
uniform lower bound witnessed on some permitted finite subset if and only if
it is no larger than the named positive optimum. -/
theorem exists_finiteWitnessGap_iff_le_uniformSevenMargin (p : Fin 4 → Albert)
    (hp : ∀ i, IsAtom (p i)) (δ : ℝ) :
    (∃ F : Finset (Word (Fin 4)), (∀ w ∈ F, w ∈ wordsE3Seven) ∧
      ∀ g ∈ hilbertProjectiveTables.{u} ℝ 4, ∃ w ∈ F,
        δ ≤ |g w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w|) ↔
      δ ≤ uniformSevenMargin p := by
  constructor
  · rintro ⟨F,hF,hgap⟩
    obtain ⟨g,hg,hmin⟩ := (uniformSevenMargin_physical_minima.{u} p).1.1
    obtain ⟨w,hw,he⟩ := hgap g hg
    rcases hg with ⟨H,hN,hI,hC,M,hM⟩
    let := hN
    let := hI
    let := hC
    let ρ := (1 / 3 : ℝ) • albertUnit
    have hg : M.toAlgebraic.probability = g := funext hM
    have hmax := Finset.le_sup' (fun v => |g v - nativeWordProbability p ρ v|)
      ((mem_sevenAYesWords w).mpr (hF w hw))
    have heq := sevenAYesWordError_eq_reduced M.toAlgebraic p hp ρ
    rw [hg] at heq
    change _ ≤ finiteWordError sevenAYesWords sevenAYesWords_nonempty g (nativeWordProbability p ρ) at hmax
    rw [heq, show finiteWordError _ _ g (nativeWordProbability p ρ) = uniformSevenError p g from rfl,
      hmin] at hmax
    exact he.trans hmax
  · intro hδ
    refine ⟨reducedSevenAYesWords,fun w hw => ((mem_reducedSevenAYesWords w).mp hw).1,?_⟩
    rintro g ⟨H,hN,hI,hC,M,hg⟩
    let := hN
    let := hI
    let := hC
    obtain ⟨w,hw,he⟩ := uniformSevenMargin_witness p M.toAlgebraic
    exact ⟨w,hw,hδ.trans (by simpa only [hg w] using he)⟩

/-- The existing finite six-step model makes every nonempty finite horizon-six
maximum error attain zero, in each physical field and carrier universe. -/
theorem uniformSixError_physical_minima (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (F : Finset (Word (Fin 4))) (hF : F.Nonempty)
    (hs : ∀ w ∈ F, w.length ≤ 6) :
    let e := fun g => finiteWordError F hF g (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit))
    IsLeast (e '' hilbertProjectiveTables.{u} ℝ 4) 0 ∧
      IsLeast (e '' hilbertProjectiveTables.{u} ℂ 4) 0 ∧
      IsLeast (e '' quaternionicProjectiveTables.{u} 4) 0 := by
  let ρ := (1 / 3 : ℝ) • albertUnit
  let e := fun g => finiteWordError F hF g (nativeWordProbability p ρ)
  obtain ⟨M,hm⟩ := MatchingModels.prop_cer_universalsix_c12 p hp hA
  let m := momentsOfProjectiveData M.toAlgebraic
  have hReal : IsLeast (e '' hilbertProjectiveTables.{u} ℝ 4) 0 := by
    refine ⟨?_,?_⟩
    · refine ⟨momentWordProbability m, ?_, finiteWordError_eq_zero_of_agree _ _ _ _ ?_⟩
      · rw [hilbertProjectiveTables_real_eq_moment_image]
        exact ⟨m, momentsOfProjectiveData_admissible M.toAlgebraic, rfl⟩
      · intro w hw
        rw [momentWordProbability_eq_probability M.toAlgebraic, M.toAlgebraic_probability]
        exact hm w (hs w hw)
    · rintro _ ⟨g,hg,rfl⟩
      exact finiteWordError_nonnegative _ _ _ _
  exact ⟨hReal, by rwa [← real_complex_projectiveTables_eq], by rwa [← real_quaternionic_projectiveTables_eq]⟩

open AlbertChallenge (ProjectiveRepresentation QuaternionicRepresentation RightQuaternionicStructure) in
open AlbertChallenge.Bridge in
/-- The named gap gives the paper's reduced A-yes witness in the actual physical
representation interfaces, independently of field and carrier universe. -/
theorem uniformSevenMargin_physical_witness (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) :
    0 < uniformSevenMargin p ∧
    (∀ (𝕜 : Type) (H : Type u) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [CompleteSpace H] (M : ProjectiveRepresentation 4 𝕜 H),
      ∃ w ∈ reducedSevenAYesWords,
        uniformSevenMargin p ≤ |M.probability w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w|) ∧
    (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation 4 S),
      ∃ w ∈ reducedSevenAYesWords,
        uniformSevenMargin p ≤ |M.probability w - nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w|) := by
  refine ⟨uniformSevenMargin_pos p hp hA, ?_, ?_⟩
  · intro 𝕜 H _ _ _ _ M
    obtain ⟨w,hw,hg⟩ := uniformSevenMargin_witness p (ofProjectiveRepresentation M)
    exact ⟨w,hw,by rwa [ofProjectiveRepresentation_probability] at hg⟩
  · intro H _ _ _ S M
    obtain ⟨w,hw,hg⟩ := uniformSevenMargin_witness p (ofQuaternionicRepresentation M)
    exact ⟨w,hw,by rwa [ofQuaternionicRepresentation_probability] at hg⟩

end AlbertSequential.Ends
