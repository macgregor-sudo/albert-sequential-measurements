/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.QuaternionicTraceProjectiveWords
public import HilbertTraceModulus
public import Ends.UniformB
public import BlockB.StateSupport

@[expose] public section
noncomputable section
namespace AlbertSequential.HilbertTrace
open SharpDisturbance
variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (b : HilbertBasis B ℝ H) (S : RightQuaternionicHilbertStructure H)
local notation "Op" => S.toOperatorStructure.operatorAlgebra
local notation "Carrier" => quaternionicSignedFiniteTrace b S

def quaternionicBranch {I : Type*} (M : I → QuaternionicInstrument b S) (q : Outcome I) :
    Carrier →ₗ[ℝ] Carrier := if q.2 then (M q.1).branchOne else (M q.1).branchZero

/-- Core Proposition 6.21 on an arbitrary right-quaternionic Hilbert space. -/
theorem quaternionic_sharp_effects_disturb (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (M : Fin 4 → QuaternionicInstrument b S) (P : Fin 4 → Op) (hP : ∀ i, IsStarProjection (P i))
    (hE : ∀ i X, (M i).massOne b S X = quaternionicTracePairing b S (P i) X)
    (ρ : Carrier) (hρ : IsQuaternionicDensity b S ρ) (δ : ℝ) (hδ : 0 < δ)
    (gap : ∀ N : QuaternionicProjectiveData (Fin 4) S.toOperatorStructure, ∃ w ∈ Ends.wordsE3Seven,
      δ ≤ |N.state (N.wordEffect w) - nativeWordProbability p ((1/3 : ℝ) • albertUnit) w|)
    (obs : ∀ w ∈ Ends.wordsE3Seven, quaternionicSignedTrace b S (wordMap (quaternionicBranch b S M) w ρ) =
      nativeWordProbability p ((1/3 : ℝ) • albertUnit) w) :
    ∃ (q : Outcome (Fin 4)) (σ : Carrier) (u : Word (Fin 4)),
      IsQuaternionicDensity b S σ ∧ quaternionicSignedTrace b S (quaternionicBranch b S M q σ) = 1 ∧ u ≠ [] ∧ u.length ≤ 6 ∧
      δ/2 ≤ |quaternionicSignedTrace b S (wordMap (quaternionicBranch b S M) (q::u) σ) -
        quaternionicSignedTrace b S (wordMap (quaternionicBranch b S M) u σ)| ∧ δ ≤ quaternionicTraceNorm b S (quaternionicBranch b S M q σ-σ) := by
  let F := quaternionicBranch b S M
  let L := fun q => quaternionicSandwich b S (algebraicOutcome P q)
  let C := {x : Carrier | x.val.IsPositive}
  have hpos (q) (x : Carrier) (hx : x ∈ C) : F q x ∈ C := by
    rcases q with ⟨i,t⟩; cases t
    · exact (M i).zero_positive x hx
    · exact (M i).one_positive x hx
  have hn (x : Carrier) (hx : x ∈ C) : 0 ≤ quaternionicSignedTrace b S x := by
    change 0 ≤ (1/4 : ℝ) * signedTrace b (quaternionicCarrierInclusion b S x)
    rw [signedTrace_eq_positiveTrace_toReal b _ hx]; positivity
  have hdec (q) (x : Carrier) (hx : x ∈ C) : quaternionicSignedTrace b S (F q x) ≤ quaternionicSignedTrace b S x := by
    rcases q with ⟨i,t⟩; cases t
    · change quaternionicSignedTrace b S ((M i).branchZero x) ≤ _
      rw [(M i).signedTrace_branchZero]; linarith [((M i).massOne_dominated b S x hx).1]
    · exact ((M i).massOne_dominated b S x hx).2
  have hproj (q : Outcome (Fin 4)) : IsStarProjection (algebraicOutcome P q) := by
    rcases q with ⟨i,t⟩; cases t
    · exact (hP i).one_sub
    · exact hP i
  have hmass (q : Outcome (Fin 4)) (X : Carrier) :
      quaternionicSignedTrace b S (F q X) = quaternionicTracePairing b S (algebraicOutcome P q) X := by
    rcases q with ⟨i,t⟩; cases t
    · change quaternionicSignedTrace b S ((M i).branchZero X) = quaternionicTracePairing b S (1-P i) X
      rw [(M i).signedTrace_branchZero,hE,quaternionicTracePairing_complement_eq]
    · exact hE i X
  have ht (q) (x) : quaternionicSignedTrace b S (F q x) = quaternionicSignedTrace b S (L q x) := by
    dsimp only [L]
    rw [hmass,signedTrace_quaternionicSandwich,(hproj q).isSelfAdjoint.star_eq,(hproj q).isIdempotentElem.eq]
  have hFL (q) (x) : F q (L q x) = F q x :=
    (branch_factors_through_quaternionicSandwich b S (F q) (hproj q) (hpos q) (hmass q) x).symm
  have hid (q) (x) : L q (L q x) = L q x := by
    apply Subtype.ext
    let R := (algebraicOutcome P q).val
    have hpR : IsStarProjection R := (hproj q).map S.toOperatorStructure.operatorValue
    change R * (R * x.val * star R) * star R = R * x.val * star R
    have hself : star R = R := hpR.isSelfAdjoint.star_eq
    have hRR : R*R = R := hpR.isIdempotentElem.eq
    rw [hself]
    calc
      _ = (R*R) * x.val * (R*R) := by simp only [mul_assoc]
      _ = _ := by rw [hRR]
  obtain ⟨w,⟨hlen,hhead⟩,hw⟩ := gap (quaternionicTraceProjectiveModel b S P hP ρ hρ)
  cases w with
  | nil => simp at hhead
  | cons q w =>
    have ha : q = (0,true) := by simpa using hhead
    subst q
    have hsing := obs [(0,true)] ⟨by decide,rfl⟩
    rw [BlockB.nativeWordProbability_cons_yes_e3 p 0 (hp 0) [],show nativeWordProbability p (p 0) [] =
      albertTrace (p 0) by rfl,(hp 0).2,mul_one] at hsing
    rw [quaternionicTraceProjectiveModel_probability,← obs _ ⟨hlen,hhead⟩, abs_sub_comm] at hw
    obtain ⟨q,σ,u,hσ,hσt,hq,hu,hu6,hgap⟩ := exists_disturbance (C := C) (quaternionicSignedTrace b S) hn
      (fun x hx hz => Subtype.ext (by by_contra h; have t := (quaternionic_signedTrace_pos_iff b S hx).2 h; linarith))
      (fun x hx t ht => ContinuousLinearMap.IsPositive.smul_of_nonneg hx ht)
      F L (fun q x hx => quaternionicSandwich_positive b S _ x hx)
      (fun q x hx => (ht q x).symm ▸ hdec q x hx) ht hFL hid hρ.1 w (by simp only [List.length_cons] at hlen; omega)
      (by rw [← ht]; exact le_of_eq hsing) hδ hw
    refine ⟨q,σ,u,⟨hσ,hσt⟩,hq,hu,hu6,hgap,?_⟩
    let X := F q σ - σ
    obtain ⟨v,n,hv,hn',hX,hTr⟩ := quaternionic_signedTrace_jordan_decomposition b S X
    have hzero : quaternionicSignedTrace b S X = 0 := by change quaternionicSignedTrace b S (F q σ - σ) = 0; rw [map_sub,hq,hσt,sub_self]
    have hbound := word_trace_zero_half_bound (C := C) (quaternionicSignedTrace b S) hn F hpos hdec u hv hn' hX hzero
    rw [hTr] at hbound
    change |quaternionicSignedTrace b S (wordMap F u (F q σ - σ))| ≤ quaternionicTraceNorm b S X / 2 at hbound
    rw [map_sub,map_sub] at hbound
    change δ/2 ≤ |quaternionicSignedTrace b S (wordMap F u (F q σ)) - quaternionicSignedTrace b S (wordMap F u σ)| at hgap
    linarith

end AlbertSequential.HilbertTrace
