/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.ComplexTraceProjectiveWords
public import HilbertTraceModulus
public import Ends.UniformB
public import BlockB.StateSupport

@[expose] public section
noncomputable section
namespace AlbertSequential.HilbertTrace
open SharpDisturbance
variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (b : HilbertBasis B ℂ H)

/-- Trace norm of a self-adjoint trace-class operator on a complex Hilbert space. -/
def complexTraceNorm (X : signedFiniteTrace b) : ℝ := (positiveTrace b (CFC.abs X.val)).toReal

theorem complex_signedTrace_jordan_decomposition (X : signedFiniteTrace b) :
    ∃ U V : signedFiniteTrace b, U.val.IsPositive ∧ V.val.IsPositive ∧ X = U-V ∧
      signedTrace b U + signedTrace b V = complexTraceNorm b X := by
  have h := signedFiniteTrace_isSelfAdjoint b X
  have hu := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.posPart_nonneg X.val)
  have hv := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.negPart_nonneg X.val)
  have hf := (complex_mem_signedFiniteTrace_iff_modulus b X.val h).mp X.property
  rw [← CFC.posPart_add_negPart X.val h, positiveTrace_add b hu hv, ENNReal.add_ne_top] at hf
  let u : signedFiniteTrace b := ⟨_, IsPositiveFiniteTrace.mem_signedFiniteTrace b ⟨hu,hf.1⟩⟩
  let v : signedFiniteTrace b := ⟨_, IsPositiveFiniteTrace.mem_signedFiniteTrace b ⟨hv,hf.2⟩⟩
  refine ⟨u,v,hu,hv,Subtype.ext (CFC.posPart_sub_negPart X.val h).symm,?_⟩
  rw [signedTrace_eq_positiveTrace_toReal b u hu, signedTrace_eq_positiveTrace_toReal b v hv,
    complexTraceNorm, ← CFC.posPart_add_negPart X.val h, positiveTrace_add b hu hv, ENNReal.toReal_add hf.1 hf.2]

def complexBranch {I : Type*} (M : I → ComplexInstrument b) (q : Outcome I) :
    signedFiniteTrace b →ₗ[ℝ] signedFiniteTrace b := if q.2 then (M q.1).branchOne else (M q.1).branchZero

/-- Core Proposition 6.21 on an arbitrary complex Hilbert space. -/
theorem complex_sharp_effects_disturb (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (M : Fin 4 → ComplexInstrument b) (P : Fin 4 → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (hE : ∀ i X, (M i).massOne b X = signedTracePairing b (P i) X)
    (ρ : signedFiniteTrace b) (hρ : IsComplexDensity b ρ) (δ : ℝ) (hδ : 0 < δ)
    (gap : ∀ N : HilbertProjectiveData (Fin 4) ℂ H, ∃ w ∈ Ends.wordsE3Seven,
      δ ≤ |N.probability w - nativeWordProbability p ((1/3 : ℝ) • albertUnit) w|)
    (obs : ∀ w ∈ Ends.wordsE3Seven, signedTrace b (wordMap (complexBranch b M) w ρ) =
      nativeWordProbability p ((1/3 : ℝ) • albertUnit) w) :
    ∃ (q : Outcome (Fin 4)) (σ : signedFiniteTrace b) (u : Word (Fin 4)),
      IsComplexDensity b σ ∧ signedTrace b (complexBranch b M q σ) = 1 ∧ u ≠ [] ∧ u.length ≤ 6 ∧
      δ/2 ≤ |signedTrace b (wordMap (complexBranch b M) (q::u) σ) -
        signedTrace b (wordMap (complexBranch b M) u σ)| ∧ δ ≤ complexTraceNorm b (complexBranch b M q σ-σ) := by
  let F := complexBranch b M
  let L := fun q => complexSandwich b (algebraicOutcome P q)
  let C := {x : signedFiniteTrace b | x.val.IsPositive}
  have hpos (q) (x : signedFiniteTrace b) (hx : x ∈ C) : F q x ∈ C := by
    rcases q with ⟨i,t⟩; cases t
    · exact (M i).zero_positive x hx
    · exact (M i).one_positive x hx
  have hn (x : signedFiniteTrace b) (hx : x ∈ C) : 0 ≤ signedTrace b x := by
    rw [signedTrace_eq_positiveTrace_toReal b x hx]; exact ENNReal.toReal_nonneg
  have hdec (q) (x : signedFiniteTrace b) (hx : x ∈ C) : signedTrace b (F q x) ≤ signedTrace b x := by
    rcases q with ⟨i,t⟩; cases t
    · change signedTrace b ((M i).branchZero x) ≤ _
      rw [(M i).signedTrace_branchZero]; linarith [((M i).massOne_dominated b x hx).1]
    · exact ((M i).massOne_dominated b x hx).2
  have hproj (q : Outcome (Fin 4)) : IsStarProjection (algebraicOutcome P q) := by
    rcases q with ⟨i,t⟩; cases t
    · exact (hP i).one_sub
    · exact hP i
  have hmass (q : Outcome (Fin 4)) (X : signedFiniteTrace b) :
      signedTrace b (F q X) = signedTracePairing b (algebraicOutcome P q) X := by
    rcases q with ⟨i,t⟩; cases t
    · change signedTrace b ((M i).branchZero X) = signedTracePairing b (1-P i) X
      rw [(M i).signedTrace_branchZero,hE,complexTracePairing_complement_eq]
    · exact hE i X
  have ht (q) (x) : signedTrace b (F q x) = signedTrace b (L q x) := by
    dsimp only [L]
    rw [hmass,signedTrace_complexSandwich,(hproj q).isSelfAdjoint.star_eq,(hproj q).isIdempotentElem.eq]
  have hFL (q) (x) : F q (L q x) = F q x :=
    (branch_factors_through_complexSandwich b (F q) (hproj q) (hpos q) (hmass q) x).symm
  have hid (q) (x) : L q (L q x) = L q x := by
    apply Subtype.ext
    let R := algebraicOutcome P q
    change R * (R * x.val * star R) * star R = R * x.val * star R
    have hself : star R = R := (hproj q).isSelfAdjoint.star_eq
    have hRR : R*R = R := (hproj q).isIdempotentElem.eq
    rw [hself]
    calc
      _ = (R*R) * x.val * (R*R) := by simp only [mul_assoc]
      _ = _ := by rw [hRR]
  obtain ⟨w,⟨hlen,hhead⟩,hw⟩ := gap (complexTraceProjectiveModel b P hP ρ hρ)
  cases w with
  | nil => simp at hhead
  | cons q w =>
    have ha : q = (0,true) := by simpa using hhead
    subst q
    have hsing := obs [(0,true)] ⟨by decide,rfl⟩
    rw [BlockB.nativeWordProbability_cons_yes_e3 p 0 (hp 0) [],show nativeWordProbability p (p 0) [] =
      albertTrace (p 0) by rfl,(hp 0).2,mul_one] at hsing
    rw [complexTraceProjectiveModel_probability,← obs _ ⟨hlen,hhead⟩, abs_sub_comm] at hw
    obtain ⟨q,σ,u,hσ,hσt,hq,hu,hu6,hgap⟩ := exists_disturbance (C := C) (signedTrace b) hn
      (fun x hx hz => Subtype.ext (by by_contra h; have t := (complex_signedTrace_pos_iff b hx).2 h; linarith))
      (fun x hx t ht => ContinuousLinearMap.IsPositive.smul_of_nonneg hx (Complex.zero_le_real.mpr ht))
      F L (fun q x hx => complexSandwich_positive b _ x hx)
      (fun q x hx => (ht q x).symm ▸ hdec q x hx) ht hFL hid hρ.1 w (by simp only [List.length_cons] at hlen; omega)
      (by rw [← ht]; exact le_of_eq hsing) hδ hw
    refine ⟨q,σ,u,⟨hσ,hσt⟩,hq,hu,hu6,hgap,?_⟩
    let X := F q σ - σ
    obtain ⟨v,n,hv,hn',hX,hTr⟩ := complex_signedTrace_jordan_decomposition b X
    have hzero : signedTrace b X = 0 := by change signedTrace b (F q σ - σ) = 0; rw [map_sub,hq,hσt,sub_self]
    have hbound := word_trace_zero_half_bound (C := C) (signedTrace b) hn F hpos hdec u hv hn' hX hzero
    rw [hTr] at hbound
    change |signedTrace b (wordMap F u (F q σ - σ))| ≤ complexTraceNorm b X / 2 at hbound
    rw [map_sub,map_sub] at hbound
    change δ/2 ≤ |signedTrace b (wordMap F u (F q σ)) - signedTrace b (wordMap F u σ)| at hgap
    linarith

/-- The separation assumption for the disturbance bound follows uniformly from
the native positive invariant and the published length-seven separation. -/
theorem exists_complex_disturbance_margin (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) : ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (N : HilbertProjectiveData (Fin 4) ℂ H), ∃ w ∈ Ends.wordsE3Seven,
        δ ≤ |N.probability w - nativeWordProbability p ((1/3 : ℝ) • albertUnit) w| := by
  obtain ⟨F, δ, hf, hδ, _, hgap, _⟩ := Ends.uniform_b.{0,0,_,0} p hp hA
  refine ⟨δ,hδ,?_⟩
  intro H _ _ _ N
  obtain ⟨w, hw, h⟩ := hgap ℂ H N
  exact ⟨w,hf w hw,h⟩

end AlbertSequential.HilbertTrace
