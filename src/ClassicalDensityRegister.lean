/- SPDX-License-Identifier: Apache-2.0 -/
module
public import CanonicalIdealInstruments
public import GeneralEJAWordTransport
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Normalized-state classical register for core §3, model class (III). -/
@[expose] public section
noncomputable section
namespace AlbertSequential

/-- A classical register carrying its state from one binary observation to the next. -/
structure ClassicalBinaryRegister (ι S : Type*) where
  probability : Outcome ι → S → ℝ
  nonneg : ∀ a s, 0 ≤ probability a s
  normalized : ∀ i s, probability (i,true) s + probability (i,false) s = 1
  next : Outcome ι → S → S

def ClassicalBinaryRegister.wordProbability {ι S : Type*} (R : ClassicalBinaryRegister ι S) :
    S → Word ι → ℝ
  | _, [] => 1
  | s, a :: w => R.probability a s * R.wordProbability (R.next a s) w

namespace ClassicalBinaryRegister
variable {ι S : Type*} (R : ClassicalBinaryRegister ι S)

def outputLaw (i : ι) (s : S) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (R.probability (i,b) s)) (by
    rw [Fintype.sum_bool, ← ENNReal.ofReal_add (R.nonneg _ _) (R.nonneg _ _), R.normalized]
    simp)

/-- Both the observed bit and the next classical state have an actual joint probability law. -/
def transition (i : ι) (s : S) : PMF (Bool × S) :=
  (R.outputLaw i s).map (fun b => (b,R.next (i,b) s))

theorem transition_apply (i : ι) (s : S) (b : Bool) (t : S) :
    letI := Classical.decEq S
    R.transition i s (b,t) = if t = R.next (i,b) s then ENNReal.ofReal (R.probability (i,b) s) else 0 := by
  classical
  cases b <;> simp [transition,PMF.map_apply,tsum_fintype,outputLaw]

end ClassicalBinaryRegister

namespace UnitalJordanProduct
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : UnitalJordanProduct E) (hfr : P.FormallyReal)
local notation "τ" => P.canonicalTraceOfFormallyReal hfr
local notation "States" => {x : E // P.IsCanonicalDensity hfr x}

/-- Arbitrary positive binary state updates act on a classical register. The previous state
is a permissible next state on an impossible outcome, where the branch carries zero mass. -/
theorem exists_classical_density_register (T : Outcome ι → E →ₗ[ℝ] E)
    (hpos : ∀ a x, x ∈ P.squareCone → T a x ∈ P.squareCone)
    (hn : ∀ i x, τ (T (i,true) x + T (i,false) x) = τ x) :
    ∃ R : ClassicalBinaryRegister ι States,
      (∀ a s, R.probability a s = τ (T a s.val)) ∧
      (∀ a s, R.probability a s • (R.next a s).val = T a s.val) ∧
      (∀ s w, R.wordProbability s w = τ (w.foldl (fun x a => T a x) s.val)) := by
  classical
  let prob (a : Outcome ι) (s : States) := τ (T a s.val)
  have hp (a) (s : States) : 0 ≤ prob a s :=
    CanonicalInstruments.trace_nonnegative_on_squareCone P hfr _ (hpos a s.val s.property.1)
  let next (a) (s : States) : States :=
    if h : prob a s = 0 then s else ⟨(prob a s)⁻¹ • T a s.val,
      P.nonnegative_smul_mem_squareCone _ (hpos a _ s.property.1) _ (inv_nonneg.mpr (hp a s)),
      by rw [map_smul]; exact inv_mul_cancel₀ h⟩
  let R : ClassicalBinaryRegister ι States := {
    probability := prob, nonneg := hp, next := next
    normalized := fun i s => by simpa only [prob,← map_add,hn] using s.property.2 }
  have hraw (a) (s : States) : prob a s • (next a s).val = T a s.val := by
    by_cases h : prob a s = 0
    · rw [h,zero_smul]
      obtain ⟨y,hy⟩ := hpos a _ s.property.1
      by_cases hy0 : y = 0
      · simp [hy,hy0]
      · exact False.elim ((P.canonicalTraceOfFormallyReal_square_positive hfr y hy0).ne'
          (hy ▸ (show τ (T a s.val) = 0 from h)))
    · simp only [next,dite_eq_right h,smul_smul,mul_inv_cancel₀ h,one_smul]
  have hscale (w : Word ι) (r : ℝ) (x : E) : w.foldl (fun y a => T a y) (r • x) =
      r • w.foldl (fun y a => T a y) x := by
    induction w generalizing x with
    | nil => rfl
    | cons a w ih => simp only [List.foldl_cons,map_smul,ih]
  refine ⟨R,fun _ _ => rfl,hraw,?_⟩
  intro s w
  induction w generalizing s with
  | nil => exact s.property.2.symm
  | cons a w ih =>
    change prob a s * R.wordProbability (next a s) w = τ (w.foldl (fun x a => T a x) (T a s.val))
    rw [ih,← hraw a s,hscale,map_smul]
    rfl

theorem exists_classical_register_for_ideal_tests (p : ι → E) (hp : ∀ i, P.product (p i) (p i) = p i) :
    ∃ R : ClassicalBinaryRegister ι States, ∀ s w,
      R.wordProbability s w = τ (P.sequentialBranchState p s.val w) := by
  let T (a : Outcome ι) := P.quadraticRepresentation (P.sequentialOutcome p a)
  obtain ⟨R,_,_,hw⟩ := P.exists_classical_density_register hfr T
    (fun _ _ hx => CanonicalInstruments.quadraticRepresentation_preserves_squareCone P hfr _ _ hx)
    (fun i x => CanonicalInstruments.quadratic_pair_normalized P hfr _ (hp i) x)
  exact ⟨R,hw⟩

end UnitalJordanProduct
end AlbertSequential
