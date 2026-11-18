/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PositiveFunctionalNull
public import ChronologicalWords
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Algebraic cyclic representation used by the all-history reconstruction.
The null subspace is only a left ideal. The quotient below is a vector space,
and its endomorphism ring supplies the associative target. No Hilbert-space
completion, faithfulness, trace, or dimension bound is used.
-/
@[expose] public section
noncomputable section
namespace AlbertSequential

section WordAlgebra
variable {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]

local instance : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm

theorem wordAmplitude_mem_wordVectorSpan (P : ι → A) (w : Word ι) :
    wordAmplitude P w ∈ WordVectorSpan P := Submodule.subset_span ⟨w, rfl⟩

theorem one_mem_wordVectorSpan (P : ι → A) : (1 : A) ∈ WordVectorSpan P := by
  simpa only [wordAmplitude_nil] using wordAmplitude_mem_wordVectorSpan P []

theorem mul_mem_wordVectorSpan (P : ι → A) {x y : A}
    (hx : x ∈ WordVectorSpan P) (hy : y ∈ WordVectorSpan P) :
    x * y ∈ WordVectorSpan P := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨u, rfl⟩
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨v, rfl⟩
          rw [← wordAmplitude_append P v u]
          exact wordAmplitude_mem_wordVectorSpan P _
      | zero => simpa only [mul_zero] using (WordVectorSpan P).zero_mem
      | add y z hy hz ihy ihz =>
          rw [mul_add]
          exact (WordVectorSpan P).add_mem ihy ihz
      | smul r y hy ih =>
          rw [mul_smul_comm]
          exact (WordVectorSpan P).smul_mem r ih
  | zero => simpa only [zero_mul] using (WordVectorSpan P).zero_mem
  | add x z hx hz ihx ihz =>
      rw [add_mul]
      exact (WordVectorSpan P).add_mem ihx ihz
  | smul r x hx ih =>
      rw [smul_mul_assoc]
      exact (WordVectorSpan P).smul_mem r ih

/-- The actual word span, packaged as a unital real subalgebra. -/
def wordSubalgebra (P : ι → A) : Subalgebra ℝ A where
  carrier := WordVectorSpan P
  zero_mem' := (WordVectorSpan P).zero_mem
  add_mem' := (WordVectorSpan P).add_mem
  one_mem' := one_mem_wordVectorSpan P
  mul_mem' := fun hx hy => mul_mem_wordVectorSpan P hx hy
  algebraMap_mem' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (WordVectorSpan P).smul_mem r (one_mem_wordVectorSpan P)

/-- The null space restricted to the word algebra, rather than an invalid
two-sided algebra quotient. -/
def cyclicNullSubmodule (M : AlgebraicProjectiveData ι A) :
    Submodule ℝ (wordSubalgebra M.projection) :=
  (positiveFunctionalNullSubmodule M.state M.state_star M.state_positive).comap
    (wordSubalgebra M.projection).val.toLinearMap

abbrev CyclicWordSpace (M : AlgebraicProjectiveData ι A) :=
  (wordSubalgebra M.projection) ⧸ cyclicNullSubmodule M

theorem mem_cyclicNullSubmodule (M : AlgebraicProjectiveData ι A)
    (x : wordSubalgebra M.projection) :
    x ∈ cyclicNullSubmodule M ↔ NullFor M.state (x : A) := Iff.rfl

/-- Left multiplication by a word-algebra element, before null descent. -/
def wordLeftMultiply (M : AlgebraicProjectiveData ι A)
    (z : wordSubalgebra M.projection) :
    Module.End ℝ (wordSubalgebra M.projection) where
  toFun x := z * x
  map_add' x y := mul_add z x y
  map_smul' r x := by simp

theorem wordLeftMultiply_preserves_null (M : AlgebraicProjectiveData ι A)
    (z : wordSubalgebra M.projection) :
    cyclicNullSubmodule M ≤ (cyclicNullSubmodule M).comap (wordLeftMultiply M z) := by
  intro x hx
  exact nullFor_left_invariant M.state M.state_star M.state_positive z x hx

/-- The actual cyclic representation as vector-space endomorphisms. -/
def cyclicLeftAction (M : AlgebraicProjectiveData ι A)
    (z : wordSubalgebra M.projection) : Module.End ℝ (CyclicWordSpace M) :=
  (cyclicNullSubmodule M).mapQ (cyclicNullSubmodule M) (wordLeftMultiply M z)
    (wordLeftMultiply_preserves_null M z)

@[simp] theorem cyclicLeftAction_mk (M : AlgebraicProjectiveData ι A)
    (z x : wordSubalgebra M.projection) :
    cyclicLeftAction M z ((cyclicNullSubmodule M).mkQ x) =
      (cyclicNullSubmodule M).mkQ (z * x) := rfl

@[simp] theorem cyclicLeftAction_quotient_mk (M : AlgebraicProjectiveData ι A)
    (z x : wordSubalgebra M.projection) :
    cyclicLeftAction M z (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (z * x) := rfl

theorem cyclicLeftAction_one (M : AlgebraicProjectiveData ι A) :
    cyclicLeftAction M 1 = 1 := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp only [cyclicLeftAction_quotient_mk, one_mul, one_apply_eq_self]

theorem cyclicLeftAction_mul (M : AlgebraicProjectiveData ι A)
    (z w : wordSubalgebra M.projection) :
    cyclicLeftAction M (z * w) = cyclicLeftAction M z * cyclicLeftAction M w := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp only [mul_apply_eq_comp, cyclicLeftAction_quotient_mk, mul_assoc]

theorem cyclicLeftAction_add (M : AlgebraicProjectiveData ι A)
    (z w : wordSubalgebra M.projection) :
    cyclicLeftAction M (z + w) = cyclicLeftAction M z + cyclicLeftAction M w := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp only [LinearMap.add_apply, cyclicLeftAction_quotient_mk, add_mul, Submodule.Quotient.mk_add]

theorem cyclicLeftAction_smul (M : AlgebraicProjectiveData ι A) (r : ℝ)
    (z : wordSubalgebra M.projection) :
    cyclicLeftAction M (r • z) = r • cyclicLeftAction M z := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp only [LinearMap.smul_apply, cyclicLeftAction_quotient_mk, smul_mul_assoc, Submodule.Quotient.mk_smul]

/-- Multiplication descends to an associative target without declaring a
product on the null quotient. -/
def cyclicRepresentation (M : AlgebraicProjectiveData ι A) :
    wordSubalgebra M.projection →ₐ[ℝ] Module.End ℝ (CyclicWordSpace M) where
  toFun := cyclicLeftAction M
  map_one' := cyclicLeftAction_one M
  map_mul' := cyclicLeftAction_mul M
  map_zero' := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => simp only [cyclicLeftAction_quotient_mk, zero_mul, Submodule.Quotient.mk_zero, LinearMap.zero_apply]
  map_add' := cyclicLeftAction_add M
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, cyclicLeftAction_smul,
      cyclicLeftAction_one, Algebra.algebraMap_eq_smul_one]

def cyclicVector (M : AlgebraicProjectiveData ι A) : CyclicWordSpace M :=
  (cyclicNullSubmodule M).mkQ 1

theorem cyclicVector_ne_zero (M : AlgebraicProjectiveData ι A) :
    cyclicVector M ≠ 0 := by
  intro h
  have hn : (1 : wordSubalgebra M.projection) ∈ cyclicNullSubmodule M :=
    (Submodule.Quotient.mk_eq_zero (cyclicNullSubmodule M)).mp h
  change M.state (star (1 : A) * 1) = 0 at hn
  simp only [star_one, mul_one, M.state_unit] at hn
  exact one_ne_zero hn

theorem cyclic_endomorphism_unit_ne_zero (M : AlgebraicProjectiveData ι A) :
    (1 : Module.End ℝ (CyclicWordSpace M)) ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun h (cyclicVector M)
  exact cyclicVector_ne_zero M he

/-- Evaluation at the cyclic vector is a real-linear functional on Q.
It is well-defined even for nonfaithful and nontracial model states. -/
def cyclicExpectation (M : AlgebraicProjectiveData ι A) :
    CyclicWordSpace M →ₗ[ℝ] ℝ :=
  (cyclicNullSubmodule M).liftQ
    (M.state.comp (wordSubalgebra M.projection).val.toLinearMap) (by
      intro x hx
      change M.state (x : A) = 0
      have hp := nullFor_pair_zero M.state M.state_star M.state_positive x hx (1 : A)
      simpa only [mul_one, M.state_star] using hp)

@[simp] theorem cyclicExpectation_mk (M : AlgebraicProjectiveData ι A)
    (x : wordSubalgebra M.projection) :
    cyclicExpectation M (Submodule.Quotient.mk x) = M.state (x : A) := rfl

theorem cyclicExpectation_action_vector (M : AlgebraicProjectiveData ι A)
    (z : wordSubalgebra M.projection) :
    cyclicExpectation M (cyclicRepresentation M z (cyclicVector M)) = M.state (z : A) := by
  change cyclicExpectation M (Submodule.Quotient.mk (z * 1)) = M.state (z : A)
  rw [mul_one, cyclicExpectation_mk]

/-- All-history vanishing gives the zero endomorphism on the actual cyclic
space; it does not assert that the original ambient operator was zero. -/
theorem cyclicRepresentation_eq_zero_of_all_histories
    (M : AlgebraicProjectiveData ι A) (z : wordSubalgebra M.projection)
    (hz : ∀ w, NullFor M.state ((z : A) * wordAmplitude M.projection w)) :
    cyclicRepresentation M z = 0 := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change (cyclicNullSubmodule M).mkQ (z * x) = 0
      apply (Submodule.Quotient.mk_eq_zero (cyclicNullSubmodule M)).mpr
      exact nullFor_on_wordSpan M.state M.state_star M.state_positive M.projection z hz x
        x.property

end WordAlgebra
end AlbertSequential
