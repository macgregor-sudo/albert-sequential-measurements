/- SPDX-License-Identifier: Apache-2.0 -/
module

public import BlockA.SecondOrderResidual
public import FieldDimensionTableEquivalence
public import MatchingModels.UniversalSix
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace AlbertSequential.AppF

open scoped Matrix
universe u

/-- Validity on all three actual Class-I Hilbert table classes in a fixed, arbitrary universe. -/
def IsClassIProjectiveEquality {n : ℕ} (c : Word (Fin n) →₀ ℝ) : Prop :=
  ∀ f : Word (Fin n) → ℝ,
    (f ∈ hilbertProjectiveTables.{u} ℝ n ∨ f ∈ hilbertProjectiveTables.{u} ℂ n ∨
      f ∈ quaternionicProjectiveTables.{u} n) →
    c.sum (fun w a => a * f w) = 0

private def liftedGroupEvaluation {n : ℕ} {A : Type*} [Ring A] [Algebra ℝ A]
    (p : Fin n → A) (hp : ∀ i, p i * p i = p i) : GroupAlgebra n →ₐ[ℝ] A :=
  MonoidAlgebra.lift ℝ A (RWord n)
    (rwordLift (fun i => (2 : ℝ) • p i - 1) fun i => reflection_of_idempotent_sq (hp i))

private theorem liftedGroupEvaluation_proj {n : ℕ} {A : Type*} [Ring A] [Algebra ℝ A]
    (p : Fin n → A) (hp : ∀ i, p i * p i = p i) (i : Fin n) :
    liftedGroupEvaluation p hp (groupProj n i) = p i := by
  have hgen : liftedGroupEvaluation p hp (groupGen n i) = (2 : ℝ) • p i - 1 := by
    simp [liftedGroupEvaluation, groupGen]
  rw [groupProj, map_smul, map_add, map_one, hgen,
    show (1 : A) + ((2 : ℝ) • p i - 1) = (2 : ℝ) • p i by abel, smul_smul]
  norm_num

theorem algebraic_wordSum_eq_zero_of_freeProductZero {n : ℕ} {A : Type*} [Ring A] [StarRing A]
    [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A) (c : Word (Fin n) →₀ ℝ)
    (hc : freeProductImage c = 0) : c.sum (fun w a => a * M.probability w) = 0 := by
  let _ : Algebra ℝ A := Algebra.ofModule smul_mul_assoc mul_smul_comm
  let ev := liftedGroupEvaluation M.projection M.idempotent
  have hword (w : Word (Fin n)) :
      ev (wordQuadOperator (groupProj n) w) = wordOperator M.projection w := by
    rw [← wordQuadOperator_eq_wordOperator _ M.selfAdjoint]
    induction w with
    | nil => exact map_one ev
    | cons a w ih =>
      rw [wordQuadOperator, wordQuadOperator, map_mul, map_mul, ih]
      obtain ⟨i, b⟩ := a
      cases b <;> simp [algebraicOutcome, ev, liftedGroupEvaluation_proj]
  have h := congrArg (fun z => M.state (ev z)) hc
  simpa only [freeProductImage, Finsupp.sum, map_sum, map_zero, map_smul, smul_eq_mul, hword,
    AlgebraicProjectiveData.probability] using h

private def finiteVectorReadout {N : ℕ} (v : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun X := dotProduct v (X *ᵥ v)
  map_add' X Y := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' r X := by simp [Matrix.smul_mulVec, dotProduct_smul]

private theorem finiteVectorReadout_star {N : ℕ} (v : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    finiteVectorReadout v (star X) = finiteVectorReadout v X := by
  have hstar : star X = Xᵀ := by ext i j; simp [Matrix.star_apply]
  change dotProduct v (star X *ᵥ v) = dotProduct v (X *ᵥ v)
  rw [hstar, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]

private theorem finiteVectorReadout_positive {N : ℕ} (v : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    0 ≤ finiteVectorReadout v (star X * X) := by
  have hstar : star X = Xᵀ := by ext i j; simp [Matrix.star_apply]
  change 0 ≤ dotProduct v ((star X * X) *ᵥ v)
  rw [hstar, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((X *ᵥ v) i)

/-- Every finite real vector-state table occurs in the finite Class-I real class in any
chosen carrier universe. Reindexing is a star-algebra equivalence. -/
theorem finiteRealVectorTable_mem {n N : ℕ} (p : Fin n → Matrix (Fin N) (Fin N) ℝ)
    (hp : ∀ i, (p i)ᵀ = p i ∧ p i * p i = p i)
    (v : Fin N → ℝ) (hv : dotProduct v v = 1) :
    (fun w => dotProduct v (wordOperator p w *ᵥ v)) ∈ finiteHilbertProjectiveTables.{u} ℝ n := by
  let e : Matrix (Fin N) (Fin N) ℝ ≃⋆ₐ[ℝ] Matrix (ULift.{u} (Fin N)) (ULift.{u} (Fin N)) ℝ :=
    Matrix.reindexStarAlgEquiv ℝ ℝ Equiv.ulift.symm
  let φ := finiteVectorReadout v
  have hs (i : Fin n) : star (p i) = p i := by
    ext a b
    simpa [Matrix.star_apply] using congrFun (congrFun (hp i).1 a) b
  let M : AlgebraicProjectiveData (Fin n) (Matrix (ULift.{u} (Fin N)) (ULift.{u} (Fin N)) ℝ) :=
    { projection := fun i => e (p i)
      idempotent := fun i => by rw [← map_mul, (hp i).2]
      selfAdjoint := fun i => by rw [← map_star, hs i]
      state := φ.comp e.symm.toAlgEquiv.toLinearMap
      state_unit := by
        change φ (e.symm 1) = 1
        rw [map_one]
        change dotProduct v (1 *ᵥ v) = 1
        rwa [Matrix.one_mulVec]
      state_star := by
        intro X
        change φ (e.symm (star X)) = φ (e.symm X)
        rw [map_star]
        exact finiteVectorReadout_star v _
      state_positive := by
        intro X
        change 0 ≤ φ (e.symm (star X * X))
        rw [map_mul, map_star]
        exact finiteVectorReadout_positive v _ }
  have hword (w : Word (Fin n)) :
      e.symm (wordOperator M.projection w) = wordOperator p w := by
    have hamp (w : Word (Fin n)) :
        e.symm (wordAmplitude M.projection w) = wordAmplitude p w := by
      induction w using List.reverseRecOn with
      | nil => exact map_one e.symm
      | append_singleton w a ih =>
        rw [wordAmplitude_append_singleton, wordAmplitude_append_singleton, map_mul, ih]
        obtain ⟨i, b⟩ := a
        cases b <;> simp [algebraicOutcome, M]
    rw [wordOperator, wordOperator, map_mul, map_star, hamp]
  have hfin : FiniteDimensional ℝ (CyclicHilbert M) := cyclicHilbert_finite_of_ambient M
  let _ := hfin
  apply mem_finiteHilbertProjectiveTables_of_model (cyclicHilbertModel M)
  intro w
  rw [cyclicHilbertModel_probability]
  change φ (e.symm (wordOperator M.projection w)) = dotProduct v (wordOperator p w *ᵥ v)
  rw [hword]
  rfl

theorem freeProductZero_implies_classIEquality {n : ℕ} {c : Word (Fin n) →₀ ℝ}
    (hc : freeProductImage c = 0) : IsClassIProjectiveEquality.{u} c := by
  intro f hf
  rcases hf with hf | hf | hf
  · obtain ⟨H, _, _, _, M, he⟩ := hf
    simpa only [← he] using algebraic_wordSum_eq_zero_of_freeProductZero M.toAlgebraic c hc
  · obtain ⟨H, _, _, _, M, he⟩ := hf
    simpa only [← he] using algebraic_wordSum_eq_zero_of_freeProductZero M.toAlgebraic c hc
  · obtain ⟨H, _, _, _, S, M, he⟩ := hf
    simpa only [← he] using algebraic_wordSum_eq_zero_of_freeProductZero M.toAlgebraic c hc

/-- Proposition 6.17(a), for actual real, complex and quaternionic Class-I models in
any carrier universe. Testing finite real vector states is sufficient. -/
theorem classIEquality_iff_finiteRealVectorStates {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    IsClassIProjectiveEquality.{u} c ↔ IsProjectiveEquality c := by
  constructor
  · intro h N p hp v hv
    have hmem := finiteRealVectorTable_mem.{u} p hp v hv
    obtain ⟨H, hN, hI, hC, _, M, he⟩ := hmem
    exact h _ (Or.inl ⟨H, hN, hI, hC, M, he⟩)
  · intro h
    exact freeProductZero_implies_classIEquality ((isProjectiveEquality_iff_freeProductZero c).mp h)

theorem classIEquality_iff_freeProductZero {n : ℕ} (c : Word (Fin n) →₀ ℝ) :
    IsClassIProjectiveEquality.{u} c ↔ freeProductImage c = 0 :=
  (classIEquality_iff_finiteRealVectorStates c).trans (isProjectiveEquality_iff_freeProductZero c)

/-- Proposition 6.17(d), for a genuine finite-support equality at all Class-I models
in any carrier universe. -/
theorem classIEquality_native_le_six (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hA : 0 < fourPointInvariant p) (c : Word (Fin 4) →₀ ℝ)
    (hlen : ∀ w ∈ c.support, w.length ≤ 6) (hc : IsClassIProjectiveEquality.{u} c) :
    c.sum (fun w a => a * nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) = 0 := by
  obtain ⟨M, hmatch⟩ := MatchingModels.prop_cer_universalsix_c12 p hp hA
  have hzero := algebraic_wordSum_eq_zero_of_freeProductZero M.toAlgebraic c
    ((classIEquality_iff_freeProductZero c).mp hc)
  rw [Finsupp.sum, ← hzero, Finsupp.sum]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [← hmatch w (hlen w hw), M.toAlgebraic_probability]

end AlbertSequential.AppF
