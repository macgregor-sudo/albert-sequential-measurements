/- SPDX-License-Identifier: Apache-2.0 -/
module
public import FieldDimensionTableEquivalence
public import ChronologicalWords
public import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace AlbertSequential.AlgebraicProjectiveData

variable {I A B : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A] [Ring B] [StarRing B] [Module ℝ B] [IsScalarTower ℝ B B]
  [SMulCommClass ℝ B B] [StarModule ℝ B]

/-- Same tests on two actual associative operator blocks, with the weighted state. -/
def weightedProduct (M : AlgebraicProjectiveData I A) (N : AlgebraicProjectiveData I B)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    AlgebraicProjectiveData I (A × B) where
  projection i := (M.projection i, N.projection i)
  idempotent i := Prod.ext (M.idempotent i) (N.idempotent i)
  selfAdjoint i := Prod.ext (M.selfAdjoint i) (N.selfAdjoint i)
  state := a • (M.state.comp (LinearMap.fst ℝ A B)) + b • (N.state.comp (LinearMap.snd ℝ A B))
  state_unit := by
    change a * M.state 1 + b * N.state 1 = 1
    simpa [M.state_unit,N.state_unit] using hab
  state_star x := by
    change a * M.state (star x.1) + b * N.state (star x.2) = a * M.state x.1 + b * N.state x.2
    rw [M.state_star,N.state_star]
  state_positive x := add_nonneg (mul_nonneg ha (M.state_positive x.1)) (mul_nonneg hb (N.state_positive x.2))

theorem weightedProduct_probability (M : AlgebraicProjectiveData I A) (N : AlgebraicProjectiveData I B)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (w : Word I) :
    (M.weightedProduct N a b ha hb hab).probability w = a * M.probability w + b * N.probability w := by
  let proj : I → A × B := fun i => (M.projection i,N.projection i)
  have hout (q : Outcome I) : algebraicOutcome proj q =
      (algebraicOutcome M.projection q,algebraicOutcome N.projection q) := by
    rcases q with ⟨i,c⟩
    cases c <;> rfl
  have hamp (v : Word I) : wordAmplitude proj v =
      (wordAmplitude M.projection v,wordAmplitude N.projection v) := by
    induction v with
    | nil => rfl
    | cons q v ih =>
      rw [wordAmplitude_cons,wordAmplitude_cons,wordAmplitude_cons,ih,hout]
      rfl
  change a * M.state (wordOperator proj w).1 + b * N.state (wordOperator proj w).2 = _
  simp only [wordOperator,hamp]
  rfl

end AlbertSequential.AlgebraicProjectiveData

namespace AlbertSequential
universe u

/-- Convexity here concerns actual models reproducing every word. -/
theorem convex_hilbertProjectiveTables_real (n : ℕ) : Convex ℝ (hilbertProjectiveTables.{u} ℝ n) := by
  intro f hf g hg a b ha hb hab
  rcases hf with ⟨H,hHN,hHI,hHC,M,hM⟩
  let := hHN
  let := hHI
  let := hHC
  rcases hg with ⟨K,hKN,hKI,hKC,N,hN⟩
  let := hKN
  let := hKI
  let := hKC
  let W := M.toAlgebraic.weightedProduct N.toAlgebraic a b ha hb hab
  apply mem_hilbertProjectiveTables_of_model (cyclicHilbertModel W)
  intro w
  rw [cyclicHilbertModel_probability]
  dsimp only [W]
  rw [AlgebraicProjectiveData.weightedProduct_probability,hM,hN]
  rfl

theorem convex_hilbertProjectiveTables_complex (n : ℕ) :
    Convex ℝ (hilbertProjectiveTables.{u} ℂ n) := by
  rw [← real_complex_projectiveTables_eq]
  exact convex_hilbertProjectiveTables_real n

theorem convex_quaternionicProjectiveTables (n : ℕ) : Convex ℝ (quaternionicProjectiveTables.{u} n) := by
  rw [← real_quaternionic_projectiveTables_eq]
  exact convex_hilbertProjectiveTables_real n

end AlbertSequential
