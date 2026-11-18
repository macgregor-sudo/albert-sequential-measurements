module

public import TetrahedronEngine
public import Interfaces.AlgebraicReconstruction
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-! Arbitrary-base and arbitrary-order relabelling of the fixed-base
associative tetrahedron engine (`TetrahedronEngine.tetrahedron_annihilates_base`),
plus cyclic and reversal invariance of the denominator-free discriminant
`tetrahedronDiscriminantAtOrder`. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

/-- Reindex pairwise overlap data along `f : Fin 4 → Fin 4`. -/
def reindexOverlap (f : Fin 4 → Fin 4) (o : OverlapData) : OverlapData :=
  fun a b => o (f a) (f b)

/-- Reindex triple shape invariants along `f : Fin 4 → Fin 4`. -/
def reindexTriangle (f : Fin 4 → Fin 4) (R : TriangleData) : TriangleData :=
  fun a b c => R (f a) (f b) (f c)

/-- Exact R1--R3 corner relations of `thm:tetra:algebraic` at an arbitrary
base `j` and ordering `(k, l, m)` of the remaining three indices of `Fin 4`. -/
structure CornerRelationsAtOrder {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (X : Fin 4 → A) (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ) : Prop where
  distinct : Function.Injective (![j, k, l, m] : Fin 4 → Fin 4)
  idempotent : ∀ a, X a * X a = X a
  overlap_symmetric : ∀ a b, o a b = o b a
  triangle_swap : ∀ a b c, R a b c = R b a c ∧ R a b c = R a c b
  pair : ∀ a b, a ≠ b → X a * X b * X a = o a b • X a
  triangle_jkl : X j * (X k * X l + X l * X k) * X j = (2 * R j k l) • X j
  triangle_jlm : X j * (X l * X m + X m * X l) * X j = (2 * R j l m) • X j
  triangle_jmk : X j * (X m * X k + X k * X m) * X j = (2 * R j m k) • X j
  triangle_klm : X k * (X l * X m + X m * X l) * X k = (2 * R k l m) • X k
  quadruple_klm : X j * (X k * X l * X m + X m * X l * X k) * X j = (2 * Q 0) • X j
  quadruple_lmk : X j * (X l * X m * X k + X k * X m * X l) * X j = (2 * Q 1) • X j
  quadruple_mkl : X j * (X m * X k * X l + X l * X k * X m) * X j = (2 * Q 2) • X j

/-- The denominator-free discriminant `Δ_j` (Eq. `eq:tet:Dprime`)
at arbitrary base `j` and ordered remaining vertices `(k, l, m)`, with `Q`
ordered `(klm, lmk, mkl)`. Distinct from the normalized statistic `D_tet`. -/
def tetrahedronDiscriminantAtOrder (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ) : ℝ :=
  let r₁ := R j k l
  let r₂ := R j l m
  let r₃ := R j m k
  let b₁ := r₁ ^ 2 - o j k * o k l * o l j
  let b₂ := r₂ ^ 2 - o j l * o l m * o m j
  let b₃ := r₃ ^ 2 - o j m * o m k * o k j
  let b₁₂ := o j l * Q 0 - r₁ * r₂
  let b₂₃ := o j m * Q 1 - r₂ * r₃
  let b₁₃ := o j k * Q 2 - r₃ * r₁
  let s := o j k * o j l * o j m * R k l m - r₁ * r₂ * r₃ -
    r₁ * b₂₃ - r₂ * b₁₃ - r₃ * b₁₂
  show ℝ from -(b₁ * b₂ * b₃ + 2 * b₁₂ * b₂₃ * b₁₃ -
    b₁ * b₂₃ ^ 2 - b₂ * b₁₃ ^ 2 - b₃ * b₁₂ ^ 2) - s ^ 2

private theorem perm_eq_vec (σ : Equiv.Perm (Fin 4)) :
    (![σ 0, σ 1, σ 2, σ 3] : Fin 4 → Fin 4) = σ := by
  funext a
  fin_cases a <;> rfl

theorem tetrahedronDiscriminantAtOrder_eq_reindex
    (o : OverlapData) (R : TriangleData) (j k l m : Fin 4) (Q : Fin 3 → ℝ) :
    tetrahedronDiscriminantAtOrder o R j k l m Q =
      tetrahedronDiscriminant (reindexOverlap ![j, k, l, m] o)
        (reindexTriangle ![j, k, l, m] R) Q := rfl

theorem tetrahedronDiscriminant_reindex_perm
    (o : OverlapData) (R : TriangleData)
    (σ : Equiv.Perm (Fin 4)) (Q : Fin 3 → ℝ) :
    tetrahedronDiscriminant (reindexOverlap σ o) (reindexTriangle σ R) Q =
      tetrahedronDiscriminantAtOrder o R (σ 0) (σ 1) (σ 2) (σ 3) Q := by
  rw [tetrahedronDiscriminantAtOrder_eq_reindex, perm_eq_vec σ]

theorem cornerRelations_perm_iff
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    (X : Fin 4 → A) (o : OverlapData) (R : TriangleData)
    (σ : Equiv.Perm (Fin 4)) (Q : Fin 3 → ℝ) :
    CornerRelations (X ∘ σ) (reindexOverlap σ o) (reindexTriangle σ R) Q ↔
      CornerRelationsAtOrder X o R (σ 0) (σ 1) (σ 2) (σ 3) Q := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [perm_eq_vec σ]
      exact σ.injective
    · intro a
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        h.idempotent (σ.symm a)
    · intro a b
      simpa only [reindexOverlap, Equiv.apply_symm_apply] using
        h.overlap_symmetric (σ.symm a) (σ.symm b)
    · intro a b c
      simpa only [reindexTriangle, Equiv.apply_symm_apply] using
        h.triangle_swap (σ.symm a) (σ.symm b) (σ.symm c)
    · intro a b hab
      have hne : σ.symm a ≠ σ.symm b := fun h' => hab (σ.symm.injective h')
      simpa only [Function.comp_apply, reindexOverlap, Equiv.apply_symm_apply] using
        h.pair (σ.symm a) (σ.symm b) hne
    · exact h.triangle_012
    · exact h.triangle_023
    · exact h.triangle_031
    · exact h.triangle_123
    · exact h.quadruple_123
    · exact h.quadruple_231
    · exact h.quadruple_312
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      exact h.idempotent (σ a)
    · intro a b
      exact h.overlap_symmetric (σ a) (σ b)
    · intro a b c
      exact h.triangle_swap (σ a) (σ b) (σ c)
    · intro a b hab
      exact h.pair (σ a) (σ b) (fun h' => hab (σ.injective h'))
    · exact h.triangle_jkl
    · exact h.triangle_jlm
    · exact h.triangle_jmk
    · exact h.triangle_klm
    · exact h.quadruple_klm
    · exact h.quadruple_lmk
    · exact h.quadruple_mkl

theorem tetrahedron_annihilates_perm
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (X : Fin 4 → A) (o : OverlapData) (R : TriangleData)
    (σ : Equiv.Perm (Fin 4)) (Q : Fin 3 → ℝ)
    (hR : CornerRelationsAtOrder X o R (σ 0) (σ 1) (σ 2) (σ 3) Q) :
    tetrahedronDiscriminantAtOrder o R (σ 0) (σ 1) (σ 2) (σ 3) Q • X (σ 0) = 0 := by
  have hbase := tetrahedron_annihilates_base (X ∘ σ) (reindexOverlap σ o)
    (reindexTriangle σ R) Q ((cornerRelations_perm_iff X o R σ Q).mpr hR)
  simpa only [tetrahedronDiscriminant_reindex_perm, Function.comp_apply] using hbase

theorem tetrahedron_annihilates_at_order
    {A : Type*} [NonUnitalRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (X : Fin 4 → A) (o : OverlapData) (R : TriangleData)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ)
    (hR : CornerRelationsAtOrder X o R j k l m Q) :
    tetrahedronDiscriminantAtOrder o R j k l m Q • X j = 0 := by
  let σ : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective (![j, k, l, m] : Fin 4 → Fin 4)
      (Finite.injective_iff_bijective.mp hR.distinct)
  have h0 : σ 0 = j := rfl
  have h1 : σ 1 = k := rfl
  have h2 : σ 2 = l := rfl
  have h3 : σ 3 = m := rfl
  have hR' : CornerRelationsAtOrder X o R (σ 0) (σ 1) (σ 2) (σ 3) Q := by
    simpa only [h0, h1, h2, h3] using hR
  simpa only [h0, h1, h2, h3] using tetrahedron_annihilates_perm X o R σ Q hR'

/-- Cyclic invariance of `Δ_j` under `(k, l, m) ↦ (l, m, k)` and `(Q₀, Q₁, Q₂) ↦ (Q₁, Q₂, Q₀)`. -/
theorem tetrahedronDiscriminantAtOrder_cyclic
    (o : OverlapData) (R : TriangleData)
    (hR : ∀ a b c, R a b c = R b a c ∧ R a b c = R a c b)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ) :
    tetrahedronDiscriminantAtOrder o R j l m k ![Q 1, Q 2, Q 0] =
      tetrahedronDiscriminantAtOrder o R j k l m Q := by
  have hQ0 : (![Q 1, Q 2, Q 0] : Fin 3 → ℝ) 0 = Q 1 := rfl
  have hQ1 : (![Q 1, Q 2, Q 0] : Fin 3 → ℝ) 1 = Q 2 := rfl
  have hQ2 : (![Q 1, Q 2, Q 0] : Fin 3 → ℝ) 2 = Q 0 := rfl
  have hRlmk : R l m k = R k l m := by
    rw [(hR k l m).1, (hR l k m).2]
  dsimp only [tetrahedronDiscriminantAtOrder]
  rw [hQ0, hQ1, hQ2, hRlmk]
  ring

/-- Reversal invariance of `Δ_j` under `(k, l, m) ↦ (k, m, l)`: exchanges indices
`1 ↔ 3` of `B` and corresponds to reversing triples `(k,m,l), (m,l,k), (l,k,m)`
into `(l,m,k), (k,l,m), (m,k,l)`, so `Q' = ![Q 1, Q 0, Q 2]`. -/
theorem tetrahedronDiscriminantAtOrder_swap
    (o : OverlapData) (R : TriangleData)
    (ho : ∀ a b, o a b = o b a)
    (hR : ∀ a b c, R a b c = R b a c ∧ R a b c = R a c b)
    (j k l m : Fin 4) (Q : Fin 3 → ℝ) :
    tetrahedronDiscriminantAtOrder o R j k m l ![Q 1, Q 0, Q 2] =
      tetrahedronDiscriminantAtOrder o R j k l m Q := by
  have hQ0 : (![Q 1, Q 0, Q 2] : Fin 3 → ℝ) 0 = Q 1 := rfl
  have hQ1 : (![Q 1, Q 0, Q 2] : Fin 3 → ℝ) 1 = Q 0 := rfl
  have hQ2 : (![Q 1, Q 0, Q 2] : Fin 3 → ℝ) 2 = Q 2 := rfl
  have hr1 : R j k m = R j m k := (hR j k m).2
  have hr2 : R j m l = R j l m := (hR j m l).2
  have hr3 : R j l k = R j k l := (hR j l k).2
  have hRf : R k m l = R k l m := (hR k m l).2
  have hnu1 : o j k * o k m * o m j = o j m * o m k * o k j := by
    rw [ho j k, ho k m, ho m j]
    ring
  have hnu2 : o j m * o m l * o l j = o j l * o l m * o m j := by
    rw [ho j m, ho m l, ho l j]
    ring
  have hnu3 : o j l * o l k * o k j = o j k * o k l * o l j := by
    rw [ho j l, ho l k, ho k j]
    ring
  dsimp only [tetrahedronDiscriminantAtOrder]
  rw [hQ0, hQ1, hQ2, hr1, hr2, hr3, hRf, hnu1, hnu2, hnu3]
  ring

end AlbertSequential
