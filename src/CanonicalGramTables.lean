/- SPDX-License-Identifier: Apache-2.0 -/
module

public import FiniteGramEquivalence

/-! Matrix-only M1--M3 constraints on the fixed complete finite word domain.
Their diagonal image is exactly the set of actual real vector-state tables.
No sparse sublist is asserted to reconstruct a model. -/

@[expose] public section
noncomputable section
namespace AlbertSequential

abbrev ReducedGramIndex (n L : ℕ) :=
  {w : Word (Fin n) // w ∈ reducedWordsUpTo (Fin n) L}

def emptyReducedGramIndex (n L : ℕ) : ReducedGramIndex n L :=
  ⟨[], empty_mem_reducedWordsUpTo L⟩

/-- The word domain is fixed and complete. M2/M3 are literally those of the
existing witness; only its redundant total probability function is removed. -/
structure CanonicalGramConstraints {n L : ℕ}
    (G : Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ) : Prop where
  positive : G.PosSemidef
  normalized : G (emptyReducedGramIndex n L) (emptyReducedGramIndex n L) = 1
  probabilities : ∀ u, 0 ≤ G u u ∧ G u u ≤ 1
  complement : ∀ (u v : ReducedGramIndex n L) (i : Fin n),
    v.val.length < L → IsReducedWord (v.val ++ [(i, true)]) →
    ∀ (hy : v.val ++ [(i, true)] ∈ reducedWordsUpTo (Fin n) L)
      (hn : v.val ++ [(i, false)] ∈ reducedWordsUpTo (Fin n) L),
      G u ⟨v.val ++ [(i, true)], hy⟩ +
        G u ⟨v.val ++ [(i, false)], hn⟩ = G u v
  orthogonal : ∀ (u v : ReducedGramIndex n L) i,
    u.val.getLast? = some (i, true) → v.val.getLast? = some (i, false) →
    G u v = 0

def canonicalGramMatrices (n L : ℕ) :
    Set (Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ) :=
  {G | CanonicalGramConstraints G}

def gramDiagonal {n L : ℕ}
    (G : Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ) :
    ReducedGramIndex n L → ℝ := fun u => G u u

/-- The table of an actual normalized vector and orthogonal projections.
Its coordinates include all and only reduced words through L. -/
def finiteRealProjectiveTables (n L : ℕ) : Set (ReducedGramIndex n L → ℝ) :=
  {t | ∃ d, ∃ M : FiniteRealVectorProjectiveModel n d,
    ∀ u : ReducedGramIndex n L, M.probability u.val = t u}

def totalGramDiagonal {n L : ℕ}
    (G : Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ)
    (w : Word (Fin n)) : ℝ :=
  if h : w ∈ reducedWordsUpTo (Fin n) L then G ⟨w, h⟩ ⟨w, h⟩ else 0

theorem totalGramDiagonal_apply {n L : ℕ}
    (G : Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ)
    (u : ReducedGramIndex n L) : totalGramDiagonal G u.val = G u u := by
  simp only [totalGramDiagonal, dite_eq_left u.property]

def CanonicalGramConstraints.toWitness {n L : ℕ}
    {G : Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ}
    (hG : CanonicalGramConstraints G) : FiniteGramWitness n L (totalGramDiagonal G) where
  words := reducedWordsUpTo (Fin n) L
  complete := mem_reducedWordsUpTo L
  gram := G
  positive := hG.positive
  normalized := by
    change totalGramDiagonal G (emptyReducedGramIndex n L).val = 1
    rw [totalGramDiagonal_apply]
    exact hG.normalized
  probabilities w hw := by
    rw [totalGramDiagonal_apply G ⟨w, hw⟩]
    exact hG.probabilities ⟨w, hw⟩
  diagonal u := (totalGramDiagonal_apply G u).symm
  complement := hG.complement
  orthogonal := hG.orthogonal

theorem gramDiagonal_mem_tables {n L : ℕ}
    {G : Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ}
    (hG : CanonicalGramConstraints G) :
    gramDiagonal G ∈ finiteRealProjectiveTables n L := by
  obtain ⟨M, hM⟩ := finiteGram_reconstruction hG.toWitness
  refine ⟨G.rank, M, fun u => ?_⟩
  exact (hM u.val u.property).trans (totalGramDiagonal_apply G u)

/-- Direct canonical indexing avoids any assumed equality of dependent Gram
index types. This is the same Gram used in vector-state necessity. -/
def RealVectorProjectiveData.canonicalGram {n L : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : RealVectorProjectiveData (Fin n) E) :
    Matrix (ReducedGramIndex n L) (ReducedGramIndex n L) ℝ :=
  fun u v => inner ℝ (M.branchVector u.val) (M.branchVector v.val)

theorem RealVectorProjectiveData.canonicalGram_constraints {n L : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : RealVectorProjectiveData (Fin n) E) :
    CanonicalGramConstraints (M.canonicalGram (L := L)) := by
  classical
  refine {
    positive := realVectorGram_positive _
    normalized := M.probability_nil
    probabilities := fun u => ⟨M.probability_nonneg u.val, M.probability_le_one u.val⟩
    complement := ?_
    orthogonal := ?_ }
  · intro u v i hlen hred hy hn
    change inner ℝ (M.branchVector u.val) (M.branchVector (v.val ++ [(i, true)])) +
      inner ℝ (M.branchVector u.val) (M.branchVector (v.val ++ [(i, false)])) =
      inner ℝ (M.branchVector u.val) (M.branchVector v.val)
    rw [M.branchVector_append_singleton, M.branchVector_append_singleton]
    simp only [RealVectorProjectiveData.outcome, Bool.false_eq_true, ↓reduceIte,
      LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right]
    ring
  · intro u v i hu hv
    obtain ⟨u', hu'⟩ := List.getLast?_eq_some_iff.mp hu
    obtain ⟨v', hv'⟩ := List.getLast?_eq_some_iff.mp hv
    change inner ℝ (M.branchVector u.val) (M.branchVector v.val) = 0
    rw [hu', hv', M.branchVector_append_singleton, M.branchVector_append_singleton]
    exact M.inner_yes_no i _ _

theorem finiteRealProjectiveTables_eq_diagonal_image (n L : ℕ) :
    finiteRealProjectiveTables n L = gramDiagonal '' canonicalGramMatrices n L := by
  ext t
  constructor
  · rintro ⟨d, M, hM⟩
    refine ⟨M.canonicalGram, M.canonicalGram_constraints, ?_⟩
    funext u
    exact hM u
  · rintro ⟨G, hG, rfl⟩
    exact gramDiagonal_mem_tables hG

end AlbertSequential
