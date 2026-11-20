module

import FiniteArrowOfTimeCP

set_option autoImplicit false

open AlbertSequential AlbertSequential.FiniteArrowOfTime
open scoped BigOperators

universe u v

variable {I : Type u} {A : I → Type v} [Finite I]
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

example {N d : ℕ} (R : Register A N) (e : History A N ≃ Fin d)
    (i : I) (a : A i) (k l : Fin d × Fin d) (h : k ≠ l) :
    (R.diagonalCP e (fun _ : Unit => empty)).2 i a k l = 0 := by
  unfold Register.diagonalCP
  exact Matrix.diagonal_apply_ne _ h

example (N : ℕ) (t : Table A N) :
    (∃ (d : ℕ) (r : RawFiniteCPModel d Unit I A),
      IsNormalizedFiniteCPModel r ∧ ∀ h : History A N,
        finiteCPWordProbability r () h.val = t h) ↔
      t empty = 1 ∧ (∀ (h : History A N) (hn : h.val.length < N) (i : I),
        (∑ a : A i, t (snoc h hn ⟨i, a⟩)) = t h) ∧ (∀ h, 0 ≤ t h) := by
  rw [show (∃ (d : ℕ) (r : RawFiniteCPModel d Unit I A),
    IsNormalizedFiniteCPModel r ∧ ∀ h : History A N,
      finiteCPWordProbability r () h.val = t h) = HasFiniteCPRealization t by rfl,
    exists_diagonalCP_iff]
  exact ⟨fun h => ⟨h.1.root, h.1.marginal, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem finiteCP_only_causal_affine_equalities {N : ℕ}
    (f : Table A N →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ t, HasFiniteCPRealization t → f t = c) ↔ (∀ t, IsCausal t → f t = c) := by
  constructor
  · intro he t ht
    have hs := (mem_affineSpan_cpTables_iff t).mpr ht
    refine affineSpan_induction (p := fun s => f s = c) hs he ?_
    intro a p q r hp hq hr
    change f (a • (p - q) + r) = c
    simp [hp, hq, hr]
  · intro he t ht
    exact he t ((exists_diagonalCP_iff t).mp ht).1

#print axioms finiteCP_only_causal_affine_equalities
