/- Apache-2.0. Part of the proofs in `Solution`: transfer of the development's theorems to the
definitions of `Challenge`. -/
module

public import Bridge.Albert
public import NativeIdempotentClassification

/-!
# Atoms are the primitive idempotents

The Challenge defines an atom as an idempotent of trace one (`IsAtom`). The paper's atoms are the
primitive idempotents: nonzero idempotents that are not the sum of two nonzero orthogonal
idempotents. The two agree in `J`:

* an idempotent has trace `0, 1, 2` or `3` (`native_idempotent_trace_cases`), and trace `0` only
  for `0` (positivity, `isPositive_trace_eq_zero`); a sum of two nonzero orthogonal idempotents
  therefore has trace at least two;
* conversely an idempotent of trace two or three diagonalizes under an automorphism of `J`
  (`nativeDiagonalization`) to a diagonal `0/1` matrix with at least two entries `1`; splitting
  off one diagonal unit and transporting back gives two nonzero orthogonal idempotents.

Orthogonality of idempotents is `q ∘ r = 0`.
-/

@[expose] public section
noncomputable section

namespace AlbertSequential.NativeAnalysis

open AlbertSequential

/-- A nonzero idempotent has trace at least one. -/
theorem one_le_trace_of_idempotent {q : Albert} (hq : jordanMul q q = q) (hne : q ≠ 0) :
    1 ≤ albertTrace q := by
  rcases native_idempotent_trace_cases q hq with h | h | h | h
  · exact absurd ((isPositive_trace_eq_zero q (isPositive_idempotent q hq)).mp h) hne
  all_goals linarith

/-- An idempotent of trace at least two is a sum of two nonzero orthogonal idempotents. -/
theorem exists_orthogonal_split {p : Albert} (hp : jordanMul p p = p) (h2 : 2 ≤ albertTrace p) :
    ∃ q r : Albert, jordanMul q q = q ∧ jordanMul r r = r ∧ q ≠ 0 ∧ r ≠ 0 ∧
      jordanMul q r = 0 ∧ p = q + r := by
  classical
  obtain ⟨g, d, hg⟩ := nativeDiagonalization p
  have hid : jordanMul (diagonalElement d) (diagonalElement d) = diagonalElement d := by
    rw [← hg, ← g.preserves_product, hp]
  have hbits (j : Fin 3) : d j = 0 ∨ d j = 1 := by
    have h := congrArg (fun x : Albert => x.1 j) hid
    rw [diagonal_square] at h
    have h' : d j ^ 2 = d j := h
    have hm : d j * (d j - 1) = 0 := by nlinarith [h']
    rcases mul_eq_zero.mp hm with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have htr : albertTrace p = ∑ j, d j :=
    ((g.preserves_trace p).symm.trans (congrArg albertTrace hg)).trans (diagonal_trace d)
  obtain ⟨i, hi⟩ : ∃ i, d i = 1 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ j, d j = 0 := fun j => (hbits j).resolve_right (hcon j)
    rw [htr, Finset.sum_eq_zero fun j _ => h0 j] at h2
    norm_num at h2
  let e : Fin 3 → ℝ := fun j => if j = i then 1 else 0
  let d' : Fin 3 → ℝ := fun j => d j - e j
  let ginv := g.linearEquiv.symm
  have hmul : ∀ x y, ginv (jordanMul x y) = jordanMul (ginv x) (ginv y) := by
    intro x y
    apply g.linearEquiv.injective
    rw [g.preserves_product]
    simp [ginv]
  have htrinv : ∀ x, albertTrace (ginv x) = albertTrace x := by
    intro x
    rw [← g.preserves_trace (ginv x)]
    simp [ginv]
  have hsum_e : ∑ j, e j = 1 := by simp [e]
  have he_sq : (fun j => e j ^ 2) = e := by
    funext j
    by_cases hj : j = i <;> simp [e, hj]
  have hd'_sq : (fun j => d' j ^ 2) = d' := by
    funext j
    by_cases hj : j = i
    · simp [d', e, hj, hi]
    · rcases hbits j with h | h <;> simp [d', e, hj, h]
  have hed' : (fun j => e j * d' j) = fun _ => (0 : ℝ) := by
    funext j
    by_cases hj : j = i
    · simp [d', e, hj, hi]
    · simp [e, hj]
  have hdiag0 : diagonalElement (fun _ => (0 : ℝ)) = 0 := rfl
  refine ⟨ginv (diagonalElement e), ginv (diagonalElement d'), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmul, diagonal_square, he_sq]
  · rw [← hmul, diagonal_square, hd'_sq]
  · intro h
    have := htrinv (diagonalElement e)
    rw [h, albertTrace_zero, diagonal_trace, hsum_e] at this
    norm_num at this
  · intro h
    have := htrinv (diagonalElement d')
    rw [h, albertTrace_zero, diagonal_trace] at this
    have hs : ∑ j, d' j = ∑ j, d j - 1 := by
      simp only [d', Finset.sum_sub_distrib, hsum_e]
    rw [hs, ← htr] at this
    linarith
  · rw [← hmul, diagonal_product, hed', hdiag0, map_zero]
  · rw [← map_add]
    apply g.linearEquiv.injective
    rw [hg]
    simp only [ginv, LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · funext j
      change d j = e j + (d j - e j)
      ring
    · funext j
      change (0 : Octonion) = 0 + 0
      rw [add_zero]

/-- **Atoms are the primitive idempotents** (native form). -/
theorem isAtom_iff_primitive (p : Albert) :
    IsAtom p ↔ jordanMul p p = p ∧ p ≠ 0 ∧
      ¬ ∃ q r : Albert, jordanMul q q = q ∧ jordanMul r r = r ∧ q ≠ 0 ∧ r ≠ 0 ∧
        jordanMul q r = 0 ∧ p = q + r := by
  constructor
  · rintro ⟨hid, htr⟩
    refine ⟨hid, fun h0 => ?_, ?_⟩
    · rw [h0, albertTrace_zero] at htr
      norm_num at htr
    · rintro ⟨q, r, hq, hr, hq0, hr0, _, rfl⟩
      have h1 := one_le_trace_of_idempotent hq hq0
      have h2 := one_le_trace_of_idempotent hr hr0
      rw [albertTrace_add] at htr
      linarith
  · rintro ⟨hid, hne, hind⟩
    refine ⟨hid, ?_⟩
    rcases native_idempotent_trace_cases p hid with h | h | h | h
    · exact absurd ((isPositive_trace_eq_zero p (isPositive_idempotent p hid)).mp h) hne
    · exact h
    all_goals exact absurd (exists_orthogonal_split hid (by linarith)) hind

end AlbertSequential.NativeAnalysis

namespace AlbertChallenge.Bridge

open AlbertChallenge

theorem zero_toT : (0 : AlbertSequential.Albert) = toT 0 := rfl

theorem add_toT (x y : Albert) : toT x + toT y = toT (x + y) := rfl

/-- **Atoms are the primitive idempotents**, in the Challenge's terms. -/
theorem isAtom_iff_primitive_bridge (p : Albert) :
    IsAtom p ↔ jordanMul p p = p ∧ p ≠ 0 ∧
      ¬ ∃ q r : Albert, jordanMul q q = q ∧ jordanMul r r = r ∧ q ≠ 0 ∧ r ≠ 0 ∧
        jordanMul q r = 0 ∧ p = q + r := by
  rw [← isAtom_toT, AlbertSequential.NativeAnalysis.isAtom_iff_primitive]
  simp only [jordanMul_toT, zero_toT, toT_inj, ne_eq]
  constructor
  · rintro ⟨hid, hne, hind⟩
    refine ⟨hid, hne, fun ⟨q, r, hq, hr, hq0, hr0, hqr, hpqr⟩ => hind ⟨toT q, toT r, ?_⟩⟩
    simp only [jordanMul_toT, toT_inj, add_toT]
    exact ⟨hq, hr, hq0, hr0, hqr, hpqr⟩
  · rintro ⟨hid, hne, hind⟩
    refine ⟨hid, hne, fun ⟨q, r, hq, hr, hq0, hr0, hqr, hpqr⟩ => hind ⟨q, r, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact (jordanMul_eq q q).trans hq
    · exact (jordanMul_eq r r).trans hr
    · exact hq0
    · exact hr0
    · exact (jordanMul_eq q r).trans hqr
    · exact (toT_inj _ _).mp (hpqr.trans (add_toT q r))

end AlbertChallenge.Bridge
