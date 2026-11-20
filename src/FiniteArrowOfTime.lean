/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Interfaces.InstrumentsAndCompactness
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! Finite arrow-of-time tables and the classical history instrument that realizes them. -/
@[expose] public section
noncomputable section

namespace AlbertSequential.FiniteArrowOfTime

open scoped BigOperators

variable {I : Type*} {A : I → Type*} {N : ℕ}

abbrev History {I : Type*} (A : I → Type*) (N : ℕ) :=
  {w : InstrumentWord A // w.length ≤ N}

abbrev Table {I : Type*} (A : I → Type*) (N : ℕ) := History A N → ℝ

def empty : History A N := ⟨[], Nat.zero_le _⟩

def snoc (h : History A N) (hn : h.val.length < N) (a : Sigma A) : History A N :=
  ⟨h.val ++ [a], by simpa using hn⟩

/-- The finite register stores the history, and stays at a terminal history past the horizon. -/
def advance (h : History A N) (a : Sigma A) : History A N :=
  if hn : h.val.length < N then snoc h hn a else h

structure IsCausal [∀ i, Fintype (A i)] (t : Table A N) : Prop where
  root : t empty = 1
  marginal : ∀ (h : History A N) (hn : h.val.length < N) (i : I),
    ∑ a : A i, t (snoc h hn ⟨i,a⟩) = t h

/-- A classical instrument chooses an outcome for each independent setting and appends it. -/
structure Register {I : Type*} (A : I → Type*) (N : ℕ) [∀ i, Fintype (A i)] where
  readout : History A N → (i : I) → A i → ℝ
  nonneg : ∀ h i a, 0 ≤ readout h i a
  normalized : ∀ h i, ∑ a : A i, readout h i a = 1

variable [∀ i, Fintype (A i)]

def Register.run (R : Register A N) : History A N → InstrumentWord A → ℝ
  | _, [] => 1
  | h, a :: w => R.readout h a.1 a.2 * R.run (advance h a) w

def Register.table (R : Register A N) : Table A N := fun h => R.run empty h.val

private theorem Register.run_nonneg (R : Register A N) (h : History A N)
    (w : InstrumentWord A) : 0 ≤ R.run h w := by
  induction w generalizing h with
  | nil => exact zero_le_one
  | cons a w ih => exact mul_nonneg (R.nonneg ..) (ih _)

private theorem Register.run_marginal (R : Register A N) (h : History A N)
    (w : InstrumentWord A) (i : I) :
    (∑ a : A i, R.run h (w ++ [⟨i,a⟩])) = R.run h w := by
  induction w generalizing h with
  | nil =>
    simpa only [List.nil_append, Register.run, mul_one] using R.normalized h i
  | cons a w ih =>
    simp only [List.cons_append, Register.run, ← Finset.mul_sum, ih _]

theorem Register.table_causal (R : Register A N) : IsCausal R.table where
  root := rfl
  marginal h _hn i := R.run_marginal empty h.val i

private theorem Register.run_pos (R : Register A N)
    (hR : ∀ h i a, 0 < R.readout h i a) (h : History A N) (w : InstrumentWord A) :
    0 < R.run h w := by
  induction w generalizing h with
  | nil => exact zero_lt_one
  | cons a w ih => exact mul_pos (hR ..) (ih _)

variable [∀ i, Nonempty (A i)]

private theorem uniform_pos (i : I) : 0 < (Fintype.card (A i) : ℝ)⁻¹ :=
  inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

private theorem uniform_sum (i : I) : (∑ _ : A i, (Fintype.card (A i) : ℝ)⁻¹) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀
    (Nat.cast_pos.mpr Fintype.card_pos).ne']

private def uniformRegister : Register A N where
  readout _ i _ := (Fintype.card (A i) : ℝ)⁻¹
  nonneg _ i _ := (uniform_pos i).le
  normalized _ i := uniform_sum i

private def conditional (t : Table A N) (h : History A N) (i : I) (a : A i) : ℝ :=
  if h.val.length < N ∧ 0 < t h then t (advance h ⟨i,a⟩) / t h
  else (Fintype.card (A i) : ℝ)⁻¹

omit [∀ i, Nonempty (A i)] in
private theorem conditional_mul (t : Table A N) (ht : IsCausal t) (hp : ∀ h, 0 ≤ t h)
    (h : History A N) (hl : h.val.length < N) (i : I) (a : A i) :
    t h * conditional t h i a = t (snoc h hl ⟨i,a⟩) := by
  by_cases hpos : 0 < t h
  · rw [conditional, ite_eq_left ⟨hl, hpos⟩, advance, dite_eq_left hl]
    field_simp
  · have hz : t h = 0 := le_antisymm (le_of_not_gt hpos) (hp h)
    have hle : t (snoc h hl ⟨i,a⟩) ≤ t h := by
      rw [← ht.marginal h hl i]
      exact Finset.single_le_sum (fun b _ => hp (snoc h hl ⟨i,b⟩)) (Finset.mem_univ a)
    rw [hz, zero_mul]
    exact (le_antisymm (hle.trans_eq hz) (hp _)).symm

private def fromTable (t : Table A N) (ht : IsCausal t) (hp : ∀ h, 0 ≤ t h) : Register A N where
  readout := conditional t
  nonneg h i a := by
    by_cases hpos : h.val.length < N ∧ 0 < t h
    · rw [conditional, ite_eq_left hpos]; exact div_nonneg (hp _) hpos.2.le
    · rw [conditional, ite_eq_right hpos]; exact (uniform_pos i).le
  normalized h i := by
    by_cases hpos : h.val.length < N ∧ 0 < t h
    · simp only [conditional, ite_eq_left hpos, advance, dite_eq_left hpos.1]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ht.marginal, mul_inv_cancel₀ hpos.2.ne']
    · simp only [conditional, ite_eq_right hpos, uniform_sum]

private theorem fromTable_run (t : Table A N) (ht : IsCausal t) (hp : ∀ h, 0 ≤ t h)
    (h : History A N) (w : InstrumentWord A) (hw : (h.val ++ w).length ≤ N) :
    t h * (fromTable t ht hp).run h w = t ⟨h.val ++ w, hw⟩ := by
  induction w generalizing h with
  | nil => simp only [Register.run, mul_one, List.append_nil]
  | cons a w ih =>
    have hl : h.val.length < N := by simp only [List.length_append, List.length_cons] at hw; omega
    have he : advance h a = snoc h hl a := dite_eq_left hl
    have H : ((snoc h hl a).val ++ w).length ≤ N := by simpa [snoc, List.append_assoc] using hw
    rw [Register.run, ← mul_assoc]
    change t h * conditional t h a.1 a.2 * (fromTable t ht hp).run (advance h a) w = _
    rw [conditional_mul t ht hp h hl, he, ih _ H]
    congr 1
    apply Subtype.ext
    simp [snoc, List.append_assoc]

/-- Nonnegative arrow-of-time tables are exactly the finite history register tables. -/
theorem exists_register_iff (t : Table A N) :
    (∃ R : Register A N, R.table = t) ↔ IsCausal t ∧ ∀ h, 0 ≤ t h := by
  constructor
  · rintro ⟨R, rfl⟩
    exact ⟨R.table_causal, fun h => R.run_nonneg empty h.val⟩
  · rintro ⟨ht, hp⟩
    refine ⟨fromTable t ht hp, ?_⟩
    funext h
    have H : ((empty : History A N).val ++ h.val).length ≤ N := h.property
    have he := fromTable_run t ht hp empty h.val H
    rw [ht.root, one_mul] at he
    exact he

private def causalAffineSpace : AffineSubspace ℝ (Table A N) where
  carrier := {t | IsCausal t}
  smul_vsub_vadd_mem' c u v w hu hv hw := by
    change IsCausal (c • (u - v) + w)
    constructor
    · change c * (u empty - v empty) + w empty = 1
      rw [hu.root, hv.root, hw.root, sub_self, mul_zero, zero_add]
    · intro h hn i
      change (∑ a : A i, (c * (u (snoc h hn ⟨i,a⟩) - v (snoc h hn ⟨i,a⟩)) +
        w (snoc h hn ⟨i,a⟩))) = c * (u h - v h) + w h
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        hu.marginal, hv.marginal, hw.marginal]

variable [Finite I]

private theorem exists_positive_perturbation (t : Table A N) :
    let u := (uniformRegister : Register A N).table
    ∃ r : ℝ, 0 < r ∧ ∀ h : History A N, 0 < u h + r * (t h - u h) := by
  classical
  intro u
  let _ : Finite (History A N) := (List.finite_length_le (Sigma A) N).to_subtype
  let _ : Fintype (History A N) := Fintype.ofFinite _
  let _ : Nonempty (History A N) := ⟨empty⟩
  have hu (h : History A N) : 0 < u h :=
    uniformRegister.run_pos (fun _ i _ => uniform_pos i) empty h.val
  let radius (h : History A N) := u h / (|t h - u h| + 1)
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ radius Finset.univ_nonempty
  have hr : 0 < radius m := div_pos (hu _) (by positivity)
  refine ⟨radius m, hr, fun h => ?_⟩
  have hh : radius m ≤ radius h := hm h (Finset.mem_univ h)
  have hbound : radius m * (|t h - u h| + 1) ≤ u h :=
    (le_div_iff₀ (by positivity)).mp hh
  have hlower := mul_le_mul_of_nonneg_left (neg_abs_le (t h - u h)) hr.le
  rw [mul_add, mul_one] at hbound
  rw [mul_neg] at hlower
  change 0 < u h + radius m * (t h - u h)
  linarith

/-- The affine hull of the realizable tables consists of precisely the normalized signed
tables satisfying arrow-of-time marginalization. -/
theorem mem_affineSpan_registerTables_iff (t : Table A N) :
    t ∈ affineSpan ℝ (Set.range (Register.table (A := A) (N := N))) ↔ IsCausal t := by
  let S := Set.range (Register.table (A := A) (N := N))
  constructor
  · intro h
    exact (affineSpan_le.mpr (by rintro _ ⟨R,rfl⟩; exact R.table_causal) :
      affineSpan ℝ S ≤ causalAffineSpace) h
  · intro ht
    let u := (uniformRegister : Register A N).table
    obtain ⟨r,hr,hp⟩ := exists_positive_perturbation t
    let s := r • (t - u) + u
    have hu : u ∈ causalAffineSpace := uniformRegister.table_causal
    have hs : s ∈ causalAffineSpace :=
      (causalAffineSpace (A := A) (N := N)).smul_vsub_vadd_mem r (show t ∈ _ from ht) hu hu
    obtain ⟨R, hR⟩ := (exists_register_iff s).mpr ⟨hs, fun h => by
      change 0 ≤ (r • (t - u) + u) h
      rw [add_comm]
      exact (hp h).le⟩
    have hu' : u ∈ affineSpan ℝ S := subset_affineSpan ℝ S ⟨uniformRegister,rfl⟩
    have hs' : s ∈ affineSpan ℝ S := subset_affineSpan ℝ S ⟨R,hR⟩
    have h := (affineSpan ℝ S).smul_vsub_vadd_mem r⁻¹ hs' hu' hu'
    have e : r⁻¹ • (s - u) + u = t := by
      rw [show s - u = r • (t - u) by simp [s], smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
        sub_add_cancel]
    exact e ▸ h

end AlbertSequential.FiniteArrowOfTime
