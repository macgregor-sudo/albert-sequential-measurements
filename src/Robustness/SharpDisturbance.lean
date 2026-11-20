/- SPDX-License-Identifier: Apache-2.0 -/
module
public import Robustness.PositiveInstrumentStability

@[expose] public section
noncomputable section
namespace AlbertSequential.SharpDisturbance
variable {E I : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual chronological composition, retained as a linear map. -/
def wordMap (F : I → E →ₗ[ℝ] E) : List I → E →ₗ[ℝ] E
  | [] => LinearMap.id
  | i::w => (wordMap F w).comp (F i)

theorem wordMap_eq_chronologicalState (F : I → E →ₗ[ℝ] E) (w : List I) (x : E) :
    wordMap F w x = chronologicalState (fun i => F i) x w := by
  induction w generalizing x with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- Six hybrid replacements suffice. The final press has the same trace for the two
instruments. No normalization of a zero-mass history is used. -/
theorem exists_disturbance {C : Set E} (τ : E →ₗ[ℝ] ℝ)
    (hn : ∀ x ∈ C, 0 ≤ τ x) (hz : ∀ x ∈ C, τ x = 0 → x = 0)
    (hnorm : ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → t • x ∈ C)
    (F L : I → E →ₗ[ℝ] E) (hL : ∀ i x, x ∈ C → L i x ∈ C)
    (hdec : ∀ i x, x ∈ C → τ (L i x) ≤ τ x)
    (htr : ∀ i x, τ (F i x) = τ (L i x))
    (hFL : ∀ i x, F i (L i x) = F i x)
    (hid : ∀ i x, L i (L i x) = L i x)
    {x : E} (hx : x ∈ C) {a : I} (w : List I) (hlen : w.length ≤ 6)
    (hmass : τ (L a x) ≤ 1/3) {δ : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ |τ (wordMap F (a::w) x) - τ (wordMap L (a::w) x)|) :
    ∃ (q : I) (σ : E) (u : List I), σ ∈ C ∧ τ σ = 1 ∧ τ (F q σ) = 1 ∧
      u ≠ [] ∧ u.length ≤ 6 ∧ δ/2 ≤ |τ (wordMap F (q::u) σ) - τ (wordMap F u σ)| := by
  classical
  by_contra bad
  have local_bound (q : I) (y : E) (hy : y ∈ C) (hfix : L q y = y)
      (hm : τ y ≤ 1/3) (u : List I) (hu : u ≠ []) (hu6 : u.length ≤ 6) :
      |τ (wordMap F u (F q y)) - τ (wordMap F u y)| < δ / 6 := by
    by_cases h0 : τ y = 0
    · have he := hz y hy h0
      subst y; simp; linarith
    let σ := (τ y)⁻¹ • y
    have hpos := lt_of_le_of_ne (hn y hy) (Ne.symm h0)
    have hs : σ ∈ C := hnorm y hy _ (inv_nonneg.mpr hpos.le)
    have ht : τ σ = 1 := by simp [σ, h0]
    have hf : τ (F q σ) = 1 := by rw [htr]; simpa [σ,hfix] using ht
    have hsmall : |τ (wordMap F (q::u) σ) - τ (wordMap F u σ)| < δ/2 :=
      lt_of_not_ge fun h => bad ⟨q,σ,u,hs,ht,hf,hu,hu6,h⟩
    have he : y = τ y • σ := by simp [σ,smul_smul,h0]
    calc
      _ = τ y * |τ (wordMap F (q::u) σ) - τ (wordMap F u σ)| := by
        conv_lhs => rw [he]
        simp only [wordMap, LinearMap.comp_apply, map_smul, smul_eq_mul, ← mul_sub,
          abs_mul, abs_of_pos hpos]
      _ < τ y * (δ/2) := mul_lt_mul_of_pos_left hsmall hpos
      _ ≤ δ/6 := by nlinarith
  have hybrid (v : List I) : ∀ (q : I) (y : E), y ∈ C → τ (L q y) ≤ 1/3 → v.length ≤ 6 →
      |τ (wordMap F (q::v) y) - τ (wordMap L (q::v) y)| ≤ (v.length : ℝ)* (δ/6) ∧
      (v ≠ [] → |τ (wordMap F (q::v) y) - τ (wordMap L (q::v) y)| < (v.length : ℝ)* (δ/6)) := by
    induction v with
    | nil => intro q y _ _ _; simp [wordMap,htr]
    | cons j u ih =>
      intro q y hy hm hu
      have hl := hL q y hy
      have h1 := local_bound q (L q y) hl (hid q y) hm (j::u) (by simp) hu
      rw [hFL] at h1
      have h2 := (ih j (L q y) hl ((hdec j _ hl).trans hm) (by simpa using (Nat.le_trans (Nat.le_succ _) hu))).1
      have ht := abs_sub_le (τ (wordMap F (j::u) (F q y))) (τ (wordMap F (j::u) (L q y)))
        (τ (wordMap L (j::u) (L q y)))
      have hs : |τ (wordMap F (j::u) (F q y)) - τ (wordMap L (j::u) (L q y))| <
          ((j::u).length : ℝ) * (δ/6) := by
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        linarith
      exact ⟨hs.le,fun _ => hs⟩
  by_cases he : w = []
  · subst w; simp [wordMap,htr] at hgap; linarith
  have hlt := (hybrid w a x hx hmass hlen).2 he
  have hn6 : (w.length : ℝ) ≤ 6 := by exact_mod_cast hlen
  nlinarith

theorem word_trace_bounds {C : Set E} (τ : E →ₗ[ℝ] ℝ) (hn : ∀ x ∈ C, 0 ≤ τ x)
    (F : I → E →ₗ[ℝ] E) (hp : ∀ q x, x ∈ C → F q x ∈ C)
    (hd : ∀ q x, x ∈ C → τ (F q x) ≤ τ x) (w : List I) {x : E} (hx : x ∈ C) :
    0 ≤ τ (wordMap F w x) ∧ τ (wordMap F w x) ≤ τ x := by
  induction w generalizing x with
  | nil => exact ⟨hn x hx,le_rfl⟩
  | cons q _ ih =>
    obtain ⟨ha,hb⟩ := ih (hp q x hx)
    exact ⟨ha,hb.trans (hd q x hx)⟩

/-- Two equal trace masses in a Jordan decomposition give the sharp factor 1/2
for the distinguishability of a trace-zero increment. -/
theorem word_trace_zero_half_bound {C : Set E} (τ : E →ₗ[ℝ] ℝ)
    (hn : ∀ x ∈ C, 0 ≤ τ x) (F : I → E →ₗ[ℝ] E) (hp : ∀ q x, x ∈ C → F q x ∈ C)
    (hd : ∀ q x, x ∈ C → τ (F q x) ≤ τ x) (w : List I) {x p n : E}
    (hp' : p ∈ C) (hn' : n ∈ C) (hx : x = p-n) (hz : τ x = 0) :
    |τ (wordMap F w x)| ≤ (τ p + τ n)/2 := by
  have hpos := word_trace_bounds τ hn F hp hd w hp'
  have hneg := word_trace_bounds τ hn F hp hd w hn'
  rw [hx,map_sub] at hz
  rw [hx,map_sub,map_sub,abs_le]
  constructor <;> linarith

end AlbertSequential.SharpDisturbance
