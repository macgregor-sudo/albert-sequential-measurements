/- SPDX-License-Identifier: Apache-2.0 -/
module

public import RobustCert.Table
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-! # The robust functional `Λ''` of thm:cer:seven(b), generic part

Given a certificate vector `Φ = Σ c_i [w_i]` and, for every ordered pair `(i, j)`, a checked defect
decomposition of `⟨[w_i],[w_j]⟩` (`pairs`), the AM–GM step `2|⟨a,d⟩| ≤ ε‖a‖² + ‖d‖²/ε` with
`‖a‖² = g(α)` and `‖d‖² = X(g)` (`WalkForm.purity_residual`) turns `0 ≤ ‖Φ‖²` into
`0 ≤ Λ''(g)` for an explicit list `lam2` of (coefficient, word), in every `WalkForm`.
`ε` per defect is `θ r_π` with `π = Pr_{p_A}(α)` read from the table and `r_π` the largest power of
two with `r_π² π ≤ 1` (paper's bucket choice).  Evaluated on a table with `TableValues` at the traces
`T`, `Λ''` equals `octVal` (all `X` vanish), and prop:robust(a) follows (`robust_margin`).

Counters (`counterT`, `counterW`) are computed from the decomposition data: `T = Σ |c_i c_j| Σ|λ|`,
`W_π = Σ |c_i c_j| Σ_{π(α) = π} |y|`, the definitions of core appendix `app:cert`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven.Robust

open AlbertSequential AlbertSequential.LengthSeven

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## Lists of reals -/

theorem sum_map_le {α : Type} (l : List α) (f g : α → ℝ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem cast_sum_map {α : Type} (l : List α) (F : α → ℚ) :
    (((l.map F).sum : ℚ) : ℝ) = (l.map fun a => (F a : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]

theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (F : β → ℝ) :
    ((l.flatMap g).map F).sum = (l.map fun a => ((g a).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]

theorem mul_sum_map {α : Type} (k : ℝ) (l : List α) (F : α → ℝ) :
    k * (l.map F).sum = (l.map fun a => k * F a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-! ## The certificate vector -/

def phiVec (W : WalkForm V) (vecs : List (ℚ × List Letter)) : V :=
  (vecs.map fun a => (a.1 : ℝ) • W.pathVec a.2).sum

/-- Ordered pairs of the certificate vector with coefficient products. -/
def pairSpec (vecs : List (ℚ × List Letter)) : List (ℚ × List Letter × List Letter) :=
  vecs.flatMap fun a => vecs.map fun b => (a.1 * b.1, a.2, b.2)

theorem form_phiVec_right (W : WalkForm V) (x : V) (l : List (ℚ × List Letter)) :
    W.form x (phiVec W l) = (l.map fun b => (b.1 : ℝ) * W.form x (W.pathVec b.2)).sum := by
  induction l with
  | nil => simp [phiVec]
  | cons b l ih =>
    simp only [phiVec, List.map_cons, List.sum_cons, map_add, map_smul, smul_eq_mul] at ih ⊢
    rw [ih]

theorem normSq_phiVec (W : WalkForm V) (vecs : List (ℚ × List Letter)) :
    W.normSq (phiVec W vecs) =
      ((pairSpec vecs).map fun t => (t.1 : ℝ) * W.form (W.pathVec t.2.1) (W.pathVec t.2.2)).sum := by
  unfold WalkForm.normSq pairSpec
  rw [sum_map_flatMap]
  conv_lhs => rw [form_phiVec_right]
  have hl : ∀ l : List (ℚ × List Letter), ∀ x : V, W.form (phiVec W l) x =
      (l.map fun a => (a.1 : ℝ) * W.form (W.pathVec a.2) x).sum := by
    intro l x
    induction l with
    | nil => simp [phiVec]
    | cons a l ih =>
      simp only [phiVec, List.map_cons, List.sum_cons, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul] at ih ⊢
      rw [ih]
  rw [← form_phiVec_right, hl]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [form_phiVec_right, mul_sum_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply]
  push_cast
  ring

/-! ## AM–GM for one defect -/

theorem amgm (W : WalkForm V) (a r : V) (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    s * W.form a r ≤ |s| * (ε / 2 * W.normSq a + W.normSq r / (2 * ε)) := by
  have h1 := W.psd (ε • a + r)
  have h2 := W.psd (ε • a - r)
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul] at h1 h2
  rw [W.symm r a] at h1 h2
  unfold WalkForm.normSq
  set A := W.form a a
  set B := W.form a r
  set C := W.form r r
  have key : 2 * ε * |B| ≤ ε ^ 2 * A + C := by
    rcases abs_cases B with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [hb] <;> nlinarith
  have hB : |B| ≤ ε / 2 * A + C / (2 * ε) := by
    have e : ε / 2 * A + C / (2 * ε) = (ε ^ 2 * A + C) / (2 * ε) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  calc s * B ≤ |s * B| := le_abs_self _
    _ = |s| * |B| := abs_mul s B
    _ ≤ |s| * (ε / 2 * A + C / (2 * ε)) := mul_le_mul_of_nonneg_left hB (abs_nonneg s)

/-! ## The functional `Λ''` -/

/-- Largest power of two `r` (from `r₀`, by doubling, fuel `n`) with `r² π ≤ 1`. -/
def rOf : ℕ → ℚ → ℚ → ℚ
  | 0, r, _ => r
  | n + 1, r, π => if (2 * r) ^ 2 * π ≤ 1 then rOf n (2 * r) π else r

theorem rOf_pos : ∀ (n : ℕ) (r π : ℚ), 0 < r → 0 < rOf n r π
  | 0, r, _, hr => hr
  | n + 1, r, π, hr => by
    simp only [rOf]
    split
    · exact rOf_pos n (2 * r) π (by positivity)
    · exact hr

/-- `π(α) = Pr_{p_A}(α)` on the table `T` (1 if not evaluable; then the bucket is just coarser). -/
def piQ (T : TraceTable) (α : List Letter) : ℚ := (fvalQ T (.yes α)).getD 1

/-- `ε = θ r_π`. -/
def epsQ (T : TraceTable) (θ : ℚ) (α : List Letter) : ℚ := θ * rOf 64 1 (piQ T α)

theorem epsQ_pos (T : TraceTable) (θ : ℚ) (hθ : 0 < θ) (α : List Letter) : 0 < epsQ T θ α :=
  mul_pos hθ (rOf_pos 64 1 _ one_pos)

/-- The four words of one defect in `Λ''`: `|ky| (ε/2 [α] + X/(2ε))`. -/
def defTerms (T : TraceTable) (θ k : ℚ) (d : Defect) : List (ℚ × Word Letter) :=
  [(|k * d.y| * epsQ T θ d.α / 2, yesWord d.α),
   (|k * d.y| / (2 * epsQ T θ d.α), d.long),
   (-(|k * d.y| * d.c / epsQ T θ d.α), d.mid),
   (|k * d.y| * (d.c * d.c) / (2 * epsQ T θ d.α), d.short)]

def entryTerms (T : TraceTable) (θ : ℚ) (p : ℚ × Entry) : List (ℚ × Word Letter) :=
  p.2.tabs.map (fun m => (p.1 * m.1, m.2.toWord)) ++ p.2.defs.flatMap (defTerms T θ p.1)

/-- The functional `Λ''` as a list of (coefficient, word from `p_A`). -/
def lam2 (T : TraceTable) (θ : ℚ) (pairs : List (ℚ × Entry)) : List (ℚ × Word Letter) :=
  pairs.flatMap (entryTerms T θ)

def evalF (g : Word Letter → ℝ) (L : List (ℚ × Word Letter)) : ℝ := (L.map fun m => (m.1 : ℝ) * g m.2).sum

/-- `ℓ¹` norm (terms not merged; an upper bound for the merged norm). -/
def l1 (L : List (ℚ × Word Letter)) : ℚ := (L.map fun m => |m.1|).sum

theorem l1_nonneg : ∀ L : List (ℚ × Word Letter), 0 ≤ l1 L
  | [] => by simp [l1]
  | m :: L => by
    have := l1_nonneg L
    simp only [l1, List.map_cons, List.sum_cons] at this ⊢
    exact add_nonneg (abs_nonneg _) this

theorem evalF_append (g : Word Letter → ℝ) (L M : List (ℚ × Word Letter)) :
    evalF g (L ++ M) = evalF g L + evalF g M := by simp [evalF, List.sum_append]

theorem evalF_flatMap {α : Type} (g : Word Letter → ℝ) (l : List α) (F : α → List (ℚ × Word Letter)) :
    evalF g (l.flatMap F) = (l.map fun a => evalF g (F a)).sum := by
  unfold evalF; rw [sum_map_flatMap]

theorem evalF_tabs (g : Word Letter → ℝ) (k : ℚ) (l : List (ℚ × TabWord)) :
    evalF g (l.map fun m => (k * m.1, m.2.toWord)) =
      (k : ℝ) * (l.map fun m => (m.1 : ℝ) * g m.2.toWord).sum := by
  unfold evalF
  rw [List.map_map, mul_sum_map]
  congr 1
  apply List.map_congr_left
  intro m _
  simp only [Function.comp_apply]
  push_cast
  ring

theorem evalF_defTerms (T : TraceTable) (θ k : ℚ) (d : Defect) (g : Word Letter → ℝ) :
    evalF g (defTerms T θ k d) =
      (|k * d.y| : ℝ) * ((epsQ T θ d.α : ℝ) / 2 * g (yesWord d.α) +
        (g d.long - 2 * d.c * g d.mid + d.c ^ 2 * g d.short) / (2 * epsQ T θ d.α)) := by
  simp only [evalF, defTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem defect_le (W : WalkForm V) (T : TraceTable) (θ : ℚ) (hθ : 0 < θ) (k : ℚ) (d : Defect) :
    (k : ℝ) * ((d.y : ℝ) * W.form (W.pathVec d.α) (d.resid W)) ≤
      evalF (fun w => W.normSq (W.vec w)) (defTerms T θ k d) := by
  rw [evalF_defTerms]
  have hε : (0 : ℝ) < (epsQ T θ d.α : ℝ) := by exact_mod_cast epsQ_pos T θ hθ d.α
  have hr : W.normSq (d.resid W) = W.normSq (W.vec d.long) - 2 * d.c * W.normSq (W.vec d.mid)
      + (d.c : ℝ) ^ 2 * W.normSq (W.vec d.short) := by
    unfold Defect.resid Defect.long Defect.mid Defect.short
    exact W.purity_residual d.t (d.q, true) d.v d.c
  have ha : W.normSq (W.pathVec d.α) = W.normSq (W.vec (yesWord d.α)) := rfl
  have := amgm W (W.pathVec d.α) (d.resid W) _ hε ((k : ℝ) * d.y)
  rw [← mul_assoc, ← hr, ← ha]
  have habs : (|k * d.y| : ℝ) = |(k : ℝ) * (d.y : ℝ)| := by push_cast; rfl
  rw [habs]
  exact this

theorem entry_le (W : WalkForm V) (T : TraceTable) (θ : ℚ) (hθ : 0 < θ) (p : ℚ × Entry) :
    (p.1 : ℝ) * p.2.rhs W ≤ evalF (fun w => W.normSq (W.vec w)) (entryTerms T θ p) := by
  unfold entryTerms Entry.rhs
  rw [evalF_append, evalF_tabs, evalF_flatMap, mul_add, mul_sum_map (p.1 : ℝ) p.2.defs]
  apply add_le_add (le_refl _)
  exact sum_map_le _ _ _ fun d _ => defect_le W T θ hθ p.1 d

/-- **`Λ''(g) ≥ 0` in every `WalkForm`**, from checked decompositions of all pairs. -/
theorem lam2_nonneg (W : WalkForm V) (T : TraceTable) (θ : ℚ) (hθ : 0 < θ)
    (vecs : List (ℚ × List Letter)) (pairs : List (ℚ × Entry))
    (hp : pairs.map (fun p => (p.1, p.2.u1, p.2.u2)) = pairSpec vecs)
    (hok : pairs.all (fun p => p.2.ok) = true) :
    0 ≤ evalF (fun w => W.normSq (W.vec w)) (lam2 T θ pairs) := by
  have h0 := W.psd (phiVec W vecs)
  have h1 : W.form (phiVec W vecs) (phiVec W vecs) =
      (pairs.map fun p => (p.1 : ℝ) * p.2.rhs W).sum := by
    have := normSq_phiVec W vecs
    unfold WalkForm.normSq at this
    rw [this, ← hp, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hpm
    simp only [Function.comp_apply]
    rw [Entry.sound W p.2 (List.all_eq_true.mp hok p hpm)]
  rw [h1] at h0
  unfold lam2
  rw [evalF_flatMap]
  exact le_trans h0 (sum_map_le _ _ _ fun p _ => entry_le W T θ hθ p)

/-! ## Value on the octonionic table -/

/-- All table words evaluable and all defect constants are purity constants. -/
def octOk (T : TraceTable) (pairs : List (ℚ × Entry)) : Bool :=
  pairs.all fun p => p.2.tabs.all (fun m => (fvalQ T m.2).isSome) &&
    p.2.defs.all (fun d => (fvalQ T (.yes d.α)).isSome && d.xok T)

/-- `Λ''` on the octonionic table (computed). -/
def octVal (T : TraceTable) (θ : ℚ) (pairs : List (ℚ × Entry)) : ℚ :=
  (pairs.map fun p => (p.2.tabs.map fun m => p.1 * m.1 * (fvalQ T m.2).getD 0).sum +
    (p.2.defs.map fun d => |p.1 * d.y| * epsQ T θ d.α / 2 * piQ T d.α).sum).sum

theorem evalF_oct {τ : TraceData} {f : Word Letter → ℝ} (T : TraceTable) (h : T.Holds τ)
    (hT : TableValues τ f) (θ : ℚ) (pairs : List (ℚ × Entry)) (hok : octOk T pairs = true) :
    evalF f (lam2 T θ pairs) = octVal T θ pairs := by
  unfold lam2 octVal
  rw [evalF_flatMap, cast_sum_map]
  congr 1
  apply List.map_congr_left
  intro p hpm
  have hp := List.all_eq_true.mp hok p hpm
  simp only [Bool.and_eq_true] at hp
  obtain ⟨htab, hdef⟩ := hp
  unfold entryTerms
  rw [evalF_append, evalF_tabs, evalF_flatMap, mul_sum_map, Rat.cast_add, cast_sum_map, cast_sum_map]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro m hm
    have hs := List.all_eq_true.mp htab m hm
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
    rw [fvalQ_sound h hT m.2 q hq, hq]
    simp only [Option.getD_some]
    push_cast
    ring
  · congr 1
    apply List.map_congr_left
    intro d hd
    have hs := List.all_eq_true.mp hdef d hd
    simp only [Bool.and_eq_true] at hs
    obtain ⟨hsome, hx⟩ := hs
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
    have hX := xok_sound h hT d hx
    have hα : f (yesWord d.α) = q := fvalQ_sound h hT (.yes d.α) q hq
    rw [evalF_defTerms, hα]
    have hpi : piQ T d.α = q := by simp [piQ, hq]
    rw [hpi]
    have hlong : f d.long = 2 * d.c * f d.mid - (d.c : ℝ) ^ 2 * f d.short := by linarith
    rw [hlong]
    push_cast
    ring

theorem evalF_sub_le (g f : Word Letter → ℝ) (L : List (ℚ × Word Letter)) (δ : ℝ)
    (hδ : ∀ m ∈ L, |g m.2 - f m.2| ≤ δ) : evalF g L - evalF f L ≤ (l1 L : ℝ) * δ := by
  induction L with
  | nil => simp [evalF, l1]
  | cons m L ih =>
    have h1 := hδ m (by simp)
    have h2 := ih fun m' hm' => hδ m' (by simp [hm'])
    simp only [evalF, l1, List.map_cons, List.sum_cons] at h2 ⊢
    have h3 : (m.1 : ℝ) * g m.2 - (m.1 : ℝ) * f m.2 ≤ |(m.1 : ℝ)| * δ := by
      rw [← mul_sub]
      calc (m.1 : ℝ) * (g m.2 - f m.2) ≤ |(m.1 : ℝ) * (g m.2 - f m.2)| := le_abs_self _
        _ = |(m.1 : ℝ)| * |g m.2 - f m.2| := abs_mul _ _
        _ ≤ |(m.1 : ℝ)| * δ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    rw [cast_sum_map] at h2
    rw [Rat.cast_add, cast_sum_map, Rat.cast_abs]
    linarith

/-- **prop:robust(a) for `Λ''`**: a `WalkForm` whose word values are within `δ` of a table with the
traces `T` on the support of `Λ''` has `−octVal ≤ ‖λ''‖₁ δ`. -/
theorem robust_margin (W : WalkForm V) {τ : TraceData} {f : Word Letter → ℝ} (T : TraceTable)
    (h : T.Holds τ) (hT : TableValues τ f) (θ : ℚ) (hθ : 0 < θ)
    (vecs : List (ℚ × List Letter)) (pairs : List (ℚ × Entry))
    (hp : pairs.map (fun p => (p.1, p.2.u1, p.2.u2)) = pairSpec vecs)
    (hok : pairs.all (fun p => p.2.ok) = true) (hoct : octOk T pairs = true) (δ : ℝ)
    (hδ : ∀ m ∈ lam2 T θ pairs, |W.normSq (W.vec m.2) - f m.2| ≤ δ) :
    -(octVal T θ pairs : ℝ) ≤ (l1 (lam2 T θ pairs) : ℝ) * δ := by
  have h0 := lam2_nonneg W T θ hθ vecs pairs hp hok
  have h1 := evalF_oct T h hT θ pairs hoct
  have h2 := evalF_sub_le (fun w => W.normSq (W.vec w)) f _ δ hδ
  linarith

/-! ## Counters (definitions of core appendix `app:cert`), computed from the data -/

/-- `T = Σ_pairs |c_i c_j| Σ |λ|`. -/
def counterT (pairs : List (ℚ × Entry)) : ℚ :=
  (pairs.map fun p => |p.1| * (p.2.tabs.map fun m => |m.1|).sum).sum

/-- `W_π = Σ_pairs Σ_{defects with π(α) = π} |c_i c_j y|`. -/
def counterW (T : TraceTable) (pairs : List (ℚ × Entry)) (π : ℚ) : ℚ :=
  (pairs.map fun p => (p.2.defs.map fun d => if piQ T d.α = π then |p.1 * d.y| else 0).sum).sum

end AlbertSequential.LengthSeven.Robust
