/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.Basic

/-! # The walk form

The carrier of Lemma A (paper hypothesis (H) of core `sec:cer`, with "real Hilbert space"
weakened to a real module with a symmetric positive semidefinite bilinear form):
four form-self-adjoint idempotents `P A, …, P D` and a vector `ξ` with
`⟨ξ, ξ⟩ = 1`, `P A ξ = ξ`.  No completion, GNS construction or definiteness is
used.  Because the form is only semidefinite, the paper's vector identities are
stated as `Eqv` (equality after pairing with every vector); every use in the
paper pairs them with a path vector, so nothing is lost.

Conventions.
* `op (i, true) = P i`, `op (i, false) = 1 − P i` ("no").
* `seqL u` applies the outcomes of the chronological word `u` in time order;
  `vec u = seqL u ξ`.  For letters, `pathVec u = [u] = P_{u_k} ⋯ P_{u_1} ξ`.
* `L w = ⟨ξ, P_{w_1} ⋯ P_{w_n} ξ⟩` (paper's walk functional), so
  `⟨[u], [v]⟩ = L (u ++ v.reverse)` (eq:cer:walkrule). -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

open AlbertSequential

/-- A real module with a symmetric positive semidefinite bilinear form, four
form-self-adjoint idempotents and a unit vector fixed by `P A`. -/
structure WalkForm (V : Type*) [AddCommGroup V] [Module ℝ V] where
  form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symm : ∀ x y, form x y = form y x
  psd : ∀ x, 0 ≤ form x x
  P : Letter → V →ₗ[ℝ] V
  idem : ∀ i x, P i (P i x) = P i x
  selfAdj : ∀ i x y, form (P i x) y = form x (P i y)
  ξ : V
  fixA : P 0 ξ = ξ
  unit : form ξ ξ = 1

namespace WalkForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (W : WalkForm V)

/-! ## Null vectors -/

/-- Cauchy–Schwarz null-vector lemma: a vector of zero square pairs to zero with
every vector. -/
theorem null_pair (z : V) (hz : W.form z z = 0) (y : V) : W.form z y = 0 := by
  by_contra hne
  have key : ∀ t : ℝ, 0 ≤ t ^ 2 * W.form y y + 2 * t * W.form z y := by
    intro t
    have h := W.psd (z + t • y)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hz, W.symm y z] at h
    nlinarith [h]
  have h1 := key (-(W.form z y) / (W.form y y + 1))
  have hyy := W.psd y
  have hpos : 0 < W.form y y + 1 := by linarith
  have hsq : 0 < (W.form z y) ^ 2 := by positivity
  rw [div_pow, neg_sq] at h1
  have : (W.form z y) ^ 2 / (W.form y y + 1) ^ 2 * W.form y y
      + 2 * (-(W.form z y) / (W.form y y + 1)) * W.form z y < 0 := by
    have e : (W.form z y) ^ 2 / (W.form y y + 1) ^ 2 * W.form y y
        + 2 * (-(W.form z y) / (W.form y y + 1)) * W.form z y
        = (W.form z y) ^ 2 * (W.form y y - 2 * (W.form y y + 1)) / (W.form y y + 1) ^ 2 := by
      field_simp
      ring
    rw [e]
    apply div_neg_of_neg_of_pos
    · nlinarith
    · positivity
  linarith

/-! ## Equality modulo null vectors -/

/-- `x` and `y` have the same pairing with every vector. -/
def Eqv (x y : V) : Prop := ∀ z, W.form x z = W.form y z

namespace Eqv
variable {W}

theorem refl (x : V) : W.Eqv x x := fun _ => rfl
theorem of_eq {x y : V} (h : x = y) : W.Eqv x y := h ▸ refl x
theorem symm' {x y : V} (h : W.Eqv x y) : W.Eqv y x := fun z => (h z).symm
theorem trans {x y u : V} (h : W.Eqv x y) (h' : W.Eqv y u) : W.Eqv x u :=
  fun z => (h z).trans (h' z)
theorem add {x y x' y' : V} (h : W.Eqv x y) (h' : W.Eqv x' y') : W.Eqv (x + x') (y + y') :=
  fun z => by simp only [map_add, LinearMap.add_apply, h z, h' z]
theorem sub {x y x' y' : V} (h : W.Eqv x y) (h' : W.Eqv x' y') : W.Eqv (x - x') (y - y') :=
  fun z => by simp only [map_sub, LinearMap.sub_apply, h z, h' z]
theorem smul {x y : V} (c : ℝ) (h : W.Eqv x y) : W.Eqv (c • x) (c • y) :=
  fun z => by simp only [map_smul, LinearMap.smul_apply, h z]
theorem form_left {x y : V} (h : W.Eqv x y) (z : V) : W.form x z = W.form y z := h z
theorem form_right {x y : V} (h : W.Eqv x y) (z : V) : W.form z x = W.form z y := by
  rw [W.symm z x, W.symm z y]; exact h z
/-- `Eqv` is a congruence for the projections. -/
theorem map_P {x y : V} (i : Letter) (h : W.Eqv x y) : W.Eqv (W.P i x) (W.P i y) :=
  fun z => by rw [W.selfAdj, W.selfAdj]; exact h _

end Eqv

/-- A vector of zero square is `Eqv` to zero. -/
theorem eqv_zero_of_null {z : V} (hz : W.form z z = 0) : W.Eqv z 0 :=
  fun y => by rw [W.null_pair z hz y]; simp

/-! ## Outcome operators and path vectors -/

/-- Outcome operator: `P i` for yes, `1 − P i` for no. -/
def op (a : Outcome Letter) : V →ₗ[ℝ] V :=
  if a.2 then W.P a.1 else LinearMap.id - W.P a.1

@[simp] theorem op_yes (i : Letter) : W.op (i, true) = W.P i := rfl
@[simp] theorem op_no (i : Letter) : W.op (i, false) = LinearMap.id - W.P i := rfl

theorem op_idem (a : Outcome Letter) (x : V) : W.op a (W.op a x) = W.op a x := by
  rcases a with ⟨i, b⟩
  cases b
  · simp only [op_no, LinearMap.sub_apply, LinearMap.id_apply, map_sub, W.idem]
    abel
  · exact W.idem i x

theorem op_selfAdj (a : Outcome Letter) (x y : V) :
    W.form (W.op a x) y = W.form x (W.op a y) := by
  rcases a with ⟨i, b⟩
  cases b
  · simp only [op_no, LinearMap.sub_apply, LinearMap.id_apply, map_sub, W.selfAdj]
  · exact W.selfAdj i x y

/-- Sequential operator of a chronological word: first outcome acts first. -/
def seqL : Word Letter → V →ₗ[ℝ] V
  | [] => LinearMap.id
  | a :: u => seqL u ∘ₗ W.op a

@[simp] theorem seqL_nil : W.seqL [] = LinearMap.id := rfl
theorem seqL_cons (a : Outcome Letter) (u : Word Letter) :
    W.seqL (a :: u) = W.seqL u ∘ₗ W.op a := rfl

theorem seqL_append (u v : Word Letter) : W.seqL (u ++ v) = W.seqL v ∘ₗ W.seqL u := by
  induction u with
  | nil => rfl
  | cons a u ih => rw [List.cons_append, seqL_cons, ih, seqL_cons, LinearMap.comp_assoc]

theorem seqL_singleton (a : Outcome Letter) : W.seqL [a] = W.op a := rfl

theorem seqL_cons_apply (a : Outcome Letter) (u : Word Letter) (x : V) :
    W.seqL (a :: u) x = W.seqL u (W.op a x) := rfl

theorem seqL_nil_apply (x : V) : W.seqL [] x = x := rfl

theorem op_yes_apply (i : Letter) (x : V) : W.op (i, true) x = W.P i x := rfl

theorem op_no_apply (i : Letter) (x : V) : W.op (i, false) x = x - W.P i x := rfl

theorem seqL_apply_append (u v : Word Letter) (x : V) :
    W.seqL (u ++ v) x = W.seqL v (W.seqL u x) := by
  rw [seqL_append]; rfl

theorem seqL_apply_concat (u : Word Letter) (a : Outcome Letter) (x : V) :
    W.seqL (u ++ [a]) x = W.op a (W.seqL u x) := by
  rw [seqL_apply_append]; rfl

/-- Adjoint of a sequential operator: the reversed word. -/
theorem seqL_adjoint (u : Word Letter) (x y : V) :
    W.form (W.seqL u x) y = W.form x (W.seqL u.reverse y) := by
  induction u generalizing x y with
  | nil => rfl
  | cons a u ih =>
    rw [seqL_cons, LinearMap.comp_apply, ih, W.op_selfAdj, List.reverse_cons,
      seqL_apply_concat]

section
variable {W}

theorem Eqv.map_op {x y : V} (a : Outcome Letter) (h : W.Eqv x y) :
    W.Eqv (W.op a x) (W.op a y) :=
  fun z => by rw [W.op_selfAdj, W.op_selfAdj]; exact h _

/-- `Eqv` is a congruence for every sequential operator ("inside longer words"). -/
theorem Eqv.map_seqL {x y : V} (u : Word Letter) (h : W.Eqv x y) :
    W.Eqv (W.seqL u x) (W.seqL u y) :=
  fun z => by rw [W.seqL_adjoint, W.seqL_adjoint]; exact h _

end

/-- Path vector of an outcome word, `P_{u_k} ⋯ P_{u_1} ξ` (no-outcomes as `1 − P`). -/
def vec (u : Word Letter) : V := W.seqL u W.ξ

/-- Path vector `[u] = P_{u_k} ⋯ P_{u_1} ξ` of a letter word (all outcomes yes). -/
def pathVec (u : List Letter) : V := W.vec (yesWord u)

/-- Square of a vector. -/
def normSq (x : V) : ℝ := W.form x x

@[simp] theorem vec_nil : W.vec [] = W.ξ := rfl

theorem vec_append (u v : Word Letter) : W.vec (u ++ v) = W.seqL v (W.vec u) :=
  W.seqL_apply_append u v W.ξ

theorem vec_concat (u : Word Letter) (a : Outcome Letter) :
    W.vec (u ++ [a]) = W.op a (W.vec u) :=
  W.seqL_apply_concat u a W.ξ

/-- A leading yes on `A` costs nothing. -/
@[simp] theorem vec_cons_yesA (u : Word Letter) : W.vec ((0, true) :: u) = W.vec u := by
  simp only [vec, seqL_cons, LinearMap.comp_apply, op_yes, W.fixA]

theorem vec_dropYesA (u : Word Letter) : W.vec (dropYesA u) = W.vec u := by
  cases u with
  | nil => rfl
  | cons a u =>
    simp only [dropYesA]
    split_ifs with h
    · subst h; simp
    · rfl

/-- Equal neighbours merge (`P² = P`, `(1−P)² = 1−P`). -/
theorem vec_merge (u : Word Letter) (a : Outcome Letter) (v : Word Letter) :
    W.vec (u ++ a :: a :: v) = W.vec (u ++ a :: v) := by
  rw [vec_append, vec_append, seqL_cons, seqL_cons]
  simp only [LinearMap.comp_apply, W.op_idem]

/-- A yes immediately followed by a no on the same test kills the path vector. -/
theorem vec_yes_no (u : Word Letter) (i : Letter) (v : Word Letter) :
    W.vec (u ++ (i, true) :: (i, false) :: v) = 0 := by
  rw [vec_append, seqL_cons_apply, seqL_cons_apply, op_yes_apply, op_no_apply, W.idem, sub_self,
    map_zero]

/-- A no immediately followed by a yes on the same test kills the path vector. -/
theorem vec_no_yes (u : Word Letter) (i : Letter) (v : Word Letter) :
    W.vec (u ++ (i, false) :: (i, true) :: v) = 0 := by
  rw [vec_append, seqL_cons_apply, seqL_cons_apply, op_no_apply, op_yes_apply, map_sub, W.idem,
    sub_self, map_zero]

theorem normSq_vec_dropYesA (u : Word Letter) :
    W.normSq (W.vec (dropYesA u)) = W.normSq (W.vec u) := by
  rw [vec_dropYesA]

/-! ## Walks -/

/-- `prodL w = P_{w_1} ∘ ⋯ ∘ P_{w_n}` for a letter word `w`. -/
def prodL : List Letter → V →ₗ[ℝ] V
  | [] => LinearMap.id
  | a :: r => W.P a ∘ₗ prodL r

theorem prodL_append (u v : List Letter) : W.prodL (u ++ v) = W.prodL u ∘ₗ W.prodL v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prodL, ih, LinearMap.comp_assoc]

theorem prodL_adjoint (w : List Letter) (x y : V) :
    W.form (W.prodL w x) y = W.form x (W.prodL w.reverse y) := by
  induction w generalizing x y with
  | nil => rfl
  | cons a r ih =>
    simp only [prodL, LinearMap.comp_apply, W.selfAdj, List.reverse_cons, prodL_append,
      LinearMap.id_apply, ih]

theorem seqL_yesWord (u : List Letter) : W.seqL (yesWord u) = W.prodL u.reverse := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    rw [yesWord_cons, seqL_cons, ih, List.reverse_cons, prodL_append]
    rfl

/-- Walk functional `L(w) = ⟨ξ, P_{w_1} ⋯ P_{w_n} ξ⟩`. -/
def L (w : List Letter) : ℝ := W.form W.ξ (W.prodL w W.ξ)

theorem pathVec_eq (u : List Letter) : W.pathVec u = W.prodL u.reverse W.ξ := by
  simp only [pathVec, vec, seqL_yesWord]

/-- eq:cer:walkrule: `⟨[u], [v]⟩ = L(u v̄)`. -/
theorem form_pathVec (u v : List Letter) :
    W.form (W.pathVec u) (W.pathVec v) = W.L (u ++ v.reverse) := by
  rw [pathVec_eq, pathVec_eq, prodL_adjoint, List.reverse_reverse, L, prodL_append]
  rfl

@[simp] theorem L_nil : W.L [] = 1 := W.unit

theorem L_reverse (w : List Letter) : W.L w.reverse = W.L w := by
  unfold L
  rw [W.symm, prodL_adjoint, List.reverse_reverse]

theorem L_cons_A (w : List Letter) : W.L (0 :: w) = W.L w := by
  unfold L
  simp only [prodL, LinearMap.comp_apply]
  rw [← W.selfAdj, W.fixA]

theorem L_append_A (w : List Letter) : W.L (w ++ [0]) = W.L w := by
  unfold L
  rw [prodL_append]
  simp only [prodL, LinearMap.comp_apply, LinearMap.comp_id, W.fixA]

theorem prodL_merge (a : Letter) (r : List Letter) :
    W.prodL (a :: a :: r) = W.prodL (a :: r) := by
  ext x
  simp only [prodL, LinearMap.comp_apply, W.idem]

theorem L_merge (u : List Letter) (a : Letter) (v : List Letter) :
    W.L (u ++ a :: a :: v) = W.L (u ++ a :: v) := by
  unfold L
  rw [prodL_append, prodL_append, prodL_merge]

theorem prodL_mergeAdj : ∀ w : List Letter, W.prodL (mergeAdj w) = W.prodL w
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => by
    rw [mergeAdj]
    split_ifs with h
    · subst h
      rw [prodL_mergeAdj (a :: r), prodL_merge]
    · rw [prodL, prodL_mergeAdj (b :: r)]
      rfl

theorem L_mergeAdj (w : List Letter) : W.L (mergeAdj w) = W.L w := by
  unfold L; rw [prodL_mergeAdj]

theorem L_stripLead : ∀ w : List Letter, W.L (stripLead w) = W.L w
  | [] => rfl
  | a :: r => by
    rw [stripLead]
    split_ifs with h
    · subst h; rw [L_stripLead r, L_cons_A]
    · rfl

theorem L_stripTrail (w : List Letter) : W.L (stripTrail w) = W.L w := by
  unfold stripTrail
  rw [L_reverse, L_stripLead, L_reverse]

theorem L_canon (w : List Letter) : W.L (canon w) = W.L w := by
  unfold canon
  simp only
  split_ifs
  · rw [L_stripTrail, L_stripLead, L_mergeAdj]
  · rw [L_reverse, L_stripTrail, L_stripLead, L_mergeAdj]

/-- Entries of a path-vector Gram matrix by computable normalisation. -/
theorem form_pathVec_canon (u v : List Letter) :
    W.form (W.pathVec u) (W.pathVec v) = W.L (canon (u ++ v.reverse)) := by
  rw [form_pathVec, L_canon]

/-! ## Polarisation (the identity behind Lemma D) -/

/-- `2⟨X P_a J, X J⟩ = ‖X P_a J‖² + ‖X J‖² − ‖X (1 − P_a) J‖²` with `J = vec s`,
`X = seqL r`. -/
theorem polarisation (s : Word Letter) (a : Letter) (r : Word Letter) :
    2 * W.form (W.vec (s ++ (a, true) :: r)) (W.vec (s ++ r)) =
      W.normSq (W.vec (s ++ (a, true) :: r)) + W.normSq (W.vec (s ++ r))
        - W.normSq (W.vec (s ++ (a, false) :: r)) := by
  have e1 : W.vec (s ++ (a, true) :: r) = W.seqL r (W.P a (W.vec s)) := by
    rw [vec_append, seqL_cons]; rfl
  have e2 : W.vec (s ++ r) = W.seqL r (W.vec s) := vec_append ..
  have e3 : W.vec (s ++ (a, false) :: r) =
      W.seqL r (W.vec s) - W.seqL r (W.P a (W.vec s)) := by
    rw [vec_append, seqL_cons, LinearMap.comp_apply, op_no, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub]
  rw [e1, e2, e3]
  unfold normSq
  simp only [map_sub, LinearMap.sub_apply]
  rw [W.symm (W.seqL r (W.vec s)) (W.seqL r (W.P a (W.vec s)))]
  ring

/-! ## Purity residual (lem:purity, vector form) -/

theorem form_seqL_dropLast (v : Word Letter) (η : V) :
    W.form (W.seqL v η) (W.seqL v.dropLast η) = W.normSq (W.seqL v η) := by
  rcases List.eq_nil_or_concat v with h | ⟨v', l, rfl⟩
  · subst h; rfl
  · rw [List.concat_eq_append, List.dropLast_concat, seqL_apply_concat, normSq,
      W.op_selfAdj, W.op_selfAdj, W.op_idem]

/-- The three-word purity residual.  With `η = vec (t ++ [q])` and
`z = vec (t ++ [q] ++ v ++ v̄ ++ [q]) − c • η`,
`‖z‖² = ‖[t,q,v,v̄,q]‖² − 2c ‖[t,q,v]‖² + c² ‖[t,q]‖²`. -/
theorem purity_residual (t : Word Letter) (q : Outcome Letter) (v : Word Letter) (c : ℝ) :
    W.normSq (W.vec (t ++ [q] ++ v ++ purityMirror v ++ [q]) - c • W.vec (t ++ [q])) =
      W.normSq (W.vec (t ++ [q] ++ v ++ purityMirror v ++ [q]))
        - 2 * c * W.normSq (W.vec (t ++ [q] ++ v))
        + c ^ 2 * W.normSq (W.vec (t ++ [q])) := by
  set η := W.vec (t ++ [q]) with hη
  have hlong : W.vec (t ++ [q] ++ v ++ purityMirror v ++ [q]) =
      W.op q (W.seqL (purityMirror v) (W.seqL v η)) := by
    rw [vec_concat, vec_append, vec_append]
  have hmid : W.vec (t ++ [q] ++ v) = W.seqL v η := vec_append ..
  have hfix : W.op q η = η := by rw [hη, vec_concat, W.op_idem]
  have hcross : W.form (W.vec (t ++ [q] ++ v ++ purityMirror v ++ [q])) η =
      W.normSq (W.vec (t ++ [q] ++ v)) := by
    rw [hlong, W.op_selfAdj, hfix, seqL_adjoint, purityMirror, List.reverse_reverse,
      hmid, form_seqL_dropLast]
  unfold normSq at hcross ⊢
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [W.symm η (W.vec (t ++ [q] ++ v ++ purityMirror v ++ [q])), hcross]
  ring

/-- Purity relation as a vector identity (modulo null vectors). -/
def PurityHolds (t : Word Letter) (q : Outcome Letter) (v : Word Letter) (c : ℝ) : Prop :=
  W.Eqv (W.vec (t ++ [q] ++ v ++ purityMirror v ++ [q])) (c • W.vec (t ++ [q]))

/-- Null residual ⇒ purity relation. -/
theorem purityHolds_of_residual (t : Word Letter) (q : Outcome Letter) (v : Word Letter)
    (c : ℝ)
    (h : W.normSq (W.vec (t ++ [q] ++ v ++ purityMirror v ++ [q]))
        - 2 * c * W.normSq (W.vec (t ++ [q] ++ v))
        + c ^ 2 * W.normSq (W.vec (t ++ [q])) = 0) :
    W.PurityHolds t q v c := by
  have hz := W.purity_residual t q v c
  rw [h] at hz
  have h0 := W.eqv_zero_of_null hz
  intro y
  have := h0 y
  simp only [map_sub, LinearMap.sub_apply, map_zero, LinearMap.zero_apply] at this
  linarith

end WalkForm
end AlbertSequential.LengthSeven
