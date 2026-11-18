/- SPDX-License-Identifier: Apache-2.0 -/
module

public import LengthSeven.ShortRules
public import LengthSeven.Adapters
public import LengthSeven.NativeBinding
public import NativeWordPurity
public import NativeWordDuality
public import NativeTracePartitions

/-! # The native Albert table satisfies `TableValues`

For four atoms `p : Fin 4 → Albert` of the exact compact Albert algebra, the word
functional from the pure state `p_A = p 0`,
`f = nativeWordProbability p (p 0)` (chronological Lüders updates
`x ↦ U_{p_a} x`, `x ↦ U_{e - p_a} x`), satisfies the interface `TableValues` with
the trace data `nativeTraceData p` (`tableValues_native`).  Hypotheses: the four
elements are atoms (`IsAtom`: trace-one idempotents).  No nondegeneracy, no
positivity of `𝒜` and no trace relation is needed: every constant of
`TableValues` is a polynomial in the thirteen traces, and every factorisation is
the purity identity of lem:purity at an atom.

Route (no octonion arithmetic is redone): the purity
factorisations `native_corner_middle_probability` and
`native_corner_long_probability` reduce every field to a short word from the
atom `p_q` itself (`prob_mid`, `prob_long`); those short values are computed with
`U_p x = ⟨p, x⟩ p` (`quadraticMap_atom`), `U_{e-p} = id - 2 L_p + U_p` (proved
here, `quadraticMap_complement_idem`), trace-form associativity and
commutativity.  The double pairing `⟨p_A ∘ p_x, p_y ∘ p_z⟩` equals
`(ω_y + ω_z)/2` with ω indexed by the middle letter (`dpair_native`).

Also here: the conditioning `e/3 → p_A` (`e3_conditioning`), the bridge from a
representation matching the `e/3` probabilities of the words of length at most
seven that begin with "yes on `A`" to `Reproduces` / `Gram28Hyp` /
`Gram28Rules` / `ShortRules` of the induced `WalkForm.ofAlgebraic`
(`lengthSeven_e3_rules`), and the general ω index identity
`ω_y = ⟨p_A, {p_x p_y p_z}⟩` for every ordering, for every four elements
(`nativeTraceData_om_eq_triple`), which pins `om` to the middle letter
independently of any special configuration. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.LengthSeven

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## Two native operator facts -/

/-- `U_{e-q} = id - 2 L_q + U_q` for an idempotent `q` (paper, proof of lem:cer:short). -/
theorem quadraticMap_complement_idem (q x : Albert) (hq : jordanMul q q = q) :
    quadraticMap (albertUnit - q) x = x - (2 : ℝ) • jordanMul q x + quadraticMap q x := by
  unfold quadraticMap
  simp only [jordanMul_sub_left, jordanMul_sub_right, jordanMul_albertUnit_left,
    jordanMul_albertUnit_right, hq, two_smul]
  abel

theorem nativeOutcome_yes (p : Fin 4 → Albert) (q : Letter) :
    nativeOutcome p (q, true) = p q := by simp [nativeOutcome]

theorem nativeOutcome_no (p : Fin 4 → Albert) (q : Letter) :
    nativeOutcome p (q, false) = albertUnit - p q := by simp [nativeOutcome]

theorem tracePairing_atom_self (q : Albert) (hq : IsAtom q) : tracePairing q q = 1 := by
  unfold tracePairing; rw [hq.1, hq.2]

section Native

variable (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
include hp

/-! ## Purity factorisations reduced to words from the atom itself -/

/-- After a yes on the atom `p_q`, the rest of the word is read from `p_q`. -/
theorem prob_mid (ρ : Albert) (t : Word Letter) (q : Letter) (v : Word Letter) :
    nativeWordProbability p ρ (t ++ (q, true) :: v) =
      nativeWordProbability p (p q) v * nativeWordProbability p ρ (t ++ [(q, true)]) := by
  have ha : IsAtom (nativeOutcome p (q, true)) := by rw [nativeOutcome_yes]; exact hp q
  have h := native_corner_middle_probability p ρ t v (q, true) ha
  rw [show t ++ (q, true) :: v = (t ++ [(q, true)]) ++ v by simp, h, nativeOutcome_yes,
    nativeWordProbability_eq_pairing p (p q) v]

/-- The long purity word `(t, q, v, v̄, q)` gives the square of the value from `p_q`. -/
theorem prob_long (ρ : Albert) (t : Word Letter) (q : Letter) (v : Word Letter) :
    nativeWordProbability p ρ (t ++ (q, true) :: (v ++ purityMirror v ++ [(q, true)])) =
      nativeWordProbability p (p q) v ^ 2 * nativeWordProbability p ρ (t ++ [(q, true)]) := by
  have ha : IsAtom (nativeOutcome p (q, true)) := by rw [nativeOutcome_yes]; exact hp q
  have h := native_corner_long_probability p (fun i => (hp i).1) ρ t v (q, true) ha
  rw [show t ++ (q, true) :: (v ++ purityMirror v ++ [(q, true)]) =
      (t ++ [(q, true)]) ++ v ++ purityMirror v ++ [(q, true)] by simp, h, nativeOutcome_yes,
    nativeWordProbability_eq_pairing p (p q) v]

/-! ## Short values from an atom -/

/-- `Pr_{p_q}(v) = o_qv`. -/
theorem val_one (q v : Letter) :
    nativeWordProbability p (p q) [(v, true)] = (nativeTraceData p).o q v := by
  have hU : ∀ i x, quadraticMap (p i) x = tracePairing (p i) x • p i :=
    fun i x => quadraticMap_atom (p i) x (hp i)
  simp only [nativeWordProbability, nativeBranchState, List.foldl_cons, List.foldl_nil,
    nativeOutcome_yes, hU, albertTrace_smul, (hp _).2, mul_one, nativeTraceData_o]
  exact tracePairing_comm _ _

/-- `Pr_{p_q}(v^b, w) = ⟨p_w, U_{v^b} p_q⟩ = c2`. -/
theorem val_two (q v w : Letter) (b : Bool) :
    nativeWordProbability p (p q) [(v, b), (w, true)] = (nativeTraceData p).c2 b q v w := by
  have hU : ∀ i x, quadraticMap (p i) x = tracePairing (p i) x • p i :=
    fun i x => quadraticMap_atom (p i) x (hp i)
  have hUn : ∀ i x, quadraticMap (albertUnit - p i) x =
      x - (2 : ℝ) • jordanMul (p i) x + tracePairing (p i) x • p i := fun i x => by
    rw [quadraticMap_complement_idem (p i) x (hp i).1, hU]
  cases b <;>
  · simp only [nativeWordProbability, nativeBranchState, List.foldl_cons, List.foldl_nil,
      nativeOutcome_yes, nativeOutcome_no, hU, hUn, albertTrace_smul, (hp _).2, mul_one,
      tracePairing_add_right, tracePairing_sub_right, tracePairing_smul_right,
      TraceData.c2, TraceData.noConst, nativeTraceData_o, nativeTraceData_R,
      Bool.false_eq_true, ↓reduceIte, tracePairing_comm, jordanMul_comm]

omit hp in
/-- The double pairing `⟨p_A ∘ p_x, p_y ∘ p_z⟩` is `(ω_y + ω_z)/2`, ω by middle letter,
written in the orientation produced by expanding `U_{e-p_y} U_{e-p_x} p_A`. -/
theorem dpair_native (x y z : Letter) (h : IsOrderingBCD x y z) :
    (nativeTraceData p).dpair y z =
      tracePairing (p z) (jordanMul (p y) (jordanMul (p x) (p 0))) := by
  have key : tracePairing (p z) (jordanMul (p y) (jordanMul (p x) (p 0))) =
      tracePairing (jordanMul (p 0) (p x)) (jordanMul (p y) (p z)) := by
    rw [tracePairing_comm, jordanMul_comm (p y), tracePairing_associative,
      jordanMul_comm (p x)]
  rw [key]
  unfold IsOrderingBCD at h
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp at h <;>
  · simp [TraceData.dpair, nativeTraceData, fpOmega1, fpOmega2, fpOmega3,
      fpDoublePair1, fpDoublePair2, fpDoublePair3, jordanMul_comm (p 2) (p 1), jordanMul_comm (p 3) (p 1), jordanMul_comm (p 3) (p 2)]
    ring

/-- `Pr_{p_A}(x^a, y^b, z) = ⟨p_z, U_{y^b} U_{x^a} p_A⟩ = c3`. -/
theorem val_three (x y z : Letter) (a b : Bool) (h : IsOrderingBCD x y z) :
    nativeWordProbability p (p 0) [(x, a), (y, b), (z, true)] =
      (nativeTraceData p).c3 a b x y z := by
  have hU : ∀ i x, quadraticMap (p i) x = tracePairing (p i) x • p i :=
    fun i x => quadraticMap_atom (p i) x (hp i)
  have hUn : ∀ i x, quadraticMap (albertUnit - p i) x =
      x - (2 : ℝ) • jordanMul (p i) x + tracePairing (p i) x • p i := fun i x => by
    rw [quadraticMap_complement_idem (p i) x (hp i).1, hU]
  have hd := dpair_native p x y z h
  cases a <;> cases b <;>
  · simp only [nativeWordProbability, nativeBranchState, List.foldl_cons, List.foldl_nil,
      nativeOutcome_yes, nativeOutcome_no, hU, hUn, albertTrace_smul, (hp _).2, mul_one,
      tracePairing_add_right, tracePairing_sub_right, tracePairing_smul_right,
      jordanMul_add_right, jordanMul_sub_right, jordanMul_smul_right,
      TraceData.c3, TraceData.noConst, nativeTraceData_o, nativeTraceData_R, hd]
    simp only [tracePairing_comm, jordanMul_comm] <;>
    ring

/-! ## The native instance of `TableValues` -/

/-- **Native table values.** For four atoms of `J = H₃(𝕆)`, the word probabilities
from `p_A` satisfy the Albert-side interface with the trace data of the atoms. -/
theorem tableValues_native :
    TableValues (nativeTraceData p) (nativeWordProbability p (p 0)) where
  empty := (hp 0).2
  yesA_head u := by
    change nativeWordProbability p (quadraticMap (nativeOutcome p (0, true)) (p 0)) u = _
    rw [nativeOutcome_yes, quadraticMap_atom _ _ (hp 0), tracePairing_atom_self _ (hp 0),
      one_smul]
  mid1 t q v := by rw [prob_mid p hp, val_one p hp]
  long1 t q v := by
    have e : t ++ [(q, true), (v, true), (q, true)] =
        t ++ (q, true) :: ([(v, true)] ++ purityMirror [(v, true)] ++ [(q, true)]) := by
      simp [purityMirror]
    rw [e, prob_long p hp, val_one p hp]
  mid2 t q v w b := by rw [prob_mid p hp, val_two p hp]
  long2 t q v w b := by
    have e : t ++ [(q, true), (v, b), (w, true), (v, b), (q, true)] =
        t ++ (q, true) :: ([(v, b), (w, true)] ++ purityMirror [(v, b), (w, true)] ++
          [(q, true)]) := by
      simp [purityMirror]
    rw [e, prob_long p hp, val_two p hp]
  mid3 t x y z a b h := by rw [prob_mid p hp, val_three p hp x y z a b h]
  long3 t x y z a b h := by
    have e : t ++ [(0, true), (x, a), (y, b), (z, true), (y, b), (x, a), (0, true)] =
        t ++ (0, true) :: ([(x, a), (y, b), (z, true)] ++
          purityMirror [(x, a), (y, b), (z, true)] ++ [(0, true)]) := by
      simp [purityMirror]
    rw [e, prob_long p hp, val_three p hp x y z a b h]

/-! ## Conditioning `e/3 → p_A` -/

/-- `Pr_{e/3}(A, u) = (1/3) Pr_{p_A}(u)`, because `U_{p_A}(e/3) = p_A/3`. -/
theorem e3_conditioning (u : Word Letter) :
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) ((0, true) :: u) =
      (1 / 3) * nativeWordProbability p (p 0) u := by
  change nativeWordProbability p
      (quadraticMap (nativeOutcome p (0, true)) ((1 / 3 : ℝ) • albertUnit)) u = _
  rw [nativeOutcome_yes, quadraticMap_smul_right, quadraticMap_unit_argument, (hp 0).1,
    nativeWordProbability_smul]

end Native

/-! ## From a representation matching the `e/3` table to the walk-form hypotheses -/

section Bridge

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [StarModule ℝ A]

/-- `M` reproduces, from `e/3`, the Albert probabilities of the words `(A, u)`, `u ∈ S`. -/
def ReproducesE3 (M : AlgebraicProjectiveData Letter A) (p : Fin 4 → Albert)
    (S : Set (Word Letter)) : Prop :=
  ∀ u ∈ S, M.probability ((0, true) :: u) =
    nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) ((0, true) :: u)

variable (M : AlgebraicProjectiveData Letter A) (p : Fin 4 → Albert)
  (hp : ∀ i, IsAtom (p i)) {S : Set (Word Letter)}
include hp

theorem probability_yesA_of_e3 (hM : ReproducesE3 M p S) (hS : [] ∈ S) :
    M.probability [(0, true)] = 1 / 3 := by
  rw [hM [] hS, e3_conditioning p hp]
  change (1 / 3 : ℝ) * albertTrace (p 0) = 1 / 3
  rw [(hp 0).2, mul_one]

theorem probability_yesA_pos_of_e3 (hM : ReproducesE3 M p S) (hS : [] ∈ S) :
    0 < M.probability [(0, true)] := by
  rw [probability_yesA_of_e3 M p hp hM hS]; norm_num

/-- The conditioned walk form of a representation matching the `e/3` table on
`(A, S)` reproduces the Albert table from `p_A` on `S`
(paper eq:cer:H: `‖P_u ξ‖² = 3 Pr_{e/3}(A,u) = Pr_{p_A}(u)`). -/
theorem ofAlgebraic_reproduces_native (hM : ReproducesE3 M p S) (hS : [] ∈ S)
    (h : 0 < M.probability [(0, true)]) :
    (WalkForm.ofAlgebraic M h).Reproduces S (nativeWordProbability p (p 0)) := by
  apply WalkForm.ofAlgebraic_reproduces
  intro u hu
  rw [hM u hu, e3_conditioning p hp, probability_yesA_of_e3 M p hp hM hS]
  ring

/-- **Bridge, paper shape.** If `M` reproduces, from `e/3`, the octonionic probability of
every word of length at most seven that begins with "yes" on `A`, then `Pr(A) = 1/3 > 0`
and the conditioned walk form reproduces the Albert table from `p_A` on all words of
length at most six; hence lem:cer:short (`ShortRules`), hypotheses (i)–(iii) of
lem:cer:gram28 (`Gram28Hyp`) on that word set, and the rule package of Lemma A
(`Gram28Rules`), all with the native trace data. -/
theorem lengthSeven_e3_rules
    (hM : ∀ w : Word Letter, w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :
    ∃ h : 0 < M.probability [(0, true)],
      (WalkForm.ofAlgebraic M h).Reproduces {u | u.length ≤ 6}
          (nativeWordProbability p (p 0)) ∧
        ShortRules (WalkForm.ofAlgebraic M h) (nativeTraceData p) ∧
        Gram28Hyp (WalkForm.ofAlgebraic M h) (nativeTraceData p) {u | u.length ≤ 6} ∧
        Gram28Rules (WalkForm.ofAlgebraic M h) (nativeTraceData p) := by
  have hE : ReproducesE3 M p {u | u.length ≤ 6} := fun u hu =>
    hM _ (by simp only [List.length_cons]; exact Nat.succ_le_succ hu) rfl
  have hnil : ([] : Word Letter) ∈ {u : Word Letter | u.length ≤ 6} := by simp
  have h := probability_yesA_pos_of_e3 M p hp hE hnil
  have hrep := ofAlgebraic_reproduces_native M p hp hE hnil h
  have hT := tableValues_native p hp
  have hS : ∀ u : Word Letter, u.length ≤ 6 → u ∈ {u : Word Letter | u.length ≤ 6} :=
    fun _ hu => hu
  have hG := WalkForm.gram28Hyp_of_lengthSix hrep hT hS
  exact ⟨h, hrep, WalkForm.shortRules_of_table hrep hT hS, hG, WalkForm.Gram28Hyp.rules hG hrep hT⟩

/-- **Input of Lemma A (`lemmaA_e3`), native form.** A representation reproducing, from
`e/3`, the octonionic probability of every word of length at most seven that begins with
"yes" on `A` gives, for its conditioned walk form, exactly the two hypotheses of
`lemmaA_e3`: the table from `p_A` on the words of length at most six (`wordsE3`) and
`TableValues` with `τ = nativeTraceData p`. -/
theorem lemmaA_e3_inputs
    (hM : ∀ w : Word Letter, w.length ≤ 7 → w.head? = some (0, true) →
      M.probability w = nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) :
    ∃ h : 0 < M.probability [(0, true)],
      (WalkForm.ofAlgebraic M h).Reproduces {u | u.length ≤ 6}
          (nativeWordProbability p (p 0)) ∧
        TableValues (nativeTraceData p) (nativeWordProbability p (p 0)) := by
  obtain ⟨h, hrep, -⟩ := lengthSeven_e3_rules M p hp hM
  exact ⟨h, hrep, tableValues_native p hp⟩

end Bridge

/-! ## Merge closure for reduced-only word sets -/

/-- The table facts that let a word set be closed under merging equal neighbours and
under the null words `(…, i, ī, …)`. -/
structure MergeValues (f : Word Letter → ℝ) : Prop where
  merge : ∀ (u : Word Letter) (a : Outcome Letter) (v : Word Letter),
    f (u ++ a :: a :: v) = f (u ++ a :: v)
  yes_no : ∀ (u : Word Letter) (i : Letter) (v : Word Letter),
    f (u ++ (i, true) :: (i, false) :: v) = 0
  no_yes : ∀ (u : Word Letter) (i : Letter) (v : Word Letter),
    f (u ++ (i, false) :: (i, true) :: v) = 0

/-- Closure of a word set under un-merging equal neighbours, plus all null words. -/
inductive MergeClosure (S : Set (Word Letter)) : Word Letter → Prop
  | base {u : Word Letter} : u ∈ S → MergeClosure S u
  | merge (u : Word Letter) (a : Outcome Letter) (v : Word Letter) :
      MergeClosure S (u ++ a :: v) → MergeClosure S (u ++ a :: a :: v)
  | yes_no (u : Word Letter) (i : Letter) (v : Word Letter) :
      MergeClosure S (u ++ (i, true) :: (i, false) :: v)
  | no_yes (u : Word Letter) (i : Letter) (v : Word Letter) :
      MergeClosure S (u ++ (i, false) :: (i, true) :: v)

theorem subset_mergeClosure (S : Set (Word Letter)) : S ⊆ {u | MergeClosure S u} :=
  fun _ h => MergeClosure.base h

/-- A walk form reproducing a merge-compatible table on `S` reproduces it on the merge
closure of `S`. -/
theorem WalkForm.Reproduces.mergeClosure {V : Type*} [AddCommGroup V] [Module ℝ V]
    {W : WalkForm V} {S : Set (Word Letter)} {f : Word Letter → ℝ}
    (hrep : W.Reproduces S f) (hf : MergeValues f) : W.Reproduces {u | MergeClosure S u} f := by
  intro u hu
  induction hu with
  | base h => exact hrep _ h
  | merge u a v _ ih => rw [W.vec_merge, ih, hf.merge]
  | yes_no u i v => rw [W.vec_yes_no, hf.yes_no]; simp [WalkForm.normSq]
  | no_yes u i v => rw [W.vec_no_yes, hf.no_yes]; simp [WalkForm.normSq]

/-- `U_{e-q} U_q = 0` for an idempotent `q`. -/
theorem quadraticMap_complement_comp (q x : Albert) (hq : jordanMul q q = q) :
    quadraticMap (albertUnit - q) (quadraticMap q x) = 0 := by
  have hL : jordanMul q (quadraticMap q x) = quadraticMap q x := by
    have h : quadraticMap q x ∈ Set.range (quadraticMap q) := ⟨x, rfl⟩
    rw [quadraticMap_idempotent_range q hq] at h
    exact h
  rw [quadraticMap_complement_idem _ _ hq, hL, quadraticMap_idempotent_comp q x hq]
  module

/-- `U_q U_{e-q} = 0` for an idempotent `q`. -/
theorem quadraticMap_comp_complement (q x : Albert) (hq : jordanMul q q = q) :
    quadraticMap q (quadraticMap (albertUnit - q) x) = 0 := by
  have h := quadraticMap_complement_comp (albertUnit - q) x (complementary_idempotent q hq)
  rwa [sub_sub_cancel] at h

theorem nativeWordProbability_cons' (p : Fin 4 → Albert) (X : Albert) (a : Outcome Letter)
    (w : Word Letter) :
    nativeWordProbability p X (a :: w) =
      nativeWordProbability p (quadraticMap (nativeOutcome p a) X) w := rfl

/-- The native word functional (any state, idempotent tests) is merge-compatible. -/
theorem mergeValues_native (p : Fin 4 → Albert) (hp : ∀ i, jordanMul (p i) (p i) = p i)
    (ρ : Albert) : MergeValues (nativeWordProbability p ρ) where
  merge u a v := by
    simp only [native_probability_append, nativeWordProbability_cons']
    rw [quadraticMap_idempotent_comp _ _ (nativeOutcome_idempotent p hp a)]
  yes_no u i v := by
    simp only [native_probability_append, nativeWordProbability_cons', nativeOutcome_yes,
      nativeOutcome_no]
    rw [quadraticMap_complement_comp _ _ (hp i), ← zero_smul ℝ (0 : Albert),
      nativeWordProbability_smul, zero_mul]
  no_yes u i v := by
    simp only [native_probability_append, nativeWordProbability_cons', nativeOutcome_yes,
      nativeOutcome_no]
    rw [quadraticMap_comp_complement _ _ (hp i), ← zero_smul ℝ (0 : Albert),
      nativeWordProbability_smul, zero_mul]

/-! ## The ω index: general identity -/

/-- **ω index identity.** For every four elements of `J` and every ordering `x, y, z`
of `B, C, D`, `om y = ⟨p_A, {p_x p_y p_z}⟩`: the binding through `fpOmega1..3`
is indexed by the middle letter of the Jordan triple.  A rotated binding (for
instance through the indices of `nativeCornerQ`) would make this identity fail
wherever the three ω differ. -/
theorem nativeTraceData_om_eq_triple (p : Fin 4 → Albert) (x y z : Letter)
    (h : IsOrderingBCD x y z) :
    (nativeTraceData p).om y = tracePairing (p 0) (jordanTriple (p x) (p y) (p z)) := by
  rw [tracePairing_jordanTriple_partitions]
  unfold IsOrderingBCD at h
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp at h <;>
  · simp [nativeTraceData, fpOmega1, fpOmega2, fpOmega3,
      fpDoublePair1, fpDoublePair2, fpDoublePair3, nativePairPartition,
      jordanMul_comm (p 2) (p 1), jordanMul_comm (p 3) (p 1), jordanMul_comm (p 3) (p 2)] <;>
    ring

end AlbertSequential.LengthSeven
