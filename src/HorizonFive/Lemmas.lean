/- SPDX-License-Identifier: Apache-2.0 -/
module

public import HorizonFive.Groups
public import Mathlib.Algebra.Star.Free

/-! # The three lemmas of companion `app:cert:h5` and the two imported results, as typed statements

Nothing in this file is assumed globally: each statement is a `Prop` (a `def`), used only as an
explicit hypothesis of a theorem.  The proved sub-lemmas at the end are unconditional.

Paper lemmas (hypotheses of the assembly theorem `horizonFive_of_lemmas`; each is proved elsewhere):

* `ReflectionClassConsistency`  = lem:cer:h5:refl(a), proved as `reflectionClassConsistency` (ReflA);
* `ReflectionContraction`       = lem:cer:h5:refl(b), proved as `reflectionContraction` (Contraction);
* `RecognitionThroughFive`      = lem:cer:h5:lift; as typed it fails at `n = 0`
  (`not_recognitionThroughFive`); the case `1 ≤ n` is `recognitionThroughFivePos` (Recognition);
* `TransferThroughSeven`        = lem:cer:h5:seven, proved as `transferThroughSeven` (Final).

Imported literature results (NOT axiomatized; precisely typed statements, not used as hypotheses
by any theorem in this repository):

* `CohnReversibleTheorem` — Cohn's reversible theorem in the form companion `app:cert:h5` uses
  (McCrimmon, A Taste of Jordan Algebras, App. A; locator unchecked);
* `SerreAxisProposition` — Serre, Trees, Ch. I §6.4 Prop. 24, the no-fixed-vertex case
  (locator unchecked).

Reflections are given by presentations `(v, i)` with `v` an arbitrary word; `ς(v, i) = ρ(v) s_i`
is evaluated natively as `U_{s_{v_1}} ⋯ U_{s_{v_k}} s_i`.  The paper's well-definedness
(`ς` depends only on the group element `v r_i v⁻¹`) plus its lemma give exactly the presentation
form used here; group equalities are tested on reduced forms `reduceRW`. -/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace AlbertSequential.HorizonFive

open AlbertSequential AlbertSequential.NativeAnalysis

/-! ## Reflections -/

/-- A presentation `v r_i v⁻¹` of a reflection of `G`. -/
structure Refl where
  v : List Test
  i : Test

/-- The word `v i v^R` of a reflection presentation. -/
def Refl.word (t : Refl) : List Test := t.v ++ [t.i] ++ t.v.reverse

/-- `ς(t) = ρ(v) s_i = U_{s_{v_1}} ⋯ U_{s_{v_k}} s_i` in the Albert algebra. -/
def varsigma (p : Test → Albert) (t : Refl) : Albert :=
  t.v.foldr (fun a y => quadraticMap (nativeSymmetry p a) y) (nativeSymmetry p t.i)

/-- The reversal class `[g] = (g + g⁻¹)/2` of the group element of a word (`g⁻¹` is the reversed
word because the generators are involutions). -/
def classElt (l : List Test) : UniversalProjectionAlgebra 4 :=
  (1 / 2 : ℝ) • (groupElt l + groupElt l.reverse)

/-- **lem:cer:h5:refl(a)** (paper lemma; proved as `reflectionClassConsistency`, `HorizonFive.ReflA`). If `t'u' = tu` or
`t'u' = (tu)⁻¹` in `G`, then `ς(t) ∘ ς(u) = ς(t') ∘ ς(u')`, for any four atoms. -/
def ReflectionClassConsistency : Prop :=
  ∀ p : Test → Albert, (∀ i, IsAtom (p i)) → ∀ t u t' u' : Refl,
    (reduceRW (t'.word ++ u'.word) = reduceRW (t.word ++ u.word) ∨
      reduceRW (t'.word ++ u'.word) = reduceRW (t.word ++ u.word).reverse) →
    jordanMul (varsigma p t) (varsigma p u) = jordanMul (varsigma p t') (varsigma p u')

/-- **lem:cer:h5:refl(b)** (paper lemma; proved as `reflectionContraction`, `HorizonFive.Contraction`). There is a Jordan polynomial `K`
of degree `|tu|` with `σ̂(K) = [tu]` and `ν̂(K) = ς(t) ∘ ς(u)` (for any four atoms; `K` does not
depend on the atoms). -/
def ReflectionContraction : Prop :=
  ∀ t u : Refl, ∃ K : JPoly Test,
    K.deg = (reduceRW (t.word ++ u.word)).1.length ∧
    specialEval K = classElt (t.word ++ u.word) ∧
    ∀ p : Test → Albert, (∀ i, IsAtom (p i)) →
      albertEval p K = jordanMul (varsigma p t) (varsigma p u)

/-! ## The Clifford volume functional `ℓ` -/

/-- Left multiplication of `σ γ_S` (`S` in increasing order) by `γ_i`, in `Cl_{4,0}`:
move `γ_i` past the smaller elements of `S`, then cancel or insert. -/
def cliffMul (i : Test) (x : ℤ × Finset Test) : ℤ × Finset Test :=
  ((-1) ^ (x.2.filter (· < i)).card * x.1, symmDiff x.2 {i})

/-- The image `± γ_S` of the group element of a word under `r_i ↦ γ_i`. -/
def cliffImage (l : List Test) : ℤ × Finset Test := l.foldr cliffMul (1, ∅)

/-- `ℓ` on words: the coefficient of `γ_1γ_2γ_3γ_4`. -/
def cliffVol (l : List Test) : ℤ :=
  if (cliffImage l).2 = Finset.univ then (cliffImage l).1 else 0

/-- **lem:cer:h5:lift** (paper lemma). As typed here it fails at `n = 0`
(`not_recognitionThroughFive`); the case `1 ≤ n` is proved as `recognitionThroughFivePos`. A reversal-fixed `y ∈ ℝ[G]`, given
by its coefficients on reduced words of length at most `n ≤ 5` in each of which `r_j` occurs
exactly once, with `ℓ(y) = 0`, is `σ̂(K)` for a Jordan polynomial `K` of degree at most `n` and of
degree one in `x_j`. -/
def RecognitionThroughFive : Prop :=
  ∀ (n : ℕ), n ≤ 5 → ∀ (j : Test) (y : List Test →₀ ℝ),
    (∀ l ∈ y.support, reducedB l = true ∧ l.length ≤ n ∧ l.count j = 1) →
    (∀ l, y l.reverse = y l) →
    (y.sum fun l a => a * (cliffVol l : ℝ)) = 0 →
    ∃ K : JPoly Test, K.deg ≤ n ∧ K.LinearIn j ∧
      specialEval K = y.sum fun l a => a • groupElt l

/-- **lem:cer:h5:seven** (paper lemma; proved as `transferThroughSeven`, `HorizonFive.Final`). For any four atoms: if `F` has
degree at most seven and `σ̂(F) = 0`, then `ν̂(F) = 0`. -/
def TransferThroughSeven : Prop :=
  ∀ p : Test → Albert, (∀ i, IsAtom (p i)) →
    ∀ F : JComb, (∀ G ∈ F.support, G.deg ≤ 7) → specialEvalC F = 0 → albertEvalC p F = 0

/-! ## Imported results (hypotheses only) -/

/-- Multihomogeneity of a Jordan expression, with letter weights `wt`. -/
inductive IsHomog {Y : Type} (wt : Y → Test → ℕ) : (Test → ℕ) → JPoly Y → Prop
  | one : IsHomog wt 0 .one
  | var (y : Y) : IsHomog wt (wt y) (.var y)
  | add (μ : Test → ℕ) (a b : JPoly Y) : IsHomog wt μ a → IsHomog wt μ b →
      IsHomog wt μ (.add a b)
  | smul (μ : Test → ℕ) (r : ℝ) (a : JPoly Y) : IsHomog wt μ a → IsHomog wt μ (.smul r a)
  | mul (μ ν : Test → ℕ) (a b : JPoly Y) : IsHomog wt μ a → IsHomog wt ν b →
      IsHomog wt (μ + ν) (.mul a b)

/-- The free associative algebra `ℝ⟨x_1, …, x_4⟩`; its `star` is word reversal. -/
abbrev FreeAssoc := FreeAlgebra ℝ Test

/-- The monomial of a word. -/
def freeWord (w : List Test) : FreeAssoc := (w.map (FreeAlgebra.ι ℝ)).prod

/-- Elements of multidegree `μ`. -/
def homogSpan (μ : Test → ℕ) : Submodule ℝ FreeAssoc :=
  Submodule.span ℝ (freeWord '' {w | ∀ i, w.count i = μ i})

/-- The associative expansion of a Jordan expression (letters `x_i ↦ x_i`). -/
def assocExpansion (K : JPoly Test) : FreeAssoc :=
  (specialTarget FreeAssoc).eval (FreeAlgebra.ι ℝ) K

/-- The tetrad `{x_{σ0} x_{σ1} x_{σ2} x_{σ3}} = x_{σ0}x_{σ1}x_{σ2}x_{σ3} + x_{σ3}x_{σ2}x_{σ1}x_{σ0}`. -/
def tetrad (σ : Equiv.Perm Test) : FreeAssoc :=
  freeWord [σ 0, σ 1, σ 2, σ 3] + freeWord [σ 3, σ 2, σ 1, σ 0]

/-- Expansion of Jordan expressions in the letters and one extra letter `none ↦ tetrad`. -/
def tetradExpansion (σ : Equiv.Perm Test) (K : JPoly (Option Test)) : FreeAssoc :=
  (specialTarget FreeAssoc).eval (fun y => match y with
    | none => tetrad σ
    | some i => FreeAlgebra.ι ℝ i) K

/-- Letter weights: `x_i` has multidegree `e_i`, the tetrad has `(1,1,1,1)`. -/
def tetradWeight : Option Test → Test → ℕ
  | none => fun _ => 1
  | some i => Pi.single i 1

/-- **Imported (Cohn's reversible theorem, as used in companion `app:cert:h5`; hypothesis only).**
Over `ℝ`, a reversible (star-fixed) element of multidegree `μ`:
(three) if `μ` involves at most three letters, is the associative expansion of a Jordan
polynomial of multidegree `μ`;
(four) for every ordering `σ` of the four letters, is the expansion of a Jordan expression of
multidegree `μ` in the letters and the one tetrad `{x_{σ0}x_{σ1}x_{σ2}x_{σ3}}`. -/
structure CohnReversibleTheorem : Prop where
  three : ∀ μ : Test → ℕ, (Finset.univ.filter fun i => μ i ≠ 0).card ≤ 3 →
    ∀ y ∈ homogSpan μ, star y = y →
      ∃ K : JPoly Test, IsHomog (fun i => Pi.single i 1) μ K ∧ assocExpansion K = y
  four : ∀ (σ : Equiv.Perm Test) (μ : Test → ℕ), ∀ y ∈ homogSpan μ, star y = y →
    ∃ K : JPoly (Option Test), IsHomog tetradWeight μ K ∧ tetradExpansion σ K = y

/-! Trees, stated from scratch (no `SimpleGraph` library is used).  Vertices `V`,
adjacency `adj`; a walk is a vertex list with consecutive vertices adjacent; it backtracks if some
`x_k = x_{k+2}`.  A tree is a connected, loopless, symmetric graph with no closed
non-backtracking walk of positive length. -/

/-- Consecutive vertices adjacent. -/
def WalkAdj {V : Type} (adj : V → V → Prop) : List V → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => adj a b ∧ WalkAdj adj (b :: l)

/-- No immediate backtracking `x_k = x_{k+2}`. -/
def NoBacktrack {V : Type} : List V → Prop
  | a :: b :: c :: l => a ≠ c ∧ NoBacktrack (b :: c :: l)
  | _ => True

/-- `l` is a walk from `u` to `v` with `n` edges. -/
def IsWalkOf {V : Type} (adj : V → V → Prop) (u v : V) (n : ℕ) (l : List V) : Prop :=
  WalkAdj adj l ∧ l.head? = some u ∧ l.getLast? = some v ∧ l.length = n + 1

/-- Graph distance. -/
def treeDist {V : Type} (adj : V → V → Prop) (u v : V) : ℕ :=
  sInf {n | ∃ l, IsWalkOf adj u v n l}

/-- Trees. -/
structure IsTreeAdj {V : Type} (adj : V → V → Prop) : Prop where
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ u, ¬ adj u u
  connected : ∀ u v, ∃ n l, IsWalkOf adj u v n l
  acyclic : ∀ l : List V, WalkAdj adj l → NoBacktrack l → l.head? = l.getLast? → l.length ≤ 1

/-- The least displacement `min_P d(P, sP)`. -/
def minDisplacement {V : Type} (adj : V → V → Prop) (s : V ≃ V) : ℕ :=
  sInf (Set.range fun P => treeDist adj P (s P))

/-- **Imported (Serre, Trees, Ch. I §6.4 Prop. 24, case without fixed vertex; hypothesis only).**
For an automorphism `s` of a tree without inversion and without fixed vertex, the least
displacement `m` is positive and the set `Min(s)` of vertices of least displacement is a line
(a bi-infinite path) on which `s` acts by a translation of amplitude `m`. -/
def SerreAxisProposition : Prop :=
  ∀ (V : Type) (adj : V → V → Prop), IsTreeAdj adj → ∀ s : V ≃ V,
    (∀ u v, adj u v ↔ adj (s u) (s v)) →
    (∀ u v, adj u v → ¬ (s u = v ∧ s v = u)) → (∀ P, s P ≠ P) →
      0 < minDisplacement adj s ∧
      ∃ ℓ : ℤ → V, Function.Injective ℓ ∧ (∀ n, adj (ℓ n) (ℓ (n + 1))) ∧
        Set.range ℓ = {P | treeDist adj P (s P) = minDisplacement adj s} ∧
        ∃ k : ℤ, k.natAbs = minDisplacement adj s ∧ ∀ n, s (ℓ n) = ℓ (n + k)

/-! ## Proved sub-lemmas -/

section Associative
variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The Jordan triple product in a target. -/
def tripleOp {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) (a b c : E) : E :=
  T.mul (T.mul a b) c + T.mul (T.mul c b) a - T.mul (T.mul a c) b

theorem eval_triple {E : Type*} [AddCommGroup E] [Module ℝ E] (T : JTarget E) {X : Type}
    (v : X → E) (a b c : JPoly X) :
    T.eval v (JPoly.triple a b c) = tripleOp T (T.eval v a) (T.eval v b) (T.eval v c) := by
  simp only [JPoly.triple, JTarget.eval, tripleOp]
  module

/-- `{a,b,c}` has associative expansion `(abc + cba)/2`. -/
theorem special_tripleOp (a b c : R) :
    tripleOp (specialTarget R) a b c = (1 / 2 : ℝ) • (a * b * c + c * b * a) := by
  simp only [tripleOp, specialTarget_mul, smul_mul_assoc, mul_smul_comm, _root_.mul_add, add_mul,
    mul_assoc, smul_add, smul_smul]
  module

/-- The length-five step of lem:cer:h5:lift: with `d² = 1`, the special value of
`{a,b,c} + U_d{a,b,c}` equals `d ∘ T`, `T = {dabc} = dabc + cbad`, namely
`(abc + cba)/2 + (dabcd + dcbad)/2`. -/
theorem special_lift_length_five (a b c d : R) (hd : d * d = 1) :
    tripleOp (specialTarget R) a b c + (specialTarget R).Uop d (tripleOp (specialTarget R) a b c) =
      (specialTarget R).mul d (d * a * b * c + c * b * a * d) ∧
    (specialTarget R).mul d (d * a * b * c + c * b * a * d) =
      (1 / 2 : ℝ) • (a * b * c + c * b * a) + (1 / 2 : ℝ) • (d * a * b * c * d + d * c * b * a * d) := by
  have hd' : ∀ z, d * (d * z) = z := fun z => by rw [← mul_assoc, hd, one_mul]
  have h2 : (specialTarget R).mul d (d * a * b * c + c * b * a * d) =
      (1 / 2 : ℝ) • (a * b * c + c * b * a) +
        (1 / 2 : ℝ) • (d * a * b * c * d + d * c * b * a * d) := by
    simp only [specialTarget_mul, _root_.mul_add, add_mul, mul_assoc, hd, hd', _root_.mul_one]
    module
  refine ⟨?_, h2⟩
  rw [h2, special_tripleOp, specialTarget_Uop]
  simp only [smul_mul_assoc, mul_smul_comm, _root_.mul_add, add_mul, mul_assoc, smul_add]
  try module

/-- Tetrads alternate modulo Jordan triple products:
`{abcd} + {bacd} = 4{a∘b, c, d}`, `{abcd} + {acbd} = 4{a, b∘c, d}`,
`{abcd} + {abdc} = 4{a, b, c∘d}` (associative expansions). -/
theorem special_tetrad_alternation (a b c d : R) :
    let T := specialTarget R
    let tet : R → R → R → R → R := fun x y z w => x * y * z * w + w * z * y * x
    (tet a b c d + tet b a c d = (4 : ℝ) • tripleOp T (T.mul a b) c d) ∧
    (tet a b c d + tet a c b d = (4 : ℝ) • tripleOp T a (T.mul b c) d) ∧
    (tet a b c d + tet a b d c = (4 : ℝ) • tripleOp T a b (T.mul c d)) := by
  intro T tet
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [T, tet, special_tripleOp, specialTarget_mul, smul_mul_assoc, mul_smul_comm,
      _root_.mul_add, add_mul, mul_assoc, smul_add, smul_smul]
    module

end Associative

section Clifford
variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- (eq:cer:h5:volume): if `γ_i² = 1` and `γ_iγ_k = -γ_kγ_i` (`i ≠ k`), the span of `1` and the
`γ_i` is closed under `X ∘ Y = (XY + YX)/2`, so every Jordan polynomial evaluated at the `γ_i`
lies in it (and has no `γ_1γ_2γ_3γ_4` component). -/
theorem clifford_eval_mem_span (γ : Test → R) (hsq : ∀ i, γ i * γ i = 1)
    (hanti : ∀ i k, i ≠ k → γ i * γ k = - (γ k * γ i)) (F : JPoly Test) :
    (specialTarget R).eval γ F ∈ Submodule.span ℝ (insert (1 : R) (Set.range γ)) := by
  set S := Submodule.span ℝ (insert (1 : R) (Set.range γ)) with hS
  have hgen : ∀ g ∈ insert (1 : R) (Set.range γ), ∀ g' ∈ insert (1 : R) (Set.range γ),
      (specialTarget R).mul g g' ∈ S := by
    intro g hg g' hg'
    rcases hg with rfl | ⟨i, rfl⟩ <;> rcases hg' with rfl | ⟨k, rfl⟩
    · rw [specialTarget_mul]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_) <;> rw [one_mul] <;>
        exact Submodule.subset_span (Set.mem_insert _ _)
    · rw [specialTarget_mul]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_) <;>
        simp only [one_mul, _root_.mul_one] <;>
        exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
    · rw [specialTarget_mul]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_) <;>
        simp only [one_mul, _root_.mul_one] <;>
        exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    · by_cases hik : i = k
      · subst hik
        rw [specialTarget_mul, hsq]
        refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_) <;>
          exact Submodule.subset_span (Set.mem_insert _ _)
      · rw [specialTarget_mul, hanti i k hik, neg_add_cancel, smul_zero]
        exact S.zero_mem
  -- closure under the product, by bilinearity
  have hleft : ∀ g ∈ insert (1 : R) (Set.range γ), ∀ y ∈ S, (specialTarget R).mul g y ∈ S := by
    intro g hg y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact hgen g hg x hx
    | zero =>
      rw [show (0 : R) = (0 : ℝ) • (0 : R) by simp, (specialTarget R).mul_smul, zero_smul]
      exact S.zero_mem
    | add x y _ _ hx hy => rw [(specialTarget R).mul_add]; exact S.add_mem hx hy
    | smul r x _ hx => rw [(specialTarget R).mul_smul]; exact S.smul_mem r hx
  have hmul : ∀ x ∈ S, ∀ y ∈ S, (specialTarget R).mul x y ∈ S := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem g hg => exact hleft g hg y hy
    | zero =>
      rw [show (0 : R) = (0 : ℝ) • (0 : R) by simp, (specialTarget R).smul_mul, zero_smul]
      exact S.zero_mem
    | add x z _ _ hx hz => rw [(specialTarget R).add_mul]; exact S.add_mem hx hz
    | smul r x _ hx => rw [(specialTarget R).smul_mul]; exact S.smul_mem r hx
  induction F with
  | one => exact Submodule.subset_span (Set.mem_insert _ _)
  | var i => exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  | add a b ha hb => exact S.add_mem ha hb
  | smul r a ha => exact S.smul_mem r ha
  | mul a b ha hb => exact hmul _ ha _ hb

end Clifford

/-- Degree bookkeeping of the final assembly: a symbol with `a ≥ 1` operators `A` and `b`
operators `C`, `a + b ≤ 5`, has degree `a + 2b ≤ 10 - a`; degree nine forces `(a,b) = (1,4)` and
degree eight forces `(a,b) = (2,3)`. -/
theorem symbol_degree_bookkeeping (a b : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ 5) :
    a + 2 * b ≤ 10 - a ∧ (a + 2 * b = 9 → a = 1 ∧ b = 4) ∧ (a + 2 * b = 8 → a = 2 ∧ b = 3) := by
  omega

/-- Lemma seven's use of the bound: four positive multiplicities with sum at most seven include a
one; at degree eight the balanced multidegree `(2,2,2,2)` has none. -/
theorem four_positive_le_seven_has_one (μ : Test → ℕ) (hpos : ∀ i, 0 < μ i)
    (hsum : μ 0 + μ 1 + μ 2 + μ 3 ≤ 7) : ∃ j, μ j = 1 := by
  by_contra h
  push Not at h
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2; have h3 := hpos 3
  have := h 0; have := h 1; have := h 2; have := h 3
  omega

end AlbertSequential.HorizonFive
