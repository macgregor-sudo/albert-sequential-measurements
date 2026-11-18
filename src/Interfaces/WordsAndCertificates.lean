module

public import Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.List.GetD

/-! Words, word probabilities, the algebraic comparator class and certificate
statement types. No witness/Gram/soundness theorem is proved in this file.
`Word` has chronological order. Native multiplication is always explicit. -/
@[expose] public section
noncomputable section
namespace AlbertSequential

abbrev Outcome (ι : Type*) := ι × Bool
abbrev Word (ι : Type*) := List (Outcome ι)

def nativeOutcome {ι : Type*} (tests : ι → Albert) (a : Outcome ι) : Albert :=
  if a.2 then tests a.1 else albertUnit - tests a.1

def nativeBranchState {ι : Type*} (tests : ι → Albert) (ρ : Albert)
    (w : Word ι) : Albert :=
  w.foldl (fun x a => quadraticMap (nativeOutcome tests a) x) ρ

def nativeWordProbability {ι : Type*} (tests : ι → Albert) (ρ : Albert)
    (w : Word ι) : ℝ := albertTrace (nativeBranchState tests ρ w)

/-- Independent effect-side recursion: first outcome is the outermost update. -/
def nativeWordEffect {ι : Type*} (tests : ι → Albert) : Word ι → Albert
  | [] => albertUnit
  | a :: w => quadraticMap (nativeOutcome tests a) (nativeWordEffect tests w)

def IsReducedWord {ι : Type*} : Word ι → Prop
  | [] => True
  | [_] => True
  | a :: b :: w => a.1 ≠ b.1 ∧ IsReducedWord (b :: w)

def algebraicOutcome {ι A : Type*} [Ring A] (P : ι → A) (a : Outcome ι) : A :=
  if a.2 then P a.1 else 1 - P a.1

/-- Last outcome multiplies on the left; no scalar traciality is used. -/
def wordAmplitude {ι A : Type*} [Ring A] (P : ι → A) (w : Word ι) : A :=
  w.foldl (fun x a => algebraicOutcome P a * x) 1

def wordOperator {ι A : Type*} [Ring A] [StarRing A]
    (P : ι → A) (w : Word ι) : A :=
  star (wordAmplitude P w) * wordAmplitude P w

/-- Alternative algebraic comparator, deliberately not named a Hilbert model.
Hilbert R/C/H models map into it (`HilbertProjectiveData.toAlgebraic`,
`QuaternionicProjectiveData.toAlgebraic`). No faithfulness,
normality, traciality, finite dimension or rank condition is imposed. -/
structure AlgebraicProjectiveData (ι A : Type*) [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] where
  projection : ι → A
  idempotent : ∀ i, projection i * projection i = projection i
  selfAdjoint : ∀ i, star (projection i) = projection i
  state : A →ₗ[ℝ] ℝ
  state_unit : state 1 = 1
  state_star : ∀ x, state (star x) = state x
  state_positive : ∀ x, 0 ≤ state (star x * x)

def AlgebraicProjectiveData.probability {ι A : Type*} [Ring A] [StarRing A]
    [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData ι A) (w : Word ι) : ℝ :=
  M.state (wordOperator M.projection w)

def AlgebraicProjectiveData.Matches {ι A : Type*} [Ring A] [StarRing A]
    [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] (M : AlgebraicProjectiveData ι A) (p : ι → Albert) (ρ : Albert) : Prop :=
  ∀ w, M.probability w = nativeWordProbability p ρ w

/-- Exact M1--M3 data for lem:cer:recon. The finite index list must equal ALL
reduced words through L. It cannot be replaced by an arbitrary sparse subset.
The reconstructed projection model and dimension=rank are not part of this structure. -/
structure FiniteGramWitness (n L : ℕ) (f : Word (Fin n) → ℝ) where
  words : Finset (Word (Fin n))
  complete : ∀ w, w ∈ words ↔ w.length ≤ L ∧ IsReducedWord w
  gram : Matrix {w // w ∈ words} {w // w ∈ words} ℝ
  positive : gram.PosSemidef
  normalized : f [] = 1
  probabilities : ∀ w ∈ words, 0 ≤ f w ∧ f w ≤ 1
  diagonal : ∀ u, gram u u = f u.val
  complement : ∀ (u v : {w // w ∈ words}) (i : Fin n),
    v.val.length < L → IsReducedWord (v.val ++ [(i, true)]) →
    ∀ (hy : v.val ++ [(i, true)] ∈ words)
      (hn : v.val ++ [(i, false)] ∈ words),
      gram u ⟨v.val ++ [(i, true)], hy⟩ +
        gram u ⟨v.val ++ [(i, false)], hn⟩ = gram u v
  orthogonal : ∀ (u v : {w // w ∈ words}) i,
    u.val.getLast? = some (i, true) → v.val.getLast? = some (i, false) →
    gram u v = 0

/-- Sparse-list statement for the eleven-step theorem of the paper (inhabited by
`Ends.Eleven.elevenWordList`). A length bound alone does not give this list or its native purity ledger. -/
structure ElevenWordList where
  baseWords : Finset (Word (Fin 4))
  cardinality : baseWords.card = 2041
  starts_at_base : ∀ w ∈ baseWords, w.head? = some (0, true)
  reduced : ∀ w ∈ baseWords, IsReducedWord w
  length_bound : ∀ w ∈ baseWords, w.length ≤ 11
  length_counts : ∀ k : Fin 11,
    (baseWords.filter (fun w => w.length = k.val + 1)).card =
      (![1, 3, 15, 36, 32, 94, 240, 180, 432, 576, 432] : Fin 11 → ℕ) k

/-- A finite rational word functional. Its support and native evaluation are
concrete; this is NOT a free-group-algebra SOS checker. -/
structure RationalWordFunctional (ι : Type*) where
  terms : List (ℚ × Word ι)

def RationalWordFunctional.evaluate {ι : Type*} (c : RationalWordFunctional ι)
    (f : Word ι → ℝ) : ℝ :=
  (c.terms.map (fun t => (t.1 : ℝ) * f t.2)).sum

/-- Typed consumer for an explicitly supplied noncommutative certificate
identity at ONE algebraic comparator. The universal rational word identity,
its parser and its semantic binder are not formalized here. -/
structure EvaluatedSquareIdentity {ι A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (P : ι → A) (c : RationalWordFunctional ι) where
  squares : List (ℚ × A)
  positive_coefficients : ∀ t ∈ squares, 0 < t.1
  identity : (c.terms.map (fun t => (t.1 : ℝ) • wordOperator P t.2)).sum =
    (squares.map (fun t => (t.1 : ℝ) • (star t.2 * t.2))).sum

/-- Tiny chronology consumers: these prove only definitional recursion. -/
example {ι : Type*} (p : ι → Albert) (ρ : Albert) :
    nativeBranchState p ρ [] = ρ := by
  simp only [nativeBranchState, List.foldl_nil]
example {ι : Type*} (p : ι → Albert) (ρ : Albert) (a b : Outcome ι) :
    nativeBranchState p ρ [a, b] =
      quadraticMap (nativeOutcome p b) (quadraticMap (nativeOutcome p a) ρ) := by
  simp only [nativeBranchState, List.foldl_cons, List.foldl_nil]
example {ι A : Type*} [Ring A] (P : ι → A) (a b : Outcome ι) :
    wordAmplitude P [a, b] = algebraicOutcome P b * (algebraicOutcome P a * 1) := by
  simp only [wordAmplitude, List.foldl_cons, List.foldl_nil]

end AlbertSequential
