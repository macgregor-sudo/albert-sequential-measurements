module

public import Interfaces.WordsAndCertificates
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Matrix

/-!
Definitions and statement types; no theorem is proved in this file.
Source: core `sec:ins` and appendix `app:mem`. Complex finite-dimensional
CP instruments below are NOT the arbitrary R/C/H positive trace-class maps
in thm:ideal or prop:cer:nearideal.
The fields of an `...Obligations` structure are statements, proved in other modules.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

abbrev ComplexMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev ChoiMatrix (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ

def IsMatrixDensity {d : ℕ} (ρ : ComplexMatrix d) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- Unnormalized Choi convention: first coordinate=input, second=output. -/
def choiAction {d : ℕ} (C : ChoiMatrix d) (X : ComplexMatrix d) : ComplexMatrix d :=
  fun k l => ∑ i, ∑ j, X i j * C (i, k) (j, l)

def choiOutputTrace {d : ℕ} (C : ChoiMatrix d) : ComplexMatrix d :=
  fun i j => ∑ k, C (i, k) (j, k)

def krausAction {d : ℕ} (K : List (ComplexMatrix d)) (X : ComplexMatrix d) :
    ComplexMatrix d := (K.map (fun V => V * X * V.conjTranspose)).sum

def krausEffect {d : ℕ} (K : List (ComplexMatrix d)) : ComplexMatrix d :=
  (K.map (fun V => V.conjTranspose * V)).sum

def HasRealEntries {d : ℕ} (X : ComplexMatrix d) : Prop :=
  ∀ i j, (X i j).im = 0

/-- General finite nonempty outcomes may depend on the test label.
Binary `Word` is imported; this distinct type has an explicit adapter below. -/
abbrev InstrumentWord {X : Type*} (A : X → Type*) := List (Sigma A)

def generalizeBinaryWord {X : Type*} (w : Word X) : InstrumentWord (fun _ : X => Bool) :=
  w.map (fun a => ⟨a.1, a.2⟩)

abbrev RawFiniteCPModel (d : ℕ) (P X : Type*) (A : X → Type*) :=
  (P → ComplexMatrix d) × ((x : X) → A x → ChoiMatrix d)

def IsNormalizedFiniteCPModel {d : ℕ} {P X : Type*} {A : X → Type*}
    [∀ x, Fintype (A x)] (r : RawFiniteCPModel d P X A) : Prop :=
  (∀ p, IsMatrixDensity (r.1 p)) ∧
  (∀ x a, (r.2 x a).PosSemidef) ∧
  (∀ x, ∑ a, choiOutputTrace (r.2 x a) = 1)

/-- Chronological fold: the first letter acts first. No conditional division;
zero-probability histories are included without an extra hypothesis. -/
def finiteCPWordState {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (p : P) (w : InstrumentWord A) : ComplexMatrix d :=
  w.foldl (fun ρ a => choiAction (r.2 a.1 a.2) ρ) (r.1 p)

def finiteCPWordProbability {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (p : P) (w : InstrumentWord A) : ℝ :=
  (Matrix.trace (finiteCPWordState r p w)).re

/-- This explicitly proves equivalence to finite Kraus data, not an assumption
that positivity of an arbitrary linear map means complete positivity. -/
structure ChoiKrausObligations (d : ℕ) : Prop where
  choi_iff_kraus : ∀ C : ChoiMatrix d, C.PosSemidef ↔
    ∃ K : List (ComplexMatrix d), ∀ X, choiAction C X = krausAction K X
  trace_preservation : ∀ C : ChoiMatrix d,
    choiOutputTrace C = 1 ↔ ∀ X, Matrix.trace (choiAction C X) = Matrix.trace X
  effect_binding : ∀ (C : ChoiMatrix d) (K : List (ComplexMatrix d)),
    (∀ X, choiAction C X = krausAction K X) → choiOutputTrace C = (krausEffect K).transpose

def MatchesAllWords {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (t : P → InstrumentWord A → ℝ) : Prop :=
  ∀ p w, finiteCPWordProbability r p w = t p w

/-- Only a finite set of labels is constrained, but ALL words on that menu
are matched. Unused coordinates of r are arbitrary normalized instruments. -/
def MatchesFiniteMenu {d : ℕ} {P X : Type*} {A : X → Type*}
    (r : RawFiniteCPModel d P X A) (t : P → InstrumentWord A → ℝ)
    (ps : Finset P) (xs : Finset X) : Prop :=
  ∀ p ∈ ps, ∀ w : InstrumentWord A,
    (∀ a ∈ w, a.1 ∈ xs) → finiteCPWordProbability r p w = t p w

/-- Fixed-D compactness, exactly normalized stationary instruments. Arbitrary
label sets, no continuity/equivariance/affine preparation-map requirement. -/
structure FixedDimensionCompactnessObligations (d : ℕ) (P X : Type*)
    (A : X → Type*) [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)] : Prop where
  parameter_compact : 0 < d → IsCompact
    {r : RawFiniteCPModel d P X A | IsNormalizedFiniteCPModel r}
  word_continuous : ∀ p w,
    Continuous (fun r : RawFiniteCPModel d P X A => finiteCPWordProbability r p w)
  finite_menu_iff : 0 < d → ∀ t : P → InstrumentWord A → ℝ,
    (∃ r : RawFiniteCPModel d P X A, IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t) ↔
    (∀ (ps : Finset P) (xs : Finset X),
      ∃ r : RawFiniteCPModel d P X A,
        IsNormalizedFiniteCPModel r ∧ MatchesFiniteMenu r t ps xs)
  finite_error_gap : 0 < d → ∀ t : P → InstrumentWord A → ℝ,
    (¬ ∃ r : RawFiniteCPModel d P X A,
      IsNormalizedFiniteCPModel r ∧ MatchesAllWords r t) →
    ∃ (F : Finset (P × InstrumentWord A)) (δ : ℝ), 0 < δ ∧
      ∀ r : RawFiniteCPModel d P X A, IsNormalizedFiniteCPModel r →
        ∃ q ∈ F, δ ≤ |finiteCPWordProbability r q.1 q.2 - t q.1 q.2|

/-- A supplied finite Kraus realization. The normalization equation concerns
the SUM over outcomes. Individual branches are generally not TP. -/
structure BinaryKrausRealization (d : ℕ) (X : Type*) where
  initial : ComplexMatrix d
  density : IsMatrixDensity initial
  kraus : X → Bool → List (ComplexMatrix d)
  normalized : ∀ x, krausEffect (kraus x true) + krausEffect (kraus x false) = 1

def binaryKrausProbability {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) (w : Word X) : ℝ :=
  (Matrix.trace (w.foldl (fun ρ a => krausAction (r.kraus a.1 a.2) ρ) r.initial)).re

def IsRealKrausRealization {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) : Prop :=
  HasRealEntries r.initial ∧ ∀ x a K, K ∈ r.kraus x a → HasRealEntries K

/-- Exact native binding for thm:cp69 and cor:ins:nohalf. It includes every
initial state and all words; real matrix data is not dropped. Construction,
spinor orientation and trace preservation are its fields (`nativeFiniteSimulationObligations`). -/
structure NativeFiniteSimulationObligations : Prop where
  general : ∀ (n : ℕ) (p : Fin n → Albert), (∀ i, IsAtom (p i)) →
    ∀ ρ, IsDensity ρ → ∃ r : BinaryKrausRealization (17 * n + 1) (Fin n),
      IsRealKrausRealization r ∧ ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w
  no_half_component : ∀ (n : ℕ) (p : Fin n → Albert), (∀ i, IsAtom (p i)) →
    ∀ ρ, IsDensity ρ →
    (∃ (i : Fin n) (t : ℝ) (y : Albert), 0 ≤ t ∧ IsPositive y ∧
      jordanMul (p i) y = 0 ∧ ρ = t • p i + y) →
    ∃ r : BinaryKrausRealization (17 * n) (Fin n), IsRealKrausRealization r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w

/- OperationalBoundaries.lean gives the typed statements for the
full sharp dilation (embedding C^d→C^(d+d), channels, projection effects,
ALL-INPUT intertwining, range support, conditional repeatability and real data),
the Hankel d≥6 bound and reachable-state ideality with all affine effects,
and the supported-output native simulation statement needed for
the sharp 138/136 corollaries. A same-table 2d proxy would not establish the
dilation theorem. Core bounds are 2d, NOT the companion's d+max rank(A−A²). -/

end AlbertSequential
