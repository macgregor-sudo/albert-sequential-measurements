module

public import Interfaces.Geometry
public import NativeTopology
public import Mathlib.Analysis.Convex.Basic

/-!
Definitions and statement types; this file proves nothing. The moment coordinates below
are actual words in free symmetric idempotents, with ALL left/right contexts.
The compact domain is not a fixed-dimensional CP parameter space.
General-EJA classification and the literal stronger reading of cor:bri:finite(b)
are not stated here. No statement of `Challenge` is used.
-/
@[expose] public section
noncomputable section
open scoped ComplexOrder
namespace AlbertSequential

abbrev ProjectionMonomial (n : ℕ) := List (Fin n)
abbrev ProjectionPolynomial (n : ℕ) := List (ℝ × ProjectionMonomial n)
abbrev ProjectionMoments (n : ℕ) := ProjectionMonomial n → ℝ

/-- Positivity is tested on every real polynomial square, not just monomials.
Idempotence can be inserted in every context, before and after the repeated
letter. Boundedness is included for compactness; that it follows from the other
conditions and loses no comparator models is a separate statement. -/
structure AdmissibleProjectionMoments (n : ℕ) (m : ProjectionMoments n) : Prop where
  normalized : m [] = 1
  reversal : ∀ w, m w.reverse = m w
  idempotent_context : ∀ u v i,
    m (u ++ [i, i] ++ v) = m (u ++ [i] ++ v)
  positive_polynomial_squares : ∀ c : ProjectionPolynomial n,
    0 ≤ (c.map (fun a =>
      (c.map (fun b => a.1 * b.1 * m (a.2.reverse ++ b.2))).sum)).sum
  bounded : ∀ w, -1 ≤ m w ∧ m w ≤ 1

def projectionMomentDomain (n : ℕ) : Set (ProjectionMoments n) :=
  {m | AdmissibleProjectionMoments n m}

def polynomialMultiply {n : ℕ} (a b : ProjectionPolynomial n) : ProjectionPolynomial n :=
  a.flatMap (fun x => b.map (fun y => (x.1 * y.1, x.2 ++ y.2)))
def polynomialStar {n : ℕ} (a : ProjectionPolynomial n) : ProjectionPolynomial n :=
  a.map (fun x => (x.1, x.2.reverse))
def polynomialMoment {n : ℕ} (m : ProjectionMoments n) (a : ProjectionPolynomial n) : ℝ :=
  (a.map (fun x => x.1 * m x.2)).sum

def outcomePolynomial {n : ℕ} (a : Outcome (Fin n)) : ProjectionPolynomial n :=
  if a.2 then [(1, [a.1])] else [(1, []), (-1, [a.1])]

def amplitudePolynomial {n : ℕ} (w : Word (Fin n)) : ProjectionPolynomial n :=
  w.foldl (fun acc a => polynomialMultiply (outcomePolynomial a) acc) [(1, [])]

def effectPolynomial {n : ℕ} (w : Word (Fin n)) : ProjectionPolynomial n :=
  polynomialMultiply (polynomialStar (amplitudePolynomial w)) (amplitudePolynomial w)

def momentWordProbability {n : ℕ} (m : ProjectionMoments n) (w : Word (Fin n)) : ℝ :=
  polynomialMoment m (effectPolynomial w)

/-- Literal finite monomial evaluation in the alternative associative model.
No quotient algebra or bounded representation is assumed to exist. -/
def evaluateMonomial {n : ℕ} {A : Type*} [Ring A] (P : Fin n → A)
    (w : ProjectionMonomial n) : A := w.foldr (fun i acc => P i * acc) 1

def momentsOfProjectiveData {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A) : ProjectionMoments n :=
  fun w => M.state (evaluateMonomial M.projection w)

/-- Soundness/binding statements for the moment coordinates (proved as `algebraicMomentBinding`).
The arbitrary-Hilbert R/C/H -> algebraic passage is the separate `toAlgebraic`
bridge; no finite-dimensional restriction is introduced here. -/
structure AlgebraicMomentBinding {n : ℕ} {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A]
    (M : AlgebraicProjectiveData (Fin n) A) : Prop where
  admissible : AdmissibleProjectionMoments n (momentsOfProjectiveData M)
  probabilities : ∀ w, momentWordProbability (momentsOfProjectiveData M) w = M.probability w

/-- Topological claims about the concrete domain, not assumptions hidden in
its definition. Product topology is inherited from the function type. -/
structure MomentDomainTopology (n : ℕ) : Prop where
  compact : IsCompact (projectionMomentDomain n)
  convex : Convex ℝ (projectionMomentDomain n)
  word_continuous : ∀ w : Word (Fin n),
    Continuous (fun m : ProjectionMoments n => momentWordProbability m w)

structure FiniteRealWordFunctional (n : ℕ) where
  terms : List (ℝ × Word (Fin n))

def FiniteRealWordFunctional.evaluate {n : ℕ} (c : FiniteRealWordFunctional n)
    (f : Word (Fin n) → ℝ) : ℝ := (c.terms.map (fun t => t.1 * f t.2)).sum

def FiniteRealWordFunctional.HasHorizon {n : ℕ} (c : FiniteRealWordFunctional n)
    (L : ℕ) : Prop := ∀ t ∈ c.terms, t.2.length ≤ L

/-- The quantifier order is ∃L,c,gamma>0, then ALL moment models and ALL
allowed target states. This is a common linear margin, not pointwise no-go,
fixed-D compactness, a nonlinear witness or a state-dependent coefficient list. -/
def UniformMomentSeparator {n : ℕ} (p : Fin n → Albert) (states : Set Albert) : Prop :=
  ∃ L : ℕ, ∃ c : FiniteRealWordFunctional n, ∃ γ : ℝ,
    0 < γ ∧ c.HasHorizon L ∧
    (∀ m, AdmissibleProjectionMoments n m →
      0 ≤ c.evaluate (momentWordProbability m)) ∧
    (∀ ρ ∈ states, c.evaluate (nativeWordProbability p ρ) ≤ -γ)

def nativeDensitySet : Set Albert := {ρ | IsDensity ρ}

def NoMomentMatch {n : ℕ} (p : Fin n → Albert) (states : Set Albert) : Prop :=
  ∀ m, AdmissibleProjectionMoments n m → ∀ ρ ∈ states,
    ∃ w, momentWordProbability m w ≠ nativeWordProbability p ρ w

/-- Reusable separation bridge with hypotheses on the actual state set.
Trace-one normalization lets the empty word encode the affine separator
constant on BOTH model and target tables; without it this claim is false.
It does not assume the desired finite separator as a parameter. Empty state
sets are not excluded: their trivial separator case is part of the statement. -/
structure CompactMomentSeparationContract (n : ℕ) : Prop where
  separates : ∀ (p : Fin n → Albert) (states : Set Albert),
    IsCompact states → Convex ℝ states →
    (∀ ρ ∈ states, albertTrace ρ = 1) → NoMomentMatch p states →
    UniformMomentSeparator p states

/-- cor:bri:finite(a) at the algebraic-moment comparison boundary (proved as
`albertUniformSeparation`). NoMomentMatch is a separate statement, not part of
this one. Moment representation/Hilbert bridges are needed for exact class-I equivalence. -/
structure AlbertUniformSeparationContract (n : ℕ) : Prop where
  all_states : ∀ p : Fin n → Albert, (∀ i, IsAtom (p i)) → GeneratesAlbert p →
    UniformMomentSeparator p nativeDensitySet

/- The general-EJA relative epsilon threshold is not stated here: native Albert alone
cannot encode several exceptional summands. Its condition would be total
exceptional mass >= epsilon, not max mass. The no-common-functional clause
is not stated under the stronger literal reading; the paper's proof only
excludes one common positive gamma as mass tends to zero. -/

/-- Complex finite matrices of arbitrary d, with the ordinary unnormalized
matrix trace. This is separate from trace-preserving ComplexWindow. -/
abbrev HermitianEmbeddingMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def IsEmbeddingDensity (d : ℕ) (σ : HermitianEmbeddingMatrix d) : Prop :=
  σ.PosSemidef ∧ Matrix.trace σ = 1

/-- A SUPPLIED injective unital Jordan embedding of an actual native unital
subalgebra. No classification, trace-preservation or existence is assumed. -/
structure SuppliedHermitianEmbedding (B : NativeJordanSubalgebra) (d : ℕ) where
  map : B.carrier →ₗ[ℝ] HermitianEmbeddingMatrix d
  injective : Function.Injective map
  hermitian : ∀ x, (map x).IsHermitian
  unit : map ⟨albertUnit, B.unit_mem⟩ = 1
  jordan : ∀ x y : B.carrier,
    map ⟨jordanMul x y, B.product_mem x x.property y y.property⟩ =
      (1 / 2 : ℝ) • (map x * map y + map y * map x)

/-- lem:bri:state specialized to native Albert ambient V. The arbitrary-EJA
ambient version of the paper is not
covered. The density is the image of the unique pairing representative z.
No normalized-trace convention is silently substituted. -/
structure SuppliedEmbeddingStateTransport : Prop where
  unique_pairing : ∀ (B : NativeJordanSubalgebra) (d : ℕ)
    (ι : SuppliedHermitianEmbedding B d) (ρ : Albert), IsDensity ρ →
    ∃! z : B.carrier, ∀ x : B.carrier,
      (Matrix.trace (ι.map z * ι.map x)).re = tracePairing ρ x
  density_and_words : ∀ (B : NativeJordanSubalgebra) (d : ℕ)
    (ι : SuppliedHermitianEmbedding B d) (ρ : Albert), IsDensity ρ →
    ∀ z : B.carrier,
    (∀ x : B.carrier, (Matrix.trace (ι.map z * ι.map x)).re = tracePairing ρ x) →
    IsEmbeddingDensity d (ι.map z) ∧
    ∀ (n : ℕ) (p : Fin n → B.carrier),
      (∀ i, jordanMul (p i) (p i) = (p i : Albert)) →
      ∀ w : Word (Fin n),
        (Matrix.trace (ι.map z * wordOperator (fun i => ι.map (p i)) w)).re =
          nativeWordProbability (fun i => (p i : Albert)) ρ w

/-- A typed consumer of the exact quantifier boundary, not a construction. -/
example {n : ℕ} (h : AlbertUniformSeparationContract n) (p : Fin n → Albert)
    (ha : ∀ i, IsAtom (p i)) (hg : GeneratesAlbert p) :
    UniformMomentSeparator p nativeDensitySet := h.all_states p ha hg

end AlbertSequential
