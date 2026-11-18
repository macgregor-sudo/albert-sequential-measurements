module

public import Interfaces.InstrumentsAndCompactness
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
Source: core prop:robust and prop:cer:nearideal, companion prop:windowlaw.
Only the finite-table margin layer is stated here. The spectral and arbitrary
R/C/H trace-class layers and the native invariant-measure identification are
not stated here (see the closing comment); finite complex matrices are not substitutes for them.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace AlbertSequential

def finiteWitnessValue {ι : Type*} (s : Finset ι) (c f : ι → ℝ) : ℝ :=
  ∑ w ∈ s, c w * f w

def finiteWitnessCoefficientNorm {ι : Type*} (s : Finset ι) (c : ι → ℝ) : ℝ :=
  ∑ w ∈ s, |c w|

/-- Finite-support coefficient estimates. This generic layer has no hypothesis
of traciality, finite Hilbert dimension or a particular comparator field.
Applying it to the paper requires the comparator's witness soundness. -/
structure FiniteWitnessMarginObligations (ι : Type*) : Prop where
  coefficient_norm_positive : ∀ (s : Finset ι) (c f : ι → ℝ) (γ : ℝ),
    0 < γ → finiteWitnessValue s c f ≤ -γ → 0 < finiteWitnessCoefficientNorm s c
  separation : ∀ (s : Finset ι) (c f g : ι → ℝ) (γ : ℝ),
    0 < γ → finiteWitnessValue s c f ≤ -γ → 0 ≤ finiteWitnessValue s c g →
    ∃ w ∈ s, γ / finiteWitnessCoefficientNorm s c ≤ |g w - f w|
  perturbed_separation : ∀ (s : Finset ι) (c f f' g : ι → ℝ) (γ δ : ℝ),
    0 < γ → 0 ≤ δ → finiteWitnessValue s c f ≤ -γ →
    0 ≤ finiteWitnessValue s c g → (∀ w ∈ s, |f' w - f w| ≤ δ) →
    ∃ w ∈ s, γ / finiteWitnessCoefficientNorm s c - δ ≤ |g w - f' w|

def spectralRoundingError (ε : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * ε)) / 2

def faceCalibrationBound (δ ε : ℝ) : ℝ :=
  let τ := spectralRoundingError ε
  min 2 ((δ + τ + Real.sqrt ((δ - τ) ^ 2 + 4 * τ)) / 2)

/-- Arithmetic transfer of assumed word-error estimates to a witness bound.
Here g is any table satisfying the displayed witness inequality. This does not
assert a projective realization of g, operator rounding, telescoping, all-state
calibration or arbitrary-dimensional operator estimates. Those belong to separate
parts of prop:robust and prop:cer:nearideal and are not assumed here. -/
structure RobustWitnessTransferObligations (X : Type*) : Prop where
  rounded_square_root : ∀ (s : Finset (Word X)) (c f g h : Word X → ℝ)
    (L : ℕ) (γ δ ε : ℝ),
    0 < γ → 0 ≤ δ → 0 ≤ ε → ε < 1 / 4 →
    (∀ w ∈ s, w.length ≤ L) → finiteWitnessValue s c f ≤ -γ →
    0 ≤ finiteWitnessValue s c g →
    (∀ w ∈ s, |h w - f w| ≤ δ) →
    (∀ w ∈ s, |h w - g w| ≤ 2 * (w.length : ℝ) * Real.sqrt (spectralRoundingError ε)) →
    γ / finiteWitnessCoefficientNorm s c ≤ δ + 2 * L * Real.sqrt (spectralRoundingError ε)
  calibrated_positive_branches : ∀ (s : Finset (Word X)) (c f g h : Word X → ℝ)
    (L : ℕ) (γ η δ ε : ℝ),
    0 < γ → 0 ≤ η → 0 ≤ δ → 0 ≤ ε → ε < 1 / 4 →
    (∀ w ∈ s, w.length ≤ L) → finiteWitnessValue s c f ≤ -γ →
    0 ≤ finiteWitnessValue s c g →
    (∀ w ∈ s, |h w - f w| ≤ η) →
    (∀ w ∈ s, |h w - g w| ≤ (w.length : ℝ) * faceCalibrationBound δ ε) →
    γ / finiteWitnessCoefficientNorm s c ≤ η + L * faceCalibrationBound δ ε

/-- The deterministic normalization in nu_(3,k). At Z=0 this definition uses
the field's inverse-zero convention; that the Gaussian zero event is null is
not proved here, so no density claim is made at the zero matrix. -/
def normalizedComplexGram (k : ℕ) (Z : Matrix (Fin 3) (Fin k) ℂ) : ComplexMatrix 3 :=
  (Matrix.trace (Z * Z.conjTranspose))⁻¹ • (Z * Z.conjTranspose)

/-- Pushforward of a SPECIFIED ensemble. This definition does not assert that
the supplied measure is standard complex Gaussian or an invariant atom law. -/
def normalizedGramPushforward (k : ℕ)
    (ensemble : MeasureTheory.Measure (Matrix (Fin 3) (Fin k) ℂ)) :
    MeasureTheory.Measure (ComplexMatrix 3) :=
  MeasureTheory.Measure.map (normalizedComplexGram k) ensemble

/- The window law (not stated in this file):
The exact companion prop:windowlaw quantifies over a native unital complex window
W inside V≅H3(K), K=C/H/O, with invariant atom probability, trace-orthogonal
projection and unital Jordan identification. It asserts the STANDARD COMPLEX
Gaussian induced law k=1/2 dim_R K=1,2,4, rank min(3,k) almost surely and the
eigenvalue density. A statement needs: native measurable atom/frame/automorphism types;
canonical Borel structures; invariant measure; projection/isomorphism; the
Gaussian ensemble with real/imag variance 1/2; Riesz rank support and exact
Laplace normalization/uniqueness; rank/density conclusions. Supplying arbitrary
measures or a real Wishart law would not give this statement. No
abstract `WindowLaw` predicate or assumed theorem is introduced here.

The spectral and trace-class layer (not stated in this file):
prop:robust(b) needs square-root instruments, spectral projections of effects
with ||E²−E||≤ε<1/4, norm telescoping and every state in arbitrary dimension.
prop:cer:nearideal needs bounded positive REAL-LINEAR maps on self-adjoint
trace-class operators over R/C/H, outcome-sum TP, operator-norm rounding and
trace-norm calibration on EVERY density operator of BOTH rounded faces. Its
conclusion is unnormalized branch error ≤beta and all-word error m*beta.
Neither complete positivity nor finite dimension is a paper hypothesis.
No postselection/ancillary-norm bound follows. The scalar transfer contracts
above assume, and do not supply, those substantive operator conclusions.
-/

end AlbertSequential
