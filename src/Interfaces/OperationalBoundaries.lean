module

public import Interfaces.InstrumentsAndCompactness
public import Interfaces.Geometry
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Convex.Hull
public import NativeTopology

/-!
Exact operational boundary statements for the core paper. These structures are
statements, not proofs or axioms; other modules prove them. A supplied witness is explicitly
distinguished from the obligation to construct one for every admissible input.
Source: core `sec:ins` (prop:ins:sharpdilation, prop:ins:lower) and companion prop:ins:reachable.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexOrder
namespace AlbertSequential

/-- The actual first-block inclusion C^d → C^(d+d); d+d is exactly 2d. -/
def firstBlockInclusion (d : ℕ) : Matrix (Fin (d + d)) (Fin d) ℂ :=
  fun i j => if i.val = j.val then 1 else 0

def embedFirstBlock {d : ℕ} (X : ComplexMatrix d) : ComplexMatrix (d + d) :=
  firstBlockInclusion d * X * (firstBlockInclusion d).conjTranspose

def compressFirstBlock {d : ℕ} (Z : ComplexMatrix (d + d)) : ComplexMatrix d :=
  (firstBlockInclusion d).conjTranspose * Z * firstBlockInclusion d

structure SharpDilationData (d : ℕ) (X : Type*) where
  projection : X → ComplexMatrix (d + d)
  channelKraus : X → Bool → List (ComplexMatrix (d + d))

def SharpDilationData.outcomeProjection {d : ℕ} {X : Type*}
    (s : SharpDilationData d X) (x : X) (a : Bool) : ComplexMatrix (d + d) :=
  if a then s.projection x else 1 - s.projection x

def SharpDilationData.branch {d : ℕ} {X : Type*}
    (s : SharpDilationData d X) (x : X) (a : Bool)
    (Z : ComplexMatrix (d + d)) : ComplexMatrix (d + d) :=
  krausAction (s.channelKraus x a)
    (s.outcomeProjection x a * Z * s.outcomeProjection x a)

def SharpDilationData.wordProbability {d : ℕ} {X : Type*}
    (s : SharpDilationData d X) (ρ : ComplexMatrix d) (w : Word X) : ℝ :=
  (Matrix.trace (w.foldl (fun Z a => s.branch a.1 a.2 Z) (embedFirstBlock ρ))).re

/-- Every output must lie in the first block, even for nonpositive inputs.
Effects are specified by trace pairing on ALL input matrices. -/
def IsSharpDilation {d : ℕ} {X : Type*} (r : BinaryKrausRealization d X)
    (s : SharpDilationData d X) : Prop :=
  (∀ x, (s.projection x).conjTranspose = s.projection x ∧
    s.projection x * s.projection x = s.projection x) ∧
  (∀ x a, krausEffect (s.channelKraus x a) = 1) ∧
  IsMatrixDensity (embedFirstBlock r.initial) ∧
  (∀ x Z, Matrix.trace (s.branch x true Z + s.branch x false Z) = Matrix.trace Z) ∧
  (∀ x, compressFirstBlock (s.projection x) = krausEffect (r.kraus x true)) ∧
  (∀ x a Z, Matrix.trace (s.branch x a Z) =
    Matrix.trace (s.outcomeProjection x a * Z)) ∧
  (∀ x a Y, s.branch x a (embedFirstBlock Y) = embedFirstBlock (krausAction (r.kraus x a) Y)) ∧
  (∀ x a Z, ∃ Y : ComplexMatrix d, s.branch x a Z = embedFirstBlock Y) ∧
  (∀ w, s.wordProbability r.initial w = binaryKrausProbability r w)

/-- Support in the 1-eigenspace of the yes effect and the kernel for no.
For positive outputs these left-action equations are exactly the source support
conditions; no spectral-gap or nonzero-branch assumption is imposed. -/
def HasCertaintySupportedOutputs {d : ℕ} {X : Type*}
    (r : BinaryKrausRealization d X) : Prop :=
  ∀ x Y, Y.PosSemidef →
    krausEffect (r.kraus x true) * krausAction (r.kraus x true) Y =
      krausAction (r.kraus x true) Y ∧
    krausEffect (r.kraus x true) * krausAction (r.kraus x false) Y = 0

def IsRepeatableSharpDilation {d : ℕ} {X : Type*} (s : SharpDilationData d X) : Prop :=
  ∀ x a Z, Z.PosSemidef → s.branch x a Z =
    s.outcomeProjection x a * s.branch x a Z * s.outcomeProjection x a

def IsRealSharpDilation {d : ℕ} {X : Type*} (s : SharpDilationData d X) : Prop :=
  (∀ x, HasRealEntries (s.projection x)) ∧
  ∀ x a K, K ∈ s.channelKraus x a → HasRealEntries K

/-- Existence is not stored in the input data. It is the main obligation.
Repeatability and reality are required of the SAME chosen dilation. No A≠0,1
hypothesis removes the zero/unit cases. Finite-Kraus completeness for arbitrary
finite complex CP instruments is separately ChoiKrausObligations. -/
structure SharpDilationObligations (d : ℕ) (X : Type*) : Prop where
  inclusion_isometry : (firstBlockInclusion d).conjTranspose * firstBlockInclusion d = 1
  existence : ∀ r : BinaryKrausRealization d X, ∃ s : SharpDilationData d X,
    IsSharpDilation r s ∧
    (HasCertaintySupportedOutputs r → IsRepeatableSharpDilation s) ∧
    (IsRealKrausRealization r → IsRealSharpDilation s)

/-- The construction-level strengthening needed to derive the real, all-state
repeatable sharp simulations in dimensions 2(17n+1) and 34n. This asks for a
particular supported simulator; it does not assert that EVERY realization of
the same table has certainty-supported outputs. -/
structure NativeSupportedSimulationObligations : Prop where
  general : ∀ (n : ℕ) (p : Fin n → Albert), (∀ i, IsAtom (p i)) →
    ∀ ρ, IsDensity ρ → ∃ r : BinaryKrausRealization (17 * n + 1) (Fin n),
      IsRealKrausRealization r ∧ HasCertaintySupportedOutputs r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w
  no_half_component : ∀ (n : ℕ) (p : Fin n → Albert), (∀ i, IsAtom (p i)) →
    ∀ ρ, IsDensity ρ →
    (∃ (i : Fin n) (t : ℝ) (y : Albert), 0 ≤ t ∧ IsPositive y ∧
      jordanMul (p i) y = 0 ∧ ρ = t • p i + y) →
    ∃ r : BinaryKrausRealization (17 * n) (Fin n),
      IsRealKrausRealization r ∧ HasCertaintySupportedOutputs r ∧
      ∀ w, binaryKrausProbability r w = nativeWordProbability p ρ w

/-- Finite restrictions of the controlled Hankel array, in real scalars.
u++v means u is performed before v; no iid/random-setting weighting appears. -/
def finiteHankelMatrix {X : Type*} (f : Word X → ℝ)
    {m n : ℕ} (u : Fin m → Word X) (v : Fin n → Word X) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => f (u i ++ v j)

structure HankelDimensionObligations : Prop where
  finite_CP_bound : ∀ (d : ℕ) (X : Type*)
    (r : RawFiniteCPModel d Unit X (fun _ => Bool)), IsNormalizedFiniteCPModel r →
    ∀ (m n : ℕ) (u : Fin m → Word X) (v : Fin n → Word X),
      (finiteHankelMatrix
        (fun w => finiteCPWordProbability r () (generalizeBinaryWord w)) u v).rank ≤ d ^ 2
  native_rank_witness : ∀ (n : ℕ) (p : Fin n → Albert),
    (∀ i, IsAtom (p i)) → GeneratesAlbert p →
    ∃ (u v : Fin 27 → Word (Fin n)),
      (finiteHankelMatrix (nativeWordProbability p ((1 / 3 : ℝ) • albertUnit)) u v).rank = 27
  native_lower_bound : ∀ (n d : ℕ) (p : Fin n → Albert),
    (∀ i, IsAtom (p i)) → GeneratesAlbert p →
    ∀ r : RawFiniteCPModel d Unit (Fin n) (fun _ => Bool), IsNormalizedFiniteCPModel r →
    (∀ w, finiteCPWordProbability r () (generalizeBinaryWord w) =
      nativeWordProbability p ((1 / 3 : ℝ) • albertUnit) w) → 6 ≤ d

def nativeReachableStates {X : Type*} (p : X → Albert) : Set Albert :=
  {y | ∃ w : Word X,
    0 < albertTrace (nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w) ∧
    y = (albertTrace (nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w))⁻¹ •
      nativeBranchState p ((1 / 3 : ℝ) • albertUnit) w}

def nativeReachableStateSpace {X : Type*} (p : X → Albert) : Set Albert :=
  closure (convexHull ℝ (nativeReachableStates p))

def stateSpaceCone (C : Set Albert) : Set Albert :=
  {z | ∃ (t : ℝ) (y : Albert), 0 ≤ t ∧ y ∈ C ∧ z = t • y}

/-- Every affine [0,1]-valued effect on C. The function is defined arbitrarily
outside C; no global affine extension or continuity is assumed. The displayed
convex-combination equation defines affinity on C directly. -/
def IsAffineOperationalEffect (C : Set Albert) (f : Albert → ℝ) : Prop :=
  (∀ x ∈ C, 0 ≤ f x ∧ f x ≤ 1) ∧
  ∀ x ∈ C, ∀ y ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t • x + (1 - t) • y) = t * f x + (1 - t) * f y

/-- Source permits idempotents of EVERY rank, including 0 and e. Sh is stated
literally as no third state/effect separating both certainty faces. -/
structure ReachableIdealityObligations (X : Type*) : Prop where
  states_are_density : ∀ p : X → Albert, (∀ i, jordanMul (p i) (p i) = p i) →
    ∀ ρ ∈ nativeReachableStateSpace p, IsDensity ρ
  branch_linear : ∀ p : X → Albert, ∀ a : Outcome X,
    ∃ L : Albert →ₗ[ℝ] Albert, ∀ z, L z = quadraticMap (nativeOutcome p a) z
  branch_positive : ∀ p : X → Albert, (∀ i, jordanMul (p i) (p i) = p i) →
    ∀ a : Outcome X, ∀ z ∈ stateSpaceCone (nativeReachableStateSpace p),
      quadraticMap (nativeOutcome p a) z ∈ stateSpaceCone (nativeReachableStateSpace p)
  normalized : ∀ p : X → Albert, (∀ i, jordanMul (p i) (p i) = p i) →
    ∀ i z, albertTrace (quadraticMap (p i) z + quadraticMap (albertUnit - p i) z) =
      albertTrace z
  ideality : ∀ p : X → Albert, (∀ i, jordanMul (p i) (p i) = p i) →
    ∀ a : Outcome X, ∀ ρ ∈ nativeReachableStateSpace p,
      tracePairing ρ (nativeOutcome p a) = 1 → quadraticMap (nativeOutcome p a) ρ = ρ
  sharpness : ∀ p : X → Albert, (∀ i, jordanMul (p i) (p i) = p i) →
    ∀ i, ¬ ∃ (σ : Albert) (f : Albert → ℝ),
      σ ∈ nativeReachableStateSpace p ∧ IsAffineOperationalEffect (nativeReachableStateSpace p) f ∧
      f σ = 1 ∧ ∀ ρ ∈ nativeReachableStateSpace p,
        (tracePairing ρ (p i) = 0 ∨ tracePairing ρ (p i) = 1) → f ρ = 0

/- Native sharp 138/136 corollaries require composing the strengthened
NativeSupportedSimulationObligations with SharpDilationObligations. The
table-only NativeFiniteSimulationObligations cannot provide the supported-output
proof. NativeSupportedSimulationObligations is the explicit
construction-level bridge (proved as `nativeSupportedSimulationObligations`). The dimension is (17n+1)+(17n+1) or 17n+17n.

Reachable positivity refers to the specified state cone only. There is no
affine encoding into the finite CP simulator, no premise of density in OP²,
and no assertion of ideality on its larger hidden quantum state space.
-/

end AlbertSequential
