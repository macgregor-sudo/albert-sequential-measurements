/- Apache-2.0. Proofs of the statements of `Challenge`, which accompanies the paper "On sequential
ideal measurements in the exceptional Jordan algebra". Generated mechanically: the theorem
statements and docstrings are copied verbatim from Challenge.lean; only the proofs differ. -/
module

public import ChallengeDefs
public import Bridge.AlbertHeadlines
public import Bridge.Exclusion
public import Bridge.C12
public import Bridge.Seven
public import Bridge.Least
public import Bridge.Matrix
public import Bridge.Criterion
public import Bridge.Atoms

/-!
# Solution: proofs of the statements of `Challenge`

The definitions are those of `ChallengeDefs` (the Challenge's definition prefix, verbatim). Every
proof below is a one-line appeal to the bridge layer (`Bridge/*.lean`), which proves the statements
from the development's compiled theorems.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge

universe u v

/-! ## Theorems -/

/-- **No representation for generating atoms** (thm:bridgeJ, no-go half; cor:fp:noideal).
If atoms generate `J`, no representation reproduces all their word probabilities from any
`ρ`. -/
theorem no_representation_of_generates {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) (ρ : Albert) : NoRepresentationOn.{v} p ρ Set.univ := by
  exact Bridge.no_representation_bridge p hp hg ρ

/-- **A finite separating inequality** (thm:bridgeJ, last sentence). For generating atoms there
are a length `L` and a linear inequality on words of length at most `L` that holds in every
real, complex and quaternionic representation and fails by at least `γ > 0` from every state. -/
theorem linear_separator_of_generates {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) :
    ∃ (L : ℕ) (W : Finset (Word n)) (c : Word n → ℝ) (γ : ℝ), 0 < γ ∧ (∀ w ∈ W, w.length ≤ L) ∧
      (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (M : ProjectiveRepresentation n ℝ H), 0 ≤ ∑ w ∈ W, c w * M.probability w) ∧
      (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : ProjectiveRepresentation n ℂ H), 0 ≤ ∑ w ∈ W, c w * M.probability w) ∧
      (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation n S),
        0 ≤ ∑ w ∈ W, c w * M.probability w) ∧
      (∀ ρ, IsDensity ρ → ∑ w ∈ W, c w * wordProbability p ρ w ≤ -γ) := by
  exact Bridge.linear_separator_bridge p hp hg

/-- **Seven steps suffice for every generating quadruple** (thm:cer:uniform (a)). From `e/3` no
representation reproduces every word of length at most seven beginning with "yes" on test `0`;
from `p_0` none reproduces every word of length at most six. -/
theorem seven_steps_exclude (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hg : Generates p) :
    NoRepresentationOn.{v} p maximallyMixed (yesFirstUpTo 7) ∧
      NoRepresentationOn.{v} p (p 0) (wordsUpTo 4 6) := by
  exact Bridge.seven_steps_bridge p hp hg

/-- **Six steps never suffice** (prop:cer:universalsix): for every generating quadruple a
representation on `ℂ¹²` reproduces every word of length at most six from `e/3`. -/
theorem six_step_model (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hg : Generates p) :
    ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w ∈ wordsUpTo 4 6, M.probability w = wordProbability p maximallyMixed w := by
  exact Bridge.six_step_model_bridge p hp hg

/-- **`L_min = 7`**: for a generating quadruple, seven is the least `L` such that no real,
complex or quaternionic representation (on a Hilbert space in `Type`) reproduces from `e/3` every
word of length at most `L`. -/
theorem least_separating_length (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) :
    IsLeast {L : ℕ | (∀ (𝕜 : Type) (H : Type) [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : ProjectiveRepresentation 4 𝕜 H),
        ¬ ∀ w ∈ wordsUpTo 4 L, M.probability w = wordProbability p maximallyMixed w) ∧
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation 4 S),
        ¬ ∀ w ∈ wordsUpTo 4 L, M.probability w = wordProbability p maximallyMixed w)} 7 := by
  exact Bridge.least_separating_bridge p hp hg

/-- **The four-point criterion**, parts (i) and (iii) (thm:fourpoint): `𝒜 ≥ 0`, and `𝒜 > 0`
exactly when the four atoms generate `J`. -/
theorem fourPoint_criterion (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    0 ≤ fourPointInvariant p ∧ (0 < fourPointInvariant p ↔ Generates p) := by
  exact Bridge.fourPoint_criterion_bridge p hp

/-- **The maximum** (prop:max, value part): `𝒜 ≤ 4/19683` for all atoms, attained at `M`. -/
theorem quadrupleM_spec :
    (∀ i, IsAtom (quadrupleM i)) ∧ fourPointInvariant quadrupleM = 4 / 19683 ∧
      ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) → fourPointInvariant p ≤ 4 / 19683 := by
  exact Bridge.quadrupleM_spec_bridge

/-- **The rational quadruple `S`**: four atoms with `𝒜 = 1/5832`. -/
theorem quadrupleS_spec :
    (∀ i, IsAtom (quadrupleS i)) ∧ fourPointInvariant quadrupleS = 1 / 5832 := by
  exact Bridge.quadrupleS_spec_bridge

/-- **Three atoms** (prop:three). Three atoms never generate `J`, and from every state some
representation on `ℂ³` reproduces every word of their tests. (The statement does not record the rank
of the projections.) -/
theorem three_atoms (p : Fin 3 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ¬ Generates p ∧ ∀ ρ, IsDensity ρ →
      ∃ M : ProjectiveRepresentation 3 ℂ (EuclideanSpace ℂ (Fin 3)),
        ∀ w : Word 3, M.probability w = wordProbability p ρ w := by
  exact Bridge.three_atoms_bridge p hp

/-- **Vanishing invariant** (the paragraph after cor:fp:noideal). If four atoms have `𝒜 = 0`, then
from every state some representation on `ℂ⁶` reproduces every word of their tests. -/
theorem zero_invariant_model (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (h0 : fourPointInvariant p = 0) :
    ∀ ρ, IsDensity ρ → ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (Fin 6)),
      ∀ w : Word 4, M.probability w = wordProbability p ρ w := by
  exact Bridge.zero_invariant_bridge p hp h0

/-- **The Albert criterion** (thm:bridgeJ, (1) ⇔ (2) ⇔ (3), for every finite family of atoms).
For atoms `p₁, …, p_n` of `J` each of the following is equivalent to `p₁, …, p_n` not generating
`J`: some unital Jordan subalgebra containing them is special; one family of orthogonal
projections on `ℂ^d`, with `d = 6` or `d = 24`, serves every state, that is, from every state a
representation with these projections and a density-operator state reproduces every word; from
at least one state some real, complex or quaternionic representation, or algebraic model, on a
space in `Type` reproduces every word. -/
theorem albert_criterion {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    (¬ Generates p ↔ ∃ B : JordanSubalgebra, (∀ i, p i ∈ B.carrier) ∧ B.IsSpecial) ∧
    (¬ Generates p ↔ ∃ d : ℕ, (d = 6 ∨ d = 24) ∧
      ∃ M₀ : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)), ∀ ρ, IsDensity ρ →
        ∃ M : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)),
          M.projection = M₀.projection ∧ M.HasDensityState ∧
          ∀ w : Word n, M.probability w = wordProbability p ρ w) ∧
    (¬ Generates p ↔ ∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn.{0} p ρ Set.univ) := by
  exact Bridge.albert_criterion_bridge p hp

/-- **Atoms are the primitive idempotents.** An element of `J` is an atom (an idempotent of trace
one) if and only if it is a primitive idempotent: a nonzero idempotent that is not the sum of two
nonzero orthogonal idempotents (`q ∘ r = 0`). -/
theorem isAtom_iff_primitive (p : Albert) :
    IsAtom p ↔ jordanMul p p = p ∧ p ≠ 0 ∧
      ¬ ∃ q r : Albert, jordanMul q q = q ∧ jordanMul r r = r ∧ q ≠ 0 ∧ r ≠ 0 ∧
        jordanMul q r = 0 ∧ p = q + r := by
  exact Bridge.isAtom_iff_primitive_bridge p

end AlbertChallenge
