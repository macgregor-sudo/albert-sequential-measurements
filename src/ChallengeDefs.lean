/- The definitions of Challenge.lean, verbatim (everything before its theorems; the module docstring
below describes the whole Challenge file). Generated mechanically from Challenge.lean. -/
/- Apache-2.0. Statements accompanying the paper "On sequential ideal measurements in the exceptional
Jordan algebra". -/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fin.VecNotation

/-!
# Ideal measurements on the Albert algebra: the statements

This file accompanies the paper "On sequential ideal measurements in the exceptional Jordan
algebra". Every theorem below is stated with a deliberate `sorry` hole; the module `Solution`
proves the same statements, with the same definitions, without importing this file. Only Mathlib is
imported, so every object used in the statements is defined here.

The Albert algebra `J = H₃(𝕆)` is the 27-dimensional real Jordan algebra of 3×3 Hermitian matrices
over the octonions, with product `x ∘ y = (xy + yx)/2`. A *test* is the ideal yes–no measurement of an
atom `p` of `J` (the papers allow any idempotent; every test here is of an atom). From a state
`ρ` the outcomes "yes" and "no" update `ρ` by the quadratic maps `U_p` and `U_{e-p}`; the probability
of a finite word of outcomes is the trace of the updated, unnormalised state. A *sequential
projective representation* replaces `J` by a real, complex or quaternionic Hilbert space of any
dimension, each test by an orthogonal projection of any rank, and `ρ` by a state `φ`; it gives the
word with projections `Q₁, …, Q_m` the value `φ(Q₁ ⋯ Q_m ⋯ Q₁)`. The exclusions are also stated for
algebraic models (a real `*`-algebra with self-adjoint idempotents and a positive normalised
functional).

The theorems: no representation for generating atoms; a finite separating inequality; words of
length seven exclude every representation from `e/3` for every generating quadruple (six from a
pure state); a model on `ℂ¹²` reproduces every word of length six, so seven is least; the
four-point invariant `𝒜` is nonnegative and positive exactly for generating quadruples; two
explicit quadruples `M` (the maximiser) and `S`; three atoms are reproduced on `ℂ³` and never
generate; four atoms with `𝒜 = 0` are reproduced on `ℂ⁶`; for every finite family of atoms, not
generating `J` is equivalent to lying in a special subalgebra, to one family of projections on
`ℂ⁶` or `ℂ²⁴` serving every state, and to a representation from one state; the atoms are exactly
the primitive idempotents.
-/

@[expose] public section
noncomputable section

namespace AlbertChallenge

universe u v

/-! ## Octonions and the Albert algebra -/

/-- The real octonions `𝕆`: the Cayley–Dickson double of Hamilton's quaternions `ℍ = ℍ[ℝ]`
(Mathlib's `Quaternion ℝ`). A pair `(a, b)` stands for `a + b ℓ`. Only the real vector space
structure is inherited from the product; the multiplication is `octMul`. -/
def Octonion : Type := Quaternion ℝ × Quaternion ℝ

/-- Octonions add coordinatewise, as pairs of quaternions. -/
instance : AddCommGroup Octonion := inferInstanceAs (AddCommGroup (Quaternion ℝ × Quaternion ℝ))
/-- Real scalars act coordinatewise on octonions: `𝕆` is the real vector space `ℍ × ℍ ≅ ℝ⁸`. -/
instance : Module ℝ Octonion := inferInstanceAs (Module ℝ (Quaternion ℝ × Quaternion ℝ))

/-- Octonion multiplication `(a, b)(c, d) = (ac − d̄b, da + bc̄)`: the Cayley–Dickson product with
parameter `−1`, which gives the compact (division) octonions. It is not associative. -/
def octMul (x y : Octonion) : Octonion :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)

/-- Octonion conjugation `(a, b) ↦ (ā, −b)`. -/
def octConj (x : Octonion) : Octonion := (star x.1, -x.2)

/-- The real scalar `r` as an octonion. -/
def octScalar (r : ℝ) : Octonion := (⟨r, 0, 0, 0⟩, 0)

/-- The real part of an octonion. -/
def octRe (x : Octonion) : ℝ := x.1.re

/-- The imaginary unit `i` of `ℍ ⊂ 𝕆`. -/
def octI : Octonion := (⟨0, 1, 0, 0⟩, 0)
/-- The imaginary unit `j` of `ℍ ⊂ 𝕆`. -/
def octJ : Octonion := (⟨0, 0, 1, 0⟩, 0)
/-- The Cayley–Dickson unit `ℓ = (0, 1)`, an imaginary unit of `𝕆` orthogonal to `ℍ`. -/
def octL : Octonion := (0, ⟨1, 0, 0, 0⟩)

/-- `‖x‖² = Re(x x̄)`, the octonion norm form. -/
def octNormSq (x : Octonion) : ℝ := octRe (octMul x (octConj x))

/-- An element of `J = H₃(𝕆)`, recorded by its three real diagonal entries and its upper entries
in positions `(0,1)`, `(0,2)`, `(1,2)`, in that order; the lower entries are their conjugates.
Only the real vector space structure is inherited; the product is `jordanMul`. -/
def Albert : Type := (Fin 3 → ℝ) × (Fin 3 → Octonion)

/-- Elements of `J` add entrywise. -/
instance : AddCommGroup Albert := inferInstanceAs (AddCommGroup ((Fin 3 → ℝ) × (Fin 3 → Octonion)))
/-- Real scalars act entrywise: `J` is a 27-dimensional real vector space. -/
instance : Module ℝ Albert := inferInstanceAs (Module ℝ ((Fin 3 → ℝ) × (Fin 3 → Octonion)))

/-- The Hermitian octonionic 3×3 matrix with the given coordinates. -/
def albertMatrix (x : Albert) : Fin 3 → Fin 3 → Octonion :=
  fun i j => match i.val, j.val with
    | 0, 0 => octScalar (x.1 0)
    | 1, 1 => octScalar (x.1 1)
    | 2, 2 => octScalar (x.1 2)
    | 0, 1 => x.2 0
    | 0, 2 => x.2 1
    | 1, 2 => x.2 2
    | 1, 0 => octConj (x.2 0)
    | 2, 0 => octConj (x.2 1)
    | 2, 1 => octConj (x.2 2)
    | _, _ => 0

/-- The (non-associative) product of two octonionic 3×3 matrices. -/
def octMatrixMul (x y : Fin 3 → Fin 3 → Octonion) : Fin 3 → Fin 3 → Octonion :=
  fun i j => ∑ k : Fin 3, octMul (x i k) (y k j)

/-- Read back the coordinates (real parts of the diagonal, upper entries) of a 3×3 matrix. -/
def albertCoordinates (m : Fin 3 → Fin 3 → Octonion) : Albert :=
  (fun i => octRe (m i i), ![m 0 1, m 0 2, m 1 2])

/-- The Jordan product `x ∘ y = (xy + yx)/2` of `J`. -/
def jordanMul (x y : Albert) : Albert :=
  (1 / 2 : ℝ) • albertCoordinates
    (octMatrixMul (albertMatrix x) (albertMatrix y) + octMatrixMul (albertMatrix y) (albertMatrix x))

/-- The unit `e` of `J`, the identity matrix. -/
def albertUnit : Albert := (fun _ => 1, fun _ => 0)

/-- The matrix trace; `tr e = 3`. -/
def albertTrace (x : Albert) : ℝ := ∑ i : Fin 3, x.1 i

/-- The trace form `⟨x, y⟩ = tr(x ∘ y)`. -/
def tracePairing (x y : Albert) : ℝ := albertTrace (jordanMul x y)

/-- The quadratic map `U_x y = 2 x ∘ (x ∘ y) − (x ∘ x) ∘ y`. -/
def quadraticMap (x y : Albert) : Albert :=
  2 • jordanMul x (jordanMul x y) - jordanMul (jordanMul x x) y

/-- An atom of `J`: an idempotent of trace one. In `H₃(𝕆)` these are the primitive (minimal
nonzero) idempotents, the rank-one idempotents `v v†` (the analogue of rank-one projections); the
identification with primitive idempotents is the theorem `isAtom_iff_primitive` below. -/
def IsAtom (p : Albert) : Prop := jordanMul p p = p ∧ albertTrace p = 1

/-- A state of `J`: a trace-one element of the positive cone, which in a Euclidean Jordan
algebra is the cone of squares. -/
def IsDensity (ρ : Albert) : Prop := (∃ y : Albert, ρ = jordanMul y y) ∧ albertTrace ρ = 1

/-- The maximally mixed state `e/3`. -/
def maximallyMixed : Albert := (1 / 3 : ℝ) • albertUnit

/-- A unital Jordan subalgebra of `J`: a real subspace containing `e` and closed under `∘`. -/
structure JordanSubalgebra where
  /-- The underlying real subspace. -/
  carrier : Submodule ℝ Albert
  /-- It contains the unit `e`. -/
  unit_mem : albertUnit ∈ carrier
  /-- It is closed under the Jordan product. -/
  mul_mem : ∀ x ∈ carrier, ∀ y ∈ carrier, jordanMul x y ∈ carrier

/-- `p₁, …, p_n` generate `J`: the only unital Jordan subalgebra containing them is `J`
(that is, `Jord⟨e, p₁, …, p_n⟩ = J`). -/
def Generates {n : ℕ} (p : Fin n → Albert) : Prop :=
  ∀ B : JordanSubalgebra, (∀ i, p i ∈ B.carrier) → B.carrier = ⊤

/-! ## Words and their probabilities on the Albert algebra -/

/-- A word of outcomes of tests `0, …, n−1`, in chronological order (head = first outcome);
`(i, true)` is "yes" and `(i, false)` is "no" on test `i`. -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

/-- The effect of an outcome: `p_i` for "yes", `e − p_i` for "no". -/
def outcomeEffect {n : ℕ} (p : Fin n → Albert) (a : Fin n × Bool) : Albert :=
  if a.2 then p a.1 else albertUnit - p a.1

/-- The probability of the word `w` from the state `ρ`: apply the Lüders updates `U_q` of the
outcomes in chronological order and take the trace, `tr(U_{q_m} ⋯ U_{q_1} ρ)`. -/
def wordProbability {n : ℕ} (p : Fin n → Albert) (ρ : Albert) (w : Word n) : ℝ :=
  albertTrace (w.foldl (fun σ a => quadraticMap (outcomeEffect p a) σ) ρ)

/-- Words of length at most `L`. -/
def wordsUpTo (n L : ℕ) : Set (Word n) := {w | w.length ≤ L}

/-- Words in four tests of length at most `L` whose first outcome is "yes" on test `0`. -/
def yesFirstUpTo (L : ℕ) : Set (Word 4) := {w | w.length ≤ L ∧ w.head? = some (0, true)}

/-! ## Sequential projective representations -/

/-- The operator of an outcome: `P_i` for "yes", `1 − P_i` for "no". -/
def outcomeOperator {A : Type*} [Ring A] {n : ℕ} (P : Fin n → A) (a : Fin n × Bool) : A :=
  if a.2 then P a.1 else 1 - P a.1

/-- The palindromic product `Q₁ ⋯ Q_{m−1} Q_m Q_{m−1} ⋯ Q₁` of the outcome operators of a word
`w = (a₁, …, a_m)` (and `1` for the empty word). -/
def wordOperator {A : Type*} [Ring A] {n : ℕ} (P : Fin n → A) (w : Word n) : A :=
  (w.map (outcomeOperator P)).prod * ((w.map (outcomeOperator P)).dropLast.reverse).prod

/-- A sequential projective representation of `n` tests on a real (`𝕜 = ℝ`) or complex
(`𝕜 = ℂ`) Hilbert space `H` of any dimension: an orthogonal projection of any rank for each test
and a state, i.e. a `𝕜`-linear functional on the bounded operators that is real and nonnegative
on positive operators and takes the value `1` at the identity. -/
structure ProjectiveRepresentation (n : ℕ) (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] where
  /-- The projection `P_i` of test `i`, a bounded operator on `H`. -/
  projection : Fin n → H →L[𝕜] H
  /-- Each `P_i` is an orthogonal projection: self-adjoint and idempotent. -/
  isStarProjection : ∀ i, IsStarProjection (projection i)
  /-- The state `φ`, a `𝕜`-linear functional on the bounded operators. For `𝕜 = ℝ` it is not
  required to be symmetric on non-self-adjoint operators. -/
  state : (H →L[𝕜] H) →ₗ[𝕜] 𝕜
  /-- `φ(1) = 1`. -/
  state_one : state 1 = 1
  /-- `φ` is real and nonnegative on positive operators. -/
  state_nonneg : ∀ T : H →L[𝕜] H, T.IsPositive → ∃ r : ℝ, 0 ≤ r ∧ state T = r

/-- The value `φ(Q₁ ⋯ Q_m ⋯ Q₁)` a representation gives a word. -/
def ProjectiveRepresentation.probability {n : ℕ} {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M : ProjectiveRepresentation n 𝕜 H) (w : Word n) : ℝ :=
  RCLike.re (M.state (wordOperator M.projection w))

/-- A right quaternionic Hilbert space structure on a real Hilbert space `H`: a right action of
`ℍ` by bounded real operators and an `ℍ`-valued inner product, right `ℍ`-linear in the second
argument and Hermitian, whose real part is the real inner product of `H`. -/
structure RightQuaternionicStructure (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  /-- Right multiplication `x ↦ x q` by a quaternion, a bounded real operator on `H`. -/
  rightMul : Quaternion ℝ →ₗ[ℝ] (H →L[ℝ] H)
  /-- Multiplication by `1` is the identity. -/
  rightMul_one : rightMul 1 = 1
  /-- It is a right action: `x (q r) = (x q) r`. -/
  rightMul_mul : ∀ q r, rightMul (q * r) = rightMul r * rightMul q
  /-- The quaternion-valued inner product. Only the axioms below are assumed (no separate
  positivity or completeness condition); they restrict the class of structures. -/
  qInner : H → H → Quaternion ℝ
  /-- Additivity in the second argument. -/
  qInner_add_right : ∀ x y z, qInner x (y + z) = qInner x y + qInner x z
  /-- Right `ℍ`-linearity in the second argument. -/
  qInner_rightMul : ∀ x y q, qInner x (rightMul q y) = qInner x y * q
  /-- Hermitian symmetry. -/
  qInner_symm : ∀ x y, qInner y x = star (qInner x y)
  /-- Its real part is the real inner product of `H`. -/
  re_qInner : ∀ x y, (qInner x y).re = inner ℝ x y

/-- The bounded `ℍ`-linear operators: those commuting with the right action of `ℍ`. -/
def RightQuaternionicStructure.linearOperators {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (S : RightQuaternionicStructure H) :
    StarSubalgebra ℝ (H →L[ℝ] H) :=
  StarSubalgebra.centralizer ℝ (Set.range S.rightMul)

/-- A sequential projective representation of `n` tests on a quaternionic Hilbert space: an
`ℍ`-linear orthogonal projection of any rank for each test and a state on the `ℍ`-linear
operators (real-linear, nonnegative on positive operators, `1` at the identity). -/
structure QuaternionicRepresentation (n : ℕ) {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (S : RightQuaternionicStructure H) where
  /-- The projection of test `i`, an `ℍ`-linear bounded operator. -/
  projection : Fin n → S.linearOperators
  /-- Each projection is self-adjoint and idempotent. -/
  isStarProjection : ∀ i, IsStarProjection (projection i)
  /-- The state, a real-linear functional on the `ℍ`-linear operators. -/
  state : S.linearOperators →ₗ[ℝ] ℝ
  /-- The state is `1` at the identity. -/
  state_one : state 1 = 1
  /-- The state is nonnegative on positive operators. -/
  state_nonneg : ∀ T : S.linearOperators, (T : H →L[ℝ] H).IsPositive → 0 ≤ state T

/-- The value `φ(Q₁ ⋯ Q_m ⋯ Q₁)` a quaternionic representation gives a word. -/
def QuaternionicRepresentation.probability {n : ℕ} {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {S : RightQuaternionicStructure H}
    (M : QuaternionicRepresentation n S) (w : Word n) : ℝ :=
  M.state (wordOperator M.projection w)

/-- An algebraic model of `n` tests: self-adjoint idempotents in a real `*`-algebra and a
real-linear functional that is Hermitian, positive on `x* x` and normalised. -/
structure AlgebraicModel (n : ℕ) (A : Type v) [Ring A] [StarRing A] [Algebra ℝ A]
    [StarModule ℝ A] where
  /-- The element `P_i` of test `i`. -/
  projection : Fin n → A
  /-- `P_i² = P_i`. -/
  idempotent : ∀ i, projection i * projection i = projection i
  /-- `P_i* = P_i`. -/
  selfAdjoint : ∀ i, star (projection i) = projection i
  /-- The state, a real-linear functional on `A`. -/
  state : A →ₗ[ℝ] ℝ
  /-- `φ(1) = 1`. -/
  state_one : state 1 = 1
  /-- `φ(x*) = φ(x)`. -/
  state_star : ∀ x, state (star x) = state x
  /-- `φ(x* x) ≥ 0`. -/
  state_nonneg : ∀ x, 0 ≤ state (star x * x)

/-- The value `φ(Q₁ ⋯ Q_m ⋯ Q₁)` an algebraic model gives a word. -/
def AlgebraicModel.probability {n : ℕ} {A : Type v} [Ring A] [StarRing A] [Algebra ℝ A]
    [StarModule ℝ A] (M : AlgebraicModel n A) (w : Word n) : ℝ :=
  M.state (wordOperator M.projection w)

/-- No representation of any of the three Hilbert-space kinds, nor any algebraic model, in
universe `Type v`, reproduces `wordProbability p ρ` on every word of the set `W`. -/
def NoRepresentationOn {n : ℕ} (p : Fin n → Albert) (ρ : Albert) (W : Set (Word n)) : Prop :=
  (∀ (𝕜 : Type) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [CompleteSpace H] (M : ProjectiveRepresentation n 𝕜 H),
      ¬ ∀ w ∈ W, M.probability w = wordProbability p ρ w) ∧
  (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation n S),
      ¬ ∀ w ∈ W, M.probability w = wordProbability p ρ w) ∧
  (∀ (A : Type v) [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] (M : AlgebraicModel n A),
      ¬ ∀ w ∈ W, M.probability w = wordProbability p ρ w)

/-! ## The four-point invariant -/

/-- The thirteen traces of four atoms: transition probabilities `o_{ij} = ⟨p_i, p_j⟩`, shape
traces `R_{ijk} = ⟨p_i ∘ p_j, p_k⟩`, double-pair traces `t₁, t₂, t₃`. This one is the transition
probability `o_{ij} = ⟨p_i, p_j⟩ = tr(p_i ∘ p_j)`. -/
def overlap (p : Fin 4 → Albert) (i j : Fin 4) : ℝ := tracePairing (p i) (p j)
/-- The shape invariant `R_{ijk} = ⟨p_i ∘ p_j, p_k⟩ = tr((p_i ∘ p_j) ∘ p_k)` of three of the atoms. -/
def triangle (p : Fin 4 → Albert) (i j k : Fin 4) : ℝ := tracePairing (jordanMul (p i) (p j)) (p k)
/-- The three double-pair traces `t₁ = ⟨p_0 ∘ p_1, p_2 ∘ p_3⟩`, `t₂ = ⟨p_0 ∘ p_2, p_1 ∘ p_3⟩`,
`t₃ = ⟨p_0 ∘ p_3, p_1 ∘ p_2⟩` (indexed `0, 1, 2`). -/
def doublePair (p : Fin 4 → Albert) : Fin 3 → ℝ :=
  ![tracePairing (jordanMul (p 0) (p 1)) (jordanMul (p 2) (p 3)),
    tracePairing (jordanMul (p 0) (p 2)) (jordanMul (p 1) (p 3)),
    tracePairing (jordanMul (p 0) (p 3)) (jordanMul (p 1) (p 2))]

/-- The four-point invariant `𝒜(p_A, p_B, p_C, p_D)` (paper eq. A:Acal52), with `ω_r` the sum of
the other two double-pair traces minus `t_r`. -/
def fourPointInvariant (p : Fin 4 → Albert) : ℝ :=
  let o := overlap p
  let R := triangle p
  let t := doublePair p
  let ω1 := t 1 + t 2 - t 0
  let ω2 := t 0 + t 2 - t 1
  let ω3 := t 0 + t 1 - t 2
  o 0 1 * o 0 2 * o 0 3 * o 1 2 * o 1 3 * o 2 3
    - (R 0 1 2 ^ 2 * o 0 3 * o 1 3 * o 2 3 + R 0 1 3 ^ 2 * o 0 2 * o 1 2 * o 2 3
        + R 0 2 3 ^ 2 * o 0 1 * o 1 2 * o 1 3 + R 1 2 3 ^ 2 * o 0 1 * o 0 2 * o 0 3)
    - 4 * R 0 1 2 * R 0 1 3 * R 0 2 3 * R 1 2 3
    - (o 0 1 * o 2 3 * ω1 ^ 2 + o 0 2 * o 1 3 * ω2 ^ 2 + o 0 3 * o 1 2 * ω3 ^ 2)
    + 2 * ω1 * (R 0 1 2 * R 0 1 3 * o 2 3 + R 0 2 3 * R 1 2 3 * o 0 1)
    + 2 * ω2 * (R 0 1 2 * R 0 2 3 * o 1 3 + R 0 1 3 * R 1 2 3 * o 0 2)
    + 2 * ω3 * (R 0 1 2 * R 1 2 3 * o 0 3 + R 0 1 3 * R 0 2 3 * o 1 2)
    - 2 * ω1 * ω2 * ω3

/-! ## Two explicit quadruples -/

/-- The rank-one element `v v†` for `v ∈ 𝕆³` (an atom when `‖v‖ = 1` and the entries of `v` lie
in an associative subalgebra). -/
def rankOne (v : Fin 3 → Octonion) : Albert :=
  (fun i => octNormSq (v i),
    ![octMul (v 0) (octConj (v 1)), octMul (v 0) (octConj (v 2)), octMul (v 1) (octConj (v 2))])

/-- The maximiser `M`: `v_A = (1,0,0)`, `v_B = (1,√2,0)/√3`, `v_C = (1,i,1)/√3`,
`v_D = (1,j,ℓ)/√3`. -/
def quadrupleM : Fin 4 → Albert :=
  let s := 1 / Real.sqrt 3
  ![rankOne ![octScalar 1, 0, 0],
    rankOne ![octScalar s, octScalar (Real.sqrt 2 * s), 0],
    rankOne ![octScalar s, s • octI, octScalar s],
    rankOne ![octScalar s, s • octJ, s • octL]]

/-- The rational quadruple `S`, by coordinates: `p_A = diag(1,0,0)`,
`p_B = ½(1,1,0; 1,0,0)`, `p_C = ⅓(1,1,1; −i,1,i)`, `p_D = ⅓(1,1,1; −j,−ℓ,−jℓ)`. -/
def quadrupleS : Fin 4 → Albert :=
  ![(![1, 0, 0], 0),
    (1 / 2 : ℝ) • (![1, 1, 0], ![octScalar 1, 0, 0]),
    (1 / 3 : ℝ) • (![1, 1, 1], ![-octI, octScalar 1, octI]),
    (1 / 3 : ℝ) • (![1, 1, 1], ![-octJ, -octL, -octMul octJ octL])]

/-! ## Special subalgebras and density-operator states -/

/-- A unital Jordan subalgebra `B` of `J` is *special*: an injective, real-linear, unital Jordan
homomorphism maps it into the complex Hermitian `d × d` matrices for some `d > 0`, whose Jordan
product is `(XY + YX)/2`. This is a finite-dimensional form of the papers' notion (isomorphism onto a
Jordan algebra of self-adjoint operators on a complex Hilbert space); for subalgebras of `J` the two
agree. -/
def JordanSubalgebra.IsSpecial (B : JordanSubalgebra) : Prop :=
  ∃ (d : ℕ) (f : B.carrier →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ), 0 < d ∧ Function.Injective f ∧
    (∀ x, (f x).IsHermitian) ∧ f ⟨albertUnit, B.unit_mem⟩ = 1 ∧
    ∀ x y : B.carrier, f ⟨jordanMul x y, B.mul_mem x x.2 y y.2⟩ =
      (1 / 2 : ℝ) • (f x * f y + f y * f x)

/-- The state of a representation on `ℂ^d` is a density operator: `φ(T) = tr(σ T)` for a positive
operator `σ` of trace one. -/
def ProjectiveRepresentation.HasDensityState {n d : ℕ}
    (M : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d))) : Prop :=
  ∃ σ : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d), σ.IsPositive ∧
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin d)) σ = 1 ∧
    ∀ T, M.state T = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin d)) (σ * T)

end AlbertChallenge
