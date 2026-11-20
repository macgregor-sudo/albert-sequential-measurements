# On sequential ideal measurements in the exceptional Jordan algebra

A Lean 4 formalization accompanying two papers: "On sequential ideal measurements in the exceptional
Jordan algebra" (the *core paper*), Hexagon record
[hexagon:2611.00620](https://hexagonmath.org/abs/2611.00620), and "Finite certificates for
sequential measurements in the exceptional Jordan algebra" (the *companion paper*), whose LaTeX
source is `companion/macgregor-finite-certificates.tex` in the source archive of the same record.
The release tagged `v2.0.0` accompanies version 2 of both papers, whose PDFs are attached to the
[GitHub release v2.0.0](https://github.com/macgregor-sudo/albert-sequential-measurements/releases/tag/v2.0.0);
the release tagged `v1.0.0` accompanied version 1. Repository:
https://github.com/macgregor-sudo/albert-sequential-measurements.

The formalization concerns sequences of ideal yes–no measurements on the Albert algebra and whether
a real, complex or quaternionic Hilbert-space model can reproduce their statistics. Every numbered
statement of the core paper (96, counting definitions, remarks and examples) is proved in Lean, and
so is every numbered statement of the companion paper (30) except Remark 5.3, which is proved in
part. [Status of every numbered statement](#status-of-every-numbered-statement) names the
declarations for each. Twelve theorems of the core paper are also stated in a file that imports
only Mathlib, and Comparator checks that the proofs prove exactly those statements. The other
results are kernel-checked by the ordinary build, and an audit of every exported
declaration of every module except `Challenge` checks that none depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound` ([How it was verified](#how-it-was-verified)).

Status: research artifact. Each release is a fixed tagged commit; the repository is not maintained
and does not accept contributions. Lean `v4.36.0`, Mathlib `v4.36.0` (commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`), unmodified.

All mathematics, proofs, text and Lean code in this repository were produced by AI systems, except
the adapted code listed in [docs/ATTRIBUTION.md](docs/ATTRIBUTION.md) (see
[How this was produced](#how-this-was-produced)). No human has checked that the Lean statements mean
what the papers say.

## Background in one page

A *Jordan algebra* here is a real vector space with a commutative bilinear product `x ∘ y`. The
example to keep in mind is the space of Hermitian `n × n` matrices with `x ∘ y = (xy + yx)/2`. The
*octonions* `𝕆` are the 8-dimensional real division algebra obtained by doubling the quaternions `ℍ`
(the Cayley–Dickson construction); their multiplication is not associative. The *Albert algebra*
`J = H₃(𝕆)` is the 27-dimensional space of Hermitian `3 × 3` octonionic matrices with the same
product. It is a Jordan algebra that is not isomorphic to any Jordan algebra of self-adjoint
operators on a Hilbert space.

In `J` an *idempotent* is an element `p` with `p ∘ p = p`. An *atom* is an idempotent of trace one, the
analogue of a rank-one projection; theorem 12 below shows that the atoms are exactly the primitive
idempotents, the nonzero idempotents that are not a sum of two nonzero idempotents `q`, `r` with
`q ∘ r = 0`. A *state* is a trace-one element of the cone of squares, the analogue of a density
matrix; `e/3`, where `e` is the identity matrix, is the *maximally mixed state*. The *quadratic map*
`U_x y = 2 x ∘ (x ∘ y) − (x ∘ x) ∘ y` plays the role of `y ↦ x y x`.

An *ideal test* of an atom `p` has outcomes "yes" and "no". From a state `ρ` the outcome "yes"
updates `ρ` to `U_p ρ` and "no" to `U_{e−p} ρ` (the Lüders rule, without renormalisation). A *word*
is a finite sequence of outcomes in chronological order, and its *probability* is the trace of the
state after all its updates, `tr(U_{q_m} ⋯ U_{q_1} ρ)`.

A *sequential projective representation* of `n` tests is a Hilbert space over `ℝ`, `ℂ` or `ℍ`, of any
dimension, an orthogonal projection `P_i` of any rank for each test, and a state `φ` on the bounded
operators. It assigns to a word with outcome operators `Q_1, …, Q_m` (each `Q_t` is `P_i` or
`1 − P_i`) the number `φ(Q_1 ⋯ Q_{m−1} Q_m Q_{m−1} ⋯ Q_1)`, and it *reproduces* a set of words if
these numbers equal the Albert word probabilities on that set. An *algebraic model* replaces the
Hilbert space by a real `*`-algebra, the projections by self-adjoint idempotents and the state by a
real-linear functional that is Hermitian, nonnegative on every `x* x` and equal to `1` at `1`; every
representation induces one. Atoms `p_1, …, p_n` *generate* `J` if the only subspace of `J` that
contains `e` and the `p_i` and is closed under `∘` is `J` itself. A unital subalgebra of `J` is
*special* (in the Challenge's sense) if a real-linear, injective, unital map into the complex
Hermitian `d × d` matrices, `d ≥ 1`, takes `x ∘ y` to `(XY + YX)/2`.

For four atoms the core paper defines a polynomial `𝒜`, the *four-point invariant*, in thirteen traces
of their Jordan products: six transition probabilities `o_ij = tr(p_i ∘ p_j)`, four shape invariants
`R_ijk = tr((p_i ∘ p_j) ∘ p_k)` and three double-pair traces such as `tr((p_A ∘ p_B) ∘ (p_C ∘ p_D))`.

## Compared theorems

The statement file is [`src/Challenge.lean`](src/Challenge.lean), namespace `AlbertChallenge`. It imports six
Mathlib modules and nothing else, so every object used in a statement is defined there with a
docstring. Each theorem in it ends in `sorry`. [`src/Solution.lean`](src/Solution.lean) states the same twelve
theorems over a verbatim copy of the Challenge's definitions (`src/ChallengeDefs.lean`) and proves each by
one appeal to the bridge modules `src/Bridge/*.lean` (namespace `AlbertChallenge.Bridge`), which derive
them from the development (namespace `AlbertSequential`). [`comparator.json`](comparator.json) names
the twelve theorems and the three permitted axioms for Comparator, the tool Palomar uses to check that
a solution proves exactly the statements of a challenge. Paper results are cited by their printed numbers, which are the same in versions 1 and 2, with
their LaTeX labels.

**1. No representation for generating atoms** (core Theorem 4.1, `thm:bridgeJ`, no-go sentence;
Corollary 5.11, `cor:fp:noideal`).
If finitely many atoms generate `J`, then for every element `ρ` of `J`, a state or not, no
representation of any of the three kinds and no algebraic model, on a carrier in any universe
`Type v`, reproduces their word probabilities on all words.

```lean
theorem no_representation_of_generates {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) (ρ : Albert) : NoRepresentationOn.{v} p ρ Set.univ
```

**2. A finite separating inequality** (core Theorem 4.1, last sentence; Corollary 4.16(a),
`cor:bri:finite`). For
generating atoms there are a length `L`, a finite set of words of length at most `L`, real
coefficients and `γ > 0` such that the weighted sum of word values is nonnegative in every real,
complex and quaternionic representation (carriers in `Type v`) and at most `−γ` for the Albert
probabilities from every state. As stated, the inequality may depend on the universe `v` of the
carriers, since the existential sits inside the universe parameter; the proof
(`Bridge.linear_separator_bridge`) takes `L`, the words, the coefficients and `γ` from the
universe-free statement `uniformMomentSeparator_generating_atoms` about moment sequences, so one
inequality serves every universe, and it is also nonnegative on algebraic models.

```lean
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
      (∀ ρ, IsDensity ρ → ∑ w ∈ W, c w * wordProbability p ρ w ≤ -γ)
```

**3. Seven steps exclude every model** (core Theorem 6.1(a), `thm:cer:uniform`). For four atoms that generate `J`,
no representation or algebraic model (carriers in `Type v`) reproduces from `e/3` every word of length
at most seven whose first outcome is "yes" on test `0`, and none reproduces from the pure state `p 0`
every word of length at most six.

```lean
theorem seven_steps_exclude (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hg : Generates p) :
    NoRepresentationOn.{v} p maximallyMixed (yesFirstUpTo 7) ∧
      NoRepresentationOn.{v} p (p 0) (wordsUpTo 4 6)
```

**4. Six steps never suffice** (core Proposition 6.2, `prop:cer:universalsix`). For four atoms that generate `J`, some
complex representation on `ℂ¹²` reproduces from `e/3` every word of length at most six.

```lean
theorem six_step_model (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hg : Generates p) :
    ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w ∈ wordsUpTo 4 6, M.probability w = wordProbability p maximallyMixed w
```

**5. The least separating length is seven** (core: "`L_min = 7`", in Theorem 6.1 and
Proposition 6.2). For four atoms that generate `J`, seven is the least `L` such that no real,
complex or quaternionic representation on a Hilbert space in `Type`, Lean's lowest universe,
reproduces from `e/3` every word of length at most `L`.

```lean
theorem least_separating_length (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) :
    IsLeast {L : ℕ | (∀ (𝕜 : Type) (H : Type) [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] [CompleteSpace H] (M : ProjectiveRepresentation 4 𝕜 H),
        ¬ ∀ w ∈ wordsUpTo 4 L, M.probability w = wordProbability p maximallyMixed w) ∧
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (S : RightQuaternionicStructure H) (M : QuaternionicRepresentation 4 S),
        ¬ ∀ w ∈ wordsUpTo 4 L, M.probability w = wordProbability p maximallyMixed w)} 7
```

**6. The four-point criterion** (core Theorem 5.5, `thm:fourpoint`, parts (i) and (iii)). For any four atoms,
`𝒜 ≥ 0`, and `𝒜 > 0` exactly when they generate `J`.

```lean
theorem fourPoint_criterion (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    0 ≤ fourPointInvariant p ∧ (0 < fourPointInvariant p ↔ Generates p)
```

**7. The maximum of `𝒜`** (core Proposition 5.12, `prop:max`, bound and value). The four elements of the explicit
quadruple `M` are atoms, `𝒜(M) = 4/19683`, and `𝒜 ≤ 4/19683` for all four atoms.

```lean
theorem quadrupleM_spec :
    (∀ i, IsAtom (quadrupleM i)) ∧ fourPointInvariant quadrupleM = 4 / 19683 ∧
      ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) → fourPointInvariant p ≤ 4 / 19683
```

**8. The rational quadruple `S`** (core Section 6, paragraph "Two configurations"; unnumbered). The four elements of the explicit quadruple `S`, with rational
coordinates, are atoms, and `𝒜(S) = 1/5832`.

```lean
theorem quadrupleS_spec :
    (∀ i, IsAtom (quadrupleS i)) ∧ fourPointInvariant quadrupleS = 1 / 5832
```

**9. Three atoms** (core Proposition 5.1, `prop:three`). Three atoms never generate `J`, and for every state some
complex representation on `ℂ³`, which may depend on the state, reproduces every word.

```lean
theorem three_atoms (p : Fin 3 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ¬ Generates p ∧ ∀ ρ, IsDensity ρ →
      ∃ M : ProjectiveRepresentation 3 ℂ (EuclideanSpace ℂ (Fin 3)),
        ∀ w : Word 3, M.probability w = wordProbability p ρ w
```

**10. Vanishing invariant** (core, the paragraph after Corollary 5.11; unnumbered). If four atoms have `𝒜 = 0`,
then for every state some complex representation on `ℂ⁶`, which may depend on the state, reproduces
every word.

```lean
theorem zero_invariant_model (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (h0 : fourPointInvariant p = 0) :
    ∀ ρ, IsDensity ρ → ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (Fin 6)),
      ∀ w : Word 4, M.probability w = wordProbability p ρ w
```

**11. The Albert criterion** (core Theorem 4.1, the equivalence of (1), (2) and (3)). For any finite
family of atoms `p_1, …, p_n` (any `n`, including `0`), each of the following three conditions is
equivalent to "`p_1, …, p_n` do not generate `J`".
(a) Some unital Jordan subalgebra of `J` that contains every `p_i` is special (`IsSpecial`: a
real-linear, injective, unital map into the complex Hermitian `d × d` matrices, for some `d > 0`, that
takes `x ∘ y` to `(XY + YX)/2`).
(b) There are `d = 6` or `d = 24` and one representation `M₀` on `ℂ^d` such that for every state `ρ`
some representation on `ℂ^d` with the same projections as `M₀` and a density-operator state
(`φ(T) = tr(σT)` with `σ` positive of trace one; `HasDensityState`) reproduces every word from `ρ`.
The projections do not depend on the state; only `σ` does.
(c) For at least one state `ρ`, some real or complex representation (scalar field any `RCLike`
field), some quaternionic representation or some algebraic model, with carrier in `Type`,
reproduces every word from `ρ`.

```lean
theorem albert_criterion {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i)) :
    (¬ Generates p ↔ ∃ B : JordanSubalgebra, (∀ i, p i ∈ B.carrier) ∧ B.IsSpecial) ∧
    (¬ Generates p ↔ ∃ d : ℕ, (d = 6 ∨ d = 24) ∧
      ∃ M₀ : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)), ∀ ρ, IsDensity ρ →
        ∃ M : ProjectiveRepresentation n ℂ (EuclideanSpace ℂ (Fin d)),
          M.projection = M₀.projection ∧ M.HasDensityState ∧
          ∀ w : Word n, M.probability w = wordProbability p ρ w) ∧
    (¬ Generates p ↔ ∃ ρ, IsDensity ρ ∧ ¬ NoRepresentationOn.{0} p ρ Set.univ)
```

**12. Atoms are the primitive idempotents** (core Section 3.1, the definition of atoms;
unnumbered). An element `p` of `J` is an atom (`p ∘ p = p` and `tr p = 1`) if and only if `p ∘ p = p`,
`p ≠ 0`, and there are no idempotents `q`, `r`, both nonzero, with `q ∘ r = 0` and `p = q + r`.

```lean
theorem isAtom_iff_primitive (p : Albert) :
    IsAtom p ↔ jordanMul p p = p ∧ p ≠ 0 ∧
      ¬ ∃ q r : Albert, jordanMul q q = q ∧ jordanMul r r = r ∧ q ≠ 0 ∧ r ≠ 0 ∧
        jordanMul q r = 0 ∧ p = q + r
```

How the twelve relate to the core paper's statements. Theorem 11 is the core paper's criterion for
every finite family of atoms, in a form stronger than printed in two places: condition (b) fixes the
dimension at `6` or `24` and uses one family of projections for all states, where the printed
condition allows a dimension depending on the state; and "special" is witnessed by complex Hermitian
matrices of finite size, where the paper allows operators on any complex Hilbert space. Condition (c)
is restricted to carriers in `Type` and admits algebraic models; theorem 1 shows, in every universe,
that a representation from one state excludes generation. Theorems 1, 2 and 11 together give core
Theorem 4.1 with its condition (1) read as "the generated subalgebra is not `J`". The printed
theorem itself, with speciality in the operator sense, is proved but not compared:
`Bridge.printed_albert_criterion` (carriers in `Type`), with `Bridge.proper_iff_hasClassIModel`
and `nativeOperatorSpecial_iff_proper` in every universe; it rests on `albertJordanHom_eq_zero`, which
says that `J` has no nonzero Jordan homomorphism into an associative algebra. Likewise
`Bridge.least_separating_length_all_universes` proves theorem 5 for Hilbert spaces in every
universe. Theorems 9 and 10 give smaller models for three atoms and for four
atoms that do not generate `J` (by theorem 6 these are exactly the quadruples with `𝒜 = 0`).
Theorems 3 to 6 give the core paper's account of four generating atoms: from `e/3` a complex model
agrees with them on every word of length six and no model agrees at length seven.
[docs/STATEMENTS.md](docs/STATEMENTS.md) gives every definition these statements use and each difference from
the papers; [docs/PROOF-PATH.md](docs/PROOF-PATH.md) gives the route of each proof, and
[Dense proof for AI agents](#dense-proof-for-ai-agents) states those routes as chains of implications.


## Scope of the formal statements

Hypotheses. Theorems 1 to 6 and 9 to 11 assume that their inputs are atoms (`IsAtom`: idempotent of
trace one); theorem 12 characterises atoms and has no hypothesis, and theorems 7 and 8 prove that
the explicit quadruples consist of atoms. Theorems 1 to 5 assume the atoms generate `J` (`Generates`);
theorem 6 relates that hypothesis to `𝒜 > 0`, which is the hypothesis the core paper states for
theorems 3 to 5. Theorem 1 places no condition on `ρ`; for a `ρ` that is not a state its conclusion
is stronger than the paper's, and immediate when `tr ρ ≠ 1`, because the empty word then fails to
match.

Model classes, as encoded in `Challenge.lean`:

- A real or complex representation (`ProjectiveRepresentation n 𝕜 H`) quantifies over every `RCLike`
  field `𝕜`, which covers `ℝ` and `ℂ`. Its state is a `𝕜`-linear functional on all bounded operators
  that is real and nonnegative on positive operators and equals `1` at the identity. The papers use a
  positive real-linear functional on bounded self-adjoint operators. For `𝕜 = ℝ` the Challenge's
  condition does not force the state to be Hermitian on non-self-adjoint operators, so this class is
  wider than the papers'; the exclusions cover it, and the bridges symmetrise such a state before use.
  The same holds for quaternionic states, which are real-linear on the `ℍ`-linear operators and not
  required to be symmetric. The extra freedom changes no word value: every word operator
  `Q_1 ⋯ Q_m ⋯ Q_1` is self-adjoint, and on self-adjoint operators such a state agrees with its
  symmetrisation.
- A quaternionic Hilbert space is not a primitive. It is a real Hilbert space with a right action of
  `ℍ` by bounded real operators and an `ℍ`-valued inner product whose real part is the real inner
  product (`RightQuaternionicStructure`). The `ℍ`-linear operators are the commutant of the right
  action (`linearOperators`), and the projections and the state live there
  (`QuaternionicRepresentation`). No proof uses the `ℍ`-valued inner product: its axioms only
  restrict the class, so the exclusions would hold without them. The development proves that its
  operator-structure presentation is equivalent to a right `ℍ`-module with an `ℍ`-valued inner
  product (`rightQuaternionicHilbertPresentationEquiv`); that equivalence is not part of a compared
  statement.
- Algebraic models (`AlgebraicModel`) are excluded in theorems 1 and 3, which is stronger than
  excluding representations, and admitted as witnesses in theorem 11(c). Theorems 2 and 5 do not
  mention them.
- There is no condition of normality, faithfulness, finite dimension, separability or projection
  rank. Carriers range over an arbitrary universe `Type v` in theorems 1 to 3 and over `Type`, Lean's
  lowest universe, in theorem 5 and in theorem 11(c). Theorems 4, 9, 10 and 11(b) name the carriers
  `ℂ¹²`, `ℂ³`, `ℂ⁶` and `ℂ⁶` or `ℂ²⁴`.

Encoding choices to check against the papers:

- `Albert` is a pair (three real diagonal entries, three octonionic upper entries in positions
  `(0,1)`, `(0,2)`, `(1,2)`); only its real vector space structure comes from the product type, and
  the product is the explicit function `jordanMul`. The paper's `(ξ; x₁, x₂, x₃)` is the Lean upper
  triple `(x₃, conj x₂, x₁)`.
- `Octonion` is a pair of Mathlib quaternions with product `(a, b)(c, d) = (ac − d̄b, da + bc̄)`, the
  Cayley–Dickson doubling with parameter `−1`. Mathlib `v4.36.0` has no octonions or Albert algebra.
  The same convention is used by the development's `Glennie.octMul`, adapted from an earlier entry
  (see [Relation to earlier formalizations and reused code](#relation-to-earlier-formalizations-and-reused-code)).
- `IsAtom` is "idempotent of trace one"; the papers define an atom as a primitive idempotent.
  Theorem 12 proves that the two agree, with orthogonality of idempotents taken as `q ∘ r = 0`.
- `JordanSubalgebra.IsSpecial` asks for an embedding into complex Hermitian matrices of finite size;
  the paper's "special" (for a Euclidean Jordan algebra) means isomorphic to a Jordan algebra of
  self-adjoint operators on a complex Hilbert space.
- The Challenge does not state that `jordanMul` satisfies the Jordan identity; the development proves
  it (`NativeAnalysis.jordan_identity`, module `NativeJordanIdentity`).
- `wordProbability` applies the unnormalised updates in chronological order and takes the trace; the
  head of the list is the first outcome. Words are arbitrary lists, not reduced words.
- `fourPointInvariant` is the polynomial of core equation (5.4) (`eq:A:Acal52`), with
  `ω_r = t₁ + t₂ + t₃ − 2 t_r`. It appears only in theorems 6, 7, 8 and 10.
- `quadrupleM` and `quadrupleS` are written in the printed form (rank-one elements `v v†` and explicit
  coordinates). That they consist of atoms is proved, not assumed.
- Test `0` is the paper's `A`, and `p 0` is its pure state `p_A`.

Edge cases of the definitions, and why the hypotheses exclude them:

- Zero spaces and trivial algebras. A representation on the zero space, or an algebraic model in the
  zero ring, would have `1 = 0` and so `φ(1) = 0`; the field `state_one` (`φ(1) = 1`) excludes it, so
  no exclusion holds vacuously because of a degenerate model.
- `n = 0`. With no atoms, `Generates p` is false (the line `ℝe` is a proper unital subalgebra), so
  theorems 1 and 2 are not vacuous for a reachable input; theorem 11 holds for `n = 0` with `d = 1` in
  (a) and is proved for every `n`.
- `ρ` that is not a state. Only theorem 1 admits it; when `tr ρ ≠ 1` its conclusion is immediate from
  the empty word, and for other `ρ` it is stronger than the printed statement.
- Empty word. `wordOperator` of the empty word is `1`, so every model gives it the value `1`;
  `wordsUpTo` contains it, `yesFirstUpTo` does not. This is why `L = 0` is not in the set of
  theorem 5.
- Coordinates of `jordanMul`. `albertCoordinates` keeps the real parts of the diagonal entries of
  `xy + yx`; for Hermitian octonionic matrices these entries are real, so nothing is discarded. The
  catch-all branch of `albertMatrix` is unreachable for indices in `Fin 3`.
- `rankOne v` is an atom only when `v` has norm one and its entries lie in an associative
  subalgebra; theorems 7 and 8 prove that the quadruples `M` and `S` consist of atoms, so nothing is
  assumed about them.
- `IsSpecial` asks `d > 0`; unitality and injectivity already force it, since `e ≠ 0`.
- `NoRepresentationOn p ρ W` is false for empty `W`; every compared use has `W` nonempty
  (`Set.univ`, `yesFirstUpTo 7`, `wordsUpTo 4 6`).
- The scalar field `𝕜` of a real or complex representation ranges over `RCLike` fields in `Type`,
  which up to isomorphism are `ℝ` and `ℂ`; the carriers range over `Type v`.

What is not formalized. Every numbered statement of the core paper is proved in Lean. In the
companion paper Remark 5.3 is proved in part: the properties of the signed invariant `Φ` and the
invariance of the 29 traces are proved, and the cited results on generators, relations, degree
bounds, the invariant field and integrality are not. Some unnumbered passages use cited structure
theorems that are not formalized: the smooth structure of the space of four atoms modulo `F₄` in
core Section 5.2, whose dimension count `4·16 − 52 = 12` is checked; the Lie-group facts about `F₄`
and its subgroups quoted in core Appendix A.5 and in proofs that use them, where the formal proofs
use explicit automorphisms; the spectral doubling in the printed proof of core Proposition C.2, whose
conclusions are checked directly; and the classification of the Wallach set for all Riesz parameters
cited in companion Section 5. Values that the papers call numerical are not formalized. Core
Appendix G and companion Appendix C give the same account, and
[docs/UNNUMBERED-CORE.md](docs/UNNUMBERED-CORE.md) and
[docs/UNNUMBERED-LATE.md](docs/UNNUMBERED-LATE.md) go through the unnumbered claims passage by
passage.

## Dense proof for AI agents

Tags: [Tn] compared theorem n; [L] Lean-checked, not compared; [P] printed route, replaced in Lean by the route stated before it. Labels are core-paper labels. All $`p_i`$ are atoms (`IsAtom`); gen means `Generates`; $`\Pr_\rho(w)`$ is `wordProbability p ρ w`, written $`\Pr^{q}_\rho`$ for another quadruple $`q`$; $`\mathrm{Jord}\langle e,p_i\rangle`$ is the unital subalgebra generated by the $`p_i`$. Four tests: $`A,B,C,D`$ are tests $`0,1,2,3`$; $`t_r`$, $`\omega_r`$ as in the table below and in [Scope of the formal statements](#scope-of-the-formal-statements), $`(\omega_B,\omega_C,\omega_D)=(\omega_1,\omega_2,\omega_3)`$. $`\Pr_{\mathfrak D}(w)=\varphi(Q_1\cdots Q_m\cdots Q_1)`$ is the value a model $`\mathfrak D`$ gives $`w`$.

Models. $`Q_t\in\{P_i,1-P_i\}`$ self-adjoint idempotent $`\Rightarrow Q_1\cdots Q_{m-1}Q_mQ_{m-1}\cdots Q_1=a^*a,\ a=Q_m\cdots Q_1`$; real or complex representation $`\mapsto`$ algebraic model on $`B(H)`$ as real $`*`$-algebra with state $`T\mapsto\operatorname{Re}\varphi(\tfrac12(T+T^*))`$; quaternionic representation $`\mapsto`$ algebraic model on the commutant of the right $`\mathbb H`$-action ($`\mathbb H`$-valued inner product unused); Challenge algebraic model $`\mapsto`$ development algebraic model $`\mathfrak D`$; all word values preserved [L]. Every exclusion below is proved for development algebraic models $`\mathfrak D`$, carriers in any universe.

T12. Idempotent $`q\Rightarrow\mathrm{tr}\,q\in\{0,1,2,3\}`$, $`\mathrm{tr}\,q=0\Leftrightarrow q=0`$; $`q\ne0\Rightarrow\mathrm{tr}\,q\ge1`$, so $`q+r`$ with $`q,r\ne0`$, $`q\circ r=0`$ has trace $`\ge2`$ and is no atom; $`\mathrm{tr}\,p\in\{2,3\}\Rightarrow\exists g\in\mathrm{Aut}(J)`$, $`gp`$ diagonal $`0/1`$ with $`\ge2`$ ones $`\Rightarrow p=q+r`$, $`q,r\ne0`$ idempotent, $`q\circ r=0`$ [T12].

$`\mathsf S`$. Atoms with rational coordinates [T8]; $`o_{AB}=\tfrac12`$, other $`o_{ab}=\tfrac13`$, $`(R_{ABC},R_{ABD},R_{ACD},R_{BCD})=(\tfrac16,\tfrac16,\tfrac19,\tfrac19)`$, $`t_r=\omega_r=\tfrac1{18}`$ [L] $`\Rightarrow\mathcal A(\mathsf S)=\tfrac1{5832}`$ [T8], so $`\mathsf S`$ generates by T6; $`Q_{A;BCD}=Q_{A;CDB}=Q_{A;DBC}=\tfrac1{18}`$, $`\Delta_A(\mathsf S)=\tfrac1{104976}`$ [L].

T1. Purity: $`q`$ atom, $`c=\mathrm{tr}(U_{v_m}\cdots U_{v_1}q)`$, $`z_q(v)=P_qE_vP_q-cP_q`$, $`\check v=(v_{m-1},\dots,v_1)`$: $`\|z_q(v)P_t\Omega\|^2=\Pr_{\mathfrak D}(t,q,v,\check v,q)-2c\Pr_{\mathfrak D}(t,q,v)+c^2\Pr_{\mathfrak D}(t,q)`$ in every model $`\mathfrak D`$, the same combination of $`\Pr_\rho`$ is $`0`$ in $`J`$ by $`U_{U_ab}=U_aU_bU_a`$, $`U_qx=\langle q,x\rangle q`$. Reflections $`U_{2p-e}=2(U_p+U_{e-p})-\mathrm{id}`$, $`\Sigma Y\Sigma=2PYP+2(1-P)Y(1-P)-Y`$ $`(\Sigma=2P-1)`$; reflected-orbit span $`=\mathrm{Jord}\langle e,p_i\rangle`$; transported purity and linear relations vanish on the cyclic word space $`\Rightarrow`$ matching $`\mathfrak D`$ from any $`\rho\in J`$ gives $`\eta:\mathrm{Jord}\langle e,p_i\rangle\to\mathrm{End}`$(cyclic word space), Jordan, $`\eta(e)=1`$ [L, tests atoms of $`J`$]; gen $`\Rightarrow`$ domain $`J`$. Exceptionality [L]: $`\eta:J\to A^+`$, $`A`$ associative real, possibly nonunital; $`X_a=\eta(s_a)`$, $`(s_a)=\mathsf S`$; Jordan maps preserve $`U`$ and $`\{xyz\}\Rightarrow`$ (R1)–(R3) for $`X_a\Rightarrow\Delta_AX_A=0`$ (algebraic tetrahedron identity, no positivity, no $`o_{ab}>0`$) $`\Rightarrow\eta(E_{11})=0`$ $`(s_A=E_{11})`$ $`\Rightarrow`$ Peirce propagation $`\eta(E_{22})=\eta(E_{33})=0\Rightarrow\eta(e)=0\Rightarrow\eta=\eta(e\circ\cdot)=0`$; [P] (R1) at $`b\ne A`$, $`o_{Ab}\ne0\Rightarrow\eta(s_b)=0`$, $`y=\sum_as_a`$, $`y^3-4y^2+\tfrac{23}6y-\tfrac79e=0\Rightarrow\eta(e)=0\Rightarrow\eta=\eta(U_e\,\cdot)=0`$. $`\eta(e)=1\ne0`$ (state $`\varphi(1)=1`$) $`\Rightarrow`$ no matching real, complex or quaternionic representation or algebraic model, any $`n`$, any $`\rho\in J`$, carriers in `Type v` [T1].

T2. $`\mathcal M_n`$ = moment vectors $`\nu`$ on words in $`n`$ letters: $`\nu(\varnothing)=1`$, reversal-invariant, idempotent in context, $`\ge0`$ on polynomial squares, $`|\nu|\le1`$; compact convex; densities of $`J`$ compact convex. $`\Pr_\nu(w)`$: value of the word $`w`$ under $`\nu`$ (polynomial in the moments). T1 at the moment level $`\Rightarrow`$ no $`(\nu,\rho)`$ matches on all words; compactness $`\Rightarrow`$ a finite word set $`F\ni\varnothing`$ on which no $`(\nu,\rho)`$ matches; strict separation of the disjoint compact convex images in $`\mathbb R^F`$ $`\Rightarrow\exists L,(c_w)_{w\in F},\gamma>0`$: $`\sum c_w\Pr_\nu(w)\ge0\ \forall\nu\in\mathcal M_n`$, $`\sum c_w\Pr_\rho(w)\le-\gamma\ \forall`$ states $`\rho`$ [L]; [P] nested closed sets $`\{(\nu,\rho):\text{match for }|w|\le L\}`$, one empty. $`\Rightarrow`$ for each `Type v`: $`\ge0`$ on real, complex, quaternionic representations [T2]; the same $`L,c,\gamma`$ for every universe and for algebraic models [L]. No bound on $`L,\gamma`$.

T6. $`\exists g\in\mathrm{Aut}(J)`$: $`gp_i=v_iv_i^\dagger`$, $`v_A=(1,0,0)`$, $`v_B=(B_0,B_1,0)`$, $`v_C=(C_0,C_1+C_2i,C_3)`$, $`v_D=(D_0,X,Y)`$, $`X=x_0+x_1i+x_2j`$, $`Y=y_0+y_1i+y_2j+y_3ij+y_4\ell`$, $`B_0,B_1,C_0,C_2,C_3,D_0,x_2,y_4\ge0`$; $`\mathcal A`$ is $`\mathrm{Aut}(J)`$-invariant; edge amplitudes $`g_1=B_0C_0+B_1z`$, $`g_2=B_0D_0+B_1X`$, $`g_3=C_0D_0+\bar zX+C_3Y`$, $`z=C_1+C_2i`$, $`u_k=\operatorname{Im}g_k`$; Harvey–Lawson $`\det(\langle u_k,u_l\rangle)-\langle u_1\times u_3,u_2\rangle^2=\tfrac14|[u_1,u_3,u_2]|^2`$ ($`u\times v=\operatorname{Im}(uv)`$, $`[x,y,z]=(xy)z-x(yz)`$), Artin $`\Rightarrow\mathcal A=\tfrac14B_0^2B_1^4C_0^2C_2^2C_3^2D_0^2|[i,X,Y]|^2=B_0^2B_1^4C_0^2C_2^2C_3^2D_0^2x_2^2y_4^2\ge0`$. $`\mathcal A>0\Rightarrow`$ no pair coincident or orthogonal, $`C_2C_3x_2y_4\ne0\Rightarrow`$ gen; $`\mathcal A=0\Rightarrow p_i`$ in one quaternionic subalgebra ($`\cong H_3(\mathbb H)`$, $`\dim15<27`$) $`\Rightarrow`$ (gen $`\Rightarrow\mathcal A>0`$); hence $`\mathcal A\ge0`$, $`\mathcal A>0\Leftrightarrow`$ gen [T6]; $`\mathcal A=0\Leftrightarrow`$ atoms in one quaternionic subalgebra [L].

T7. Normal form, unit vectors: $`B_0^2B_1^4=u(1-u)^2\le\tfrac4{27}`$ $`(u=B_0^2)`$, $`C_0^2C_2^2C_3^2\le\tfrac1{27}`$, $`D_0^2x_2^2y_4^2\le\tfrac1{27}`$ (three nonnegative factors with sum $`\le1`$) $`\Rightarrow\mathcal A\le\tfrac4{3^9}=\tfrac4{19683}`$; $`\mathsf M`$: all $`o=\tfrac13`$, $`R=\tfrac19`$, $`t_r=\tfrac1{27}`$ [L]; atoms, $`\mathcal A(\mathsf M)=\tfrac4{19683}`$, bound for all atoms [T7]; equality exactly on the $`\mathrm{Aut}(J)`$-orbit of $`\mathsf M`$ [L].

T9. $`n=3`$: $`\exists g\in\mathrm{Aut}(J)`$, $`gp_i\in H_3(\mathbb C)\Rightarrow`$ trace-preserving iso $`\psi:W\to H_3(\mathbb C)`$, $`W=g^{-1}H_3(\mathbb C)`$; $`\psi(p_i)`$ rank one; $`\sigma=\psi(\rho_W)`$, $`\rho_W`$ trace-orthogonal projection of $`\rho`$ on $`W`$, density matrix, $`\operatorname{Re}\mathrm{tr}(\sigma Q_1\cdots Q_m\cdots Q_1)=\Pr_\rho(w)\ \forall w`$ [L]; state $`T\mapsto\mathrm{tr}(\sigma T)`$, $`\mathrm{tr}(\sigma X)=\mathrm{tr}(\sqrt\sigma X\sqrt\sigma)\ge0`$ $`\Rightarrow`$ representation on $`\mathbb C^3`$ per state; gen would contradict T1 at $`\rho=p_0`$ [T9].

T10. $`\mathcal A=0\Rightarrow p_i\in`$ quaternionic subalgebra [L] $`\Rightarrow`$ embedding $`\iota_{\mathbb H}:H_3(\mathbb H)\to H_6(\mathbb C)`$, trace form $`\times2`$ $`\Rightarrow`$ fixed rank-two projections on $`\mathbb C^6`$, density matrix per state, every word [L] $`\Rightarrow`$ [T10].

T11. $`\neg`$gen $`\Rightarrow`$ proper unital $`B\ni p_i`$ $`\Rightarrow B\subseteq\mathbb Rq\oplus J_0(q)`$ ($`q`$ atom) or $`B\subseteq`$ quaternionic subalgebra [L] $`\Rightarrow`$ unital Jordan embedding into $`H_{24}(\mathbb C)`$ (trace form $`\times8`$) or $`H_6(\mathbb C)`$ ($`\times2`$) $`\Rightarrow`$ state-independent Hermitian idempotents $`P_i`$, per-state density matrix $`\sigma`$ with $`\operatorname{Re}\mathrm{tr}(\sigma Q_1\cdots Q_m\cdots Q_1)=\Pr_\rho(w)`$ $`\Rightarrow`$ (b), $`d\in\{6,24\}`$, $`M_0`$ from $`\rho=\mathrm{diag}(1,0,0)`$; (b) $`\Rightarrow`$ (c) at that $`\rho`$, carrier in `Type`; (c) $`\Rightarrow\neg`$gen by T1 at universe $`0`$; (a) $`\Leftrightarrow\neg`$gen: unital subalgebra proper $`\Leftrightarrow`$ unital injective Jordan map into $`H_d(\mathbb C)`$, $`d\ge1`$ [L] [T11]. Printed `thm:bridgeJ`, (1) $`\Leftrightarrow`$ (2) $`\Leftrightarrow`$ (3) with operator-sense speciality and $`d`$ depending on $`\rho`$, carriers in `Type` [L] (`Bridge.printed_albert_criterion`): from T1, T11 and $`\eta:J\to A^+\Rightarrow\eta=0`$; carriers in any universe [L] (`Bridge.proper_iff_hasClassIModel`, `nativeOperatorSpecial_iff_proper`); its last two sentences are T1 and T2.

T3. $`\mathcal A>0`$ (T6) $`\Rightarrow o_{ab}\in(0,1)`$. Match from $`e/3`$ on `yesFirstUpTo 7` $`\Rightarrow`$ positive semidefinite real form on the cyclic word space, $`\xi=P_A\Omega/\|P_A\Omega\|`$; match from $`p_A`$ on `wordsUpTo 4 6` $`\Rightarrow\xi=\Omega`$ ($`\Pr_{\mathfrak D}(A)=1`$); either $`\Rightarrow`$ (H): $`P_A\xi=\xi`$, $`\|P_u\xi\|^2=3\Pr_{e/3}(A,u)=\Pr_{p_A}(u)`$, $`|u|\le6`$. (H) $`\Rightarrow`$ (R1$`_t`$) $`P_qP_vP_q\zeta=o_{qv}\zeta`$, $`v\ne q`$, $`|t|\le3`$; (R2$`_t`$) $`P_q(P_vP_w+P_wP_v)P_q\zeta=2R_{qvw}\zeta`$, $`q,v,w`$ distinct, $`|t|\le1`$; (R3$`_0`$) $`P_A(P_xP_yP_z+P_zP_yP_x)P_A\xi=2\omega_y\xi`$, $`(x,y,z)`$ an ordering of $`B,C,D`$; $`\zeta=P_qP_t\xi`$, $`t`$ a yes-history, words of length $`\le6`$ from $`p_A`$ [L]. $`\Rightarrow`$ all $`406=\binom{29}2`$ Gram entries $`\langle[w],[w']\rangle`$, $`[w]=P_{w_k}\cdots P_{w_1}\xi`$, $`w,w'\in\mathcal W_{28}`$, are fixed polynomials in the thirteen traces [L, entry by entry; printed walk reduction `lem:cer:reduce` (Lemma 6.6) L, proved separately, not used] $`\Rightarrow`$ each entry $`=\mathcal Q(\hat u(w),\hat u(w'))`$, $`\mathcal Q`$ explicit indefinite comparison form, needs only $`o_{AB}o_{AC}o_{AD}\ne0`$ [L]. Trace relation $`t_1+t_2+t_3=\tfrac12-\tfrac12\sum_{a<b}o_{ab}+\tfrac12(o_{AB}o_{CD}+o_{AC}o_{BD}+o_{AD}o_{BC})+R_{ABC}+R_{ABD}+R_{ACD}+R_{BCD}`$ ($`e_4=0`$ in rank three) [L], used once ($`\tau=0`$) $`\Rightarrow\exists\Xi_B,\Xi_C,\Xi_D\in\mathrm{span}\,\hat u(\mathcal W_{28})`$: $`\mathcal Q(\Xi_x,\Xi_x)=4\hat D\alpha_x(\alpha_x+\mu_x)`$, $`\mathcal Q(\Xi_x,\Xi_y)=-4\hat D\mu m_z`$ $`(\{x,y,z\}=\{B,C,D\})`$, $`\det\bigl[\mathcal Q(\Xi_x/(2\alpha_x),\Xi_y/(2\alpha_y))\bigr]=-4\hat D^3/\prod_x(1-o_{Ax})<0`$, $`\hat D=m^3\mathcal A>0`$ [L, ring identities] $`\Rightarrow e_x=\sum_wc_{x,w}[w]`$ real vectors with that Gram matrix, contradiction [T3]. [P] $`\mathcal Q`$ built on $`\mathrm{Cl}_{0,3}`$ via $`\hat M=\Lambda\Lambda^{\mathsf T}`$ (needs $`\hat M`$ positive definite); Lean presents the same eight-dimensional algebra by structure constants polynomial in the traces. Margin $`\delta>0`$ on a finite yes-first set [L]; seven steps from every state [L].

T4. $`\mathcal A>0\Rightarrow\exists\lambda\in(0,1)`$, atoms $`p^\pm`$ in the standard quaternionic subalgebra, $`o(p^\pm)=o(p)`$, $`R(p^\pm)=R(p)`$, $`t_r(p)=\lambda t_r(p^+)+(1-\lambda)t_r(p^-)`$ [L]; equal $`o,R`$ and this $`t`$-mixture $`\Rightarrow\Pr^{p}_{e/3}(w)=\lambda\Pr^{p^+}_{e/3}(w)+(1-\lambda)\Pr^{p^-}_{e/3}(w)`$ for $`|w|\le6`$ (through length six each term of the expansion has at most one trace factor involving all four atoms, affine in $`t`$) [L] $`\Rightarrow`$ $`\iota_{\mathbb H}(p_i^+)\oplus\iota_{\mathbb H}(p_i^-)`$ on $`\mathbb C^{12}`$, rank-two blocks, state $`\lambda\,\mathrm{Tr}/6\oplus(1-\lambda)\mathrm{Tr}/6`$, matches `wordsUpTo 4 6` from $`e/3`$ [T4].

T5. $`7\in`$ set: T3 at universe $`0`$, `yesFirstUpTo 7` $`\subseteq`$ `wordsUpTo 4 7`. $`L\le6\notin`$ set: T4, $`\mathbb C^{12}`$ in `Type`, `wordsUpTo 4 L` $`\subseteq`$ `wordsUpTo 4 6` $`\Rightarrow`$ least $`L=7`$, real, complex, quaternionic, Hilbert spaces in `Type` [T5].

Synopsis symbols. $`J,\circ,e,\mathrm{tr},U_x`$, atoms, states, words, $`\Pr_\rho`$, representations, algebraic models, gen, special, $`\mathcal A`$, $`o_{ij}`$, $`R_{ijk}`$ are those of [Background in one page](#background-in-one-page); $`\mathsf M`$, $`\mathsf S`$ are `quadrupleM`, `quadrupleS` of [Compared theorems](#compared-theorems) (coordinates in [Challenge](src/Challenge.lean)); $`\omega_r`$ is defined in [Scope of the formal statements](#scope-of-the-formal-statements).

| Symbols | Exact Lean definitions |
|---|---|
| $`o_{ij}`$, $`R_{ijk}`$, $`t_r`$ ($`r=1,2,3`$), $`\omega_r=t_1+t_2+t_3-2t_r`$, $`\mathcal A`$ | `fpOverlap`, `fpTriangle`, `fpDoublePair1`–`fpDoublePair3`, `fpOmega1`–`fpOmega3` ([ThirteenTracesAndAform](src/ThirteenTracesAndAform.lean)); in the Challenge `AlbertChallenge.overlap`, `triangle`, `doublePair` (index $`r-1`$), and `fourPointInvariant` with its `let` bindings `ω1`–`ω3` ([Challenge](src/Challenge.lean)) |
| $`\mathfrak D`$ (the development's algebraic models) and $`\Pr_{\mathfrak D}`$ | `AlgebraicProjectiveData`, `AlgebraicProjectiveData.probability`, `AlgebraicProjectiveData.Matches` ([Interfaces.WordsAndCertificates](src/Interfaces/WordsAndCertificates.lean)); conversions `AlbertChallenge.Bridge.wordOperator_palindrome`, `ofProjectiveRepresentation`, `ofQuaternionicRepresentation`, `ofAlgebraicModel`, `ofFunctional` ([Bridge.Models](src/Bridge/Models.lean)) |
| $`P_t`$ (product of the outcome operators of $`t`$, latest on the left), $`E_v=P_v^*P_v`$; $`\lVert x\Omega\rVert^2=\varphi(x^*x)`$ | `wordAmplitude`, `wordOperator` ([Interfaces.WordsAndCertificates](src/Interfaces/WordsAndCertificates.lean)); `AlgebraicProjectiveData.squareMass` ([ProjectiveWordProbabilities](src/ProjectiveWordProbabilities.lean)) |
| $`z_q(v)`$ and its squared norm | `outcomePurityElement`, `purityResidual_threeHistories` ([PurityResiduals](src/PurityResiduals.lean)) |
| $`i,j,\ell`$; $`[x,y,z]`$ | `AlbertChallenge.octI`, `octJ`, `octL` ([Challenge](src/Challenge.lean)); `octAssociator` ([OctonionGeometry](src/OctonionGeometry.lean)) |
| $`\eta`$, cyclic word space, $`\Omega`$ | `exists_generatedCyclicJordanMap` ([GeneratedCyclicReconstruction](src/GeneratedCyclicReconstruction.lean)), `CyclicWordSpace`, `cyclicVector`, `cyclic_endomorphism_unit_ne_zero` ([CyclicWordQuotient](src/CyclicWordQuotient.lean)), `nativeOrbitSpan_eq_top_of_generates` ([NativeReflectionOrbit](src/NativeReflectionOrbit.lean)) |
| $`\{xyz\}=(x\circ y)\circ z+(z\circ y)\circ x-(x\circ z)\circ y`$, $`Q_{j;klm}=\langle p_j,\{p_kp_lp_m\}\rangle`$; (R1) $`X_aX_bX_a=o_{ab}X_a`$, (R2) $`X_a(X_bX_c+X_cX_b)X_a=2R_{abc}X_a`$, (R3) $`X_a(X_bX_cX_d+X_dX_cX_b)X_a=2Q_{a;bcd}X_a`$ | `jordanTriple`, `nativeCornerQ`, `CornerRelations` (base $`0`$, except the (R2) field `triangle_123` at base $`1`$) ([Interfaces.AlgebraicReconstruction](src/Interfaces/AlgebraicReconstruction.lean)) |
| $`\Delta_j=-\det\mathcal B-\sigma^2`$; $`r=(R_{jkl},R_{jlm},R_{jmk})`$, $`\kappa_1=o_{jk}o_{kl}o_{lj}`$ (cyclically), $`b_{aa}=r_a^2-\kappa_a`$, $`b_{12}=o_{jl}Q_{j;klm}-r_1r_2`$, $`b_{23}=o_{jm}Q_{j;lmk}-r_2r_3`$, $`b_{13}=o_{jk}Q_{j;mkl}-r_3r_1`$, $`\sigma=o_{jk}o_{jl}o_{jm}R_{klm}-r_1r_2r_3-r_1b_{23}-r_2b_{13}-r_3b_{12}`$ | `tetrahedronDiscriminant` (base $`j=0`$) ([Interfaces.AlgebraicReconstruction](src/Interfaces/AlgebraicReconstruction.lean)); $`\Delta_jX_j=0`$: `tetrahedronEngine` ([TetrahedronEngine](src/TetrahedronEngine.lean)); $`\Delta_A(\mathsf S)`$: `fixedS_discriminant`, `fixedS_cornerRelations` ([FixedSBinding](src/FixedSBinding.lean)) |
| $`A^+`$: $`A`$ with $`x\circ y=\tfrac12(xy+yx)`$; $`\eta:J\to A^+`$ Jordan; $`\eta=0`$; $`E_{11},E_{22},E_{33}`$ | `IsJordanHom` ([Defs](src/Defs.lean)); `albertJordanHom_eq_zero` ([AlbertExceptionality](src/AlbertExceptionality.lean)); `diagAtom` ([DiagPeirceAnchor](src/DiagPeirceAnchor.lean)); propagation `jordanHom_eq_zero_of_diagAtom0` ([NativePeircePropagation](src/NativePeircePropagation.lean)) |
| $`\mathcal M_n`$, $`\Pr_\nu(w)`$; finite set $`F`$ | `AdmissibleProjectionMoments`, `projectionMomentDomain`, `momentWordProbability`, `UniformMomentSeparator` ([Interfaces.SeparationAndConverse](src/Interfaces/SeparationAndConverse.lean)); `noMomentMatch_generating_atoms`, `uniformMomentSeparator_generating_atoms` ([AlbertUniformSeparation](src/AlbertUniformSeparation.lean)); `uniformMomentSeparator_of_compact_noMatch` ([CompactMomentSeparation](src/CompactMomentSeparation.lean)) |
| normal form $`(v_A,\dots,v_D)`$; quaternionic subalgebra; $`\mathbb Rq\oplus J_0(q)`$ (line subalgebra); $`\iota_{\mathbb H}:H_3(\mathbb H)\to H_6(\mathbb C)`$, $`\mathrm{Aut}(J)`$ | `sparseFourConfigOct`, `sparseFourConfigOct_fourPointInvariant`, `sparseFourConfig_fourPointInvariant`, `fourPointInvariant_automorphism_invariant` ([ThirteenTracesAndAform](src/ThirteenTracesAndAform.lean)), `lemma_A_normal_general`, `fourPointInvariant_eq_zero_iff` ([ThreeAtomAndFourPoint](src/ThreeAtomAndFourPoint.lean)); `NativeAlbertAutomorphism` ([Interfaces.Geometry](src/Interfaces/Geometry.lean)); Harvey–Lawson `harvey_lawson_132` ([OctonionGeometry](src/OctonionGeometry.lean)); `lineSubalgebra`, `lem_five_sub`, `lineCliffordEmbed`, `symplecticQuatEmbed`, `proper_iff_special` ([SubalgebraCoordsAndLine](src/SubalgebraCoordsAndLine.lean)); `QuaternionicWindow`, `QuaternionicWindow.finrank_eq` ([FrameSlotNormalizers](src/FrameSlotNormalizers.lean)) |
| $`\sigma`$-representation on $`\mathbb C^d`$ | `AlbertChallenge.Bridge.matrixRepresentation` ([Bridge.Matrix](src/Bridge/Matrix.lean)), `matrix_data_of_proper` ([Bridge.Criterion](src/Bridge/Criterion.lean)) |
| (H), $`\xi`$, $`[w]`$, $`\mathcal W_{28}`$, Gram table | `LengthSeven.WalkForm`, `LengthSeven.WalkForm.pathVec` ([LengthSeven.WalkForm](src/LengthSeven/WalkForm.lean)); `LengthSeven.word28` ([LengthSeven.Basic](src/LengthSeven/Basic.lean)); `LengthSeven.LemmaA.gram28` ([LengthSeven.LemmaA.Table](src/LengthSeven/LemmaA/Table.lean)), `LengthSeven.LemmaA.lemmaA` ([LengthSeven.LemmaA.Main](src/LengthSeven/LemmaA/Main.lean)) |
| $`\mathcal Q`$, $`\hat u(w)`$, $`\Xi_x`$; $`m_x=1/o_{Ax}`$, $`\mu_x=m_x-1`$, $`m=m_Bm_Cm_D`$, $`\mu=\mu_B\mu_C\mu_D`$, $`\alpha_x=\mu/\mu_x`$, $`\hat D`$, $`\tau`$ | `LemmaB.Q`, `LemmaB.uhat` ([LemmaB.Model](src/LemmaB/Model.lean)), `LemmaB.Xi` ([LemmaB.Sources](src/LemmaB/Sources.lean)), `LemmaB.Params.mB`, `μB`, `m`, `μ`, `αB`, `Dhat`, `tau` ([LemmaB.Algebra](src/LemmaB/Algebra.lean)), `LemmaB.Traces.toParams`, `TraceRelation`, `Dhat_toParams`, `tau_eq_zero`, `det_gram_normalised_traces` ([LemmaB.Traces](src/LemmaB/Traces.lean)); entry identity `LengthSeven.TableModel.tableModel` ([TableModel.Main](src/TableModel/Main.lean)) |
| $`p^\pm`$, $`\lambda`$; $`\iota_{\mathbb H}`$ blocks; $`\mathbb C^{12}`$ model | `MatchingModels.prop_cer_quatpair_c` ([MatchingModels.QuatPair](src/MatchingModels/QuatPair.lean)), `MatchingModels.nativeWordProbability_e3_affine_le_six` ([MatchingModels.UniversalSixAffinity](src/MatchingModels/UniversalSixAffinity.lean)), `MatchingModels.quatProj6`, `MatchingModels.c12BlockMixtureModel` ([MatchingModels.MatrixClassIBridge](src/MatchingModels/MatrixClassIBridge.lean)), `MatchingModels.prop_cer_universalsix_witness` ([MatchingModels.UniversalSix](src/MatchingModels/UniversalSix.lean)) |

Names follow the convention of the [theorem map](docs/THEOREM-MAP.md): prefix `AlbertSequential` omitted except for names beginning with `AlbertChallenge` or `LemmaB`; within a cell a name without a dot after a dotted one has the same prefix.

## Status of every numbered statement

Each numbered statement of the two papers (theorems, propositions, lemmas, corollaries, definitions,
remarks and examples, with the numbers printed in versions 1 and 2) has one status, the opening
words of its margin note in version 2. *Formalized*: a Lean declaration proves the printed statement.
*Formalized, stronger*: the Lean statement has weaker hypotheses or a stronger conclusion, which the
row names. *Formalized, different route*: the Lean statement is the printed one and the formal proof
departs from the printed proof, as the row says. *Formalized in part*: Lean proves the parts named.
The last column is the text of the margin note. Declarations are named as in the notes, by their
last components, as many as identify them uniquely in `src/` (most full names begin with
`AlbertSequential`); `idealTest_iff_projection` names one declaration in each of three namespaces, as
its row says. [docs/DECLARATIONS.tsv](docs/DECLARATIONS.tsv) gives the full name and module of each.
A note also names a restriction of the setting where there is one, such as Hilbert spaces in `Type`,
the lowest universe of Lean's type theory. Unnumbered results that are compared (theorems 5, 8, 10
and 12) are described above; other unnumbered results are in [docs/THEOREM-MAP.md](docs/THEOREM-MAP.md)
and in [docs/UNNUMBERED-CORE.md](docs/UNNUMBERED-CORE.md) and [docs/UNNUMBERED-LATE.md](docs/UNNUMBERED-LATE.md).

Core paper (96 numbered statements):

| No. | Label | Status | Lean declarations and scope |
|---|---|---|---|
| Lem 3.1 | `lem:set:support` | Formalized | `quadraticSupport_of_canonicalTrace_pairing_zero`. |
| Def 3.2 | `def:ideal` | Formalized | `PositiveInstruments.IsIdealTest`; the same two face conditions and sharpness on real, complex and quaternionic signed trace-class operators are in the three instrument namespaces of `HilbertTrace`. |
| Thm 3.3 | `thm:ideal` | Formalized | `PositiveInstruments.idealTest_iff_quadraticRepresentation`; `idealTest_iff_projection` in each of the real, complex and quaternionic instrument namespaces gives the projection, both updates and the measured effect. |
| Def 3.4 | `def:idealmodel` | Formalized | `HilbertProjectiveData` (ℝ, ℂ), `QuaternionicProjectiveData`; the proofs use the wider class `AlgebraicProjectiveData`. |
| Rem 3.5 | `rem:set:hidden` | Formalized | `FixedUnitary.exists_projective_of_fixedUnitary` (ℂ); `real_projective_of_fixedUnitary_jordanTable`, `quaternionic_projective_of_fixedUnitary_jordanTable` (ℝ, ℍ). The representation keeps the dimension. |
| Def 3.6 | `def:memorymodel` | Formalized | `IsNormalizedFiniteCPModel`, `RealFiniteKrausModel`. |
| Thm 4.1 | `thm:bridgeJ` | Formalized | `printed_albert_criterion`, `proper_iff_hasClassIModel`, `nativeOperatorSpecial_iff_proper`; the last two sentences: `Bridge.no_classI_of_generates`, `AlbertChallenge.linear_separator_of_generates`. |
| Rem 4.2 | `rem:bri:assoc` | Formalized | `native_chronological_composition`. |
| Lem 4.3 | `lem:bri:gns` | Formalized | `cyclicHilbertModel`, `cyclicHilbertModel_probability`, starting from an algebraic model. |
| Lem 4.4 | `lem:bri:null` | Formalized | `cyclic_null_on_histories`, `cyclic_null_operator_of_matches`. |
| Lem 4.5 | `lem:purity` | Formalized | `cyclic_generatedPurity_null_history`, `cyclic_generatedPurity_zero_operator`. |
| Lem 4.6 | `lem:bri:lift` | Formalized | `hasSequentialEffectLift_orbit_corner`, `hasSequentialEffectLift_reflection`. |
| Lem 4.7 | `lem:bri:orbit` | Formalized | `generatedMenu_reflection_span`. |
| Prop 4.8 | `prop:bri:eta` | Formalized | `generated_cyclicHilbertJordanMap`. |
| Lem 4.9 | `lem:bri:state` | Formalized | `explicit_state_all_words`, `explicit_state_subalgebra_words`. |
| Def 4.10 | `def:bri:minimal` | Formalized | `IsBPrimitiveTest`; the sufficient conditions below: `isBPrimitiveTest_of_ambient`, `isBPrimitiveTest_of_rank_le_three`. |
| Thm 4.11 | `thm:bridge` | Formalized | `exists_projectiveRepresentation_iff_zeroAlbertWeights_of_BPrimitive_native`, on the generated algebra; (a) without B-primitivity: `exists_projectiveRepresentation_of_zeroAlbertWeights_in_generatedMenu_native`; (b) over ℝ, ℂ and ℍ: `no_hilbertModel_of_BPrimitiveMenu_albertWeight`, `no_quaternionicModel_of_BPrimitiveMenu_albertWeight`. The classification of the simple summands is proved in Lean. |
| Rem 4.12 | `rem:mixture` | Formalized | The example: `TwoAlbert.paired_albert_mixture`; failure of the purity relations: `TwoAlbert.pair_compression_not_scalar`. The question it poses is open. |
| Cor 4.13 | `cor:four` | Formalized | (i)–(iii): `special_iff_all_tables_and_four_tables_native`, for complex Hilbert spaces in Lean's lowest universe; `projectiveTables_field_equivalence` gives the same tables over ℝ and ℍ. Two and three tests: `exists_projectiveRepresentation_of_at_most_three_native`. |
| Prop 4.14 | `prop:field` | Formalized | `projectiveTables_field_equivalence`; `spinFactorTableUnion_ssubset_finiteComplex_three`, `canonicalProjectiveTables_iff_special_native`, for complex Hilbert spaces in Lean's lowest universe. |
| Rem 4.15 | `rem:bri:foil` | Formalized | `finiteJordanTables_eq_convexHull`, `finiteJordan_linear_inequality_iff`, for algebras and Hilbert spaces in Lean's lowest universe. |
| Cor 4.16 | `cor:bri:finite` | Formalized | (a) `AlbertChallenge.linear_separator_of_generates`; (b) `uniformHilbertSeparator_exceptionalWeight`, `exceptionalWeight_no_uniform_margin`, with the summands supplied by `exists_complete_exceptional_ideal_family`. |
| Prop 5.1 | `prop:three` | Formalized, different route | `complexTripleContract_holds`: the normalizing automorphisms are constructed in the development, without the facts on F₄ used in the printed proof. With only the space ℂ³ recorded: `AlbertChallenge.three_atoms`. |
| Def 5.2 | `def:traces` | Formalized | `fpOverlap`, `fpTriangle`, `fpDoublePair1`, `fpOmega1` and their analogues. |
| Prop 5.3 | `prop:fp:tracerel` | Formalized | `canonical_fourPrimitive_trace_relation`. |
| Rem 5.4 | `rem:fp:tracerel-rank` | Formalized | (a) `fourAtom_trace_ideal_principal`; (b) `complex_dyad_trace_relation_excess`; (c) `rankFour_trace_relation_counterexample_complex`, and for representations matching the words of length at most four, `matching_four_words_trace_relation`. |
| Thm 5.5 | `thm:fourpoint` | Formalized | `thm_fourpoint`; the strict signs in (iv): `lemma_A_normal_nondegenerate`. Parts (i) and (iii): `AlbertChallenge.fourPoint_criterion`. |
| Prop 5.6 | `prop:windowdet` | Formalized | `prop_windowdet`, `prop_windowdet_zero`, for any complex subalgebra containing the three atoms; that it is the one they generate: `lemma_A_window_generated`. |
| Cor 5.7 | `cor:fp:rank` | Formalized | `cor_fp_rank`. |
| Lem 5.8 | `lem:fp:access` | Formalized | `cyclic_native_corner_relations`. |
| Thm 5.9 | `thm:tetra` | Formalized, stronger | `hilbert_tetrahedronNormalized_eq_zero`, `hilbert_fpTetraDtet_eq_zero`. The P_x need only be idempotent, not self-adjoint, and (R2) at the base k is used only for the pair l,m. |
| Prop 5.10 | `prop:Dacal` | Formalized | `prop_Dacal_poly`; `tetrahedronDiscriminant_eq_overlap_mul_fourPointInvariant` is a variant normalised at one vertex. |
| Cor 5.11 | `cor:fp:noideal` | Formalized | `LengthSeven.Uniform.noideal_algebraic`, `LengthSeven.Uniform.noideal_hilbert`, `LengthSeven.Uniform.noideal_rightQuaternionic`, from every state; also `FiveTest.cor_fp_noideal`. |
| Prop 5.12 | `prop:max` | Formalized | `prop_max`, `maximizerConfig_traces`, `fourPointInvariant_maximizerConfig`. The bound and the value at the maximiser: `AlbertChallenge.quadrupleM_spec`. |
| Lem 5.13 | `lem:fp:DeltaWmax` | Formalized | `lem_fp_DeltaWmax`. |
| Cor 5.14 | `cor:fp:maxmixed` | Formalized | `cor_fp_maxmixed`. |
| Thm 6.1 | `thm:cer:uniform` | Formalized, different route | `AlbertChallenge.seven_steps_exclude`, `AlbertChallenge.Bridge.least_separating_length_all_universes`, `uniformSevenMargin_physical_minima`, `uniformSevenMargin_physical_witness`. After Lemma 6.5 the formal proof takes the route of Appendix G. |
| Prop 6.2 | `prop:cer:universalsix` | Formalized | `MatchingModels.prop_cer_universalsix_witness`, `MatchingModels.prop_cer_universalsix_c12`, `AlbertChallenge.Bridge.least_separating_length_all_universes`. |
| Cor 6.3 | `cor:cer:everystate` | Formalized | `BlockB.cor_cer_everystate`, `BlockB.everystate_lengthSeven_algebraic` and its Hilbert and quaternionic versions. |
| Lem 6.4 | `lem:cer:recon` | Formalized, different route | `finiteGram_iff_finiteRealModel`, `AlgebraicProjectiveData.finiteGram`: necessity is proved from the positive functional of an algebraic model, not through the cyclic representation. |
| Lem 6.5 | `lem:cer:short` | Formalized | `LengthSeven.WalkForm.shortRules_of_table`; from e/3: `LengthSeven.lengthSeven_e3_rules`. |
| Lem 6.6 | `lem:cer:reduce` | Formalized | `LengthSeven.algebraicWalk_L_eq_upsilon`, `LengthSeven.algebraicWalk_gram_eq_upsilon`, for any symmetric bilinear form on a real vector space. |
| Lem 6.7 | `lem:cer:tablemodel` | Formalized | `LengthSeven.TableModel.tableModel`, `comparisonMatrix_native_normalization`, `native_comparison_gram_factor`, `cliffordGramFactorEquiv_generator`. |
| Lem 6.8 | `lem:cer:gram28` | Formalized | `native_gram_eq_comparison_of_gram28Hyp`. |
| Lem 6.9 | `lem:cer:negative` | Formalized, different route | `LemmaB.gram_Xi`, `LemmaB.Xi_mem_span_uhat`, `LemmaB.no_psd_realisation_traces`: the Gram entries are checked as a ring identity modulo the trace relation. |
| Thm 6.10 | `thm:cer:seven` | Formalized, different route | `BlockB.seven_M_e3_algebraic`, `BlockB.seven_S_e3_algebraic`, `BlockB.seven_M_pA_algebraic`, `BlockB.seven_S_pA_algebraic` and the Hilbert and quaternionic versions: the squared norms of the vectors Φ are evaluated from the Gram entries of Lemma 6.8, not from Lemma C.1. |
| Prop 6.11 | `prop:horizon` | Formalized | `MatchingModels.horizon_M_matrix`, `MatchingModels.horizon_S_matrix`, `MatchingModels.horizon_M_matrix_roundTrip_excess`, `MatchingModels.horizon_S_matrix_roundTrip_excess`. |
| Rem 6.12 | `rem:cer:variance` | Formalized | `printedPhi_form`, `printedPhi_variance_decomposition`, `printedPhiAffine_omegas`; the value 788/729: `printedPhiValue_M_partner`. |
| Prop 6.13 | `prop:cer:schedule` | Formalized | (a) `MatchingModels.prop_cer_schedule_a`; the consequence, `prop_cer_schedule_a_two_schedules`, needs only that the list excludes the representations on ℂ¹². (b) `MatchingModels.prop_cer_schedule_b`. |
| Rem 6.14 | `rem:cer:tracial` | Formalized | `cyclic_anchoredSeven_e3_not_match_of_faithful_or_tracial`; the model of Proposition 6.11 fails at length seven: `LengthSeven.horizonC12Model_fails_anchoredSeven`. |
| Thm 6.15 | `thm:eleven` | Formalized | `BlockB.thm_eleven_with_overlaps`, `ledger_mem_iff_deposited`, `BlockB.ledgerApplications_occurrences`. Table 1 counts each application with its multiplicity. |
| Prop 6.16 | `prop:Dfails` | Formalized | `MatchingModels.dfails_length_le_two`, `MatchingModels.dfails_thirteen_traces`, `MatchingModels.dfails_tetra_dtet`, `MatchingModels.dfails_purity_defect`, `MatchingModels.dfails_length_three_deviations`. |
| Prop 6.17 | `prop:cer:noequality` | Formalized | (a) `classIEquality_iff_freeProductZero`, `classIEquality_iff_finiteRealVectorStates`; (b) `freeWordCombination_zero_readout`, `wordTable_extraOne`, `wordTable_extraTwo`, `basicWordEqualities_do_not_imply_extraOne_at`, `basicWordEqualities_do_not_imply_extraTwo_at`; (c) `projectiveViolation_iff_freeWordSpanKernel`, `exists_projectiveViolation_of_freeWordSpan_eq_univ`; (d) `classIEquality_native_le_six`. FJ_n is a quotient of Jordan terms. |
| Rem 6.18 | `rem:cer:fivestep` | Formalized, stronger | `HorizonFive.horizonFive_projectiveEquality`, assuming only that c vanishes on real finite-dimensional representations with vector states; the form with E(c)=0: `HorizonFive.horizonFiveClause`. |
| Prop 6.19 | `prop:robust` | Formalized | `FiniteRealWordFunctional.positive_witness_margin_forces_some_word`, `positive_witness_margin_perturbed_word`. |
| Prop 6.20 | `prop:cer:nearideal` | Formalized | `ComplexInstrument.exists_roundedTraceInstrument`, `RealInstrument.exists_roundedTraceInstrument`, `QuaternionicInstrument.exists_roundedTraceInstrument` (the rounded projections and τ); `RoundedTraceInstrument.branch_error`, `RoundedTraceInstrument.word_error`, `RoundedTraceInstrument.witness_bound` (the bounds); `complex_roundedTraceInstrument_word`, `real_roundedTraceInstrument_word`, `quaternionic_roundedTraceInstrument_word` (the rounded model). |
| Prop 6.21 | `prop:cer:sharpdisturb` | Formalized, stronger | `real_sharp_effects_disturb`, `complex_sharp_effects_disturb`, `quaternionic_sharp_effects_disturb`. The gap δ₀ is assumed only for representations on the same Hilbert space. |
| Rem 6.22 | `rem:cer:sharpdisturb` | Formalized | `complex_certain_disturbed_not_mem_preparationHull`, `real_certain_disturbed_not_mem_preparationHull`, `quaternionic_certain_disturbed_not_mem_preparationHull`. |
| Lem 7.1 | `lem:five:coord` | Formalized | `lem_five_coord`, `lem_five_coord_gen`, with subalgebras of H₃(K) taken inside J. |
| Thm 7.2 | `thm:pentad` | Formalized | (i)–(iii): `pentadF_isAtom`, `pentadF_generatesAlbert`, `pentadDrop_generated_finrank`; (a) `thm_pentad_a`; (b) `LengthSeven.Uniform.pentad_b_algebraic`, `FiveTest.thm_pentad_b`. |
| Lem 7.3 | `lem:five:helly` | Formalized | `lem_five_helly`. |
| Prop 7.4 | `prop:arity` | Formalized | `prop_arity`. |
| Cor 7.5 | `cor:helly` | Formalized | `cor_helly_geometric`, `Bridge.physical_helly`; five cannot be lowered: `pentadF_generatesAlbert`, `pentadDrop_generated_finrank`. |
| Thm 8.1 | `thm:cp69` | Formalized | `NativeAnalysis.exists_nativeGeneral_real_simulation`; the dimension 17n+1: `NativeAnalysis.nativeTaggedBlock_card`. |
| Cor 8.2 | `cor:ins:nohalf` | Formalized | `NativeAnalysis.exists_nativeNoHalf_real_simulation`; 68 for four tests: `NativeAnalysis.exists_nativeFourIdempotent_mixed_instrument_68`. |
| Rem 8.3 | `rem:ins:notideal` | Formalized | `NativeAnalysis.exists_nativeGeneral_nonprojective_simulation`; the spectrum on a Peirce block: `nativeCornerYesEffect_charpoly`. |
| Prop 8.4 | `prop:ins:lower` | Formalized | `native_CP_dimension_at_least_six`; the upper bound 68: `NativeAnalysis.exists_nativeFourIdempotent_mixed_instrument_68`. |
| Lem 8.5 | `lem:ins:factor` | Formalized | `exists_displayed_completelyPositive_channel_factorization`. |
| Prop 8.6 | `prop:ins:sharpdilation` | Formalized | `exists_completelyPositive_same_choice_sharpDilation`. |
| Cor 8.7 | `cor:ins:sharpalbert` | Formalized | `NativeAnalysis.exists_nativeSharp_instrument_2_17n_add_one`, `NativeAnalysis.exists_nativeNoHalf_sharp_instrument_34n`. |
| Rem 8.8 | `rem:ins:sharpnotideal` | Formalized | For the instruments of Corollary 8.7: `nativeGeneral_sharp_initialRail_disturbance`. For every realization with sharp effects: `complex_sharp_simulator_ideality_failure`, `real_sharp_simulator_ideality_failure`, `quaternionic_sharp_simulator_ideality_failure`. |
| Ex 8.9 | `ex:ins:twopress` | Formalized | `nativeM_sharp_two_presses` gives the certain state, the probabilities 1 and 1/3, and that the state is not reachable. That P_A and P_B coincide on the plane spanned by ι\|P_C⟩ and ι'\|P_C⟩ is not stated separately. |
| Prop 8.10 | `prop:markov` | Formalized | `frameClassicalWordProbability_eq`, `frameMemory_card`; the comparison with ℂ³: `mutuallyUnbiasedFrames_qutrit_word_statistics`. |
| Lem A.1 | `lem:A:slots` | Formalized | `cyclicSlot_product`, `cyclicSlot_extract`, `cyclicSlot_coefficientSubalgebra`. |
| Lem A.2 | `lem:A:restrict` | Formalized | `complexRestrictionContract_holds`. |
| Lem A.3 | `lem:A:three` | Formalized, different route | `lemma_A_three`: automorphisms constructed in the development instead of the facts on F₄. |
| Lem A.4 | `lem:A:normal` | Formalized, different route | `lemma_A_normal`, `lemma_A_normal_nondegenerate`: automorphisms constructed in the development instead of the facts on F₄. |
| Lem A.5 | `lem:A:Aform` | Formalized | `sparseFourConfigOct_fourPointInvariant`, `sparseFourConfigOct_signedGram`, `NormalFormPolynomial.normalFormPolynomial_eq`. |
| Lem A.6 | `lem:A:degenerate` | Formalized | `lemma_A_degenerate`. |
| Lem A.7 | `lem:A:zero` | Formalized | `lemma_A_zero_quaternionic_normal_form`, `lemma_A_zero_of_factor`, `lemma_A_zero_of_quat`. |
| Lem A.8 | `lem:A:generate` | Formalized | `lemma_A_generate_three`, `lemma_A_generate_four`. |
| Lem A.9 | `lem:A:window` | Formalized | `paperWindowTriangle_a`, `paperWindowTriangle_b`, `paperWindowTriangle_c`. |
| Lem A.10 | `lem:A:clifford` | Formalized | `localUnit_volume_eq_half_reverse`, `localUnit_volume_square`, in an algebra with a local unit, which contains the unital case. |
| Ex B.1 | `ex:set:c3` | Formalized | `UnsharpQutrit.not_projective_luders`, `UnsharpQutrit.certainty_face`, `UnsharpQutrit.repeatable`, `UnsharpQutrit.middle_distinguishes`. |
| Lem B.2 | `lem:bri:rank` | Formalized | `quadraticImage_primitive_ray_and_traceSq`. |
| Lem C.1 | `lem:cer:gram7` | Formalized | `LengthSeven.printedGram_of_H`. |
| Prop C.2 | `prop:cer:quatpair` | Formalized | `MatchingModels.prop_cer_quatpair_a`, `MatchingModels.prop_cer_quatpair_b`, `MatchingModels.prop_cer_quatpair_c_line`; the mixture on ℂ¹²: `MatchingModels.prop_cer_universalsix_witness`. |
| Lem E.1 | `lem:five:sub` | Formalized | `lem_five_sub`. |
| Lem E.2 | `lem:fiv:facts` | Formalized | `lem_fiv_facts_a`, `lem_fiv_facts_b`. |
| Lem E.3 | `lem:five:line` | Formalized | `lem_five_line`. |
| Def F.1 | (no label) | Formalized | `CornerRelations`. |
| Lem F.2 | `lem:tet:corner` | Formalized | `SubalgebraCorner.map_quad`, `atom_corner_relations`. |
| Thm F.3 | `thm:tetra:algebraic` | Formalized | `tetrahedronEngine`, with a possibly nonunital target. |
| Cor F.4 | `cor:tet:special` | Formalized | `tetrahedron_subalgebra_obstruction`. |
| Thm F.5 | `thm:tet:albert` | Formalized, different route | `albertJordanHom_eq_zero`: the unit is reached by Peirce propagation from S instead of the cubic equation. |
| Thm F.6 | `thm:glennie` | Formalized | `AppF.existsUnique_nativePsiCoefficient`, `AppF.thm_glennie_normSq`, `AppF.thm_glennie_perm`, `AppF.thm_glennie_eq_zero_iff`. |

Companion paper (30 numbered statements):

| No. | Label | Status | Lean declarations and scope |
|---|---|---|---|
| Lem 2.1 | `lem:cer:finite` | Formalized | `CornerHolonomy.finiteVectorTetrahedron`. |
| Thm 2.2 | `thm:eleven` | Formalized | `BlockB.thm_eleven_with_overlaps`, `ledger_mem_iff_deposited`, `BlockB.ledgerApplications_occurrences`. Table 1 counts each application with its multiplicity. |
| Lem 2.3 | `lem:cer:sound` | Formalized | `ReflectionCertificate.sound_on_hilbert_model`, `sound_on_quaternionic_model`. |
| Thm 2.4 | `thm:cer:sevenrobust` | Formalized | For M: `BlockB.robustFunctionalM_support`, `robustFunctionalM_rational`, `robustFunctionalM_nonneg_hilbert`, `robustFunctionalM_nonneg_quaternionic`, `robustFunctionalM_eval_e3`, `robustFunctionalM_coefficientNorm_le_paper`; for S `robustFunctionalS_support`, `robustFunctionalS_rational`, `robustFunctionalS_nonneg_hilbert`, `robustFunctionalS_nonneg_quaternionic`, `robustFunctionalS_eval_e3`, `robustFunctionalS_coefficientNorm_le_paper`. The coefficients are those of the released records (`robust_coefficient_recorded_formula`; Appendix A.2). |
| Prop 2.5 | `prop:robust:sqrt` | Formalized | `real_square_root_instrument_witness_bound`, `complex_square_root_instrument_witness_bound`, `quaternionic_square_root_instrument_witness_bound`. |
| Prop 2.6 | `prop:cer:Seleven` | Formalized | `fixedSPrintedWitness_native_le`, `fixedSPrinted_occurrence_has_ledger_application`. |
| Prop 2.7 | `prop:cer:leftmult` | Formalized | `LeftModelNormalForm.literalFirstDeviation`; the splitting for arbitrary coefficient vectors: `leftModelLiteralWeightedModel`. |
| Prop 3.1 | `prop:eq:five` | Formalized, stronger | `HorizonFive.horizonFive_projectiveEquality`, assuming only that c vanishes on real finite-dimensional representations with vector states; the form with E(c)=0: `HorizonFive.horizonFiveClause`. |
| Prop 3.2 | `prop:so:kernel` | Formalized | (a) `AppF.red1_jordan`, `red1_injective`; (b) `AppF.E2_jordanHom_kills_K`; (c) `redq_jordan`, `redq_unit`, `redq_eq_zero_iff`. The dimensions 18 of K, 63 of E₂ and 45 of E₂/K: `AppF.secondOrderKernel_finrank`, `secondOrderNeighborhood_finrank`, `secondOrderQuotient_finrank`; E₂ is not special: `AppF.E2_not_special`. |
| Cor 3.3 | `cor:so:residual` | Formalized | `AppF.cor_so_residual`, `AppF.cor_so_residual_of_atoms`, `cor_so_residual_linearFunctional`; a C² version with remainder o(t²): `cor_so_residual_littleO_of_atoms`. |
| Lem 4.1 | `lem:five:reflect` | Formalized | `signedReflectionTransfer_probability`, `signedReflectionTransfer_hilbert`, `signedReflectionTransfer_quaternionic`. |
| Thm 4.2 | `thm:five:refl` | Formalized, different route | `FiveTest.thm_five_refl`, `FiveTest.reflectedFiveTestFunctional_native`. The explicit vector is checked through its Gram entries. |
| Prop 4.3 | `prop:five:short` | Formalized | (a) `FiveTest.five_short_p0`, `FiveTest.five_short_e3`; (b) `Ends.five_short_b_exists`. The value δ_F>9×10⁻²¹ derived below: `FiveTest.reflectedFiveTest_robust_hilbert`, `FiveTest.reflectedFiveTest_robust_quaternionic`, `reflectedFiveTestMargin_gt`. |
| Cor 4.4 | `cor:five:minimum` | Formalized | `MatchingModels.classI_minimum_F_p0`, `MatchingModels.classI_minimum_F_e3`. |
| Cor 4.5 | `cor:five:depth` | Formalized | `FiveTest.reflectionDepth_no_hilbertModel`, `FiveTest.reflectionDepth_no_quaternionicModel`. The Lean list consists of all words up to the stated length, so it is longer than the list of the proof and serves every state. |
| Rem 4.6 | `rem:five:orbit` | Formalized | `menuReflectionSubgroup_eq_wordRange`, `positive_quad_finite_depth_of_dense_subgroup`. The questions it poses are open. |
| Prop 4.7 | `cor:c:hellyquat` | Formalized | `paperLineHellySix_controls_iso`. |
| Cor 4.8 | `cor:c:hellysix` | Formalized | `quaternionicHelly_six_iso`, `quaternionicHelly_isLeast`; the representation on ℂ⁶, with rank-two projections: `quaternionicHelly_projective`. |
| Prop 5.1 | `prop:windowlaw` | Formalized | V=J: `albert_complexWindow_probability_law_of_invariant`, with the invariant measure from `existsUnique_invariantAlbertAtomProbability`; V≅ H₃(ℂ), H₃(ℍ): `complexAmbientWindow_probability_law_of_iso`, `quaternionicAmbientWindow_probability_law_of_iso`. The eigenvalue density: `projectedAlbertAtom_orderedEigenvalueLaw_eq_density`. |
| Rem 5.2 | `rem:fp:metric` | Formalized | `quadrangle_projective_transitive`, `quadrangleLocus_dense`, `continuous_projective_four_point_invariant_constant`; a cubic-norm-preserving map that changes 𝒜: `rescaled_maximalMenu_invariant_lt`. |
| Rem 5.3 | `rem:fp:invariants` | Formalized in part | The properties of Φ: `signedThreeInvariant_swap`, `signedThreeInvariant_scale`, `signedThreeInvariant_generates_of_ne_zero`, `signedThreeInvariant_zero_of_atom`, `cyclicTrace_signedThree_zero`. The 29 traces are invariant: `adjoin_nativeIltyakovTraces_le`. The cited results on generators, relations, degree bounds, the invariant field and integrality are not formalized. |
| Prop 6.1 | `prop:ins:reachable` | Formalized | `native_reachable_sharpness`, `native_reachable_certainty_ideality`; all assertions together, including positivity on the cone and the trace-preserving sum: `nativeReachableIdealityObligations`. |
| Prop 6.2 | `prop:ins:compactness` | Formalized | `stationaryKraus_global_iff_local_finite_menus`; the error bound for realizations of the finite menu: `stationaryKraus_finite_menu_error_gap`; both in Kraus form. |
| Lem 6.3 | `lem:ins:repair` | Formalized | `binaryKraus_repeatability_repair`; the hypothesis holds for octonionic tables by `binaryKraus_noSwitch_of_native`. |
| Prop 6.4 | `prop:c:sharpdim` | Formalized | `exists_optimalSharpDilation`; the converse: `simultaneousCornerProjections_iff`. |
| Cor 6.5 | `cor:c:sharp26` | Formalized | `exists_nativeSharp_instrument_26n_sub_seven`. |
| Cor 6.6 | `cor:c:sharpnohalf` | Formalized | `exists_nativeNoHalf_sharp_instrument_26n_sub_nine`; from e/3 with four tests: `exists_nativeFour_mixed_sharp_instrument_95`. |
| Lem A.1 | `lem:cer:h5:refl` | Formalized | (a) `HorizonFive.reflectionClassConsistency`; (b) `HorizonFive.reflectionContraction`. |
| Lem A.2 | `lem:cer:h5:lift` | Formalized | `HorizonFive.recognitionThroughFivePos`. |
| Lem A.3 | `lem:cer:h5:seven` | Formalized | `HorizonFive.transferThroughSeven`. |

## Corrections in version 2 of the papers

Version 2 of each paper corrects the following passages of version 1; its changelog lists the same
items. The declarations named prove the corrected statements. [docs/CORRECTIONS.md](docs/CORRECTIONS.md)
gives the computations and examples.

Core paper:

| Passage | Version 1 | Version 2 | Lean |
|---|---|---|---|
| Section 5.4, paragraph "Holonomies at a vertex" | the double-pair traces are the real parts of Bargmann invariants of four pure states | each double-pair trace is the mean of two such invariants, and the combinations `ω_r` of Definition 5.2 are single ones; no statement or proof used the sentence | `Bargmann.doublePairTrace_dyads`, `Bargmann.omega_dyads`; for finite-rank projections on a complex Hilbert space `Bargmann.Hilbert.doubleTrace_eq`, `Bargmann.Hilbert.omega_eq` |
| Section 2, paragraph "The tetrahedron" | `𝒟 = 0` in every representation | `𝒟 = 0` under the hypotheses of Theorem 5.9, the relations and `P_j ≠ 0`; without them the representation of Proposition 6.16 has `𝒟 > 0` | `hilbert_fpTetraDtet_eq_zero`; `MatchingModels.dfails_tetra_dtet` |
| Appendix B.11, proof of Corollary 4.16 | the set of states whose largest exceptional weight is at least `ε` is not convex when `m ≥ 2` | for some `ε` it is convex; it need not be convex; the proof uses the total exceptional weight and is unchanged | `convex_twoSummandWeightStates_max_iff`, `convex_totalWeightCut` |

Companion paper:

| Passage | Version 1 | Version 2 | Lean |
|---|---|---|---|
| Section 2.5, after Proposition 2.7 | `L_i, L_j, L_{e₃'}` are the anticommuting matrices `C₁, C₂, C₃` of the model of core Proposition 6.16, and `𝒱` becomes `1 ⊗ σ_x` | in the coordinates used they act as `−C₁, −C₂, −C₃`, and `𝒱` as `−1 ⊗ σ_x`; the deviation `4/243` is unchanged | `NativeAnalysis.fixedS_positive_i_incompatible`, `NativeAnalysis.fixedSLeftProjections_intertwine`, `NativeAnalysis.fixedSLeftProbability_eq_dfails` |
| Section 4.3 | the bound `\|u\| + ν(u) ≤ 10`, stated without saying which words `u` | the bound is stated for the continuation `u` after the initial "yes" on `A`, as the proof uses it | `FiveTest.reflectedRobustTailTerms_wordBudget`, `FiveTest.reflectedAnchoredTerms_horizon` |
| Section 4.6 | the ordinary cohomology of the full simplex with constant coefficients vanishes | it vanishes in positive degrees | `fullSimplex_positiveCocycle_iff_coboundary`, `fullSimplex_zeroCocycle_iff_constant` |
| Proof of Corollary 6.5 | eigenvalues `0` and `1 − o_ij`, eight times each | when `o_ij = 1` they coincide and `0` has multiplicity sixteen; the rank bound is unchanged | `NativeAnalysis.nativeCornerYesEffect_charpoly`, `NativeAnalysis.nativeCornerYesEffect_charpoly_of_eq` |
| Appendix A.2 | a rule for the final `q` in the left words of defect vectors | the rule differed from the coefficient records of Theorem 2.4 at 936 of the 7,962 residual occurrences of each configuration; the text now refers to the records, whose totals are the printed ones; Theorem 2.4 is unchanged | `LengthSeven.Robust.robust_coefficient_recorded_formula` (module `PaperRobustSourceCorrespondence`) |
| Appendix A.4 | the 1,673 applications were called distinct | they are counted with repetition, and 1,118 of them are distinct | `BlockB.ledgerApplications_occurrences`, `BlockB.ledgerApplications_distinct_card` |

## How it was verified

Given trust in the Lean kernel and in the checking tools, the twelve compared theorems hold as stated
in `Challenge.lean`, and every other declaration holds as stated in its source file. No tool can
check that a statement means what its English description says; where a description and the Lean
statement differ, the Lean statement is what was proved.

Three checks of different strength apply.

The build. `lake build` builds the default targets of `lakefile.toml`: the library
`AlbertSequentialMeasurements`, whose globs cover every module under `src/` other than `Challenge`
and `Solution`, and those two modules. Building a module elaborates each declaration and has the
Lean kernel check its proof, so every declaration of `src/` named in this README, in the papers or
in `docs/` is kernel-checked by the build.

The axiom audit. After the build, `tools/audit_project_axioms.py` imports, in batches of sixteen,
every module under `src/` that git tracks at `HEAD`, except `Challenge`. For each constant that a
module exports (theorems, definitions, instances and auxiliary declarations alike) it collects the
axioms the constant depends on, recursively, with `Lean.collectAxioms`, and it fails if one of them
is not in the list `permitted_axioms` of `comparator.json`: `propext`, `Classical.choice`,
`Quot.sound`. With `--negative-control` it audits `Challenge` instead and must fail on `sorryAx`.
The audit says nothing about what the statements mean, and it does not cover the files in
`tools/checks`.

Comparator. For the twelve theorems named in `comparator.json`, Comparator, the tool Palomar uses to
check that a solution proves exactly the statements of a challenge, compares the exports of
`Challenge` and `Solution`: it checks that `Solution` proves theorems with exactly the statements of
`Challenge.lean`, over the same definitions, using only the three permitted axioms, and its proofs
are replayed by NanoDa and by the Lean kernel. Only these twelve statements are tied in this way to
a file that imports only Mathlib and defines every object it uses. Every other result is stated in
the development's own terms, whose definitions a reader has to compare with the papers; the margin
notes and the [status ledger](#status-of-every-numbered-statement) name the declarations, and
[docs/STATEMENTS.md](docs/STATEMENTS.md) gives the definitions behind the twelve.

Further checks. The 141 files in `tools/checks` import modules and restate selected declarations
with `example` or query their axioms with `#print axioms`. Python scripts in `tools/` recompute
certificates of the papers in exact rational arithmetic, independently of Lean; three of them read
the TeX sources from the source archive of version 1 of the Hexagon record and check their SHA-256
digests. [docs/REPLAY.md](docs/REPLAY.md) describes each script.

Results for the release commit:

| Check | Result |
|---|---|
| `lake build` (all 966 modules; 9,944 Lake jobs with dependencies) | exit 0 |
| `python3 tools/audit_project_axioms.py` | 38,148 exported declarations in 965 modules, standard axioms only |
| `python3 tools/audit_project_axioms.py --negative-control` | fails on `sorryAx`, as required |
| Comparator with NanoDa, `Challenge` against `Solution` | accepted by NanoDa and by the Lean kernel |
| Comparator with `Challenge` as the solution | rejected (illegal axiom `sorryAx`), as required |
| `lake env lean` on each file of `tools/checks` | 141 of 141 compile |
| exact-arithmetic scripts of [docs/REPLAY.md](docs/REPLAY.md) | all six pass |

Size: `Challenge.lean` has 497 lines (27,975 bytes), above Palomar's advisory threshold of 300 lines
and below its limit of 1,000 lines and 100 KiB; it is unchanged since `v1.0.0`, as are `Solution.lean`
and `comparator.json`. The repository has 966 Lean modules with 232,660 lines; its largest file is
`src/PentadArityAndHelly.lean`, with 7,576 lines.

## Check it yourself

Requirements: Linux or macOS, `elan`, git, about 8 GiB of free memory per Lean process and about
12 GiB of disk space (the Mathlib cache and toolchain take about 10 GiB). The toolchain is pinned in
`lean-toolchain` (`leanprover/lean4:v4.36.0`) and the Mathlib revision in `lake-manifest.json`. A few
modules need up to about 7.3 GiB each (four exceed 7 GiB; the largest is `RobustCert.RobustM`); imports marked `-- build order only` make the
largest of them compile one after another, so that a parallel `lake build` does not run them at the
same time.

```sh
git clone https://github.com/macgregor-sudo/albert-sequential-measurements.git
cd albert-sequential-measurements
git checkout v2.0.0
lake exe cache get                                         # prebuilt Mathlib oleans
lake build                                                 # every module, including Challenge and Solution
python3 tools/audit_project_axioms.py                      # axioms of every exported declaration
python3 tools/audit_project_axioms.py --negative-control   # must fail on sorryAx
python3 -c 'import json; print("import Solution"); [print("#print axioms", n) for n in json.load(open("comparator.json"))["theorem_names"]]' \
  | lake env lean --stdin                                  # axioms of the twelve theorems
```

The last command should print, for each of the twelve theorems, a line of the form

```text
'AlbertChallenge.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To compare statements, `python3 tools/replay_comparator.py <output-directory>` exports `Challenge`
and `Solution` with `leanexport`, runs Comparator on [`comparator.json`](comparator.json) (challenge
module `Challenge`, solution module `Solution`, the twelve theorem names, the three permitted axioms,
NanoDa enabled) and checks that `Solution` is accepted and that `Challenge`, used as its own solution,
is rejected because of `sorryAx`. It needs the `leanexport` and Comparator executables, which are not
dependencies of this repository, to be available to `lake`. The importing checks and the
exact-arithmetic scripts are run as described in [docs/REPLAY.md](docs/REPLAY.md).

## Reading the proof

The development lives in the namespace `AlbertSequential`, except `LemmaB/*` and part of
`TableModel/*` (namespace `LemmaB`), `Glennie/*` (namespace `Glennie`) and
`CompositionAlgebras/*` (namespace `CompositionAlgebra` and others); the names below are module names.
Its Albert-side definitions (`Defs`) are the Challenge's definitions under other names, and the
bridges between the two are definitional up to an identity cast. A tour by layer, bottom up;
[docs/MODULES.md](docs/MODULES.md) groups the modules, and the
[status ledger](#status-of-every-numbered-statement) and [docs/THEOREM-MAP.md](docs/THEOREM-MAP.md)
name declarations.

1. **The Albert algebra.** `Defs` (octonions, `Albert`, `jordanMul`, trace, quadratic map, atoms,
   states), `NativeAlbertLaws`, `NativeJordanIdentity`, `NativeIdempotentClassification`,
   `NativeAutomorphisms`, `FrameSlotNormalizers`, `OctonionGeometry`, and the adapted layer
   `Glennie/*` (compact octonions and Albert algebra, automorphisms, diagonalisation, square cone).
   General Jordan algebras: `RealJordanOperators`, `RealJordanFundamental`, `JordanPowerAssociativity`,
   `UnitalJordanProduct`, `JordanProductQuadratic`, `EuclideanJordanForm`, and the finite-dimensional
   theory behind them (`JordanSpectralResolution`, `JordanPeirceFusion`, `FormalReality*`,
   `EuclideanJordan*`, `JordanIdeal*`, `JordanSimpleIdealDecomposition`); the classification of the
   simple summands of rank three uses the adapted composition algebras (`CompositionAlgebras/*`,
   Hurwitz's theorem) through `HurwitzRankThreeClassification`, and the general criterion of core
   Theorem 4.11 is in `GeneralEJA*`.
2. **Words and models.** `Interfaces.WordsAndCertificates` (`nativeWordProbability`,
   `AlgebraicProjectiveData`), `HilbertProjectiveData`, `QuaternionicProjectiveData`,
   `RightQuaternionicHilbert`, `ChronologicalWords`, `BoundedWordEffects`, and the trace-class
   instruments on Hilbert spaces of any dimension (`HilbertTrace*`).
3. **Reconstruction and the no-go theorem.** A model that reproduces every word yields a Jordan
   homomorphism from the generated subalgebra into operators: `CyclicHilbertModel` and the other
   `Cyclic*` modules, `PositiveFunctionalNull`, `PurityResiduals`, `SequentialEffectLifts`,
   `NativeReflectionOrbit`, `GeneratedCyclicReconstruction`, `AlbertCyclicReconstruction`. No nonzero
   Jordan homomorphism from `J` into an associative algebra exists: `TetrahedronEngine`,
   `AlbertExceptionality`. Assembly: `AlgebraicProjectiveNoGo`; the finite separator:
   `AlgebraicSeparationAssembly`, `CompactMomentSeparation`, `AlbertUniformSeparation`.
4. **Three, four and more atoms.** `ThirteenTracesAndAform`, `ThreeAtomAndFourPoint`,
   `ComplexWindowDeterminantAndMax`, `FixedSBinding`; proper subalgebras and their embeddings into
   complex Hermitian matrices: `SubalgebraCoordsAndLine`, `HermitianStateTransport`,
   `SuppliedEmbeddingStateTransport`.
5. **Length seven.** `LengthSeven/*` (walk interface, Albert-side table values, Lemma A),
   `LemmaB/*` (no positive semidefinite realisation), `TableModel/*` (the entry-by-entry identity),
   `Uniform.Main`, and `MatchingModels/*` (the `ℂ¹²` model and the quaternionic pairs).
6. **Further results.** `Uniform.Corollaries`, `Ends/*`, `BlockA/*`, `BlockB/*`, `AppF/*`,
   `HorizonFive/*`, `RobustCert/*`, `FiveTest/*`, `PentadArityAndHelly`, `Pending.GlennieGeneral`,
   `Robustness/*`, the constructed separators (`Corner*`, `Holonomy*`, `FixedS*`, `Residual*`), the
   instrument modules (`NativeTaggedInitialModels`, `NativeSharpInstrumentSimulation` and their
   imports), the probability law of companion Proposition 5.1 (`WindowProbability*`), the companion
   modules (`Companion*`), and the joins `Joins/*`.
7. **Statement layer.** `Challenge`, `ChallengeDefs`, `Solution`, and the bridge modules `Bridge/*`
   (namespace `AlbertChallenge.Bridge`, except the native form of theorem 12 in `Bridge.Atoms`), among
   them `Bridge.PrintedCriterion`, `Bridge.UniverseCriterion`, `Bridge.UniverseHorizon` and
   `Bridge.PhysicalHelly` for the printed statements in every universe.

## How this was produced

Robert R. MacGregor is the human contributor and the person responsible for the repository. The AI
statement of version 2 of the core paper reads:

> All text, mathematics and proofs herein, and all Lean 4 code apart from the adapted files noted in
> Appendix G, were produced by Claude Fable 5.2, Claude Opus 5.5, GPT-6.2 Astra, GPT-6.2 Sol, Gemini
> Carbon and Gemini Hydrogen, and every numbered statement is machine-checked in Lean (Appendix G).
> Except for this statement, all content herein was generated by AI and has not been understood
> without AI interpretation.

The companion paper's statement is the same except that it refers to the core paper for the adapted
files and reads "every numbered statement except Remark 5.3, which is checked in part, is
machine-checked in Lean (Appendix C)". In this repository "machine-checked" means proved in Lean and checked by the
build and the axiom audit; twelve of the core paper's results are in addition compared by
Comparator.

Three groups of files are adapted from earlier code ([docs/ATTRIBUTION.md](docs/ATTRIBUTION.md)):
the declarations adapted from Physlib in `src/RealJordanFundamental.lean`,
`src/JordanPowerAssociativity.lean` and `src/RealJordanOperators.lean`, written by their upstream
author, who is named there and in the file headers; the fifteen modules under `src/Glennie/`,
adapted from the contributor's earlier Palomar entry PALOMAR-2026-10-16-000013, whose own production
account is recorded in that entry; and the ten modules under `src/CompositionAlgebras/`, adapted from
`ehrlich-b/composition-algebras` (Palomar entry PALOMAR-2026-08-29-000018), whose copyright holder
is named in the file headers.

Review. The code of release `v1.0.0` was written by AI agents and reviewed module by module by an AI
agent other than the writer, except the modules listed for that release in its README. The modules
added for version 2 were written by AI agents and checked by other AI agents; an independent AI
reviewer then compared a sample of 28 printed statements with their Lean statements and searched the
sources for `sorry`, `axiom`, `native_decide` and similar constructs outside `Challenge.lean`. Every
declaration name cited in the margin notes of version 2 resolves to a declaration in `src/`, as
checked by script. No human has reviewed the mathematics, the Lean proofs or the
faithfulness of the statements.

## Relation to earlier formalizations and reused code

The mathematics formalized here is that of the two papers; the formalization is source-based, not
an original presentation. Results that the papers attribute to earlier work, such as the
exceptionality of `H₃(𝕆)` (Albert, 1934), the classification of formally real Jordan algebras
(Jordan, von Neumann and Wigner, 1934), Hurwitz's theorem on composition algebras and Glennie's
identity (1966), are cited there with their sources. The area is the operational study of
Jordan-algebraic state spaces in the foundations of quantum theory, between mathematical physics and
nonassociative algebra. The core paper's section "Related work" describes prior work; the result it
names as nearest is the theorem of Müller and Garner (Theorem 2 of their 2023 paper) that an
unrestricted finite-dimensional generalized probabilistic theory has an exact linear embedding into
finite-dimensional quantum theory exactly when it is a special Euclidean Jordan algebra, which
concerns single-shot probabilities without an update rule, while the criterion here fixes finitely
many tests and compares all sequences under the Lüders update. No derivation of either statement
from the other is established. Novelty has not been established by a literature search recorded
here, and no claim of novelty or priority is made.

Reused code. The fifteen modules under `src/Glennie/` (compact octonions and Albert algebra and their
elementary laws, automorphisms, diagonalisation, square cone) are adapted from the contributor's
earlier Palomar entry PALOMAR-2026-10-16-000013 (`macgregor-sudo/compact-albert-recognition` at commit
`40d3b34`, Apache-2.0). `src/RealJordanFundamental.lean`, `src/JordanPowerAssociativity.lean` and
`src/RealJordanOperators.lean` are adapted from four files of Physlib (`leanprover-community/physlib`
at commit `08a6c1b5`, Apache-2.0) and keep its copyright notice. The ten modules under
`src/CompositionAlgebras/` (composition algebras, the Cayley–Dickson construction, the octonions and
Hurwitz's classification, `CompositionAlgebra.hurwitz_classification`) are adapted from
`ehrlich-b/composition-algebras` at commit `98d4437c` (Palomar entry PALOMAR-2026-08-29-000018,
Apache-2.0) and keep its copyright notice; they serve the classification of the simple summands of
rank three in core Theorem 4.11. Details, with the declarations adapted and the changes made:
[docs/ATTRIBUTION.md](docs/ATTRIBUTION.md) and [THIRD_PARTY_NOTICES](THIRD_PARTY_NOTICES).

Earlier Palomar entries by the same contributor, from which no file is used:
PALOMAR-2026-09-13-000001 (`macgregor-sudo/albert-frame-triple-invariants`, split Albert frame
invariants), an ancestor of code in PALOMAR-2026-10-16-000013, and PALOMAR-2026-10-29-000034
(`macgregor-sudo/tight-39-code`, the tight 39-point code in the octonionic projective plane), which
shares the `Glennie/` ancestry.

Related registered work from which no code is used: sequential products on Hermitian matrix
algebras, `ehrlich-b/sequential-products-lean` (PALOMAR-2026-08-22-000006, the real and complex
classification theorems; PALOMAR-2026-08-21-000009, Albert's power-associativity theorem for
commutative Jordan rings carrying a real-module structure; PALOMAR-2026-08-21-000001, the real case
of Wigner's theorem); Euclidean Jordan algebras, `ehrlich-b/euclidean-jordan`
(PALOMAR-2026-08-23-000005, the Koecher–Alfsen–Shultz theorem; PALOMAR-2026-08-23-000006, spectral
resolution; PALOMAR-2026-08-29-000001, the trace form; PALOMAR-2026-08-29-000008, the Peirce
decomposition relative to a frame); Hurwitz's theorem in dimension form, PALOMAR-2026-08-29-000015,
registered from `ehrlich-b/composition-algebras` at an earlier commit; and Jordan homomorphisms of
associative rings, `stalex444/herstein-jordan-homomorphisms` (PALOMAR-2026-11-11-000008, Herstein's
theorem onto prime rings). The core paper cites the three `ehrlich-b` repositories. This development
proves its own spectral and Peirce results (`JordanSpectralResolution`, `JordanPeirceFusion`), its own
power associativity (adapted from Physlib) and its own octonions for the Albert algebra (`Glennie/`
and the Challenge's Cayley–Dickson definition); its statement that every Jordan homomorphism from `J`
into an associative algebra is zero (`albertJordanHom_eq_zero`) has a non-associative source and
uses no result of the Herstein entry. The core paper also cites a Lean formalization by M. J. Soares
(`markkasaurus/albert-algebra-lean`, Zenodo, doi:10.5281/zenodo.21482444, Apache-2.0; not a Palomar
entry), which proves the Jordan identity of `H₃(𝕆)`, its real dimension 27, Glennie's identity in
symmetrisations of associative algebras and an explicit violation of it in `H₃(𝕆)`. No code of it is
used; this development proves the Jordan identity of its own encoding (`NativeAnalysis.jordan_identity`)
and the vanishing of every Jordan homomorphism from `J` into an associative algebra
(`albertJordanHom_eq_zero`) independently, by another route.

The Challenge of PALOMAR-2026-10-16-000013 also defines the compact octonions and the Albert algebra.
`Challenge.lean` defines them again, because a Challenge may import only Mathlib; it uses the same
Cayley–Dickson convention as `Glennie.octMul`.

## Repository layout

| Path | Contents |
|---|---|
| `README.md` | this file |
| `src/Challenge.lean` | the twelve compared statements and their definitions; Mathlib imports only |
| `src/ChallengeDefs.lean` | the Challenge's definitions, verbatim, for the Solution |
| `src/Solution.lean` | the same statements with proofs, via `src/Bridge/*.lean` |
| `src/Bridge/` | translation between the Challenge's objects and the development's, and the printed statements in every universe |
| `src/CompositionAlgebras/` | the adapted composition-algebra files and their upstream licence text |
| `src/` (other files and directories) | the development, by layer as above; module names are the paths below `src/` |
| `comparator.json` | Comparator configuration |
| `formalization.yaml` | Palomar metadata (v0.4) |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | build configuration and pins |
| `.gitignore` | excludes Lake's build directory `.lake` |
| `.github/workflows/palomar.yml` | manual run of Palomar's verification workflow (`mode: full`) on this commit |
| `tools/audit_project_axioms.py`, `tools/replay_comparator.py` | the axiom audit and the Comparator run |
| `tools/checks/` | Lean files that import modules and check selected declarations |
| `tools/*.py` (others) | exact-arithmetic replays of the papers' certificates ([docs/REPLAY.md](docs/REPLAY.md)) |
| `docs/STATEMENTS.md` | each compared statement, its definitions and the differences from the papers |
| `docs/PROOF-PATH.md` | proof route of each compared theorem and the exact strength of the named steps |
| `docs/THEOREM-MAP.md` | further declarations, with plain meanings, including unnumbered results |
| `docs/MODULES.md` | the modules, grouped by what they prove |
| `docs/DECLARATIONS.tsv` | every declaration named in the margin notes of version 2 of the papers, with its full name and module |
| `docs/UNNUMBERED-CORE.md`, `docs/UNNUMBERED-LATE.md` | unnumbered claims of the papers and their Lean counterparts or status |
| `docs/CORRECTIONS.md` | the corrections of version 2, with computations |
| `docs/HELLY-AND-TRACE.md`, `docs/SCHEDULE-AND-SPIN.md` | scope notes on companion Proposition 4.7 and Corollary 4.8, core Theorem 3.3(b), Proposition 6.13, Proposition 4.14(b) and Theorem 4.11(a) |
| `docs/REPLAY.md` | the further checks and how to run them |
| `docs/ATTRIBUTION.md`, `THIRD_PARTY_NOTICES` | adapted code, its origin and licence |
| `CITATION.cff` | citation metadata |
| `LICENSE` | Apache-2.0 (also the licence of the adapted Physlib and composition-algebra files) |

## Citation and licence

Contributor: Robert R. MacGregor, ORCID [0009-0003-1734-8054](https://orcid.org/0009-0003-1734-8054).

Cite with [`CITATION.cff`](CITATION.cff). The code is licensed Apache-2.0, and adapted files keep
their notices. [Code licence](LICENSE), [attribution](docs/ATTRIBUTION.md).

The two papers are distributed under CC BY 4.0, as stated on their title pages; they are not part of
this repository's tree.
