# On sequential ideal measurements in the exceptional Jordan algebra

A Lean 4 formalization accompanying two papers: "On sequential ideal measurements in the exceptional
Jordan algebra" (the *core paper*) and "Finite certificates for sequential measurements in the
exceptional Jordan algebra" (the *companion paper*). The
core paper is the Hexagon record [hexagon:2611.00620](https://hexagonmath.org/abs/2611.00620), whose source archive
also holds the companion paper's LaTeX source as `companion/macgregor-finite-certificates.tex`. Repository:
https://github.com/macgregor-sudo/albert-sequential-measurements.

The formalization concerns sequences of ideal yes–no measurements on the Albert algebra and whether
a real, complex or quaternionic Hilbert-space model can reproduce their statistics. Twelve theorems
are stated in a file that imports only Mathlib, and Comparator checks that the proofs prove exactly
those statements. The development proves further results, listed with their declarations in the
[theorem map](#theorem-map); [docs/MODULES.md](docs/MODULES.md) locates every module. Every numbered
statement of the two papers is listed with its status (formalized, formalized in a narrower or
different form, or not formalized) under
[Status of every numbered statement](#status-of-every-numbered-statement); the papers also contain
results proved by hand only, which are not formalized here.

Status: frozen research artifact at the commit tagged `v1.0.0`. Not maintained and not accepting
contributions. Lean `v4.36.0`, Mathlib `v4.36.0` (commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`),
unmodified. The Palomar registry entry for this repository records its registration and review.

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
a solution proves exactly the statements of a challenge. Paper results are cited by their LaTeX
label, prefixed "core" or "companion".

**1. No representation for generating atoms** (core `thm:bridgeJ`, no-go sentence; `cor:fp:noideal`).
If finitely many atoms generate `J`, then for every element `ρ` of `J`, a state or not, no
representation of any of the three kinds and no algebraic model, on a carrier in any universe
`Type v`, reproduces their word probabilities on all words.

```lean
theorem no_representation_of_generates {n : ℕ} (p : Fin n → Albert) (hp : ∀ i, IsAtom (p i))
    (hg : Generates p) (ρ : Albert) : NoRepresentationOn.{v} p ρ Set.univ
```

**2. A finite separating inequality** (core `thm:bridgeJ`, last sentence; `cor:bri:finite`(a)). For
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

**3. Seven steps exclude every model** (core `thm:cer:uniform`(a)). For four atoms that generate `J`,
no representation or algebraic model (carriers in `Type v`) reproduces from `e/3` every word of length
at most seven whose first outcome is "yes" on test `0`, and none reproduces from the pure state `p 0`
every word of length at most six.

```lean
theorem seven_steps_exclude (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hg : Generates p) :
    NoRepresentationOn.{v} p maximallyMixed (yesFirstUpTo 7) ∧
      NoRepresentationOn.{v} p (p 0) (wordsUpTo 4 6)
```

**4. Six steps never suffice** (core `prop:cer:universalsix`). For four atoms that generate `J`, some
complex representation on `ℂ¹²` reproduces from `e/3` every word of length at most six.

```lean
theorem six_step_model (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) (hg : Generates p) :
    ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (Fin 12)),
      ∀ w ∈ wordsUpTo 4 6, M.probability w = wordProbability p maximallyMixed w
```

**5. The least separating length is seven** (core: "`L_min = 7`", in `thm:cer:uniform` and
`prop:cer:universalsix`). For four atoms that generate `J`, seven is the least `L` such that no real,
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

**6. The four-point criterion** (core `thm:fourpoint`, parts (i) and (iii)). For any four atoms,
`𝒜 ≥ 0`, and `𝒜 > 0` exactly when they generate `J`.

```lean
theorem fourPoint_criterion (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i)) :
    0 ≤ fourPointInvariant p ∧ (0 < fourPointInvariant p ↔ Generates p)
```

**7. The maximum of `𝒜`** (core `prop:max`, bound and value). The four elements of the explicit
quadruple `M` are atoms, `𝒜(M) = 4/19683`, and `𝒜 ≤ 4/19683` for all four atoms.

```lean
theorem quadrupleM_spec :
    (∀ i, IsAtom (quadrupleM i)) ∧ fourPointInvariant quadrupleM = 4 / 19683 ∧
      ∀ p : Fin 4 → Albert, (∀ i, IsAtom (p i)) → fourPointInvariant p ≤ 4 / 19683
```

**8. The rational quadruple `S`** (core, paragraph on the configurations `M` and `S` in the section on
finite certificates; no label). The four elements of the explicit quadruple `S`, with rational
coordinates, are atoms, and `𝒜(S) = 1/5832`.

```lean
theorem quadrupleS_spec :
    (∀ i, IsAtom (quadrupleS i)) ∧ fourPointInvariant quadrupleS = 1 / 5832
```

**9. Three atoms** (core `prop:three`). Three atoms never generate `J`, and for every state some
complex representation on `ℂ³`, which may depend on the state, reproduces every word.

```lean
theorem three_atoms (p : Fin 3 → Albert) (hp : ∀ i, IsAtom (p i)) :
    ¬ Generates p ∧ ∀ ρ, IsDensity ρ →
      ∃ M : ProjectiveRepresentation 3 ℂ (EuclideanSpace ℂ (Fin 3)),
        ∀ w : Word 3, M.probability w = wordProbability p ρ w
```

**10. Vanishing invariant** (core, the paragraph after `cor:fp:noideal`). If four atoms have `𝒜 = 0`,
then for every state some complex representation on `ℂ⁶`, which may depend on the state, reproduces
every word.

```lean
theorem zero_invariant_model (p : Fin 4 → Albert) (hp : ∀ i, IsAtom (p i))
    (h0 : fourPointInvariant p = 0) :
    ∀ ρ, IsDensity ρ → ∃ M : ProjectiveRepresentation 4 ℂ (EuclideanSpace ℂ (Fin 6)),
      ∀ w : Word 4, M.probability w = wordProbability p ρ w
```

**11. The Albert criterion** (core `thm:bridgeJ`, the equivalence of (1), (2) and (3)). For any finite
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

**12. Atoms are the primitive idempotents** (core, the definition of atoms in the section on the
setting). An element `p` of `J` is an atom (`p ∘ p = p` and `tr p = 1`) if and only if `p ∘ p = p`,
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
`thm:bridgeJ` with its condition (1) read as "the generated subalgebra is not `J`"; that `J` itself
has no nonzero Jordan homomorphism into an associative algebra, which makes the paper's operator form
of speciality equivalent, is `albertJordanHom_eq_zero`, proved but not compared. Theorems 9 and 10 give smaller models for three atoms and for four
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
- `fourPointInvariant` is the polynomial of core equation `eq:A:Acal52`, with
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

Not formalized. Some numbered results of each paper are proved by hand only, and the remarks and
examples are not formalized, except core Remark 6.18, whose statement is proved in Lean; [Status of every numbered statement](#status-of-every-numbered-statement)
lists them all. In the core paper they are Theorem 3.3(b) (ideal tests on Hilbert spaces are Lüders
instruments), Definition 4.10 and Theorem 4.11 (the criterion for general Euclidean Jordan algebras),
Corollary 4.13, Proposition 4.14(b), (c), Corollary 4.16(b), Lemma 6.6 (walk reduction), Proposition
6.13, Proposition 6.17(b), (c), Proposition 6.21 and Lemma B.2, together with the parts named in the
table of the results that are formalized only in a narrower form. In the companion paper they are
Lemmas 2.1 and 6.3, Propositions 2.7, 4.7, 5.1 and 6.4, and Corollaries 4.5, 4.8, 6.5 and 6.6, among
them the quaternionic Helly number (Proposition 4.7, Corollary 4.8) and the smaller sharp dilations
(Proposition 6.4, Corollaries 6.5, 6.6). None of
these is claimed here. The appendices "Formalization" of the two papers (core Appendix G, companion
Appendix C) and the margin notes give the same account.

## Dense proof for AI agents

Tags: [Tn] compared theorem n; [L] Lean-checked, not compared; [H] hand proof only, not formalized; [P] printed route, replaced in Lean by the route stated before it. Labels are core-paper labels. All $`p_i`$ are atoms (`IsAtom`); gen means `Generates`; $`\Pr_\rho(w)`$ is `wordProbability p ρ w`, written $`\Pr^{q}_\rho`$ for another quadruple $`q`$; $`\mathrm{Jord}\langle e,p_i\rangle`$ is the unital subalgebra generated by the $`p_i`$. Four tests: $`A,B,C,D`$ are tests $`0,1,2,3`$; $`t_r`$, $`\omega_r`$ as in the table below and in [Scope of the formal statements](#scope-of-the-formal-statements), $`(\omega_B,\omega_C,\omega_D)=(\omega_1,\omega_2,\omega_3)`$. $`\Pr_{\mathfrak D}(w)=\varphi(Q_1\cdots Q_m\cdots Q_1)`$ is the value a model $`\mathfrak D`$ gives $`w`$.

Models. $`Q_t\in\{P_i,1-P_i\}`$ self-adjoint idempotent $`\Rightarrow Q_1\cdots Q_{m-1}Q_mQ_{m-1}\cdots Q_1=a^*a,\ a=Q_m\cdots Q_1`$; real or complex representation $`\mapsto`$ algebraic model on $`B(H)`$ as real $`*`$-algebra with state $`T\mapsto\operatorname{Re}\varphi(\tfrac12(T+T^*))`$; quaternionic representation $`\mapsto`$ algebraic model on the commutant of the right $`\mathbb H`$-action ($`\mathbb H`$-valued inner product unused); Challenge algebraic model $`\mapsto`$ development algebraic model $`\mathfrak D`$; all word values preserved [L]. Every exclusion below is proved for development algebraic models $`\mathfrak D`$, carriers in any universe.

T12. Idempotent $`q\Rightarrow\mathrm{tr}\,q\in\{0,1,2,3\}`$, $`\mathrm{tr}\,q=0\Leftrightarrow q=0`$; $`q\ne0\Rightarrow\mathrm{tr}\,q\ge1`$, so $`q+r`$ with $`q,r\ne0`$, $`q\circ r=0`$ has trace $`\ge2`$ and is no atom; $`\mathrm{tr}\,p\in\{2,3\}\Rightarrow\exists g\in\mathrm{Aut}(J)`$, $`gp`$ diagonal $`0/1`$ with $`\ge2`$ ones $`\Rightarrow p=q+r`$, $`q,r\ne0`$ idempotent, $`q\circ r=0`$ [T12].

$`\mathsf S`$. Atoms with rational coordinates [T8]; $`o_{AB}=\tfrac12`$, other $`o_{ab}=\tfrac13`$, $`(R_{ABC},R_{ABD},R_{ACD},R_{BCD})=(\tfrac16,\tfrac16,\tfrac19,\tfrac19)`$, $`t_r=\omega_r=\tfrac1{18}`$ [L] $`\Rightarrow\mathcal A(\mathsf S)=\tfrac1{5832}`$ [T8], so $`\mathsf S`$ generates by T6; $`Q_{A;BCD}=Q_{A;CDB}=Q_{A;DBC}=\tfrac1{18}`$, $`\Delta_A(\mathsf S)=\tfrac1{104976}`$ [L].

T1. Purity: $`q`$ atom, $`c=\mathrm{tr}(U_{v_m}\cdots U_{v_1}q)`$, $`z_q(v)=P_qE_vP_q-cP_q`$, $`\check v=(v_{m-1},\dots,v_1)`$: $`\|z_q(v)P_t\Omega\|^2=\Pr_{\mathfrak D}(t,q,v,\check v,q)-2c\Pr_{\mathfrak D}(t,q,v)+c^2\Pr_{\mathfrak D}(t,q)`$ in every model $`\mathfrak D`$, the same combination of $`\Pr_\rho`$ is $`0`$ in $`J`$ by $`U_{U_ab}=U_aU_bU_a`$, $`U_qx=\langle q,x\rangle q`$. Reflections $`U_{2p-e}=2(U_p+U_{e-p})-\mathrm{id}`$, $`\Sigma Y\Sigma=2PYP+2(1-P)Y(1-P)-Y`$ $`(\Sigma=2P-1)`$; reflected-orbit span $`=\mathrm{Jord}\langle e,p_i\rangle`$; transported purity and linear relations vanish on the cyclic word space $`\Rightarrow`$ matching $`\mathfrak D`$ from any $`\rho\in J`$ gives $`\eta:\mathrm{Jord}\langle e,p_i\rangle\to\mathrm{End}`$(cyclic word space), Jordan, $`\eta(e)=1`$ [L, tests atoms of $`J`$]; gen $`\Rightarrow`$ domain $`J`$. Exceptionality [L]: $`\eta:J\to A^+`$, $`A`$ associative real, possibly nonunital; $`X_a=\eta(s_a)`$, $`(s_a)=\mathsf S`$; Jordan maps preserve $`U`$ and $`\{xyz\}\Rightarrow`$ (R1)–(R3) for $`X_a\Rightarrow\Delta_AX_A=0`$ (algebraic tetrahedron identity, no positivity, no $`o_{ab}>0`$) $`\Rightarrow\eta(E_{11})=0`$ $`(s_A=E_{11})`$ $`\Rightarrow`$ Peirce propagation $`\eta(E_{22})=\eta(E_{33})=0\Rightarrow\eta(e)=0\Rightarrow\eta=\eta(e\circ\cdot)=0`$; [P] (R1) at $`b\ne A`$, $`o_{Ab}\ne0\Rightarrow\eta(s_b)=0`$, $`y=\sum_as_a`$, $`y^3-4y^2+\tfrac{23}6y-\tfrac79e=0\Rightarrow\eta(e)=0\Rightarrow\eta=\eta(U_e\,\cdot)=0`$. $`\eta(e)=1\ne0`$ (state $`\varphi(1)=1`$) $`\Rightarrow`$ no matching real, complex or quaternionic representation or algebraic model, any $`n`$, any $`\rho\in J`$, carriers in `Type v` [T1].

T2. $`\mathcal M_n`$ = moment vectors $`\nu`$ on words in $`n`$ letters: $`\nu(\varnothing)=1`$, reversal-invariant, idempotent in context, $`\ge0`$ on polynomial squares, $`|\nu|\le1`$; compact convex; densities of $`J`$ compact convex. $`\Pr_\nu(w)`$: value of the word $`w`$ under $`\nu`$ (polynomial in the moments). T1 at the moment level $`\Rightarrow`$ no $`(\nu,\rho)`$ matches on all words; compactness $`\Rightarrow`$ a finite word set $`F\ni\varnothing`$ on which no $`(\nu,\rho)`$ matches; strict separation of the disjoint compact convex images in $`\mathbb R^F`$ $`\Rightarrow\exists L,(c_w)_{w\in F},\gamma>0`$: $`\sum c_w\Pr_\nu(w)\ge0\ \forall\nu\in\mathcal M_n`$, $`\sum c_w\Pr_\rho(w)\le-\gamma\ \forall`$ states $`\rho`$ [L]; [P] nested closed sets $`\{(\nu,\rho):\text{match for }|w|\le L\}`$, one empty. $`\Rightarrow`$ for each `Type v`: $`\ge0`$ on real, complex, quaternionic representations [T2]; the same $`L,c,\gamma`$ for every universe and for algebraic models [L]. No bound on $`L,\gamma`$.

T6. $`\exists g\in\mathrm{Aut}(J)`$: $`gp_i=v_iv_i^\dagger`$, $`v_A=(1,0,0)`$, $`v_B=(B_0,B_1,0)`$, $`v_C=(C_0,C_1+C_2i,C_3)`$, $`v_D=(D_0,X,Y)`$, $`X=x_0+x_1i+x_2j`$, $`Y=y_0+y_1i+y_2j+y_3ij+y_4\ell`$, $`B_0,B_1,C_0,C_2,C_3,D_0,x_2,y_4\ge0`$; $`\mathcal A`$ is $`\mathrm{Aut}(J)`$-invariant; edge amplitudes $`g_1=B_0C_0+B_1z`$, $`g_2=B_0D_0+B_1X`$, $`g_3=C_0D_0+\bar zX+C_3Y`$, $`z=C_1+C_2i`$, $`u_k=\operatorname{Im}g_k`$; Harvey–Lawson $`\det(\langle u_k,u_l\rangle)-\langle u_1\times u_3,u_2\rangle^2=\tfrac14|[u_1,u_3,u_2]|^2`$ ($`u\times v=\operatorname{Im}(uv)`$, $`[x,y,z]=(xy)z-x(yz)`$), Artin $`\Rightarrow\mathcal A=\tfrac14B_0^2B_1^4C_0^2C_2^2C_3^2D_0^2|[i,X,Y]|^2=B_0^2B_1^4C_0^2C_2^2C_3^2D_0^2x_2^2y_4^2\ge0`$. $`\mathcal A>0\Rightarrow`$ no pair coincident or orthogonal, $`C_2C_3x_2y_4\ne0\Rightarrow`$ gen; $`\mathcal A=0\Rightarrow p_i`$ in one quaternionic subalgebra ($`\cong H_3(\mathbb H)`$, $`\dim15<27`$) $`\Rightarrow`$ (gen $`\Rightarrow\mathcal A>0`$); hence $`\mathcal A\ge0`$, $`\mathcal A>0\Leftrightarrow`$ gen [T6]; $`\mathcal A=0\Leftrightarrow`$ atoms in one quaternionic subalgebra [L].

T7. Normal form, unit vectors: $`B_0^2B_1^4=u(1-u)^2\le\tfrac4{27}`$ $`(u=B_0^2)`$, $`C_0^2C_2^2C_3^2\le\tfrac1{27}`$, $`D_0^2x_2^2y_4^2\le\tfrac1{27}`$ (three nonnegative factors with sum $`\le1`$) $`\Rightarrow\mathcal A\le\tfrac4{3^9}=\tfrac4{19683}`$; $`\mathsf M`$: all $`o=\tfrac13`$, $`R=\tfrac19`$, $`t_r=\tfrac1{27}`$ [L]; atoms, $`\mathcal A(\mathsf M)=\tfrac4{19683}`$, bound for all atoms [T7]; equality exactly on the $`\mathrm{Aut}(J)`$-orbit of $`\mathsf M`$ [L].

T9. $`n=3`$: $`\exists g\in\mathrm{Aut}(J)`$, $`gp_i\in H_3(\mathbb C)\Rightarrow`$ trace-preserving iso $`\psi:W\to H_3(\mathbb C)`$, $`W=g^{-1}H_3(\mathbb C)`$; $`\psi(p_i)`$ rank one; $`\sigma=\psi(\rho_W)`$, $`\rho_W`$ trace-orthogonal projection of $`\rho`$ on $`W`$, density matrix, $`\operatorname{Re}\mathrm{tr}(\sigma Q_1\cdots Q_m\cdots Q_1)=\Pr_\rho(w)\ \forall w`$ [L]; state $`T\mapsto\mathrm{tr}(\sigma T)`$, $`\mathrm{tr}(\sigma X)=\mathrm{tr}(\sqrt\sigma X\sqrt\sigma)\ge0`$ $`\Rightarrow`$ representation on $`\mathbb C^3`$ per state; gen would contradict T1 at $`\rho=p_0`$ [T9].

T10. $`\mathcal A=0\Rightarrow p_i\in`$ quaternionic subalgebra [L] $`\Rightarrow`$ embedding $`\iota_{\mathbb H}:H_3(\mathbb H)\to H_6(\mathbb C)`$, trace form $`\times2`$ $`\Rightarrow`$ fixed rank-two projections on $`\mathbb C^6`$, density matrix per state, every word [L] $`\Rightarrow`$ [T10].

T11. $`\neg`$gen $`\Rightarrow`$ proper unital $`B\ni p_i`$ $`\Rightarrow B\subseteq\mathbb Rq\oplus J_0(q)`$ ($`q`$ atom) or $`B\subseteq`$ quaternionic subalgebra [L] $`\Rightarrow`$ unital Jordan embedding into $`H_{24}(\mathbb C)`$ (trace form $`\times8`$) or $`H_6(\mathbb C)`$ ($`\times2`$) $`\Rightarrow`$ state-independent Hermitian idempotents $`P_i`$, per-state density matrix $`\sigma`$ with $`\operatorname{Re}\mathrm{tr}(\sigma Q_1\cdots Q_m\cdots Q_1)=\Pr_\rho(w)`$ $`\Rightarrow`$ (b), $`d\in\{6,24\}`$, $`M_0`$ from $`\rho=\mathrm{diag}(1,0,0)`$; (b) $`\Rightarrow`$ (c) at that $`\rho`$, carrier in `Type`; (c) $`\Rightarrow\neg`$gen by T1 at universe $`0`$; (a) $`\Leftrightarrow\neg`$gen: unital subalgebra proper $`\Leftrightarrow`$ unital injective Jordan map into $`H_d(\mathbb C)`$, $`d\ge1`$ [L] [T11]. Printed `thm:bridgeJ` (operator-sense speciality, $`d`$ depending on $`\rho`$) follows from T1, T2, T11 and $`\eta:J\to A^+\Rightarrow\eta=0`$ [L] by a short argument that is not a Lean declaration.

T3. $`\mathcal A>0`$ (T6) $`\Rightarrow o_{ab}\in(0,1)`$. Match from $`e/3`$ on `yesFirstUpTo 7` $`\Rightarrow`$ positive semidefinite real form on the cyclic word space, $`\xi=P_A\Omega/\|P_A\Omega\|`$; match from $`p_A`$ on `wordsUpTo 4 6` $`\Rightarrow\xi=\Omega`$ ($`\Pr_{\mathfrak D}(A)=1`$); either $`\Rightarrow`$ (H): $`P_A\xi=\xi`$, $`\|P_u\xi\|^2=3\Pr_{e/3}(A,u)=\Pr_{p_A}(u)`$, $`|u|\le6`$. (H) $`\Rightarrow`$ (R1$`_t`$) $`P_qP_vP_q\zeta=o_{qv}\zeta`$, $`v\ne q`$, $`|t|\le3`$; (R2$`_t`$) $`P_q(P_vP_w+P_wP_v)P_q\zeta=2R_{qvw}\zeta`$, $`q,v,w`$ distinct, $`|t|\le1`$; (R3$`_0`$) $`P_A(P_xP_yP_z+P_zP_yP_x)P_A\xi=2\omega_y\xi`$, $`(x,y,z)`$ an ordering of $`B,C,D`$; $`\zeta=P_qP_t\xi`$, $`t`$ a yes-history, words of length $`\le6`$ from $`p_A`$ [L]. $`\Rightarrow`$ all $`406=\binom{29}2`$ Gram entries $`\langle[w],[w']\rangle`$, $`[w]=P_{w_k}\cdots P_{w_1}\xi`$, $`w,w'\in\mathcal W_{28}`$, are fixed polynomials in the thirteen traces [L, entry by entry; printed walk reduction `lem:cer:reduce` H, not used] $`\Rightarrow`$ each entry $`=\mathcal Q(\hat u(w),\hat u(w'))`$, $`\mathcal Q`$ explicit indefinite comparison form, needs only $`o_{AB}o_{AC}o_{AD}\ne0`$ [L]. Trace relation $`t_1+t_2+t_3=\tfrac12-\tfrac12\sum_{a<b}o_{ab}+\tfrac12(o_{AB}o_{CD}+o_{AC}o_{BD}+o_{AD}o_{BC})+R_{ABC}+R_{ABD}+R_{ACD}+R_{BCD}`$ ($`e_4=0`$ in rank three) [L], used once ($`\tau=0`$) $`\Rightarrow\exists\Xi_B,\Xi_C,\Xi_D\in\mathrm{span}\,\hat u(\mathcal W_{28})`$: $`\mathcal Q(\Xi_x,\Xi_x)=4\hat D\alpha_x(\alpha_x+\mu_x)`$, $`\mathcal Q(\Xi_x,\Xi_y)=-4\hat D\mu m_z`$ $`(\{x,y,z\}=\{B,C,D\})`$, $`\det\bigl[\mathcal Q(\Xi_x/(2\alpha_x),\Xi_y/(2\alpha_y))\bigr]=-4\hat D^3/\prod_x(1-o_{Ax})<0`$, $`\hat D=m^3\mathcal A>0`$ [L, ring identities] $`\Rightarrow e_x=\sum_wc_{x,w}[w]`$ real vectors with that Gram matrix, contradiction [T3]. [P] $`\mathcal Q`$ built on $`\mathrm{Cl}_{0,3}`$ via $`\hat M=\Lambda\Lambda^{\mathsf T}`$ (needs $`\hat M`$ positive definite); Lean presents the same eight-dimensional algebra by structure constants polynomial in the traces. Margin $`\delta>0`$ on a finite yes-first set [L]; seven steps from every state [L].

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

Names follow the convention of the [theorem map](#theorem-map): prefix `AlbertSequential` omitted except for names beginning with `AlbertChallenge` or `LemmaB`; within a cell a name without a dot after a dotted one has the same prefix.

## Theorem map

Every substantial result proved in the repository, with its plain meaning, paper label, Lean
declaration and module. Declarations are named without the prefix `AlbertSequential`, except those
beginning with `AlbertChallenge` (the compared theorems and the bridge layer) and `LemmaB` or
`Glennie`, which are top-level namespaces. Within a cell, a name without a dot after a dotted one has
the same prefix. "Yes" in the last column means the result is one of the twelve theorems compared
with `Challenge.lean`; "no" means it is proved here and checked by Lean but not compared. Where the
Lean statement is narrower than the printed one, the meaning says how. [docs/STATEMENTS.md](docs/STATEMENTS.md)
repeats the map with the remaining gaps.

| Result | Paper | Lean declaration(s) | Module | Compared |
|---|---|---|---|---|
| No model of any kind reproduces generating atoms, from any `ρ` | core `thm:bridgeJ`, `cor:fp:noideal` | `AlbertChallenge.no_representation_of_generates` | `Solution` | yes |
| A finite separating inequality for generating atoms | core `thm:bridgeJ`, `cor:bri:finite`(a) | `AlbertChallenge.linear_separator_of_generates` | `Solution` | yes |
| Seven steps exclude every model from `e/3` (yes-first words), six from `p_A` | core `thm:cer:uniform`(a) | `AlbertChallenge.seven_steps_exclude` | `Solution` | yes |
| A model on `ℂ¹²` reproduces every word of length at most six from `e/3` | core `prop:cer:universalsix` | `AlbertChallenge.six_step_model` | `Solution` | yes |
| `L_min = 7` (Hilbert spaces in `Type`, Lean's lowest universe) | core `thm:cer:uniform`, `prop:cer:universalsix` | `AlbertChallenge.least_separating_length` | `Solution` | yes |
| `𝒜 ≥ 0`, and `𝒜 > 0` exactly for generating quadruples | core `thm:fourpoint`(i),(iii) | `AlbertChallenge.fourPoint_criterion` | `Solution` | yes |
| `𝒜 ≤ 4/19683`, attained at `M` | core `prop:max` | `AlbertChallenge.quadrupleM_spec` | `Solution` | yes |
| `S` consists of atoms and `𝒜(S) = 1/5832` | core, configuration `S` | `AlbertChallenge.quadrupleS_spec` | `Solution` | yes |
| Three atoms do not generate `J` and are reproduced on `ℂ³` from every state | core `prop:three` | `AlbertChallenge.three_atoms` | `Solution` | yes |
| Four atoms with `𝒜 = 0` are reproduced on `ℂ⁶` from every state | core, paragraph after `cor:fp:noideal` | `AlbertChallenge.zero_invariant_model` | `Solution` | yes |
| For any finite family of atoms, not generating `J` is equivalent to lying in a special subalgebra, to one family of projections on `ℂ⁶` or `ℂ²⁴` serving every state with density-operator states, and to a representation or algebraic model in `Type` from one state | core `thm:bridgeJ`, (1)–(3) | `AlbertChallenge.albert_criterion` | `Solution` | yes |
| The atoms are exactly the primitive idempotents | core, definition of atoms | `AlbertChallenge.isAtom_iff_primitive` | `Solution` | yes |
| The same criterion in the development's terms: a proper subalgebra containing the atoms, fixed Hermitian idempotent `d × d` matrices (`d ∈ {6, 24}`) and a density matrix for each state | core `thm:bridgeJ` | `Bridge.albert_criterion_bridge`, `Bridge.matrix_data_of_proper`, `Bridge.exists_proper_native_of_not_generates` | `Bridge.Criterion` | no |
| Atoms are the primitive idempotents, native form; a nonzero idempotent has trace at least one, and an idempotent of trace at least two splits into two nonzero orthogonal idempotents | core, definition of atoms | `NativeAnalysis.isAtom_iff_primitive`, `NativeAnalysis.one_le_trace_of_idempotent`, `NativeAnalysis.exists_orthogonal_split` | `Bridge.Atoms` | no |
| Ideal tests, finite positive forms | core `def:ideal` | `PositiveInstruments.IsIdealTest` | `IdealTestFoundations` | no |
| An ideal test is the Lüders map `U_p`, for finite positive forms (part (b) not formalized) | core `thm:ideal`(a) | `PositiveInstruments.idealTest_iff_quadraticRepresentation` | `IdealJordanInstruments` | no |
| Support of a positive element with zero pairing, in `J` (the printed lemma is for any `V`) | core `lem:set:support` (narrower) | `native_positive_zero_pairing_support` | `NativeSupport` | no |
| The development's model classes (Hilbert, quaternionic, algebraic) | core `def:idealmodel` | `HilbertProjectiveData`, `QuaternionicProjectiveData`, `AlgebraicProjectiveData` | `HilbertProjectiveData`, `QuaternionicProjectiveData`, `Interfaces.WordsAndCertificates` | no |
| Finite completely positive memory models | core `def:memorymodel` | `IsNormalizedFiniteCPModel`, `RealFiniteKrausModel` | `Interfaces.InstrumentsAndCompactness`, `RealFiniteKrausModel` | no |
| The no-go half of the criterion, per model class | core `thm:bridgeJ` | `algebraicProjective_not_matches_generating_atoms`, `HilbertModelSeparation.hilbert_not_matches_generating_atoms`, `HilbertModelSeparation.rightQuaternionic_not_matches_generating_atoms` | `AlgebraicProjectiveNoGo`, `HilbertModelSeparation` | no |
| One finite functional, `≥ 0` on all real, complex and quaternionic models, `≤ −γ` on `J` from every state | core `cor:bri:finite`(a) | `HilbertModelSeparation.uniformHilbertSeparator_generating_atoms` | `HilbertModelSeparation` | no |
| Cyclic (GNS-type) real Hilbert model of a matching algebraic model | core `lem:bri:gns` | `cyclicHilbertModel`, `cyclicHilbertModel_probability` | `CyclicHilbertModel` | no |
| Null vectors on all histories: the null set of a positive functional is a left ideal, and the step to word vectors (the moment step of the printed lemma is not part of this declaration) | core `lem:bri:null` (narrower) | `allHistoryNullContract` | `PositiveFunctionalNull` | no |
| Purity: the three-history residual identity; its vanishing in `J` for an outcome that is an atom of `J` | core `lem:purity` (narrower) | `purityResidual_threeHistories`, `NativeAnalysis.native_corner_long_probability` | `PurityResiduals`, `NativeWordPurity` | no |
| Lifts of conjugated effects | core `lem:bri:lift` | `hasSequentialEffectLift_orbit_corner`, `hasSequentialEffectLift_reflection` | `SequentialEffectLifts` | no |
| The reflection-orbit span is the generated subalgebra, for tests that are atoms of `J` | core `lem:bri:orbit` (narrower) | `nativeOrbitSpan_iff_generated` | `NativeReflectionOrbit` | no |
| A matching model yields a Jordan homomorphism on the generated subalgebra | core `prop:bri:eta` | `exists_generatedCyclicJordanMap` | `GeneratedCyclicReconstruction` | no |
| Transport of a state along a supplied embedding | core `lem:bri:state` | `FaithfulHermitianJordanEmbedding.exists_unique_positive_trace_representative`, `suppliedEmbeddingStateTransport` | `HermitianStateTransport`, `SuppliedEmbeddingStateTransport` | no |
| Real, complex and quaternionic representations give the same tables, also in finite dimension: each inclusion by a construction that keeps every word probability (the equalities of classes are not stated as such; parts (b), (c) are not formalized) | core `prop:field`(a) | `HilbertProjectiveData.complexExtensionModel_probability`, `HilbertProjectiveData.quaternionExtensionModel_probability`, `cyclicHilbertModel_probability`, `HilbertProjectiveData.cyclicHilbert_finite`, `QuaternionicProjectiveData.cyclicHilbert_finite_of_real`, `complexification_finiteDimensional`, `quaternionification_finiteDimensional`, `RightQuaternionicHilbertStructure.finiteDimensional_opposite_iff_real` | `ComplexProjectiveExtension`, `QuaternionicProjectiveExtension`, `CyclicHilbertModel`, `CyclicFiniteDimension`, `FieldExtensionFiniteDimension` | no |
| The development's two presentations of a quaternionic Hilbert space (operator structure, right `ℍ`-module with `ℍ`-valued inner product) are equivalent | none (supporting) | `rightQuaternionicHilbertPresentationEquiv` | `QuaternionicPresentationEquivalence` | no |
| Three atoms lie in a copy of `H₃(ℂ)` and are reproduced by rank-one projections on `ℂ³` | core `prop:three` | `complexTripleContract_holds` | `ThreeAtomAndFourPoint` | no |
| Four atoms with `𝒜 = 0`: rank-two projections on `ℂ⁶`, fixed for all states | core, paragraph after `cor:fp:noideal` | `fourPoint_zero_c6_representation` | `ThreeAtomAndFourPoint` | no |
| Any number of atoms such that every subfamily of at most five lies in a proper subalgebra: fixed Hermitian idempotent complex `d × d` matrices, `d ∈ {6, 24}`, reproduce every word from every state with a density matrix | core `thm:bridgeJ`, `cor:helly` | `cor_helly_operational_if`, `generatesAlbert_iff_generatedSubalgebra_eq_top` | `PentadArityAndHelly`, `SubalgebraCoordsAndLine` | no |
| The thirteen traces | core `def:traces` | `fpOverlap`, `fpTriangle`, `fpDoublePair1`, `fpOmega1` and their companions | `ThirteenTracesAndAform` | no |
| The trace relation of four atoms (rank-three model and `J`) | core `prop:fp:tracerel` (narrower) | `rankThree_fourIdempotent_trace_relation`, `albert_fourAtom_trace_relation` | `ThirteenTracesAndAform` | no |
| Four-point theorem (i)–(iv): `𝒜 = 0` exactly when the atoms lie in a copy of `H₃(ℍ)`; normal form; `𝒜` as squared coordinates times the squared norm of an octonion associator | core `thm:fourpoint` | `thm_fourpoint`, `lemma_A_normal_nondegenerate` | `ThreeAtomAndFourPoint` | no |
| `𝒜` as a determinant in a complex subalgebra; rank trichotomy | core `prop:windowdet`, `cor:fp:rank` | `prop_windowdet`, `prop_windowdet_zero`, `cor_fp_rank` | `ComplexWindowDeterminantAndMax` | no |
| Triangle and triple defects as purity residuals | core `lem:fp:access` (narrower) | `triangleDefect_primitive_decomposition`, `symmetricTripleDefect_primitive_decomposition` | `PrimitivePurityDecomposition` | no |
| Tetrahedron identity, algebraic form, possibly nonunital target | core `thm:tetra` (algebraic form), `thm:tetra:algebraic` | `tetrahedronEngine` | `TetrahedronEngine` | no |
| The tetrahedron statistic `𝒟` (Lean `fpTetraDtet`) times the product of the six transition probabilities equals `𝒜`, for positive transition probabilities; Lean's `tetrahedronDiscriminant` equals `𝒜` times the three transition probabilities at `p_0` | core `prop:Dacal` | `prop_Dacal_poly`, `tetrahedronDiscriminant_eq_overlap_mul_fourPointInvariant` | `ThirteenTracesAndAform` | no |
| No ideal model for generating quadruples, any state of `J` | core `cor:fp:noideal` | `LengthSeven.Uniform.noideal_algebraic`, `noideal_hilbert`, `noideal_rightQuaternionic`; `FiveTest.cor_fp_noideal` | `Uniform.Corollaries`, `FiveTest.Compose` | no |
| Maximum of `𝒜`, maximiser unique up to automorphism; traces at `M` | core `prop:max` | `prop_max`, `maximizerConfig_traces`, `fourPointInvariant_maximizerConfig` | `ComplexWindowDeterminantAndMax` | no |
| Bound on the triangle factor | core `lem:fp:DeltaWmax` | `lem_fp_DeltaWmax` | `ComplexWindowDeterminantAndMax` | no |
| At a maximiser each atom gives every word in the other three its probability from `e/3` | core `cor:fp:maxmixed` | `cor_fp_maxmixed` | `ComplexWindowDeterminantAndMax` | no |
| Deterministic identity behind the law of a pure state seen in a complex subalgebra (the law itself is not formalized) | companion `prop:windowlaw` | `complexWindow_laplace_integrand` | `ComplexWindowDeterminantAndMax` | no |
| Margin: a finite set of yes-first words of length at most seven and `δ > 0` such that every model misses the Albert value from `e/3` by at least `δ` on one of them; the same from `p_A` at length six | core `thm:cer:uniform`(b); the `p_A` form is not printed | `Ends.uniform_b`, `uniform_b_algebraic`, `uniform_b_pA` | `Ends.UniformB` | no |
| `L_min = 7` stated through separation predicates, Hilbert spaces in `Type` | core `thm:cer:uniform` | `MatchingModels.lMin_eq_seven` | `MatchingModels.LMinSeven` | no |
| The six-step model is a mixture of two quaternionic quadruples on `ℂ¹²`; real, quaternionic and algebraic versions; no linear equality, and no linear inequality, valid on all models and supported on words of length at most six is violated from `e/3` | core `prop:cer:universalsix`, `prop:cer:quatpair`, `prop:cer:noequality`(d); the inequality form is not printed | `MatchingModels.prop_cer_universalsix_witness`, `prop_cer_universalsix_c12`, `prop_cer_quatpair_a`, `prop_cer_quatpair_b`, `prop_cer_quatpair_c_line`, `no_classI_linearEq_le_six`, `no_classI_linearIneq_le_six` | `MatchingModels.UniversalSix`, `MatchingModels.QuatPair` | no |
| From every state, length seven excludes every model; from `e/3`, length six does not | core `cor:cer:everystate` | `BlockB.cor_cer_everystate`, `BlockB.everystate_lengthSeven_algebraic` | `BlockB.EveryState` | no |
| Finite Gram table exactly when a finite real model exists | core `lem:cer:recon` | `finiteGram_iff_finiteRealModel`, `AlgebraicProjectiveData.finiteGram` | `FiniteGramEquivalence`, `AlgebraicGramNecessity` | no |
| Relations at short histories, from the table | core `lem:cer:short` | `LengthSeven.WalkForm.shortRules_of_table`, `LengthSeven.lengthSeven_e3_rules` | `LengthSeven.ShortRules`, `LengthSeven.TableValues` | no |
| The 406 Gram entries of the 28 path vectors are fixed by words of length at most seven | core `lem:cer:gram28`, `lem:cer:gram7` (narrower) | `LengthSeven.LemmaA.lemmaA`, `lemmaA_of_gram28Hyp` | `LengthSeven.LemmaA.Main` | no |
| Those entries equal the comparison form's, entry by entry | core `lem:cer:tablemodel` (narrower) | `LengthSeven.TableModel.tableModel`, `tableModel_lemmaB` | `TableModel.Main` | no |
| Three vectors with negative Gram determinant: no positive semidefinite realisation | core `lem:cer:negative` | `LemmaB.gram_Xi`, `LemmaB.Xi_mem_span_uhat`, `LemmaB.no_psd_realisation_traces` | `LemmaB.Gram`, `LemmaB.Lemma`, `LemmaB.Conclusion` | no |
| Exact length-seven certificates for `M` and `S` | core `thm:cer:seven` | `BlockB.seven_M_e3_algebraic`, `seven_S_e3_algebraic`, `seven_M_pA_algebraic`, `seven_S_pA_algebraic`; `BlockB.isTracesM_maximizerConfig`, `isTracesS_fixedS` | `BlockB.RobustNativeMS` | no |
| `ℂ¹²` model through length six | core `prop:horizon` (narrower: not the equal mixture of `Q₊`, `Q₋`) | `MatchingModels.prop_cer_universalsix_c12` | `MatchingModels.UniversalSix` | no |
| A list of 2,041 words of length at most eleven and its four relabelled copies (8,164 words) exclude every model, from `e/3` and from every state; one functional on them; for `𝒜 > 0` all six transition probabilities lie in `(0, 1)` | core and companion `thm:eleven` | `BlockB.thm_eleven_with_overlaps`, `BlockB.thm_eleven_full`, `Ends.Eleven.elevenBase_card`, `elevenBase_hist`, `BlockB.elevenUnion_card`, `BlockB.elevenLedgerWords_eq_elevenBase`, `MatchingModels.overlap_pos_lt_one_of_fourPoint_pos` | `Joins.Eleven`, `BlockB.ElevenTheorem`, `BlockB.ElevenSupport`, `Ends.Eleven` | no |
| For `S`: an explicit word functional supported on words of length at most eleven, nonnegative on every algebraic model and at most `−7/828` on the Albert table from every state, and the table error it forces | companion `prop:cer:Seleven` | `fixedSConstructedWitness`, `fixedSConstructedWitness_model_nonnegative`, `fixedSConstructedWitness_horizon`, `fixedSConstructedWitness_native_le`, `fixedSConstructedWitness_forces_error` | `FixedSConstructedWitness` | no |
| A tetrahedron statistic `𝒟 > 0` is not a witness | core `prop:Dfails` | `MatchingModels.dfails_length_le_two`, `dfails_thirteen_traces`, `dfails_tetra_dtet`, `dfails_purity_defect`, `dfails_length_three_deviations` | `MatchingModels.DfailsModel` | no |
| Six characterisations of a projective equality: vanishing on finite-dimensional real representations with vector states (Lean's definition), on real matrix projections, in the free product `ℝ[ℤ₂^{*n}]`, in the universal algebra of `n` projections, on special idempotents, and on every algebraic model in `Type`; Hilbert-space representations enter through the algebraic models they induce | core `prop:cer:noequality`(a) | `AppF.prop_cer_noequality_a`, `AppF.IsProjectiveEquality` | `BlockA.SecondOrderResidual` | no |
| No equality through five steps: for any four atoms and any state, every combination of words of length at most five that vanishes on all real finite-dimensional representations with vector states vanishes on `J`; the same with the hypothesis `E(c) = 0` in the group algebra `ℝ[ℤ₂^{*4}]` (the universal algebra of four projections) | core `rem:cer:fivestep`, companion `prop:eq:five` | `HorizonFive.horizonFive_projectiveEquality`, `HorizonFive.horizonFiveClause` | `Joins.NoEquality`, `HorizonFive.Final` | no |
| Products of two reflections; recognition through length five; transfer through degree seven (the form with `n = 0`, which is false, is refuted by `HorizonFive.not_recognitionThroughFive`) | companion `lem:cer:h5:refl`, `lem:cer:h5:lift`, `lem:cer:h5:seven` | `HorizonFive.reflectionClassConsistency`, `reflectionContraction`, `recognitionThroughFivePos`, `not_recognitionThroughFive`, `transferThroughSeven` | `HorizonFive.ReflA`, `HorizonFive.Contraction`, `HorizonFive.Recognition`, `HorizonFive.RecogBase`, `HorizonFive.Final` | no |
| A separating functional forces a table error of at least `γ/‖λ‖₁` | core `prop:robust` (first assertion) | `FiniteRealWordFunctional.separation_forces_error` | `RealWordFunctionals` | no |
| Near-ideal instruments, abstract trace-norm form | core `prop:cer:nearideal` (narrower) | `calibrated_positive_instrument_word_error_le` | `Robustness.PositiveInstrumentStability` | no |
| Soundness of square identities, required only after evaluation in the model (without the prefixed form) | companion `lem:cer:sound` (narrower) | `AlgebraicProjectiveData.evaluatedSquareIdentity_sound` | `EvaluatedSquareSoundness` | no |
| For `M` and `S`: a rational functional on reduced yes-first words of length at most seven, nonnegative on every model, equal to `−γ_M`, `−γ_S` at `e/3`, with `‖λ‖₁ ≤ 4.470·10⁹` (M), `≤ 1.9519·10¹⁰` (S) and hence the printed bounds; a model within `δ` on its support has `δ > 6·10⁻¹²` (M), `δ > 1.15·10⁻¹²` (S). The functional is assembled from an encoded certificate; that it is the functional of the companion's appendix is not a Lean theorem | companion `thm:cer:sevenrobust` | `BlockB.thm_cer_seven_b_M_algebraic`, `thm_cer_seven_b_S_algebraic`, `robustFunctionalM`, `robustFunctionalS`, `robust_M_algebraic`, `robust_S_algebraic` | `BlockB.RobustNativeMS` | no |
| The totals `T` and `W_π` of the robust certificates | companion, appendix on certificates | `LengthSeven.Robust.counterT_M`, `counterT_S`, `counterW_M_0` and the analogous declarations | `RobustCert.RobustM`, `RobustCert.RobustS` | no |
| Generalised Lüders (square-root) instruments of nearly projective effects, `‖E² − E‖ ≤ ε < 1/4`: a table error at most `δ` on the support of a separating functional of horizon `L` forces `δ + 2L√τ(ε) ≥ γ/‖λ‖₁`, with `τ(ε) = (1 − √(1 − 4ε))/2` | companion `prop:robust:sqrt` | `real_square_root_instrument_witness_bound`, `complex_square_root_instrument_witness_bound`, `quaternionic_square_root_instrument_witness_bound` | `Robustness.RootInstrumentWitnessBounds` | no |
| Second-order kernel: `E₁` embeds as a Jordan subalgebra of `M₃(D₁)⁺`; Jordan homomorphisms into special algebras kill `K`; reduction mod `I` maps `E₂` unitally into `M₃(D₂/I)⁺` with kernel exactly `K`; `E₂` is not special (the dimensions 18 and 45 are not formalized) | companion `prop:so:kernel` | `AppF.red1_jordan`, `AppF.red1_injective`, `AppF.D1.instRing`, `AppF.E2_jordanHom_kills_K`, `AppF.redq_jordan`, `AppF.redq_unit`, `AppF.redq_eq_zero_iff`, `AppF.Dq.instRing`, `AppF.term_value_mem_K`, `AppF.E2_not_special` | `AppF.SecondOrderSpecial`, `AppF.SecondOrderKernel`, `AppF.SecondOrderQuotient` | no |
| Universal equalities near a complex subalgebra: the residual is `r(t) = t²Q + O(t³)` with `Q` orthogonal to the subalgebra; the remainder `r(t) − t²Q` is `O(t³)`, also under every linear functional, and the probability combination from every state in the subalgebra is `O(t³)` | core, section on equalities; companion `cor:so:residual` | `AppF.cor_so_residual`, `cor_so_residual_of_atoms`, `cor_so_residual_linearFunctional` | `BlockA.SecondOrderResidual` | no |
| Shestakov's identity: the polynomial `ψ` vanishes in special Jordan algebras and is killed by every Jordan homomorphism from `J` into an associative algebra | core, appendix on the algebraic obstruction, the display before `thm:glennie` | `AppF.special_psi_eq_zero`, `jordanHom_kills_psi` | `AppF.Shestakov` | no |
| Matrices over a subalgebra generated by atoms; proper subalgebras; atoms on a line | core `lem:five:coord`, `lem:five:sub`, `lem:fiv:facts`, `lem:five:line` | `lem_five_coord`, `lem_five_coord_gen`, `lem_five_sub`, `lem_fiv_facts_a`, `lem_fiv_facts_b`, `lem_five_line` | `SubalgebraCoordsAndLine` | no |
| A unital subalgebra of `J` is proper exactly when a unital injective Jordan map takes it into the complex Hermitian `d × d` matrices for some `d ≥ 1` | core `cor:tet:special` (for `J`) | `proper_iff_special` | `SubalgebraCoordsAndLine` | no |
| Five explicit atoms generate `J`; every four of them are reproduced from every state by rank-two projections on `ℂ⁶`; no model reproduces the five from any `ρ` | core `thm:pentad` | `pentadF_isAtom`, `pentadF_generatesAlbert`, `pentadDrop_generated_finrank`, `thm_pentad_a`, `LengthSeven.Uniform.pentad_b_algebraic`, `FiveTest.thm_pentad_b` | `PentadArityAndHelly`, `Uniform.Corollaries`, `FiveTest.Compose` | no |
| Irredundant families, arity; Helly number five for proper (equivalently special) subalgebras, and four does not suffice | core `lem:five:helly`, `prop:arity`, `cor:helly` (first sentence) | `lem_five_helly`, `prop_arity`, `cor_helly_geometric`, `cor_helly_special`, `cor_helly_sharp` | `PentadArityAndHelly` | no |
| Operational Helly statement: for a finite family of atoms, a representation of one of the three kinds or an algebraic model (carriers in `Type`) from some state exists exactly when one exists from every state, and exactly when every subfamily of at most five tests (indexed by injections) has one from some state; also in the development's algebraic-model form, with fixed complex matrices of size 6 or 24 for the family | core `cor:helly` (second sentence; carriers in `Type`) | `AlbertChallenge.Bridge.cor_helly_classI`, `AlbertChallenge.Bridge.not_generates_of_small`, `cor_helly_operational_iff_unconditional`, `cor_helly_operational_iff`, `albertUniformSeparation` | `Joins.Helly`, `PentadArityAndHelly`, `AlbertUniformSeparation` | no |
| Reflected quadruple: transfer in span form; separation within the budget | companion `lem:five:reflect` (narrower), `thm:five:refl` | `FiveTest.quad_lift`, `FiveTest.thm_five_refl`, `LengthSeven.LemmaA.lemmaA_budget` | `FiveTest.Transfer`, `FiveTest.Main`, `LengthSeven.LemmaA.Main` | no |
| The reflected quadruple of the five tests consists of atoms, with its thirteen traces and `𝒜 = 1/11664` | companion, the paragraph before `thm:five:refl` and Appendix C | `FiveTest.reflQuad_isAtom`, `FiveTest.reflQuad_overlaps`, `FiveTest.fourPointInvariant_reflQuad`, `FiveTest.reflTraces_Acal` | `FiveTest.Quad`, `FiveTest.Main` | no |
| Length eleven excludes five tests; a positive margin exists from `e/3` at length eleven and from `p_0` at length ten | core, section on five tests; companion `prop:five:short`; the `p_0` margin is not printed | `FiveTest.five_short_p0`, `five_short_e3`, `Ends.five_short_b_exists`, `five_short_b_p0_exists` | `FiveTest.Main`, `Ends.FiveB` | no |
| Least length for five tests, Hilbert spaces in `Type` | companion `cor:five:minimum` (narrower) | `MatchingModels.cor_five_minimum_p0_isLeast_classI`, `cor_five_minimum_e3_isLeast_classI` | `MatchingModels.FiveTestMinimum` | no |
| Ideal-test statistics by a finite real completely positive realization, dimension `17n+1` (and `17n` from an initial state without a Peirce-½ component, core `cor:ins:nohalf`); `68` for four tests | core `thm:cp69`, `cor:ins:nohalf` | `NativeAnalysis.exists_nativeGeneral_real_simulation`, `nativeTaggedBlock_card`, `exists_nativeNoHalf_real_simulation`, `exists_nativeFourIdempotent_mixed_instrument_68` | `NativeTaggedInitialModels`, `NativeFiniteIdempotentSimulation` | no |
| Lower bound six on the memory dimension | core `prop:ins:lower` | `native_CP_dimension_at_least_six` | `FiniteCPHankelRank` | no |
| Factoring through the square root of the effect (existence) | core `lem:ins:factor` (narrower) | `exists_kraus_channel_factorization` | `InstrumentFactorization` | no |
| Sharp effects with arbitrary channels | core `prop:ins:sharpdilation` (without its last sentence in general) | `exists_supported_sharpDilation` | `SupportedSharpDilation` | no |
| A finite-dimensional device with sharp, non-ideal answers reproduces every word, dimension `2(17n+1)` (and `34n`) | core `cor:ins:sharpalbert` | `NativeAnalysis.exists_nativeSharp_instrument_2_17n_add_one`, `exists_nativeNoHalf_sharp_instrument_34n` | `NativeSharpInstrumentSimulation` | no |
| Complete measurements give a Markov chain; qutrit comparison | core `prop:markov` | `frameClassicalWordProbability_eq`, `frameMemory_card`, `mutuallyUnbiasedFrames_qutrit_word_statistics` | `CompleteMeasurementMarkov`, `CompleteFrameQutritComparison` | no |
| Ideality on reachable states: density, linearity and positivity of the branches on the reachable cone, trace-preserving sum, ideality and sharpness | companion `prop:ins:reachable` | `nativeReachableIdealityObligations`, `native_reachable_sharpness`, `native_reachable_certainty_ideality` | `NativeReachableIdeality`, `NativeReachableDensity` | no |
| Fixed-dimension compactness, in Kraus form: a stationary realization exists for all labels exactly when one exists for every finite menu (a finite set of preparation and test labels); without a global one, finitely many pairs and `δ > 0` such that every realization of their finite menu misses one by at least `δ` | companion `prop:ins:compactness` | `stationaryKraus_global_iff_local_finite_menus`, `stationaryKraus_finite_menu_error_gap`, `stationaryKraus_finite_positive_error_gap`, `extendFiniteMenuModel_normalized`, `finiteMenuExtension_wordProbability`, `stationaryKrausRealization_iff_choi` | `PaperFixedDimensionCompactness`, `FiniteMenuExtension`, `Joins.Compactness` | no |
| Slot products in a frame | core `lem:A:slots` (part (a)) | `jordanMul_slotElem01_slotElem12` | `FrameSlotNormalizers` | no |
| Restriction to a complex subalgebra; normal forms for three and four atoms; degenerate pairs; zero set; generation | core `lem:A:restrict`, `lem:A:three`, `lem:A:normal`, `lem:A:degenerate`, `lem:A:zero`, `lem:A:generate` | `complexRestrictionContract_holds`, `lemma_A_three`, `lemma_A_normal`, `lemma_A_degenerate`, `lemma_A_zero_of_quat`, `lemma_A_zero_of_factor`, `lemma_A_generate_three`, `lemma_A_generate_four` | `ThreeAtomAndFourPoint` | no |
| Traces and `𝒜` of the normal-form configuration | core `lem:A:Aform` (narrower) | `sparseFourConfigOct_traces`, `sparseFourConfigOct_fourPointInvariant` | `ThirteenTracesAndAform` | no |
| Triangles in the normal form generate a complex subalgebra | core `lem:A:window` (narrower) | `lemma_A_window_generated`, `prop_windowdet_zero` | `ComplexWindowDeterminantAndMax` | no |
| Identities of the local volume element (nonunital form) | core `lem:A:clifford` | `localUnit_volume_eq_half_reverse`, `localUnit_volume_square` | `LocalVolume` | no |
| Corner relations; Jordan homomorphisms preserve `U` and the triple product | core, appendix on the algebraic obstruction; `lem:tet:corner` (maps on all of `J`) | `CornerRelations`, `jordanHom_map_quadratic`, `jordanHom_map_triple` | `Interfaces.AlgebraicReconstruction`, `JordanHomTransport`, `JordanTripleTransport` | no |
| Every Jordan homomorphism from `J` into an associative algebra (possibly nonunital) is zero | core `thm:tet:albert`, `cor:tet:special` | `albertJordanHom_eq_zero` | `AlbertExceptionality` | no |
| Glennie's identity: `‖F‖² = 9·2²¹·N(p_A+p_B+p_C)·𝒜` for any four atoms; `F = 0` exactly when `𝒜 = 0` | core `thm:glennie` | `AppF.thm_glennie`, `thm_glennie_normSq`, `thm_glennie_perm`, `thm_glennie_eq_zero_iff` | `BlockA.GlennieGeneral` (statements in `Pending.GlennieGeneral`) | no |
| The values of `‖F‖²` at `M` (`2²⁴/3⁹`, order `A,B,C;D`) and at `S` (`2¹⁷/3⁵` when `p_A, p_B` are among the first three, `2¹⁹/3⁶` otherwise), by exact evaluation | core, remark after `thm:glennie` | `AppF.glennie_maximizer_value`, `glennie_maximizer`, `glennie_fixedS_value`, `glennie_fixedS`, `glennie_fixedS_ABD_C`, `glennie_fixedS_ACD_B`, `glennie_fixedS_BCD_A` | `AppF.GlennieMFinal`, `AppF.GlennieS`, `AppF.GlennieSOrders` | no |
| Jordan identity of `J`; classification of idempotents by trace | none (supporting) | `NativeAnalysis.jordan_identity`, `NativeAnalysis.native_idempotent_classification`, `NativeAnalysis.native_idempotent_trace_cases` | `NativeJordanIdentity`, `NativeIdempotentClassification` | no |
| Finite-dimensional formally real Jordan algebras with an associative inner product: spectral resolution, Peirce decomposition and fusion, primitive idempotents, canonical trace, cone of squares, ideals and decomposition into orthogonal simple ideals, Riesz representation of states | none (supporting; these do not mention `J`, and the papers' general Euclidean Jordan algebra results that use them, such as core `thm:bridge`, are proved by hand only) | `UnitalJordanProduct.exists_genuine_simple_factor_decomposition` and the declarations of the modules named | the "General Jordan algebras" group of [docs/MODULES.md](docs/MODULES.md) | no |

Some files state `Prop`-valued interfaces: structures whose names end in `Contract` or
`Obligations`, and the module `Glennie.Obligations`. They are hypotheses or targets inside the
development, not axioms. Every one used by a result above is proved in the repository (for example
`complexTripleContract_holds`, `allHistoryNullContract`, `albertUniformSeparation`,
`nativeReachableIdealityObligations`); `cor_helly_operational_iff` takes its contract as an explicit
argument, and `cor_helly_operational_iff_unconditional` supplies it. The axiom audit and its scope are
described in the next section.

## Status of every numbered statement

Each numbered statement of the two papers (theorems, propositions, lemmas, corollaries, definitions,
remarks and examples, with the numbers printed in the PDFs) has exactly one status. *Formalized*: a
Lean declaration proves the printed statement (the route may differ). *Narrower*: Lean proves the part
or special case named. *Different form*: Lean proves the statement about an object it constructs, or
in a form from which the printed statement follows by an argument that is not a Lean declaration; the
difference is named. *Not formalized*: proved by hand only, or a remark or example. The Lean names
are those of the paper's margin note (first three); the [theorem map](#theorem-map) and
[docs/STATEMENTS.md](docs/STATEMENTS.md) give the rest. The statuses were checked against the margin
notes and the appendices "Formalization" (core Appendix G, companion Appendix C); the column on the
right states what the Lean statement proves. Unnumbered results that are
compared (theorems 5, 8, 10 and 12) are described above.

Core paper:

| No. | Label | Status | Lean declarations (from the margin note) and how the Lean statement differs |
|---|---|---|---|
| Lem 3.1 | `lem:set:support` | Narrower | `native_positive_zero_pairing_support`; stated for `V = J` only |
| Def 3.2 | `def:ideal` | Narrower | `PositiveInstruments.IsIdealTest`; defined for finite-dimensional positive forms; the trace-class Hilbert-space version is not defined |
| Thm 3.3 | `thm:ideal` | Narrower | `PositiveInstruments.idealTest_iff_quadraticRepresentation`; part (a) only, for finite-dimensional positive forms; part (b), on Hilbert spaces, by hand |
| Def 3.4 | `def:idealmodel` | Formalized | `HilbertProjectiveData`, `QuaternionicProjectiveData`, `AlgebraicProjectiveData` |
| Rem 3.5 | `rem:set:hidden` | Not formalized | remark |
| Def 3.6 | `def:memorymodel` | Formalized | `IsNormalizedFiniteCPModel`, `RealFiniteKrausModel` |
| Thm 4.1 | `thm:bridgeJ` | Different form | `AlbertChallenge.albert_criterion`, `AlbertChallenge.no_representation_of_generates`, `AlbertChallenge.linear_separator_of_generates`; compared theorems 11, 1 and 2; theorem 11 states (2) more strongly (`d` is 6 or 24, one family of projections for all states), (3) for carriers in `Type` with algebraic models admitted, and (1) with finite complex Hermitian matrices; theorem 1 gives (3) ⇒ not generating in every universe, and `albertJordanHom_eq_zero` (not compared) gives operator-sense speciality ⇒ `B ≠ J`; the printed theorem follows from these by a short argument that is not itself a Lean declaration |
| Rem 4.2 | `rem:bri:assoc` | Not formalized | remark |
| Lem 4.3 | `lem:bri:gns` | Formalized | `cyclicHilbertModel`, `cyclicHilbertModel_probability` |
| Lem 4.4 | `lem:bri:null` | Narrower | `allHistoryNullContract`; the null-set part only (left invariance, extension from word vectors to their span); the step to `π(Z)π(P_t)Ω = 0` is not a declaration |
| Lem 4.5 | `lem:purity` | Narrower | `purityResidual_threeHistories`, `NativeAnalysis.native_corner_long_probability`; the vanishing in `J` for an outcome that is an atom of `J`; the printed lemma allows an outcome primitive in the generated subalgebra |
| Lem 4.6 | `lem:bri:lift` | Formalized | `hasSequentialEffectLift_orbit_corner`, `hasSequentialEffectLift_reflection` |
| Lem 4.7 | `lem:bri:orbit` | Narrower | `nativeOrbitSpan_iff_generated`; for tests that are atoms of `J`; the printed lemma allows tests primitive in the generated subalgebra |
| Prop 4.8 | `prop:bri:eta` | Narrower | `exists_generatedCyclicJordanMap`; for tests that are atoms of `J`, with `η` valued in operators on the cyclic space of an algebraic model |
| Lem 4.9 | `lem:bri:state` | Narrower | `FaithfulHermitianJordanEmbedding.exists_unique_positive_trace_representative`, `suppliedEmbeddingStateTransport`; the word transport only for unital subalgebras of `J` and states of `J`; the embedding is supplied |
| Def 4.10 | `def:bri:minimal` | Not formalized | used only by Theorem 4.11 |
| Thm 4.11 | `thm:bridge` | Not formalized | hand proof only |
| Rem 4.12 | `rem:mixture` | Not formalized | remark |
| Cor 4.13 | `cor:four` | Not formalized | hand proof only |
| Prop 4.14 | `prop:field` | Narrower | `HilbertProjectiveData.complexExtensionModel_probability`, `HilbertProjectiveData.quaternionExtensionModel_probability`, `cyclicHilbertModel_probability` …; part (a), each inclusion by a construction preserving all word probabilities and finite dimension; the equalities of classes are not stated; (b), (c) by hand |
| Rem 4.15 | `rem:bri:foil` | Not formalized | remark |
| Cor 4.16 | `cor:bri:finite` | Narrower | `HilbertModelSeparation.uniformHilbertSeparator_generating_atoms`; part (a) only; (b) by hand |
| Prop 5.1 | `prop:three` | Formalized | `complexTripleContract_holds`, `AlbertChallenge.three_atoms`; different route |
| Def 5.2 | `def:traces` | Formalized | `fpOverlap`, `fpTriangle`, `fpDoublePair1` … |
| Prop 5.3 | `prop:fp:tracerel` | Narrower | `rankThree_fourIdempotent_trace_relation`, `albert_fourAtom_trace_relation`; for an explicit rank-three model and for `J`; general rank-three Euclidean Jordan algebras are not treated |
| Rem 5.4 | `rem:fp:tracerel-rank` | Not formalized | remark |
| Thm 5.5 | `thm:fourpoint` | Formalized | `thm_fourpoint`, `lemma_A_normal_nondegenerate`, `AlbertChallenge.fourPoint_criterion` |
| Prop 5.6 | `prop:windowdet` | Formalized | `prop_windowdet`, `prop_windowdet_zero`, `lemma_A_window_generated` |
| Cor 5.7 | `cor:fp:rank` | Formalized | `cor_fp_rank` |
| Lem 5.8 | `lem:fp:access` | Narrower | `triangleDefect_primitive_decomposition`, `symmetricTripleDefect_primitive_decomposition`; the defects of (R2), (R3) as combinations of purity residuals; the final operator identities are not a declaration |
| Thm 5.9 | `thm:tetra` | Narrower | `tetrahedronEngine`; the algebraic form (Theorem F.3) only; the passage to `D_tet = 0` on a Hilbert space is not stated |
| Prop 5.10 | `prop:Dacal` | Formalized | `prop_Dacal_poly`, `tetrahedronDiscriminant_eq_overlap_mul_fourPointInvariant` |
| Cor 5.11 | `cor:fp:noideal` | Formalized | `LengthSeven.Uniform.noideal_algebraic`, `LengthSeven.Uniform.noideal_hilbert`, `LengthSeven.Uniform.noideal_rightQuaternionic` … |
| Prop 5.12 | `prop:max` | Formalized | `prop_max`, `maximizerConfig_traces`, `fourPointInvariant_maximizerConfig` … |
| Lem 5.13 | `lem:fp:DeltaWmax` | Formalized | `lem_fp_DeltaWmax` |
| Cor 5.14 | `cor:fp:maxmixed` | Formalized | `cor_fp_maxmixed` |
| Thm 6.1 | `thm:cer:uniform` | Narrower | `AlbertChallenge.seven_steps_exclude`, `LengthSeven.Uniform.uniform_lengthSeven_e3_algebraic`, `LengthSeven.Uniform.uniform_lengthSix_pA_algebraic` …; `L_min` is taken over Hilbert spaces in `Type`; the exclusions hold in every universe; different route; (b) with a finite witness set and no explicit `δ` |
| Prop 6.2 | `prop:cer:universalsix` | Narrower | `MatchingModels.prop_cer_universalsix_witness`, `MatchingModels.prop_cer_universalsix_c12`, `AlbertChallenge.six_step_model` …; `L_min` is taken over Hilbert spaces in `Type`; the exclusions hold in every universe |
| Cor 6.3 | `cor:cer:everystate` | Formalized | `BlockB.cor_cer_everystate`, `BlockB.everystate_lengthSeven_algebraic` |
| Lem 6.4 | `lem:cer:recon` | Formalized | `finiteGram_iff_finiteRealModel`, `AlgebraicProjectiveData.finiteGram`; different route |
| Lem 6.5 | `lem:cer:short` | Formalized | `LengthSeven.WalkForm.shortRules_of_table`, `LengthSeven.lengthSeven_e3_rules` |
| Lem 6.6 | `lem:cer:reduce` | Not formalized | hand proof only; not used by the formal proof |
| Lem 6.7 | `lem:cer:tablemodel` | Narrower | `LengthSeven.TableModel.tableModel`, `LengthSeven.TableModel.tableModel_lemmaB`; the last sentence, for words of `𝒲₂₈`, entry by entry, with Lean's Gram table; the walk-space assertion is not stated |
| Lem 6.8 | `lem:cer:gram28` | Narrower | `LengthSeven.LemmaA.lemmaA_of_gram28Hyp`, `LengthSeven.LemmaA.lemmaA`, `LengthSeven.TableModel.tableModel`; for words of `𝒲₂₈` only, entry by entry |
| Lem 6.9 | `lem:cer:negative` | Formalized | `LemmaB.gram_Xi`, `LemmaB.Xi_mem_span_uhat`, `LemmaB.no_psd_realisation_traces`; different route |
| Thm 6.10 | `thm:cer:seven` | Formalized | `BlockB.seven_M_e3_algebraic`, `BlockB.seven_S_e3_algebraic`, `BlockB.seven_M_pA_algebraic` …; different route |
| Prop 6.11 | `prop:horizon` | Narrower | `MatchingModels.prop_cer_universalsix_c12`, `MatchingModels.lMin_eq_seven`; a model on `ℂ¹²` through length six, not the equal mixture of `Q₊`, `Q₋` |
| Rem 6.12 | `rem:cer:variance` | Not formalized | remark |
| Prop 6.13 | `prop:cer:schedule` | Not formalized | hand proof only |
| Rem 6.14 | `rem:cer:tracial` | Not formalized | remark |
| Thm 6.15 | `thm:eleven` | Different form | `BlockB.thm_eleven_with_overlaps`, `BlockB.thm_eleven_full`, `MatchingModels.overlap_pos_lt_one_of_fourPoint_pos` …; Lean's list is generated from an encoding of the 1,673 relation applications; its count and length histogram are proved; that it is the list printed in the companion's appendix is not a Lean theorem |
| Prop 6.16 | `prop:Dfails` | Formalized | `MatchingModels.dfails_length_le_two`, `MatchingModels.dfails_thirteen_traces`, `MatchingModels.dfails_tetra_dtet` … |
| Prop 6.17 | `prop:cer:noequality` | Narrower | `AppF.prop_cer_noequality_a`, `MatchingModels.no_classI_linearEq_le_six`; part (a) with projective equalities defined by real finite-dimensional vector states, representations entering through algebraic models in `Type`; part (d); (b), (c) by hand |
| Rem 6.18 | `rem:cer:fivestep` | Formalized | `HorizonFive.horizonFive_projectiveEquality`, `HorizonFive.horizonFiveClause`; with the weaker hypothesis of vanishing on real finite-dimensional representations with vector states |
| Prop 6.19 | `prop:robust` | Narrower | `FiniteRealWordFunctional.separation_forces_error`; the first assertion only |
| Prop 6.20 | `prop:cer:nearideal` | Narrower | `calibrated_positive_instrument_word_error_le`; in an abstract trace-norm setting with the leakage bound as a hypothesis; the Hilbert-space instance and the witness bound are not formalized |
| Prop 6.21 | `prop:cer:sharpdisturb` | Not formalized | hand proof only |
| Rem 6.22 | `rem:cer:sharpdisturb` | Not formalized | remark |
| Lem 7.1 | `lem:five:coord` | Formalized | `lem_five_coord`, `lem_five_coord_gen` |
| Thm 7.2 | `thm:pentad` | Formalized | `pentadF_isAtom`, `pentadF_generatesAlbert`, `pentadDrop_generated_finrank` … |
| Lem 7.3 | `lem:five:helly` | Formalized | `lem_five_helly` |
| Prop 7.4 | `prop:arity` | Formalized | `prop_arity` |
| Cor 7.5 | `cor:helly` | Narrower | `cor_helly_geometric`, `cor_helly_special`, `cor_helly_sharp` …; the operational sentence for carriers in `Type`, algebraic models admitted, subfamilies indexed by injections |
| Thm 8.1 | `thm:cp69` | Formalized | `NativeAnalysis.exists_nativeGeneral_real_simulation`, `NativeAnalysis.nativeTaggedBlock_card` |
| Cor 8.2 | `cor:ins:nohalf` | Formalized | `NativeAnalysis.exists_nativeNoHalf_real_simulation`, `NativeAnalysis.exists_nativeFourIdempotent_mixed_instrument_68` |
| Rem 8.3 | `rem:ins:notideal` | Not formalized | remark |
| Prop 8.4 | `prop:ins:lower` | Formalized | `native_CP_dimension_at_least_six`, `NativeAnalysis.exists_nativeFourIdempotent_mixed_instrument_68` |
| Lem 8.5 | `lem:ins:factor` | Narrower | `exists_kraus_channel_factorization`; existence of the channel, in Kraus form; the formula is not stated |
| Prop 8.6 | `prop:ins:sharpdilation` | Narrower | `exists_supported_sharpDilation`; without its last sentence, on real Kraus operators, in general |
| Cor 8.7 | `cor:ins:sharpalbert` | Formalized | `NativeAnalysis.exists_nativeSharp_instrument_2_17n_add_one`, `NativeAnalysis.exists_nativeNoHalf_sharp_instrument_34n` |
| Rem 8.8 | `rem:ins:sharpnotideal` | Not formalized | remark |
| Ex 8.9 | `ex:ins:twopress` | Not formalized | example |
| Prop 8.10 | `prop:markov` | Formalized | `frameClassicalWordProbability_eq`, `frameMemory_card`, `mutuallyUnbiasedFrames_qutrit_word_statistics` |
| Lem A.1 | `lem:A:slots` | Narrower | `jordanMul_slotElem01_slotElem12`; part (a), in the development's slot indexing; (b), (c) not stated in this form |
| Lem A.2 | `lem:A:restrict` | Formalized | `complexRestrictionContract_holds` |
| Lem A.3 | `lem:A:three` | Formalized | `lemma_A_three`; different route |
| Lem A.4 | `lem:A:normal` | Formalized | `lemma_A_normal`, `lemma_A_normal_nondegenerate`; different route |
| Lem A.5 | `lem:A:Aform` | Narrower | `sparseFourConfigOct_traces`, `sparseFourConfigOct_fourPointInvariant`; the trace identities and the formula for `𝒜`; the description of `G` and `s` is not stated |
| Lem A.6 | `lem:A:degenerate` | Formalized | `lemma_A_degenerate` |
| Lem A.7 | `lem:A:zero` | Narrower | `lemma_A_zero_of_factor`, `lemma_A_zero_of_quat`; part (b); in place of (a), its consequence that `𝒜` vanishes on four atoms of a quaternionic subalgebra |
| Lem A.8 | `lem:A:generate` | Formalized | `lemma_A_generate_three`, `lemma_A_generate_four` |
| Lem A.9 | `lem:A:window` | Narrower | `lemma_A_window_generated`, `prop_windowdet_zero`; parts (b), (c); part (a) and `P_{gW} g = g P_W` are not stated as separate theorems |
| Lem A.10 | `lem:A:clifford` | Formalized | `localUnit_volume_eq_half_reverse`, `localUnit_volume_square` |
| Ex B.1 | `ex:set:c3` | Not formalized | example |
| Lem B.2 | `lem:bri:rank` | Not formalized | hand proof only |
| Lem C.1 | `lem:cer:gram7` | Narrower | `LengthSeven.LemmaA.lemmaA`; every Gram entry between the 28 path vectors is derived; the printed formulas are not stated in this form |
| Prop C.2 | `prop:cer:quatpair` | Formalized | `MatchingModels.prop_cer_quatpair_a`, `MatchingModels.prop_cer_quatpair_b`, `MatchingModels.prop_cer_quatpair_c_line` … |
| Lem E.1 | `lem:five:sub` | Formalized | `lem_five_sub` |
| Lem E.2 | `lem:fiv:facts` | Formalized | `lem_fiv_facts_a`, `lem_fiv_facts_b` |
| Lem E.3 | `lem:five:line` | Formalized | `lem_five_line` |
| Def F.1 | (no label) | Formalized | `CornerRelations`; the corner relations (Definition F.1) |
| Lem F.2 | `lem:tet:corner` | Narrower | `jordanHom_map_quadratic`, `jordanHom_map_triple`; only for maps defined on all of `J`; the corner relations for a subalgebra `C` are not stated |
| Thm F.3 | `thm:tetra:algebraic` | Formalized | `tetrahedronEngine` |
| Cor F.4 | `cor:tet:special` | Narrower | `albertJordanHom_eq_zero`, `proper_iff_special`; only the case `C = J`, where `η = 0` |
| Thm F.5 | `thm:tet:albert` | Formalized | `albertJordanHom_eq_zero`; different route |
| Thm F.6 | `thm:glennie` | Different form | `AppF.thm_glennie`, `AppF.thm_glennie_normSq`, `AppF.thm_glennie_perm` …; `F` is defined as the sum of the nine placements of the polarisation of `ψ`; its identification with the coefficient `[s²t²u²]` is not a Lean theorem |

Companion paper:

| No. | Label | Status | Lean declarations (from the margin note) and how the Lean statement differs |
|---|---|---|---|
| Lem 2.1 | `lem:cer:finite` | Not formalized | no Lean counterpart |
| Thm 2.2 | `thm:eleven` | Different form | `BlockB.thm_eleven_with_overlaps`, `BlockB.thm_eleven_full`, `MatchingModels.overlap_pos_lt_one_of_fourPoint_pos` …; as core Theorem 6.15 |
| Lem 2.3 | `lem:cer:sound` | Narrower | `AlgebraicProjectiveData.evaluatedSquareIdentity_sound`; the first assertion, with the identity required only after evaluation in the model; the prefixed form is not stated |
| Thm 2.4 | `thm:cer:sevenrobust` | Different form | `BlockB.thm_cer_seven_b_M_algebraic`, `BlockB.thm_cer_seven_b_S_algebraic`, `BlockB.robustFunctionalM` …; Lean proves every printed property for its own functional, assembled from encoded derivation data; that it is the functional of the appendix is not a Lean theorem |
| Prop 2.5 | `prop:robust:sqrt` | Formalized | `real_square_root_instrument_witness_bound`, `complex_square_root_instrument_witness_bound`, `quaternionic_square_root_instrument_witness_bound` |
| Prop 2.6 | `prop:cer:Seleven` | Different form | `fixedSConstructedWitness`, `fixedSConstructedWitness_horizon`, `fixedSConstructedWitness_model_nonnegative` …; Lean builds the functional from its own encoding of the purity occurrences; that these are the appendix's occurrences, and that its words lie in `𝓕`, are not Lean theorems |
| Prop 2.7 | `prop:cer:leftmult` | Not formalized | no Lean counterpart |
| Prop 3.1 | `prop:eq:five` | Formalized | `HorizonFive.horizonFive_projectiveEquality`, `HorizonFive.horizonFiveClause` |
| Prop 3.2 | `prop:so:kernel` | Narrower | `AppF.red1_jordan`, `AppF.red1_injective`, `AppF.E2_jordanHom_kills_K` …; parts (a)–(c) and the non-speciality of `E₂`, with `D₁`, `D₂/I` explicit; the dimensions 18 and 45 are not formalized |
| Cor 3.3 | `cor:so:residual` | Formalized | `AppF.cor_so_residual`, `AppF.cor_so_residual_of_atoms`, `AppF.cor_so_residual_linearFunctional` |
| Lem 4.1 | `lem:five:reflect` | Narrower | `FiveTest.quad_lift`; for the reflected quadruple only, the transfer as membership in a span of words; (a), (b), (d) not stated in general |
| Thm 4.2 | `thm:five:refl` | Formalized | `FiveTest.thm_five_refl`, `LengthSeven.LemmaA.lemmaA_budget`; by the first argument of the printed proof; the explicit vector `Φ` is not formalized |
| Prop 4.3 | `prop:five:short` | Formalized | `FiveTest.five_short_p0`, `FiveTest.five_short_e3`, `Ends.five_short_b_exists` …; the explicit margin value after the proof is not formalized |
| Cor 4.4 | `cor:five:minimum` | Narrower | `MatchingModels.cor_five_minimum_p0_isLeast_classI`, `MatchingModels.cor_five_minimum_e3_isLeast_classI`; `L_min` is taken over Hilbert spaces in `Type`; the exclusions hold in every universe |
| Cor 4.5 | `cor:five:depth` | Not formalized | no Lean counterpart |
| Rem 4.6 | `rem:five:orbit` | Not formalized | remark |
| Prop 4.7 | `cor:c:hellyquat` | Not formalized | no Lean counterpart |
| Cor 4.8 | `cor:c:hellysix` | Not formalized | no Lean counterpart |
| Prop 5.1 | `prop:windowlaw` | Not formalized | only the deterministic identity behind its Laplace transform is proved (`complexWindow_laplace_integrand`) |
| Rem 5.2 | `rem:fp:metric` | Not formalized | remark |
| Rem 5.3 | `rem:fp:invariants` | Not formalized | remark |
| Prop 6.1 | `prop:ins:reachable` | Formalized | `native_reachable_sharpness`, `native_reachable_certainty_ideality`, `nativeReachableIdealityObligations` |
| Prop 6.2 | `prop:ins:compactness` | Formalized | `stationaryKraus_global_iff_local_finite_menus`, `stationaryKraus_finite_menu_error_gap`; in Kraus form, equivalent to completely positive form by `stationaryKrausRealization_iff_choi` |
| Lem 6.3 | `lem:ins:repair` | Not formalized | no Lean counterpart |
| Prop 6.4 | `prop:c:sharpdim` | Not formalized | no Lean counterpart |
| Cor 6.5 | `cor:c:sharp26` | Not formalized | no Lean counterpart |
| Cor 6.6 | `cor:c:sharpnohalf` | Not formalized | no Lean counterpart |
| Lem A.1 | `lem:cer:h5:refl` | Formalized | `HorizonFive.reflectionClassConsistency`, `HorizonFive.reflectionContraction` |
| Lem A.2 | `lem:cer:h5:lift` | Formalized | `HorizonFive.recognitionThroughFivePos` |
| Lem A.3 | `lem:cer:h5:seven` | Formalized | `HorizonFive.transferThroughSeven` |

## How it was verified

Given trust in the Lean kernel and in the checking tools, the twelve compared theorems hold as stated
in `Challenge.lean`. No tool can check that a statement means what its English description says;
where the description and the Lean statement differ, the Lean statement is what was proved.

Two sets of runs, before the publication commit: on the working copy from which this repository is cut,
and on this repository's files themselves.

On the working copy (Lean files token-identical to the ones here, except for the build-order imports
described under "Check it yourself", and differing otherwise only in comments and docstrings):

- A build of every module (551 source files) with Lean `v4.36.0` and the unmodified Mathlib `v4.36.0`
  cache (commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`), one module at a time: exit 0, wall time
  5,327 s, CPU time 5,065 s user, largest memory use 7.46 GiB (`RobustCert.RobustM`).
- `#print axioms` on that build: `[propext, Classical.choice, Quot.sound]` for the twelve Solution
  theorems and for every declaration named in the two papers (230 names, each resolved to exactly one
  declaration).
- A type-identity check: the twelve statements of `Solution.lean` and `Challenge.lean`, printed with
  `pp.all`, are identical.
- Negative controls: altered statement files (octonion multiplication, norm, star and unit; Albert
  multiplication, star and unit; reversed order of a word; a complex-only exclusion in place of the
  full one) fail to elaborate as intended (9 of 9). These files belong to the working copy and are not
  part of this repository.

On this repository's files (18 November 2026):

- A clean `lake build Solution Challenge` (the part of the build that the Palomar pipeline runs), three
  jobs: exit 0, 378 s, largest memory of the build's control group 3.2 GiB.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]` for the twelve Solution theorems and for
  every declaration named in the papers (230 names), of which 108 lie in the import closure of
  `Solution`.
- Comparator in export mode, with NanoDa and the Lean kernel, on `comparator.json`: it accepts
  `Solution` against the twelve-theorem `Challenge` ("nanoda kernel accepts the solution", "Lean
  default kernel accepts the solution") and rejects a copy of `Challenge.lean` used as the solution
  ("Illegal axiom detected: 'sorryAx'").
- A clean `lake build` of all 524 modules of this repository: exit 0, 3,484 s with three jobs on three cores, largest memory use 7.30 GiB (`RobustCert.RobustM`).

| Check | Result | Run on |
|---|---|---|
| Build of all modules | exit 0 | working copy, 2026-11-18 |
| `#print axioms`, twelve Solution theorems and the cited declarations | standard axioms only (230 names) | this repository's files, 2026-11-18 |
| `#print axioms`, the same within Solution's import closure | standard axioms only (108 names) | this repository's files, 2026-11-18 |
| Comparator with NanoDa, Challenge against Solution | accepted; `sorry` copy rejected | this repository's files, 2026-11-18 |
| `lake build Solution Challenge` | exit 0 | this repository's files, 2026-11-18 |
| `lake build` of all modules | exit 0 | this repository's files, 2026-11-18 |

Size: `Challenge.lean` has 497 lines (27,971 bytes), above Palomar's advisory threshold of 300 lines
and below its limit of 1,000 lines and 100 KiB. The repository has 524 Lean modules with
156,316 lines; its largest file is `src/PentadArityAndHelly.lean`, with 7,576 lines.

## Check it yourself

Requirements: Linux or macOS, `elan`, git, about 8 GiB of free memory per Lean process and about
12 GiB of disk space (the Mathlib cache and toolchain take about 10 GiB, the build about 1 GiB). The
toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.36.0`) and the Mathlib revision in
`lake-manifest.json`. A few modules need up to about 7.5 GiB each; thirteen imports marked
`-- build order only` make the largest of them compile one after another, so that a parallel `lake build`
does not run them at the same time.

```sh
git clone https://github.com/macgregor-sudo/albert-sequential-measurements.git
cd albert-sequential-measurements
git checkout v1.0.0
lake exe cache get          # prebuilt Mathlib oleans
lake build                  # all modules, including Challenge and Solution
python3 -c 'import json; print("import Solution"); [print("#print axioms", n) for n in json.load(open("comparator.json"))["theorem_names"]]' \
  | lake env lean --stdin   # prints the axioms of the twelve theorems
```

The last command should print, for each of the twelve theorems, a line of the form

```text
'AlbertChallenge.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To compare statements, export both modules and run Comparator on [`comparator.json`](comparator.json)
(challenge module `Challenge`, solution module `Solution`, the twelve theorem names, the three
permitted axioms, NanoDa enabled):

```sh
lake env leanexport Challenge -- <constants> > Challenge.export
lake env leanexport Solution -- <constants> > Solution.export
lake comparator --config comparator.json \
  --challenge-from-export Challenge.export --solution-from-export Solution.export
```

where `<constants>` is the list of kernel constants and the twelve theorem names that Comparator
expects. These are the commands of the local run, which used the toolchain's own `lake` and
`leanexport`; none of the commands in this section has been run on the repository as published.

## Reading the proof

The development lives in the namespace `AlbertSequential`, except `LemmaB/*` and part of
`TableModel/*` (namespace `LemmaB`) and `Glennie/*` (namespace `Glennie`); the names below are module
names. Its Albert-side definitions (`Defs`) are the Challenge's definitions under other names, and
the bridges between the two are definitional up to an identity cast. A tour by layer, bottom up;
[docs/MODULES.md](docs/MODULES.md) assigns every module to a group.

1. **The Albert algebra.** `Defs` (octonions, `Albert`, `jordanMul`, trace, quadratic map, atoms,
   states), `NativeAlbertLaws`, `NativeJordanIdentity`, `NativeIdempotentClassification`,
   `NativeAutomorphisms`, `FrameSlotNormalizers`, `OctonionGeometry`, and the adapted layer
   `Glennie/*` (compact octonions and Albert algebra, automorphisms, diagonalisation, square cone).
   General Jordan algebras: `RealJordanOperators`, `RealJordanFundamental`, `JordanPowerAssociativity`,
   `UnitalJordanProduct`, `JordanProductQuadratic`, `EuclideanJordanForm`, and the finite-dimensional
   theory behind them (`JordanSpectralResolution`, `JordanPeirceFusion`, `FormalReality*`,
   `EuclideanJordan*`, `JordanIdeal*`, `JordanSimpleIdealDecomposition`).
2. **Words and models.** `Interfaces.WordsAndCertificates` (`nativeWordProbability`,
   `AlgebraicProjectiveData`), `HilbertProjectiveData`, `QuaternionicProjectiveData`,
   `RightQuaternionicHilbert`, `ChronologicalWords`, `BoundedWordEffects`.
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
   imports), and the joins `Joins/*`.
7. **Statement layer.** `Challenge`, `ChallengeDefs`, `Solution`, and `Bridge.Albert`,
   `Bridge.AlbertHeadlines`, `Bridge.Models`, `Bridge.Exclusion`, `Bridge.Seven`, `Bridge.C12`,
   `Bridge.Least`, `Bridge.Matrix`, `Bridge.Criterion`, `Bridge.Atoms` (all declarations in namespace
   `AlbertChallenge.Bridge`, except the native form of theorem 12 in `Bridge.Atoms`).

To find the Lean declaration for a paper result, use the [theorem map](#theorem-map); the
[dense proof](#dense-proof-for-ai-agents) names the declarations along each compared proof.

## How this was produced

Robert R. MacGregor is the human contributor and the person responsible for the repository. The AI
statement of the core paper reads:

> All text, mathematics and proofs herein, and all Lean 4 code apart from the adapted files noted in
> Appendix G, were produced by Claude Fable 5.2, Claude Opus 5.5, GPT-6.2 Astra, GPT-6.2 Sol, Gemini
> Carbon and Gemini Hydrogen, and the main theorems on the Albert algebra are machine-checked in Lean.
> Except for this statement, all content herein was generated by AI and has not been understood
> without AI interpretation.

Two groups of files are not new work produced for this repository, and both are disclosed as
adapted ([docs/ATTRIBUTION.md](docs/ATTRIBUTION.md)): the declarations adapted from Physlib in
`src/RealJordanFundamental.lean`, `src/JordanPowerAssociativity.lean` and
`src/RealJordanOperators.lean`, written by their upstream author, who is named there and in the file
headers; and the fifteen modules under `src/Glennie/`, adapted from the contributor's earlier Palomar
entry PALOMAR-2026-10-16-000013, whose own production account is recorded in that entry.

In this repository "the main theorems" are the twelve statements of `Challenge.lean`; the results the
papers prove by hand only are named under [Status of every numbered statement](#status-of-every-numbered-statement).

Review. Every module not named in this paragraph was reviewed by an AI agent other than the one that
wrote it. The following had no such review at the release commit: the length-seven proof
(`LengthSeven/*`, `LemmaB/*`, `TableModel/*`, `Uniform/*`), `MatchingModels/*`, `FiveTest/*`,
`HorizonFive/*`, `RobustCert/*`, `Ends/*`, `AppF/*`, `BlockA/*`, `BlockB/*`, `Pending.GlennieGeneral`,
`Joins/*`, the statement layer (`Challenge`, `ChallengeDefs`, `Solution`, `Bridge/*`), the changes made to port the code to Lean `v4.36.0`, the
conversion of 54 files to the module system and the licence and attribution headers. Every compared
theorem passes through unreviewed bridge files, and theorems 3, 4, 5, 9, 10 and 11 also rest on
unreviewed modules (`Uniform.Main`, `MatchingModels/*`). No human has reviewed the mathematics, the
Lean proofs or the faithfulness of the statements.

## Relation to earlier formalizations and reused code

The mathematics formalized here is that of the two papers; the formalization is source-based, not
an original presentation. Results that the papers attribute to earlier work, such as the
exceptionality of `H₃(𝕆)` (Albert, 1934), the classification of formally real Jordan algebras
(Jordan, von Neumann and Wigner, 1934) and Glennie's identity (1966), are cited there with their
sources. The area is the operational study of Jordan-algebraic state spaces in the foundations of
quantum theory, between mathematical physics and nonassociative algebra. The core paper's section
"Related work" describes prior work; the result it names as nearest is the theorem of Müller and
Garner (Theorem 2 of their 2023 paper) that an unrestricted finite-dimensional generalized probabilistic
theory has an exact linear embedding into finite-dimensional quantum theory exactly when it is a special Euclidean Jordan algebra, which concerns single-shot
probabilities without an update rule, while the criterion here fixes finitely many tests and compares
all sequences under the Lüders update. No derivation of either statement from the other is
established. Novelty has not been established by a literature search recorded here, and no claim of
novelty or priority is made.

Reused code. The fifteen modules under `src/Glennie/` (compact octonions and Albert algebra and their
elementary laws, automorphisms, diagonalisation, square cone) are adapted from the contributor's
earlier Palomar entry PALOMAR-2026-10-16-000013 (`macgregor-sudo/compact-albert-recognition` at commit
`40d3b34`, Apache-2.0). `src/RealJordanFundamental.lean`, `src/JordanPowerAssociativity.lean` and
`src/RealJordanOperators.lean` are adapted from four files of Physlib (`leanprover-community/physlib` at commit
`08a6c1b5`, files by Tom Ole Diem, Apache-2.0) and keep its copyright notice. Details, with the
declarations adapted and the changes made: [docs/ATTRIBUTION.md](docs/ATTRIBUTION.md) and
[THIRD_PARTY_NOTICES](THIRD_PARTY_NOTICES).

Earlier Palomar entries by the same contributor, from which no file is used:
PALOMAR-2026-09-13-000001 (`macgregor-sudo/albert-frame-triple-invariants`, split Albert frame
invariants), an ancestor of code in PALOMAR-2026-10-16-000013, and PALOMAR-2026-10-29-000034
(`macgregor-sudo/tight-39-code`, the tight 39-point code in the octonionic projective plane), which
shares the `Glennie/` ancestry.

Related registered Lean work by others, from which no code is used (relationship `independent` in
`formalization.yaml`): sequential products on Hermitian matrix algebras,
`ehrlich-b/sequential-products-lean` (PALOMAR-2026-08-22-000006, the real and complex classification
theorems; PALOMAR-2026-08-21-000009, Albert's power-associativity theorem for commutative Jordan
rings carrying a real-module structure; PALOMAR-2026-08-21-000001, the real case of Wigner's theorem); Euclidean Jordan algebras,
`ehrlich-b/euclidean-jordan` (PALOMAR-2026-08-23-000005, the Koecher–Alfsen–Shultz theorem;
PALOMAR-2026-08-23-000006, spectral resolution; PALOMAR-2026-08-29-000001, the trace form;
PALOMAR-2026-08-29-000008, the Peirce decomposition relative to a frame); composition algebras,
`ehrlich-b/composition-algebras` (PALOMAR-2026-08-29-000015 and PALOMAR-2026-08-29-000018, Hurwitz's
theorem in dimension and classification form, with the octonions constructed); and Jordan
homomorphisms of associative rings, `stalex444/herstein-jordan-homomorphisms` (PALOMAR-2026-11-11-000008,
Herstein's theorem onto prime rings). The core paper cites the three `ehrlich-b` repositories. This
development proves its own spectral and Peirce results (`JordanSpectralResolution`,
`JordanPeirceFusion`), its own power associativity (adapted from Physlib) and its own octonions
(`Glennie/` and the Challenge's Cayley–Dickson definition); its statement that every Jordan
homomorphism from `J` into an associative algebra is zero (`albertJordanHom_eq_zero`) has a
non-associative source and uses no result of the Herstein entry. The core paper also cites a Lean
formalization by M. J. Soares (`markkasaurus/albert-algebra-lean`, Zenodo, doi:10.5281/zenodo.21482444,
Apache-2.0; not a Palomar entry), which proves the Jordan identity of `H₃(𝕆)`, its real dimension 27,
Glennie's identity in symmetrisations of associative algebras and an explicit violation of it in
`H₃(𝕆)`. No code of it is used; this development proves the Jordan identity of its own encoding
(`NativeAnalysis.jordan_identity`) and the vanishing of every Jordan homomorphism from `J` into an
associative algebra (`albertJordanHom_eq_zero`) independently, by another route.

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
| `src/Bridge/` | translation between the Challenge's objects and the development's |
| `src/` (other files and directories) | the development, by layer as above; module names are the paths below `src/` |
| `comparator.json` | Comparator configuration |
| `formalization.yaml` | Palomar metadata (v0.4) |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | build configuration and pins |
| `.gitignore` | excludes Lake's build directory `.lake` |
| `.github/workflows/palomar.yml` | manual run of Palomar's verification workflow (`mode: full`) on this commit |
| `docs/MODULES.md` | every module, grouped by what it proves |
| `docs/STATEMENTS.md` | each compared statement, its definitions and known gaps; the theorem map with gaps |
| `docs/PROOF-PATH.md` | proof route of each compared theorem and the exact strength of the named steps |
| `docs/ATTRIBUTION.md`, `THIRD_PARTY_NOTICES` | adapted code, its origin and licence |
| `CITATION.cff` | citation metadata |
| `LICENSE` | Apache-2.0 (also the licence of the adapted Physlib files) |

## Citation and licence

Contributor: Robert R. MacGregor, ORCID [0009-0003-1734-8054](https://orcid.org/0009-0003-1734-8054).

Cite with [`CITATION.cff`](CITATION.cff). The files of this repository are licensed Apache-2.0
([LICENSE](LICENSE), as `project.license` declares); adapted files keep their notices
([docs/ATTRIBUTION.md](docs/ATTRIBUTION.md)). The two papers, which are distributed outside the
repository, are licensed CC BY 4.0.
