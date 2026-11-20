# Statements

This file accounts for each compared declaration of [`src/Challenge.lean`](../src/Challenge.lean) (namespace `AlbertChallenge`):
what it says, which paper result it formalizes, the definitions it uses, and the known differences
between the paper's statement and the Lean statement. Paper results are cited by their LaTeX label,
prefixed "core" or "companion"; the [README](../README.md) gives their printed numbers and, in its
status ledger, the declarations that prove every numbered statement, including the printed forms
that the compared statements do not reach. [THEOREM-MAP.md](THEOREM-MAP.md) lists further
declarations.

## Definitions used by the compared statements

All are defined in `Challenge.lean` with docstrings; Mathlib supplies the rest.

| Definition | Ordinary meaning |
|---|---|
| `Octonion` | the real octonions `𝕆`, as pairs `(a, b)` of Mathlib quaternions `ℍ[ℝ]` standing for `a + bℓ`; only the real vector space structure is inherited from the product type |
| `octMul` | octonion multiplication `(a, b)(c, d) = (ac − d̄b, da + bc̄)`, the Cayley–Dickson doubling of `ℍ` with parameter `−1` (the compact, division octonions) |
| `octConj`, `octScalar`, `octRe`, `octNormSq` | conjugation `(a, b) ↦ (ā, −b)`, the real scalars, the real part, the norm form `Re(x x̄)` |
| `octI`, `octJ`, `octL` | the imaginary units `i`, `j` of `ℍ ⊂ 𝕆` and the doubling unit `ℓ = (0, 1)` |
| `Albert` | `J = H₃(𝕆)`: three real diagonal entries and the upper entries in positions `(0,1)`, `(0,2)`, `(1,2)`; only the real vector space structure is inherited |
| `albertMatrix`, `octMatrixMul`, `albertCoordinates` | the Hermitian octonionic matrix of an element, the product of two such matrices, and the coordinates read back from a matrix |
| `jordanMul` | the Jordan product `x ∘ y = (xy + yx)/2` |
| `albertUnit` | the identity matrix `e` |
| `albertTrace` | the matrix trace, with `tr e = 3` |
| `tracePairing` | the trace form `⟨x, y⟩ = tr(x ∘ y)` |
| `quadraticMap` | `U_x y = 2 x ∘ (x ∘ y) − (x ∘ x) ∘ y`, the analogue of `y ↦ x y x` |
| `IsAtom` | `p ∘ p = p` and `tr p = 1`; by `isAtom_iff_primitive` these are the primitive idempotents |
| `IsDensity` | a state of `J`: a square of trace one |
| `maximallyMixed` | the state `e/3` |
| `JordanSubalgebra` | a real subspace of `J` containing `e` and closed under `∘` |
| `Generates` | the only unital Jordan subalgebra containing the given elements is `J` |
| `JordanSubalgebra.IsSpecial` | a unital Jordan subalgebra `B` is special: for some `d > 0` a real-linear, injective map `f` from `B` into the complex `d × d` matrices has Hermitian values, `f e = 1` and `f(x ∘ y) = ½(f x · f y + f y · f x)` |
| `Word n` | a list of pairs (test index, outcome), head first; `true` is "yes" |
| `outcomeEffect` | `p_i` for "yes", `e − p_i` for "no" |
| `wordProbability` | `tr(U_{q_m} ⋯ U_{q_1} ρ)`, the Lüders updates of the outcomes applied in order, without renormalisation |
| `wordsUpTo n L` | words in `n` tests of length at most `L` |
| `yesFirstUpTo L` | words in four tests of length at most `L` whose first outcome is "yes" on test `0` |
| `outcomeOperator`, `wordOperator` | `P_i` or `1 − P_i`; the palindromic product `Q_1 ⋯ Q_{m−1} Q_m Q_{m−1} ⋯ Q_1` (`1` for the empty word) |
| `ProjectiveRepresentation n 𝕜 H` | a Hilbert space `H` over an `RCLike` field `𝕜` (any dimension), an orthogonal projection of any rank per test, and a state: a `𝕜`-linear functional on bounded operators, real and nonnegative on positive operators, `1` at the identity |
| `ProjectiveRepresentation.probability` | the real part of `φ(wordOperator P w)` |
| `ProjectiveRepresentation.HasDensityState` | for a representation on `ℂ^d` (`EuclideanSpace ℂ (Fin d)`): `φ(T) = tr(σ T)` for a positive operator `σ` with `tr σ = 1` (`LinearMap.trace`) |
| `RightQuaternionicStructure H` | on a real inner product space `H`: a right action of `ℍ` by bounded real operators and an `ℍ`-valued inner product, right `ℍ`-linear in its second argument, Hermitian, with real part the real inner product |
| `RightQuaternionicStructure.linearOperators` | the bounded `ℍ`-linear operators, defined as the commutant of the right action |
| `QuaternionicRepresentation n S` | an `ℍ`-linear orthogonal projection per test and a state on the `ℍ`-linear operators (real-linear, nonnegative on positive operators, `1` at the identity) |
| `QuaternionicRepresentation.probability` | `φ(wordOperator P w)` |
| `AlgebraicModel n A` | a real `*`-algebra `A`, a self-adjoint idempotent per test, and a real-linear functional that is Hermitian, nonnegative on every `x* x` and `1` at `1` |
| `AlgebraicModel.probability` | `φ(wordOperator P w)` |
| `NoRepresentationOn p ρ W` | no real or complex representation (scalar field in `Type`, carrier in `Type v`), no quaternionic representation and no algebraic model (carriers in `Type v`) agrees with `wordProbability p ρ` on all of `W` |
| `overlap`, `triangle`, `doublePair` | the thirteen traces of four atoms: `o_ij = ⟨p_i, p_j⟩`, `R_ijk = ⟨p_i ∘ p_j, p_k⟩`, and `t_1, t_2, t_3` |
| `fourPointInvariant` | the four-point invariant `𝒜`, the polynomial of core equation `eq:A:Acal52` in those traces, with `ω_r = t_1 + t_2 + t_3 − 2 t_r` |
| `rankOne` | `v v†` for `v ∈ 𝕆³` |
| `quadrupleM` | the maximiser `M`: `v_A = (1,0,0)`, `v_B = (1,√2,0)/√3`, `v_C = (1,i,1)/√3`, `v_D = (1,j,ℓ)/√3` |
| `quadrupleS` | the rational configuration `S`, in coordinates (diagonal; upper entries): `p_A = diag(1,0,0)`, `p_B = ½(1,1,0; 1,0,0)`, `p_C = ⅓(1,1,1; −i,1,i)`, `p_D = ⅓(1,1,1; −j,−ℓ,−jℓ)` |

## The compared declarations

### `no_representation_of_generates`

Meaning: if atoms `p_1, …, p_n` generate `J`, then for every `ρ ∈ J` no real, complex or quaternionic
representation and no algebraic model reproduces `wordProbability p ρ` on all words.

Paper: core `thm:bridgeJ`, the no-go sentence; `cor:fp:noideal` for four atoms, through
`fourPoint_criterion`.

Definitions: `IsAtom`, `Generates`, `NoRepresentationOn` and those it uses.

Gaps: the paper says "from any state"; the Lean statement allows any `ρ ∈ J`. Quaternionic Hilbert
spaces are realised as real ones with a right `ℍ`-structure. Representation states are `𝕜`-linear on
all bounded operators; for `𝕜 = ℝ` this admits states that are not Hermitian, a wider class than the
paper's. Algebraic models are an addition. Each of these strengthens the statement. The equivalence of
conditions (1) to (3) of `thm:bridgeJ` is `albert_criterion`.

### `linear_separator_of_generates`

Meaning: for generating atoms there are `L`, a finite set `W` of words of length at most `L`,
coefficients `c` and `γ > 0` such that `∑_{w ∈ W} c_w · value(w) ≥ 0` in every real, complex and
quaternionic representation and `≤ −γ` for the Albert probabilities from every state.

Paper: core `thm:bridgeJ`, last sentence; `cor:bri:finite`(a).

Definitions: `IsAtom`, `Generates`, `ProjectiveRepresentation`, `QuaternionicRepresentation`,
`IsDensity`, `wordProbability`.

Gaps: algebraic models are not covered (the development proves the inequality for them,
`wordFunctional_nonnegative_on_algebraic_models`). The existential sits inside the universe
parameter `v`, so as stated the inequality may depend on `v`; the proof takes it from the
universe-free `uniformMomentSeparator_generating_atoms`, so one inequality serves every universe. No value of `L`, `W`, `c` or `γ` is given; the paper
gives none either. The real and complex cases name `ℝ` and `ℂ` rather than every `RCLike` field. Part
(b) of `cor:bri:finite` is proved but not compared (`uniformHilbertSeparator_exceptionalWeight`,
`exceptionalWeight_no_uniform_margin`).

### `seven_steps_exclude`

Meaning: for four atoms generating `J`, no representation or algebraic model reproduces from `e/3`
every word of length at most seven whose first outcome is "yes" on test `0`, and none reproduces from
`p 0` every word of length at most six.

Paper: core `thm:cer:uniform`(a).

Definitions: `NoRepresentationOn`, `maximallyMixed`, `yesFirstUpTo`, `wordsUpTo`.

Gaps: the paper's hypothesis is `𝒜 > 0`; the Lean statement uses `Generates p`, which is equivalent by
`fourPoint_criterion`. Test `0` is the paper's `A`. Algebraic models are an addition. Part (b), a
positive margin, is not compared. Words are all lists of outcomes, reduced or not, as in the paper.

### `six_step_model`

Meaning: for four atoms generating `J`, some representation on `ℂ¹²` reproduces from `e/3` every word of
length at most six.

Paper: core `prop:cer:universalsix`, first sentence.

Definitions: `ProjectiveRepresentation`, `wordsUpTo`, `maximallyMixed`.

Gaps: the paper also describes the model (a mixture of two quaternionic quadruples with block
projections of rank two) and draws the consequence that no linear equality on words of length at most
six separates the table. Neither is in the compared statement; both are proved in the development
(`MatchingModels.prop_cer_universalsix_witness`, `MatchingModels.no_classI_linearEq_le_six`, and `MatchingModels.no_classI_linearIneq_le_six` for inequalities).

### `least_separating_length`

Meaning: for four atoms generating `J`, the set of `L` for which no real, complex or quaternionic
representation on a Hilbert space in `Type` reproduces from `e/3` every word of length at most `L` has
least element `7`.

Paper: core "`L_min = 7`", in `thm:cer:uniform` and `prop:cer:universalsix`.

Definitions: `ProjectiveRepresentation`, `QuaternionicRepresentation`, `wordsUpTo`.

Gaps: carriers are restricted to `Type`, and algebraic models are not part of the set. The paper
defines `L_min` without a universe restriction; the development proves the same minimum for Hilbert
spaces in every universe (`AlbertChallenge.Bridge.least_separating_length_all_universes`, not
compared). `L = 0` is not in the set, since every representation
matches the empty word.

### `fourPoint_criterion`

Meaning: for any four atoms, `𝒜 ≥ 0`, and `𝒜 > 0` exactly when they generate `J`.

Paper: core `thm:fourpoint`, parts (i) and (iii).

Definitions: `fourPointInvariant` and the thirteen traces, `Generates`.

Gaps: parts (ii) (`𝒜 = 0` exactly when the atoms lie in a copy of `H₃(ℍ)`) and (iv) (normal form and
the associator formula) are not compared; the development proves them (`thm_fourpoint`). `𝒜` is the
polynomial of `eq:A:Acal52`, which the paper uses as the definition of `𝒜`.

### `quadrupleM_spec`

Meaning: the four elements of `quadrupleM` are atoms, `𝒜(M) = 4/19683`, and `𝒜 ≤ 4/19683` for all four
atoms.

Paper: core `prop:max`, the bound and the value at the maximiser.

Definitions: `quadrupleM`, `rankOne`, `fourPointInvariant`.

Gaps: the lower bound `0 ≤ 𝒜` is in `fourPoint_criterion`. Uniqueness of the maximiser up to an
automorphism of `J` and the traces at `M` are not compared; the development proves them (`prop_max`,
`maximizerConfig_traces`).

### `quadrupleS_spec`

Meaning: the four elements of `quadrupleS` are atoms and `𝒜(S) = 1/5832`.

Paper: core, the paragraph on the configurations `M` and `S` in the section on finite certificates (no
label of its own).

Definitions: `quadrupleS`, `fourPointInvariant`.

Gaps: the traces of `S` are not compared. That `S` generates `J` follows from this theorem and
`fourPoint_criterion`.

### `three_atoms`

Meaning: three atoms never generate `J`, and from every state some representation on `ℂ³` reproduces
every word.

Paper: core `prop:three`.

Definitions: `IsAtom`, `Generates`, `IsDensity`, `ProjectiveRepresentation`.

Gaps: the paper says the three atoms lie in a copy of `H₃(ℂ)` and the model uses rank-one projections;
the statement records only the carrier `ℂ³`. The representation may depend on the state. The
development's `complexTripleContract_holds` has the rank-one form.

### `zero_invariant_model`

Meaning: if four atoms have `𝒜 = 0`, then from every state some representation on `ℂ⁶` reproduces every
word.

Paper: core, the paragraph after `cor:fp:noideal`; for four atoms a case of `thm:bridgeJ`, (1) ⇒ (2).

Definitions: `IsAtom`, `fourPointInvariant`, `IsDensity`, `ProjectiveRepresentation`.

Gaps: the statement does not say that the atoms lie in a copy of `H₃(ℍ)` or that the projections have
rank two. By `fourPoint_criterion` the hypothesis `𝒜 = 0` covers every quadruple that does not
generate `J`. In the development
(`fourPoint_zero_c6_representation`) the projections are fixed and only the density matrix depends on
the state; the compared statement lets the whole representation depend on the state. For every
non-generating family, `albert_criterion` gives fixed projections on `ℂ⁶` or `ℂ²⁴`.

### `albert_criterion`

Meaning: for any finite family of atoms `p_1, …, p_n` (any `n`, including `0`), each of three
conditions is equivalent to `¬ Generates p`: (a) some unital Jordan subalgebra containing every `p_i`
is special (`JordanSubalgebra.IsSpecial`); (b) there are `d ∈ {6, 24}` and a representation `M₀` on
`ℂ^d` such that for every state `ρ` some representation `M` on `ℂ^d` with `M.projection = M₀.projection`
and a density-operator state reproduces every word from `ρ`; (c) for some state `ρ`,
`NoRepresentationOn.{0} p ρ Set.univ` fails, that is, some real or complex representation, some
quaternionic representation or some algebraic model with carrier in `Type` reproduces every word
from `ρ`.

Paper: core `thm:bridgeJ`, the equivalence of (1), (2) and (3); the model class is (I).

Definitions: `IsAtom`, `Generates`, `JordanSubalgebra`, `JordanSubalgebra.IsSpecial`,
`ProjectiveRepresentation`, `ProjectiveRepresentation.HasDensityState`, `IsDensity`,
`NoRepresentationOn`.

Gaps: (a) asks for some subalgebra containing the atoms rather than the generated one (equivalent,
by restriction), and "special" is witnessed by complex Hermitian matrices of finite size; the paper's
"special" for a Euclidean Jordan algebra is the operator form (a Jordan algebra of self-adjoint
operators on a complex Hilbert space). That a subalgebra special in the operator form is not `J`
follows from `albertJordanHom_eq_zero`, which is not part of this statement; the printed theorem with
operator-form speciality is proved but not compared (`AlbertChallenge.Bridge.printed_albert_criterion`,
and in every universe `AlbertChallenge.Bridge.proper_iff_hasClassIModel` and
`nativeOperatorSpecial_iff_proper`). (b) is stronger than the
printed (2) in two ways: `d` is `6` or `24`, and the quantifier order is "∃ `d`, ∃ projections, ∀ `ρ`"
(only the density operator depends on the state), where the printed (2) lets the dimension depend on
`ρ`. (c) is restricted to carriers in `Type` and also admits algebraic models, which the printed (3)
does not mention; since every representation in the paper's sense with carrier in `Type` is one of
the Challenge's, the printed (3) for such carriers implies (c), and for carriers in any universe
`no_representation_of_generates` gives the implication (3) ⇒ not generating. With theorems 1 and 2,
which give the two sentences after the list, the statement yields the printed theorem for every
finite family of atoms. Atoms are trace-one idempotents (equivalent to the paper's primitive
idempotents by `isAtom_iff_primitive`).

### `isAtom_iff_primitive`

Meaning: for every `p ∈ J`, `IsAtom p` (`p ∘ p = p` and `tr p = 1`) holds if and only if `p ∘ p = p`,
`p ≠ 0`, and `p` is not `q + r` for idempotents `q`, `r` with `q ≠ 0`, `r ≠ 0` and `q ∘ r = 0`.

Paper: core, section on the setting: "the primitive idempotents are the atoms, or pure states".

Definitions: `IsAtom`, `jordanMul`, `albertTrace`.

Gaps: orthogonality of two idempotents is stated as `q ∘ r = 0`, the standard Jordan-algebra notion
(for idempotents of `J` it is equivalent to `tr(q ∘ r) = 0`, which is not stated). The equivalent
description of an atom as a minimal nonzero idempotent is not stated in that form.

### Gaps common to all compared statements

- `IsAtom` is "trace-one idempotent". The paper defines an atom as a primitive idempotent; the two
  agree by the compared theorem `isAtom_iff_primitive`.
- `jordanMul` is not shown in the Challenge to satisfy the Jordan identity; the development proves it
  (`NativeAnalysis.jordan_identity`).
- The coordinates of `Albert` differ from the paper's `(ξ; x₁, x₂, x₃)`: the paper's triple is the Lean
  upper triple `(x₃, conj x₂, x₁)`.
- `RightQuaternionicStructure` assumes `InnerProductSpace ℝ H`; completeness is assumed where it is
  used. Its `ℍ`-valued inner product is not used by any proof.
- Real and quaternionic representation states need not be symmetric on non-self-adjoint operators;
  word operators are self-adjoint, so this changes no word value.
- The edge cases of each definition (zero spaces, `n = 0`, the empty word, `ρ` not a state) are
  listed in the README under "Scope of the formal statements".
