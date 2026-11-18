# Statements

This file accounts for each compared declaration of [`src/Challenge.lean`](../src/Challenge.lean) (namespace `AlbertChallenge`):
what it says, which paper result it formalizes, the definitions it uses, and the known differences
between the paper's statement and the Lean statement. It ends with the theorem map of the whole
repository and the gap of each entry. Paper results are cited by their LaTeX label, prefixed "core"
or "companion"; the [README](../README.md) gives their printed numbers and the status of every
numbered statement.

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
(b) of `cor:bri:finite` is not formalized.

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
defines `L_min` without a universe restriction. `L = 0` is not in the set, since every representation
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
follows from `albertJordanHom_eq_zero`, which is not part of this statement. (b) is stronger than the
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

## Theorem map with gaps

Each row names a paper result proved in the repository but not compared, its Lean declarations
(without the prefix `AlbertSequential`; names beginning with `LemmaB` are in that top-level
namespace; in a cell, a name without a dot after a dotted one has the same prefix), how the Lean
statement relates to the printed one ("same", "different route", "narrower" or "different form", as in the README's status table) and, for narrower
ones, what is missing. The twelve compared theorems are above. [MODULES.md](MODULES.md) locates every
module.
The [README](../README.md) gives the plain meaning of each row and the printed number of each label.

| Paper label | Lean declaration(s) | Relation | What the Lean statement lacks |
|---|---|---|---|
| core `lem:set:support` | `native_positive_zero_pairing_support` | narrower | stated for `V = J` only |
| core `def:ideal` | `PositiveInstruments.IsIdealTest` | narrower | finite positive forms only |
| core `thm:ideal` | `PositiveInstruments.idealTest_iff_quadraticRepresentation` | narrower | part (b), on Hilbert spaces |
| core `def:idealmodel` | `HilbertProjectiveData`, `QuaternionicProjectiveData`, `AlgebraicProjectiveData` | same | |
| core `def:memorymodel` | `IsNormalizedFiniteCPModel`, `RealFiniteKrausModel` | same | |
| core `thm:bridgeJ` | compared: `AlbertChallenge.albert_criterion`, `AlbertChallenge.no_representation_of_generates`, `AlbertChallenge.linear_separator_of_generates`; in the development's terms `AlbertChallenge.Bridge.albert_criterion_bridge`, `algebraicProjective_not_matches_generating_atoms`, `HilbertModelSeparation.uniformHilbertSeparator_generating_atoms`, `cor_helly_operational_if` | different form | see `albert_criterion` above: (2) stronger, (3) in `Type` with algebraic models admitted; (3) in any universe by theorem 1; operator-sense speciality by `albertJordanHom_eq_zero`; the assembly of the printed theorem is not a Lean declaration |
| core, definition of atoms | `AlbertChallenge.isAtom_iff_primitive`, `NativeAnalysis.isAtom_iff_primitive` | same | see `isAtom_iff_primitive` above |
| core `lem:bri:gns` | `cyclicHilbertModel`, `cyclicHilbertModel_probability` | same | |
| core `lem:bri:null` | `allHistoryNullContract` | narrower | the null-set part only; the step from `E(X) = Z²`, `θ(X) = 0` and matching to the vanishing of `π(Z)π(P_t)Ω` is not part of this declaration |
| core `lem:purity` | `purityResidual_threeHistories`, `NativeAnalysis.native_corner_long_probability` | narrower | the vanishing in `J` for an outcome that is an atom of `J`; the printed lemma allows an outcome primitive in the generated subalgebra |
| core `lem:bri:lift` | `hasSequentialEffectLift_orbit_corner`, `hasSequentialEffectLift_reflection` | same | |
| core `lem:bri:orbit` | `nativeOrbitSpan_iff_generated` | narrower | for tests that are atoms of `J`; the printed lemma allows tests primitive in the generated subalgebra |
| core `prop:bri:eta` | `exists_generatedCyclicJordanMap` | narrower | gaps named in the core margin note |
| core `lem:bri:state` | `FaithfulHermitianJordanEmbedding.exists_unique_positive_trace_representative`, `suppliedEmbeddingStateTransport` | narrower | an embedding must be supplied; general `V` |
| core `prop:field` | `HilbertProjectiveData.complexExtensionModel_probability`, `HilbertProjectiveData.quaternionExtensionModel_probability`, `cyclicHilbertModel_probability`, `HilbertProjectiveData.cyclicHilbert_finite`, `QuaternionicProjectiveData.cyclicHilbert_finite_of_real`, `complexification_finiteDimensional`, `quaternionification_finiteDimensional` | narrower | parts (b), (c); in (a) each inclusion is a construction, the equalities of classes are not stated |
| core `cor:bri:finite` | `HilbertModelSeparation.uniformHilbertSeparator_generating_atoms` | narrower | part (b) |
| core `prop:three` | `complexTripleContract_holds` | different route | |
| core `def:traces` | `fpOverlap`, `fpTriangle`, `fpDoublePair1`, `fpOmega1` and companions | same | |
| core `prop:fp:tracerel` | `rankThree_fourIdempotent_trace_relation`, `albert_fourAtom_trace_relation` | narrower | general rank-three `V` |
| core `thm:fourpoint` | `thm_fourpoint`, `lemma_A_normal_nondegenerate` | same | |
| core `prop:windowdet` | `prop_windowdet`, `prop_windowdet_zero`, `lemma_A_window_generated` | same | |
| core `cor:fp:rank` | `cor_fp_rank` | same | |
| core `lem:fp:access` | `triangleDefect_primitive_decomposition`, `symmetricTripleDefect_primitive_decomposition` | narrower | the final composition |
| core `thm:tetra` | `tetrahedronEngine` | narrower | the Hilbert-space form |
| core `prop:Dacal` | `prop_Dacal_poly`, `tetrahedronDiscriminant_eq_overlap_mul_fourPointInvariant` | same | |
| core `cor:fp:noideal` | `LengthSeven.Uniform.noideal_algebraic`, `noideal_hilbert`, `noideal_rightQuaternionic`, `FiveTest.cor_fp_noideal` | same | |
| core `prop:max` | `prop_max`, `maximizerConfig_traces`, `fourPointInvariant_maximizerConfig` | same | |
| core `lem:fp:DeltaWmax` | `lem_fp_DeltaWmax` | same | |
| core `cor:fp:maxmixed` | `cor_fp_maxmixed` | same | |
| core `thm:cer:uniform` | `LengthSeven.Uniform.uniform_lengthSeven_e3_algebraic`, `uniform_lengthSix_pA_algebraic`, `MatchingModels.lMin_eq_seven`, `Ends.uniform_b`, `Ends.uniform_b_pA` | narrower | `L_min` is taken over Hilbert spaces in `Type`; the exclusions hold in every universe; different route; (b) is proved with a finite witness set and no explicit `δ`; Lean adds a margin from `p_A` at length six |
| core `prop:cer:universalsix` | `MatchingModels.prop_cer_universalsix_witness`, `prop_cer_universalsix_c12`, `lMin_eq_seven`, `no_classI_linearEq_le_six`, `no_classI_linearIneq_le_six` | narrower | `L_min` is taken over Hilbert spaces in `Type`; the exclusions hold in every universe; Lean also proves the inequality form |
| core `cor:cer:everystate` | `BlockB.cor_cer_everystate`, `BlockB.everystate_lengthSeven_algebraic` | same | the bundle quantifies over carriers in `Type` |
| core `lem:cer:recon` | `finiteGram_iff_finiteRealModel`, `AlgebraicProjectiveData.finiteGram` | different route | |
| core `lem:cer:short` | `LengthSeven.WalkForm.shortRules_of_table`, `LengthSeven.lengthSeven_e3_rules` | same | |
| core `lem:cer:tablemodel` | `LengthSeven.TableModel.tableModel`, `tableModel_lemmaB` | narrower | proved for the words of `𝒲₂₈` |
| core `lem:cer:gram28` | `LengthSeven.LemmaA.lemmaA_of_gram28Hyp`, `lemmaA`, `LengthSeven.TableModel.tableModel` | narrower | proved for the words of `𝒲₂₈` |
| core `lem:cer:gram7` | `LengthSeven.LemmaA.lemmaA` | narrower | the printed formulas are not stated |
| core `lem:cer:negative` | `LemmaB.gram_Xi`, `LemmaB.Xi_mem_span_uhat`, `LemmaB.no_psd_realisation_traces` | different route | |
| core `thm:cer:seven` | `BlockB.seven_M_e3_algebraic`, `seven_S_e3_algebraic`, `seven_M_pA_algebraic`, `seven_S_pA_algebraic` | different route | |
| core `prop:horizon` | `MatchingModels.prop_cer_universalsix_c12`, `lMin_eq_seven` | narrower | a `ℂ¹²` model, not the equal mixture of `Q₊`, `Q₋` |
| core, companion `thm:eleven` | `BlockB.thm_eleven_with_overlaps`, `BlockB.thm_eleven_full`, `Ends.Eleven.elevenBase_card`, `elevenBase_hist`, `BlockB.elevenUnion_card`, `MatchingModels.overlap_pos_lt_one_of_fourPoint_pos`, `BlockB.elevenLedgerWords_eq_elevenBase` | different form | the list is defined from an encoding of the 1,673 relation applications; the formal proof checks its count and length histogram; that this list is the list printed in the companion's appendix is not a Lean theorem |
| core `prop:Dfails` | `MatchingModels.dfails_length_le_two`, `dfails_thirteen_traces`, `dfails_tetra_dtet`, `dfails_purity_defect`, `dfails_length_three_deviations` | same | |
| core `prop:cer:noequality` | `AppF.prop_cer_noequality_a`, `MatchingModels.no_classI_linearEq_le_six` | narrower | parts (b), (c); in (a) projective equalities are defined by finite-dimensional real vector states and the list of equivalents reaches representations only through algebraic models in `Type` |
| core `rem:cer:fivestep` | `HorizonFive.horizonFive_projectiveEquality`, `HorizonFive.horizonFiveClause` | same | the hypothesis is vanishing on real finite-dimensional representations with vector states, implied by being a projective equality |
| core `prop:robust` | `FiniteRealWordFunctional.separation_forces_error` | narrower | the second assertion |
| core `prop:cer:nearideal` | `calibrated_positive_instrument_word_error_le` | narrower | an abstract trace-norm setting |
| core `lem:five:coord` | `lem_five_coord`, `lem_five_coord_gen` | same | |
| core `thm:pentad` | `pentadF_isAtom`, `pentadF_generatesAlbert`, `pentadDrop_generated_finrank`, `thm_pentad_a`, `LengthSeven.Uniform.pentad_b_algebraic`, `FiveTest.thm_pentad_b` | same | |
| core `lem:five:helly` | `lem_five_helly` | same | |
| core `prop:arity` | `prop_arity` | same | |
| core `cor:helly` | `cor_helly_geometric`, `cor_helly_special`, `cor_helly_sharp`, `AlbertChallenge.Bridge.cor_helly_classI`, `cor_helly_operational_iff_unconditional`, `cor_helly_operational_iff`, `albertUniformSeparation` | narrower | the operational sentence is stated for carriers in `Type`, with algebraic models admitted as representations and subfamilies indexed by injections `Fin k → Fin n`, `k ≤ 5` |
| core `thm:cp69` | `NativeAnalysis.exists_nativeGeneral_real_simulation`, `nativeTaggedBlock_card` | same | |
| core `cor:ins:nohalf` | `NativeAnalysis.exists_nativeNoHalf_real_simulation`, `exists_nativeFourIdempotent_mixed_instrument_68` | same | |
| core `prop:ins:lower` | `native_CP_dimension_at_least_six`, `NativeAnalysis.exists_nativeFourIdempotent_mixed_instrument_68` | same | |
| core `lem:ins:factor` | `exists_kraus_channel_factorization` | narrower | existence only, not the formula |
| core `prop:ins:sharpdilation` | `exists_supported_sharpDilation` | narrower | the real clause in general |
| core `cor:ins:sharpalbert` | `NativeAnalysis.exists_nativeSharp_instrument_2_17n_add_one`, `exists_nativeNoHalf_sharp_instrument_34n` | same | |
| core `prop:markov` | `frameClassicalWordProbability_eq`, `frameMemory_card`, `mutuallyUnbiasedFrames_qutrit_word_statistics` | same | |
| core `lem:A:slots` | `jordanMul_slotElem01_slotElem12` | narrower | parts (b), (c) |
| core `lem:A:restrict` | `complexRestrictionContract_holds` | same | |
| core `lem:A:three` | `lemma_A_three` | different route | |
| core `lem:A:normal` | `lemma_A_normal`, `lemma_A_normal_nondegenerate` | different route | |
| core `lem:A:Aform` | `sparseFourConfigOct_traces`, `sparseFourConfigOct_fourPointInvariant` | narrower | the forms `G`, `s` |
| core `lem:A:degenerate` | `lemma_A_degenerate` | same | |
| core `lem:A:zero` | `lemma_A_zero_of_factor`, `lemma_A_zero_of_quat` | narrower | part (a) |
| core `lem:A:generate` | `lemma_A_generate_three`, `lemma_A_generate_four` | same | |
| core `lem:A:window` | `lemma_A_window_generated`, `prop_windowdet_zero` | narrower | part (a) and `P_{gW} g = g P_W` |
| core `lem:A:clifford` | `localUnit_volume_eq_half_reverse`, `localUnit_volume_square` | same | |
| core `prop:cer:quatpair` | `MatchingModels.prop_cer_quatpair_a`, `prop_cer_quatpair_b`, `prop_cer_quatpair_c_line`, `prop_cer_universalsix_witness` | same | |
| core `lem:five:sub` | `lem_five_sub` | same | |
| core `lem:fiv:facts` | `lem_fiv_facts_a`, `lem_fiv_facts_b` | same | |
| core `lem:five:line` | `lem_five_line` | same | |
| core Definition F.1, corner relations | `CornerRelations` | same | |
| core `lem:tet:corner` | `jordanHom_map_quadratic`, `jordanHom_map_triple` | narrower | the subalgebra `C`; maps on all of `J` only |
| core `thm:tetra:algebraic` | `tetrahedronEngine` | same | |
| core `cor:tet:special` | `albertJordanHom_eq_zero`, `proper_iff_special` | narrower | the case `C ≠ J` |
| core `thm:tet:albert` | `albertJordanHom_eq_zero` | different route | |
| core `thm:glennie` | `AppF.thm_glennie`, `thm_glennie_normSq`, `thm_glennie_perm`, `thm_glennie_eq_zero_iff`; values at `M`, `S`: `AppF.glennie_maximizer_value`, `glennie_fixedS_value`, `glennie_fixedS_ABD_C`, `glennie_fixedS_ACD_B`, `glennie_fixedS_BCD_A` | different form | `F` is defined as the sum of the nine placements of the polarisation of `ψ`; its identification with the coefficient `[s²t²u²]` is not a Lean theorem |
| companion `lem:cer:sound` | `AlgebraicProjectiveData.evaluatedSquareIdentity_sound` | narrower | the identity is a hypothesis about its value in the given model, not a parsed identity in `ℝ[ℤ₂^{*n}]` (which implies it); the prefixed form |
| companion `thm:cer:sevenrobust` | `BlockB.thm_cer_seven_b_M_algebraic`, `thm_cer_seven_b_S_algebraic`, `robustFunctionalM`, `robustFunctionalS`, `LengthSeven.Robust.counterT_M`, `counterT_S` | different form | Lean proves every printed property (support, values `−γ`, ℓ¹ bounds) for its own functional, assembled from an encoded certificate; that this is the functional of the appendix, and the appendix's clauses (i)–(iv) on its support, are not Lean theorems |
| companion `prop:robust:sqrt` | `real_square_root_instrument_witness_bound`, `complex_square_root_instrument_witness_bound`, `quaternionic_square_root_instrument_witness_bound` | same | |
| companion `prop:eq:five` | `HorizonFive.horizonFive_projectiveEquality`, `HorizonFive.horizonFiveClause` | same | as core `rem:cer:fivestep` |
| companion `prop:so:kernel` | `AppF.red1_jordan`, `red1_injective`, `E2_jordanHom_kills_K`, `redq_jordan`, `redq_unit`, `redq_eq_zero_iff`, `AppF.Dq.instRing`, `AppF.E2_not_special` | narrower | the dimensions 18 and 45 |
| companion `cor:so:residual` | `AppF.cor_so_residual`, `cor_so_residual_of_atoms`, `cor_so_residual_linearFunctional` | same | |
| companion `lem:five:reflect` | `FiveTest.quad_lift` | narrower | the reflected quadruple only, in span form |
| companion `thm:five:refl` | `FiveTest.thm_five_refl`, `LengthSeven.LemmaA.lemmaA_budget` | different route | |
| companion `prop:five:short` | `FiveTest.five_short_p0`, `five_short_e3`, `Ends.five_short_b_exists`, `five_short_b_p0_exists` | same | the explicit value of the margin given after the proof is not formalized; Lean adds a margin from `p_0` at length ten |
| companion `cor:five:minimum` | `MatchingModels.cor_five_minimum_p0_isLeast_classI`, `cor_five_minimum_e3_isLeast_classI` | narrower | `L_min` is taken over Hilbert spaces in `Type`; the exclusions hold in every universe |
| companion `prop:ins:reachable` | `nativeReachableIdealityObligations`, `native_reachable_sharpness`, `native_reachable_certainty_ideality` | same | |
| companion `prop:ins:compactness` | `stationaryKraus_global_iff_local_finite_menus`, `stationaryKraus_finite_menu_error_gap`, `stationaryKraus_finite_positive_error_gap`, `stationaryKrausRealization_iff_choi` | same | stated for Kraus realizations, equivalent to CP realizations by `stationaryKrausRealization_iff_choi` |
| companion `lem:cer:h5:refl` | `HorizonFive.reflectionClassConsistency`, `HorizonFive.reflectionContraction` | same | |
| companion `lem:cer:h5:lift` | `HorizonFive.recognitionThroughFivePos` | same | (`HorizonFive.not_recognitionThroughFive` refutes an internal form that allowed `n = 0`, not the printed lemma) |
| companion `lem:cer:h5:seven` | `HorizonFive.transferThroughSeven` | same | |
| companion `prop:windowlaw` | `complexWindow_laplace_integrand` | not formalized | only the deterministic identity behind its Laplace transform is proved |
| companion `prop:cer:Seleven` | `fixedSConstructedWitness`, `fixedSConstructedWitness_model_nonnegative`, `fixedSConstructedWitness_horizon`, `fixedSConstructedWitness_native_le`, `fixedSConstructedWitness_forces_error` | different form | Lean builds the functional from its own encoding of the purity occurrences; that these are the occurrences of the companion's appendix, and that its words lie in the eleven-step lists, are not Lean theorems |
