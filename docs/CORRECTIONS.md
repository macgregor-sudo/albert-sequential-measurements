# Corrections in version 2 of the papers

Version 2 of the core paper and of the companion paper corrects the passages of version 1 listed
here; each paper's changelog lists the same items. This file gives the computations and examples
behind them and the Lean declarations that prove the corrected statements. Section numbers are
those of version 2, which agree with version 1.

## Core Section 5.4, double-pair traces and Bargmann invariants

Version 1 said, in the paragraph "Holonomies at a vertex", that the double-pair traces are the real
parts of the Bargmann invariants of four pure states. Each double-pair trace is the mean of two such
invariants.

For complex rank-one projections `A`, `B`, `C`, `D`, call a *cycle* the real trace of an ordered
product of the four. Write `x`, `y` and `z` for the cycles in the orders ABCD, ABDC and ACBD. In the
notation of Definition 5.2,

```text
t₁ = (x + y)/2      ω₁ = t₂ + t₃ − t₁ = z
t₂ = (y + z)/2      ω₂ = t₁ + t₃ − t₂ = x
t₃ = (x + z)/2      ω₃ = t₁ + t₂ − t₃ = y
```

For the first identity, expand `(AB + BA)(CD + DC)` and take the real trace. The four summands ABCD,
ABDC, BACD and BADC have real traces `x`, `y`, `y` and `x`, by cyclic rotation and conjugate
reversal, and division by four gives the mean. The other rows follow by interchanging labels. For
dyads the trace of a cycle is the product of the four successive inner products, including the
closing one.

Example: the projections onto the real directions (1,0,0), (1,1,0), (1,2,0), (1,3,0) have
`(x, y, z) = (21/100, 28/100, 12/100)`. The double-pair traces are `49/200`, `1/5` and `33/200`, and
the combinations `ω₁, ω₂, ω₃` are `12/100`, `21/100` and `28/100`. `python3 tools/replay_bargmann_example.py`
recomputes this example in exact arithmetic.

Lean: `Bargmann.doublePairTrace_dyads` and `Bargmann.omega_dyads` for dyads; for finite-rank
operators on an arbitrary complex Hilbert space, `Bargmann.Hilbert.hasSum_double`,
`Bargmann.Hilbert.doubleTrace_eq` and `Bargmann.Hilbert.omega_eq`, where the diagonal is absolutely
summable in every Hilbert basis and its sum does not depend on the basis. No statement or proof of
the paper used the sentence.

## Core Section 2, the tetrahedron statistic

Version 1 stated `𝒟 = 0` in every representation in the paragraph "The tetrahedron". Theorem 5.9
assumes the corner relations and `P_j ≠ 0`, and without them the statement fails:
`MatchingModels.dfails_tetra_dtet` gives `𝒟 > 0` for the representation of Proposition 6.16. With
the hypotheses, `hilbert_fpTetraDtet_eq_zero` proves `𝒟 = 0`.

## Core Appendix B.11, maximum versus total exceptional weight

Version 1 said, in the proof of Corollary 4.16, that the set of states whose largest exceptional
weight is at least `ε` is not convex when `m ≥ 2`. For two normalized weights whose sum is the unit
weight, this set is the whole state space for `ε ≤ 1/2`, not convex for `1/2 < ε ≤ 1`, and empty for
`ε > 1`; so it need not be convex, and for some `ε` it is. The proof uses the set where the total
exceptional weight is at least `ε`, which is convex by linearity, and is unchanged. Lean:
`convex_totalWeightCut`, `convex_twoSummandWeightStates_max_iff`.

## Companion Section 2.5, signs of the fixed-S matrices

Version 1 identified `L_i`, `L_j`, `L_{e₃'}` with the anticommuting matrices `C₁`, `C₂`, `C₃` of
the model of core Proposition 6.16, and the volume element `𝒱` with `1 ⊗ σ_x`. The printed spinor
generators and the signs of the fixed-S columns use different basis conventions: in the coordinates
that intertwine them, left multiplication by `i`, `j`, `ℓ` acts by `−C₁`, `−C₂`, `−C₃`, and `𝒱` by
`−1 ⊗ σ_x`. `NativeAnalysis.fixedS_positive_i_incompatible` shows that the version 1 signs cannot
hold simultaneously. The signed identification intertwines the projections and every word
(`NativeAnalysis.fixedSLeftProjections_intertwine`, `NativeAnalysis.fixedSLeftProbability_eq_dfails`).
The three-step deviation `4/243` is unchanged.

## Companion Section 4.3, the cost of the reflected witness

The bound `|u| + ν(u) ≤ 10` applies to the continuation `u` after the initial "yes" on `A`, which
defines the anchored state `ζ = P_A Ω`; version 2 says so. `FiveTest.reflectedRobustTailTerms_wordBudget`
checks the bound for the continuation words, `FiveTest.reflectedAnchoredTerms_horizon` adds the
initial "yes" on `A` and obtains five-test words of length at most eleven, and
`FiveTest.reflectedFiveTestFunctional_support` checks the merged support. The threshold stated after
Proposition 4.3 is `FiveTest.reflectedFiveTest_robust_hilbert`,
`FiveTest.reflectedFiveTest_robust_quaternionic` and `reflectedFiveTestMargin_gt`.

## Companion Section 4.6, cohomology of the full simplex

Version 1 said that the ordinary cohomology of the full simplex with constant coefficients vanishes;
it vanishes in positive degrees, and in degree zero the cocycles on a nonempty simplex are the
constants. For the five atoms in the displayed order the four-point invariant on the facets is
`(0, 0, 0, 0, 1/5832)`, whose alternating coboundary is `1/5832`, so this cochain is not a cocycle.
Lean: `companionCConfig_coboundary`, `fullSimplex_positiveCocycle_iff_coboundary`,
`fullSimplex_zeroCocycle_iff_constant`.

## Companion, proof of Corollary 6.5, multiplicities

Version 1 gave the eigenvalues `0` and `1 − o_ij` eight times each. For a repeated test, `o_ij = 1`,
they coincide and `0` has multiplicity sixteen (`NativeAnalysis.nativeCornerYesEffect_charpoly`,
`NativeAnalysis.nativeCornerYesEffect_charpoly_of_eq`). The rank bound is unchanged.

## Companion Appendix A.2, the coefficient records of Theorem 2.4

Theorem 2.4 states the existence of the robust functionals with the printed margins and bounds, and
the released exact coefficient records witness it. Version 1 of Appendix A.2 stated a rule for keeping
or deleting the final `q` in the left words of defect vectors that differs from the records: among the
7,962 residual occurrences of each configuration it disagrees at 936, comprising 18 contributions to
`W₃` and 918 to `R₃`. Entry 301 is an example. Its pairing ends its left history with `D`; removing
that `D` keeps the Gram identity, because the residual lies in the range of the self-adjoint
projection `D`, but it can change the probability bucket and hence the coefficient.

Applying the version 1 rule at those entries, with the other elimination choices fixed, gives margins
`4466849/169869312` for `M` and `394539295/18345885696` for `S` instead of the printed ones. Version 2
refers to the records, whose totals are the printed ones; Theorem 2.4 is unchanged. Symmetric
elimination choices can also give different coefficients with the same table contribution and bucket
masses, so a certificate is identified by its coefficient rule as well as by its margins.

Lean: `LengthSeven.Robust.robust_coefficient_recorded_formula` and the module
`PaperRobustSourceCorrespondence`, which proves the coefficient formula of the records and checks the
alternative reduction at entry 301 and the symmetric choices at entry 41. Exact replays:
`python3 tools/replay_residual_occurrences.py` and `python3 tools/check_residual_source_choices.py`,
run from the repository root.

## Companion Appendix A.4, the 1,673 applications

Version 1 called the 1,673 applications of the eleven-step construction distinct. They are counted
with repetition, at one base, and 1,118 of the history, base and suffix triples are distinct; for
instance, two different contractions give the same triple with history `A`, base `A` and suffix `D`.
After the triples are expanded into measured words, the base family has 2,041 distinct words and the
union over the four bases 8,164. The witness keeps repeated occurrences and their coefficients.
Lean: `BlockB.ledgerApplications_occurrences`, `BlockB.ledgerApplications_distinct_card`,
`fixedSPrinted_occurrence_has_ledger_application`, `fixedSPrintedWitness_support_deposited`.
