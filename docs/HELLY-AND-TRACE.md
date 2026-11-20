# Quaternionic Helly number and positive operator traces

Scope notes on the Lean proofs of companion Proposition 4.7 and Corollary 4.8 and of core Theorem 3.3(b).

## Companion Proposition 4.7 and Corollary 4.8

In `QuaternionicHellySix`, `paperLineHellySix_controls_iso` uses the displayed six dyads and unital subalgebras Jordan-isomorphic to the standard quaternionic algebra. Every five dyads fit in such a subalgebra and the full six do not. `paperLineHelly_generated_structure` gives their centered multiplication table. The generated dimensions are seven for each five and eight for all six.

`quaternionicHelly_six_iso` applies to arbitrary sets of atoms, including infinite sets. `quaternionicHelly_isLeast` establishes the least local testing size. `quaternionicHelly_projective` realizes every finite qualifying family from every Albert density by rank-two projections and a density matrix on complex dimension six. `paperLineHellySix_projective_nonconverse` supplies the fixed-state converse counterexample.

For the upper bound the Lean proof chooses a finite basis of centered vectors and bounds the dimension of the quaternionic corner. It reaches the printed conclusions without the cited `Spin(9)` action or the Peirce-space isomorphism used in the printed proof, which are not formalized.

## Core Theorem 3.3(b), analytic prerequisites

`HilbertTraceBasis` proves Parseval and basis independence for the squared Hilbert–Schmidt mass with arbitrary basis index types. `HilbertTraceComplex` and `HilbertTraceReal` prove basis independence of the extended positive trace and summable rank-one expansions of finite-trace positive bounded operators. `HilbertTraceQuaternionic` constructs the actual right-quaternionic dyad in the real operator commutant and proves that one quarter of its real trace equals the squared norm on diagonal dyads. The modules `HilbertTraceRealIdeal`, `HilbertTraceComplexIdeal` and `HilbertTraceQuaternionicIdeal` prove the characterization of ideal trace-class instruments (`idealTest_iff_projection` in each). They verify both measured branches and the effect readout, including trivial projections, for arbitrary Hilbert dimension.

## Checks

From the repository root, with the pinned toolchain:

```sh
lake build +QuaternionicHellySix +HilbertTraceRealIdeal +HilbertTraceComplexIdeal +HilbertTraceQuaternionicIdeal
lake env lean tools/checks/RealTraceInstrument.lean
lake env lean tools/checks/ComplexTraceInstrument.lean
lake env lean tools/checks/QuaternionicTraceInstrument.lean
```

`tools/checks/HellyTrace.lean` restates the least Helly number, the eight-dimensional span and the basis independence of the real positive trace, and prints the axioms of eight declarations.
