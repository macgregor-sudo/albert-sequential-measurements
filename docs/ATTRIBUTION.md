# Attribution of adapted code

The Lean software is licensed Apache-2.0 ([LICENSE](../LICENSE)). Its Lean code, mathematics and text were
produced by AI systems (see the [README](../README.md)), except for three groups of adapted files: the
declarations adapted from Physlib, listed below, were written by their upstream author; the
modules under `src/Glennie/` are adapted from the contributor's earlier Palomar entry
PALOMAR-2026-10-16-000013, whose production account is recorded there; and the ten modules under
`src/CompositionAlgebras/` are adapted from `ehrlich-b/composition-algebras`, whose copyright
holder is named below. All three sources are licensed Apache-2.0. This file names each file, its origin and what was changed;
[`THIRD_PARTY_NOTICES`](../THIRD_PARTY_NOTICES) repeats the notices in plain text.

## Physlib

Source: Physlib, https://github.com/leanprover-community/physlib, commit
`08a6c1b5b8e6db340547142c3f7047635128c786`, licensed Apache-2.0, copyright Tom Ole Diem. Physlib's
licence is Apache-2.0, the licence of this repository; its full text is the root [`LICENSE`](../LICENSE). Thanks to
Tom Ole Diem and the Physlib contributors.

“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to
Robert Hooke, 1676.

| File | Origin | Declarations adapted | Changes |
|---|---|---|---|
| `src/RealJordanFundamental.lean` | `PhyslibAlpha/ProbabilisticTheory/JordanOrderUnit/Quadratic/Fundamental.lean` | `cyclic_mulLeft_commutator`, `innerDerivation_add_left`, `innerDerivation_mul`, `innerDerivation_comm`, `tripleOperator`, `triple_eq_V_apply`, `innerDerivation_sub_right`, `innerDerivation_mul_left`, `tripleOperator_comm`, `tripleOperator_quadRep_step`, `V_quadRep_eq_quadRep_triple`, and `quadRep_fundamental_apply`, `quadRep_fundamental` (renamed `quadraticRepresentation_fundamental_apply`, `quadraticRepresentation_fundamental`) | only the cyclic polarisation and the derivation and triple arguments for the fundamental formula of the quadratic representation are kept; ambient class weakened to `NonUnitalNonAssocCommRing`; local operator definitions; imports, namespace and two endpoint names changed; other proof bodies unchanged; no Physlib import remains |
| `src/JordanPowerAssociativity.lean` | `PhyslibAlpha/ProbabilisticTheory/JordanOrderUnit/Power/Associative.lean` | `commute_mulLeft_sq`, `commute_mulLeft_apply`, `linearized_mul_sq`, `square_mul_jpow`, `mulLeft_jpow_add_two`, `fundamental_mulLeft_commute_pow`, `commute_mulLeft_pow`, `pow_add` | stated for a concrete Jordan product structure instead of an abstract unital ring; explicit powers use that structure's unit through a wrapper, with no ambient multiplication or unit instance; `jpow_*` renamed `elementPower_*`; proof bodies otherwise unchanged; no Physlib import remains |
| `src/RealJordanOperators.lean` | `PhyslibAlpha/ProbabilisticTheory/JordanOrderUnit/Operator.lean` and `.../Quadratic/Triple.lean` | definitions `mulLeft`, `quadRep`, `innerDerivation`, `jordanTriple`; lemmas `mulLeft_apply`, `quadRep_apply`, `innerDerivation_apply`, `innerDerivation_swap`, `jordanTriple_outer_comm`, `jordanTriple_diag` | renamed (`mulLeft` as `leftMultiplication`, `quadRep` as `quadraticRepresentation`), with `a * a` in place of `a ^[2]` and the `_apply` lemmas proved by `rfl`; `innerDerivation_swap` and `jordanTriple_outer_comm` keep the upstream proofs; no Physlib import remains. Copies of these two files at the commit above are not kept; the comparison was made against a local Physlib snapshot of October 2026 with the same author header, and the file is attributed as adapted |

All three files keep the upstream copyright notice and author line in their headers:

```text
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license
Authors: Tom Ole Diem
```

`src/UnitalJordanProduct.lean`, `src/JordanProductQuadratic.lean` and `src/EuclideanJordanForm.lean` are written
for this development and follow the conventions of the same Physlib files; a scan of every
development file against the Physlib sources found declarations matching Physlib bodies only in the
three files above.

## PALOMAR-2026-10-16-000013

Source: "Finite Observations and Recognition of the Compact Albert Algebra", Palomar entry
PALOMAR-2026-10-16-000013, version 1, by the same contributor:
https://github.com/macgregor-sudo/compact-albert-recognition/tree/40d3b344180d9ddb78aaa2876873377c1e631515,
licensed Apache-2.0.

The fifteen modules under `src/Glennie/` are adapted from that entry: `Native`, `Native/AlgebraLaws`,
`Native/LinearMaps`, `Native/RealConjugation`, `Native/Triality`, `BasicLaws`, `Obligations`,
`Automorphism`, `Hilbert`, `Compactness`, `ScalarRotation`, `Diagonalization`, `NativeSquareConeR01`,
`NativeQuadraticPositiveR01` and `Compact/OperationalPhi`. They define the compact octonions and the
Albert algebra as pairs of quaternions, the product and trace, and prove elementary laws, real
conjugation, triality transport, compactness of the automorphism maps, diagonalisation and the square
cone. `src/Glennie/Native.lean` is that entry's `Glennie/Native.lean` with two `Nat` instances and the
auxiliary declaration `Albert.extExplicit` removed, one proof shortened and the header replaced. The
other fourteen descend from a later private version of the same code by the same contributor.
None of that entry's compared conclusions is used as a hypothesis here.

Two further Palomar entries by the same contributor are related but contribute no file, and are
cited here as earlier registered work:
PALOMAR-2026-09-13-000001 (`macgregor-sudo/albert-frame-triple-invariants` at `dd06ef5`, split Albert
frame invariants), which is an ancestor of code in PALOMAR-2026-10-16-000013, and
PALOMAR-2026-10-29-000034 (`macgregor-sudo/tight-39-code` at `46f01c1`, tight 39-point code), which
shares the `Glennie/` ancestry.

## Composition algebras

Source: https://github.com/ehrlich-b/composition-algebras, commit
[`98d4437ce1bfd8d042b8383e0cfe28ec3e595eee`](https://github.com/ehrlich-b/composition-algebras/tree/98d4437ce1bfd8d042b8383e0cfe28ec3e595eee),
registered in Palomar as PALOMAR-2026-08-29-000018 v1, licensed Apache-2.0, copyright Bryan Ehrlich
(as stated in the retained upstream headers). Thanks to Bryan Ehrlich.

The classification of the simple summands of rank three in core Theorem 4.11
(`HurwitzRankThreeClassification`) uses `CompositionAlgebra.hurwitz_classification`, Hurwitz's
classification of the finite-dimensional Euclidean composition algebras over `ℝ`, from these files. The upstream toolchain is Lean `v4.33.0`, with Mathlib at
`db584cd6d46c92f209a44c0f1c829460d327499d`. The source archive SHA-256 is
`707a08e715beb738eae294b87d67ffd06d530819e9f6038132a2d49a48fb0852`.

The ten adapted `.lean` files mirror their upstream paths under `src/CompositionAlgebras/`:
`Composition/Defs`, `Composition/Doubling`, `Composition/CayleyDickson`, `Octonions`,
`OctonionTrace`, `OctonionModule`, `Composition/Instances`, `Composition/Isomorphisms`,
`Composition/Hurwitz`, and `Composition/Classification`. Each file is adapted whole, with all its
declarations. Each keeps its original Apache-2.0 copyright and author header and identifies its
changes. All ten were adapted to the Lean module system.
`Octonions` imports the direct replacement of a deprecated Mathlib import. `Composition/Isomorphisms`
removes redundant tactic combinators and simp arguments. The original Apache-2.0 text is included at
[`src/CompositionAlgebras/LICENSE`](../src/CompositionAlgebras/LICENSE); its SHA-256 is
`cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30`. Upstream has no `NOTICE` file.
The project uses these files with its existing Lean and Mathlib 4.36.0 pins.

## Related registered work by others (no code used)

The registered Palomar entries below treat related mathematics; no file or declaration of them is
used here, and this development proves its own versions of the overlapping results. The core paper
cites the three `ehrlich-b` repositories.

| Entry | Repository and commit | Registered theorems |
|---|---|---|
| PALOMAR-2026-08-22-000006 v1 | `ehrlich-b/sequential-products-lean` at `9c6d92f5` | `TwistNormalForm.real_classification`, `TwistNormalForm.complex_classification` (sequential products on real and complex Hermitian matrix algebras) |
| PALOMAR-2026-08-21-000009 v1 | `ehrlich-b/sequential-products-lean` at `9c6d92f5` | `AlbertPowerAssoc.jpow_mul_jpow` (Albert's power-associativity theorem for commutative Jordan rings carrying a real-module structure) |
| PALOMAR-2026-08-21-000001 v1 | `ehrlich-b/sequential-products-lean` at `3c0e870e` | `WignerReal.exists_isometry_of_transProbPreserving` (real case of Wigner's theorem) |
| PALOMAR-2026-08-23-000005 v1 | `ehrlich-b/euclidean-jordan` at `58fb886d` | `KoecherAlfsenShultz.orderIso_preservesJordan` (Koecher–Alfsen–Shultz theorem) |
| PALOMAR-2026-08-23-000006 v1 | `ehrlich-b/euclidean-jordan` at `58fb886d` | `JordanSpectral.spectral_resolution_bilinear` (spectral resolution) |
| PALOMAR-2026-08-29-000001 v1 | `ehrlich-b/euclidean-jordan` at `a0077822` | `JordanTraceForm.traceForm_comm`, `traceForm_assoc`, `traceForm_self_nonneg`, `traceForm_self_eq_zero_iff` (the Jordan trace form) |
| PALOMAR-2026-08-29-000008 v1 | `ehrlich-b/euclidean-jordan` at `a83407e4` | `JordanFramePeirce.frameBlock_isInternal`, `finrank_frameBlock_diag` (Peirce decomposition relative to a frame) |
| PALOMAR-2026-11-11-000008 v1 | `stalex444/herstein-jordan-homomorphisms` at `34dffa8a` | `JordanPrime.jordan_onto_prime` and five further theorems (Herstein's theorem on Jordan homomorphisms of associative rings onto prime rings) |

## Mathlib

The development depends on Mathlib `v4.36.0` (commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`,
Apache-2.0) as a package; no Mathlib file is copied or modified.

## Other public code consulted, no code used

The trace-class ideal of the Tau Ceti project, at commit
[`aa3cfad1274c06cff25f2b58848498b3c3f68d0f`](https://github.com/TauCetiProject/TauCeti/blob/aa3cfad1274c06cff25f2b58848498b3c3f68d0f/TauCeti/Analysis/OperatorIdeal/Family/TraceClass.lean)
(Apache-2.0, [licence](https://github.com/TauCetiProject/TauCeti/blob/aa3cfad1274c06cff25f2b58848498b3c3f68d0f/LICENSE)),
uses the same Lean and Mathlib revisions and provides real and complex nuclear approximation numbers.
The papers need a trace and its duality on real, complex and right-quaternionic operators; the
development builds these on its own representations (`HilbertTrace*`) and copies no code from Tau Ceti.

The repository [`Cobord/JordanAlgebra`](https://github.com/Cobord/JordanAlgebra/tree/a4b0d58554732ced63b4217200baa56be5a2c3d5),
at the revision inspected, carries no licence grant that applies; none of its code is used.
