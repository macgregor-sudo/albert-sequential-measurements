# Schedule mixtures and spin-factor tables

Scope notes on the Lean proofs of core Proposition 6.13, Proposition 4.14(b) and Theorem 4.11(a).

Core Proposition 6.13(b) is `AlbertSequential.MatchingModels.prop_cer_schedule_b` in `ScheduleMatchingMixture`. It quantifies over every finite normalized mixture of strictly positive block weights. Each block is the standard complex six-dimensional representation of a quaternionic window, evaluated at normalized matrix trace. The target is the native table of four Albert atoms with positive four-point invariant in the state `e/3`. For each such mixture a mismatch occurs among the words of length at most five or the two specified seven-letter words. The proof uses the rank-one round-trip identity to force zero variance across blocks, then recovers the invariant from the signed probabilities. For 6.13(a), `prop_cer_schedule_a` constructs one complex 12-dimensional model for both the shorter words and every sign pattern on the chosen schedule. The fixed pairing coordinate controls the only term with two full four-label factors.

For core Proposition 4.14(b), `spinSeparationQutritTable_mem_finiteComplex` gives a specific table realized by the three coordinate projections and the maximally mixed complex qutrit. Each projection has probability one third. Two distinct successive yes outcomes have probability zero. `spinSeparationQutritTable_not_mem_spinFactor` excludes the resulting all-word table in every finite-dimensional formally real spin factor with its actual Jordan product and canonical density. `SpinFactorClifford` constructs Hermitian Clifford generators for an arbitrary finite-dimensional spin factor, yielding the all-menu inclusion. `spinFactorTableUnion_ssubset_finiteComplex_three` combines it with the qutrit witness in the same space of three-test tables.

`UnitalJordanProduct.exists_projectiveRepresentation_of_zero_complement_weight` constructs a finite complex all-word realization after discarding an orthogonal ideal of zero state weight, given a faithful finite Hermitian embedding of the retained ideal. This is the conditional realization step in core Theorem 4.11(a).

Checks, from the repository root with the pinned toolchain:

```sh
lake build +ScheduleMatchingAffinity +ScheduleMatchingMixture +SpinFactorClifford +GeneralEJAGenerated +Robustness.SevenStepCalibration +QuaternionicHellySix +HilbertTraceComplex +HilbertTraceReal +HilbertTraceQuaternionic
lake env lean tools/checks/ScheduleMixture.lean
lake env lean tools/checks/SpinTables.lean
lake env lean tools/checks/FixedSchedule.lean
lake env lean tools/checks/SpinJordanCalibration.lean
lake env lean tools/checks/HellyTrace.lean
```

These files restate both signed round trips, the qutrit table, the sharp Helly number and selected supporting results, and print the axioms of the declarations involved.
