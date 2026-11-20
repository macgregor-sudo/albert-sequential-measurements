# Modules

Every module of the repository; module `A.B` is the file `src/A/B.lean`. The default targets of
`lakefile.toml` build every module. A module marked * is imported, directly or not, by `Solution`, so
the twelve compared theorems depend on it; the others prove the further results named in the
[status ledger](../README.md#status-of-every-numbered-statement) and in
[THEOREM-MAP.md](THEOREM-MAP.md), or lemmas for them. This file only locates modules; the ledger and
the theorem map name the declarations. There are 966 modules, 214 of them marked *.

The first table groups the 524 modules of release `v1.0.0` by what they prove. The second lists the
442 modules added for release `v2.0.0`, with the numbered statements whose ledger declarations each
contains; a dash means that the module supplies lemmas, scope checks of unnumbered claims
([UNNUMBERED-CORE.md](UNNUMBERED-CORE.md), [UNNUMBERED-LATE.md](UNNUMBERED-LATE.md)) or declarations
named only in the theorem map.

## Modules of release v1.0.0

| Group | What it contains | Modules |
|---|---|---|
| Statement layer | The twelve compared statements (`Challenge`), the verbatim copy of their definitions used by the proofs (`ChallengeDefs`), the proofs (`Solution`), and the translation between the Challenge's objects and the development's (`Bridge.*`, namespace `AlbertChallenge.Bridge`). | `Bridge.Albert`*, `Bridge.AlbertHeadlines`*, `Bridge.Atoms`*, `Bridge.C12`*, `Bridge.Criterion`*, `Bridge.Exclusion`*, `Bridge.Least`*, `Bridge.Matrix`*, `Bridge.Models`*, `Bridge.Seven`*, `Challenge`, `ChallengeDefs`*, `Solution`* |
| Joins | Short compositions of earlier results: core Corollary 7.5 without its separation hypothesis and in model class (I) (`Joins.Helly`), core Remark 6.18 for projective equalities (`Joins.NoEquality`), core Theorem 6.15 with its side assertion (`Joins.Eleven`), companion Proposition 6.2 on finite menus (`Joins.Compactness`). | `Joins.Compactness`, `Joins.Eleven`, `Joins.Helly`, `Joins.NoEquality` |
| Octonions and the Albert algebra | The native coordinates of the octonions and of `J = H₃(𝕆)`, the product, trace, quadratic map, Jordan identity, automorphisms, diagonalisation, classification of idempotents (trace 0, 1, 2 or 3), square cone, Peirce decomposition relative to the diagonal frame, topology, octonion geometry (associator, cross product), and the adapted earlier layer `Glennie.*`. | `AcceptedRootAtomAdapter`*, `Defs`*, `DiagPeirceAnchor`*, `FrameSlotNormalizers`*, `GeneratedAlbertOperations`*, `Glennie.Automorphism`*, `Glennie.BasicLaws`*, `Glennie.Compact.OperationalPhi`*, `Glennie.Compactness`*, `Glennie.Diagonalization`*, `Glennie.Hilbert`*, `Glennie.Native`*, `Glennie.Native.AlgebraLaws`*, `Glennie.Native.LinearMaps`*, `Glennie.Native.RealConjugation`*, `Glennie.Native.Triality`*, `Glennie.NativeQuadraticPositiveR01`*, `Glennie.NativeSquareConeR01`*, `Glennie.Obligations`*, `Glennie.ScalarRotation`*, `HermitianCoordinates`, `NativeAlbertLaws`*, `NativeAnalysis`*, `NativeAtomCompression`*, `NativeAtomReflections`*, `NativeAtomSpanning`, `NativeAtomicExchange`, `NativeAutomorphisms`*, `NativeCubicLowerBounds`, `NativeDensityCompactness`*, `NativeDiagonalProduct`*, `NativeFirstHalfTrace`, `NativeIdempotentClassification`*, `NativeJordanIdentity`*, `NativeJordanQuadratic`*, `NativeMatrixTrace`*, `NativeNewtonCubic`, `NativeOrthogonalCorner`, `NativePeirceIdentities`*, `NativePeircePropagation`*, `NativeRecoveredCoordinates`*, `NativeSquareCone`*, `NativeSupport`*, `NativeTopology`*, `NativeTracePartitions`*, `NativeTraceRiesz`, `OctonionGeometry`*, `OctonionRealCoordinates` |
| General Jordan algebras | Results for real Jordan algebras that do not mention `J`: quadratic and triple operators and the fundamental formula (adapted from Physlib), power associativity (adapted from Physlib), unital products, and for finite-dimensional formally real (Euclidean) Jordan algebras with an associative inner product the spectral resolution, Peirce decomposition and fusion rules, primitive idempotents and their refinement, the canonical and normalized trace, the cone of squares, ideals and the decomposition into orthogonal simple ideals, Riesz representation of states, and transport of these structures along Jordan homomorphisms. | `EuclideanJordanForm`*, `EuclideanJordanQuadraticPositive`, `EuclideanJordanSquareCone`*, `EuclideanPrimitiveCorner`, `FormalRealityCanonicalTrace`, `FormalRealityPositiveForm`, `FormalRealitySimpleFactors`, `FormalRealitySpectral`, `JordanAssociativeSpectral`*, `JordanCubicCritical`, `JordanGeneratedAlgebra`*, `JordanHomTransport`*, `JordanIdealOrthogonal`, `JordanIdealProjections`, `JordanIdealRestriction`, `JordanIdealTransport`, `JordanIdeals`, `JordanMappedIdealProducts`, `JordanNormalizedTrace`, `JordanPeirceFusion`, `JordanPeircePositiveMultiplication`*, `JordanPowerAssociativity`*, `JordanPrimitivePairing`, `JordanPrimitiveRefinement`, `JordanPrimitiveSpectralResolution`, `JordanPrimitiveTransport`, `JordanProductQuadratic`*, `JordanProductTransport`, `JordanQuadraticSplit`, `JordanRegularTrace`, `JordanSimpleFactors`, `JordanSimpleIdealDecomposition`, `JordanSpectralResolution`*, `JordanSquareConeTransport`, `JordanSquareLifts`*, `JordanStateRiesz`, `JordanTripleTransport`*, `NativePeirceHalfOperators`, `OrthogonalSubspaceComponents`, `PeirceHalfOperators`, `PrimitiveCompressionSymmetry`, `RealJordanFundamental`*, `RealJordanOperators`*, `RealJordanPairing`, `RealJordanPeirce`*, `UnitalJordanProduct`* |
| Words and models | Words, their chronological effects and probabilities; the development's model classes (real and complex Hilbert-space representations, quaternionic representations in two equivalent presentations, algebraic models); passage between the classes and fields, including finite dimension; the universal algebra of projections; word reduction and relabelling. | `BinaryTestReduction`, `BoundedWordEffects`*, `ChronologicalWords`*, `ComplexProjectiveExtension`, `EffectLiftEmbedding`*, `FieldExtensionFiniteDimension`, `FourCopyOperatorEmbedding`*, `FourCopyQuaternionicStructure`*, `FreeProjectionMoments`*, `HilbertClassIConstructor`*, `HilbertOperatorAlgebra`*, `HilbertProjectiveData`*, `Interfaces.AlgebraicReconstruction`*, `Interfaces.Geometry`*, `Interfaces.InstrumentsAndCompactness`*, `Interfaces.MeasuresAndRobustness`, `Interfaces.OperationalBoundaries`*, `Interfaces.SeparationAndConverse`*, `Interfaces.WordsAndCertificates`*, `LinearRelationDescent`*, `NativeTestReduction`, `NativeWordDuality`*, `NativeWordPositivity`*, `NativeWordSpan`, `ProjectionMomentDescent`*, `ProjectionMomentRealization`*, `ProjectionPolynomialEvaluation`*, `ProjectiveWordProbabilities`*, `QuaternionicClassIConstructor`, `QuaternionicOperatorAlgebra`*, `QuaternionicPresentationEquivalence`*, `QuaternionicProjectiveData`*, `QuaternionicProjectiveExtension`*, `QuaternionicRightLinearOperators`*, `RealPairCompression`*, `RealPairOperators`*, `ReducedWords`*, `RightQuaternionicHilbert`*, `UniversalProjectionAlgebra`*, `WordReduction`, `WordRelabelling` |
| Reconstruction and the no-go theorem | From a model that reproduces every word: the cyclic real Hilbert representation, null vectors and purity, lifts of conjugated effects, the reflection-orbit span, the Jordan homomorphism on the generated subalgebra; the algebraic tetrahedron identity in a possibly nonunital associative target, the corner relations, and the theorem that every Jordan homomorphism from `J` into an associative algebra is zero. | `AlbertCyclicReconstruction`*, `AlbertExceptionality`*, `AlgebraicProjectiveNoGo`*, `CornerAlgebra`*, `CyclicFiniteDimension`, `CyclicHilbertCompletion`*, `CyclicHilbertModel`*, `CyclicHilbertRepresentation`*, `CyclicInnerProduct`*, `CyclicOperatorNorm`, `CyclicOrbitReconstruction`*, `CyclicWordQuotient`*, `CyclicWordVectors`*, `GeneratedCyclicReconstruction`*, `LocalVolume`*, `NativeOrbitLifts`*, `NativeReflectionOrbit`*, `NativeWordPurity`*, `OrbitExpectation`*, `OrbitJordanDescent`*, `OrbitLinearDescent`*, `OrbitPairPurity`*, `OrbitPeirceLifts`*, `OrbitProjectionLabels`*, `PositiveBilinearNull`*, `PositiveFunctionalNull`*, `PurityResiduals`*, `SequentialEffectLifts`*, `SupportedPurityLeaves`*, `TetrahedronEngine`*, `TetrahedronRelabeling` |
| Finite separation | Compactness of the admissible moment functionals (the moment data of algebraic models) and of finite tables, and from it one finite word functional that is nonnegative on every model and at most `−γ` on the Albert table from every state; real word functionals and the error bound they force. | `AffineEffectClosure`, `AlbertUniformSeparation`*, `AlgebraicMomentBinding`*, `AlgebraicSeparationAssembly`*, `CompactConstraints`*, `CompactConvexHull`, `CompactMomentSeparation`*, `FiniteCoordinateExtraction`*, `FiniteTableCompactness`*, `FiniteTableSeparation`*, `HilbertModelSeparation`, `MomentTopology`*, `RealGramTopology`*, `RealWordFunctionals`, `StateTableMembership` |
| Constructed separators | An explicit constructor of finite separating functionals from residual telescopes of the purity, Clifford and holonomy defects, with structural length bounds; it supplies the functional of core Theorem 6.15(c), and for the configuration `S` an explicit functional supported on words of length at most eleven, nonnegative on every algebraic model and at most `−7/828` on the Albert table from every state (`fixedSConstructedWitness`, `fixedSConstructedWitness_native_le`; companion Proposition 2.6). | `AllCornerPairVectors`, `CliffordDefectData`, `CliffordDefectPairings`, `CliffordVolumeDefect`, `ConstructedCornerTelescope`, `ConstructedLeafCalibration`, `CornerContractionDefects`, `CornerCubicVectors`, `CornerDataVolumeVectors`, `CornerHolonomyDefects`, `CornerMixedVectors`, `CornerNumericalData`, `CornerOperatorPolynomials`, `CornerPrimitiveBinding`, `CornerScalarResidualBounds`, `CornerScalarResiduals`, `CornerSquareVectors`, `FiniteCornerWitness`, `FixedSConstructedWitness`, `FixedSCornerConditions`, `FixedSCornerDiscriminants`, `FixedSCornerScalars`, `FixedSNativeLeaves`, `FixedSSumBounds`, `HermitianDefectTelescope`, `HolonomyCliffordBinding`, `HolonomyPathCombinations`, `HolonomyPaths`, `HolonomyPrimitiveVectors`, `NativeScalarAccess`, `NormalizedHolonomyDefects`, `PrimitivePurityDecomposition`, `PrimitiveResidualOccurrences`, `PrimitiveVectorBuilders`, `PrimitiveWordSupport`, `PurityOccurrenceRelabelling`, `PurityVectorExpressions`, `ResidualOccurrenceAlgebra`, `ResidualPathLinearExtension`, `ResidualSeparatorBounds`, `ResidualTelescopeSeparator`, `ScalarCliffordTelescope`, `WordAmplitudeAlgebra`, `WordAmplitudeCombinations` |
| Three and four atoms | The thirteen traces, the trace relation, the four-point invariant and its criterion, normal forms, the window determinant, the maximum and its maximiser, the configuration `S`, the models for three atoms and for four atoms with vanishing invariant, embeddings of subalgebras into complex Hermitian matrices and transport of states along them, and the coordinates of subalgebras generated by atoms. | `ComplexPositiveFactor`*, `ComplexStateCompression`*, `ComplexWindowDeterminantAndMax`*, `FixedSBinding`*, `HermitianJordanEmbedding`*, `HermitianStateTransport`*, `SubalgebraCoordsAndLine`*, `SuppliedEmbeddingStateTransport`*, `ThirteenTracesAndAform`*, `ThreeAtomAndFourPoint`* |
| Finite Gram tables | A finite table of word probabilities comes from a finite-dimensional real model exactly when its Gram matrix is positive semidefinite; realisation in Gram-rank dimensions; soundness of square identities. | `AlgebraicGramNecessity`*, `CanonicalGramTables`*, `EvaluatedSquareSoundness`, `FiniteGramEquivalence`*, `FiniteGramModel`*, `FiniteGramReconstruction`*, `GramFactor`*, `GramModelConstruction`*, `GramProjection`*, `GramRealization`*, `SelfAdjointFiniteModel`, `SelfAdjointStateGram`*, `SquarePositiveFunctional`, `VectorGramNecessity`* |
| Length seven | The uniform length-seven exclusion: short-history relations, the 406 Gram entries of the 28 path vectors (Lemma A), their identity with the comparison form entry by entry, three vectors with negative Gram determinant (Lemma B), and the assembly for every generating quadruple. | `LemmaB.Access`*, `LemmaB.Algebra`*, `LemmaB.Conclusion`*, `LemmaB.Gram`*, `LemmaB.Lemma`*, `LemmaB.Model`*, `LemmaB.PSD`*, `LemmaB.PaperChecks`, `LemmaB.Sanity`, `LemmaB.Sources`*, `LemmaB.Traces`*, `LengthSeven.Adapters`*, `LengthSeven.Basic`*, `LengthSeven.LemmaA.EntriesA`*, `LengthSeven.LemmaA.EntriesB`*, `LengthSeven.LemmaA.EntriesC`*, `LengthSeven.LemmaA.EntriesD`*, `LengthSeven.LemmaA.Instances`*, `LengthSeven.LemmaA.Main`*, `LengthSeven.LemmaA.Rules`*, `LengthSeven.LemmaA.Table`*, `LengthSeven.LemmaA.Walks`*, `LengthSeven.NativeBinding`*, `LengthSeven.OmegaControl`, `LengthSeven.ShortRules`*, `LengthSeven.TableRules`*, `LengthSeven.TableValues`*, `LengthSeven.WalkForm`*, `TableModel.Amps`*, `TableModel.Defs`*, `TableModel.EntriesAA`*, `TableModel.EntriesAB`*, `TableModel.EntriesAC`*, `TableModel.EntriesAD`*, `TableModel.EntriesBB`*, `TableModel.EntriesBC`*, `TableModel.EntriesBD`*, `TableModel.EntriesCC`*, `TableModel.EntriesCD`*, `TableModel.EntriesDD`*, `TableModel.GaugeAA`*, `TableModel.GaugeAB`*, `TableModel.GaugeAC`*, `TableModel.GaugeAD`*, `TableModel.GaugeBB`*, `TableModel.GaugeBC`*, `TableModel.GaugeBD`*, `TableModel.GaugeCC`*, `TableModel.GaugeCD`*, `TableModel.GaugeDD`*, `TableModel.Main`*, `Uniform.Corollaries`, `Uniform.Main`* |
| Matching models | The model on `ℂ¹²` through length six as a mixture of two quaternionic quadruples, its real, quaternionic and algebraic versions, no linear equality or inequality through length six, `L_min = 7`, the positive tetrahedron statistic that is not a witness, and the least lengths for five tests. | `MatchingModels.DfailsModel`, `MatchingModels.FiveTestClifford`, `MatchingModels.FiveTestLowerBound`, `MatchingModels.FiveTestMinimum`, `MatchingModels.LMinSeven`, `MatchingModels.MatrixClassIBridge`*, `MatchingModels.QuatPair`*, `MatchingModels.UniversalSix`*, `MatchingModels.UniversalSixAffinity`* |
| Certificates and margins | Positive margins (core Theorem 6.1(b) and the five-test bound), exclusion from every state, the length-eleven list and its functional, the length-seven certificates for `M` and `S` with their robust constants, and the encoded certificate data. | `BlockB.ElevenCore`, `BlockB.ElevenSupport`, `BlockB.ElevenTheorem`, `BlockB.EveryState`, `BlockB.RobustNativeMS`, `BlockB.StateSupport`, `Ends.Eleven`, `Ends.FiveB`, `Ends.Margin`, `Ends.UniformB`, `RobustCert.Assembly`, `RobustCert.DataM1`, `RobustCert.DataM2`, `RobustCert.DataM3`, `RobustCert.DataM4`, `RobustCert.DataS1`, `RobustCert.DataS2`, `RobustCert.DataS3`, `RobustCert.DataS4`, `RobustCert.Exact`, `RobustCert.Formal`, `RobustCert.RobustM`, `RobustCert.RobustS`, `RobustCert.Table` |
| Equalities, second order and Glennie's identity | No equality through five steps, characterisations of projective equalities, the second-order kernel near a complex subalgebra and its residual, Shestakov's identity, and Glennie's identity relating a polarised Jordan polynomial to `𝒜`, with its values at `M` and `S`. | `AppF.ExactModel`, `AppF.GlennieIngredients`, `AppF.GlennieM`, `AppF.GlennieMFinal`, `AppF.GlennieS`, `AppF.GlennieSOrders`, `AppF.SecondOrderKernel`, `AppF.SecondOrderQuotient`, `AppF.SecondOrderSpecial`, `AppF.Shestakov`, `BlockA.GlennieBimodule`, `BlockA.GlennieDefect`, `BlockA.GlennieGeneral`, `BlockA.GlennieWindowTrace`, `BlockA.SecondOrderResidual`, `HorizonFive.Assembly`, `HorizonFive.Axis`, `HorizonFive.AxisLine`, `HorizonFive.Components`, `HorizonFive.Contraction`, `HorizonFive.Final`, `HorizonFive.Groups`, `HorizonFive.JordanPoly`, `HorizonFive.Lemmas`, `HorizonFive.Passive`, `HorizonFive.RecogBase`, `HorizonFive.RecogData1`, `HorizonFive.RecogData2`, `HorizonFive.RecogData3`, `HorizonFive.Recognition`, `HorizonFive.ReflA`, `HorizonFive.Seven`, `HorizonFive.ShapeFacts`, `HorizonFive.Statement`, `HorizonFive.Symbols`, `HorizonFive.ThreeLetters`, `HorizonFive.Volume`, `HorizonFive.Window`, `HorizonFive.WordBridge`, `HorizonFive.WordFacts`, `Pending.GlennieGeneral` |
| Five tests | Five atoms that generate `J` while every four are reproduced on `ℂ⁶`; irredundant families, arity and the Helly number five; the reflected quadruple and the length-eleven bound for five tests. | `FiveTest.Budget`, `FiveTest.Compose`, `FiveTest.Main`, `FiveTest.Quad`, `FiveTest.RatAlbert`, `FiveTest.Transfer`, `PentadArityAndHelly` |
| Instruments | Ideal tests and Lüders maps for finite positive forms; completely positive realizations of the Albert statistics in dimension `17n+1` and `17n`; sharp effects with arbitrary channels and the realization in dimension `2(17n+1)`; lower bound six on the memory dimension; Choi and Kraus forms; fixed-dimension compactness and the finite-menu error gap; ideality on the reachable states; complete measurements as Markov chains and the qutrit comparison. | `BinaryKrausDilation`, `BinaryProjectionDilation`, `BinarySpectralSupport`, `CPWordProbabilities`, `ChoiCompletePositivity`, `ChoiKrausAlgebra`, `ChoiKrausEquivalence`, `ChoiParameterCompactness`, `ChoiWordContinuity`, `CompleteFrameQutritComparison`, `CompleteFrameQutritRealization`, `CompleteMeasurementMarkov`, `CompletelyPositiveFactorization`, `DefaultChoiModel`, `DegenerateSharpDilation`, `FiniteBinaryProjection`, `FiniteCPHankelRank`, `FiniteKrausSupportTransport`, `FiniteMenuCompactness`, `FiniteMenuExtension`, `FiniteSpectralSupport`, `FixedDimensionCompactness`, `IdealJordanCompression`, `IdealJordanInstruments`, `IdealTestFoundations`, `InstrumentFactorization`, `IsometricKrausCompletion`, `KrausCertaintySupport`, `KrausSupport`, `LinearMapChoi`, `LocalFiniteErrorGap`, `MeasurePrepareKraus`, `NativeCornerEffects`, `NativeCornerKrausTransition`, `NativeCornerYesKraus`, `NativeFiniteIdempotentSimulation`, `NativeFiniteInstrumentSimulation`, `NativeHalfCoordinates`, `NativeHalfExchangeMatrix`, `NativeHalfMatrices`, `NativeHalfMatrixLaws`, `NativeHalfRepresentation`, `NativeHalfSubspaces`, `NativeHalfTraceEncoding`, `NativeHankelRank`, `NativePositiveOverlapKraus`, `NativeReachableCone`, `NativeReachableDensity`*, `NativeReachableIdeality`, `NativeReachableSharpness`, `NativeReachableUpdates`, `NativeScalarKrausSources`, `NativeSharpInstrumentSimulation`, `NativeSupportedInstrumentSimulation`, `NativeTaggedAllWords`, `NativeTaggedCertaintySupport`, `NativeTaggedInitialModels`, `NativeTaggedLocalInstrument`, `NativeTaggedPieces`, `NormalizedKrausOutput`, `PaperFixedDimensionCompactness`, `PositiveMatrixCompactness`, `PositiveMeasurePrepare`, `ProjectionSupportTransfer`, `QutritFourierBases`, `QutritMutuallyUnbiasedBases`, `QutritProjectiveStatistics`, `RealFiniteKrausComplexification`, `RealFiniteKrausModel`, `RealFiniteKrausReindex`, `RealKrausBridge`, `RealMatrixComplexification`, `RealSharpDilation`, `RealSpectralSupport`, `RealSupportedSharpDilation`, `RectangularKrausFamilies`, `ReducedBinaryKrausModel`, `RepeatableBinaryDilation`, `SharpDilationFamilies`, `SharpDilationSemantics`, `SharpJordanEffects`, `StationaryCPCompactness`, `StationaryKrausSemantics`, `StationaryLinearCPModels`, `SupportedSharpDilation`, `TaggedAllWordSimulation`, `TaggedBlockMatrices`, `TaggedBlockStates`, `TaggedCertaintySupport`, `TaggedKrausFamilies`, `TaggedLinearEncoding` |
| Robustness | Perturbation bounds: generalised Lüders instruments of nearly projective effects, spectral rounding, state and amplitude errors in real, complex and quaternionic Hilbert spaces, order-unit and trace-base norms, and near-ideal instruments in an abstract trace-norm setting. | `Robustness.BoundedOperatorOrderUnit`, `Robustness.ComplexOperatorSpectralRounding`, `Robustness.ComplexificationPositivity`, `Robustness.ComplexifiedBoundedOperators`*, `Robustness.ContinuousSpectralRounding`, `Robustness.ContinuousSquareRootIdentification`, `Robustness.EffectPerturbation`, `Robustness.FaceCalibration`, `Robustness.HilbertAmplitudeErrors`, `Robustness.HilbertSquareRootModels`, `Robustness.HilbertStateNorm`, `Robustness.HilbertWordRounding`, `Robustness.OperatorSubalgebraStates`, `Robustness.OrderUnitStates`, `Robustness.PositiveInstrumentStability`, `Robustness.PositiveQuadraticCrossBound`, `Robustness.QuadraticBounds`, `Robustness.QuaternionicOperatorSpectralRounding`, `Robustness.QuaternionicSquareRootModels`, `Robustness.QuaternionicStateBounds`, `Robustness.RealHilbertComplexification`*, `Robustness.RealOperatorCalculusDescent`, `Robustness.RealOperatorDescent`*, `Robustness.RealOperatorSpectralRounding`, `Robustness.RealSpectralCorrespondence`, `Robustness.RootInstrumentWitnessBounds`, `Robustness.SpectralRoundingScalars`, `Robustness.TraceBaseNorm`, `Robustness.WitnessTransport`, `Robustness.WordContractions` |
| Checking files | Files that mainly import modules together, print axioms (`#print axioms`) or test definitions on small cases; `BlockA.Checks` also proves the non-vacuity and off-window sharpness statements for companion Corollary 3.3. | `BlockA.Checks`, `NativeControls`, `NullSpaceControls` |

## Modules added for release v2.0.0

| Module | Numbered statements |
|---|---|
| `AdaptiveWordExperiments` | — |
| `AlbertDerivationDimension` | — |
| `AlbertDerivationFrame` | — |
| `AlbertDerivationSlots` | — |
| `AlbertGeneratingOrbitTangent` | — |
| `AppF.AssociatorTriangleBinding` | — |
| `AppF.CoefficientHermitianMatrices` | — |
| `AppF.CoefficientRegularQuotient` | — |
| `AppF.GlennieCoefficient` | core Thm F.6 |
| `AppF.HermitianCoefficientKernel` | — |
| `AppF.HigherJetAssociators` | — |
| `AppF.HigherJetCoefficientAlgebras` | — |
| `AppF.HigherJetCoefficientIdeal` | — |
| `AppF.HigherJetCoefficientProduct` | — |
| `AppF.HigherJetHermitian` | — |
| `AppF.HigherJetHermitianDimensions` | — |
| `AppF.HigherJetNativeOrthogonality` | — |
| `AppF.HigherJetUniversalKernels` | — |
| `AppF.SecondOrderCoefficientIdeal` | — |
| `AppF.SecondOrderDimensions` | companion Prop 3.2 |
| `AppF.SecondOrderHermitian` | — |
| `AppF.SecondOrderQuotientImage` | — |
| `AssociativeDyadOverlap` | — |
| `BargmannDoublePair` | — |
| `BlockA.SecondOrderResidualLittleO` | companion Cor 3.3 |
| `Bridge.EJAFixedUnitary` | — |
| `Bridge.PhysicalHelly` | core Cor 7.5 |
| `Bridge.PrintedCriterion` | core Thm 4.1 |
| `Bridge.UniverseCriterion` | core Thm 4.1 |
| `Bridge.UniverseHorizon` | core Thm 6.1, core Prop 6.2, companion Cor 4.4 |
| `CanonicalIdealInstruments` | — |
| `CanonicalSupport` | core Lem 3.1 |
| `ClassicalDensityRegister` | — |
| `ClassifiedJordanFoil` | core Rem 4.15, core Cor 4.16 |
| `CompanionFreudenthalPolar` | — |
| `CompanionIltyakovAction` | — |
| `CompanionIltyakovTraces` | companion Rem 5.3 |
| `CompanionLeftMultiplicationBlockMatrices` | companion Prop 2.7 |
| `CompanionLeftMultiplicationChord` | — |
| `CompanionLeftMultiplicationEndpoint` | companion Prop 2.7 |
| `CompanionLeftMultiplicationFixedS` | — |
| `CompanionLeftMultiplicationFixedSBasis` | — |
| `CompanionLeftMultiplicationFixedSTrace` | — |
| `CompanionLeftMultiplicationNormalForm` | — |
| `CompanionLeftMultiplicationPolynomial` | — |
| `CompanionLeftMultiplicationQuaternionTrace` | — |
| `CompanionLeftMultiplicationSectors` | — |
| `CompanionLeftMultiplicationState` | — |
| `CompanionLocalGlobal` | — |
| `CompanionOctonionLeftMultiplication` | — |
| `CompanionProjectiveIncidence` | — |
| `CompanionProjectiveMetricInvariant` | companion Rem 5.2 |
| `CompanionProjectiveRayMaps` | — |
| `CompanionProjectiveTriples` | — |
| `CompanionQuadrangleGeometry` | — |
| `CompanionQuadrangleTopology` | companion Rem 5.2 |
| `CompanionQuadrangleTransitivity` | companion Rem 5.2 |
| `CompanionReadoutBudgets` | — |
| `CompanionSignedInvariant` | companion Rem 5.3 |
| `CompanionSignedInvariantGeneration` | companion Rem 5.3 |
| `CompanionThreeFrameContainment` | — |
| `ComplexDensityChord` | — |
| `ComplexGramTraceExcess` | core Rem 5.4 |
| `CompositionAlgebras.Composition.CayleyDickson` | — |
| `CompositionAlgebras.Composition.Classification` | — |
| `CompositionAlgebras.Composition.Defs` | — |
| `CompositionAlgebras.Composition.Doubling` | — |
| `CompositionAlgebras.Composition.Hurwitz` | — |
| `CompositionAlgebras.Composition.Instances` | — |
| `CompositionAlgebras.Composition.Isomorphisms` | — |
| `CompositionAlgebras.OctonionModule` | — |
| `CompositionAlgebras.OctonionTrace` | — |
| `CompositionAlgebras.Octonions` | — |
| `CyclicCornerKernel` | — |
| `CyclicCornerSevenObstruction` | core Rem 6.14 |
| `CyclicCornerSevenResiduals` | — |
| `CyclicCornerSevenTraceModel` | core Rem 6.14 |
| `CyclicGeneratedPurity` | core Lem 4.5 |
| `CyclicNativeCornerRelations` | core Lem 5.8 |
| `CyclicNullHistories` | core Lem 4.4 |
| `CyclicRangeCompletion` | — |
| `Ends.PrintedElevenList` | core Thm 6.15, companion Thm 2.2 |
| `Ends.UniformSevenMargin` | core Thm 6.1 |
| `EqualityClassIUniverses` | core Prop 6.17 |
| `EqualityFreeJordan` | core Prop 6.17 |
| `EqualityJordanIdentities` | core Prop 6.17 |
| `EqualityKernel` | — |
| `EqualityRepeatableCountermodels` | core Prop 6.17 |
| `EvenHyperplaneReflections` | — |
| `ExceptionalIdealEnumeration` | core Cor 4.16 |
| `ExceptionalWeightCuts` | — |
| `ExplicitJordanState` | core Lem 4.9 |
| `FieldDimensionExact` | — |
| `FieldDimensionTableClasses` | — |
| `FieldDimensionTableEquivalence` | core Cor 4.13, core Prop 4.14 |
| `FiniteArrowOfTime` | — |
| `FiniteArrowOfTimeCP` | — |
| `FiniteVectorTetrahedron` | — |
| `FiniteVectorTetrahedronPaper` | companion Lem 2.1 |
| `FiveTest.DenseOrbit` | — |
| `FiveTest.JordanReflection` | — |
| `FiveTest.PentadCircleInterpolation` | — |
| `FiveTest.PentadContinuousCoordinates` | — |
| `FiveTest.PentadContinuousWords` | — |
| `FiveTest.PentadPeirceAction` | — |
| `FiveTest.PentadPeirceFrequency` | — |
| `FiveTest.ReflectedBudgetArithmetic` | — |
| `FiveTest.ReflectedInterchange` | — |
| `FiveTest.ReflectionDepth` | companion Cor 4.5 |
| `FiveTest.ReflectionSubgroup` | companion Rem 4.6 |
| `FiveTest.SignedReflectionTransfer` | companion Lem 4.1 |
| `FixedSPrintedApplicationLedger` | companion Prop 2.6 |
| `FixedSPrintedWitness` | companion Prop 2.6 |
| `FixedSPrintedWitnessSupport` | — |
| `FixedUnitaryHistories` | — |
| `FixedUnitaryMatrix` | core Rem 3.5 |
| `FixedUnitaryPhysicalFields` | core Rem 3.5 |
| `FourTraceWordRelation` | core Rem 5.4 |
| `FullSimplexCohomology` | — |
| `GeneralEJAAlbertIdeal` | — |
| `GeneralEJAAssociativeCoordinates` | — |
| `GeneralEJAAssociativeEnvelope` | — |
| `GeneralEJAClassifiedTables` | core Thm 4.11, core Cor 4.13, core Prop 4.14 |
| `GeneralEJACoefficientAdjoints` | — |
| `GeneralEJACoefficientMatrixProduct` | — |
| `GeneralEJACoefficientNormalization` | — |
| `GeneralEJACoefficientRegular` | — |
| `GeneralEJAFactorEmbeddings` | — |
| `GeneralEJAFrameCoherence` | — |
| `GeneralEJAFrameColumns` | — |
| `GeneralEJAFrameCommonChart` | — |
| `GeneralEJAFrameComposition` | — |
| `GeneralEJAFrameConnectivity` | — |
| `GeneralEJAFrameDiagonalCoefficients` | — |
| `GeneralEJAFrameFusion` | — |
| `GeneralEJAFrameGlobalChart` | — |
| `GeneralEJAFrameMatrix` | — |
| `GeneralEJAFrameMatrixRealization` | — |
| `GeneralEJAFrameMatrixSurjective` | — |
| `GeneralEJAFramePeirce` | — |
| `GeneralEJAFrameProducts` | — |
| `GeneralEJAFrameProjections` | — |
| `GeneralEJAFrameRegularRepresentation` | — |
| `GeneralEJAFrameReverse` | — |
| `GeneralEJAFrameSparseProducts` | — |
| `GeneralEJAFrameTraceNormalization` | — |
| `GeneralEJAFrameTransport` | — |
| `GeneralEJAGenerated` | core Thm 4.11 |
| `GeneralEJAHigherRankReduction` | — |
| `GeneralEJALowRankClassification` | — |
| `GeneralEJAOperatorCompression` | — |
| `GeneralEJARankFourClassification` | — |
| `GeneralEJASmallMenus` | core Cor 4.13 |
| `GeneralEJASpecialFactors` | — |
| `GeneralEJATableSpeciality` | — |
| `GeneralEJAWordTransport` | — |
| `GeneralizedJordanLuders` | — |
| `GeneratedCyclicHilbertMap` | core Prop 4.8 |
| `GeneratedOrbitReconstruction` | — |
| `GeneratedOrbitUpdates` | — |
| `GeneratedPrimitiveTests` | core Def 4.10 |
| `GeneratedPurityEffects` | — |
| `GeneratedReflectionOrbit` | core Lem 4.7 |
| `GeneratingMenuStabilizer` | — |
| `GroupCertificateModels` | companion Lem 2.3 |
| `H3PrimitiveAtoms` | — |
| `H3SetHelly` | — |
| `HermitianPositiveStateExtension` | — |
| `HilbertBargmannTraces` | — |
| `HilbertTraceBasis` | — |
| `HilbertTraceBasisPairing` | — |
| `HilbertTraceCalibration` | core Prop 6.20 |
| `HilbertTraceCalibrationData` | — |
| `HilbertTraceCalibrationRounding` | — |
| `HilbertTraceCalibrationWitness` | — |
| `HilbertTraceCarrier` | — |
| `HilbertTraceComplex` | — |
| `HilbertTraceComplexEffect` | — |
| `HilbertTraceComplexIdeal` | core Thm 3.3 |
| `HilbertTraceComplexInstrument` | — |
| `HilbertTraceDensity` | — |
| `HilbertTraceEndpointProjections` | — |
| `HilbertTraceModulus` | — |
| `HilbertTraceNorm` | — |
| `HilbertTracePairing` | — |
| `HilbertTracePairingExpansion` | — |
| `HilbertTraceQuaternionic` | — |
| `HilbertTraceQuaternionicAverage` | — |
| `HilbertTraceQuaternionicBasisPairing` | — |
| `HilbertTraceQuaternionicCarrier` | — |
| `HilbertTraceQuaternionicEffect` | — |
| `HilbertTraceQuaternionicIdeal` | core Thm 3.3 |
| `HilbertTraceQuaternionicInstrument` | — |
| `HilbertTraceQuaternionicNorm` | — |
| `HilbertTraceReal` | — |
| `HilbertTraceRealEffect` | — |
| `HilbertTraceRealIdeal` | core Thm 3.3 |
| `HilbertTraceRealInstrument` | — |
| `HilbertTraceRiesz` | — |
| `HilbertTraceSandwich` | — |
| `HilbertTraceSharpIdealityNoGo` | core Rem 8.8 |
| `HurwitzNativeAlbert` | — |
| `HurwitzPeirceAdapter` | — |
| `HurwitzRankThreeClassification` | — |
| `JordanConeUnitInterior` | — |
| `JordanDensityCompactness` | — |
| `JordanExceptionalWeightLimit` | — |
| `JordanExceptionalWeightSeparator` | core Cor 4.16 |
| `JordanOperatorTables` | — |
| `JordanPrimitiveRuns` | — |
| `JordanTableFoil` | — |
| `JordanTableMixtures` | — |
| `LemmaB.AdjugateNegativeVector` | — |
| `LengthSeven.AlgebraicWalkSpace` | — |
| `LengthSeven.Gram28ScalarRules` | — |
| `LengthSeven.PhysicalScalarRules` | — |
| `LengthSeven.PrintedGramPermutation` | — |
| `LengthSeven.PrintedGramTable` | — |
| `LengthSeven.PrintedHilbertGram` | core Lem C.1 |
| `LengthSeven.PrintedPaths` | — |
| `LengthSeven.PrintedPhysicalGram` | — |
| `LengthSeven.WalkReduction` | — |
| `LengthSeven.WalkReductionComplete` | core Lem 6.6 |
| `LengthSeven.WalkReductionGuide` | — |
| `LengthSeven.WalkReductionGuideData` | — |
| `LengthSeven.WalkTolerance` | — |
| `LengthSeven.WalkTolerance.Chains` | — |
| `LengthSeven.WalkTolerance.EntriesA` | — |
| `LengthSeven.WalkTolerance.EntriesB` | — |
| `LengthSeven.WalkTolerance.EntriesC` | — |
| `LengthSeven.WalkTolerance.EntriesD` | — |
| `LengthSeven.WalkTolerance.Main` | — |
| `LengthSeven.WalkTolerance.Native` | — |
| `LengthSeven.WalkToleranceRules` | — |
| `LengthSeven.WalkToleranceSteps` | — |
| `MaximalProperSubalgebras` | — |
| `MinimalSpectralDilation` | — |
| `MinimalSpectralFrameAssembly` | — |
| `NativeAlbertTableMixtures` | — |
| `NativeCayleyChart` | — |
| `NativeCayleyHomogeneous` | — |
| `NativeCayleyManifold` | — |
| `NativeCayleyOrthogonalSphere` | — |
| `NativeCayleyOrthogonalSphereSmooth` | — |
| `NativeChronologicalComposition` | core Rem 4.2 |
| `NativeCornerLorentz` | — |
| `NativeCornerSpectralCoordinates` | — |
| `NativeCornerSpinorReflections` | — |
| `NativeFrameCoarseGraining` | — |
| `NativeFrameGeneration` | — |
| `NativeGenericGeneration` | — |
| `NativeHalfBoost` | — |
| `NativeLineFamily` | — |
| `NativeOneTestConsequences` | — |
| `NativePrintedSpinorCoordinates` | — |
| `NativePureStates` | — |
| `NativeTaggedNonprojectiveEffects` | core Rem 8.3 |
| `NativeTaggedSharpIdealityFailure` | core Rem 8.8, core Ex 8.9 |
| `OctonionicHolonomies` | — |
| `OctonionicHolonomyAlgebra` | — |
| `OctonionicHolonomyAssociative` | — |
| `OppositeCliffordIrreducible` | — |
| `OppositeCliffordVolumes` | — |
| `OptimalBinaryFrameChoice` | — |
| `OptimalProjectionFamily` | companion Prop 6.4 |
| `OptimalSharpDilation` | companion Prop 6.4 |
| `OptimalSharpMenu` | — |
| `OptimalSpectralFrames` | — |
| `PaperComplexWindowNormalForm` | core Lem A.9 |
| `PaperNormalFormGram` | core Lem A.5 |
| `PaperNormalFormPolynomial` | core Lem A.5 |
| `PaperResidualCyclic` | — |
| `PaperResidualVectors` | — |
| `PaperRobustResiduals` | — |
| `PaperRobustSourceCorrespondence` | companion Thm 2.4 |
| `PaperRobustVectors` | — |
| `PaperSharpDilationFormula` | core Lem 8.5, core Prop 8.6 |
| `PartnerVariance` | — |
| `PartnerVarianceGram` | core Rem 6.12 |
| `PartnerVariancePhysical` | — |
| `PartnerVariancePolynomial` | — |
| `PartnerVarianceTraceBinding` | core Rem 6.12 |
| `PentadInvariantIndependence` | — |
| `PositiveStateExtension` | — |
| `PrimitiveImageRank` | core Lem B.2 |
| `PrintedConfigurationTransport` | — |
| `PrintedLineCoordinates` | — |
| `PrintedSlotLaws` | core Lem A.1 |
| `ProjectiveTableMixtures` | — |
| `PurityApplicationOccurrences` | core Thm 6.15, companion Thm 2.2 |
| `PurityDistinctCount` | — |
| `QuaternionicDensityLift` | — |
| `QuaternionicFourAtomNormalForm` | core Lem A.7 |
| `QuaternionicGramReadout` | — |
| `QuaternionicHellySix` | companion Prop 4.7, companion Cor 4.8 |
| `QuaternionicSchurNewton` | — |
| `QuaternionicSchurTrace` | — |
| `RankOneWordReadout` | — |
| `RankThreeCanonicalTrace` | core Prop 5.3 |
| `RealPairJordanBlock` | — |
| `RealPairJordanSpan` | — |
| `RealPairQutrit` | — |
| `ReducedFrameResidualRank` | — |
| `ReducedRealSpectralFrames` | — |
| `ReducedSharpDilationChannels` | — |
| `ReducedSharpDilationRepeatability` | — |
| `ReducedSharpDilationSemantics` | — |
| `ReducedSharpFrameCoordinates` | — |
| `ReflectedRobustData1` | — |
| `ReflectedRobustData2` | — |
| `ReflectedRobustData3` | — |
| `ReflectedRobustData4` | — |
| `ReflectedRobustData5` | — |
| `ReflectedRobustData6` | — |
| `ReflectedRobustFunctional` | companion Thm 4.2, companion Prop 4.3 |
| `ReflectedRobustLedger` | — |
| `ReflectedRobustRecipes` | — |
| `ReflectedRobustTranscript` | — |
| `ReflectedRobustTransfer` | — |
| `ReflectedRobustUniform` | — |
| `ReflectedRobustVector` | — |
| `ReflectionGroupCertificate` | — |
| `RepeatabilityRepair` | companion Lem 6.3 |
| `Robustness.ComplexSharpDisturbance` | core Prop 6.21 |
| `Robustness.ComplexTraceProjectiveWords` | — |
| `Robustness.HilbertPreparationHull` | core Rem 6.22 |
| `Robustness.OperatorTraceCalibration` | — |
| `Robustness.PreparationCoordinates` | — |
| `Robustness.PreparationHull` | — |
| `Robustness.PreparationHullDensity` | — |
| `Robustness.QuaternionicSharpDisturbance` | core Prop 6.21 |
| `Robustness.QuaternionicTraceProjectiveWords` | — |
| `Robustness.RealSharpDisturbance` | core Prop 6.21 |
| `Robustness.RealTraceProjectiveWords` | — |
| `Robustness.RoundedTraceInstrument` | — |
| `Robustness.SevenStepCalibration` | — |
| `Robustness.SharpDisturbance` | — |
| `Robustness.SignedTraceMass` | — |
| `ScheduleMatchingAffinity` | core Prop 6.13 |
| `ScheduleMatchingMixture` | core Prop 6.13 |
| `ScheduleMatchingRationalCoordinates` | — |
| `ScheduleMatchingRationalForm` | — |
| `ScheduleMatchingRationalInvolution` | — |
| `ScheduleMatchingSectorField` | — |
| `ScheduleMatchingSectorMatrices` | core Prop 6.11 |
| `ScheduleMatchingSectors` | — |
| `SharpDilationCertaintyDisturbance` | — |
| `SharpDilationChannelFrame` | — |
| `SharpDilationRank` | — |
| `SingleAtomQubit` | — |
| `SpinFactorClifford` | core Prop 4.14 |
| `SpinFactorTables` | — |
| `SpinorEffectSpectrum` | — |
| `StationaryDimensionPadding` | — |
| `SubalgebraCornerTransport` | core Lem F.2 |
| `TableModel.CliffordComparison` | — |
| `TableModel.CliffordCoordinates` | — |
| `TableModel.CliffordGramFactor` | core Lem 6.7 |
| `TableModel.CliffordNativeGram` | core Lem 6.7 |
| `TableModel.CliffordVolumeCoordinates` | — |
| `TableModel.CliffordVolumeDet` | — |
| `TableModel.CliffordWalkSpace` | — |
| `TableModel.WalkSpace` | — |
| `TableModel.WalkSpaceRelations` | — |
| `TableModel.WalkUpsilon` | core Lem 6.8 |
| `TaggedDilationDefect` | — |
| `TaggedDilationDefectCorollaries` | companion Cor 6.5, companion Cor 6.6 |
| `TaggedDilationDefectSpectrum` | core Rem 8.3 |
| `TetrahedronHilbert` | core Thm 5.9 |
| `TetrahedronSubalgebraObstruction` | core Cor F.4 |
| `TracePolynomialSupport` | — |
| `TracialCornerKernel` | — |
| `TwoAlbertPurityFailure` | core Rem 4.12 |
| `TwoAlbertTableMixture` | core Rem 4.12 |
| `UnsharpQutritExample` | core Ex B.1 |
| `WindowProbabilityAlbertGroup` | — |
| `WindowProbabilityAlbertInvariance` | companion Prop 5.1 |
| `WindowProbabilityAlbertRiesz` | — |
| `WindowProbabilityAlbertRieszCone` | — |
| `WindowProbabilityAlbertRieszHomogeneity` | — |
| `WindowProbabilityAlbertWindowLaw` | companion Prop 5.1 |
| `WindowProbabilityChart` | — |
| `WindowProbabilityChartBinding` | — |
| `WindowProbabilityChartMeasure` | — |
| `WindowProbabilityChartTransform` | — |
| `WindowProbabilityComplexAmbient` | companion Prop 5.1 |
| `WindowProbabilityGaussian` | — |
| `WindowProbabilityGaussianRank` | — |
| `WindowProbabilityGaussianUnitary` | — |
| `WindowProbabilityGramCandidate` | — |
| `WindowProbabilityGramCongruence` | — |
| `WindowProbabilityGramDensity` | — |
| `WindowProbabilityGramLaw` | — |
| `WindowProbabilityGramPowerCandidate` | — |
| `WindowProbabilityGramPowerLaw` | — |
| `WindowProbabilityGramPowerTilt` | — |
| `WindowProbabilityGramTilt` | — |
| `WindowProbabilityHermitianHaar` | — |
| `WindowProbabilityIntegrals` | — |
| `WindowProbabilityInvariant` | — |
| `WindowProbabilityLaplace` | — |
| `WindowProbabilityPiDensity` | — |
| `WindowProbabilityPureState` | — |
| `WindowProbabilityQuaternionicAtoms` | — |
| `WindowProbabilityQuaternionicLaw` | — |
| `WindowProbabilityQuaternionicRelative` | companion Prop 5.1 |
| `WindowProbabilityQuaternionicSample` | — |
| `WindowProbabilityQuaternionicSymmetry` | — |
| `WindowProbabilitySpectralAngularWeight` | — |
| `WindowProbabilitySpectralChart` | — |
| `WindowProbabilitySpectralDerivative` | — |
| `WindowProbabilitySpectralFlag` | — |
| `WindowProbabilitySpectralFlagCharts` | — |
| `WindowProbabilitySpectralFlagEvaluation` | — |
| `WindowProbabilitySpectralFlagOrder` | — |
| `WindowProbabilitySpectralFlagPartition` | — |
| `WindowProbabilitySpectralFlagProjection` | — |
| `WindowProbabilitySpectralFlagSectors` | — |
| `WindowProbabilitySpectralGramSupport` | — |
| `WindowProbabilitySpectralGramWeight` | — |
| `WindowProbabilitySpectralJacobian` | — |
| `WindowProbabilitySpectralJacobianFactor` | — |
| `WindowProbabilitySpectralLinearization` | — |
| `WindowProbabilitySpectralOrderedRadial` | — |
| `WindowProbabilitySpectralPowerMarginal` | — |
| `WindowProbabilitySpectralPowerPublished` | — |
| `WindowProbabilitySpectralPowerRadial` | — |
| `WindowProbabilitySpectralPowerSimplex` | — |
| `WindowProbabilitySpectralPowerSymmetric` | — |
| `WindowProbabilitySpectralProduct` | — |
| `WindowProbabilitySpectralPublishedDensity` | — |
| `WindowProbabilitySpectralRadial` | — |
| `WindowProbabilitySpectralRawMarginal` | — |
| `WindowProbabilitySpectralRegularity` | — |
| `WindowProbabilitySpectralSectorIntegrals` | — |
| `WindowProbabilitySpectralSimplexLaw` | — |
| `WindowProbabilitySpectralSimplexPermutations` | — |
| `WindowProbabilitySpectralSimplexSymmetricLaw` | — |
| `WindowProbabilitySpectralSimplexWeights` | — |
| `WindowProbabilitySpectralWindowDensity` | companion Prop 5.1 |
| `WindowProbabilitySphere` | — |
| `WindowProbabilityTransport` | — |
