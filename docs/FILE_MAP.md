# File Map

Auto-generated: 2026-03-08 18:52

## Axioms (Layer -1)

| File | Qed | Admitted | Key Imports |
|------|-----|---------|-------------|
| `ToS_Axioms.v` | 3 | 0 | Classical_Prop (re-exports classic) |

## Core

| File | Qed | Admitted | Key Imports |
|------|-----|---------|-------------|
| `AIInterface.v` | 10 | 0 | Expressions,Reduction,Typing_Expr,Progress,TypeSafety,TypeCh |
| `Archimedean_ERR.v` | 14 | 0 |  |
| `CauchyReal.v` | 19 | 0 |  |
| `CoinductiveSystems.v` | 16 | 0 | ProcessGeneral |
| `Completeness.v` | 24 | 0 | Archimedean_ERR,CauchyReal,RealField |
| `ConstitutionChecking.v` | 16 | 0 | TheoryOfSystems_Core_ERR,IntensionalIdentity,L5Resolution |
| `Conversion.v` | 16 | 0 | TheoryOfSystems_Core_ERR,IntensionalIdentity,SystemMorphism, |
| `Countability_Q.v` | 17 | 0 |  |
| `Demo.v` | 0 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism,Expressions,Re |
| `DependentSystems.v` | 25 | 0 | TheoryOfSystems_Core_ERR,SystemMorphism |
| `DiagonalArgument_ERR.v` | 41 | 1 |  |
| `Differentiation.v` | 18 | 0 | CauchyReal,RealField,SeriesConvergence,GradientDescent |
| `DomainTypes.v` | 20 | 0 |  |
| `DomainValidation.v` | 32 | 0 | DomainTypes |
| `ERR_Categorical.v` | 24 | 0 | TheoryOfSystems_Core_ERR,SystemMorphism,UniversePolymorphism |
| `EVT_ERR.v` | 35 | 1 |  |
| `EVT_idx.v` | 26 | 0 |  |
| `ErasureTheory.v` | 16 | 0 | TheoryOfSystems_Core_ERR,Roles |
| `Evaluator.v` | 20 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism,Expressions,Re |
| `Expressions.v` | 28 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism |
| `Extraction.v` | 0 | 0 | TheoryOfSystems_Core_ERR,Roles,IntensionalIdentity,ProcessGe |
| `FixedPoint.v` | 20 | 0 | CauchyReal,Completeness,MonotoneConvergence,SeriesConvergenc |
| `FormationRules.v` | 18 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism,IntensionalIde |
| `GradientDescent.v` | 18 | 0 | CauchyReal,RealField,MonotoneConvergence,SeriesConvergence,P |
| `HeineBorel_ERR.v` | 25 | 0 |  |
| `IVT_CauchyReal.v` | 8 | 0 | Archimedean_ERR,IVT_ERR,CauchyReal |
| `IVT_ERR.v` | 23 | 0 | Archimedean_ERR |
| `InductiveSystems.v` | 26 | 0 | TheoryOfSystems_Core_ERR |
| `InfoLayer.v` | 17 | 0 | TheoryOfSystems_Core_ERR,IntensionalIdentity |
| `IntegralApplications.v` | 19 | 0 | CauchyReal,RealField,EVT_idx,Differentiation,MeanValueTheore |
| `IntensionalIdentity.v` | 11 | 0 | TheoryOfSystems_Core_ERR |
| `Judgments.v` | 23 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism |
| `L5Resolution.v` | 18 | 0 | TheoryOfSystems_Core_ERR |
| `LevelAdjunction.v` | 25 | 0 | TheoryOfSystems_Core_ERR,SystemMorphism,UniversePolymorphism |
| `LevelFunctors.v` | 27 | 0 | TheoryOfSystems_Core_ERR,SystemMorphism,UniversePolymorphism |
| `LinearAlgebra.v` | 22 | 0 |  |
| `MeanValueTheorem.v` | 18 | 0 | CauchyReal,RealField,EVT_idx,Differentiation |
| `Measure.v` | 15 | 0 |  |
| `MonotoneConvergence.v` | 15 | 0 | CauchyReal,Completeness |
| `PInterval_CROWN.v` | 25 | 0 |  |
| `PhaseA_Examples.v` | 11 | 0 | TheoryOfSystems_Core_ERR,SystemMorphism,DependentSystems,Ind |
| `PipelineExtraction.v` | 7 | 0 | DomainTypes,DomainValidation,PipelineSemantics |
| `PipelineSemantics.v` | 17 | 0 | DomainTypes,DomainValidation |
| `PowerSeries.v` | 19 | 0 | CauchyReal,RealField,MonotoneConvergence,SeriesConvergence |
| `Probability.v` | 12 | 0 |  |
| `ProcessContinuumHypothesis.v` | 41 | 0 | ProcessTypes,ProcessDiagonal |
| `ProcessDiagonal.v` | 20 | 0 | ProcessTypes |
| `ProcessGeneral.v` | 16 | 0 | TheoryOfSystems_Core_ERR,CauchyReal |
| `ProcessTypes.v` | 25 | 0 |  |
| `Progress.v` | 17 | 0 | Expressions,Reduction,Typing_Expr |
| `RealField.v` | 17 | 0 | CauchyReal |
| `ReasoningConvergence.v` | 19 | 0 | CauchyReal,Completeness,MonotoneConvergence,SeriesConvergenc |
| `Reduction.v` | 25 | 0 | Expressions |
| `RiemannIntegration.v` | 18 | 0 | CauchyReal,RealField,EVT_idx,Differentiation,MeanValueTheore |
| `Roles.v` | 30 | 0 | TheoryOfSystems_Core_ERR |
| `RoundingSafety.v` | 13 | 0 |  |
| `SchroederBernstein_ERR.v` | 14 | 0 |  |
| `SeriesConvergence.v` | 22 | 0 | CauchyReal,Completeness,MonotoneConvergence |
| `ShrinkingIntervals_ERR.v` | 167 | 0 |  |
| `SoftmaxProbability.v` | 14 | 0 |  |
| `Soundness.v` | 22 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism,IntensionalIde |
| `SubjectReduction.v` | 17 | 0 | Expressions,Reduction,Typing_Expr |
| `Subtyping.v` | 20 | 0 | TheoryOfSystems_Core_ERR,SystemMorphism,Judgments,DependentS |
| `SystemCategory.v` | 29 | 0 | TheoryOfSystems_Core_ERR,SystemMorphism,UniversePolymorphism |
| `SystemMorphism.v` | 17 | 0 | TheoryOfSystems_Core_ERR |
| `TaylorSeries.v` | 18 | 0 | CauchyReal,RealField,EVT_idx,Differentiation,MeanValueTheore |
| `TernaryRepresentation_ERR.v` | 52 | 2 |  |
| `TestNode.v` | 0 | 0 |  |
| `TheoryOfSystems_Core_ERR.v` | 34 | 2 |  |
| `ToS_Lang_Extraction.v` | 8 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism,Expressions,Re |
| `TypeChecker.v` | 26 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism,Expressions,Ty |
| `TypeSafety.v` | 13 | 0 | Expressions,Reduction,Typing_Expr,SubjectReduction,Progress |
| `Typing_Expr.v` | 22 | 0 | TheoryOfSystems_Core_ERR,UniversePolymorphism,Expressions |
| `UniformConvergence.v` | 20 | 0 | CauchyReal,Completeness,MonotoneConvergence,Differentiation, |
| `UniversePolymorphism.v` | 23 | 0 | TheoryOfSystems_Core_ERR |

## Analysis

| File | Qed | Admitted | Key Imports |
|------|-----|---------|-------------|
| `BolzanoWeierstrass.v` | 26 | 0 | Archimedean_ERR,CauchyReal,Completeness,MonotoneConvergence |
| `FTC.v` | 28 | 0 | CauchyReal,RealField,EVT_idx,Differentiation,MeanValueTheore |
| `HeineBorelComplete.v` | 28 | 0 |  |
| `ImplicitFunction.v` | 20 | 0 | CauchyReal,Completeness,MonotoneConvergence,SeriesConvergenc |

## Stdlib

| File | Qed | Admitted | Key Imports |
|------|-----|---------|-------------|
| `AdvancedExamples.v` | 13 | 0 | LinearAlgebra,ProcessGeneral,stdlibVectorSpace.,stdlibTensor |
| `AuctionTheory.v` | 22 | 0 |  |
| `Automata.v` | 20 | 0 |  |
| `Category.v` | 20 | 0 |  |
| `CategoryStatExamples.v` | 16 | 0 | TheoryOfSystems_Core_ERR,stdlibCategory.,stdlibFunctor.,stdl |
| `Combinatorics.v` | 22 | 0 |  |
| `ConditionalProbability.v` | 26 | 0 |  |
| `ControlTheory.v` | 21 | 0 | LinearAlgebra,ProcessGeneral |
| `ConvexAnalysis.v` | 22 | 0 |  |
| `CreditScoring.v` | 22 | 0 | stdlibStatistics. |
| `DiscreteMathExamples.v` | 12 | 0 | stdlibPrimes.,stdlibGCD.,stdlibModularArith.,stdlibCombinato |
| `Distributions.v` | 23 | 0 | TheoryOfSystems_Core_ERR |
| `DomainExamples.v` | 14 | 0 | stdlibStatistics.,stdlibCreditScoring.,stdlibNeuralNet.,stdl |
| `Estimation.v` | 18 | 0 | TheoryOfSystems_Core_ERR |
| `FormalLanguages.v` | 18 | 0 | stdlibAutomata. |
| `FormalVerification.v` | 20 | 0 |  |
| `Functor.v` | 18 | 0 | stdlibCategory. |
| `GCD.v` | 22 | 0 | stdlibPrimes. |
| `GameTheory.v` | 25 | 0 |  |
| `Graph.v` | 30 | 0 |  |
| `GraphAlgorithms.v` | 20 | 0 | stdlibGraph. |
| `GroupTheory.v` | 22 | 0 |  |
| `Hessian.v` | 22 | 0 |  |
| `InformationTheory.v` | 20 | 0 | TheoryOfSystems_Core_ERR |
| `Lattice.v` | 30 | 0 | TheoryOfSystems_Core_ERR |
| `MDPFoundations.v` | 24 | 0 |  |
| `MathExamples.v` | 15 | 0 | GroupTheory RingField Topology |
| `MetricSpace.v` | 18 | 0 | CauchyReal,ProcessGeneral,LinearAlgebra |
| `ModularArith.v` | 22 | 0 | stdlibPrimes.,stdlibGCD. |
| `Monad.v` | 20 | 0 | TheoryOfSystems_Core_ERR,stdlibTOption. |
| `MultiAgent.v` | 18 | 0 | Graph |
| `NeuralNet.v` | 18 | 0 | stdlibStatistics. |
| `ODE.v` | 22 | 0 | ProcessGeneral |
| `Primes.v` | 21 | 0 |  |
| `RingField.v` | 20 | 0 | GroupTheory |
| `Statistics.v` | 26 | 0 |  |
| `StdlibExamples.v` | 12 | 0 | TheoryOfSystems_Core_ERR,L5Resolution,stdlibTMap.,stdlibTSet |
| `TComplex.v` | 19 | 0 | TheoryOfSystems_Core_ERR |
| `THigherOrder.v` | 18 | 0 | TheoryOfSystems_Core_ERR,DependentSystems,ConstitutionChecki |
| `TInt.v` | 18 | 0 | TheoryOfSystems_Core_ERR |
| `TMap.v` | 31 | 0 | TheoryOfSystems_Core_ERR,L5Resolution,InductiveSystems,Const |
| `TOption.v` | 14 | 0 | TheoryOfSystems_Core_ERR,DependentSystems |
| `TQueue.v` | 14 | 0 | TheoryOfSystems_Core_ERR,InductiveSystems |
| `TSearch.v` | 17 | 0 | TheoryOfSystems_Core_ERR,L5Resolution,ConstitutionChecking |
| `TSet.v` | 30 | 0 | TheoryOfSystems_Core_ERR,L5Resolution,InductiveSystems,Const |
| `TSort.v` | 20 | 0 | TheoryOfSystems_Core_ERR,L5Resolution |
| `TStream.v` | 14 | 0 | TheoryOfSystems_Core_ERR,ProcessGeneral,CoinductiveSystems |
| `TTree.v` | 23 | 0 | TheoryOfSystems_Core_ERR,L5Resolution,InductiveSystems |
| `Tensor.v` | 39 | 0 | LinearAlgebra |
| `TextAnalysis.v` | 16 | 0 |  |
| `TimeSeries.v` | 16 | 0 | ProcessGeneral,stdlibStatistics. |
| `Topology.v` | 19 | 0 |  |
| `VectorSpace.v` | 27 | 0 | LinearAlgebra |

## Process Physics (Phase 3A)

| File | Qed | Admitted | Key Imports |
|------|-----|---------|-------------|
| `InnerProductSpace.v` | 36 | 0 | LinearAlgebra, stdlib.VectorSpace, CauchyReal |
| `Orthogonality.v` | 27 | 0 | InnerProductSpace |
| `QState.v` | 19 | 0 | InnerProductSpace, CauchyReal, ProcessGeneral |
| `QObservable.v` | 16 | 0 | InnerProductSpace, QState, LinearAlgebra |
| `BornRule.v` | 13 | 0 | QState, QObservable, InnerProductSpace |
| `SpectralDichotomy.v` | 30 | 0 | ToS_Axioms, ProcessTypes, ProcessContinuumHypothesis, QObservable |
| `MeasurementProcess.v` | 19 | 0 | SpectralDichotomy, BornRule |

## Architecture of Reasoning

| File | Qed | Admitted | Key Imports |
|------|-----|---------|-------------|
| `AI_FallacyDetector.v` | 13 | 0 |  |
| `Architecture_of_Reasoning.v` | 17 | 0 |  |
| `CompleteFallacyTaxonomy.v` | 19 | 0 |  |
| `DomainViolations_Complete.v` | 17 | 0 |  |
| `ERR_Fallacies.v` | 22 | 0 |  |
| `ParadoxDissolution.v` | 29 | 0 |  |

## Totals

| Metric | Count |
|--------|-------|
| Files | 146 |
| Qed | 3111 |
| Admitted | 11 |
