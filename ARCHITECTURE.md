# Architecture

## Dependency Layers

```
Layer -1: ToS Axioms
  ToS_Axioms.v (classic = L3, L4_witness = L4 — the ONLY axioms)

Layer 7: Applications
  Pipeline (DomainTypes, DomainValidation, PipelineSemantics, PipelineExtraction)
  Architecture_of_Reasoning (Fallacies, Paradoxes, AI Detection)

Layer 6: ToS-Lang Compiler
  TypeChecker -> Evaluator -> AIInterface -> ToS_Lang_Extraction

Layer 5: ToS-Lang Semantics
  Expressions -> Reduction -> Typing_Expr -> SubjectReduction -> Progress -> TypeSafety

Layer 4: ToS-Lang Type System
  Judgments -> FormationRules -> Conversion -> Subtyping -> Soundness

Layer 3: ToS Type Primitives
  DependentSystems (Pi, Sigma) -> UniversePolymorphism -> InductiveSystems
  CoinductiveSystems -> ConstitutionChecking -> ErasureTheory

Layer 2: ToS Core
  TheoryOfSystems_Core_ERR (Level, System, Criterion, L1-L5)
  -> Roles (ERR, WellFormed, Status, Dependencies)
  -> IntensionalIdentity (P3, ext/int equivalence)
  -> ProcessGeneral (P4, Cauchy process)
  -> L5Resolution (generalized tie-breaking)
  -> SystemMorphism (iso, embedding, compose)
  -> InfoLayer (information layers)

Layer 1: Analysis
  CauchyReal -> RealField -> Completeness
  -> MonotoneConvergence -> SeriesConvergence -> PowerSeries
  -> Differentiation -> MeanValueTheorem -> RiemannIntegration
  -> IntegralApplications -> TaylorSeries -> UniformConvergence -> FixedPoint
  -> ReasoningConvergence -> GradientDescent

Layer 1.5: Process Physics
  InnerProductSpace (LinearAlgebra, VectorSpace, CauchyReal)
    -> Orthogonality
      -> QState (+ CauchyReal, ProcessGeneral)
        -> QObservable (+ LinearAlgebra)
          -> BornRule
          -> SpectralDichotomy (+ ProcessContinuumHypothesis, ToS_Axioms)
            -> MeasurementProcess (+ BornRule)

Layer 0: Standalone Mathematics
  Archimedean_ERR, Countability_Q, DiagonalArgument_ERR, HeineBorel_ERR
  ShrinkingIntervals_ERR, TernaryRepresentation_ERR, SchroederBernstein_ERR
  IVT_ERR, EVT_ERR, EVT_idx, IVT_CauchyReal
  PInterval_CROWN, LinearAlgebra, Measure, Probability
  SoftmaxProbability, RoundingSafety

Stdlib: (see below)
```

## Stdlib Organization

### Tier 2: Data Structures (12 files, 230 Qed)
```
TMap (31)  <-- Core_ERR + L5Resolution + InductiveSystems + ConstitutionChecking
TSet (30)  <-- TMap
TTree (23) <-- Core_ERR + L5Resolution + InductiveSystems
TQueue (14) <-- Core_ERR + InductiveSystems
TInt (18)  <-- Core_ERR (uses ZArith)
TComplex (19) <-- Core_ERR (uses QArith)
TStream (14) <-- Core_ERR + ProcessGeneral + CoinductiveSystems
TSort (20) <-- Core_ERR + L5Resolution
TSearch (17) <-- Core_ERR + L5Resolution + ConstitutionChecking
THigherOrder (18) <-- Core_ERR + DependentSystems + ConstitutionChecking
TOption (14) <-- Core_ERR + DependentSystems
StdlibExamples (12) <-- all above
```

### Tier 2b: Mathematical Structures (8 files, 166 Qed)
```
GroupTheory (22)  <-- standalone (QArith, ZArith)
RingField (20)   <-- GroupTheory
MetricSpace (18) <-- standalone (QArith, CauchyReal, ProcessGeneral, FixedPoint)
Topology (19)    <-- standalone (QArith)
ConditionalProbability (26) <-- standalone (Probability)
Hessian (22)     <-- standalone (QArith, ZArith)
MDPFoundations (24) <-- standalone (QArith)
MathExamples (15) <-- GroupTheory, RingField, Topology
```

### Batch 3: Discrete Math (9 files, 187 Qed)
```
Primes (21)       <-- standalone (PeanoNat)
Combinatorics (22) <-- standalone (PeanoNat)
Graph (30)        <-- standalone (PeanoNat)
Automata (20)     <-- standalone (PeanoNat)
GCD (22)          <-- Primes
GraphAlgorithms (20) <-- Graph
FormalLanguages (18) <-- Automata
ModularArith (22) <-- Primes + GCD
DiscreteMathExamples (12) <-- all above
```

### Batch 4: Category Theory + Statistics + Information Theory (9 files, 191 Qed)
```
Category (20)       <-- standalone
Monad (20)          <-- standalone (TOption)
Lattice (30)        <-- standalone (L5Resolution)
Distributions (23)  <-- standalone (QArith)
Statistics (26)     <-- standalone (QArith)
Functor (18)        <-- Category
InformationTheory (20) <-- standalone (Section-parameterized log)
Estimation (18)     <-- standalone (QArith)
CategoryStatExamples (16) <-- all above
```

## Key Theorem Chains

### Chain 1: Type Safety
```
typing_implies_wf (Soundness.v)
  -> typing_implies_safe (Soundness.v)
    -> subject_reduction (SubjectReduction.v)
      -> progress (Progress.v)
        -> tos_lang_main_theorem (TypeSafety.v)
          -> typecheck_sound (TypeChecker.v)
            -> verified_pipeline (Evaluator.v)
              -> ai_generation_safe (AIInterface.v)
```

### Chain 2: Convergence
```
is_contraction (FixedPoint.v)
  -> banach_convergence (FixedPoint.v)
    -> pipeline_converges (ReasoningConvergence.v)
      -> bellman_contraction (MDPFoundations.v)
        -> strongly_convex_contraction (Hessian.v)
```

### Chain 3: Paradox Blocking
```
ERR_WellFormed (Roles.v)
  -> circular_dep_is_paradox (Roles.v)
    -> well_formed_no_paradox (Roles.v)
      -> russell_untypable (Soundness.v)
        -> validate_pipeline_sound (DomainValidation.v)
```

### Chain 4: Process Physics (Spectral Dichotomy)
```
state_cauchy_schwarz (InnerProductSpace.v)
  -> born_cauchy_schwarz (BornRule.v)
    -> born_prob_cauchy (BornRule.v)
      -> measurement_prob_structure (MeasurementProcess.v)

process_continuum_hypothesis (ProcessContinuumHypothesis.v)
  -> spectral_dichotomy (SpectralDichotomy.v)
    -> measurement_dichotomy (MeasurementProcess.v)
      -> process_physics_measurement (MeasurementProcess.v)
```

### Chain 5: Calculus
```
CauchyReal -> RealField -> Completeness
  -> MonotoneConvergence -> SeriesConvergence -> PowerSeries
    -> Differentiation -> MeanValueTheorem
      -> RiemannIntegration -> IntegralApplications
        -> TaylorSeries -> UniformConvergence -> FixedPoint
```

## Axiom Architecture

All axioms are declared in `src/ToS_Axioms.v` (Layer -1):

| Axiom | Type | ToS Law |
|-------|------|---------|
| `classic` | `forall P, P \/ ~P` | L3 (Excluded Middle) |
| `L4_witness` | `(exists x, P x) -> {x \| P x}` | L4 (Sufficient Reason) |

Derived principles (not axioms): `L3_informative`, `L4_definite`, `NNPP_from_L3`.

**Banned imports** (no file may use these):
- `Coq.Logic.ClassicalDescription`
- `Coq.Logic.ClassicalEpsilon`
- `Coq.Logic.IndefiniteDescription`

## Import Patterns

All files use `From ToS Require Import ...` (not bare `Require Import`).

```coq
(* Axioms — every file gets these via ToS_Axioms *)
From ToS Require Import ToS_Axioms.

(* Core imports *)
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import Roles.

(* Stdlib imports *)
From ToS Require Import stdlib.TMap.
From ToS Require Import stdlib.Primes.

(* Architecture imports *)
From ToS_Arch Require Import Architecture_of_Reasoning.
```

## File Naming Conventions

- Core files: `CamelCase.v` (e.g., `TheoryOfSystems_Core_ERR.v`)
- Stdlib files: `src/stdlib/CamelCase.v` (e.g., `TMap.v`, `Primes.v`)
- Architecture files: `Architecture_of_Reasoning/CamelCase.v`
- Every file has an E/R/R header documenting Elements, Roles, Rules, Status
