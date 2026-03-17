# Source Architecture

499 files, 10139 Qed, 0 Admitted. Two axioms: `classic` (L3) + `L4_witness` (L4).

---

## Directory Overview

```
src/
  ToS_Axioms.v                    The ONLY axioms (L3 + L4)
  <76 core files>                 1649 Qed — foundations, type theory, analysis, pipeline
  process/     165 files          2658 Qed — P4 process mathematics + physics
  gauge/       100 files          2030 Qed — Yang-Mills mass gap
  navier_stokes/ 34 files          869 Qed — Navier-Stokes regularity
  physics/      14 files           356 Qed — quantum measurement theory
  stdlib/       53 files          1090 Qed — standard library

Architecture_of_Reasoning/
                6 files            117 Qed — fallacy/paradox taxonomy
```

## Dependency Graph (High-Level)

```
ToS_Axioms.v (L3 classic, L4 witness)
  |
  v
Core Framework (14 files: L1-L5, P1-P4, E/R/R, Systems, Levels)
  |
  +---> Type Theory (7 files: Pi, Sigma, Inductive, Coinductive, Constitution, Erasure)
  |       |
  |       +---> Type System (5 files: Judgments, Formation, Conversion, Subtyping, Soundness)
  |       |       |
  |       |       +---> Semantics (6 files: Expr, Reduction, Typing, SR, Progress, Safety)
  |       |               |
  |       |               +---> Compiler (4 files: TypeChecker, Evaluator, AI, Extraction)
  |       |
  |       +---> Pipeline (4 files: DomainTypes, Validation, Semantics, Extraction)
  |
  +---> Analysis (22 files: CauchyReal, Calculus chain, IVT, EVT, FixedPoint...)
  |
  +---> Physics (14 files: InnerProduct, Born Rule, Spectral Dichotomy, Qubit...)
  |
  +---> process/ ---+---> core/ (12 files: ProcessCore, Arithmetic, Bounds, Groups, Rings)
  |                 +---> analysis/ (15 files: IVT, FTC, Picard, ODE, Lebesgue, Fatou)
  |                 +---> topology/ (6 files: open, metric, compact, connected)
  |                 +---> funcanalysis/ (10 files: operators, spectral, PMG, category)
  |                 +---> err/ (10 files: E/R/R -> gauge invariance, fermions)
  |                 +---> gravity/ (20 files: Geom/Gauge categories, Regge, Einstein)
  |                 +---> adjunction/ (14 files: GR-QFT adjunction, QG, defect)
  |                 +---> spacetime/ (13 files: Lorentzian, dimension, crossing)
  |                 +---> electroweak/ (12 files: Higgs, Weinberg angle, GUT)
  |                 +---> fermions/ (13 files: Pauli, Grassmann, mass hierarchy)
  |                 +---> sm/ (7 files: anomaly, Standard Model, CP violation)
  |                 +---> rg/ (9 files: blocking, RG flow, string tension)
  |                 +---> quantum/ (8 files: Heisenberg, Born rule, entanglement, no-cloning)
  |                 +---> synthesis/ (12 files: grand unification, final assessment)
  |
  +---> gauge/ -----+---> core/ (10 files: SU(2), transfer matrix, Wilson action)
  |                 +---> gap/ (15 files: spectral gap, exact eigenvalues, PMG)
  |                 +---> rg/ (10 files: RG flow, contraction, universality)
  |                 +---> dimensions/ (17 files: 2D, 3D, strip, dimension ladder)
  |                 +---> continuum/ (8 files: continuum limit, thermodynamic limit)
  |                 +---> confinement/ (10 files: strong coupling, domain walls)
  |                 +---> axioms/ (11 files: OS axioms, Wightman, reflection positivity)
  |                 +---> synthesis/ (19 files: Yang-Mills complete, millennium)
  |
  +---> navier_stokes/ (34 files: Galerkin, enstrophy, triadic, regularity)
  |
  +---> stdlib/ (53 files: data structures, algebra, number theory, game theory...)

Architecture_of_Reasoning/ (6 files: 156 fallacies, 46 paradoxes)
```

Note: subdirectory groupings above are LOGICAL (documented in DIRECTORY_MAP.md files).
All files currently reside flat in their parent directory.

## Core src/ Files (76 files, 1649 Qed)

### Foundation (14 files)
ToS_Axioms, Core_ERR, Laws (L1-L5), Principles (P1-P4), Roles, IntensionalIdentity,
SystemMorphism, SystemCategory, LevelFunctors, LevelAdjunction, ERR_Categorical

### Type Theory (7 files)
DependentSystems, UniversePolymorphism, InductiveSystems, CoinductiveSystems,
ConstitutionChecking, ErasureTheory, PhaseA_Examples

### Type System + Semantics (15 files)
Judgments, FormationRules, Conversion, Subtyping, Soundness,
Expressions, Reduction, Typing_Expr, SubjectReduction, Progress, TypeSafety,
TypeChecker, Evaluator, AIInterface, ToS_Lang_Extraction

### Analysis (22 files)
CauchyReal, Completeness, MonotoneConvergence, SeriesConvergence, PowerSeries,
Differentiation, MeanValueTheorem, RiemannIntegration, IntegralApplications,
TaylorSeries, UniformConvergence, FixedPoint, ReasoningConvergence,
ProcessGeneral, L5Resolution, ProcessTypes, ProcessDiagonal,
ProcessContinuumHypothesis, ShrinkingIntervals_ERR, IVT, EVT_idx, Archimedean

### Pipeline (4 files)
DomainTypes, DomainValidation, PipelineSemantics, PipelineExtraction

### Applied Math (8 files)
CROWN, GradientDescent, LinearAlgebra, ProbabilityTheory, MeasureTheory,
InfoLayer, GapCompute, GapCertificate, GapExtraction

## Cross-Module Dependencies

Key import patterns between directories:

- `process/` imports from `src/` core (ProcessCore, Arithmetic, Bounds)
- `process/quantum/` imports from `process/sm/` (ProcessGaussianQ for Q[i])
- `process/adjunction/` imports from `process/gravity/` (GeomCategory, GaugeCategory)
- `process/synthesis/` imports from nearly everything
- `gauge/` is mostly self-contained (imports from `process/` only for ProcessMassGap)
- `navier_stokes/` is fully self-contained
- `physics/` imports from `src/` core only
- `stdlib/` is fully self-contained (no imports from other src/ files)

## The Derivation Chain

```
A = exists (ToS_Axioms.v)
  Step 1: Logic L1-L5 (Laws_L1.v ... Laws_L5.v)
  Step 2: Principles P1-P4 (Principles.v)
  Step 3: E/R/R Framework (Core_ERR.v, Roles.v)
  Step 4: Mathematics (Analysis, Algebra, Topology — process/)
  Step 5: Gauge invariance from E/R/R (process/err/)
  Step 6: Gravity from P3 (process/gravity/)
  Step 7: Adjunction GR<->QFT from P2 (process/adjunction/)
  Step 8: Standard Model from consistency (process/sm/, electroweak/, fermions/)
  Step 9: Quantitative predictions (process/rg/, electroweak/)
  Step 10: Quantum mechanics from logic (process/quantum/)
```
