# Theory of Systems — Formal Verification

[![Rocq](https://img.shields.io/badge/Rocq-9.0.1-blue.svg)](https://rocq-prover.org/)
[![Theorems](https://img.shields.io/badge/Theorems-2943_Proven-brightgreen.svg)]()
[![Admitted](https://img.shields.io/badge/Admitted-6-yellow.svg)]()
[![Axioms](https://img.shields.io/badge/Custom_Axioms-0-green.svg)]()
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **A complete deductive derivation of mathematics from "something exists" —
> 2943 machine-verified theorems, a verified programming language,
> and the first formally verified reasoning pipeline for LLMs.**

---

## What Is This?

Theory of Systems derives all of mathematics — including logic — from a single
first principle: **A = exists** ("something exists"). Through the act of
distinction (A/not-A), five laws of logic emerge, four principles of systems
follow, and from these: number systems, calculus, algebra, probability,
optimization, and a programming language — all formally verified.

### The Chain

```
A = exists
  -> Distinction (A/not-A)
    -> Laws L1-L5 (Identity, Non-Contradiction, Excluded Middle,
                   Sufficient Reason, Order)
      -> Principles P1-P4 (Hierarchy, Criterion Precedence,
                           Identity, Process)
        -> E/R/R Framework (Elements, Roles, Rules)
          -> N, Q, R, Calculus, Algebra, Probability, Optimization
            -> ToS-Lang (verified programming language)
              -> Verified D1-D6 Reasoning Pipeline for LLMs
```

### Key Numbers

| Metric | Count |
|--------|-------|
| Proven theorems (Qed) | 2943 |
| Coq files | 138 |
| Custom axioms | 0 |
| External axioms | `classic` (all files); `constructive_definite_description` (BW, SB); `constructive_indefinite_description` (PCH) |
| Admitted | 6 (all documented, most by design) |
| Stdlib modules | 53 |
| ToS-Lang: type safety | proven (`tos_lang_main_theorem`) |
| Pipeline: structural safety | proven (`validate_pipeline_sound`) |

---

## Quick Start

```bash
# Clone and build
git clone https://github.com/Horsocrates/theory-of-systems-coq.git
cd theory-of-systems-coq
make

# Verify counts
echo "Proven:"; grep -rc 'Qed\.' src/ Architecture_of_Reasoning/ | awk -F: '{s+=$2}END{print s}'
echo "Admitted:"; grep -rc 'Admitted\.' src/ Architecture_of_Reasoning/ | awk -F: '{s+=$2}END{print s}'

# Run the verified ToS-Lang demo
coqc -Q src ToS src/Demo.v
```

---

## Project Structure

```
src/
  Core (18 files)          L1-L5, P1-P4, E/R/R, Systems, Levels, Morphisms,
                           Category of Systems, Level Functors, Adjunction
  Type Theory (7 files)    Pi, Sigma, Inductive, Coinductive, Constitution, Erasure, Universes
  Type System (5 files)    Judgments, Formation, Conversion, Subtyping, Soundness
  Semantics (6 files)      Expressions, Reduction, Typing, SubjectReduction, Progress, TypeSafety
  Compiler (4 files)       TypeChecker, Evaluator, AIInterface, Extraction
  Pipeline (4 files)       DomainTypes, Validation, PipelineSemantics, Extraction
  Analysis (22 files)      CauchyReal, Calculus chain, Series, IVT, EVT, FixedPoint,
                           BolzanoWeierstrass, FTC, HeineBorelComplete, ImplicitFunction
  Set Theory (3 files)     ProcessTypes, ProcessDiagonal, ProcessContinuumHypothesis
  Applied Math (8 files)   CROWN, GradientDescent, LinearAlgebra, Probability, Measure...
  stdlib/ (53 files)       Data structures, algorithms, number theory, graphs, algebra,
                           categories, lattices, distributions, statistics, estimation,
                           vector spaces, tensors, ODEs, convex analysis, game theory,
                           auctions, control theory, multi-agent consensus,
                           credit scoring, neural nets, text analysis, time series,
                           formal verification...

Architecture_of_Reasoning/ (6 files)
  156 Fallacies, 46 Paradoxes, AI Fallacy Detection, Domain Violations

tos_lang/                  OCaml extraction + parser + CLI
examples/                  .tos example files
```

See [ARCHITECTURE.md](ARCHITECTURE.md) for full dependency graph.
See [docs/FILE_MAP.md](docs/FILE_MAP.md) for every file with Qed count.

---

## Highlights

### Verified Programming Language (ToS-Lang)

```
$ coqc -Q src ToS src/Demo.v

# Type check: (fun x:Nat. x) 42
= Some TyNat : option Ty

# Evaluate: (fun x:Nat. x) 42
= EConst 42 : ExprA

# Full pipeline: typecheck -> evaluate -> classify
= ER_Value (EConst 42) TyNat : EvalResultA
```

Every result computed inside Coq's kernel. Type checker and evaluator are
**proven correct**: `typecheck_sound`, `subject_reduction`, `progress`,
`tos_lang_main_theorem`.

### Verified Reasoning Pipeline (D1-D6)

Six-domain reasoning pipeline for any LLM:
- **D6-ASK** (pre-pipeline): question decomposition
- **D1-D5** (worker domains): Recognition -> Clarification -> Framework -> Comparison -> Inference
- **D6-REFLECT** (inter-domain gates + post-pipeline reflection)
- **Convergence**: Banach contraction theorem (not magic numbers)

Structural guarantees: domains can't be skipped (type error), dependencies can't be
circular (structurally impossible), confidence is computed from scorecard (not self-reported).

### Mathematical Library

Complete chain from first principles to:
- **Calculus**: Differentiation -> MVT -> Riemann Integration -> Taylor Series
- **Analysis**: Series Convergence, Power Series, Uniform Convergence, Fixed Point
- **Algebra**: Groups, Rings, Fields (with Z, Q instances)
- **Topology**: Metric spaces, open/closed sets, continuity
- **Probability**: Conditional probability, Bayes theorem
- **Optimization**: Gradient descent, Newton's method, contraction mapping
- **Data Structures**: Map, Set, Tree, Queue, Sort, Search (all as ToS Systems)
- **Discrete Math**: Primes, GCD, Modular Arithmetic, Graphs, Automata, Formal Languages
- **Number Theory**: Combinatorics, Pigeonhole principle, Sieve of Eratosthenes
- **Game Theory**: Nash equilibrium, Prisoner's Dilemma, Auctions (Vickrey), Pareto optimality
- **Control & Dynamics**: ODEs (Euler/Picard), LTI systems, Lyapunov stability, Multi-agent consensus
- **Convex Analysis**: Jensen's inequality, strong convexity, local-is-global optimality
- **Set Theory**: Process Continuum Hypothesis, Cantor diagonal, perfect subset theorem
- **Category of Systems**: Sys(L) as Category, embed/forget functors, level adjunction, E/R/R functorial decomposition

---

## Statistics

### By Category

| Category | Files | Qed | Admitted |
|----------|-------|-----|----------|
| Core + Type Theory | 26 | 544 | 2 |
| Category of Systems | 4 | 105 | 0 |
| Analysis + Applied Math | 30 | 660 | 4 |
| Set Theory (PCH) | 3 | 86 | 0 |
| ToS-Lang (Semantics + Compiler) | 10 | 198 | 0 |
| Pipeline | 4 | 76 | 0 |
| Stdlib | 53 | 1089 | 0 |
| Architecture of Reasoning | 6 | 117 | 0 |
| Integration + Extraction | 2 | 68 | 0 |
| **TOTAL** | **138** | **2943** | **6** |

### Admitted (6, all documented)

| File | Count | Reason |
|------|-------|--------|
| `TernaryRepresentation_ERR.v` | 2 | `Qfloor` discontinuity; alternative: `ShrinkingIntervals` |
| `TheoryOfSystems_Core_ERR.v` | 2 | Universe-level proofs (require explicit universe annotations) |
| `EVT_ERR.v` | 1 | `argmax_process_is_Cauchy`; use `EVT_idx.v` instead |
| `DiagonalArgument_ERR.v` | 1 | Alternative approach; use `ShrinkingIntervals` instead |

### Calculus Chain (167 Qed, 0 Admitted)

```
MonotoneConvergence (15) -> SeriesConvergence (22) -> PowerSeries (19)
  -> Differentiation (18) -> MeanValueTheorem (18) -> RiemannIntegration (18)
    -> IntegralApplications (19) -> TaylorSeries (18) -> UniformConvergence (20)
      -> FixedPoint (20)
```

### Verified Standard Library (53 files, 1089 Qed, 0 Admitted)

| Tier | Files | Qed | Contents |
|------|-------|-----|----------|
| Tier 2 | 12 | 230 | TMap, TSet, TTree, TQueue, TSort, TSearch, TStream, TInt, TComplex, THigherOrder, TOption, StdlibExamples |
| Tier 2b | 8 | 166 | GroupTheory, RingField, MetricSpace, Topology, ConditionalProbability, Hessian, MDPFoundations, MathExamples |
| Batch 3 | 9 | 187 | Primes, GCD, ModularArith, Combinatorics, Graph, GraphAlgorithms, Automata, FormalLanguages, DiscreteMathExamples |
| Batch 4 | 9 | 191 | Category, Functor, Monad, Lattice, Distributions, Statistics, InformationTheory, Estimation, CategoryStatExamples |
| Batch 5 | 9 | 209 | VectorSpace, Tensor, ODE, ConvexAnalysis, GameTheory, AuctionTheory, ControlTheory, MultiAgent, AdvancedExamples |
| Batch 6 | 6 | 106 | CreditScoring, NeuralNet, TextAnalysis, TimeSeries, FormalVerification, DomainExamples |

---

## Philosophical Foundation

**Logical Realism:** Logic is the structure of being, not a tool of thought.

**E/R/R Framework:** Every system has three aspects — Elements (what),
Roles (why, L4), Rules (how, L5). These are not three parts but three
aspects of one act of distinction.

**P4 (Infinity as Process):** No completed infinity. Numbers are limits
of convergent processes. Computations are step-indexed. ToS-Lang's evaluator
**always terminates** by construction.

**P3 (Intensional Identity):** Two systems with the same constitution
are identical. Not "have the same elements" — "have the same constitution."

---

## Publications

### Foundational

- **[The Laws of Logic as Conditions of Existence](https://philpapers.org/archive/HORTLO-18.pdf)** — Derivation of L1-L5 from first principle
- **[The Law of Order](https://philpapers.org/archive/HORTLO-19.pdf)** — L5 and the EVT breakthrough

### Reasoning Architecture

- **[The Architecture of Error](https://philpapers.org/archive/HORTAO-17.pdf)** — Structural theory of fallacies (Part 1)
- **[Domain Violations: A Systematic Taxonomy](https://philpapers.org/rec/HORDVA)** — 105 Type 2 fallacies (Part 2)
- **[Paradox Dissolution Through Hierarchical Analysis](https://philpapers.org/rec/HORPDT)** — 46 paradoxes classified

---

## Citation

```bibtex
@software{theory_of_systems_coq,
  author = {Horsocrates},
  title = {Theory of Systems — Formal Verification},
  year = {2026},
  url = {https://github.com/Horsocrates/theory-of-systems-coq}
}
```

---

## License

MIT License — see [LICENSE](LICENSE) for details.
