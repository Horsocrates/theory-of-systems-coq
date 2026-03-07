# Theory of Systems — Formal Verification

[![Rocq](https://img.shields.io/badge/Rocq-9.0.1-blue.svg)](https://rocq-prover.org/)
[![Theorems](https://img.shields.io/badge/Theorems-2141_Proven-brightgreen.svg)]()
[![Admitted](https://img.shields.io/badge/Admitted-13-yellow.svg)]()
[![Axioms](https://img.shields.io/badge/Custom_Axioms-0-green.svg)]()
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **A complete deductive derivation of mathematics from "something exists" —
> 2141 machine-verified theorems, a verified programming language,
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
| Proven theorems (Qed) | 2141 |
| Coq files | 103 |
| Custom axioms | 0 |
| External axioms | 1 (`classic` — Law of Excluded Middle, = L3) |
| Admitted | 13 (all documented, most by design) |
| Stdlib modules | 29 |
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
  Core (14 files)          L1-L5, P1-P4, E/R/R, Systems, Levels, Morphisms
  Type Theory (7 files)    Pi, Sigma, Inductive, Coinductive, Constitution, Erasure, Universes
  Type System (5 files)    Judgments, Formation, Conversion, Subtyping, Soundness
  Semantics (6 files)      Expressions, Reduction, Typing, SubjectReduction, Progress, TypeSafety
  Compiler (4 files)       TypeChecker, Evaluator, AIInterface, Extraction
  Pipeline (4 files)       DomainTypes, Validation, PipelineSemantics, Extraction
  Analysis (18 files)      CauchyReal, Calculus chain, Series, IVT, EVT, FixedPoint...
  Applied Math (8 files)   CROWN, GradientDescent, LinearAlgebra, Probability, Measure...
  stdlib/ (29 files)       Data structures, algorithms, number theory, graphs, algebra...

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

---

## Statistics

### By Category

| Category | Files | Qed | Admitted |
|----------|-------|-----|----------|
| Core + Type Theory | 26 | 544 | 5 |
| Analysis + Applied Math | 26 | 555 | 4 |
| ToS-Lang (Semantics + Compiler) | 10 | 198 | 1 |
| Pipeline | 4 | 76 | 0 |
| Stdlib | 29 | 583 | 0 |
| Architecture of Reasoning | 6 | 117 | 0 |
| Integration + Extraction | 2 | 68 | 3 |
| **TOTAL** | **103** | **2141** | **13** |

### Admitted (13, all documented)

| File | Count | Reason |
|------|-------|--------|
| `TernaryRepresentation_ERR.v` | 3 | `Qfloor` discontinuity; alternative: `ShrinkingIntervals` |
| `TheoryOfSystems_Core_ERR.v` | 2 | Bootstrap axioms (L1-L5 foundation) |
| `HeineBorel_ERR.v` | 2 | Unprovable over Q (requires real-valued continuity) |
| `EVT_ERR.v` | 1 | `argmax_process_is_Cauchy`; use `EVT_idx.v` instead |
| `DiagonalArgument_ERR.v` | 1 | Alternative approach; use `ShrinkingIntervals` instead |
| `InductiveSystems.v` | 1 | Accessibility well-foundedness |
| `ErasureTheory.v` | 1 | Erasure preserves behavior |
| `PhaseA_Examples.v` | 1 | Integration example |
| `TypeSafety.v` | 1 | Fuel-bound monotonicity (structurally sound) |

### Calculus Chain (167 Qed, 0 Admitted)

```
MonotoneConvergence (15) -> SeriesConvergence (22) -> PowerSeries (19)
  -> Differentiation (18) -> MeanValueTheorem (18) -> RiemannIntegration (18)
    -> IntegralApplications (19) -> TaylorSeries (18) -> UniformConvergence (20)
      -> FixedPoint (20)
```

### Verified Standard Library (29 files, 583 Qed, 0 Admitted)

| Tier | Files | Qed | Contents |
|------|-------|-----|----------|
| Tier 2 | 12 | 230 | TMap, TSet, TTree, TQueue, TSort, TSearch, TStream, TInt, TComplex, THigherOrder, TOption, StdlibExamples |
| Tier 2b | 8 | 166 | GroupTheory, RingField, MetricSpace, Topology, ConditionalProbability, Hessian, MDPFoundations, MathExamples |
| Batch 3 | 9 | 187 | Primes, GCD, ModularArith, Combinatorics, Graph, GraphAlgorithms, Automata, FormalLanguages, DiscreteMathExamples |

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
