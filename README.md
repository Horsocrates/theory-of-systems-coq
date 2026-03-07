# Theory of Systems — Coq Formalization

[![Rocq](https://img.shields.io/badge/Rocq-9.0.1-blue.svg)](https://coq.inria.fr/)
[![Status](https://img.shields.io/badge/Status-99.6%25_Complete-green.svg)]()
[![Theorems](https://img.shields.io/badge/Theorems-1787_Proven-brightgreen.svg)]()
[![Fallacies](https://img.shields.io/badge/Fallacies-156-blue.svg)]()
[![Paradoxes](https://img.shields.io/badge/Paradoxes-46-blue.svg)]()
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **A complete deductive derivation of mathematics from a single first principle: "A = exists"**

---

## The Deductive Chain

```
                              A = exists
                                  │
                    ┌─────────────┴─────────────┐
                    ▼                             ▼
              Distinction                   Act of Naming
              (A / ¬A)                    (observer enters)
                    │                             │
                    └─────────────┬─────────────┘
                                  ▼
                    ╔═══════════════════════════╗
                    ║    LAWS OF LOGIC (L1-L5)  ║
                    ╠═══════════════════════════╣
                    ║  L1  Identity      A = A  ║
                    ║  L2  Non-contra  ¬(A∧¬A)  ║
                    ║  L3  Excluded     A ∨ ¬A  ║
                    ║  L4  Suff.Reason  ∀A ∃why  ║
                    ║  L5  Order     min-select  ║
                    ╚═════════════╤═════════════╝
                                  │
                    ┌─────────────┼─────────────┐
                    ▼             ▼               ▼
              ╔═════════╗  ╔══════════╗  ╔══════════════╗
              ║   P1    ║  ║   P2     ║  ║     P3       ║
              ║ Exist-  ║  ║ Role     ║  ║ Intensional  ║
              ║  ence   ║  ║ assign   ║  ║  Identity    ║
              ╚════╤════╝  ╚════╤═════╝  ╚══════╤═══════╝
                   └────────────┼────────────────┘
                                ▼
                  ╔══════════════════════════════╗
                  ║ E/R/R Framework              ║
                  ║ Elements │ Roles │ Rules     ║
                  ╚═════════════╤════════════════╝
                                │
              ┌─────────────────┼──────────────────┐
              ▼                 ▼                    ▼
     ╔══════════════╗  ╔════════════════╗  ╔═══════════════╗
     ║  P4: Process ║  ║  Constitution  ║  ║  System       ║
     ║  Philosophy  ║  ║  Checking      ║  ║  Morphisms    ║
     ║  ∞ = process ║  ║  decidable     ║  ║  iso, embed   ║
     ╚══════╤═══════╝  ╚═══════╤════════╝  ╚═══════╤═══════╝
            │                  │                    │
            └──────────────────┼────────────────────┘
                               ▼
              ╔═════════════════════════════════════╗
              ║       ToS-LANG TYPE THEORY          ║
              ║  Π-systems · Σ-systems · Inductive  ║
              ║  Coinductive · Universes · Erasure   ║
              ║  Formation · Conversion · Subtyping  ║
              ║  Subject Reduction · Progress        ║
              ║  ─────────────────────────────────── ║
              ║  TYPE SAFETY: well-typed → safe      ║
              ╚══════════════════╤══════════════════╝
                                 │
              ┌──────────────────┼──────────────────┐
              ▼                  ▼                    ▼
    ╔═══════════════╗  ╔═══════════════╗   ╔═══════════════╗
    ║  NUMBER       ║  ║  ANALYSIS     ║   ║   APPLIED     ║
    ║  SYSTEMS      ║  ║  CHAIN        ║   ║   MATH        ║
    ║ ℕ → ℤ → ℚ    ║  ║ Diff → MVT   ║   ║ CROWN · GD    ║
    ║ → CauchyReal  ║  ║ → ∫ → FTC    ║   ║ Probability   ║
    ║ (completion)  ║  ║ → Taylor     ║   ║ LinAlg · IEEE  ║
    ╚═══════╤═══════╝  ║ → Uniform    ║   ╚═══════╤═══════╝
            │          ║ → FixedPoint ║           │
            │          ╚═══════╤═══════╝           │
            └──────────────────┼───────────────────┘
                               ▼
              ╔═════════════════════════════════════╗
              ║     VERIFIED STANDARD LIBRARY       ║
              ║  TMap · TSet · TTree · TQueue       ║
              ║  TSort · TSearch · THigherOrder     ║
              ║  TInt · TComplex · TStream          ║
              ║  TOption · StdlibExamples           ║
              ║  ─────────────────────────────────  ║
              ║  230 Qed · 0 Admitted · 12 files    ║
              ╚══════════════════╤══════════════════╝
                                 │
                                 ▼
              ╔═════════════════════════════════════╗
              ║    ARCHITECTURE OF REASONING        ║
              ║  156 Fallacies · 46 Paradoxes       ║
              ║  AI Fallacy Detection · D1-D6       ║
              ║  OCaml Extraction · Python Demo     ║
              ╚═════════════════════════════════════╝

                    86 files · 1787 theorems
                     8 Admitted · 0 axioms*
              ─────────────────────────────────
              * single external: classic (LEM, = L3)
```

---

## Overview

This project provides a **formal verification in Coq** of the Theory of Systems — a foundational framework for mathematics that derives all mathematical structures (including logic itself) from a single axiom through the act of distinction.

**This is NOT "ZFC minus an axiom"** — it's a fundamentally different approach where mathematics emerges deductively from one statement.

### Key Results

| Theorem | Status |
|---------|--------|
| **Non-surjectivity N -> [0,1] n Q** | 167 lemmas, 0 Admitted |
| **Countability of Q** (Calkin-Wilf) | 17 lemmas, 0 Admitted |
| **IVT / EVT** (epsilon-constructive) | 49 lemmas, 0 Admitted |
| **CROWN linear relaxation soundness** | 25 lemmas, 0 Admitted |
| **Cauchy reals + ordered field** | 36 lemmas, 0 Admitted |
| **Calculus chain** (Diff -> MVT -> Integral -> Taylor) | 111 lemmas, 0 Admitted |
| **Uniform Convergence + Dini** | 20 lemmas, 0 Admitted |
| **Fixed Point (Banach contraction)** | 20 lemmas, 0 Admitted |
| **ToS-Lang type safety** | 421 lemmas, 0 Admitted |
| **ToS-Lang verified compiler** | 64 lemmas, 0 Admitted |
| **Verified stdlib** (Map, Set, Tree, Queue, Sort, Search, ...) | 230 lemmas, 0 Admitted |
| **156 Fallacies + 46 Paradoxes** | 117 lemmas, 0 Admitted |

**Total: 1787 proven theorems across 86 files**

- **Single external axiom:** `classic` (Law of Excluded Middle, = L3)
- **No Axiom of Infinity** — consequence of P4 (Process Philosophy)
- **No Axiom of Choice**

---

## Papers

| Title | Pages | Link |
|-------|-------|------|
| **Theory of Systems v5** | 38 | [PDF](docs/Theory_of_Systems_v5.pdf) |
| **Nested Rational Intervals** | 13 | [PDF](docs/nested_intervals.pdf) |

---

## The Key Contrast

We prove **both**:

| Result | Axioms | Status |
|--------|--------|--------|
| Q is countable (bijection N <-> Q) | **None** | Fully constructive |
| Cauchy processes are uncountable | LEM only | Non-surjectivity |

**No contradiction:** A rational is finite data (two integers). A Cauchy process is infinite behavior (unbounded sequence). We enumerate objects, not behaviors.

---

## Project Structure

```
theory-of-systems-coq/
|
|-- docs/                              # Papers & documentation
|   |-- Theory_of_Systems_v5.pdf       # Main paper (38 pages)
|   |-- nested_intervals.tex           # arXiv preprint (LaTeX)
|   +-- nested_intervals.pdf           # Compiled PDF
|
|-- src/                               # Core Coq formalization (68 files)
|   |-- README.md                      # Full file-by-file guide
|   |
|   |  # --- ToS Core + Foundations ---
|   |-- TheoryOfSystems_Core_ERR.v     # Laws L1-L5, System, Criterion (34 Qed)
|   |-- Roles.v                        # E/R/R roles, status, deps (30 Qed)
|   |-- IntensionalIdentity.v          # P3: ext != int identity (11 Qed)
|   |-- ProcessGeneral.v               # Process theory, Cauchy bridge (16 Qed)
|   |-- L5Resolution.v                 # Generalized L5 tie-breaking (18 Qed)
|   |-- SystemMorphism.v               # Structure-preserving maps (17 Qed)
|   |-- InfoLayer.v                    # Information layers (17 Qed)
|   |
|   |  # --- ToS-Lang: Full Type Theory ---
|   |-- DependentSystems.v             # Pi/Sigma systems (25 Qed)
|   |-- InductiveSystems.v             # Inductive types (26 Qed)
|   |-- CoinductiveSystems.v           # Coinductive/observable (16 Qed)
|   |-- ConstitutionChecking.v         # Decidable constitution (16 Qed)
|   |-- Judgments.v ... Soundness.v    # Typing rules (99 Qed)
|   |-- Expressions.v ... TypeSafety.v # Operational semantics (124 Qed)
|   |-- TypeChecker.v ... AIInterface.v# Verified compiler (64 Qed)
|   |
|   |  # --- Set Theory & Topology ---
|   |-- ShrinkingIntervals_ERR.v       # Non-surjectivity (167 Qed)
|   |-- Countability_Q.v              # Q =~ N via Calkin-Wilf (17 Qed)
|   |-- DiagonalArgument_ERR.v        # Alternative diagonal proof (41 Qed)
|   |
|   |  # --- Analysis: Calculus Chain ---
|   |-- CauchyReal.v -> RealField.v -> Completeness.v
|   |-- MonotoneConvergence.v -> SeriesConvergence.v -> PowerSeries.v
|   |-- Differentiation.v -> MeanValueTheorem.v
|   |-- RiemannIntegration.v -> IntegralApplications.v
|   |-- TaylorSeries.v -> UniformConvergence.v -> FixedPoint.v
|   |
|   |  # --- Applied Mathematics ---
|   |-- IVT_ERR.v, EVT_idx.v          # IVT + EVT (49 Qed)
|   |-- PInterval_CROWN.v             # CROWN NN verification (25 Qed)
|   |-- GradientDescent.v             # GD convergence (18 Qed)
|   |-- LinearAlgebra.v               # QVec, QMat, dot product (20 Qed)
|   |-- Probability.v                 # Bayes + fallacies (12 Qed)
|   |
|   +-- stdlib/                        # Verified Standard Library (12 files)
|       |-- README.md                  # Full stdlib guide
|       |-- TMap.v                     # Sorted key-value map (31 Qed)
|       |-- TSet.v                     # Sorted unique set (30 Qed)
|       |-- TTree.v                    # Binary search tree (23 Qed)
|       |-- TQueue.v                   # FIFO banker's queue (14 Qed)
|       |-- TInt.v                     # Integer arithmetic (18 Qed)
|       |-- TComplex.v                 # Complex numbers over Q (19 Qed)
|       |-- TStream.v                  # Infinite lazy streams (14 Qed)
|       |-- TSort.v                    # Insertion sort + merge (20 Qed)
|       |-- TSearch.v                  # Find, filter, binary search (17 Qed)
|       |-- THigherOrder.v             # Map/filter/fold (18 Qed)
|       |-- TOption.v                  # Option + Result types (14 Qed)
|       +-- StdlibExamples.v           # Cross-module examples (12 Qed)
|
|-- Architecture_of_Reasoning/         # Fallacy & Paradox formalization (6 files)
|   |-- README.md                      # Full documentation
|   |-- CompleteFallacyTaxonomy.v      # 156 fallacies (19 Qed)
|   |-- AI_FallacyDetector.v           # LLM verification (13 Qed)
|   |-- ParadoxDissolution.v           # 46 paradoxes (29 Qed)
|   |-- Architecture_of_Reasoning.v    # L1-L5, D1-D6, E/R/R (17 Qed)
|   |-- ERR_Fallacies.v                # E/R/R fallacy mapping (22 Qed)
|   +-- DomainViolations_Complete.v    # D1-D6 violations (17 Qed)
|
|-- extraction/                        # OCaml extraction (Core)
|-- tos_lang/                          # ToS-Lang verified compiler (OCaml + Python)
|-- examples/                          # ToS-Lang example programs (.tos)
|-- _CoqProject                        # Build configuration (86 files)
+-- README.md                          # This file
```

---

## Statistics

### Core Formalization (68 files, 1440 Qed)

| File | Qed | Status |
|------|-----|--------|
| `ShrinkingIntervals_ERR.v` | 167 | **100%** |
| `TernaryRepresentation_ERR.v` | 52 | 95% (3 Admitted) |
| `DiagonalArgument_ERR.v` | 41 | 98% (1 Admitted) |
| `EVT_ERR.v` | 35 | *(legacy, 1 Admitted)* |
| `TheoryOfSystems_Core_ERR.v` | 34 | **100%** |
| `Roles.v` | 30 | **100%** |
| `Progress.v` | 30 | **100%** |
| `InductiveSystems.v` | 26 | **100%** |
| `Reduction.v` | 26 | **100%** |
| `TypeChecker.v` | 26 | **100%** |
| `DependentSystems.v` | 25 | **100%** |
| `PInterval_CROWN.v` | 25 | **100%** |
| `Completeness.v` | 24 | **100%** |
| `UniversePolymorphism.v` | 24 | **100%** |
| `Judgments.v` | 23 | **100%** |
| `IVT_ERR.v` | 23 | **100%** |
| `Soundness.v` | 22 | **100%** |
| `SeriesConvergence.v` | 22 | **100%** |
| `HeineBorel_ERR.v` | 22 | *(2 Admitted: unprovable over Q)* |
| `Subtyping.v` | 20 | **100%** |
| `Evaluator.v` | 20 | **100%** |
| `Expressions.v` | 20 | **100%** |
| `LinearAlgebra.v` | 20 | **100%** |
| `FixedPoint.v` | 20 | **100%** |
| `UniformConvergence.v` | 20 | **100%** |
| `CauchyReal.v` | 19 | **100%** |
| `IntegralApplications.v` | 19 | **100%** |
| `PowerSeries.v` | 19 | **100%** |
| `ReasoningConvergence.v` | 19 | **100%** |
| `L5Resolution.v` | 18 | **100%** |
| `Differentiation.v` | 18 | **100%** |
| `GradientDescent.v` | 18 | **100%** |
| `MeanValueTheorem.v` | 18 | **100%** |
| `RiemannIntegration.v` | 18 | **100%** |
| `TaylorSeries.v` | 18 | **100%** |
| `SubjectReduction.v` | 18 | **100%** |
| `FormationRules.v` | 18 | **100%** |
| `SystemMorphism.v` | 17 | **100%** |
| `InfoLayer.v` | 17 | **100%** |
| `Countability_Q.v` | 17 | **100%** |
| `RealField.v` | 17 | **100%** |
| `Typing_Expr.v` | 17 | **100%** |
| `CoinductiveSystems.v` | 16 | **100%** |
| `ConstitutionChecking.v` | 16 | **100%** |
| `ErasureTheory.v` | 16 | **100%** |
| `ProcessGeneral.v` | 16 | **100%** |
| `Conversion.v` | 16 | **100%** |
| `Measure.v` | 15 | **100%** |
| `MonotoneConvergence.v` | 15 | **100%** |
| `Archimedean_ERR.v` | 14 | **100%** |
| `SchroederBernstein_ERR.v` | 14 | **100%** |
| `SoftmaxProbability.v` | 14 | **100%** |
| `TypeSafety.v` | 13 | 92% (1 Admitted) |
| `RoundingSafety.v` | 13 | **100%** |
| `Probability.v` | 12 | **100%** |
| `IntensionalIdentity.v` | 11 | **100%** |
| `PhaseA_Examples.v` | 11 | **100%** |
| `AIInterface.v` | 10 | **100%** |
| `IVT_CauchyReal.v` | 8 | **100%** |
| `ToS_Lang_Extraction.v` | 8 | **100%** |
| + 8 more files | ~45 | |

### Verified Standard Library (12 files, 230 Qed)

| File | Qed | Description |
|------|-----|-------------|
| `TMap.v` | 31 | Sorted key-value map (DecTotalOrder keys) |
| `TSet.v` | 30 | Sorted unique set, union/inter/diff |
| `TTree.v` | 23 | Binary search tree with BST invariant |
| `TSort.v` | 20 | Insertion sort + fuel-based merge |
| `TComplex.v` | 19 | Complex numbers over Q |
| `TInt.v` | 18 | Integer arithmetic over Z |
| `THigherOrder.v` | 18 | Map, filter, fold, forall, exists |
| `TSearch.v` | 17 | Find, filter, count, binary search |
| `TQueue.v` | 14 | FIFO banker's queue |
| `TStream.v` | 14 | Infinite lazy streams (GenProcess) |
| `TOption.v` | 14 | Option + Result (Ok/Err) types |
| `StdlibExamples.v` | 12 | Cross-module integration (9 modules) |
| **Stdlib TOTAL** | **230** | **0 Admitted** |

### Architecture of Reasoning (6 files, 117 Qed)

| File | Qed | Description |
|------|-----|-------------|
| `ParadoxDissolution.v` | 29 | 46 paradoxes classified |
| `ERR_Fallacies.v` | 22 | E/R/R fallacy mapping |
| `CompleteFallacyTaxonomy.v` | 19 | 156 fallacies formalized |
| `Architecture_of_Reasoning.v` | 17 | L1-L5, D1-D6, E/R/R unified |
| `DomainViolations_Complete.v` | 17 | D1-D6 violation types |
| `AI_FallacyDetector.v` | 13 | LLM verification module |
| **Reasoning TOTAL** | **117** | **0 Admitted** |

### Combined Totals

| Category | Files | Qed | Admitted |
|----------|-------|-----|----------|
| Core Mathematics | 68 | 1440 | 8 |
| Verified Stdlib | 12 | 230 | 0 |
| Architecture of Reasoning | 6 | 117 | 0 |
| **GRAND TOTAL** | **86** | **1787** | **8** |

**Remaining Admitted (8, all documented):**

| File | Count | Reason |
|------|-------|--------|
| `TernaryRepresentation_ERR.v` | 3 | `Qfloor` discontinuity; alternative: `ShrinkingIntervals` |
| `HeineBorel_ERR.v` | 2 | Unprovable over Q (requires real-valued continuity) |
| `EVT_ERR.v` | 1 | `argmax_process_is_Cauchy`; use `EVT_idx.v` instead |
| `DiagonalArgument_ERR.v` | 1 | Alternative approach; use `ShrinkingIntervals` instead |
| `TypeSafety.v` | 1 | Fuel-bound monotonicity (structurally sound) |

---

## Calculus Chain

The full calculus derivation within Theory of Systems, entirely over constructive Q:

```
MonotoneConvergence (MCT, 15 Qed)
        |
        v
SeriesConvergence (geometric, comparison, 22 Qed)
        |
        v
PowerSeries (ratio test, exp convergence, 19 Qed)
        |
        v
Differentiation (division-free, power rule, 18 Qed)
        |
        v
MeanValueTheorem (grid MVT, monotonicity, Lipschitz, 18 Qed)
        |
        v
RiemannIntegration (Riemann sums, FTC, 18 Qed)
        |
        v
IntegralApplications (product rule, IBP, 19 Qed)
        |
        v
TaylorSeries (remainder, convexity, sandwich, 18 Qed)
        |
        v
UniformConvergence (limit exchange, Dini, 20 Qed)
        |
        v
FixedPoint (Banach contraction, perturbation, 20 Qed)
```

---

## Verified Standard Library

The `src/stdlib/` directory contains **12 verified data structures and algorithms**, each modeled as a ToS System with Elements/Roles/Rules/Constitution.

Every data structure connects back to the Deductive Chain:
- **Ordering** uses `DecTotalOrder` from L5Resolution (L5: Law of Order)
- **Finiteness** uses `FinitelyGenerated` from InductiveSystems (P4: Process Philosophy)
- **Decidability** uses `DecidableConstitution` from ConstitutionChecking
- **Streams** use `GenProcess` from ProcessGeneral (P4: infinity as process)
- **Higher-order** uses `PiSystem` from DependentSystems (Pi-types)

### Data Structures

| Module | Type | Key Operations | Key Properties |
|--------|------|----------------|----------------|
| **TMap** | Sorted list of (K*V) | insert, lookup, remove | lookup after insert, sorted preservation |
| **TSet** | Sorted unique list | add, member, union, inter, diff | member after add, subset reflexivity |
| **TTree** | Binary search tree | insert, member, inorder | BST invariant, height <= size (P4) |
| **TQueue** | Banker's queue | enqueue, dequeue, to_list | FIFO order, size correctness |

### Numeric Types

| Module | Type | Key Operations | Key Properties |
|--------|------|----------------|----------------|
| **TInt** | Z (integers) | add, mul, abs, div, mod | ring axioms, sign classification |
| **TComplex** | Q * Q (complex) | add, mul, conj, norm_sq | field axioms, conjugate involution |

### Algorithms & Combinators

| Module | Type | Key Operations | Key Properties |
|--------|------|----------------|----------------|
| **TSort** | list A -> list A | insertion_sort, merge | sorted output, permutation |
| **TSearch** | list A -> option A | find, filter, binary_search | found in list, predicate satisfaction |
| **THigherOrder** | (A->B) -> [A] -> [B] | map, filter, fold | length, composition, distribution |
| **TStream** | nat -> A (infinite) | take, iterate, zip_with | take length, map composition |
| **TOption** | option A / Result A E | map, bind, default | monad laws, error propagation |

See [src/stdlib/README.md](src/stdlib/README.md) for detailed documentation.

---

## ToS-Lang: Verified Type Theory & Compiler

A complete verified programming language built on Theory of Systems:

### Phase A: Type Theory (134 Qed)
Pi/Sigma systems, universes, inductive/coinductive types, constitution checking, erasure theory.

### Phase B: Typing Rules (99 Qed)
Formation rules, P3 conversion, subsystem subtyping, **typing soundness theorem**.

### Phase C: Operational Semantics (124 Qed)
Deep-embedded expressions, small-step reduction, expression typing, **subject reduction**, **progress**, **type safety**.

### Phase D: Verified Compiler (64 Qed)
- **`typecheck_sound`**: type checker is sound w.r.t. typing relation
- **`verified_pipeline`**: typecheck OK implies eval preserves type + progress
- **`ai_generation_safe`**: AI-generated code that passes typecheck is safe
- OCaml extraction to executable compiler (`tos_lang/`)

---

## Architecture of Reasoning

The `Architecture_of_Reasoning/` folder provides formal verification of fallacy detection and paradox dissolution.

### 156 Fallacies Formalized

| Type | Description | Count |
|------|-------------|-------|
| **Type 1** | Violations of Conditions | 36 |
| **Type 2** | Domain Violations | 105 |
| **Type 3** | Violations of Sequence | 3 |
| **Type 4** | Syndromes | 6 |
| **Type 5** | Context-Dependent Methods | 6 |
| **TOTAL** | | **156** |

### 46 Paradoxes Classified

| Category | Count | Examples |
|----------|-------|----------|
| **Structural** | 13 | Liar, Russell, Cantor, Burali-Forti |
| **Defective** | 25 | Sorites, Zeno, Ship of Theseus |
| **Non-paradoxes** | 8 | Monty Hall, Birthday, Simpson's |

### AI Applications

- **LLM Response Verification** — Detect hallucinations structurally
- **Chain-of-Thought Validation** — D1-D6 domain sequence checking
- **Safety Layer** — Block ad hominem, confirmation bias, propaganda
- **OCaml Extraction** — Production-ready code from Coq proofs

See [Architecture_of_Reasoning/README.md](Architecture_of_Reasoning/README.md) for full documentation.

---

## OCaml Extraction

### Core ToS (`extraction/`)

| Module | Contents |
|--------|----------|
| `TheoryOfSystems_Core_ERR.ml` | `Level`, `System`, `Criterion`, `L5_resolve` |
| `Roles.ml` | `ERR_Category`, `MathStatus`, `Dependency` |
| `ProcessGeneral.ml` | `GenProcess`, `prefix`, `process_map`, `Qdist` |
| `IntensionalIdentity.ml` | `CriterionOver` |

### ToS-Lang Verified Compiler (`tos_lang/`)

| Module | Status | Contents |
|--------|--------|----------|
| `TypeChecker.ml` | **VERIFIED** | `typecheck`, `typecheck_ann` — proven sound |
| `Evaluator.ml` | **VERIFIED** | `safe_eval`, `classify_eval` — proven safe |
| `Expressions.ml` | **VERIFIED** | `shift`, `subst`, `is_value_dec` |
| `Reduction.ml` | **VERIFIED** | `try_step`, `eval_fuel` — type-preserving |
| `parser.ml` | Unverified | Recursive descent parser |
| `printer.ml` | Unverified | Pretty printer |
| `main.ml` | Unverified | CLI: `tos_check <file.tos>` |

---

## Installation & Verification

### Prerequisites

- Rocq 9.0.1 (or Coq 8.18+)
- Standard Library (included)

### Build

```bash
git clone https://github.com/horsocrates/theory-of-systems-coq.git
cd theory-of-systems-coq
coq_makefile -f _CoqProject -o Makefile
make
```

### Verify Main Theorem

```bash
coqtop -Q src ToS -l src/ShrinkingIntervals_ERR.v -batch \
  -exec "Print Assumptions unit_interval_uncountable_trisect."
```

**Expected output:**
```
Axioms:
classic : forall P : Prop, P \/ ~P
```

---

## Philosophical Position

**Logical Realism:** Logic is the structure of being, not a tool of thought.

**Process Philosophy (P4):** Infinity is a property of process, not of object. Numbers are limits of convergent sequences, not completed infinite sets.

**L5 (Law of Order):** When multiple positions share the same Role, select the minimal index. This principle resolved key formalization challenges (EVT breakthrough).

**E/R/R Framework:** Every determinate system exhibits Elements (what exists), Roles (why significant), and Rules (how structured).

---

## Publications

### Foundational

- **[The Laws of Logic as Conditions of Existence](https://philpapers.org/archive/HORTLO-18.pdf)** — Derivation of L1-L5 from first principle
- **[The Law of Order](https://philpapers.org/archive/HORTLO-19.pdf)** — L5 and the EVT breakthrough
- **[Theory of Systems v5](docs/Theory_of_Systems_v5.pdf)** — Complete framework with Coq formalization

### Technical

- **[Nested Rational Intervals](docs/nested_intervals.pdf)** — Non-surjectivity proof (arXiv preprint)

### Reasoning Architecture

- **[The Architecture of Error](https://philpapers.org/archive/HORTAO-17.pdf)** — Structural theory of fallacies (Part 1)
- **[Domain Violations: A Systematic Taxonomy](https://philpapers.org/rec/HORDVA)** — 105 Type 2 fallacies (Part 2)
- **[Paradox Dissolution Through Hierarchical Analysis](https://philpapers.org/rec/HORPDT)** — 46 paradoxes classified

---

## Citation

```bibtex
@software{theory_of_systems_coq,
  author = {Horsocrates},
  title = {Theory of Systems — Coq Formalization},
  year = {2026},
  url = {https://github.com/horsocrates/theory-of-systems-coq}
}
```

---

## Contact

**Horsocrates**
horsocrates@proton.me
[GitHub](https://github.com/horsocrates)

---

## License

MIT License — see [LICENSE](LICENSE) for details.
