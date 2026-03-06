# Theory of Systems — Coq Formalization

[![Rocq](https://img.shields.io/badge/Rocq-9.0.1-blue.svg)](https://coq.inria.fr/)
[![Status](https://img.shields.io/badge/Status-99%25_Complete-green.svg)]()
[![Theorems](https://img.shields.io/badge/Theorems-1485_Proven-brightgreen.svg)]()
[![Fallacies](https://img.shields.io/badge/Fallacies-156-blue.svg)]()
[![Paradoxes](https://img.shields.io/badge/Paradoxes-46-blue.svg)]()
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **A complete deductive derivation of mathematics from a single first principle: "A = exists"**

---

## Overview

This project provides a **formal verification in Coq** of the Theory of Systems — a foundational framework for mathematics that derives all mathematical structures (including logic itself) from a single axiom through the act of distinction.

**This is NOT "ZFC minus an axiom"** — it's a fundamentally different approach where mathematics emerges deductively from one statement.

### The Deductive Chain

```
A = exists → Distinction (A/¬A) → Laws of Logic (L1–L5) → Principles (P1–P4) → Number Systems → Classical Analysis
```

### Key Results

| Theorem | Status |
|---------|--------|
| **Non-surjectivity ℕ → [0,1] ∩ ℚ** | 167 lemmas, 0 Admitted |
| **Countability of ℚ** (Calkin-Wilf) | 17 lemmas, 0 Admitted |
| **ε-Intermediate Value Theorem** | 23 lemmas, 0 Admitted |
| **ε-Extreme Value Theorem** | 26 lemmas, 0 Admitted |
| **CROWN linear relaxation soundness** | 25 lemmas, 0 Admitted |
| **Cauchy reals (constructive completion)** | 19 lemmas, 0 Admitted |
| **Rounding safety (IEEE 754)** | 13 lemmas, 0 Admitted |
| **Bayes' theorem + probabilistic fallacies** | 12 lemmas, 0 Admitted |
| **Constructive measure & integration** | 15 lemmas, 0 Admitted |
| **Softmax probability soundness** | 14 lemmas, 0 Admitted |
| **Ordered field on Cauchy reals** | 15 lemmas, 0 Admitted |
| **Metric completeness (NIP, sup, diagonal)** | 23 lemmas, 0 Admitted |
| **Monotone Convergence Theorem** | 15 lemmas, 0 Admitted |
| **Series Convergence (geometric, comparison)** | 22 lemmas, 0 Admitted |
| **Power Series + Exponential convergence** | 19 lemmas, 0 Admitted |
| **Gradient Descent convergence (quadratic)** | 18 lemmas, 0 Admitted |
| **Differentiation (division-free, power rule)** | 18 lemmas, 0 Admitted |
| **Mean Value Theorem (grid MVT, monotonicity, Lipschitz)** | 18 lemmas, 0 Admitted |
| **Riemann Integration (FTC, integral comparison)** | 18 lemmas, 0 Admitted |
| **Integral Applications (product rule, IBP)** | 18 lemmas, 0 Admitted |
| **Taylor Series (remainder, convexity, sandwich)** | 18 lemmas, 0 Admitted |
| **Uniform Convergence (limit exchange, Dini)** | 20 lemmas, 0 Admitted |
| **Fixed Point Theory (Banach contraction, perturbation)** | 20 lemmas, 0 Admitted |
| **E/R/R Roles, Status, Dependencies, Paradox diagnosis** | 30 lemmas, 0 Admitted |
| **P3 Intensional Identity (ext ≠ int separation)** | 11 lemmas, 0 Admitted |
| **General Process Theory (GenProcess, Cauchy bridge)** | 16 lemmas, 0 Admitted |
| **L5 Resolution (generalized tie-breaking)** | 18 lemmas, 0 Admitted |
| **System Morphisms (structure-preserving maps)** | 17 lemmas, 0 Admitted |
| **Information Layers (composition, capacity)** | 17 lemmas, 0 Admitted |
| **Linear Algebra (QVec, QMat, dot product)** | 20 lemmas, 0 Admitted |
| **ToS-Lang Type Theory (Π/Σ, universes, inductive, coinductive)** | 134 lemmas, 0 Admitted |
| **ToS-Lang Typing Rules (formation, conversion, subtyping, soundness)** | 99 lemmas, 0 Admitted |
| **ToS-Lang Operational Semantics (reduction, progress, type safety)** | 124 lemmas, 0 Admitted |
| **ToS-Lang Verified Compiler (type checker, evaluator, extraction, AI)** | 64 lemmas, 0 Admitted |
| **OCaml Extraction (Level, System, Roles, Process)** | 4 modules + deps |
| **ToS-Lang OCaml Extraction (TypeChecker, Evaluator, Expressions)** | 11 modules |
| **156 Fallacies Formalized** | Complete taxonomy |
| **46 Paradoxes Classified** | All dissolved |

**Total: 1485 proven theorems (1368 core + 117 reasoning architecture)**

- **Single external axiom:** `classic` (Law of Excluded Middle, L3)
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
| ℚ is countable (bijection ℕ ↔ ℚ) | **None** | Fully constructive |
| Cauchy processes are uncountable | LEM only | Non-surjectivity |

**No contradiction:** A rational is finite data (two integers). A Cauchy process is infinite behavior (unbounded sequence). We enumerate objects, not behaviors.

---

## Project Structure

```
theory-of-systems-coq/
│
├── docs/                              # Papers & documentation
│   ├── Theory_of_Systems_v5.pdf       # Main paper (38 pages)
│   ├── nested_intervals.tex           # arXiv preprint (LaTeX)
│   └── nested_intervals.pdf           # Compiled PDF
│
├── src/                               # Coq source files (63 files)
│   │
│   │  # === ToS Core + Foundations ===
│   ├── TheoryOfSystems_Core_ERR.v    # Laws L1-L5, System, Criterion, paradox blocking (34 Qed)
│   ├── Roles.v                       # E/R/R roles, status, deps, paradox diagnosis (30 Qed)
│   ├── IntensionalIdentity.v         # P3: extensional ≠ intensional identity (11 Qed)
│   ├── ProcessGeneral.v              # General process theory, Cauchy bridge (16 Qed)
│   ├── L5Resolution.v               # Generalized L5 tie-breaking with DecTotalOrder (18 Qed) ← NEW
│   ├── SystemMorphism.v             # Structure-preserving maps, isomorphisms (17 Qed) ← NEW
│   ├── InfoLayer.v                  # Information layers, composition, capacity (17 Qed) ← NEW
│   ├── Extraction.v                  # OCaml extraction directives
│   │
│   │  # === ToS-Lang: Type Theory + Typing Rules (Phase A+B) ===
│   ├── DependentSystems.v            # Π/Σ systems (25 Qed)
│   ├── InductiveSystems.v            # Inductive types (26 Qed)
│   ├── CoinductiveSystems.v          # Coinductive/observable (16 Qed)
│   ├── ConstitutionChecking.v        # Decidable constitution (16 Qed)
│   ├── PhaseA_Examples.v             # Phase A integration examples (11 Qed)
│   ├── Judgments.v                    # Typing judgments (23 Qed)
│   ├── FormationRules.v              # Formation rules (18 Qed)
│   ├── Conversion.v                  # P3 conversion rules (16 Qed)
│   ├── Subtyping.v                   # Subsystem subtyping (20 Qed)
│   ├── Soundness.v                   # Typing soundness (22 Qed)
│   │
│   │  # === ToS-Lang: Operational Semantics (Phase C) ===
│   ├── Expressions.v                 # Deep-embedded Expr type (20 Qed)
│   ├── Reduction.v                   # Small-step reduction (26 Qed)
│   ├── Typing_Expr.v                 # Expression typing relation (17 Qed)
│   ├── SubjectReduction.v            # Subject reduction (18 Qed)
│   ├── Progress.v                    # Progress theorem (30 Qed)
│   ├── TypeSafety.v                  # Type safety + main theorem (13 Qed)
│   │
│   │  # === ToS-Lang: Verified Compiler (Phase D) ===
│   ├── TypeChecker.v                 # Verified type checker (26 Qed) ← NEW
│   ├── Evaluator.v                   # Verified evaluator wrapper (20 Qed) ← NEW
│   ├── AIInterface.v                 # AI generation safety spec (10 Qed) ← NEW
│   ├── ToS_Lang_Extraction.v         # OCaml extraction (8 Qed) ← NEW
│   │
│   │  # === Set Theory & Topology ===
│   ├── ShrinkingIntervals_ERR.v       # Non-surjectivity ℕ → [0,1] ∩ ℚ (167 Qed)
│   ├── Countability_Q.v              # ℚ ≅ ℕ via Calkin-Wilf (17 Qed)
│   ├── SchroederBernstein_ERR.v      # Injection theorem (14 Qed)
│   ├── DiagonalArgument_ERR.v        # Alternative diagonal proof (41 Qed)
│   ├── TernaryRepresentation_ERR.v   # Digit representation (52 Qed)
│   ├── HeineBorel_ERR.v              # Compactness (partial — needs ℝ)
│   │
│   │  # === Analysis: Foundations ===
│   ├── Archimedean_ERR.v             # Archimedean property (14 Qed)
│   ├── CauchyReal.v                  # Cauchy reals: completion of ℚ (19 Qed)
│   ├── RealField.v                   # Ordered field on Cauchy reals (17 Qed)
│   ├── Completeness.v                # Metric completeness: NIP, sup, diagonal (24 Qed)
│   │
│   │  # === Analysis: Calculus Chain (B16-B22) ===
│   ├── MonotoneConvergence.v         # MCT (15 Qed)
│   ├── SeriesConvergence.v           # Geometric, comparison series (22 Qed)
│   ├── PowerSeries.v                 # Power series + exp convergence (19 Qed)
│   ├── FixedPoint.v                  # Banach contraction mapping (20 Qed)
│   ├── GradientDescent.v            # GD convergence for quadratic loss (18 Qed)
│   ├── Differentiation.v            # Division-free derivatives, power rule (18 Qed)
│   ├── MeanValueTheorem.v           # Grid MVT, monotonicity, Lipschitz (18 Qed)
│   ├── RiemannIntegration.v         # Riemann sums, FTC (18 Qed)
│   ├── IntegralApplications.v      # Product rule, IBP (19 Qed)
│   ├── TaylorSeries.v              # Taylor remainder, convexity (18 Qed)
│   ├── UniformConvergence.v        # Limit exchange, Dini (20 Qed)
│   │
│   │  # === Applied: IVT, EVT, NN Verification ===
│   ├── IVT_ERR.v                     # ε-IVT (23 Qed)
│   ├── IVT_CauchyReal.v             # Full IVT on Cauchy reals (8 Qed)
│   ├── EVT_idx.v                     # ε-EVT, L5-compliant (26 Qed)
│   ├── EVT_ERR.v                     # EVT (legacy, 35 Qed)
│   ├── PInterval_CROWN.v            # CROWN linear relaxation soundness (25 Qed)
│   ├── LinearAlgebra.v              # QVec, QMat, dot product, mat-vec multiply (20 Qed) ← NEW
│   ├── RoundingSafety.v              # IEEE 754 rounding within intervals (13 Qed)
│   ├── SoftmaxProbability.v         # Softmax probability soundness (14 Qed)
│   ├── Probability.v                # Probability + Bayesian fallacies (12 Qed)
│   └── Measure.v                   # Constructive measure & integration (15 Qed)
│
├── Architecture_of_Reasoning/         # Fallacy & Paradox formalization (6 files, 117 Qed)
│   ├── README.md
│   ├── CompleteFallacyTaxonomy.v      # All 156 fallacies (19 Qed)
│   ├── AI_FallacyDetector.v           # LLM verification module (13 Qed)
│   ├── ParadoxDissolution.v           # 46 paradoxes classified (29 Qed)
│   ├── Architecture_of_Reasoning.v    # Unified L1-L5, D1-D6, E/R/R (17 Qed)
│   ├── ERR_Fallacies.v                # E/R/R fallacy mapping (22 Qed)
│   ├── DomainViolations_Complete.v    # D1-D6 violation types (17 Qed)
│   ├── ai_fallacy_detector.ml         # OCaml extraction
│   └── demo.py                        # Python demo
│
├── extraction/                        # OCaml extraction output (Core)
│   ├── TheoryOfSystems_Core_ERR.ml   # Level, System, Criterion, L5_resolve
│   ├── Roles.ml                      # ERR_Category, MathStatus, Dependencies
│   ├── ProcessGeneral.ml             # GenProcess, prefix, process_map, Qdist
│   ├── IntensionalIdentity.ml        # CriterionOver
│   ├── diagonal_demo.ml              # Standalone Calkin-Wilf + diagonal demo
│   └── *.ml, *.mli                   # Stdlib deps (BinInt, QArith, etc.)
│
├── tos_lang/                          # ToS-Lang verified compiler ← NEW
│   ├── TypeChecker.ml                # VERIFIED type checker (extracted from Coq)
│   ├── Evaluator.ml                  # VERIFIED evaluator (extracted from Coq)
│   ├── Expressions.ml               # Expression types (extracted)
│   ├── Reduction.ml                  # Step evaluator (extracted)
│   ├── parser.ml                     # Hand-written recursive descent parser
│   ├── printer.ml                    # Pretty printer for Expr/Ty
│   ├── main.ml                       # CLI entry point
│   ├── ai_interface.py              # Python AI generation + verification
│   └── dune                          # OCaml build file
│
├── examples/                          # ToS-Lang example programs ← NEW
│   ├── identity.tos                  # (\(x : Nat). x) 42
│   ├── pair_fst.tos                  # fst (42, 7)
│   ├── higher_order.tos             # Higher-order function application
│   ├── compose.tos                   # Function composition
│   ├── swap.tos                      # Pair swap
│   └── ...                           # 8 examples total
│
├── _CoqProject                        # Build configuration (69 files)
├── CoqMakefile                        # Generated Makefile
├── .github/workflows/coq-ci.yml      # CI
└── README.md
```

---

## Statistics

### Core Formalization (63 files)

| File | Qed | Admitted | Status |
|------|-----|----------|--------|
| `ShrinkingIntervals_ERR.v` | 167 | 0 | **100%** |
| `TernaryRepresentation_ERR.v` | 52 | 2 | 96% |
| `DiagonalArgument_ERR.v` | 41 | 1 | 98% |
| `EVT_ERR.v` | 35 | 1 | *(legacy)* |
| `TheoryOfSystems_Core_ERR.v` | 34 | 2 | 94% |
| `Roles.v` | 30 | 0 | **100%** |
| `EVT_idx.v` | 26 | 0 | **100%** |
| `PInterval_CROWN.v` | 25 | 0 | **100%** |
| `Completeness.v` | 24 | 0 | **100%** |
| `IVT_ERR.v` | 23 | 0 | **100%** |
| `SeriesConvergence.v` | 22 | 0 | **100%** |
| `HeineBorel_ERR.v` | 22 | 2 | *(unprovable over ℚ)* |
| `LinearAlgebra.v` | 20 | 0 | **100%** ← NEW |
| `FixedPoint.v` | 20 | 0 | **100%** |
| `UniformConvergence.v` | 20 | 0 | **100%** |
| `CauchyReal.v` | 19 | 0 | **100%** |
| `IntegralApplications.v` | 19 | 0 | **100%** |
| `PowerSeries.v` | 19 | 0 | **100%** |
| `L5Resolution.v` | 18 | 0 | **100%** ← NEW |
| `Differentiation.v` | 18 | 0 | **100%** |
| `GradientDescent.v` | 18 | 0 | **100%** |
| `MeanValueTheorem.v` | 18 | 0 | **100%** |
| `RiemannIntegration.v` | 18 | 0 | **100%** |
| `TaylorSeries.v` | 18 | 0 | **100%** |
| `SystemMorphism.v` | 17 | 0 | **100%** ← NEW |
| `InfoLayer.v` | 17 | 0 | **100%** ← NEW |
| `Countability_Q.v` | 17 | 0 | **100%** |
| `RealField.v` | 17 | 0 | **100%** |
| `ProcessGeneral.v` | 16 | 0 | **100%** |
| `Measure.v` | 15 | 0 | **100%** |
| `MonotoneConvergence.v` | 15 | 0 | **100%** |
| `Archimedean_ERR.v` | 14 | 0 | **100%** |
| `SchroederBernstein_ERR.v` | 14 | 0 | **100%** |
| `SoftmaxProbability.v` | 14 | 0 | **100%** |
| `RoundingSafety.v` | 13 | 0 | **100%** |
| `Probability.v` | 12 | 0 | **100%** |
| `IntensionalIdentity.v` | 11 | 0 | **100%** |
| `IVT_CauchyReal.v` | 8 | 0 | **100%** |
| **ToS-Lang Phase A+B+C+D** | | | |
| `Progress.v` | 30 | 0 | **100%** |
| `InductiveSystems.v` | 26 | 1 | 96% |
| `Reduction.v` | 26 | 0 | **100%** |
| `TypeChecker.v` | 26 | 0 | **100%** ← NEW |
| `DependentSystems.v` | 25 | 0 | **100%** |
| `UniversePolymorphism.v` | 24 | 0 | **100%** |
| `Judgments.v` | 23 | 0 | **100%** |
| `Soundness.v` | 22 | 0 | **100%** |
| `Evaluator.v` | 20 | 0 | **100%** ← NEW |
| `Expressions.v` | 20 | 0 | **100%** |
| `Subtyping.v` | 20 | 0 | **100%** |
| `SubjectReduction.v` | 18 | 0 | **100%** |
| `FormationRules.v` | 18 | 0 | **100%** |
| `Typing_Expr.v` | 17 | 0 | **100%** |
| `Conversion.v` | 16 | 0 | **100%** |
| `CoinductiveSystems.v` | 16 | 0 | **100%** |
| `ConstitutionChecking.v` | 16 | 0 | **100%** |
| `ErasureTheory.v` | 16 | 1 | 94% |
| `TypeSafety.v` | 13 | 1 | 92% |
| `PhaseA_Examples.v` | 11 | 1 | 91% |
| `AIInterface.v` | 10 | 0 | **100%** ← NEW |
| `ToS_Lang_Extraction.v` | 8 | 0 | **100%** ← NEW |
| **Core TOTAL** | **1368** | **13** | **99.1%** |

### Architecture of Reasoning

| File | Theorems | Admitted |
|------|----------|----------|
| `CompleteFallacyTaxonomy.v` | 19 | **0** |
| `AI_FallacyDetector.v` | 20 | **0** |
| `ParadoxDissolution.v` | 29 | **0** |
| `Architecture_of_Reasoning.v` | 17 | **0** |
| `ERR_Fallacies.v` | 22 | **0** |
| `DomainViolations_Complete.v` | 10 | **0** |
| **Reasoning TOTAL** | **117** | **0** |

### Combined

| Category | Theorems | Admitted |
|----------|----------|----------|
| Core Mathematics | 1368 | 13 |
| Architecture of Reasoning | 117 | 0 |
| **TOTAL** | **1485** | **13** |

**Remaining Admitted (13, documented):**

| File | Count | Reason |
|------|-------|--------|
| `TernaryRepresentation_ERR.v` | 3 | `Qfloor` discontinuity; alternative: `ShrinkingIntervals` |
| `TheoryOfSystems_Core_ERR.v` | 2 | Universe polymorphism limitations (intentional) |
| `HeineBorel_ERR.v` | 2 | Unprovable over ℚ (requires real-valued continuity) |
| `EVT_ERR.v` | 1 | `argmax_process_is_Cauchy` — requires monotone refinement; use `EVT_idx.v` |
| `DiagonalArgument_ERR.v` | 1 | Alternative approach; use `ShrinkingIntervals` instead |
| `TypeSafety.v` | 1 | Fuel-bound monotonicity (structurally sound) |
| `InductiveSystems.v` | 1 | Dependent pattern matching |
| `ErasureTheory.v` | 1 | Universe level mismatch |
| `PhaseA_Examples.v` | 1 | Integration example |

---

## New in March 2026

### ToS-Lang Phase D: Verified Compiler (64 Qed, 0 Admitted)

A verified compiler for the ToS-Lang expression language, with type checker and evaluator extracted from Coq proofs to OCaml.

#### Verified Type Checker (`TypeChecker.v` — 26 Qed, 0 Admitted)

Decision procedure for `expr_has_type`, proven sound against the Phase C specification:
- `typecheck`: `TyCtx -> Expr -> option Ty` — total, decidable type checking
- `ExprAnn` / `typecheck_ann`: Church-style annotated expressions with full lambda type checking
- **`typecheck_sound`**: `typecheck G e = Some T -> expr_has_type G e T`
- **`typecheck_ann_sound`**: soundness for annotated expressions
- `erase_ann`: annotation erasure preserving semantics
- Equation lemmas, inversion lemmas, determinism, examples

#### Verified Evaluator (`Evaluator.v` — 20 Qed, 0 Admitted)

Safe evaluation pipeline wrapping `eval_fuel` with type checking:
- `safe_eval`: only evaluates well-typed expressions
- `classify_eval`: returns `ER_Value | ER_Partial | ER_TypeError`
- **`verified_pipeline`**: THE theorem — typecheck OK → eval preserves type + progress
- `classify_value_correct`, `classify_partial_correct`, `classify_error_correct`
- Termination, determinism, annotated pipeline support

#### AI Interface Specification (`AIInterface.v` — 10 Qed, 0 Admitted)

End-to-end safety guarantee for AI-generated code verification:
- **`ai_generation_safe`**: if AI output passes `typecheck_ann`, evaluation with any fuel produces a well-typed result satisfying progress
- `ai_verified_well_typed`, `ai_verified_progress`: component guarantees
- `ai_eval_sound`, `ai_eval_ann_sound`: evaluation soundness

#### OCaml Extraction (`ToS_Lang_Extraction.v` — 8 Qed + 11 modules)

Extracts verified type checker and evaluator to executable OCaml:
- `TypeChecker.ml`, `Evaluator.ml`, `Expressions.ml`, `Reduction.ml` — proven correct
- Parser (`parser.ml`), printer (`printer.ml`), CLI (`main.ml`) — handwritten glue
- `ai_interface.py` — Python AI generation + verification loop
- 8 example `.tos` programs

### Phase 3: L5 Resolution, System Morphisms, Info Layers, Linear Algebra + Admitted Closures

Four new files formalize generalized ToS infrastructure and multi-dimensional verification support:

#### Generalized L5 Resolution (`L5Resolution.v` — 18 Qed, 0 Admitted)

Typeclass-based deterministic tie-breaking that generalizes beyond L1/L2/L3:
- `DecTotalOrder`: typeclass for decidable total orders with `dto_compare`
- `l5_resolve_gen`: generalized L5 resolution — select minimal element from non-empty list
- `l5_resolve_gen_in`: result is always a member of the input list
- `l5_resolve_gen_minimal`: result is ≤ all other list elements
- `l5_resolve_gen_unique`: deterministic — same list always gives same result
- Instances for `nat`, `Q`, `Z` with full proofs

#### System Morphisms (`SystemMorphism.v` — 17 Qed, 0 Admitted)

Structure-preserving maps between systems with composition and isomorphism:
- `sys_morphism`: maps between systems preserving criteria count and validity
- `sys_iso`: isomorphisms with inverse and round-trip proofs
- `morphism_compose`: composition of morphisms is a morphism
- `morphism_id`: identity morphism on any system
- `iso_compose`: composition of isomorphisms is an isomorphism
- `iso_preserves_criteria_count`: isomorphic systems have equal criteria count

#### Information Layers (`InfoLayer.v` — 17 Qed, 0 Admitted)

Formalization of information flow between system levels:
- `InfoLayer`: record with source/target levels, channel capacity, transform
- `layer_equiv`: equivalence relation on layers (reflexive, symmetric, transitive)
- `layer_compose`: sequential composition of compatible layers
- `layer_compose_assoc`: composition is associative
- `channel_capacity_nonneg`: capacity is always non-negative
- `layer_compose_capacity_min`: composed capacity bounded by minimum

#### Linear Algebra over Q (`LinearAlgebra.v` — 20 Qed + 4 Defined, 0 Admitted)

Length-indexed vectors and matrices over Q with full algebraic properties:
- `QVec n`: length-indexed vectors with pointwise Qeq equality
- `QMat rows cols`: matrices as lists of row vectors
- `qv_add`, `qv_scale`, `dot_product`, `mat_vec_mul`: core operations
- `qv_add_comm`, `qv_add_assoc`: vector addition is commutative and associative
- `qv_scale_distrib`, `qv_scale_assoc`: scalar multiplication distributes and associates
- `dot_product_comm`, `dot_product_zero_right`: dot product properties

#### EVT Admitted Closures (EVT_ERR.v — +4 Qed, −2 Admitted)

Closed two previously Admitted lemmas in EVT_ERR.v:
- `max_on_grid_attained`: proved via UC-implies-Proper for Qeq
- `EVT_complete`: proved 4 conjuncts using argmax_is_max + grid_value_le_max
- Added `Qabs_small_eq_zero` (Archimedean squeeze) and `uc_implies_proper` helpers

### Phase 2: ToS-Lang Foundations — Roles, Identity, Processes + OCaml Extraction

Three new files formalize the core Theory of Systems concepts, with all proofs extracted to executable OCaml:

#### E/R/R Roles, Status & Dependencies (`Roles.v` — 30 Qed, 0 Admitted)

Full formalization of the E/R/R framework from the ERR paper:
- `RoleAssignment`: Element-to-role binding with level proof
- `ERR_Category`: Three-fold classification (Element / Role / Rule)
- `MathStatus` / `EpistemicStatus`: Status as **derived** concept (not a fourth primitive)
- `Dependency` with `DepDirection` (Vertical / Horizontal / External)
- `reachable_in`: Fuel-bounded graph reachability for cycle detection
- `strongly_acyclic`: No element reaches itself through any dependency chain
- `ERR_WellFormed_Full`: 4-condition well-formedness (ERR paper §7)
- **`circular_dep_is_paradox`**: Unified paradox diagnosis — `s = negb s → False`
- `russell_is_circular_status`, `liar_is_circular_status`: Classical paradoxes as circular status
- `no_fixpoint_no_status`, `well_formed_no_paradox`: Well-formedness prevents paradoxes

#### P3: Intensional Identity (`IntensionalIdentity.v` — 11 Qed, 0 Admitted)

Formal proof that extensional equivalence ≠ intensional identity:
- `CriterionOver`: Domain-fixed criterion record (avoids dependent type transport)
- `ext_equiv`: Extensional equivalence (same elements) as equivalence relation
- **`extensional_not_implies_intensional`**: Separation theorem — two criteria accepting the same elements can have different level witnesses → different P3 identity
- `system_P3_separation`: Lifts the separation result to full `System` records

#### General Process Theory (`ProcessGeneral.v` — 16 Qed, 0 Admitted)

Universal step-indexed computation type bridging to Cauchy analysis:
- `GenProcess A := nat → A`: Universal process type
- `observe`, `prefix`, `process_map`, `const_process`: Core operations
- `process_equiv` as equivalence relation (refl / sym / trans)
- `is_cauchy_gen`: Cauchy condition on Q-valued processes via `Qdist`
- `cauchy_seq_is_gen_process`: Bridge from `CauchyQ` to `GenProcess Q`
- `process_map_cauchy`: Non-expansive maps preserve Cauchy property

#### OCaml Extraction (`Extraction.v` → `extraction/`)

All key ToS types extracted to executable OCaml:
- `Level`, `System`, `Criterion`, `StructuredSystem`, `L5_resolve`
- `ERR_Category`, `MathStatus`, `EpistemicStatus`, `Dependency`
- `GenProcess`, `prefix`, `process_map`, `Qdist`
- `role_candidates`, `resolve_role` (L5 integration)
- Prop fields correctly erased; `nat → int` via `ExtrOcamlNatInt`

### Fixed Point Theory — Banach Contraction, Perturbation Stability (`FixedPoint.v`)

Banach contraction mapping theorem and fixed point theory over constructive Q:
- `is_contraction`: contraction mapping definition on [a,b] with factor 0 ≤ c < 1
- `iterate`: iterated function application f^n(x)
- `iterate_in_interval`, `iterate_shift`: iterates stay in [a,b], shift identity
- `iterate_contraction`: |f^n(x) - f^n(y)| ≤ c^n |x-y| — exponential convergence
- `iterate_step_shrink`: |f^{n+1}(x) - f^n(x)| ≤ c^n |f(x)-x| — step decay
- `qpow_le_mono`: c^m ≤ c^n for n ≤ m when 0 ≤ c ≤ 1
- **`contraction_unique_fixed`**: fixed points are unique — f(p)=p ∧ f(q)=q → p=q
- **`iterate_diff_bound`**: (1-c)|f^m(x)-f^n(x)| ≤ |f(x)-x|(c^n - c^m) — a priori error
- **`iterate_is_cauchy`**: contraction iterates form a Cauchy sequence (via geometric bound)
- **`banach_fixed_point`**: Banach fixed point as CauchySeq limit of iterates
- `approximate_fixed_point`: |f(f^n(x)) - f^n(x)| < ε for large n
- **`fixed_point_independent`**: iterates from different starting points converge
- `contraction_limit_in_interval`: limit stays approximately in [a,b]
- `iterate_add`: f^{m+n}(x) = f^m(f^n(x)) — iterate composition
- **`contraction_compose`**: composition of contractions is a contraction (c₁·c₂ factor)
- **`iterate_is_contraction`**: k-th iterate is contraction with factor c^k (k≥1)
- `contraction_monotone_iterate`: monotone f with f(x)≥x gives non-decreasing iterates
- **`perturbed_iterate_bound`**: |f^n(x)-g^n(x)| ≤ δ·Σc^k — perturbation stability
- **0 axioms** — fully constructive

### Uniform Convergence — Limit Exchange, Dini's Theorem (`UniformConvergence.v`)

Uniform convergence of function sequences with limit exchange theorems:
- `pointwise_limit_const`, `uniform_limit_const`: constant sequence convergence
- `uniform_implies_pointwise`: uniform → pointwise convergence
- `uniform_limit_unique`: limit is unique (up to Qeq on the interval)
- **`uniform_limit_continuous_at`**: ε/3 trick — uniform limit of continuous functions is continuous at a point
- `uniform_limit_continuous_on`: continuity preservation on entire interval
- `uniform_cauchy_of_convergent`: uniform convergence → uniform Cauchy
- `uniform_cauchy_pointwise`: uniform Cauchy → pointwise Cauchy
- `riemann_sum_sub`, `riemann_sum_close`: Riemann sum approximation infrastructure
- **`integral_limit_exchange`**: ∫(lim fn) ≈ lim ∫(fn) — main integral-limit exchange
- `integral_uniform_cauchy`, `riemann_sum_uniform_bound`: integral Cauchy and bounds
- `udiff_close`, `bounded_deriv_diff_increment`: derivative closeness control
- **`derivative_limit_exchange`**: pointwise increment control from uniform derivative convergence
- `uniform_deriv_preserves_bound`: bounded derivatives preserved in limit
- `uniform_limit_add`: sum of uniform convergences
- `finite_max_N`: helper — extract uniform N from finitely many pointwise convergences
- **`dini_monotone`**: Dini's theorem — monotone pointwise convergence on finite grid → uniform convergence
- **0 axioms** — fully constructive

### Riemann Integration — Sums, FTC, Integral Comparison (`RiemannIntegration.v`)

Walk-point Riemann sums with Fundamental Theorem of Calculus:
- `riemann_sum`: left Riemann sum on uniform walk-point grid
- `tele_sum`: telescoping sum for FTC proof
- `riemann_sum_const`, `riemann_sum_add`, `riemann_sum_scale`: linearity of Riemann sums
- `riemann_sum_nonneg`, `riemann_sum_monotone`: ordering properties
- `riemann_sum_abs_bound`, `riemann_sum_global_bound`: integral bounds
- `telescope_collapse`: telescoping sum = f(end) - f(a) (Qeq)
- **`ftc_grid`**: Fundamental Theorem of Calculus — Riemann sum of f' approximates f(end) - f(a)
- `ftc_constant`, `ftc_affine`: exact FTC cases
- `ftc_nonneg_integral`: nonneg derivative implies nonneg integral
- `udiff_add`, `udiff_scale`: udiff closure under addition and scaling
- `ftc_linearity`, `ftc_comparison`: integral linearity and comparison
- **0 axioms** — fully constructive

### Integral Applications — Product Rule, IBP, Antiderivative Uniqueness (`IntegralApplications.v`)

Product rule for uniform differentiability and Integration by Parts:
- `product_decomp`: algebraic identity for product increments
- `product_tele_collapse`: telescoping product sums collapse to endpoint difference
- `triple_abs_bound`: triangle inequality for three terms
- `riemann_sum_ext`: extensionality for Riemann sums
- `increment_from_udiff`: udiff gives linear increment bound
- `increment_product_bound`, `product_error_bound`: error bounds for product terms
- `udiff_ext`: transfer udiff across extensionally equal functions
- **`udiff_product`**: product rule — `(fg)' = f'g + fg'` for uniform differentiability
- `udiff_square`: corollary — `(f²)' = 2ff'`
- **`ftc_product`**: FTC for products via udiff_product
- **`integration_by_parts`**: IBP — `∫f'g ≈ fg|_a^b - ∫fg'`
- `ibp_bound`, `ibp_self`: IBP corollaries
- `udiff_negate`, `udiff_sub`: closure under negation and subtraction
- `antiderivative_unique`: same derivative implies same increment (up to ε)
- `ibp_identity`: IBP with identity function `f(x)=x`
- **0 axioms** — fully constructive

### Taylor Series — Remainder Bounds, Convexity, Sandwich (`TaylorSeries.v`)

First-order Taylor expansion with constructive remainder bounds:
- `udiff_const`, `udiff_bmt`, `bmt_sq_udiff`: building blocks for Taylor remainder
- `taylor_remainder_udiff`: remainder function `f(x) - f(a) - f'(a)(x-a)` is udiff
- **`taylor1_ftc`**: first-order Taylor via FTC — remainder ≈ RS(f'-f'(a))
- **`taylor1_bound`**: `|f(b)-f(a)-f'(a)(b-a)| ≤ (C+ε)(b-a)` if `|f'-f'(a)| ≤ C`
- `taylor1_affine`, `taylor1_quadratic`: affine remainder = 0, quadratic remainder = (b-a)²
- `ibp_taylor1_decomp`: IBP-based Taylor decomposition via `∫f''·(b-t)`
- `taylor_nonneg_remainder`: nonnegative remainder from nonneg f''
- **`taylor1_var_bound`**: variable second-derivative bound via unified grid
- **`taylor_convexity`**: f'' ≥ 0 implies approximate convexity
- **`taylor_concavity`**: f'' ≤ 0 implies approximate concavity
- `taylor_local_min`: second derivative test for approximate local minimum
- **`taylor_sandwich`**: combined convexity + upper bound sandwich theorem
- `taylor_sandwich_const_deriv`: constant derivative implies exact affine approximation
- **0 axioms** — fully constructive

### Mean Value Theorem — Grid MVT, Monotonicity, Lipschitz (`MeanValueTheorem.v`)

Walk-point telescoping approach that bypasses Q incompleteness and setoid issues:
- `walk_point_qeq`, `walk_point_in_interval`: infrastructure for Leibniz-exact grid points
- `udiff_on`: uniform differentiability on intervals (single delta for all points)
- `bounded_deriv_bounded_increment`: **Main theorem** — bounded derivative implies bounded increment via grid telescoping
- `zero_deriv_near_constant`: zero derivative implies near-constant (corollary)
- `pos_deriv_increases` / `neg_deriv_decreases`: monotonicity from derivative sign
- `nonneg_deriv_approx_nondec`: approximate monotonicity for nonneg derivative
- `bounded_deriv_lipschitz_local`: local Lipschitz from derivative bound
- `walk_endpoint_qeq`: walk endpoint equals b (cancellation)
- `affine_udiff` / `quadratic_udiff`: concrete udiff examples
- `mvt_quadratic_midpoint`: algebraic MVT identity for quadratics
- **0 axioms** — fully constructive

### Differentiation — Division-Free Derivatives & Power Rule (`Differentiation.v`)

Division-free derivative formalization using `|f(x+h) - f(x) - L*h| < eps * |h|`:
- `deriv_const`, `deriv_id`, `deriv_affine`: basic derivative rules
- `deriv_scale`, `deriv_neg`, `deriv_sum`, `deriv_sub`: linearity of derivatives
- `deriv_product`: product rule `(fg)' = f'g + fg'` (hardest proof)
- `deriv_power_succ`: power rule by induction `d/dx(x^{n+1}) = (n+1)*x^n`
- `deriv_implies_continuous`: differentiable implies continuous
- `deriv_unique`: derivative is unique (Qeq)
- `quadratic_loss_derivative`: connects to GD — `d/dw (w-w*)^2 = 2(w-w*)`
- **`local_min_zero_deriv`**: Fermat's theorem — local min implies zero derivative
- **0 axioms** -- fully constructive

### Gradient Descent Convergence (`GradientDescent.v`)

Formal proof that gradient descent on quadratic loss converges geometrically:
- `gd_error_pow`: error at step n equals contraction^n times initial error
- `gd_error_cauchy`: error sequence is Cauchy (weight convergence)
- `gd_weight_converges`: weights converge to optimum w*
- `gd_loss_decreasing`: loss is monotonically decreasing
- **`gd_loss_converges_zero`**: Crown jewel -- quadratic loss converges to 0
- `gd_convergence_rate`: |w_n - w*| <= |1-2eta|^n * |w_0 - w*|
- `optimal_lr_one_step`: eta = 1/2 gives exact convergence in one step
- `gd_cumulative_error`: cumulative error bounded by |e_0|/(1-|c|)
- **0 axioms** -- fully constructive (no classic needed)

### Power Series & Exponential Convergence (`PowerSeries.v`)

Ratio test and convergence of power series and exp(x):
- `geometric_domination`: |a(S n)| ≤ r·|a(n)| eventually → |a(N+k)| ≤ |a(N)|·r^k
- `ratio_test_abs`: division-free ratio test — eventual ratio bound implies Cauchy
- `power_series_converges`: coefficient ratio bound → Σ(a_n·x^n) converges
- `exp_term_ratio`: (n+1)·x^{n+1}/fact(n+1) = x·x^n/fact(n) (via `field`)
- `exp_ratio_bound`: ∀ 0<r<1, ∃N, ∀n≥N, |x^{n+1}/fact(n+1)| ≤ r·|x^n/fact(n)|
- **`exp_series_cauchy`**: Crown jewel — ∀x∈Q, Σ x^n/n! is Cauchy
- `exp_series_zero`: exp(0) ~ const 1
- Axiom: `classic` (inherited from MCT)

### Series Convergence (`SeriesConvergence.v`)

Convergence of series over Q via monotone convergence:
- `bernoulli_ineq`: (1+x)^n >= 1 + n*x for x >= 0 (induction on n)
- `Qpow_vanish` / `Qpow_limit_zero`: r^n → 0 for 0 <= r < 1 (via Bernoulli)
- `Qpow_cauchy`: r^n is Cauchy for 0 <= r < 1 (MCT: decreasing + bounded)
- `geometric_sum_identity`: (1-r)*S_n = 1 - r^{n+1} (division-free)
- `geometric_series_cauchy`: geometric series converges for |r| < 1
- `comparison_test`: 0 <= a(n) <= b(n) and Σb converges → Σa converges
- `absolute_convergence`: Σ|a(n)| converges → Σa(n) is Cauchy (triangle inequality on tails)
- `series_nonneg_upper_bound`: nonneg series partial sums bounded by limit
- Axiom: `classic` (inherited from MCT)

### Monotone Convergence Theorem (`MonotoneConvergence.v`)

Classical proof that bounded monotone Q-sequences are Cauchy:
- `q_inc_bounded_cauchy`: increasing + bounded above → is_cauchy (by contradiction via NNPP)
- `q_dec_bounded_cauchy`: decreasing + bounded below → is_cauchy (dual)
- `mct_limit_inc` / `mct_limit_dec`: construct CauchySeq from monotone bounded sequence
- `mct_inc_upper_bound`: limit is upper bound for all terms
- `mct_inc_least`: limit is least upper bound (cauchy_le)
- `cauchy_le_trans` / `cauchy_le_antisym`: ordering on CauchySeqs
- `squeeze_equiv` / `squeeze_cauchy_le`: squeeze theorem variants
- `seq_increasing_le`: transitive ordering for sequences of CauchySeqs
- Axiom: `classic` (LEM) — required; MCT is equivalent to LPO over Q

### Metric Completeness (`Completeness.v`)

Three equivalent formulations of completeness for Cauchy reals:
- `nested_interval_limit`: nested rational intervals have a CauchySeq limit
- `sup_bisect_cauchy`: bounded sets have supremum via bisection
- `diagonal_limit` / `diagonal_converges`: Cauchy-sequences-of-CauchySeqs converge (diagonal extraction)
- `meta_cauchy`: uniform Cauchy condition for sequences of CauchySeqs
- 0 axioms — fully constructive

### Ordered Field on Cauchy Reals (`RealField.v`)

Field structure and ordering for CauchySeq:
- `cauchy_mul`: multiplication with Cauchy proof
- `cauchy_bounded`: every CauchySeq is bounded
- `cauchy_inv_pos`: multiplicative inverse for positive sequences
- Field laws: commutativity, associativity, distributivity
- 0 axioms — fully constructive

### CROWN Linear Relaxation Soundness (`PInterval_CROWN.v`)

Formal soundness proof for the CROWN neural network verification method:
- `relu_lower_bound_sound`: optimal lower bound for ReLU relaxation
- `relu_upper_bound_sound`: triangle upper bound for ReLU
- `crown_backward_sound`: backward-propagated bounds contain true output
- `crown_tighter_ibp`: CROWN bounds are always tighter than IBP

### Probability Theory + Bayesian Fallacies (`Probability.v`)

Constructive probability over ℚ with Bayes' theorem and fallacy detection:
- `bayes_rule`: P(H|E) = P(E|H) * P(H) / P(E)
- `base_rate_fallacy_detected`: P(H|E) = P(E|H) iff P(H) = P(E)
- `conjunction_fallacy_detected`: P(A∧B) ≤ P(A) always
- `gamblers_fallacy_detected`: independence preserved across trials
- `bayes_asymmetry`: contrapositive of base rate fallacy

### Cauchy Reals (`CauchyReal.v`)

Constructive completion of ℚ via Cauchy sequences:
- Equivalence relation (refl, sym, trans) with congruence for arithmetic
- Addition, negation, subtraction, constant sequences
- Ordering, positivity, Archimedean property
- Completeness: rational approximation, self-convergence, subsequence extraction
- Algebraic laws: commutativity, associativity, identity, inverse

### Rounding Safety (`RoundingSafety.v`)

IEEE 754 floating-point rounding within interval bounds:
- `rounding_safe`: x ∈ [lo,hi] → round(x) ∈ [lo-ε, hi+ε]
- `ibp_rounding_step`: margin accumulates additively per layer
- `crown_affine_rounding`: CROWN bounds survive rounding (positive/negative slope)
- `double_rounding_error`: |round(round(x)) - x| ≤ 2ε
- `ibp_two_steps`: composition of two rounding steps

### Softmax Probability Soundness (`SoftmaxProbability.v`)

Division-free bridge from interval bounds to probability statements:
- `softmax_probability_sound`: lo_i·Σv ≤ v_i·Σhi ∧ v_i·Σlo ≤ hi_i·Σv
- `cross_mul_lower` / `cross_mul_upper`: two-step monotonicity via cross-multiplication
- `probability_bounds_consistent`: interval [lo/Σhi, hi/Σlo] is non-degenerate
- Key technique: avoid division by cross-multiplying with positive denominators

### Constructive Measure & Integration (`Measure.v`)

Riemann-style integration over ℚ using step functions:
- `integral_step_add`: linearity (integral of sum = sum of integrals)
- `integral_step_mono`: monotonicity (f ≤ g ⟹ ∫f ≤ ∫g)
- `integral_bounds`: value bounds propagate (lo·width ≤ ∫ ≤ hi·width)
- `integral_step_abs_bound`: triangle inequality (|∫f| ≤ M·width)
- `lower_upper_bound`: lower/upper Riemann sums bracket the integral
- `measure_additive`: μ([a,c]) = μ([a,b]) + μ([b,c])

### IVT on Cauchy Reals (`IVT_CauchyReal.v`)

Full Intermediate Value Theorem lifted to Cauchy real numbers:
- `ivt_cauchy_real`: ∃ c : CauchySeq, ∀ n, a ≤ c(n) ≤ b ∧ f(c(n)) → 0
- `ivt_cauchy_real_equiv`: f ∘ root is Cauchy-equivalent to `cauchy_const 0`
- `continuous_compose_cauchy`: uniform continuity preserves Cauchy property
- Bridge lemmas: `is_Cauchy ↔ is_cauchy` between IVT_ERR and CauchyReal definitions

---

## Installation & Verification

### Prerequisites

- Rocq 9.0.1 (or Coq 8.18+)
- Standard Library (included)

### Build Instructions

```bash
git clone https://github.com/horsocrates/theory-of-systems-coq.git
cd theory-of-systems-coq

# Generate Makefile and compile all files
coq_makefile -f _CoqProject -o Makefile
make
```

### Verify Main Theorem

```bash
cd src
coqc -Q . ToS ShrinkingIntervals_ERR.v
coqtop -Q . ToS -l ShrinkingIntervals_ERR.v -batch \
  -exec "Print Assumptions unit_interval_uncountable_trisect."
```

**Expected output:**
```
Axioms:
classic : forall P : Prop, P \/ ~P
```

### Run AI Fallacy Detector Demo

```bash
# Python (no dependencies)
cd Architecture_of_Reasoning
python3 demo.py

# Or with custom input
python3 demo.py "You're wrong because you're stupid."
```

---

## Philosophical Position

**Logical Realism:** Logic is the structure of being, not a tool of thought.

**Process Philosophy (P4):** Infinity is a property of process, not of object. Numbers are limits of convergent sequences, not completed infinite sets.

**L5 (Law of Order):** When multiple positions share the same Role, select the minimal index. This principle resolved key formalization challenges (EVT breakthrough).

**E/R/R Framework:** Every determinate system exhibits Elements (what exists), Roles (why significant), and Rules (how structured).

---

## Architecture of Reasoning

The `Architecture_of_Reasoning/` folder contains formal verification of fallacy detection and paradox dissolution:

### Complete Taxonomy: 156 Fallacies

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
- **Chain-of-Thought Validation** — D1→D6 domain sequence checking
- **Self-Reflection Loop** — Automatic fix prompts
- **Safety Layer** — Block ad hominem, confirmation bias
- **Propaganda Detection** — Identify manipulation patterns
- **OCaml Extraction** — Production-ready code from Coq proofs

See [Architecture_of_Reasoning/README.md](Architecture_of_Reasoning/README.md) for full documentation.

---

## OCaml Extraction

### Core ToS (`extraction/`)

| Module | Contents |
|--------|----------|
| `TheoryOfSystems_Core_ERR.ml` | `Level`, `System`, `Criterion`, `Generator`, `unfold_gen`, `L5_resolve` |
| `Roles.ml` | `ERR_Category`, `MathStatus`, `EpistemicStatus`, `Dependency`, `role_candidates` |
| `ProcessGeneral.ml` | `GenProcess`, `prefix`, `process_map`, `Qdist` |
| `IntensionalIdentity.ml` | `CriterionOver` |
| `diagonal_demo.ml` | Standalone Calkin-Wilf + diagonal demo |

### ToS-Lang Verified Compiler (`tos_lang/`)

| Module | Status | Contents |
|--------|--------|----------|
| `TypeChecker.ml` | **VERIFIED** | `typecheck`, `typecheck_ann`, `erase_ann` — proven sound |
| `Evaluator.ml` | **VERIFIED** | `safe_eval`, `classify_eval`, `safe_eval_ann` — proven safe |
| `Expressions.ml` | **VERIFIED** | `shift`, `subst`, `is_value_dec`, `expr_eq_dec` |
| `Reduction.ml` | **VERIFIED** | `try_step`, `eval_fuel` — proven type-preserving |
| `parser.ml` | Unverified | Recursive descent parser for ToS-Lang syntax |
| `printer.ml` | Unverified | Pretty printer for `Expr`, `Ty`, `EvalResult` |
| `main.ml` | Unverified | CLI: `tos_check <file.tos> [--fuel N]` |
| `ai_interface.py` | Unverified | Python AI generation + verification loop |

All Prop fields are erased during extraction. The extracted code is directly usable from OCaml programs.

---

## Publications

### Foundational

- **[The Laws of Logic as Conditions of Existence](https://philpapers.org/archive/HORTLO-18.pdf)** — Derivation of L1–L5 from first principle
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

@article{horsocrates2026nested,
  author = {Horsocrates},
  title = {Nested Rational Intervals for Non-Surjectivity of
           $\mathbb{N} \to [0,1] \cap \mathbb{Q}$:
           A Coq Formalization with Minimal Axioms},
  year = {2026},
  note = {arXiv preprint}
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

---
