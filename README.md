# Theory of Systems — Coq Formalization

[![Rocq](https://img.shields.io/badge/Rocq-9.0.1-blue.svg)](https://coq.inria.fr/)
[![Status](https://img.shields.io/badge/Status-98%25_Complete-green.svg)]()
[![Theorems](https://img.shields.io/badge/Theorems-711_Proven-brightgreen.svg)]()
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
| **156 Fallacies Formalized** | Complete taxonomy |
| **46 Paradoxes Classified** | All dissolved |

**Total: 711 proven theorems (594 core + 117 reasoning architecture)**

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
├── src/                               # Coq source files
│   ├── ShrinkingIntervals_ERR.v       # Main theorem: non-surjectivity (167 lemmas)
│   ├── Countability_Q.v              # ℚ ≅ ℕ via Calkin-Wilf (17 lemmas, 0 Admitted)
│   ├── EVT_idx.v                     # ε-EVT, L5-compliant (26 lemmas)
│   ├── IVT_ERR.v                     # ε-IVT (23 lemmas)
│   ├── Archimedean_ERR.v             # Archimedean property (14 lemmas)
│   ├── PInterval_CROWN.v            # CROWN linear relaxation soundness (25 lemmas)
│   ├── Probability.v                 # Probability + Bayesian fallacies (12 lemmas)
│   ├── CauchyReal.v                  # Cauchy reals: completion of ℚ (19 lemmas)
│   ├── RoundingSafety.v              # IEEE 754 rounding within intervals (13 lemmas)
│   ├── IVT_CauchyReal.v             # Full IVT on Cauchy reals (8 lemmas)
│   ├── Measure.v                    # Constructive measure & integration (15 lemmas)
│   ├── SoftmaxProbability.v         # IBP → probability soundness (14 lemmas)
│   ├── RealField.v                  # Ordered field on Cauchy reals (15 lemmas)
│   ├── Completeness.v               # Metric completeness: NIP, sup, diagonal (23 lemmas)
│   ├── MonotoneConvergence.v        # Monotone Convergence Theorem (15 lemmas)
│   ├── TheoryOfSystems_Core_ERR.v    # Laws L1-L5, paradox blocking
│   ├── HeineBorel_ERR.v              # Compactness (partial — needs ℝ)
│   ├── SchroederBernstein_ERR.v      # Injection theorem (14 lemmas)
│   ├── TernaryRepresentation_ERR.v   # Digit representation
│   ├── DiagonalArgument_ERR.v        # Alternative diagonal proof
│   └── EVT_ERR.v                     # EVT (deprecated, replaced by EVT_idx.v)
│
├── Architecture_of_Reasoning/         # Fallacy & Paradox formalization
│   ├── README.md                      # Detailed documentation
│   ├── CompleteFallacyTaxonomy.v      # All 156 fallacies
│   ├── AI_FallacyDetector.v           # LLM verification module
│   ├── ParadoxDissolution.v           # 46 paradoxes classified
│   ├── Architecture_of_Reasoning.v    # Unified L1-L5, D1-D6, E/R/R
│   ├── ERR_Fallacies.v                # E/R/R Framework
│   ├── DomainViolations_Complete.v    # Type 2: 105 fallacies
│   ├── ai_fallacy_detector.ml         # OCaml extraction
│   └── demo.py                        # Python demo
│
├── extraction/                        # Executable code
│   └── diagonal_demo.ml              # OCaml demo
│
├── _CoqProject                        # Build configuration
├── Makefile                           # Generated via coq_makefile
├── .github/workflows/coq-ci.yml      # CI (coqorg/coq:8.19)
└── README.md
```

---

## Statistics

### Core Formalization

| File | Qed | Admitted | Status |
|------|-----|----------|--------|
| `ShrinkingIntervals_ERR.v` | 167 | 0 | **100%** |
| `EVT_idx.v` | 26 | 0 | **100%** |
| `PInterval_CROWN.v` | 25 | 0 | **100%** |
| `IVT_ERR.v` | 23 | 0 | **100%** |
| `CauchyReal.v` | 19 | 0 | **100%** |
| `Countability_Q.v` | 17 | 0 | **100%** |
| `Archimedean_ERR.v` | 14 | 0 | **100%** |
| `SchroederBernstein_ERR.v` | 14 | 0 | **100%** |
| `RoundingSafety.v` | 13 | 0 | **100%** |
| `Probability.v` | 12 | 0 | **100%** |
| `IVT_CauchyReal.v` | 8 | 0 | **100%** |
| `Measure.v` | 15 | 0 | **100%** |
| `SoftmaxProbability.v` | 14 | 0 | **100%** |
| `RealField.v` | 15 | 0 | **100%** |
| `Completeness.v` | 23 | 0 | **100%** |
| `MonotoneConvergence.v` | 15 | 0 | **100%** |
| `TernaryRepresentation_ERR.v` | 52 | 3 | 95% |
| `DiagonalArgument_ERR.v` | 41 | 1 | 98% |
| `TheoryOfSystems_Core_ERR.v` | 31 | 3 | 91% |
| `EVT_ERR.v` | 28 | 4 | *(deprecated)* |
| `HeineBorel_ERR.v` | 22 | 2 | *(unprovable over ℚ)* |
| **Core TOTAL** | **594** | **13** | **98%** |

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
| Core Mathematics | 594 | 13 |
| Architecture of Reasoning | 117 | 0 |
| **TOTAL** | **711** | **13** |

**Remaining Admitted (documented):**

| File | Count | Reason |
|------|-------|--------|
| `EVT_ERR.v` | 4 | Deprecated — replaced by `EVT_idx.v` (0 Admitted) |
| `TernaryRepresentation_ERR.v` | 3 | `Qfloor` discontinuity; needs ~15 auxiliary lemmas |
| `TheoryOfSystems_Core_ERR.v` | 3 | Universe polymorphism limitations (intentional) |
| `HeineBorel_ERR.v` | 2 | Unprovable over ℚ (requires real-valued continuity) |
| `DiagonalArgument_ERR.v` | 1 | Alternative approach; use `ShrinkingIntervals` instead |

---

## New in March 2026

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
- **OCaml Extraction** — Production-ready code

See [Architecture_of_Reasoning/README.md](Architecture_of_Reasoning/README.md) for full documentation.

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
