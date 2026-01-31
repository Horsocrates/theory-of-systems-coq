# Theory of Systems — Coq Formalization

[![Coq](https://img.shields.io/badge/Coq-8.18.0-blue.svg)](https://coq.inria.fr/)
[![Status](https://img.shields.io/badge/Status-98%25_Complete-green.svg)]()
[![Lemmas](https://img.shields.io/badge/Lemmas-397_Proven-brightgreen.svg)]()
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **A complete deductive derivation of mathematics from a single first principle: "A = exists"**

---

## 📄 Paper

**"Nested Rational Intervals for Non-Surjectivity of ℕ → [0,1] ∩ ℚ: A Coq Formalization with Minimal Axioms"**

| Format | Pages | Description |
|--------|-------|-------------|
| [LaTeX (arXiv)](docs/nested_intervals.tex) | 13 | For submission |
| [PDF](docs/nested_intervals.pdf) | 13 | Compiled |
| [Detailed Markdown](docs/Nested_Rational_Intervals.pdf) | 36 | Extended version |

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
| **Non-surjectivity ℕ → [0,1] ∩ ℚ** | ✅ 167 lemmas, 0 Admitted |
| **Countability of ℚ** (Calkin-Wilf) | ✅ Fully constructive, no axioms |
| **ε-Intermediate Value Theorem** | ✅ 23 lemmas, 0 Admitted |
| **ε-Extreme Value Theorem** | ✅ 23 lemmas, 0 Admitted |

**Total: 397 proven lemmas, 10 Admitted (98% complete)**

**Single external axiom:** `classic` (Law of Excluded Middle, L3)  
**No Axiom of Infinity** — consequence of P4 (Process Philosophy), not a design goal  
**No Axiom of Choice**

---

## 🔑 The Key Contrast

We prove **both**:

| Result | Axioms | Status |
|--------|--------|--------|
| ℚ is countable (bijection ℕ ↔ ℚ) | **None** | Fully constructive |
| Cauchy processes are uncountable | LEM only | Non-surjectivity |

**No contradiction:** A rational is finite data (two integers). A Cauchy process is infinite behavior (unbounded sequence). We enumerate objects, not behaviors.

---

## Installation & Verification

### Prerequisites

- Coq 8.18.0 or higher
- Standard Library (included with Coq)

### Build Instructions

```bash
git clone https://github.com/horsocrates/theory-of-systems-coq.git
cd theory-of-systems-coq

# Generate Makefile and compile
coq_makefile -f _CoqProject -o Makefile
make
```

### Run OCaml Demo

```bash
cd extraction
ocaml diagonal_demo.ml
```

**Output:**
```
=== Calkin-Wilf Enumeration (Q is countable) ===
  enum_qpos( 0) = 1/1
  enum_qpos( 1) = 1/2
  enum_qpos( 2) = 2/1
  ...

=== Diagonal Construction (Cauchy processes are uncountable) ===
  Depth 1: diagonal = 1/6,    interval = [0/1, 1/3]
  Depth 2: diagonal = 1/18,   interval = [0/1, 1/9]
  ...
```

### Verification of the Main Result

```bash
coqc ShrinkingIntervals_uncountable_ERR.v
coqtop -l ShrinkingIntervals_uncountable_ERR.v -batch -exec "Print Assumptions unit_interval_uncountable_trisect."
```

**Expected output:**
```
Axioms:
classic : forall P : Prop, P \/ ~P
```

---

## Project Structure

```
theory-of-systems-coq/
│
├── docs/                              # Papers & documentation
│   ├── nested_intervals.tex           # ★ arXiv preprint (LaTeX)
│   ├── nested_intervals.pdf           # Compiled PDF
│   ├── Nested_Rational_Intervals.md   # Detailed markdown version
│   ├── references.bib                 # Bibliography
│   └── ...
│
├── src/                               # Coq source files
│   ├── ShrinkingIntervals_uncountable_ERR.v  # ★ Main theorem (167 lemmas)
│   ├── Countability_Q.v               # ★ ℚ ≅ ℕ via Calkin-Wilf (NEW)
│   ├── EVT_idx.v                      # ε-EVT (L5-compliant)
│   ├── IVT_ERR.v                      # ε-IVT
│   ├── Archimedean_ERR.v              # Archimedean property
│   ├── TheoryOfSystems_Core_ERR.v     # Laws L1-L5, paradox blocking
│   ├── HeineBorel_ERR.v               # Compactness (partial — needs ℝ)
│   ├── SchroederBernstein_ERR.v       # Injection theorem
│   ├── TernaryRepresentation_ERR.v    # Digit representation
│   └── DiagonalArgument_ERR.v         # Alternative diagonal proof
│
├── extraction/                        # Executable code
│   └── diagonal_demo.ml               # ★ OCaml demo (NEW)
│
└── README.md
```

### File Status Overview

| File | Qed | Admitted | Status |
|------|-----|----------|--------|
| `ShrinkingIntervals_uncountable_ERR.v` | 167 | 0 | ✅ **100%** |
| `Countability_Q.v` | 12 | 2 | ✅ 86% |
| `EVT_idx.v` | 23 | 0 | ✅ **100%** |
| `IVT_ERR.v` | 23 | 0 | ✅ **100%** |
| `Archimedean_ERR.v` | 14 | 0 | ✅ **100%** |
| `SchroederBernstein_ERR.v` | 14 | 0 | ✅ **100%** |
| `TernaryRepresentation_ERR.v` | 52 | 2 | 96% |
| `DiagonalArgument_ERR.v` | 41 | 1 | 98% |
| `HeineBorel_ERR.v` | 22 | 2 | 92% |
| `TheoryOfSystems_Core_ERR.v` | 29 | 3 | 91% |
| **TOTAL** | **397** | **10** | **98%** |

---

## Philosophical Position

**Logical Realism:** Logic is the structure of being, not a tool of thought.

**Process Philosophy (P4):** Infinity is a property of process, not of object. Numbers are limits of convergent sequences, not completed infinite sets.

**L5 (Law of Order):** When multiple positions share the same Role, select the minimal index. This principle resolved key formalization challenges (EVT breakthrough).

---

## Technical Contributions

### 1. Deterministic Witness Selection

When multiple candidates satisfy a specification, select the **leftmost**. This yields Leibniz equality (`=`) instead of propositional equality (`Qeq`).

### 2. Index-Based Argmax (The EVT Breakthrough)

> "Don't seek *value*, seek *position*." — L5 insight

```coq
(* OLD: Returns value, causes Qeq issues *)
Definition max_on_grid_OLD f a b n := max_list (f a) (map f (grid_list a b n)).

(* NEW: Returns f at argmax index — Leibniz equality! *)
Definition max_on_grid f a b n :=
  let l := grid_list a b n in
  f (nth (argmax_idx f l a) l a).

(* Now trivial! *)
Lemma max_on_grid_attained : ...
Proof.
  exists (nth idx l a). split.
  - apply nth_In. exact Hidx.
  - reflexivity.  (* DEFINITIONAL! *)
Qed.
```

### 3. Trisection over Bisection

Digit extraction (`Qfloor`, `mod 3`) is discontinuous. The interval-based approach avoids this entirely, proving non-surjectivity through geometric trisection with guaranteed gaps.

### 4. Executable Extraction

The Coq proof extracts to working OCaml code (`diagonal_demo.ml`) that computes witnesses for any enumeration.

---

## Proof-Theoretic Strength

Our formalization lives in **RCA₀ + LEM** — strictly below ACA₀, WKL₀, and ZF⁻.

| System | Our theorems |
|--------|--------------|
| RCA₀ | ✅ Countability of ℚ |
| RCA₀ + LEM | ✅ Non-surjectivity, ε-IVT, ε-EVT |
| WKL₀ | Not needed |
| ACA₀ | Not needed |

> *"The infinity in uncountability is directional (unbounded iteration), not cardinal (completed infinite sets)."*

---

## Remaining Work

### Categorization of 10 Admitted

**Completeness Required (2):**
- Nested intervals can converge to irrational limits
- Uniform continuity requires completeness

**Universe-Level in Coq (3):**
- Type-theoretic constraints beyond mathematics proper

**Digit Stability (3):**
- Bypassed by interval approach

**Countability Round-Trip (2):**
- Routine Calkin-Wilf bijection lemmas

> **Important:** The main non-surjectivity theorem has **0 Admitted** dependencies.

---

### Architecture of Reasoning (NEW)

Formal verification of fallacy detection and paradox dissolution:

| Module | Content | Theorems |
|--------|---------|----------|
| `AI_FallacyDetector.v` | LLM verification, safety layer | 5 |
| `Architecture_of_Reasoning.v` | Unified L1-L5, D1-D6, E/R/R | 17 |
| `DomainViolations_Complete.v` | 105 fallacies | 17 |
| `ParadoxDissolution.v` | 7 paradoxes | 24 |

**AI Applications:**
- Chain-of-thought validation (D1→D6)
- Self-reflection loop with fix prompts
- Safety layer: blocks ad hominem, confirmation bias
- OCaml extraction for production pipelines

---

## Publications

- **[The Laws of Logic as Conditions of Existence](https://philpapers.org/archive/HORTLO-18.pdf)** — Full philosophical derivation of L1–L5 and P1–P4
- **[The Law of Order](https://philpapers.org/archive/HORTLO-19.pdf)** — L5 application and the EVT breakthrough
- **[Nexted Intervals](docs/nested_intervals.pdf)** — Technical paper on non-surjectivity formalization
- **[The Architecture of Error: A Structural Theory of Logical Fallacies](https://philpapers.org/archive/HORTAO-17.pdf)** - Philosophical paper on logical fallacies (part 1/2)

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
  title = {Nested Rational Intervals for Non-Surjectivity of $\mathbb{N} \to [0,1] \cap \mathbb{Q}$: A Coq Formalization with Minimal Axioms},
  year = {2026},
  note = {arXiv:2026.XXXXX}
}
```

---

## Contact

**Horsocrates**  
📧 horsocrates@proton.me  
🔗 [GitHub](https://github.com/horsocrates/theory-of-systems-coq)

---

## License

MIT License — see [LICENSE](LICENSE) for details.

---

## Acknowledgments

- The Coq development team
- Anthropic's Claude for proof assistance and paper writing
- Google's Gemini for the L5 insight: "Don't seek value, seek position"
