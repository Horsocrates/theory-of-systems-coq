# Theory of Systems — Coq Formalization

[![Coq](https://img.shields.io/badge/Coq-8.18.0-blue.svg)](https://coq.inria.fr/)
[![Status](https://img.shields.io/badge/Status-98%25_Complete-green.svg)]()
[![Lemmas](https://img.shields.io/badge/Lemmas-385_Proven-brightgreen.svg)]()
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

- **385 proven lemmas** with only 8 remaining Admitted
- **Single external axiom:** `classic` (Law of Excluded Middle, L3)
- **No Axiom of Infinity** — this is a consequence of P4 (Process Philosophy), not a design goal
- Complete proofs of: IVT, EVT, Archimedean Property, Schröder-Bernstein, Uncountability of [0,1]

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

### Verification of the Main Result

The core proof of uncountability resides in `ShrinkingIntervals_uncountable_ERR.v`. To verify its status and dependencies:

```bash
# Check theorem compiles and inspect axioms
coqc ShrinkingIntervals_uncountable_ERR.v
coqtop -l ShrinkingIntervals_uncountable_ERR.v -batch -exec "Print Assumptions unit_interval_uncountable_trisect."
```

**Expected output:**
```
Axioms:
classic : forall P : Prop, P \/ ~P
```

> **Note:** This theorem tree contains **0 Admitted** and only the foundational `classic` axiom (L3: Law of Excluded Middle). No Axiom of Choice. No Axiom of Infinity.

### Quick Verification Commands

```bash
# Count proven vs admitted lemmas
echo "Proven (Qed):"; grep -c "Qed\." *.v | awk -F: '{sum+=$2} END {print sum}'
echo "Admitted:"; grep -c "Admitted\." *.v | awk -F: '{sum+=$2} END {print sum}'

# Verify no unexpected axioms in main theorem
grep -A5 "Print Assumptions" ShrinkingIntervals_uncountable_ERR.v
```

---

## Project Structure

```
theory-of-systems-coq/
│
├── Core/                              # Foundational E/R/R framework
│   └── TheoryOfSystems_Core_ERR.v       # Laws L1-L5, paradox blocking, FunctionalSystem
│
├── Analysis/                          # Classical analysis theorems  
│   ├── Archimedean_ERR.v                # Archimedean property of ℚ
│   ├── IVT_ERR.v                        # Intermediate Value Theorem
│   ├── EVT_idx.v                        # Extreme Value Theorem (L5-compliant)
│   └── HeineBorel_ERR.v                 # Compactness (partial — needs ℝ)
│
├── Theorems/                          # Main uncountability proofs
│   ├── ShrinkingIntervals_uncountable_ERR.v  # ★ Primary proof via trisection
│   ├── DiagonalArgument_ERR.v           # Alternative: Cantor diagonal
│   ├── TernaryRepresentation_ERR.v      # Digit representation support
│   └── SchroederBernstein_ERR.v         # Set-theoretic injection theorem
│
└── docs/                              # Documentation
    ├── Theory_of_Systems_Preprint_v4.md   # Full philosophical paper
    ├── ERR_FRAMEWORK.md                 # E/R/R methodology explained
    ├── L5_LEFTMOST_DEDUCTION.md         # L5-resolution derivation
    └── DIAGONAL_VS_INTERVALS.md         # Why intervals > digits
```

### File Status Overview

| File | Qed | Admitted | Completion |
|------|-----|----------|------------|
| `ShrinkingIntervals_uncountable_ERR.v` | 167 | 0 | ✅ **100%** |
| `EVT_idx.v` | 23 | 0 | ✅ **100%** |
| `IVT_ERR.v` | 23 | 0 | ✅ **100%** |
| `Archimedean_ERR.v` | 14 | 0 | ✅ **100%** |
| `SchroederBernstein_ERR.v` | 14 | 0 | ✅ **100%** |
| `TernaryRepresentation_ERR.v` | 52 | 2 | 96% |
| `DiagonalArgument_ERR.v` | 41 | 1 | 98% |
| `HeineBorel_ERR.v` | 22 | 2 | 92% |
| `TheoryOfSystems_Core_ERR.v` | 29 | 3 | 91% |
| **TOTAL** | **385** | **8** | **98%** |

---

## Philosophical Position

**Logical Realism:** Logic is the structure of being, not a tool of thought.

**Process Philosophy (P4):** Infinity is a property of process, not of object. Numbers are limits of convergent sequences, not completed infinite sets.

**L5 (Law of Order):** When multiple positions share the same Role, select the minimal index. This principle resolved key formalization challenges (EVT breakthrough).

---

## Key Insights

### The EVT Breakthrough

The Extreme Value Theorem proof was blocked by Qeq vs Leibniz equality issues. The solution came from L5:

> "Don't seek *value*, seek *position*."

By returning the **index** of the maximum rather than the value itself, the proof becomes trivial:

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

### Digit Stability Problem

Qfloor and mod 3 are discontinuous L3 operations on continuous L2 objects. The interval-based approach (`ShrinkingIntervals_uncountable_ERR.v`) avoids this entirely, proving uncountability through geometric trisection with guaranteed gaps.

---

## Remaining Work

### Categorization of 8 Admitted

**Philosophically Impossible over ℚ (2):**
- Nested intervals can converge to irrational limits
- Uniform continuity requires completeness

**Universe-Level in Coq (3):**
- Type-theoretic issues beyond mathematics proper

**Digit Stability (3):**
- Bypassed by interval approach

> **Important:** The main uncountability theorem (`unit_interval_uncountable_trisect`) has **0 Admitted** dependencies.

---

## Citation

If you use this work, please cite:

```bibtex
@software{theory_of_systems_coq,
  author = {Horsocrates},
  title = {Theory of Systems — Coq Formalization},
  year = {2026},
  url = {https://github.com/horsocrates/theory-of-systems-coq}
}
```

---

## License

MIT License — see [LICENSE](LICENSE) for details.

---

## Acknowledgments

- The Coq development team
- Anthropic's Claude for proof assistance
- Google's Gemini for the L5 insight: "Don't seek value, seek position"
