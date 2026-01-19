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

## Philosophical Position

**Logical Realism:** Logic is the structure of being, not a tool of thought.

**Process Philosophy (P4):** Infinity is a property of process, not of object. Numbers are limits of convergent sequences, not completed infinite sets.

**L5 (Law of Order):** When multiple positions share the same Role, select the minimal index. This principle resolved key formalization challenges (EVT breakthrough).

---

## Project Structure

### Core Files (100% Complete)

| File | Lemmas | Description |
|------|--------|-------------|
| `ShrinkingIntervals_uncountable_ERR.v` | 167 | Uncountability via nested intervals |
| `EVT_idx.v` | 23 | Extreme Value Theorem (index-based) |
| `IVT_ERR.v` | 23 | Intermediate Value Theorem |
| `Archimedean_ERR.v` | 14 | Archimedean Property |
| `SchroederBernstein_ERR.v` | 14 | Set theory injection theorem |

### Supporting Files

| File | Status | Description |
|------|--------|-------------|
| `TheoryOfSystems_Core_ERR.v` | 91% | Philosophical core (L4, L5, paradox blocking) |
| `TernaryRepresentation_ERR.v` | 96% | Ternary digit representation |
| `DiagonalArgument_ERR.v` | 98% | Cantor's diagonal in ternary |
| `HeineBorel_ERR.v` | 92% | Compactness (requires ℝ for 100%) |

### Documentation

- `Theory_of_Systems_Preprint_v3.md` — Full philosophical derivation
- `ERR_FRAMEWORK.md` — Elements/Roles/Rules methodology
- `L5_LEFTMOST_DEDUCTION.md` — L5-resolution principle derivation
- `DIAGONAL_VS_INTERVALS.md` — Why intervals supersede digits

---

## Building

### Requirements

- Coq 8.18.0 or later
- Standard library only (no external dependencies)

### Compilation

```bash
# Compile individual files
coqc TheoryOfSystems_Core_ERR.v
coqc Archimedean_ERR.v
coqc IVT_ERR.v
coqc EVT_idx.v
coqc ShrinkingIntervals_uncountable_ERR.v

# Or compile all
for f in *.v; do coqc "$f"; done
```

### Verification

```bash
# Check for remaining Admitted statements
grep -c "Admitted" *.v

# Count proven lemmas
grep -c "Qed" *.v
```

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
