# Architecture of Reasoning — Coq Formalization

[![Coq](https://img.shields.io/badge/Coq-8.18.0-blue.svg)](https://coq.inria.fr/)
[![Status](https://img.shields.io/badge/Status-100%25_Complete-brightgreen.svg)]()
[![Admitted](https://img.shields.io/badge/Admitted-0-brightgreen.svg)]()
[![Theorems](https://img.shields.io/badge/Theorems-50+-brightgreen.svg)]()

> **Complete formal verification of the Architecture of Reasoning: Fallacies, Paradoxes, and the E/R/R Framework**

---

## Overview

This package provides **machine-verified formalization** of the Architecture of Reasoning — a unified framework for understanding errors in reasoning. It accompanies the article series:

1. **The Laws of Logic as Conditions of Existence**
2. **The Law of Order: Sequence and Hierarchy**
3. **The Six Domains of Reasoning**
4. **The Architecture of Error (Fallacies)**
5. **Domain Violations: Systematic Taxonomy** (105 fallacies)
6. **Paradox Dissolution Through Hierarchical Analysis**

### Key Insight

```
                    LAW OF ORDER (L5)
                          |
          +---------------+---------------+
          |                               |
    HORIZONTAL                       VERTICAL
    (Sequence)                      (Hierarchy)
          |                               |
    D1 → D2 → D3 → D4 → D5 → D6     L1 → L2 → L3
          |                               |
     FALLACIES                       PARADOXES
     (105 types)                     (7 paradigms)
```

**Fallacies** = Horizontal violations (wrong domain sequence)  
**Paradoxes** = Vertical violations (wrong hierarchical level)

---

## File Structure

```
Architecture_of_Reasoning/
│
├── Architecture_of_Reasoning.v      # ★ Unified formalization (623 lines)
│   ├── Five Laws of Logic (L1-L5)
│   ├── Six Domains (D1-D6)
│   ├── Three Hierarchical Levels
│   ├── E/R/R Framework
│   ├── Five Fallacy Types
│   ├── Four Paradox Types
│   └── Verification Framework
│
├── AI_FallacyDetector.v             # ★ NEW: AI Application (657 lines)
│   ├── LLM Response Verification
│   ├── Chain-of-Thought Validation
│   ├── Self-Reflection Loop
│   ├── Safety Layer
│   └── OCaml Extraction Ready
│
├── ERR_Fallacies.v                  # Complete fallacy formalization (890+ lines)
│   ├── Type 1: Condition Violations
│   ├── Type 2: Domain Violations (structure)
│   ├── Type 3: Sequence Violations
│   ├── Type 4: Syndromes
│   └── Type 5: Context-Dependent
│
├── DomainViolations_Complete.v      # 105 fallacies from Article 5 (485 lines)
│   ├── D1: Recognition (26 fallacies)
│   ├── D2: Clarification (13 fallacies)
│   ├── D3: Framework Selection (16 fallacies)
│   ├── D4: Comparison (8 fallacies)
│   ├── D5: Inference (20 fallacies)
│   └── D6: Reflection (22 fallacies)
│
├── ParadoxDissolution.v             # Paradox analysis from Article 6 (770 lines)
│   ├── Structural paradoxes (Liar, Russell)
│   ├── Typological paradoxes (Sorites)
│   ├── Pseudo-paradoxes (Ship of Theseus)
│   └── Spurious paradoxes (Newcomb, Carroll)
│
└── Article_ERR_Fallacies.tex        # LaTeX article (39KB)
```

---

## Statistics

| File | Lines | Theorems | Admitted |
|------|-------|----------|----------|
| `Architecture_of_Reasoning.v` | 623 | 17 | **0** |
| `AI_FallacyDetector.v` | 657 | 5 | **0** |
| `ERR_Fallacies.v` | 892 | 22 | **0** |
| `DomainViolations_Complete.v` | 485 | 17 | **0** |
| `ParadoxDissolution.v` | 770 | 24 | **0** |
| **TOTAL** | **3427** | **85** | **0** |

---

## AI Applications (Killer Feature)

### 1. LLM Response Verification

```coq
Definition verify_llm_response (ra : ReasoningAttempt) (sig : ResponseSignals)
  : VerificationResult := ...

(* Returns: VR_Valid | VR_Type2_DomainViolation D FM | VR_Paradox_LevelConfusion LC *)
```

### 2. Chain-of-Thought Validation

```
Prompt template:
"Reason step-by-step through domains D1→D6:

D1 (Recognition): What exactly is the question/claim?
D2 (Clarification): What do the key terms mean?
D3 (Framework): What criteria will you use?
D4 (Comparison): How does this compare to known cases?
D5 (Inference): What follows from the evidence?
D6 (Reflection): What are the limits of this conclusion?

Prove no domain violation at each step."
```

### 3. Self-Reflection Loop

```python
response = llm(prompt)
violation = coq_detector(response)
if violation:
    prompt2 = f"Fix {violation}. Retry."
    response2 = llm(prompt2)
```

```coq
Definition generate_fix_prompt (vr : VerificationResult) : string :=
  match vr with
  | VR_Type2_DomainViolation d fm =>
      "Fallacy detected in " ++ domain_name d ++ ": " ++ failure_mode_name fm
  | VR_Paradox_LevelConfusion lc =>
      "Paradox detected: " ++ level_confusion_name lc
  ...
```

### 4. Safety Layer

```coq
Definition safety_check (sig : ResponseSignals) : SafetyResult :=
  if sig_self_reference sig then SR_SelfReferentialLoop
  else if sig_attacks_person sig then SR_AdHominem
  else if negb (sig_considers_counter sig) then SR_ConfirmationBias
  else SR_Safe.
```

**Blocks:**
- Confirmation bias in training data
- Ad hominem in debates  
- Self-referential hallucinations (Liar-style)
- Unfalsifiable claims

### 5. OCaml Extraction

```coq
Extraction "ai_fallacy_detector.ml" 
  verify_reasoning
  verify_llm_response
  safety_check
  generate_fix_prompt.
```

→ Real OCaml module for inference pipeline integration.

### Specific Fallacy Detectors

| Detector | Domain | Detects |
|----------|--------|---------|
| `detect_ad_hominem` | D1 | Person attack without argument |
| `detect_straw_man` | D1 | Position distortion |
| `detect_false_dilemma` | D2 | Missing options |
| `detect_appeal_to_tradition` | D3 | Irrelevant criterion |
| `detect_false_analogy` | D4 | Insufficient similarity |
| `detect_non_sequitur` | D5 | Logical gap |
| `detect_hasty_generalization` | D5 | Small sample |
| `detect_confirmation_bias` | D6 | No counterevidence |

---

## Key Theorems

### Hierarchy Principle
```coq
Theorem self_application_invalid : forall l, ~ valid_application l l.
(* Operations cannot apply to themselves — blocks all self-referential paradoxes *)
```

### Fallacy Count
```coq
Theorem total_type2_fallacies : 
  D1 + D2 + D3 + D4 + D5 + D6 = 105.
(* 26 + 13 + 16 + 8 + 20 + 22 = 105 domain violation fallacies *)
```

### Vulnerability Distribution
```coq
Theorem D1_D6_most_vulnerable :
  D1 >= D2 /\ D1 >= D3 /\ D1 >= D4 /\
  D6 >= D2 /\ D6 >= D4.
(* Recognition and Reflection are most error-prone *)

Theorem D4_least_vulnerable : forall d,
  d <> D4 -> count D4 <= count d.
(* Comparison is most constrained *)
```

### Paradox Self-Reference
```coq
Theorem structural_self_referential : forall p,
  In p classical_paradoxes ->
  type p = Structural ->
  is_self_referential (confusion p) = true.
(* All structural paradoxes involve self-reference *)
```

---

## E/R/R Framework

Every functional system has three components:

| Component | Level | Description |
|-----------|-------|-------------|
| **E**lements | L1 | What the system contains |
| **R**oles | L1 | How elements relate |
| **R**ules | L2 | Principles governing the system |

### Domain → E/R/R Mapping

| Domain | Primary Corruption | Description |
|--------|-------------------|-------------|
| D1 Recognition | **Element** | WHAT is perceived |
| D2 Clarification | **Role** | HOW it is understood |
| D3 Framework | **Rule** | BY WHAT standard |
| D4 Comparison | Element | WHAT is compared |
| D5 Inference | **Rule** | WHY conclusion follows |
| D6 Reflection | **Rule** | WHY limits recognized |

---

## Paradox Classification

| Type | Examples | Problem | Resolution |
|------|----------|---------|------------|
| **Structural** | Liar, Russell | Self-reference | Hierarchy separation |
| **Typological** | Sorites | Wrong instrument | Change framework |
| **Pseudo** | Ship of Theseus | Premise defect | Clarify premises |
| **Spurious** | Newcomb, Carroll | Hidden contradiction | Expose assumption |

### The Universal Pattern

All paradoxes reduce to **level confusion**:
- Structural: L2 operation includes itself in L1 operand
- Typological: L2 instrument misapplied to L1 object
- Pseudo: L2 analysis reveals L1 contradiction
- Spurious: Hidden assumption confuses levels

---

## Installation

```bash
# Compile all files
coqc Architecture_of_Reasoning.v
coqc ERR_Fallacies.v
coqc DomainViolations_Complete.v
coqc ParadoxDissolution.v

# Verify no unexpected axioms
coqtop -l Architecture_of_Reasoning.v -batch \
  -exec "Print Assumptions unified_diagnosis."
```

Expected output:
```
Closed under the global context
```

---

## Integration with Theory of Systems

These files extend the core Theory of Systems formalization:

```
TheoryOfSystems_Core_ERR.v          # Laws L1-L5, paradox blocking
         │
         ├── Architecture_of_Reasoning.v    # Unified framework
         │         │
         │         ├── ERR_Fallacies.v      # Fallacy types
         │         │
         │         ├── DomainViolations_Complete.v  # 105 fallacies
         │         │
         │         └── ParadoxDissolution.v # Paradox analysis
         │
         └── [Analysis theorems: IVT, EVT, etc.]
```

The E/R/R Framework connects:
- **Theory of Systems**: Philosophical foundations (L1-L5, P1-P4)
- **Architecture of Reasoning**: Diagnostic applications (fallacies, paradoxes)

---

## Citation

```bibtex
@software{architecture_of_reasoning_coq,
  author = {Horsocrates},
  title = {Architecture of Reasoning — Coq Formalization},
  year = {2026},
  url = {https://github.com/horsocrates/theory-of-systems-coq}
}
```

---

## Publications

- **The Architecture of Error: Fallacies as Domain Violations** (Article 4)
- **Domain Violations: A Systematic Taxonomy** (Article 5)
- **Paradox Dissolution Through Hierarchical Analysis** (Article 6)

All available at [PhilPapers](https://philpapers.org/).

---

## License

MIT License — see [LICENSE](LICENSE) for details.
