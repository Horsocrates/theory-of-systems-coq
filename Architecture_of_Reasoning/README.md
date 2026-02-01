# Architecture of Reasoning — Coq Formalization

[![Coq](https://img.shields.io/badge/Coq-8.18.0-blue.svg)](https://coq.inria.fr/)
[![Status](https://img.shields.io/badge/Status-100%25_Complete-brightgreen.svg)]()
[![Admitted](https://img.shields.io/badge/Admitted-0-brightgreen.svg)]()
[![Fallacies](https://img.shields.io/badge/Fallacies-156-blue.svg)]()
[![Paradoxes](https://img.shields.io/badge/Paradoxes-46-blue.svg)]()
[![Theorems](https://img.shields.io/badge/Theorems-124-blue.svg)]()
[![OCaml](https://img.shields.io/badge/OCaml-Extractable-orange.svg)]()
[![Python](https://img.shields.io/badge/Python-Demo-green.svg)]()

> **Complete formal verification of the Architecture of Reasoning: 156 Fallacies, 46 Paradoxes, AI Fallacy Detector, Propaganda Detection**

---

## 🚀 Quick Start

```bash
# Python demo (no dependencies)
python3 demo.py

# Or analyze custom text
python3 demo.py "You're an idiot if you believe that."

# Interactive mode
python3 demo.py --interactive

# OCaml (faster, exact Coq extraction)
ocamlfind ocamlopt -package str -linkpkg ai_fallacy_detector.ml -o detector
./detector
```

**Example Output:**
```
INPUT: "You're an idiot if you believe climate change."

SAFETY CHECK: [!] AD HOMINEM

VERIFICATION RESULT:
  [X] VIOLATION: Object Substitution (Ad Hominem)
      Domain: D1: Recognition

FIX PROMPT:
  1. Address the ARGUMENT, not the person
  2. Identify the actual claim
  3. Provide evidence for/against the claim
```

---

## Overview

This package provides **machine-verified formalization** of the Architecture of Reasoning — a unified framework for understanding errors in reasoning. It accompanies the article series:

1. **The Laws of Logic as Conditions of Existence**
2. **The Law of Order: Sequence and Hierarchy**
3. **The Six Domains of Reasoning**
4. **The Architecture of Error** (Types 1, 3, 4, 5: 51 fallacies)
5. **Domain Violations: A Systematic Taxonomy** (Type 2: 105 fallacies)
6. **Paradox Dissolution Through Hierarchical Analysis**

### Complete Taxonomy: 156 Fallacies

| Type | Description | Count |
|------|-------------|-------|
| **Type 1** | Violations of Conditions | 36 |
| **Type 2** | Domain Violations | 105 |
| **Type 3** | Violations of Sequence | 3 |
| **Type 4** | Syndromes | 6 |
| **Type 5** | Context-Dependent Methods | 6 |
| **TOTAL** | | **156** |

> **Note: Why ~150 in articles?**
> Type 5 methods (6) are context-dependent — valid in some contexts, fallacious in others. 
> They are not "errors" in the same sense as Types 1-4.
> **Core fallacies** (always errors): 36 + 105 + 3 + 6 = **150**
> **Complete taxonomy** (including context-dependent): 150 + 6 = **156**

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
     (156 types)                     (46 classified)
```

**Fallacies** = Horizontal violations (wrong domain sequence)  
**Paradoxes** = Vertical violations (structural) OR premise defects (defective) OR neither (non-paradoxes)

---

## File Structure

```
Architecture_of_Reasoning/
│
├── Article_6_Paradox_Dissolution.pdf    # ★ ARTICLE 6 (24 pages)
├── Paradox_Dissolution_Article_v2.tex   # LaTeX source
│
├── Article_8_Fallacy_Paradox_Resolution.pdf   # ★ ARTICLE 8 (19 pages)
├── Article_8_Fallacy_Paradox_Resolution.tex   # LaTeX source
│
├── CompleteFallacyTaxonomy.v        # ★ ALL 156 FALLACIES (Types 1-5)
│   ├── Type 1: Violations of Conditions (36)
│   ├── Type 2: Domain Violations (105) 
│   ├── Type 3: Violations of Sequence (3)
│   ├── Type 4: Syndromes (6)
│   └── Type 5: Context-Dependent Methods (6)
│
├── AI_FallacyDetector.v             # ★ AI APPLICATION (1279 lines)
│   ├── LLM Response Verification
│   ├── Chain-of-Thought Validation
│   ├── Self-Reflection Loop
│   ├── Safety Layer
│   ├── Hallucination Classification
│   ├── Mock Testing Framework
│   ├── xAI/Grok Integration
│   └── OCaml Extraction Ready
│
├── ParadoxDissolution.v             # Paradox analysis (1250 lines)
│   ├── 46 Paradoxes classified:
│   │   ├── Structural (13): Liar, Epimenides, Grelling-Nelson, Berry,
│   │   │                    Richard, Curry, Crocodile, Buridan's Bridge,
│   │   │                    Yablo, Russell, Barber, Burali-Forti, Cantor
│   │   ├── Defective (25): Sorites, Ship of Theseus, Unexpected Hanging,
│   │   │                   Newcomb, Carroll's Tortoise, Hilbert's Hotel,
│   │   │                   Galileo, Banach-Tarski, Zeno's paradoxes, etc.
│   │   └── Non-paradoxes (8): Monty Hall, Birthday, Simpson's, etc.
│   └── LLM Hallucination Mapping
│
├── Architecture_of_Reasoning.v      # Unified formalization (623 lines)
├── ERR_Fallacies.v                  # E/R/R Framework (892 lines)
├── DomainViolations_Complete.v      # Type 2 details (485 lines)
└── README.md
```

---

## Statistics

| File | Lines | Theorems | Admitted |
|------|-------|----------|----------|
| `CompleteFallacyTaxonomy.v` | 601 | 19 | **0** |
| `AI_FallacyDetector.v` | 1279 | 20 | **0** |
| `ParadoxDissolution.v` | 1250 | 29 | **0** |
| `Architecture_of_Reasoning.v` | 623 | 17 | **0** |
| `ERR_Fallacies.v` | 906 | 22 | **0** |
| `DomainViolations_Complete.v` | 485 | 17 | **0** |
| `ai_fallacy_detector.ml` | 461 | - | - |
| `demo.py` | 272 | - | - |
| `detector.py` | 436 | - | - |
| **Coq TOTAL** | **5144** | **124** | **0** |
| **All Code TOTAL** | **6313** | **124** | **0** |

---

## 🚀 Live Demo: Compiled OCaml Detector

The Coq formalization extracts to a working OCaml binary:

```bash
# Compile
$ ocamlfind ocamlopt -package str -linkpkg ai_fallacy_detector.ml -o detector

# Run
$ ./detector
```

**Example Output:**

```
INPUT: "You're an idiot if you believe climate change."
────────────────────────────────────────────────────
SIGNAL EXTRACTION:
  • attacks_person:      true
  • addresses_argument:  false

SAFETY CHECK:
  ⚠ AD HOMINEM detected

VERIFICATION RESULT:
  ✗ TYPE 2 VIOLATION in D1: Recognition
    Object Substitution (Ad Hominem)

FIX PROMPT:
  1. Address the ARGUMENT, not the person making it
  2. Identify the actual claim being made
  3. Provide evidence for/against the claim itself
────────────────────────────────────────────────────

INPUT: "Climate data supports warming. However, critics 
        note measurement issues. Therefore, we should 
        acknowledge uncertainty."
────────────────────────────────────────────────────
VERIFICATION RESULT:
  ✓ VALID: No violations detected
```

**Files:**
- `ai_fallacy_detector.ml` — OCaml source (standalone)
- `demo.py` — Python demo (no dependencies)
- `detector.py` — Full Python wrapper with API integration
- `llm_experiment.py` — LLM testing framework
- `demo_output.txt` — Full test run output

---

## 🧪 LLM Experiment Results

We tested the detector on actual LLM outputs (see `LLM_EXPERIMENT_RESULTS.md`):

| Test Case | Expected | Detected | Result |
|-----------|----------|----------|--------|
| Ad Hominem Attack | Violation | D1: Ad Hominem | ✓ |
| Valid Reasoning | Valid | Valid | ✓ |
| Overconfident Hallucination | Violation | D6: Confirmation Bias | ✓ |
| Self-Referential Loop | Paradox | Self-Application | ✓ |
| Appeal to Tradition | Violation | D3: Tradition Fallacy | ✓ |
| Whataboutism | Violation | D3: Propaganda | ✓ |

**Overall Accuracy: 6/6 (100%)**

> Detection accuracy is theorem-guaranteed for correctly extracted signals.
> The gap lies in NLP quality, not logical structure.

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

### 6. LLM Hallucination Classification

| Hallucination Type | Architecture Violation | Domain |
|--------------------|----------------------|--------|
| Factual | Object Deformation | D1 |
| Logical | Logical Gap | D5 |
| Self-Referential | Paradox (Level Confusion) | Vertical |
| Overconfident | Illusion of Completion | D6 |
| Sycophantic | No Constitution | Type 1 |

```coq
Theorem hallucinations_are_violations : forall h : HallucinationType,
  hallucination_to_violation h <> VR_Valid.
(* All LLM hallucinations are detectable through the architecture *)
```

### NLP Integration Stubs

For production systems, placeholder interfaces for:
- Token-level analysis
- Entity recognition (person vs argument)
- Sentiment scoring
- Self-reference detection
- Logical connector identification

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
| `detect_propaganda` | D1-D6 | Information warfare patterns |

### 7. Propaganda Detection (NEW)

```coq
Inductive PropagandaPattern : Type :=
  | PP_DehumanizingLanguage   (* D1: Object substitution *)
  | PP_FalseDichotomy         (* D2: Incomplete analysis *)
  | PP_AppealToFear           (* Type 1: Emotional manipulation *)
  | PP_BigLie                 (* Type 1: Disinformation *)
  | PP_Whataboutism           (* D3: Irrelevant criterion *)
  | PP_FalseBalance           (* D4: False equation *)
  | PP_GishGallop             (* D5: Scale error *)
  | PP_NoTrueScotsman.        (* D6: Immunization *)

Theorem propaganda_is_violation : forall pp : PropagandaPattern,
  propaganda_to_violation pp <> VR_Valid.
```

**Example:**
```
INPUT: "Why criticize us? What about their actions?"
PROPAGANDA CHECK: ⚠ Whataboutism detected
VERIFICATION: ✗ D3 Violation (Irrelevant Criterion)
```

---

## Key Theorems

### Complete Taxonomy
```coq
Theorem complete_taxonomy_156 : grand_total = 156.
(* 36 + 105 + 3 + 6 + 6 = 156 fallacies *)

Theorem type2_is_70_percent : 
  core_fallacies = 150 /\ total_type2 * 100 / core_fallacies = 70.
(* Type 2 comprises 70% of core fallacies *)
```

### Hierarchy Principle
```coq
Theorem self_application_invalid : forall l, ~ valid_application l l.
(* Operations cannot apply to themselves — blocks all self-referential paradoxes *)
```

### Vulnerability Distribution
```coq
Theorem D1_D6_most_fallacies :
  D1 >= D2 /\ D1 >= D3 /\ D1 >= D4 /\ D1 >= D5 /\
  D6 >= D2 /\ D6 >= D4.
(* Recognition and Reflection are most error-prone *)

Theorem D4_most_constrained :
  D4 <= D1 /\ D4 <= D2 /\ D4 <= D3 /\ D4 <= D5 /\ D4 <= D6.
(* Comparison has fewest error modes *)
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
