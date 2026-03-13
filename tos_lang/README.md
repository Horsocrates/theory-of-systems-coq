# tos_lang/ — ToS-Lang Compiler & CLI

**Verified programming language** extracted from Coq to OCaml, with a hand-written parser and Python AI integration.

---

## Overview

ToS-Lang is a minimal dependently-typed language whose type checker, evaluator, and safety guarantees are **proven correct in Coq** (Phases A-D: 421 Qed, 0 Admitted). This directory contains the extracted OCaml code and tooling.

```
$ tos_check examples/identity.tos
Type: Nat
Result: 42
```

---

## Files

### Extracted from Coq (auto-generated)

| File | Source | Description |
|------|--------|-------------|
| Expressions.ml/mli | Expressions.v | Expr (12 constructors), de Bruijn substitution |
| Reduction.ml/mli | Reduction.v | step (15 rules), eval_fuel |
| Typing_Expr.ml/mli | Typing_Expr.v | expr_has_type, canonical forms |
| TypeChecker.ml/mli | TypeChecker.v | typecheck, typecheck_ann |
| Evaluator.ml/mli | Evaluator.v | safe_eval, classify_eval |
| UniversePolymorphism.ml/mli | UniversePolymorphism.v | Universe level hierarchy |
| TheoryOfSystems_Core_ERR.ml/mli | TheoryOfSystems_Core_ERR.v | Core definitions |
| Datatypes.ml/mli | Coq stdlib | Bool, option, sum |
| List.ml/mli | Coq stdlib | List operations |
| Nat.ml/mli | Coq stdlib | Natural numbers |
| PeanoNat.ml/mli | Coq stdlib | Peano arithmetic |
| Specif.ml/mli | Coq stdlib | sig, sigT types |

### Hand-written

| File | Description |
|------|-------------|
| **parser.ml** | Recursive descent parser for `.tos` files (ExprAnn) |
| **printer.ml** | Pretty printer for Expr, Ty, ExprAnn, EvalResult |
| **main.ml** | CLI entry point: `tos_check <file.tos> [--fuel N] [--stdin] [--ast]` |
| **ai_interface.py** | Python AI generation + verification loop (ToSLangVerifier, ToSLangAI) |
| **dune** | OCaml build configuration |
| **dune-project** | Dune project metadata |

---

## CLI Usage

```bash
# Type-check and evaluate a .tos file
tos_check examples/identity.tos

# Set evaluation fuel (default: 100)
tos_check examples/compose.tos --fuel 200

# Read from stdin
echo "(ann (lam Nat (var 0)) (arrow Nat Nat))" | tos_check --stdin

# Show AST
tos_check examples/pair_fst.tos --ast
```

---

## Python AI Interface

```python
from tos_lang.ai_interface import ToSLangVerifier, ToSLangAI

# Verify AI-generated code
verifier = ToSLangVerifier()
result = verifier.verify("(ann (const 42) Nat)")

# AI generation with verification loop
ai = ToSLangAI(llm_client)
safe_code = await ai.generate_verified("identity function on Nat")
```

---

## Coq Provenance

Every safety guarantee traces back to proven Coq theorems:

| Guarantee | Coq Theorem | File |
|-----------|------------|------|
| Type checker is sound | `typecheck_sound` | TypeChecker.v |
| Types preserved by evaluation | `subject_reduction` | SubjectReduction.v |
| Well-typed programs don't get stuck | `progress` | Progress.v |
| End-to-end type safety | `tos_lang_main_theorem` | TypeSafety.v |
| Pipeline correctness | `verified_pipeline` | Evaluator.v |
| AI code safety | `ai_generation_safe` | AIInterface.v |

---

## Building

```bash
# Requires OCaml 4.14+ and dune
dune build

# Or manually:
ocamlfind ocamlopt -package str -linkpkg \
  Datatypes.ml List.ml Nat.ml PeanoNat.ml Specif.ml \
  TheoryOfSystems_Core_ERR.ml UniversePolymorphism.ml \
  Expressions.ml Reduction.ml Typing_Expr.ml \
  TypeChecker.ml Evaluator.ml \
  parser.ml printer.ml main.ml -o tos_check
```
