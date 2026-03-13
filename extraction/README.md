# extraction/ — OCaml Extraction (Core Modules)

Auto-generated OCaml code extracted from the core Theory of Systems Coq formalization via `Extraction.v`.

---

## Files

| File | Source | Description |
|------|--------|-------------|
| TheoryOfSystems_Core_ERR.ml/mli | TheoryOfSystems_Core_ERR.v | Levels, Systems, Criteria, Generators |
| IntensionalIdentity.ml/mli | IntensionalIdentity.v | P3: extensional vs intensional identity |
| Roles.ml/mli | Roles.v | E/R/R categories, MathStatus, Dependency |
| ProcessGeneral.ml/mli | ProcessGeneral.v | GenProcess, observe, prefix, process_map |
| QArith_base.ml/mli | Coq stdlib | Rational arithmetic |
| Qabs.ml/mli | Coq stdlib | Rational absolute value |
| BinInt.ml/mli | Coq stdlib | Binary integers (Z) |
| BinNums.ml/mli | Coq stdlib | Binary number types |
| BinPos.ml/mli | Coq stdlib | Positive binary numbers |
| PosDef.ml/mli | Coq stdlib | Positive number definitions |
| Datatypes.ml/mli | Coq stdlib | Bool, option, sum, prod |
| List.ml/mli | Coq stdlib | List operations |
| PeanoNat.ml/mli | Coq stdlib | Peano arithmetic |
| Specif.ml/mli | Coq stdlib | sig, sigT, exists types |
| **diagonal_demo.ml** | Hand-written | Demo of diagonal argument in OCaml |

---

## Purpose

These files provide OCaml implementations of the core ToS framework for:
- Programmatic access to Level/System/Criterion types
- Process observation and transformation
- Rational arithmetic (Q) for numerical processes
- Integration with the diagonal argument demo

---

## Relationship to tos_lang/

| Directory | Contents | Purpose |
|-----------|----------|---------|
| `extraction/` | Core framework (Levels, Systems, Processes) | Foundation types |
| `tos_lang/` | Compiler (Expressions, Typing, Evaluation) | Programming language |

Both are auto-extracted from Coq; `tos_lang/` additionally includes hand-written parser/printer/CLI.

---

## Usage

```bash
# Compile the diagonal demo
ocamlfind ocamlopt -package str -linkpkg \
  Datatypes.ml List.ml Specif.ml BinNums.ml BinPos.ml BinInt.ml \
  PosDef.ml PeanoNat.ml QArith_base.ml Qabs.ml \
  TheoryOfSystems_Core_ERR.ml IntensionalIdentity.ml \
  Roles.ml ProcessGeneral.ml diagonal_demo.ml -o diagonal_demo

./diagonal_demo
```
