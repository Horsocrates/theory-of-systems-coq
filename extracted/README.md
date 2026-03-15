# extracted/ — OCaml Extraction Output

Extracted OCaml code from Coq/Rocq via `Extraction` commands.

## Files

| File | Description |
|------|-------------|
| `gap_calculator.ml` | Extracted gap calculator — exact Q arithmetic for mass gap verification |
| `gap_calculator.mli` | OCaml interface for the gap calculator |

## How It Works

The extraction pipeline:
1. `src/extraction/GapExtraction.v` defines `Extraction` directives
2. Rocq extracts certified Coq functions to OCaml
3. Output lands here as `.ml`/`.mli` files
4. The extracted code preserves all verification guarantees from the Coq proofs

## Usage

```bash
# Build (requires OCaml toolchain)
ocamlfind ocamlopt -package zarith gap_calculator.ml -o gap_calc
```
