# src/extraction/ — Computational Extraction (47 Qed)

Certified gap calculator extracted to OCaml via Rocq's extraction mechanism.

## Files (3 files, 47 Qed, 0 Admitted)

| File | Qed | Description |
|------|-----|-------------|
| `GapCompute.v` | 26 | Core computation: exact Q arithmetic for spectral gaps |
| `GapCertificate.v` | 13 | Certificate type + verification: gap bounds with proofs |
| `GapExtraction.v` | 8 | Extraction directives: Coq → OCaml |

## Pipeline

```
GapCompute.v (computation) → GapCertificate.v (proof) → GapExtraction.v (extract)
    ↓
extracted/gap_calculator.ml (certified OCaml code)
```

## Key Theorems

- `gap_compute_correct` — computed gap matches specification
- `certificate_valid` — certificate carries machine-checked proof
- Extracted code in `../../extracted/gap_calculator.ml`
