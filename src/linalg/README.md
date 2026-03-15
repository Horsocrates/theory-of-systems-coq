# src/linalg/ — Eigenvalue Algorithms & Ionization (130 Qed)

Matrix operations, eigenvalue theory, Gershgorin discs, power method,
and ionization threshold — all as process constructions.

## Files (6 files, 130 Qed, 0 Admitted)

| File | Qed | Description |
|------|-----|-------------|
| `MatrixOps.v` | 22 | Q-valued matrices, multiplication, transpose, trace |
| `EigenvalueTheory.v` | 22 | Eigenvalue definition, characteristic polynomial |
| `GershgorinDiscs.v` | 22 | Gershgorin circle theorem for eigenvalue localization |
| `PowerMethod.v` | 22 | Power iteration as process, convergence to dominant eigenvalue |
| `IonizationThreshold.v` | 22 | Ionization energy as spectral threshold |
| `EigenvalueSynthesis.v` | 20 | Unified synthesis: eigenvalues → physical predictions |

## Key Results

- `gershgorin_theorem` — eigenvalues lie in Gershgorin discs
- `power_method_converges` — power iteration is a Cauchy process
- `ionization_from_eigenvalue` — ionization threshold from spectral bound
