# src/experimental/ — Experimental Verification (300 Qed)

Formal verification of physical predictions: Casimir effect, Coulomb potential,
and Lamb shift — all derived from process tower constructions.

## Files (8 files, 300 Qed, 0 Admitted)

| File | Qed | Description |
|------|-----|-------------|
| `BernoulliNumbers.v` | 30 | Bernoulli numbers via process, B₀=1, B₁=-1/2, B₂=1/6 |
| `ZetaNegative.v` | 30 | ζ at negative integers via Abel regularization |
| `CasimirProcess.v` | 32 | Casimir energy E = -π²/720 from ζ(-3) |
| `AbelRegularization.v` | 30 | Abel summation as process, regularized sums |
| `VacuumEnergy.v` | 42 | Vacuum energy density from regularized sums |
| `CoulombTower.v` | 44 | 3D Coulomb potential from projective tower |
| `CoulombFull3D.v` | 46 | Full 3D Coulomb: angular momentum, radial equation |
| `LambShiftTower.v` | 46 | Lamb shift: vacuum polarization correction to hydrogen |

## Key Results

- **Casimir effect**: `casimir_energy_value` — E = -π²/(720·a³)
- **Coulomb potential**: `coulomb_full_3d_synthesis` — complete 3D derivation
- **Lamb shift**: `lamb_shift_synthesis` — QED vacuum polarization as process tower
