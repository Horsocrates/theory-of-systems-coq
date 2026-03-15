# src/zeta/ — Riemann Zeta & Number Theory (594 Qed)

Process-based approach to the Riemann zeta function, prime number theory,
zero-free regions, and explicit formulas. Exploratory but fully verified.

## Files (24 files, 594 Qed, 0 Admitted)

### RH Phase 1 — Zero-Free Region (5 files, 118 Qed)

| File | Qed | Description |
|------|-----|-------------|
| `TrigInequality.v` | 24 | 3+4cos+cos2 ≥ 0, de la Vallee-Poussin |
| `ComplexZeta.v` | 24 | Zeta as process, Euler product, functional equation |
| `ZeroFreeRegion.v` | 24 | Classical zero-free region σ > 1-c/log(t) |
| `PartialSumZeros.v` | 24 | N(T) counting function, Riemann-von Mangoldt |
| `RH_Phase1_Synthesis.v` | 22 | Unified synthesis of Phase 1 results |

### RH Phase 2 — Explicit Formula (5 files, 140 Qed)

| File | Qed | Description |
|------|-----|-------------|
| `LogZeta.v` | 28 | Log-derivative of zeta, Dirichlet series |
| `PrimeSumBounds.v` | 28 | Prime sum bounds, Mertens-type estimates |
| `ZeroCountingProcess.v` | 28 | Zero counting as Cauchy process |
| `ExplicitFormula.v` | 28 | Von Mangoldt explicit formula |
| `RH_Phase2_Synthesis.v` | 28 | Unified synthesis of Phase 2 results |

### Earlier Exploration (14 files, 336 Qed)

Includes: Bernoulli numbers, zeta at negative integers, Abel regularization,
Casimir energy, vacuum energy, Coulomb tower, Lamb shift tower, and more.

## Status

This is **exploratory** work — the Riemann Hypothesis itself is not claimed
as proven. The formalization builds verified infrastructure: zero-free regions,
explicit formulas, and counting functions — all as P4 processes.
