# src/analysis/ — Analysis Gap Closures

**4 files | 102 Qed | 0 Admitted | 0 axioms**

Classical analysis theorems completing the analysis chain. All files are independent (no cross-imports).

---

## Files

| File | Qed | Key Theorem |
|------|-----|-------------|
| **BolzanoWeierstrass.v** | 26 | `bolzano_weierstrass`: bounded seq has Cauchy subsequence |
| **FTC.v** | 28 | Lipschitz theory, u-substitution, `ftc_monotone` |
| **HeineBorelComplete.v** | 28 | `udiff_implies_uniform_cont`, eps-nets, total boundedness |
| **ImplicitFunction.v** | 20 | `newton_converges`: Newton iteration as Banach contraction |

---

## Key Results

- **Bolzano-Weierstrass**: Bisection of [a,b] choosing half with infinitely many terms (via `classic`). Extracts Cauchy subsequence from nested intervals.
- **FTC Extensions**: `Lipschitz_on` + closure properties, u-substitution via `udiff_compose`, monotonicity consequences of FTC.
- **Heine-Borel Alternatives**: Provable alternatives to the unprovable-over-Q Heine-Borel. Total boundedness, eps-nets, uniform continuity via Lipschitz (not compactness).
- **Implicit Function**: Newton iteration g(x) = x - lambda*f(x) as contraction mapping. Applies Banach fixed point from FixedPoint.v (6th fixed-point application in the project).

---

## Dependencies

All files depend on the analysis chain (CauchyReal, RealField, Completeness, etc.) but NOT on each other.

```bash
# Build any file:
coqc -Q src ToS -Q Architecture_of_Reasoning ToS_Arch src/analysis/<FILE>.v
```
