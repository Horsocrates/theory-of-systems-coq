# Digit-Based vs Interval-Based Uncountability Proofs

## Theory of Systems — Two Approaches to Uncountability

This document explains why the **interval-based approach** (ShrinkingIntervals) is the preferred P4-compatible formalization, while the **digit-based approach** (DiagonalArgument) serves as a pedagogical example.

---

## The Problem: Digit Stability

### Classical Cantor Argument

The classical diagonal argument works by:
1. Assume enumeration E: ℕ → [0,1]
2. Construct diagonal D where D differs from E(n) at position n
3. D cannot be in the enumeration

### The Translation Problem

When we formalize this in Coq over Q:

```coq
Definition extract_digit (q : Q) (k : nat) : Z :=
  (Qfloor (q * 3^k) mod 3)%Z.

Definition diagonal_digit (E : Enumeration) (k : nat) : Z :=
  ternary_flip (extract_digit (E k k) k).
```

**The issue:** `Qfloor` and `mod 3` are **discontinuous operations**.

Near boundary points (e.g., 0.333... ≈ 1/3), infinitesimal Q-changes cause digit jumps:
- If `E n n ≈ 1/3 - ε`, then `extract_digit = 0`
- If `E n m ≈ 1/3 + ε`, then `extract_digit = 1`

The Cauchy property guarantees |E n m - E n n| < δ, but **NOT** digit stability!

### Worst Case

If original digit = 1 and it shifts to 2 due to boundary effects:
- `diagonal_digit = flip(1) = 2`
- `shifted_digit = 2`
- **Difference = 0** — the proof fails!

---

## The Solution: Geometry Instead of Digits

### Key Insight (Gemini 2025)

> "The function `Qfloor` and operator `mod` are **discontinuous** operations at L3 (discrete) level, which we're trying to apply to L2 (continuous processes). The solution is **Digit Stability through Geometry**."

### Interval-Based Approach

Instead of extracting digits, we use **trisection with guaranteed gap**:

```
Step n:
1. Have interval I_n of width 1/3^n
2. Take approximation E(n, n + buffer)
3. Divide I_n into three thirds: [L, M, R]
4. Choose the third FARTHEST from the approximation
5. Guaranteed gap: delta = 1/(12 * 3^n)
```

### Why This Works

**The enemy (E(n)) occupies at most 1/3 of the interval.**

By choosing the farthest third, we get:
- At least 2/3 of interval is "safe"
- Gap of delta ensures stability under Cauchy convergence
- No discontinuous operations needed

---

## Comparison

| Aspect | Digit-Based | Interval-Based |
|--------|-------------|----------------|
| Core operation | `Qfloor`, `mod 3` | Interval arithmetic |
| Continuity | Discontinuous | Continuous |
| Gap guarantee | None (boundary issues) | `delta = 1/(12 * 3^n)` |
| Stability | Problematic | Built-in |
| Coq status | 41 Qed, **1 Admitted** | 167 Qed, **0 Admitted** |
| P4 alignment | Partial (L3 ops on L2) | Full |

---

## Files

### ShrinkingIntervals_uncountable_CLEAN.v (RECOMMENDED)
- **Status:** 100% complete (167 Qed, 0 Admitted)
- **Main theorem:** `unit_interval_uncountable_trisect_v2`
- **Approach:** Trisection with synchronized delta
- **Philosophy:** Pure P4 — finite, decidable, no discontinuous ops

### DiagonalArgument_integrated.v (PEDAGOGICAL)
- **Status:** 98% complete (41 Qed, 1 Admitted)
- **Main theorem:** `unit_interval_uncountable` (depends on Admitted)
- **Approach:** Classical digit flip
- **Philosophy:** Shows why naive Cantor translation has issues

---

## Mathematical Equivalence

Both approaches prove the same theorem:

```coq
Theorem: forall E : Enumeration,
  valid_enumeration E ->
  exists D : RealProcess,
    is_Cauchy D /\
    in_unit_interval D /\
    forall n : nat, not_equiv D (E n).
```

The diagonal constructed by intervals IS the "correct" diagonal — it just avoids the digit extraction step that causes problems.

---

## Philosophical Significance

### L2/L3 Boundary

The digit-based approach attempts to apply **L3 operations** (discrete, discontinuous) to **L2 objects** (continuous processes). This category error manifests as the digit stability problem.

### P4 Finitude

The interval approach respects P4 properly:
- Each step is **finite** and **decidable**
- No reference to "completed" digit sequences
- Gap provides **quantitative sufficient reason** (L4) for separation

### Sufficient Reason (L4)

In the interval approach, we can explicitly state WHY the diagonal differs:

> "D(m) is in interval I_{n+1}, which was chosen to be at distance ≥ delta from E(n)'s approximation. By Cauchy property, E(n) stays near its approximation, so D differs from E(n) by at least delta/2."

This is a **quantitative sufficient reason**, not just "the digits differ somewhere."

---

## Conclusion

The digit-based diagonal is a valuable **pedagogical tool** showing:
1. How the classical argument translates to formal systems
2. Where discontinuity issues arise
3. Why careful treatment of L2/L3 boundaries matters

The interval-based approach is the **production-quality proof** that:
1. Is fully formalized (0 Admitted)
2. Aligns with Theory of Systems (P4, L4)
3. Avoids all boundary/stability issues

**For citations and formal verification, use `ShrinkingIntervals_uncountable_CLEAN.v`.**

---

*Document created: January 2026*
*Theory of Systems — Coq Formalization Project*
