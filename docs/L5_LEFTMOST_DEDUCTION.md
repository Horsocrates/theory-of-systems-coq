# L5 and Leftmost Tie-Breaking: A Deduction

## The Problem: Plateau Ambiguity

When a continuous function has a "plateau" (flat maximum), multiple grid points can achieve the same maximum value:

```
f(x₁) = f(x₂) = f(x₃) = M  (all maximal)
```

**Question:** Which point is "the argmax"?

Without a deterministic rule:
- Grid n might select x₁
- Grid n+1 might select x₃
- The argmax_process jumps around, failing to be Cauchy

## L5: Law of Order / Positionality

From TheoryOfSystems_Core_ERR.v:

```coq
(** L5: Each element corresponds to a UNIQUE position *)
ss_L5_valid : forall p1 p2 e,
    ss_assignment p1 = Some e -> 
    ss_assignment p2 = Some e -> 
    p1 = p2
```

**Meaning:** If element e is at positions p1 and p2, then p1 = p2.
In other words: **One Role → One Position**.

## The Deduction

### Step 1: "Maximum" as a Role

In E/R/R framework:
- **Elements** = grid points {x₀, x₁, ..., xₙ}
- **Role** = "point of maximum value"
- **Rules** = grid refinement process

### Step 2: Plateau Violates L5

When f has a plateau:
- The Role "maximum" applies to multiple Elements
- Multiple positions share the same Role
- This violates L5's uniqueness requirement

### Step 3: L5 Demands Resolution

L5 states: One Role → One Position.

Therefore, when multiple positions qualify for the Role "maximum", 
we MUST have a Rule that selects exactly one.

### Step 4: Leftmost as L5-Compliant Rule

**The natural L5-compliant choice:** Select the position with minimal index.

Why minimal (leftmost)?
1. **Uniqueness:** min is unique (well-ordering of ℕ)
2. **Determinism:** Same input → same output
3. **Order-respecting:** Uses the inherent order of positions

```coq
(* L5-compliant argmax: when values are equal, choose minimal index *)
if Qle_bool best_val (f x)
then find_max_idx_acc f xs current_idx (S current_idx) (f x)  (* update to current *)
else find_max_idx_acc f xs best_idx (S current_idx) best_val   (* keep earlier *)
```

The `Qle_bool best_val (f x)` with `<=` (not `<`) means:
- When `f(x) = best_val`, we update to `current_idx`
- Since we traverse left-to-right, first occurrence wins
- **Result: Leftmost maximal element**

## The Philosophical Point

Gemini's insight was profound:

> "Instability in mathematics is simply a lack of Rules in the System."

In ToS terms:
- **Instability** = Role without unique Position (L5 violation)
- **Resolution** = Add Rule that enforces L5

The leftmost rule is not arbitrary—it is the **minimal intervention** needed to restore L5 compliance:
1. It uses only the existing Position structure (indices)
2. It chooses the "first" in the natural order
3. It adds no external information

## Formal Statement

**Theorem (informal):** Let S be a System with Positions p₁ < p₂ < ... < pₙ. 
Let R be a Role that applies to a subset {pᵢ₁, pᵢ₂, ...} of Positions.
Then L5 requires selecting exactly one Position for R.
The L5-canonical choice is min{pᵢ₁, pᵢ₂, ...}.

**Corollary:** In argmax over a grid, when multiple points achieve the maximum,
the L5-canonical argmax is the leftmost such point.

## Connection to Process Philosophy (P4)

This also connects to P4:
- As grid refines, the plateau may "resolve" to a unique maximum
- But at finite stage n, we need L5 to make a definite choice
- The leftmost rule ensures the process is well-defined at each stage

## Conclusion

**Leftmost tie-breaking is not a hack—it is the unique L5-compliant resolution of Role ambiguity.**

This is what makes argmax_process Cauchy: not just any rule works, but specifically
a rule that respects the Position structure required by L5.

---

*"Order is not imposed on chaos; Order is the structure of existence itself."* — L5
