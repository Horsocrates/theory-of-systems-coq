# examples/ — ToS-Lang Example Programs

Sample `.tos` files demonstrating the verified ToS-Lang programming language.

---

## Programs

| File | Description | Expected Output |
|------|-------------|-----------------|
| **identity.tos** | Identity function `(fun x:Nat. x) 42` | `Type: Nat, Result: 42` |
| **constant.tos** | Constant value `42` | `Type: Nat, Result: 42` |
| **pair_fst.tos** | Pair + first projection `fst (3, 7)` | `Type: Nat, Result: 3` |
| **pair_snd.tos** | Pair + second projection `snd (3, 7)` | `Type: Nat, Result: 7` |
| **compose.tos** | Function composition `f (f 42)` | `Type: Nat, Result: 42` |
| **higher_order.tos** | Higher-order function `apply f 42` | `Type: Nat, Result: 42` |
| **nested_pair.tos** | Nested pair `fst (fst ((3,7), 5))` | `Type: Nat, Result: 3` |
| **swap.tos** | Swap pair components `(snd p, fst p)` | `Type: Nat * Nat` |

---

## Running

```bash
# With the ToS-Lang CLI (from tos_lang/)
tos_check examples/identity.tos

# Or via Coq directly
coqc -Q src ToS src/Demo.v
```

---

## Syntax

ToS-Lang uses annotated s-expressions:

```
(ann EXPR TYPE)           -- type annotation
(const N)                 -- natural number literal
(lam TYPE BODY)           -- lambda (de Bruijn: var 0 = bound variable)
(app FUN ARG)             -- function application
(pair EXPR1 EXPR2)        -- pair construction
(fst EXPR)                -- first projection
(snd EXPR)                -- second projection
(var N)                   -- variable reference (de Bruijn index)
```

**Types:** `Nat`, `(arrow T1 T2)`, `(prod T1 T2)`

---

## Verification

Every program that type-checks is guaranteed safe by the Coq-proven theorem `tos_lang_main_theorem`: well-typed programs either evaluate to a value or take a step — they never get stuck.
