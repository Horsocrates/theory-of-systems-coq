# src/stdlib/ — Verified Standard Library

**12 files | 230 Qed | 0 Admitted | 0 axioms**

Verified data structures and algorithms for Theory of Systems, each modeled as a ToS System with Elements, Roles, Rules, and Constitution.

---

## Design Principles

Every data structure in this library connects back to the ToS Deductive Chain:

| ToS Concept | Stdlib Usage | Source File |
|-------------|-------------|-------------|
| **L5: Law of Order** | `DecTotalOrder` for sorted structures | `L5Resolution.v` |
| **P4: Process Philosophy** | `FinitelyGenerated` for finite depth, `GenProcess` for streams | `InductiveSystems.v`, `ProcessGeneral.v` |
| **Constitution** | `DecidableConstitution` for membership predicates | `ConstitutionChecking.v` |
| **Pi-Systems** | Higher-order functions as dependent function types | `DependentSystems.v` |
| **E/R/R Framework** | Each module documents its Elements, Roles, Rules | `TheoryOfSystems_Core_ERR.v` |

---

## Modules

### Data Structures

#### TMap.v — Sorted Key-Value Map (31 Qed)

```
Elements: (key, value) pairs
Roles:    Key -> Identifier, Value -> Payload
Rules:    Keys sorted by DecTotalOrder, unique keys
```

| Operation | Type | Description |
|-----------|------|-------------|
| `tm_empty` | `list (K * V)` | Empty map |
| `tm_insert` | `K -> V -> map -> map` | Insert/update key-value pair |
| `tm_lookup` | `K -> map -> option V` | Look up value by key |
| `tm_remove` | `K -> map -> map` | Remove key |
| `tm_keys` | `map -> list K` | Extract all keys |
| `tm_mem` | `K -> map -> bool` | Membership test |

Key properties: `tm_lookup_insert_eq`, `tm_insert_sorted`, `tm_remove_sorted`, `NoDup_keys`.

Also defines `Sorted` predicate and helper lemmas used by TSet.

#### TSet.v — Sorted Unique Set (30 Qed)

```
Elements: set members
Roles:    Member -> element with verified membership
Rules:    Sorted, no duplicates, closed under union/inter/diff
```

| Operation | Type | Description |
|-----------|------|-------------|
| `ts_add` | `A -> set -> set` | Insert element (maintains sorted order) |
| `ts_member` | `A -> set -> bool` | Membership test |
| `ts_union` | `set -> set -> set` | Set union |
| `ts_inter` | `set -> set -> set` | Set intersection |
| `ts_diff` | `set -> set -> set` | Set difference |
| `ts_subset` | `set -> set -> bool` | Subset check |

Key properties: `ts_member_add_eq`, `ts_add_sorted`, `ts_member_In` (iff), `ts_subset_refl`.

#### TTree.v — Binary Search Tree (23 Qed)

```
Elements: tree nodes with values
Roles:    Node -> Container, Value -> Stored Element
Rules:    BST invariant (left < root < right)
```

| Operation | Type | Description |
|-----------|------|-------------|
| `tree_insert` | `A -> TTree -> TTree` | Insert maintaining BST |
| `tree_member` | `A -> TTree -> bool` | Membership test |
| `tree_inorder` | `TTree -> list A` | In-order traversal |
| `tree_size` | `TTree -> nat` | Number of nodes |
| `tree_height` | `TTree -> nat` | Tree height |

Key properties: `tree_insert_bst`, `tree_insert_member`, `tree_height_le_size` (P4 compliance).

#### TQueue.v — FIFO Banker's Queue (14 Qed)

```
Elements: queue items
Roles:    Front -> next to dequeue, Back -> recently enqueued
Rules:    FIFO order, to_list = front ++ rev back
```

| Operation | Type | Description |
|-----------|------|-------------|
| `tq_enqueue` | `A -> TQueue -> TQueue` | Add to back |
| `tq_dequeue` | `TQueue -> option (A * TQueue)` | Remove from front |
| `tq_peek` | `TQueue -> option A` | View front element |
| `tq_to_list` | `TQueue -> list A` | Convert to list (FIFO order) |

Key properties: `tq_to_list_enqueue`, `tq_dequeue_front`, `tq_size_enqueue`.

---

### Numeric Types

#### TInt.v — Integer Arithmetic (18 Qed)

```
Elements: integers (Z)
Roles:    SignedQuantity (positive | negative | zero)
Rules:    Ring axioms, integral domain
```

Operations: `tint_add`, `tint_mul`, `tint_sub`, `tint_abs`, `tint_neg`, `tint_div`, `tint_mod`.

Key properties: commutativity, associativity, distributivity, `tint_abs_nonneg`, `classify_tint` (status classification).

#### TComplex.v — Complex Numbers over Q (19 Qed)

```
Elements: complex numbers (re + im*i)
Roles:    RealPart, ImaginaryPart
Rules:    Field axioms over Qeq, conjugate involution
```

Operations: `tc_add`, `tc_mul`, `tc_conj`, `tc_neg`, `tc_norm_sq`.

Key properties: `tc_add_comm`, `tc_mul_comm`, `tc_conj_involutive`, `tc_norm_sq_nonneg`, `tc_i_squared` (i*i = -1).

---

### Algorithms

#### TSort.v — Verified Sorting (20 Qed)

```
Elements: list items
Roles:    UnsortedInput -> SortedOutput
Rules:    L5 ordering via DecTotalOrder, permutation preservation
```

| Algorithm | Description |
|-----------|-------------|
| `insertion_sort` | O(n^2) sorting, proven sorted + permutation |
| `merge` | Fuel-based merge of two sorted lists |
| `insert_sorted` | Insert into sorted list maintaining order |

Key properties: `insertion_sort_sorted`, `insertion_sort_perm`, `merge_sorted`.

#### TSearch.v — Verified Search (17 Qed)

```
Elements: list items + search criterion
Roles:    Criterion -> Selector, items -> Candidates
Rules:    DecidableConstitution (search = satisfy constitution?)
```

| Algorithm | Description |
|-----------|-------------|
| `ts_find` | Find first element satisfying predicate |
| `ts_filter` | Filter elements by predicate |
| `ts_find_index` | Find index of first match |
| `ts_count` | Count matching elements |
| `binary_search` | Fuel-based binary search on nat lists |

Key properties: `ts_find_some_true`, `ts_find_some_in`, `ts_filter_In`, `ts_filter_app`.

---

### Combinators

#### THigherOrder.v — Map, Filter, Fold (18 Qed)

```
Elements: list items + transformation function
Roles:    f -> Transformer (Pi-type), p -> Selector (Constitution check)
Rules:    Function application preserves well-formedness
```

Operations: `tmap`, `tfilter`, `tfold_left`, `tfold_right`, `tmap_filter`, `tforall`, `texists`.

Key properties: `tmap_length`, `tmap_compose`, `tfilter_length`, `tfold_left_app`, `tforall_true_iff`.

#### TStream.v — Infinite Lazy Streams (14 Qed)

```
Elements: stream positions (nat -> A)
Roles:    Observable via P4 (infinite process, finite observation)
Rules:    GenProcess from ProcessGeneral.v
```

Operations: `ts_head`, `ts_tail`, `ts_take`, `ts_iterate`, `ts_map`, `ts_zip_with`, `ts_constant`.

Key properties: `ts_head_cons`, `ts_take_length`, `ts_map_head`, `ts_map_compose`, `ts_iterate_nth`.

#### TOption.v — Option and Result Types (14 Qed)

```
Elements: wrapped value (or absence/error)
Roles:    Some -> Present, None -> Absent, Ok -> Success, Err -> Failure
Rules:    Must pattern match before access (constitution)
```

Operations: `toption_map`, `toption_bind`, `toption_default`, `tresult_map`, `tresult_bind`, `tresult_map_err`.

Key properties: `toption_map_some`, `toption_bind_some`, `tresult_map_ok`, `tresult_bind_ok`.

---

### Integration

#### StdlibExamples.v — Cross-Module Examples (12 Qed)

Demonstrates interaction between 9 stdlib modules in a single file:

| Example | Modules Used |
|---------|-------------|
| Map insert + lookup | TMap |
| Set add + member | TSet |
| Set union + subset | TSet |
| BST insert + member | TTree |
| Queue enqueue + to_list | TQueue |
| Find in list | TSearch |
| Map + filter composition | THigherOrder |
| Fold to sum | THigherOrder |
| Stream iterate + take | TStream |
| Option bind chain | TOption |
| Integer abs(neg(x)) | TInt |
| **Fold builds set, then member** | **THigherOrder + TSet** |

---

## Building

All files compile with Rocq 9.0.1. Dependencies are managed via `_CoqProject`:

```bash
# From repository root:
coq_makefile -f _CoqProject -o Makefile
make

# Single file:
coqc -Q src ToS -Q Architecture_of_Reasoning ToS_Arch src/stdlib/TMap.v
```

### Compilation Order

```
L5Resolution.v, InductiveSystems.v, ConstitutionChecking.v, ...
    |
    v
TMap.v  (defines Sorted)
    |
    v
TSet.v  (imports TMap)
    |
    v
TTree.v, TQueue.v, TInt.v, TComplex.v, TStream.v,
TSort.v, TSearch.v, THigherOrder.v, TOption.v
    (independent of each other)
    |
    v
StdlibExamples.v  (imports all except TSort, TComplex)
```
