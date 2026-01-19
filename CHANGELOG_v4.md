# Theory of Systems — Changelog v4

## [4.0.0] - 2026-01-18: EVT Breakthrough via Index-Based Approach

### Major Achievement
- **EVT_idx.v created:** 23 Qed, 0 Admitted (100%!)
- Key insight from Gemini: "Don't seek value, seek position (L5)"
- `max_on_grid_attained` now proven trivially via Leibniz equality

### Technical Changes

#### New Definitions (EVT_idx.v)
```coq
(* Accumulator-based argmax returning INDEX *)
Fixpoint find_max_idx_acc (f : Q -> Q) (l : list Q) 
  (curr_idx best_idx : nat) (best_val : Q) : nat := ...

Definition argmax_idx (f : Q -> Q) (l : list Q) (default : Q) : nat := ...

(* max_on_grid via index — THE KEY CHANGE *)
Definition max_on_grid (f : Q -> Q) (a b : Q) (n : nat) : Q :=
  let l := grid_list a b n in
  f (nth (argmax_idx f l a) l a).
```

#### New Lemmas (all Qed)
- `find_max_idx_acc_invariant` — accumulator maintains max property
- `find_max_idx_acc_bound` — result is valid index
- `argmax_idx_bound` — argmax_idx < length l
- `argmax_idx_maximizes` — f(nth argmax_idx) >= f(nth k) for all k
- `max_on_grid_attained` — **NOW TRIVIAL!**
- `grid_value_le_max` — any grid value ≤ max
- `sup_process_is_Cauchy` — main EVT result

### Statistics Update
| Metric | v3.0 | v4.0 | Change |
|--------|------|------|--------|
| Total Qed | ~390 | 385 | — |
| Total Admitted | 12 | 8 | **−4** |
| EVT Admitted | 4 | 0 | **−4** |
| Completion | 97% | 98% | +1% |

### Philosophical Significance
The index-based approach embodies L5 (Order): instead of asking "what is the maximum value?", we ask "where is the maximum position?". This transforms a Qeq-problematic existential into a definitional equality.

Gemini's insight: "Instability in mathematics is simply a lack of Rules in the System."

### Remaining 8 Admitted (categorized)
- 2 philosophically impossible over Q (Heine-Borel, uniform continuity)
- 3 universe-level in Coq (type theory)
- 3 digit stability (Qfloor issues)

---

## [3.0.0] - 2026-01-18: Methodological Insights + EVT Progress

### Major Discovery
- **Digit Stability Problem:** Qfloor and mod 3 are discontinuous L3 operations on continuous L2 objects
- This explains why digit-based proofs fail near L2/L3 boundaries

### Key Changes
- `sup_process_is_Cauchy`: Admitted → **Qed**
- 5+ helper lemmas for EVT grid analysis
- Documentation of interval vs digit approaches

---

## [2.0.0] - 2026-01-17: E/R/R Framework Integration

### Structural Changes
- All files renamed to `*_ERR.v` suffix
- E/R/R (Elements/Roles/Rules) comments added throughout
- P4 (Process Philosophy) explicitly documented

### Completeness
- ShrinkingIntervals_uncountable_CLEAN.v: 100% complete
- IVT: 100% complete
- Archimedean: 100% complete

---

## [1.0.0] - 2026-01-16: Initial Formalization

### Foundation
- TheoryOfSystems_Core.v with L1-L5, P1-P4
- Basic number systems over Q
- Diagonal argument skeleton

### Axiom
- Only `classic` (L3: Law of Excluded Middle)
- No Axiom of Infinity (P4 consequence)
