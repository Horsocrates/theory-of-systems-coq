# PROJECT STATUS v6 — Phase 3 Update

> **Date:** 2026-03-06
> **Repo:** Horsocrates/theory-of-systems-coq
> **Previous commit:** `25ce38b` (Phase 2 update)
> **Compiler:** Rocq 9.0.1 (Coq rebrand)

---

## 1. Summary Statistics

| Metric | src/ | Architecture_of_Reasoning/ | Total |
|--------|------|---------------------------|-------|
| Files | 39 | 6 | **45** |
| Qed | 928 | 117 | **1045** |
| Admitted | 8 | 0 | **8** |
| Lines | 25,690 | 4,946 | **30,636** |
| Axioms | 0 | 0 | **0** |

**Proof completion rate:** 1045 / (1045 + 8) = **99.2%**

All proofs are constructive over Q (rationals). Zero axioms across the entire codebase.

### Changes since v5 (Phase 2)

| Change | Detail |
|--------|--------|
| **+4 new files** | L5Resolution.v (18 Qed), SystemMorphism.v (17 Qed), InfoLayer.v (17 Qed), LinearAlgebra.v (20 Qed + 4 Defined) |
| **-2 Admitted closed** | `max_on_grid_attained` + `EVT_complete` in EVT_ERR.v |
| **+78 Qed** | 72 new + 4 Defined + 4 from closing Admitted + helpers |
| **+1,312 lines** | 1,262 new files + 50 in modified EVT_ERR.v |

---

## 2. Per-File Statistics

### src/ (39 files, incl. Extraction.v)

| # | File | Qed | Adm | Lines | Topic |
|---|------|-----|-----|-------|-------|
| 1 | Archimedean_ERR.v | 14 | 0 | 186 | Archimedean property of Q |
| 2 | CauchyReal.v | 19 | 0 | 409 | Cauchy sequence reals |
| 3 | Completeness.v | 24 | 0 | 523 | Completeness (least upper bound) |
| 4 | Countability_Q.v | 17 | 0 | 530 | Q is countable |
| 5 | DiagonalArgument_ERR.v | 41 | 1 | 975 | Cantor diagonal (base-3) |
| 6 | Differentiation.v | 18 | 0 | 734 | Uniform differentiability |
| 7 | EVT_ERR.v | 35 | 1 | 1069 | Extreme Value Theorem |
| 8 | EVT_idx.v | 26 | 0 | 709 | EVT (index-based, clean) |
| 9 | FixedPoint.v | 20 | 0 | 737 | Banach contraction mapping |
| 10 | GradientDescent.v | 18 | 0 | 525 | Gradient descent convergence |
| 11 | HeineBorel_ERR.v | 22 | 2 | 642 | Heine-Borel compactness |
| 12 | **InfoLayer.v** | **17** | **0** | **323** | **Information layers** ← NEW |
| 13 | IntensionalIdentity.v | 11 | 0 | 282 | P3: intensional ≠ extensional |
| 14 | IntegralApplications.v | 19 | 0 | 735 | FTC, integration by parts |
| 15 | IVT_CauchyReal.v | 8 | 0 | 382 | IVT lifted to CauchyReal |
| 16 | IVT_ERR.v | 23 | 0 | 424 | Intermediate Value Theorem |
| 17 | **L5Resolution.v** | **18** | **0** | **301** | **Generalized L5 tie-breaking** ← NEW |
| 18 | **LinearAlgebra.v** | **20** | **0** | **355** | **QVec, QMat, dot product** ← NEW |
| 19 | Measure.v | 15 | 0 | 429 | Outer measure, Lebesgue |
| 20 | MeanValueTheorem.v | 18 | 0 | 701 | Rolle, MVT, monotonicity |
| 21 | MonotoneConvergence.v | 15 | 0 | 509 | Monotone convergence |
| 22 | PInterval_CROWN.v | 25 | 0 | 558 | Interval arithmetic + CROWN |
| 23 | PowerSeries.v | 19 | 0 | 491 | Power series, radius of conv. |
| 24 | Probability.v | 12 | 0 | 355 | Discrete probability |
| 25 | ProcessGeneral.v | 16 | 0 | 364 | General process theory |
| 26 | RealField.v | 17 | 0 | 504 | Field operations on CauchyQ |
| 27 | RiemannIntegration.v | 18 | 0 | 601 | Riemann integral |
| 28 | Roles.v | 30 | 0 | 733 | E/R/R roles, status, deps |
| 29 | RoundingSafety.v | 13 | 0 | 345 | IEEE 754 rounding bounds |
| 30 | SchroederBernstein_ERR.v | 14 | 0 | 397 | Schroeder-Bernstein theorem |
| 31 | SeriesConvergence.v | 22 | 0 | 634 | Series, geometric sums |
| 32 | ShrinkingIntervals_ERR.v | 167 | 0 | 3631 | Uncountability (intervals) |
| 33 | SoftmaxProbability.v | 14 | 0 | 353 | Softmax verification |
| 34 | **SystemMorphism.v** | **17** | **0** | **283** | **Structure-preserving maps** ← NEW |
| 35 | TaylorSeries.v | 18 | 0 | 1234 | Taylor polynomials |
| 36 | TernaryRepresentation_ERR.v | 52 | 2 | 992 | Ternary/Cantor set |
| 37 | TheoryOfSystems_Core_ERR.v | 34 | 2 | 1896 | ToS core: Levels, Systems |
| 38 | UniformConvergence.v | 20 | 0 | 691 | Uniform convergence |
| 39 | Extraction.v | — | 0 | — | OCaml extraction directives |

### Architecture_of_Reasoning/ (6 files, all 0 Admitted)

| # | File | Qed | Lines | Topic |
|---|------|-----|-------|-------|
| 1 | AI_FallacyDetector.v | 13 | 1081 | LLM fallacy detection |
| 2 | Architecture_of_Reasoning.v | 17 | 623 | E/R/R framework |
| 3 | CompleteFallacyTaxonomy.v | 19 | 601 | 156-fallacy taxonomy |
| 4 | DomainViolations_Complete.v | 17 | 485 | D1-D6 violation types |
| 5 | ERR_Fallacies.v | 22 | 906 | E/R/R fallacy mapping |
| 6 | ParadoxDissolution.v | 29 | 1250 | 46 paradox dissolutions |

---

## 3. Dependency Graph

### Layer structure (src/ only)

```
LAYER 0 — Standalone (no ToS imports, only Coq stdlib):
  Archimedean_ERR    CauchyReal         Countability_Q
  DiagonalArgument   EVT_ERR            EVT_idx
  HeineBorel_ERR     LinearAlgebra      Measure
  PInterval_CROWN    Probability        RoundingSafety
  SchroederBernstein ShrinkingIntervals SoftmaxProbability
  TernaryRepresentation                 TheoryOfSystems_Core_ERR

LAYER 0.5 — Depends on Core_ERR only:
  Roles                <-- Core_ERR (E/R/R roles, status, dependencies)
  IntensionalIdentity  <-- Core_ERR (P3: intensional ≠ extensional)
  L5Resolution         <-- Core_ERR (generalized L5 tie-breaking)
  SystemMorphism       <-- Core_ERR (structure-preserving maps)

LAYER 0.5b — Depends on Core_ERR + CauchyReal:
  ProcessGeneral       <-- Core_ERR, CauchyReal (general process theory)

LAYER 0.5c — Depends on Core_ERR + IntensionalIdentity:
  InfoLayer            <-- Core_ERR, IntensionalIdentity (information layers)

LAYER 1:
  IVT_ERR          <-- Archimedean_ERR
  RealField        <-- CauchyReal

LAYER 2:
  Completeness     <-- Archimedean_ERR, CauchyReal, RealField
  IVT_CauchyReal   <-- Archimedean_ERR, IVT_ERR, CauchyReal

LAYER 3:
  MonotoneConv     <-- CauchyReal, Completeness

LAYER 4:
  SeriesConv       <-- CauchyReal, Completeness, MonotoneConv

LAYER 5:
  PowerSeries      <-- CauchyReal, RealField, MonotoneConv, SeriesConv
  FixedPoint       <-- CauchyReal, Completeness, MonotoneConv, SeriesConv

LAYER 6:
  GradientDescent  <-- CauchyReal, RealField, MonotoneConv, SeriesConv, PowerSeries

LAYER 7:
  Differentiation  <-- CauchyReal, RealField, SeriesConv, GradientDescent

LAYER 8:
  MeanValueThm    <-- CauchyReal, RealField, EVT_idx, Differentiation

LAYER 9:
  RiemannInteg    <-- CauchyReal, RealField, EVT_idx, Diff, MVT

LAYER 10:
  IntegralApps    <-- CauchyReal, RealField, EVT_idx, Diff, MVT, Riemann

LAYER 11:
  TaylorSeries    <-- CauchyReal, RealField, EVT_idx, Diff, MVT, Riemann, IntApps
  UniformConv     <-- CauchyReal, Completeness, MonoConv, Diff, MVT, Riemann, IntApps
```

### Main chains

**Calculus chain (B16-B22):**
```
CauchyReal -> RealField -> Completeness -> MonotoneConv -> SeriesConv
  -> PowerSeries -> GradientDescent -> Differentiation -> MVT
  -> Riemann -> IntegralApps -> TaylorSeries -> UniformConv -> FixedPoint
```

**ToS foundations chain (Phases 2-3):**
```
Core_ERR -> Roles                (E/R/R roles, status, dependencies, paradox diagnosis)
Core_ERR -> IntensionalIdentity  (P3: intensional ≠ extensional identity)
Core_ERR -> L5Resolution         (generalized L5 tie-breaking with DecTotalOrder)
Core_ERR -> SystemMorphism       (structure-preserving maps, isomorphisms)
Core_ERR + IntId -> InfoLayer    (information layers, composition, capacity)
Core_ERR + CauchyReal -> ProcessGeneral  (general process theory, Cauchy bridge)
```

**Set theory chain:**
```
Archimedean_ERR -> IVT_ERR -> IVT_CauchyReal
Countability_Q (standalone)
ShrinkingIntervals_ERR (standalone, 167 Qed)
DiagonalArgument_ERR (standalone)
TernaryRepresentation_ERR (standalone)
SchroederBernstein_ERR (standalone)
```

**NN verification chain:**
```
PInterval_CROWN (standalone)
LinearAlgebra (standalone — QVec, QMat for multi-dim verification)
RoundingSafety (standalone)
SoftmaxProbability (standalone)
```

**Architecture_of_Reasoning/** — all 6 files are standalone (no cross-imports).

---

## 4. Admitted Inventory (8 total, down from 10)

### Closed in Phase 3

| # | File | Lemma | How closed |
|---|------|-------|------------|
| ~~A2~~ | EVT_ERR.v | `max_on_grid_attained` | Added `uc_implies_proper` (UC → Qeq-respecting), `f(grid_point 0) == f(a)` |
| ~~A3~~ | EVT_ERR.v | `EVT_complete` | Removed `is_Cauchy c` conjunct, proved 4 remaining via argmax_is_max chain |

### Closed in Phase 2

| # | File | Lemma | How closed |
|---|------|-------|------------|
| ~~A1~~ | EVT_ERR.v | `f_argmax_eq_max_list` | Added `max_list_elem_le`, `max_list_le_bound` helpers |
| ~~A5~~ | Core_ERR.v | `update_increases_size` | Added `filter_ext_in_nat`, `NoDup_seq_local` helpers |

### Category A: Provable with effort (2 Admitted, was 4)

| # | File | Lemma | Issue | Effort |
|---|------|-------|-------|--------|
| A4 | TernaryRep.v:565 | `extracted_equals_floor` | Base-3 digit/Qfloor consistency | High (~15 aux lemmas) |
| A6 | TernaryRep.v:960 | `diagonal_Q_separation` | Depends on `extracted_equals_floor` | Blocked by A4 |

### Category B: Fundamentally unprovable over Q (4 Admitted)

| # | File | Lemma | Why unprovable | Alternative |
|---|------|-------|----------------|-------------|
| B1 | DiagArg.v:833 | `diagonal_differs_at_n` | Qfloor discontinuity breaks digit stability | ShrinkingIntervals_ERR.v (0 Admitted) |
| B2 | EVT_ERR.v:546 | `argmax_process_is_Cauchy` | False without uniqueness/isolation of max | EVT_idx.v (0 Admitted) |
| B3 | HeineBorel.v:560 | `Heine_Borel` | FALSE over Q (documented counterexample) | Heine_Borel_uniform (proved, with Lebesgue number) |
| B4 | HeineBorel.v:612 | `continuous_on_uniformly_continuous` | Requires classical Heine-Borel | Assume uniform continuity directly |

### Category C: Requires universe polymorphism (2 Admitted)

| # | File | Lemma | Issue |
|---|------|-------|-------|
| C1 | Core_ERR.v:1273 | `no_self_level_elements` | Universe constraint on `crit_domain` |
| C2 | Core_ERR.v:1304 | `cantor_no_system_of_all_L2_systems` | Same — universe-level proof |

### Admitted Summary

| Category | Count | Closable? |
|----------|-------|-----------|
| A: Provable with effort | 2 | Yes (A4+A6 close together = -2) |
| B: False/unprovable over Q | 4 | No (by design, documented) |
| C: Universe polymorphism | 2 | Possible with Coq universe features |
| **Total** | **8** | **2 closable, 6 permanent** |

---

## 5. Phase 3 New Content

### L5Resolution.v (18 Qed, 301 lines)

Typeclass-based deterministic tie-breaking that generalizes beyond the fixed L1/L2/L3 hierarchy:

| Theorem | Description |
|---------|-------------|
| `l5_resolve_gen_in` | Result is always a member of the input list |
| `l5_resolve_gen_minimal` | Result is ≤ all other list elements |
| `l5_resolve_gen_unique` | Deterministic — same list always gives same result |
| `l5_resolve_gen_singleton` | Singleton list returns its element |
| `nat_compare_spec` | nat comparison satisfies DecTotalOrder |
| `Q_compare_spec` | Q comparison satisfies DecTotalOrder |
| `Z_compare_spec` | Z comparison satisfies DecTotalOrder |

### SystemMorphism.v (17 Qed, 283 lines)

Structure-preserving maps between systems:

| Theorem | Description |
|---------|-------------|
| `morphism_compose` | Composition of morphisms is a morphism |
| `morphism_id` | Identity morphism on any system |
| `iso_compose` | Composition of isomorphisms is an isomorphism |
| `iso_sym` | Inverse of an isomorphism is an isomorphism |
| `iso_refl` | Identity is an isomorphism |
| `iso_preserves_criteria_count` | Isomorphic systems have equal criteria count |
| `morphism_preserves_level` | Morphisms preserve system level |

### InfoLayer.v (17 Qed, 323 lines)

Information flow formalization between system levels:

| Theorem | Description |
|---------|-------------|
| `layer_equiv_refl/sym/trans` | Equivalence relation on layers |
| `layer_compose_assoc` | Composition is associative |
| `layer_compose_id_left/right` | Identity layer is neutral |
| `channel_capacity_nonneg` | Capacity is always ≥ 0 |
| `layer_compose_capacity_min` | Composed capacity ≤ min of components |
| `layer_path_capacity_decreasing` | Capacity decreases along paths |

### LinearAlgebra.v (20 Qed + 4 Defined, 355 lines)

Length-indexed vectors and matrices over Q:

| Theorem | Description |
|---------|-------------|
| `qv_add_comm` | Vector addition is commutative |
| `qv_add_assoc` | Vector addition is associative |
| `qv_scale_distrib` | c·(v₁+v₂) = c·v₁ + c·v₂ |
| `qv_scale_assoc` | (c·d)·v = c·(d·v) |
| `dot_product_comm` | Dot product is commutative |
| `dot_product_zero_right` | v·0 = 0 |
| `mat_vec_mul_length` | Matrix-vector multiply preserves dimension |

### EVT_ERR.v Closures (+4 Qed, −2 Admitted)

| Theorem | Description |
|---------|-------------|
| `Qabs_small_eq_zero` | Archimedean squeeze: \|z\| < ε for all ε > 0 → z == 0 |
| `uc_implies_proper` | Uniformly continuous functions respect Qeq |
| `max_on_grid_attained` | Grid maximum is attained at some grid point (closed) |
| `EVT_complete` | EVT: 4-conjunct conclusion (closed, removed false is_Cauchy conjunct) |

---

## 6. Key Definitions (Phase 3 additions)

| Definition | File | Type | Description |
|-----------|------|------|-------------|
| `DecTotalOrder` | L5Resolution.v | Class | Decidable total order typeclass |
| `l5_resolve_gen` | L5Resolution.v | Fixpoint | Generalized L5 resolution |
| `sys_morphism` | SystemMorphism.v | Record | Structure-preserving map between systems |
| `sys_iso` | SystemMorphism.v | Record | System isomorphism (morphism + inverse) |
| `InfoLayer` | InfoLayer.v | Record | Information layer with capacity and transform |
| `layer_compose` | InfoLayer.v | Definition | Sequential composition of layers |
| `QVec` | LinearAlgebra.v | Record | Length-indexed vector over Q |
| `QMat` | LinearAlgebra.v | Record | Matrix as list of row vectors |
| `dot_product` | LinearAlgebra.v | Definition | Dot product via fold_left |
| `mat_vec_mul` | LinearAlgebra.v | Definition | Matrix-vector multiplication |

---

## 7. Build Information

### Compilation command (per file)

```bash
cd /c/Users/aleks/Desktop/RegulusAI/_tos_coq_clone
ROCQLIB="C:\\Coq\\Rocq-Platform~9.0~2025.08\\lib\\coq" \
  "C:\\Coq\\Rocq-Platform~9.0~2025.08\\bin\\coqc.exe" \
  -Q src ToS -Q Architecture_of_Reasoning ToS_Arch \
  src/<FILE>.v
```

### Full build (45/45 files compile)

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

### Known compiler quirks (Rocq 9.0.1)

- `lra` cannot handle `Qge` — convert to `Qle` first
- `simpl` can over-unfold Fixpoints — use `cbv beta` instead
- `ring` fails on Q division — use `field; lra`
- `nia` regression on nonlinear Z*positive — use `Z.mul_le_mono_nonneg + lia`
- `set ... in *` lambda matching unreliable — set from goal directly
- `qabs_rw` only works in `Qlt` context, not `Qle`
- In Q_scope, `0` parses as Q, not nat — use `O` for nat zero

---

*Generated by audit protocol.*
*Phase 3 complete: +4 files, +78 Qed, -2 Admitted. Total: 1045 theorems, 8 Admitted, 45 files.*
