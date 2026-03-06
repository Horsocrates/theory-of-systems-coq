# PROJECT STATUS v5 — Phase 2 Update

> **Date:** 2026-03-06
> **Repo:** Horsocrates/theory-of-systems-coq
> **Previous commit:** `289adf9` (B22: FixedPoint)
> **Compiler:** Rocq 9.0.1 (Coq rebrand)

---

## 1. Summary Statistics

| Metric | src/ | Architecture_of_Reasoning/ | Total |
|--------|------|---------------------------|-------|
| Files | 35 | 6 | **41** |
| Qed | 850 | 117 | **967** |
| Admitted | 10 | 0 | **10** |
| Lines | 24,230 | 4,946 | **29,176** |
| Axioms | 0 | 0 | **0** |

**Proof completion rate:** 967 / (967 + 10) = **99.0%**

All proofs are constructive over Q (rationals). Zero axioms across the entire codebase.

### Changes since v5 audit (B22)

| Change | Detail |
|--------|--------|
| **+3 new files** | Roles.v (30 Qed), IntensionalIdentity.v (11 Qed), ProcessGeneral.v (16 Qed) |
| **-2 Admitted closed** | A1: `f_argmax_eq_max_list` (EVT_ERR.v), A5: `update_increases_size` (Core_ERR.v) |
| **+63 Qed** | 57 new + 6 from closing Admitted + helpers |
| **+1,457 lines** | 1,379 new files + 78 in modified files |

---

## 2. Per-File Statistics

### src/ (35 files, incl. Extraction.v)

| # | File | Qed | Adm | Lines | Topic |
|---|------|-----|-----|-------|-------|
| 1 | Archimedean_ERR.v | 14 | 0 | 186 | Archimedean property of Q |
| 2 | CauchyReal.v | 19 | 0 | 409 | Cauchy sequence reals |
| 3 | Completeness.v | 24 | 0 | 523 | Completeness (least upper bound) |
| 4 | Countability_Q.v | 17 | 0 | 530 | Q is countable |
| 5 | DiagonalArgument_ERR.v | 41 | 1 | 975 | Cantor diagonal (base-3) |
| 6 | Differentiation.v | 18 | 0 | 734 | Uniform differentiability |
| 7 | EVT_ERR.v | 31 | 3 | 1019 | Extreme Value Theorem |
| 8 | EVT_idx.v | 26 | 0 | 709 | EVT (index-based, clean) |
| 9 | FixedPoint.v | 20 | 0 | 737 | Banach contraction mapping |
| 10 | GradientDescent.v | 18 | 0 | 525 | Gradient descent convergence |
| 11 | HeineBorel_ERR.v | 22 | 2 | 642 | Heine-Borel compactness |
| 12 | **IntensionalIdentity.v** | **11** | **0** | **282** | **P3: intensional ≠ extensional** |
| 13 | IVT_CauchyReal.v | 8 | 0 | 382 | IVT lifted to CauchyReal |
| 14 | IVT_ERR.v | 23 | 0 | 424 | Intermediate Value Theorem |
| 15 | IntegralApplications.v | 19 | 0 | 735 | FTC, integration by parts |
| 16 | MeanValueTheorem.v | 18 | 0 | 701 | Rolle, MVT, monotonicity |
| 17 | Measure.v | 15 | 0 | 429 | Outer measure, Lebesgue |
| 18 | MonotoneConvergence.v | 15 | 0 | 509 | Monotone convergence |
| 19 | PInterval_CROWN.v | 25 | 0 | 558 | Interval arithmetic + CROWN |
| 20 | PowerSeries.v | 19 | 0 | 491 | Power series, radius of conv. |
| 21 | Probability.v | 12 | 0 | 355 | Discrete probability |
| 22 | **ProcessGeneral.v** | **16** | **0** | **364** | **General process theory** |
| 23 | RealField.v | 17 | 0 | 504 | Field operations on CauchyQ |
| 24 | RiemannIntegration.v | 18 | 0 | 601 | Riemann integral |
| 25 | **Roles.v** | **30** | **0** | **733** | **E/R/R roles, status, deps** |
| 26 | RoundingSafety.v | 13 | 0 | 345 | IEEE 754 rounding bounds |
| 27 | SchroederBernstein_ERR.v | 14 | 0 | 397 | Schroeder-Bernstein theorem |
| 28 | SeriesConvergence.v | 22 | 0 | 634 | Series, geometric sums |
| 29 | ShrinkingIntervals_ERR.v | 167 | 0 | 3631 | Uncountability (intervals) |
| 30 | SoftmaxProbability.v | 14 | 0 | 353 | Softmax verification |
| 31 | TaylorSeries.v | 18 | 0 | 1234 | Taylor polynomials |
| 32 | TernaryRepresentation_ERR.v | 52 | 2 | 992 | Ternary/Cantor set |
| 33 | TheoryOfSystems_Core_ERR.v | 34 | 2 | 1896 | ToS core: Levels, Systems |
| 34 | UniformConvergence.v | 20 | 0 | 691 | Uniform convergence |

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
  HeineBorel_ERR     Measure            PInterval_CROWN
  Probability        RoundingSafety     SchroederBernstein
  ShrinkingIntervals SoftmaxProbability TernaryRepresentation
  TheoryOfSystems_Core_ERR

LAYER 0.5 — Depends on Core_ERR only:
  Roles                <-- Core_ERR (E/R/R roles, status, dependencies)
  IntensionalIdentity  <-- Core_ERR (P3: intensional ≠ extensional)

LAYER 0.5b — Depends on Core_ERR + CauchyReal:
  ProcessGeneral       <-- Core_ERR, CauchyReal (general process theory)

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

**ToS foundations chain (Phase 2, NEW):**
```
Core_ERR -> Roles                (E/R/R roles, status, dependencies, paradox diagnosis)
Core_ERR -> IntensionalIdentity  (P3: intensional ≠ extensional identity)
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
RoundingSafety (standalone)
SoftmaxProbability (standalone)
```

**Architecture_of_Reasoning/** — all 6 files are standalone (no cross-imports).

---

## 4. Admitted Inventory (10 total, down from 12)

### Closed in this update

| # | File | Lemma | How closed |
|---|------|-------|------------|
| ~~A1~~ | EVT_ERR.v | `f_argmax_eq_max_list` | Added `max_list_elem_le`, `max_list_le_bound` helpers |
| ~~A5~~ | Core_ERR.v | `update_increases_size` | Added `filter_ext_in_nat`, `NoDup_seq_local` helpers |

### Category A: Provable with effort (4 Admitted, was 6)

These are technically closable with additional helper lemmas or minor hypothesis adjustments.

| # | File | Lemma | Issue | Effort |
|---|------|-------|-------|--------|
| A2 | EVT_ERR.v:680 | `max_on_grid_attained` | Needs `Proper f (Qeq ==> Qeq)` hypothesis | Low (add hyp + rewrite) |
| A3 | EVT_ERR.v:959 | `EVT_complete` | `In (grid_point 0)` needs Leibniz-eq helper | Low (grid_point_0_eq lemma) |
| A4 | TernaryRep.v:565 | `extracted_equals_floor` | Base-3 digit/Qfloor consistency | High (~15 aux lemmas) |
| A6 | TernaryRep.v:960 | `diagonal_Q_separation` | Depends on `extracted_equals_floor` | Blocked by A4 |

### Category B: Fundamentally unprovable over Q (4 Admitted)

These are mathematically false or unprovable in constructive Q without completeness. Kept as documentation alongside their provable alternatives.

| # | File | Lemma | Why unprovable | Alternative |
|---|------|-------|----------------|-------------|
| B1 | DiagArg.v:833 | `diagonal_differs_at_n` | Qfloor discontinuity breaks digit stability | ShrinkingIntervals_ERR.v (0 Admitted) |
| B2 | EVT_ERR.v:546 | `argmax_process_is_Cauchy` | False without uniqueness/isolation of max | EVT_idx.v (0 Admitted) |
| B3 | HeineBorel.v:560 | `Heine_Borel` | FALSE over Q (documented counterexample) | Heine_Borel_uniform (proved, with Lebesgue number) |
| B4 | HeineBorel.v:612 | `continuous_on_uniformly_continuous` | Requires classical Heine-Borel | Assume uniform continuity directly |

**Design rationale:** These `_ERR` files intentionally contain Admitted to document where classical proofs break over Q. Each has a companion file or theorem that proves the constructive version cleanly.

### Category C: Requires universe polymorphism (2 Admitted)

| # | File | Lemma | Issue |
|---|------|-------|-------|
| C1 | Core_ERR.v:1273 | `no_self_level_elements` | Universe constraint on `crit_domain` |
| C2 | Core_ERR.v:1304 | `cantor_no_system_of_all_L2_systems` | Same — universe-level proof |

These encode Cantor's paradox for the Theory of Systems hierarchy. The type-theoretic blocking IS working (Coq rejects the ill-formed definitions), but formalizing the proof requires explicit universe annotations (`Set Universe Polymorphism`).

### Admitted Summary

| Category | Count | Closable? |
|----------|-------|-----------|
| A: Provable with effort | 4 | Yes (A4+A6 close together = -2) |
| B: False/unprovable over Q | 4 | No (by design, documented) |
| C: Universe polymorphism | 2 | Possible with Coq universe features |
| **Total** | **10** | **4 closable, 6 permanent** |

---

## 5. Key Definitions

### Core mathematical infrastructure

| Definition | File | Type | Description |
|-----------|------|------|-------------|
| `CauchyQ` | CauchyReal.v | Record | Cauchy sequence over Q with convergence proof |
| `cauchy_equiv` | CauchyReal.v | Relation | Equivalence: two sequences have same limit |
| `real_add/mul/neg` | CauchyReal.v | Functions | Arithmetic on Cauchy reals |
| `has_limit` | Completeness.v | Prop | Sequence converges to a limit |
| `is_bounded` | Completeness.v | Prop | Sequence bounded above/below |
| `partial_sum` | SeriesConvergence.v | Fixpoint | `S(0)=a(0); S(n+1)=S(n)+a(n+1)` |
| `udiff_on` | Differentiation.v | Definition | Uniform differentiability on [a,b] |
| `riemann_sum` | RiemannIntegration.v | Definition | Riemann sum over uniform partition |
| `riemann_integrable` | RiemannIntegration.v | Definition | Limit of Riemann sums exists |
| `iterate` | FixedPoint.v | Fixpoint | `f^n(x)` iterated application |
| `is_contraction` | FixedPoint.v | Definition | Lipschitz with factor 0 <= c < 1 |

### Interval arithmetic / NN verification

| Definition | File | Type | Description |
|-----------|------|------|-------------|
| `PInterval` | PInterval_CROWN.v | Record | Interval [lo, hi] with lo <= hi |
| `pi_add/mul/relu` | PInterval_CROWN.v | Functions | Interval arithmetic operations |
| `crown_bounds` | PInterval_CROWN.v | Theorem | CROWN linear relaxation soundness |
| `in_interval` | RoundingSafety.v | Definition | `lo <= x /\ x <= hi` |
| `ibp_safe` | RoundingSafety.v | Definition | `lo - margin <= x <= hi + margin` |

### Theory of Systems (Core + Phase 2)

| Definition | File | Type | Description |
|-----------|------|------|-------------|
| `Level` | Core_ERR.v | Inductive | L1, L2, L3 hierarchy levels |
| `System` | Core_ERR.v | Record | System at level L |
| `Criterion` | Core_ERR.v | Record | Distinguishing criterion with domain/level |
| `Element` | Core_ERR.v | Inductive | Element types within systems |
| `RoleSpec` | Core_ERR.v | Record | Role specification (structural role) |
| `RoleInstance` | Core_ERR.v | Record | Concrete role assignment |
| `Process` | Core_ERR.v | Record | Temporal process with steps |
| `StructuredSystem` | Core_ERR.v | Record | System with position-based structure |
| `InsertionValid` | Core_ERR.v | Definition | Validity predicate for element insertion |
| `RoleAssignment` | Roles.v | Record | Element-to-role binding with level proof |
| `ERR_Category` | Roles.v | Inductive | Cat_Element / Cat_Role / Cat_Rule |
| `MathStatus` | Roles.v | Inductive | Min / Max / Saddle / Regular / Undefined |
| `EpistemicStatus` | Roles.v | Inductive | Known / Unknown / Indeterminate |
| `Dependency` | Roles.v | Record | Directed dep with DepDirection |
| `ERR_WellFormed_Full` | Roles.v | Record | 4-condition well-formedness (ERR §7) |
| `circular_status` | Roles.v | Definition | `s = negb s` — paradox pattern |
| `CriterionOver` | IntensionalIdentity.v | Record | Domain-fixed criterion for P3 |
| `ext_equiv` | IntensionalIdentity.v | Definition | Extensional equivalence (same elements) |
| `GenProcess` | ProcessGeneral.v | Definition | `nat -> A` — universal process type |
| `process_equiv` | ProcessGeneral.v | Definition | Pointwise equivalence of processes |
| `is_cauchy_gen` | ProcessGeneral.v | Definition | Cauchy condition on Q-valued processes |

### Architecture of Reasoning

| Definition | File | Type | Description |
|-----------|------|------|-------------|
| `FallacyType` | CompleteFallacyTaxonomy.v | Inductive | 156 fallacy type constructors |
| `DomainViolation` | DomainViolations_Complete.v | Inductive | D1-D6 violation types |
| `ParadoxType` | ParadoxDissolution.v | Inductive | 46 paradox type constructors |
| `ERR_Structure` | Architecture_of_Reasoning.v | Record | Element/Role/Rule triple |
| `detect_fallacy` | AI_FallacyDetector.v | Fixpoint | Pattern-match fallacy detector |

---

## 6. Gap Analysis: ToS-Lang Coverage

### What EXISTS in the formalization

| ToS Concept | Status | Where |
|-------------|--------|-------|
| Levels (L1-L3) | FULL | Core_ERR.v: `Level`, `level_lt`, irrefl/trans/asymm |
| Systems | FULL | Core_ERR.v: `System`, `StructuredSystem` |
| Criteria | FULL | Core_ERR.v: `Criterion`, `crit_domain`, `crit_level_valid` |
| Elements | FULL | Core_ERR.v: `Element`, `ElemType` |
| Roles (L4) | **FULL** | Roles.v: `RoleAssignment`, `ERR_Category`, 4-cond well-formedness (30 Qed) |
| Status (derived) | **FULL** | Roles.v: `MathStatus`, `EpistemicStatus`, `StatusAssignment` |
| Dependencies | **FULL** | Roles.v: `Dependency`, `deps_acyclic`, `strongly_acyclic` |
| Paradox diagnosis | **FULL** | Roles.v: `circular_dep_is_paradox`, Russell/Liar examples |
| P3 (Intensional identity) | **FULL** | IntensionalIdentity.v: separation theorem (11 Qed) |
| Process (P4, general) | **FULL** | ProcessGeneral.v: `GenProcess`, Cauchy bridge (16 Qed) |
| E/R/R Framework | FULL | Architecture_of_Reasoning.v: `ERR_Structure` |
| Domains D1-D6 | FULL | DomainViolations_Complete.v: all 6 violation types |
| Fallacy taxonomy | FULL | CompleteFallacyTaxonomy.v: 156 types |
| Paradox dissolution | FULL | ParadoxDissolution.v: 46 types |
| Cantor's paradox | FULL | Core_ERR.v: `no_self_containing_system` (Qed) |
| L5-Resolution | PARTIAL | Only `level_lt_dec` on L1/L2/L3; no general comparator |

### What is MISSING

| Gap | Priority | Description | Estimated Effort |
|-----|----------|-------------|------------------|
| ~~**Roles.v**~~ | ~~HIGH~~ | **DONE** — 30 Qed, 733 lines | ✓ |
| ~~**IntensionalIdentity.v**~~ | ~~HIGH~~ | **DONE** — 11 Qed, 282 lines | ✓ |
| ~~**ProcessGeneral.v**~~ | ~~MEDIUM~~ | **DONE** — 16 Qed, 364 lines | ✓ |
| **L5Resolution.v** | MEDIUM | General L5 resolution for arbitrary level count | ~200 lines, 10-12 Qed |
| **LinearAlgebra.v** | LOW | Vectors, matrices (needed for multi-dim NN verification) | ~500+ lines, 25+ Qed |
| **SystemMorphisms.v** | LOW | Structure-preserving maps between systems | ~250 lines, 12-15 Qed |
| **WellFormedness checker** | LOW | Decision procedure for valid system construction | ~200 lines |
| ~~**OCaml extraction**~~ | ~~LOW~~ | **DONE** — `Extraction.v` + 29 files in `extraction/` | ✓ |

### Observations

1. **The calculus chain is remarkably complete** (B16-B22): Differentiation through Taylor series and fixed points, all 0 Admitted, 0 axioms. This exceeds what most Coq formalizations achieve over Q.

2. **The _ERR files are pedagogical by design**: They show WHERE classical proofs break over Q, with Admitted entries that are either impossible (Category B) or laborious (Category A). Each has a clean companion file.

3. **Architecture_of_Reasoning is fully proven** but largely standalone — no connection to the calculus chain. This is appropriate since it formalizes taxonomy/classification rather than theorems.

4. **ShrinkingIntervals_ERR.v is the workhorse** at 167 Qed / 3631 lines — it proves uncountability of [0,1] via nested interval bisection, completely avoiding the digit-extraction issues in TernaryRepresentation_ERR.v and DiagonalArgument_ERR.v.

5. **Phase 2 closed the ToS-specific gap**: Roles.v (30 Qed), IntensionalIdentity.v (11 Qed), and ProcessGeneral.v (16 Qed) formalize the three highest-priority ToS concepts. The repo now has strong coverage of Levels, Systems, Criteria, Elements, Roles, Status, Dependencies, Paradoxes, Identity (P3), and Processes.

---

## 7. Recommendations

### Priority 1: Close remaining Category A Admitted (achievable, -2 to -4 Admitted)

- **A2 + A3** (EVT_ERR): Add `Proper` hypothesis for Qeq-respecting functions, add `grid_point_0_eq` lemma. Estimated: 1 session.
- **A4 + A6** (TernaryRep): Close `extracted_equals_floor` with 15 Qfloor/mod helpers. Estimated: 2-3 sessions. Alternatively, this can be deprioritized since ShrinkingIntervals_ERR.v already has the 0-Admitted version.

### Priority 2: Remaining ToS-specific files

- **L5Resolution.v**: General L5 resolution for arbitrary level hierarchies.
- **SystemMorphisms.v**: Structure-preserving maps between systems.

### Priority 3: Infrastructure

- ~~**OCaml extraction**~~: **DONE** — `src/Extraction.v` + 29 files in `extraction/`.
- ~~**Makefile / _CoqProject**~~: **DONE** — `_CoqProject` (41 files) + `CoqMakefile`.

---

## 8. Build Information

### Compilation command (per file)

```bash
cd /c/Users/aleks/Desktop/RegulusAI/_tos_coq_clone
ROCQLIB="C:\\Coq\\Rocq-Platform~9.0~2025.08\\lib\\coq" \
  "C:\\Coq\\Rocq-Platform~9.0~2025.08\\bin\\coqc.exe" \
  -Q src ToS -Q Architecture_of_Reasoning ToS_Arch \
  src/<FILE>.v
```

### Known compiler quirks (Rocq 9.0.1)

- `lra` cannot handle `Qge` — convert to `Qle` first
- `simpl` can over-unfold Fixpoints — use `cbv beta` instead
- `ring` fails on Q division — use `field; lra`
- `nia` regression on nonlinear Z*positive — use `Z.mul_le_mono_nonneg + lia`
- `set ... in *` lambda matching unreliable — set from goal directly
- `qabs_rw` only works in `Qlt` context, not `Qle`

---

### Build system

`_CoqProject` defines the full dependency graph (41 files). Compile with:

```bash
make -f CoqMakefile    # or compile individual files via coqc command above
```

---

*Generated by audit protocol from CLAUDE_MD_AUDIT_AND_BUILD.md*
*Phase 2 (ToS-Lang foundations) complete: +3 files, +63 Qed, -2 Admitted.*
