# CLAUDE.md — Theory of Systems Coq Project

## Stats (as of 2026-03-20)
- **Qed:** 14517
- **Admitted:** 0
- **Files:** 910
- **Compiler:** Rocq 9.0.1 (Coq rebrand)
- **Build:** `make` (uses `_CoqProject`)

## Build Commands

```bash
# Full build
coq_makefile -f _CoqProject -o Makefile && make

# Single file (with correct paths)
ROCQLIB="C:\\Coq\\Rocq-Platform~9.0~2025.08\\lib\\coq" \
  "C:\\Coq\\Rocq-Platform~9.0~2025.08\\bin\\coqc.exe" \
  -Q src ToS -Q Architecture_of_Reasoning ToS_Arch src/<FILE>.v

# Verify counts
grep -rc 'Qed\.' src/ Architecture_of_Reasoning/ | awk -F: '{s+=$2}END{print s}'
grep -rc 'Admitted\.' src/ Architecture_of_Reasoning/ | awk -F: '{s+=$2}END{print s}'

# Regenerate docs
bash generate_docs.sh
```

## Conventions

1. **Every lemma: Qed** — ZERO new Admitted
2. If unprovable: **simplify statement**, don't Admit
3. Standard E/R/R header on every file:
   ```coq
   (** * FileName.v — Description as ToS System
       Elements: ...
       Roles:    ...
       Rules:    ...
       Status:   ...
       STATUS: N Qed, 0 Admitted, 0 axioms
       Author: Horsocrates | Date: March 2026
   *)
   ```
4. Stdlib files go in `src/stdlib/`
5. After creating file: compile, count Qed, update `_CoqProject`
6. Use `From ToS Require Import ...` (not bare `Require Import`)

## Rocq 9.0.1 Quirks

### Q arithmetic
- `lra` CANNOT handle `Qge` — convert to `Qle` first
- `lra` CANNOT handle `Qeq` (`==`) for rewriting inside products — use `Qmult_comp` + `transitivity`
- `lra` CANNOT reason about `Qabs` terms — use explicit `Qle_trans` chains
- `ring` fails on Q division — use `field; lra`
- `replace ... by ring` may fail for `Qeq` — use `assert Heq ... by ring. rewrite Heq.`

### Nat arithmetic
- `Nat.div_exact` deprecated — use `Nat.div_mod` + rewrite
- `Nat.gcd_1_l`, `Nat.gcd_1_r` don't exist — use `simpl. reflexivity.` or `rewrite Nat.gcd_comm. simpl. reflexivity.`
- `Nat.mod_add` deprecated (now `Div0.mod_add`), expects `(a + b * c) mod c` form
- `Nat.mod_same` deprecated (now `Div0.mod_same`)
- `Nat.mod_small : a < b -> a mod b = a` — direction is `a mod b = a`, NOT `a = a mod b`
- `Nat.divide` uses `exists k, n = k * d` (not `n = d * k`) — bridge with `rewrite Nat.mul_comm`
- `0 mod (S m)` doesn't compute by `reflexivity` for abstract `m` — use `Nat.mod_small`
- `nia` regression on nonlinear Z*positive — use `Z.mul_le_mono_nonneg + lia`

### General
- `ring` may fail for Z — use `Z.mul_comm/Z.mul_assoc/lia`
- `tauto` may fail — try `intuition`
- `Qed` vs `Defined`: use `Defined` for anything needing `Eval compute`
- `cbv beta` instead of `simpl` to avoid unfolding Fixpoints
- `set ... in *` lambda matching unreliable — set from GOAL directly
- `cbv zeta in HN` required after `set ... in *` to eliminate `let` wrappers

## Import Pattern

```coq
(* Always use From ToS *)
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import stdlib.TMap.
From ToS_Arch Require Import Architecture_of_Reasoning.

(* If import fails in standalone file: replicate needed definitions with comment *)
(* Replicated from Core_ERR.v to avoid circular dependency *)
```

## Key Definitions (for imports)

| Definition | File |
|-----------|------|
| `Level`, `System`, `Criterion`, `ElemOf` | `TheoryOfSystems_Core_ERR.v` |
| `RoleAssignment`, `ERR_WellFormed` | `Roles.v` |
| `CriterionOver`, `ext_equiv`, `int_equiv` | `IntensionalIdentity.v` |
| `GenProcess`, `observe` | `ProcessGeneral.v` |
| `DecTotalOrder`, `l5_resolve_gen` | `L5Resolution.v` |
| `SystemMorphism`, `compose_morphism` | `SystemMorphism.v` |
| `PiSystem`, `SigmaElem` | `DependentSystems.v` |
| `FinitelyGenerated` | `InductiveSystems.v` |
| `Observable` | `CoinductiveSystems.v` |
| `DecidableConstitution` | `ConstitutionChecking.v` |
| `Expr`, `step`, `eval_fuel` | `Expressions.v`, `Reduction.v` |
| `typecheck_ann`, `safe_eval` | `TypeChecker.v`, `Evaluator.v` |
| `is_contraction`, `banach_convergence` | `FixedPoint.v` |
| `BinProcess`, `BinCollection`, `is_enumerable` | `ProcessTypes.v` |
| `diagonal`, `binary_processes_not_enumerable` | `ProcessDiagonal.v` |
| `process_continuum_hypothesis` | `ProcessContinuumHypothesis.v` |
| `SystemCat`, `empty_system`, `unit_system` | `SystemCategory.v` |
| `embed_obj`, `EmbedFunctor`, `is_forgettable`, `forget_obj` | `LevelFunctors.v` |
| `adj_forward`, `adj_backward`, `level_adjunction` | `LevelAdjunction.v` |
| `ElementsFunctor`, `P3_separation_categorical` | `ERR_Categorical.v` |
| `Distinction`, `distinction_of`, `positive`, `negative` | `foundation/Distinction.v` |
| `NestedDistinction`, `sm_distinction`, `gauge_generators` | `foundation/NestedDistinction.v` |
| `n_cp_phases`, `has_cp_violation`, `min_generations_for_cp` | `foundation/GenerationsFromL4.v` |
| `vacuum_energy`, `cc_process` | `foundation/VacuumNecessity.v` |
| `distinction_sharpness`, `coherence` | `foundation/DistinctionProcess.v` |
| `divides`, `is_prime`, `sieve` | `stdlib/Primes.v` |
| `gcd`, `coprime`, `lcm` | `stdlib/GCD.v` |
| `Graph`, `has_node`, `has_edge` | `stdlib/Graph.v` |
| `DFA`, `dfa_accepts` | `stdlib/Automata.v` |

## File Organization

```
src/                    — core files (75 .v files)
src/foundation/        — formal foundation (18 .v files): Distinction → SM
src/stdlib/             — standard library (53 .v files)
Architecture_of_Reasoning/ — fallacy/paradox taxonomy (6 .v files)
tos_lang/               — OCaml extraction + parser + CLI
extraction/             — extracted OCaml modules
examples/               — .tos example files
docs/                   — auto-generated documentation
```

## For Agent Teams

- Each teammate owns their files — no overlap
- If you need a definition from another's file: define locally
  with `(* Will be replaced by import from X.v *)`
- Report: file, Qed count, key theorems
- Compile individually first, then full `make`
- After batch: run `bash generate_docs.sh` to update docs

---

## Local Invariants (per key file)

### ToS_Axioms.v
INVARIANTS:
- Sole source of `classic` (re-exported from Distinction.v) and `L4_witness`
- Exactly 2 core axioms. Do NOT add new axioms without discussion.
- All files that need LEM or constructive witnesses import from here.

STYLE:
- Axiom declarations only. No proofs in this file.

DO NOT:
- Add axioms (even "harmless" ones like Extensionality, FunExt)
- Remove or rename existing axioms (breaks 40+ downstream files)

### TheoryOfSystems_Core_ERR.v
INVARIANTS:
- `Level` inductive type: L1, LS. Do not change constructors.
- `level_lt` fixpoint must remain decidable and well-founded.
- `P1_no_self_membership` must compile (tests hierarchy correctness).
- `russell_paradox_blocked` must compile.

STYLE:
- Core definitions first, then properties, then E/R/R record.

DO NOT:
- Add universe polymorphism without testing all downstream
- Change `Level` or `System` types (breaks 53+ files)
- Add Admitted (previously had 3, all closed by weakening statements)

### ShrinkingIntervals_ERR.v
INVARIANTS:
- Only `classic` axiom (via ToS_Axioms). No other axioms.
- Sync invariant: `2 * delta < w / 3` at every trisection step.
- Exported names (unit_interval_uncountable_trisect_v2) used by PCH — do not rename.

STYLE:
- Long file (~3600 lines). Work in sections. `unfold`-heavy proofs.

DO NOT:
- Switch to digit-based diagonal (digit stability issue over Q is fundamental)
- Rename exported theorems (ProcessContinuumHypothesis.v depends on them)
- Add axioms beyond classic

### EVT_idx.v
INVARIANTS:
- Argmax by INDEX (nat), not by value (Q). This is a deliberate design choice.
- L5-Resolution (leftmost maximum) provides deterministic tie-breaking.
- `grid_point` and `grid_list` are bottleneck definitions (used by 5+ files).

STYLE:
- Grid refinement proofs use `vm_compute. reflexivity.` for concrete cases.
- Lipschitz bound controls error between grids.

DO NOT:
- Switch to value-based argmax (Qeq vs Leibniz equality makes proofs impossible)
- Change grid_point formula (downstream files depend on exact definition)

### IVT_CauchyReal.v
INVARIANTS:
- Epsilon-IVT formulation: `forall eps > 0, exists x: |f(x)| < eps`
- Cannot prove exact zero (impossible over Q) — this is fundamental, not a limitation.

STYLE:
- Bisection with Lipschitz error control.

DO NOT:
- Try to prove `f(x) = 0` (impossible over Q without R completeness)
- Remove Lipschitz hypothesis (needed for error bound)

### CauchyReal.v
INVARIANTS:
- `RealProcess := nat -> Q` — this IS the definition of real numbers in ToS.
- Do NOT import Coq's `Reals` library. Ever.
- Arithmetic operations preserve Cauchy property.

STYLE:
- All real operations defined pointwise on processes.

DO NOT:
- Import `From Stdlib Require Import Reals` (ontological incompatibility with P4)
- Change RealProcess type definition (breaks 333+ files via ProcessCore)

### HeineBorel_ERR.v
INVARIANTS:
- Previously had 2 Admitted (Q-limitation). Now proved with Lebesgue number assumption.
- [0,1] over Q is genuinely NOT compact — Lebesgue number hypothesis is honest, not a hack.

STYLE:
- Grid-based finite cover extraction.

DO NOT:
- Try to prove full Heine-Borel without Lebesgue number (impossible over Q)
- Spend time attempting R-completeness proof (research_level problem)

### FixedPoint.v
INVARIANTS:
- `iterate_is_cauchy` (Banach fixed-point) used by ReasoningConvergence.v — do not change signature.
- `is_contraction` definition must match: `|f(x) - f(y)| <= r * |x - y|` with `0 < r < 1`.

STYLE:
- Geometric series bound for contraction rate.

DO NOT:
- Change `is_contraction` or `iterate_is_cauchy` signatures (Regulus bridge depends on them)
- Remove `Defined` from any extraction-needed terms

---

## Context Window Guide

### Task: Add new stdlib module
LOAD: CLAUDE.md (this file), src/stdlib/TMap.v (template)
ALSO: TheoryOfSystems_Core_ERR.v (for ERR types if needed)
NOTE: Follow E/R/R header convention. All Qed, no Admitted. Update _CoqProject after.

### Task: Work on Process Physics (Phases 13A+)
LOAD: src/process/ProcessCore.v, src/process/ProcessArithmetic.v
ALSO: src/process/ProcessGeomCategory.v, src/process/ProcessGaugeCategory.v
NOTE: Process files import from process/ directory. Avoid cross-importing from stdlib/ or foundation/ (stale .vo issues). Replicate small definitions locally if needed.

### Task: Refactor Core
LOAD: TheoryOfSystems_Core_ERR.v, ToS_Axioms.v, IntensionalIdentity.v, L5Resolution.v, Roles.v
CRITICAL: Run `Print Assumptions` after EVERY change
SKIP: Everything not in core_philosophy cluster
NOTE: Core changes cascade to 53+ files. Test compilation of at least 3 downstream files.

### Task: Add new analysis theorem
LOAD: src/analysis/ directory listing, CauchyReal.v, Completeness.v
ALSO: FixedPoint.v, Differentiation.v (for tactics patterns)
NOTE: All analysis works over Q-Cauchy processes. No R. Use Lipschitz bounds for error control.

### Task: Regulus integration
LOAD: FixedPoint.v, ReasoningConvergence.v
ALSO: extraction/ directory (OCaml), tos_lang/ (parser/printer)
NOTE: Check sync_status — Coq may be ahead of Regulus Python.

### Task: Work on foundation/ files
LOAD: src/foundation/Distinction.v (has classic axiom), src/foundation/NestedDistinction.v
ALSO: ToS_Axioms.v, TheoryOfSystems_Core_ERR.v
NOTE: Foundation files build the chain Distinction -> Gauge -> SM. Read the chain before modifying.

### Task: Work on gauge/ or physics/
LOAD: src/gauge/ directory listing, src/process/ProcessCore.v
ALSO: src/process/ProcessBounds.v (has_process_mass_gap)
NOTE: Gauge files use concrete Q lattice computations. `vm_compute. reflexivity.` is the standard proof pattern.

---

## File Clusters (co-load together)

### uncountability
ShrinkingIntervals_ERR.v, Countability_Q.v, Archimedean_ERR.v, SchroederBernstein_ERR.v, ProcessContinuumHypothesis.v

### calculus_chain
CauchyReal.v -> RealField.v -> Completeness.v -> Differentiation.v -> MeanValueTheorem.v -> RiemannIntegration.v -> analysis/FTC.v -> TaylorSeries.v -> UniformConvergence.v -> FixedPoint.v

### core_philosophy
ToS_Axioms.v, TheoryOfSystems_Core_ERR.v, IntensionalIdentity.v, L5Resolution.v, Roles.v, ProcessGeneral.v, SystemMorphism.v

### type_theory
Expressions.v, Reduction.v, Typing_Expr.v, SubjectReduction.v, Progress.v, TypeSafety.v, TypeChecker.v, Evaluator.v, AIInterface.v, ErasureTheory.v

### reasoning_architecture
Architecture_of_Reasoning/ (all 6 files): CompleteFallacyTaxonomy, ParadoxDissolution, AI_FallacyDetector, DomainViolations_Complete, ERR_Fallacies

### process_physics
process/ProcessCore.v -> ProcessArithmetic.v -> ProcessBounds.v -> ProcessGeomCategory.v -> ProcessGaugeCategory.v -> ProcessGeomGaugeFunctor.v -> ProcessGGAdjProcess.v -> ProcessPhysicsSynthesis.v

### gauge_lattice
gauge/LatticeStructure.v -> GaugeField.v -> WilsonAction.v -> TransferMatrix.v -> MassGapProcess.v -> SU2Group.v -> ... -> ProcessMassGap.v

### foundation_chain
foundation/Distinction.v -> NestedDistinction.v -> GenerationsFromL4.v -> VacuumNecessity.v -> DistinctionProcess.v -> ... -> SMParticles.v

### convergence
FixedPoint.v, IteratedContraction.v, ReasoningConvergence.v, GradientDescent.v, SeriesConvergence.v, MonotoneConvergence.v

### category_systems
SystemCategory.v, LevelFunctors.v, LevelAdjunction.v, ERR_Categorical.v, process/ProcessCategory.v, process/ProcessAdjunction.v

### optimal_transport
stdlib/ProcessOptimalTransport.v, stdlib/WassersteinConvergence.v, stdlib/WassersteinRefinement.v, stdlib/ConvergenceSynthesis.v

### navier_stokes
stdlib/GridFunction.v -> FiniteDifference.v -> GalerkinSystem.v -> EnergyEstimate.v -> ProcessNS.v -> Vorticity.v -> ... -> MillenniumComplete.v -> NSComplete.v

---

## Decision Log

### 2026-01-17: Initial migration to GitHub
Created theory-of-systems-coq repo. ~240 Qed, ~10 Admitted.

### 2026-01-18: Intervals replace Diagonal for uncountability
REASON: Digit stability (Qfloor discontinuous) unresolvable over Q.
REJECTED: Fix Qfloor lemmas; switch to ternary intervals.
IMPACT: DiagonalArgument superseded. ShrinkingIntervals = primary.
REVERSIBLE: No.

### 2026-01-18: argmax by index for EVT
REASON: Qeq vs Leibniz equality — index gives reflexivity.
REJECTED: setoid_rewrite everywhere; custom Qeq-aware max.
IMPACT: EVT_idx.v: 23 Qed, 0 Admitted.
REVERSIBLE: Yes (but unnecessary).

### 2026-01: E/R/R Framework integration into Core
REASON: E/R/R is the structural triad of ToS — needs formal representation.
IMPACT: Core_ERR.v (+7 Qed). FunctionalSystem Record.

### 2026-02: Axiom refactoring to ToS_Axioms.v
REASON: Centralize classic (L3) + L4_witness in one file.
IMPACT: All files import ToS_Axioms instead of local axiom declarations.

### 2026-02: Lean formalization premature
REASON: Mathlib Axiom of Infinity ontologically incompatible with P4 (Finite Actuality).
REVERSIBLE: Yes (if Lean gets AoI-free mode).

### 2026-02: Phase 3A Process Physics
REASON: PCH naturally extends to QM — observable as process, measurement as approximation.
IMPACT: 7 new files, 160 Qed. SpectralDichotomy = key result.

### 2026-02: REGULUS_CORE.md separate from ERR_CATALOGUE.md
REASON: Domain-specific hints must not contaminate general reasoning principles.
IMPACT: Two files where there was one.

### 2026-02: Close all Admitted
REASON: 6 Admitted in Core_ERR/EVT_ERR/HeineBorel_ERR blocking project credibility.
APPROACH: Weaken statements (Core_ERR universe-level), add assumptions (HeineBorel Lebesgue number), deprecate (EVT_ERR -> EVT_idx).
IMPACT: 0 Admitted across 776 files. 13038 Qed.

### 2026-02: P4 Process Mathematics framework
REASON: All mathematics should flow through processes (nat->Q). Process = potential, not actual infinity.
IMPACT: ProcessCore.v becomes bottleneck hub (333 imports). RealProcess := nat -> Q.

### 2026-03: RG + Mass Gap + Millennium problems
REASON: Lattice gauge theory is a natural application of process-finite methods.
APPROACH: Exact Q arithmetic on small lattices. Transfer matrix eigenvalues. Continuum limit via process sequences.
IMPACT: 60+ files in gauge/, process/, stdlib/ for YM mass gap and NS regularity.

### 2026-03: Stale .vo avoidance via local replication
REASON: Cross-importing between process/ and stdlib/ causes "inconsistent assumptions" errors when .vo files are stale.
APPROACH: Replicate small definitions locally with comment `(* Replicated from X.v *)` instead of importing.
IMPACT: Reliable compilation of individual files without full `make`.

### 2026-03: Open Scope Q_scope + nat pattern matches
REASON: `Open Scope Q_scope` makes `0`, `1` etc. parsed as Q constructors in match arms.
APPROACH: Always use `O`, `S O`, `S (S O)` in pattern matches; use `%nat` on function arguments.
IMPACT: All stdlib/ files with Q computations follow this convention.

### 2026-03-20: Knowledge graph AI annotations
REASON: Enable AI agents to understand deductive structure, classical counterparts, and proof strategies.
IMPACT: annotations.json with 15 landmark + 9 bottleneck annotations. CLAUDE.md updated with invariants, clusters, context guide.

---

## Axioms (complete list)

### Core (2)
| Axiom | File | ToS Law | Purpose |
|-------|------|---------|---------|
| `classic` | foundation/Distinction.v:16 | L3 (Excluded Middle) | forall P, P \/ ~P |
| `L4_witness` | ToS_Axioms.v:86 | P4 (Finite Actuality) | ex -> sig (constructive witness) |

### Domain-specific (4)
| Axiom | File | Purpose |
|-------|------|---------|
| `ns_viscosity_axiom` | stdlib/GalerkinSystem.v | Navier-Stokes viscosity positivity |
| `ns_forcing_axiom` | stdlib/GalerkinSystem.v | NS external forcing boundedness |
| `zeta_euler_product` | stdlib/ComplexZeta.v | Euler product for zeta function |
| `zeta_log_derivative` | stdlib/LogZeta.v | Log-derivative of zeta function |

---

## Admitted — Priority List

All Admitted have been closed as of 2026-03-19. The project has **0 Admitted** across 776 files.

Previously existed (all resolved):
- HeineBorel_ERR: proved with Lebesgue number assumption
- Core_ERR (3): weakened statements to be provable within Coq's type system
- EVT_ERR: deprecated in favor of EVT_idx
