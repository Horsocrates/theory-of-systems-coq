# src/ — Core Coq Formalization

**~262 files | ~5990 Qed | 0 Admitted** (including gauge/, navier_stokes/, and subdirectories)

This directory contains the core formalization of the Theory of Systems in Coq/Rocq 9.0.

---

## Dependency Layers

Files must be compiled in dependency order. The `_CoqProject` in the root directory specifies this order.

```
Layer 0: Standalone (no ToS imports)
  |
  v
Layer 0.5: Depends on Core_ERR only
  |
  v
Layer 0.5b-h: Cross-dependencies between foundation files
  |
  v
Layers 1-11: Analysis chain (CauchyReal -> ... -> FixedPoint)
  |
  v
Phase A-D: ToS-Lang type theory and compiler
  |
  v
stdlib/: Verified data structures (depends on foundation files)
```

---

## File Guide

### ToS Core + Foundations

| File | Qed | Description |
|------|-----|-------------|
| **TheoryOfSystems_Core_ERR.v** | 34 | Laws L1-L5, `System`, `Criterion`, `Generator`, paradox blocking |
| **Roles.v** | 30 | E/R/R categories, `MathStatus`, `EpistemicStatus`, `Dependency`, paradox diagnosis |
| **L5Resolution.v** | 18 | `DecTotalOrder` typeclass, generalized L5 tie-breaking, nat/Q/Z instances |
| **SystemMorphism.v** | 17 | Structure-preserving maps, isomorphisms, composition |
| **InfoLayer.v** | 17 | Information flow between levels, channel capacity, composition |
| **IntensionalIdentity.v** | 11 | P3: extensional equivalence != intensional identity |
| **ProcessGeneral.v** | 16 | `GenProcess A := nat -> A`, Cauchy bridge, prefix, process_map |
| **UniversePolymorphism.v** | 24 | Universe hierarchy for ToS-Lang |
| **ErasureTheory.v** | 16 | Proof-irrelevance and computational erasure |
| **Extraction.v** | - | OCaml extraction directives |

### ToS-Lang: Type Theory (Phase A, 134 Qed)

| File | Qed | Description |
|------|-----|-------------|
| **DependentSystems.v** | 25 | Pi-systems (dependent functions), Sigma-systems (dependent pairs) |
| **InductiveSystems.v** | 26 | Inductive types, `FinitelyGenerated`, `BTree`, `nat` as system |
| **CoinductiveSystems.v** | 16 | Coinductive types, `Observable`, streams as P4 processes |
| **ConstitutionChecking.v** | 16 | `DecidableConstitution`, `BoolConstitution`, decidable membership |
| **PhaseA_Examples.v** | 11 | Integration examples across Phase A modules |

### ToS-Lang: Typing Rules (Phase B, 99 Qed)

| File | Qed | Description |
|------|-----|-------------|
| **Judgments.v** | 23 | `CtxEntry`, `Context`, `HasType`, `HasElem`, `SystemEquiv` |
| **FormationRules.v** | 18 | `sys_form`, `pi_form`, `sigma_form`, `layer_form`, `l5_res_rule` |
| **Conversion.v** | 16 | `P3_convertible`, beta/eta for Pi/Sigma, `l5_resolve_deterministic` |
| **Subtyping.v** | 20 | `is_embedding`, `is_subsystem`, `pi_contravariant`, `sigma_covariant` |
| **Soundness.v** | 22 | **`typing_implies_safe`** — the key typing soundness theorem |

### ToS-Lang: Operational Semantics (Phase C, 124 Qed)

| File | Qed | Description |
|------|-----|-------------|
| **Expressions.v** | 20 | `Expr` (12 constructors), de Bruijn substitution, `expr_eq_dec` |
| **Reduction.v** | 26 | `step` (15 rules), `multi_step`, `eval_fuel`, `step_deterministic` |
| **Typing_Expr.v** | 17 | `expr_has_type` (10 rules), canonical forms, weakening, substitution |
| **SubjectReduction.v** | 18 | **Subject reduction** — stepping preserves types |
| **Progress.v** | 30 | **Progress** — well-typed closed terms step or are values |
| **TypeSafety.v** | 13 | **Type safety** — well-typed programs don't get stuck |

### ToS-Lang: Verified Compiler (Phase D, 64 Qed)

| File | Qed | Description |
|------|-----|-------------|
| **TypeChecker.v** | 26 | `typecheck`, `typecheck_ann`, **`typecheck_sound`** |
| **Evaluator.v** | 20 | `safe_eval`, `classify_eval`, **`verified_pipeline`** |
| **AIInterface.v** | 10 | **`ai_generation_safe`** — AI code that typechecks is safe |
| **ToS_Lang_Extraction.v** | 8 | OCaml extraction of compiler |

### Set Theory & Topology

| File | Qed | Description |
|------|-----|-------------|
| **ShrinkingIntervals_ERR.v** | 167 | Non-surjectivity N -> [0,1] n Q (largest file) |
| **Countability_Q.v** | 17 | Q =~ N via Calkin-Wilf tree |
| **DiagonalArgument_ERR.v** | 41 | Alternative diagonal proof |
| **TernaryRepresentation_ERR.v** | 52 | Ternary digit representation |
| **SchroederBernstein_ERR.v** | 14 | Injection theorem |
| **HeineBorel_ERR.v** | 25 | Compactness, Lipschitz uniform continuity |

### Process Continuum Hypothesis (Phase 1, 86 Qed)

| File | Qed | Description |
|------|-----|-------------|
| **ProcessTypes.v** | 25 | `BinProcess`, `BinCollection`, `is_enumerable`, trees, paths |
| **ProcessDiagonal.v** | 20 | Constructive Cantor diagonal for bool, `binary_processes_not_enumerable` |
| **ProcessContinuumHypothesis.v** | 41 | Cantor-Bendixson, **`process_continuum_hypothesis`** |

### Category of Systems (Phase 2, 105 Qed)

| File | Qed | Description |
|------|-----|-------------|
| **SystemCategory.v** | 29 | `SystemCat L : Category` instance, iso/mono/epi bridges |
| **LevelFunctors.v** | 27 | `embed_functor`, restricted forget, `is_forgettable`, faithfulness |
| **LevelAdjunction.v** | 25 | Hom-set bijection, unit/counit, triangle identities |
| **ERR_Categorical.v** | 24 | E/R/R functorial decomposition, P3↔iso separation |

### Analysis: Gap Closures (analysis/, 102 Qed)

| File | Qed | Description |
|------|-----|-------------|
| **BolzanoWeierstrass.v** | 26 | Bounded sequence → Cauchy subsequence via bisection |
| **FTC.v** | 28 | Lipschitz theory, u-substitution, FTC extensions |
| **HeineBorelComplete.v** | 28 | Total boundedness, eps-nets, uniform continuity alternatives |
| **ImplicitFunction.v** | 20 | Newton iteration as Banach contraction |

### Analysis: Foundations

| File | Qed | Description |
|------|-----|-------------|
| **Archimedean_ERR.v** | 14 | Archimedean property of Q |
| **CauchyReal.v** | 19 | Cauchy reals: constructive completion of Q |
| **RealField.v** | 17 | Ordered field structure on CauchySeq |
| **Completeness.v** | 24 | Metric completeness: NIP, sup, diagonal |

### Analysis: Calculus Chain (Layers 3-11)

| File | Qed | Key Theorem |
|------|-----|-------------|
| **MonotoneConvergence.v** | 15 | Bounded monotone sequences are Cauchy |
| **SeriesConvergence.v** | 22 | Geometric series, comparison test |
| **PowerSeries.v** | 19 | Ratio test, exp(x) convergence |
| **Differentiation.v** | 18 | Division-free derivatives, power rule |
| **MeanValueTheorem.v** | 18 | Grid MVT, monotonicity, Lipschitz |
| **RiemannIntegration.v** | 18 | Riemann sums, **FTC** |
| **IntegralApplications.v** | 19 | Product rule, **integration by parts** |
| **TaylorSeries.v** | 18 | Taylor remainder, convexity, sandwich |
| **UniformConvergence.v** | 20 | Limit exchange, **Dini's theorem** |
| **FixedPoint.v** | 20 | **Banach contraction mapping**, perturbation |
| **ReasoningConvergence.v** | 19 | Reasoning pipeline as contraction |

### Applied Mathematics

| File | Qed | Description |
|------|-----|-------------|
| **IVT_ERR.v** | 23 | Epsilon-IVT (constructive) |
| **IVT_CauchyReal.v** | 8 | Full IVT on Cauchy reals |
| **EVT_idx.v** | 26 | Epsilon-EVT, L5-compliant |
| **PInterval_CROWN.v** | 25 | CROWN NN verification soundness |
| **GradientDescent.v** | 18 | GD convergence for quadratic loss |
| **LinearAlgebra.v** | 20 | QVec, QMat, dot product |
| **Probability.v** | 12 | Bayes' theorem + fallacy detection |
| **SoftmaxProbability.v** | 14 | Softmax probability soundness |
| **Measure.v** | 15 | Constructive measure & integration |
| **RoundingSafety.v** | 13 | IEEE 754 rounding within intervals |

### Verified D1-D6 Pipeline

| File | Qed | Description |
|------|-----|-------------|
| **DomainTypes.v** | - | Domain type definitions |
| **DomainValidation.v** | - | Domain validation logic |
| **PipelineSemantics.v** | - | Pipeline operational semantics |
| **PipelineExtraction.v** | - | OCaml extraction |

---

## Building

```bash
# From repository root:
coq_makefile -f _CoqProject -o Makefile
make

# Single file (Windows, Rocq 9.0.1):
ROCQLIB="C:\Coq\Rocq-Platform~9.0~2025.08\lib\coq" \
  coqc -Q src ToS -Q Architecture_of_Reasoning ToS_Arch src/<FILE>.v
```
