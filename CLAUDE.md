# CLAUDE.md — Theory of Systems Coq Project

## Stats (as of 2026-03-11)
- **Qed:** 4795
- **Admitted:** 6
- **Files:** 216
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
| `divides`, `is_prime`, `sieve` | `stdlib/Primes.v` |
| `gcd`, `coprime`, `lcm` | `stdlib/GCD.v` |
| `Graph`, `has_node`, `has_edge` | `stdlib/Graph.v` |
| `DFA`, `dfa_accepts` | `stdlib/Automata.v` |

## File Organization

```
src/                    — core files (75 .v files)
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
