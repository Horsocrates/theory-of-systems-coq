---
title: "Chapter 5. Type Safety as Fuel Finitization"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/15 Вычисления и граница финитизации/05 Типобезопасность как fuel-финитизация.md"
sourceBlob: 9a026966619c4bbfe61a10bf77a01f034a42e758
translated: 2026-10-20
status: draft
---

## One More Face of Finitization

After the discriminant (15.4) comes one more *positive*, decidable instrument of the same boundary: *typed evaluation*. The chain of reductions of a program is potentially infinite, and the question “will it break off?” is, in general form, a role-limit (15.3). Our system does not try to decide it—it **finitizes**: *fuel* cuts the run down to a finite depth (P4), and *type safety* guarantees that this finite run *will never get stuck unexpectedly* (only an explicitly singled-out benign stuck state is admitted). In short:

> **type safety is the finitization of a chain of reductions by fuel: the infinite folds into
> a finite run, and types keep it meaningful.**

The type-safety result itself (preservation ${}+{}$ progress) is standard; our angle is to read fuel as P4 finitization, and the whole chapter as the *positive mirror* of the discriminant.

## Expressions, Types, Step

The language is given by three things. *Expressions* are inductive terms (constants, pairs, $\lambda$, application, system constructions). *Types* are the role that an expression is *permitted* to play (the typing judgment $\Gamma\vdash e : T$). The *step* is the small-step reduction relation $e \to e'$: it is precisely the ORDER of steps (L5) that turns a term into a *computation*, and its iteration into a chain $e \to e_1 \to
e_2 \to …$[^1]

In E/R/R terms this is again the familiar triad: expressions are *elements*, the step is a *rule* (L5), the type is a *role* (L4). The question of the chapter is when a run by the rule is safe and how to make it finite.

## Type Preservation and Progress

Type safety stands on two halves. *Preservation* (subject reduction): the type is not lost in a step—if $\Gamma\vdash e:T$ and $e\to e'$, then $\Gamma\vdash e':T$. *Progress*: a well-typed closed expression is either already a value or can take a step—it cannot get stuck “unexpectedly” (the only stuck states are *benign*, singled out by a separate predicate). Together:

$$
\text{well typed}
  \quad\Longrightarrow\quad
  \text{the run never hits an unexpected stuck state.}
$$

This is “well-typed programs don’t get stuck,” by machine.[^2]

## Fuel Finitizes Reduction

Preservation and progress speak of *each* step. But the chain of steps can be arbitrarily long—and here **fuel** (`fuel`) comes in. `eval_fuel` $n$ applies the step *at most* $n$ times:

$$
`eval_fuel`\;0\;e = e,
  \quad
  `eval_fuel`\;(n{+}1)\;e =
    \begin{cases}
      e, & e \text{ is a value},\\
      `eval_fuel`\;n (\text{step }e), & \text{otherwise.}
    \end{cases}
$$

This is *the same* P4 unfolding as `run` $n$ for halting (15.1): the infinite chain is a role-limit, and `eval_fuel` $n$ is its finite approximation. And the two halves of §15.5.3 carry over to the run with fuel: the type is preserved along the whole run, and safe evaluation is *sound*—a well-typed program within the budget gives a value or an honest partial result with a progress status, but *never* steps outside the proved type discipline and never gets stuck *unexpectedly*.[^3]

The name `P4_evaluation_terminates` speaks for itself: termination here is a property of the *process with fuel*, not of the program (it is precisely the latter that the diagonal does not allow to be decided totally). We do not solve halting—we *bypass it by finitization*.

## The Mirror of the Discriminant

Type safety is the same positive move as the discriminant (15.4): *to reduce a role-limit question to a terminating procedure*. The discriminant reduces “is the spectrum rational?” to the perfect-square test; fuel together with type safety replaces the question “will the infinite reduction break off?” with a finite procedure: check the type, perform $n$ steps, obtain a type-preserving result with a progress status. Both draw the Element boundary by one terminating criterion; both are on the *positive* side of the pair diagonal $\oplus$ discriminant. The analogy is exact with a caveat: the discriminant *decides* a property on a given class; fuel ${}+{}$ type safety does not *decide* halting but *certifies* each finite run.

It matters what the chapter does *not* claim. The diagonal (15.3) rules out a total decider of termination, and the type system does *not* get around it as a theorem—it *finitizes* around it: fuel makes every run finite (P4), and types make the finite run meaningful. This is the honest sense of “computation is the finitization boundary”: where there is no total answer, there is a *finite procedure with a guarantee*.

## E/R/R Analysis and What the Chapter Has Prepared

**Rules (L5).**  The small step $e\to e'$ constitutes computation; `eval_fuel` $n$ is its P4 unfolding to a finite depth; preservation ${}+{}$ progress is the rule that makes the run safe.

**Roles (L4).**  The *type* is the role an expression is permitted to play; type checking is a role-criterion (a decidable one); “value / benign stuck state / step” are the statuses of progress.

{

**Elements (L1${}+{}$P4).**  Concrete expressions, runs `eval_fuel` $n$, values. *Not* an element: an infinite completed chain of reductions—a role-limit finitized by fuel.}

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| step $e\to e'$; `eval_fuel` $n$; preservation ${}+{}$ progress | the constitution and safety of the run | Rule (L5) |
| type as a role; type checking; progress statuses | roles and the criterion | Role (L4) |
| expressions; runs `eval_fuel` $n$; values | finitely actual bearers | Element (L1${}+{}$P4) |

**P4 diagnostics.**  Fuel is an *explicit* finitization: infinite chain $\to$ finite run; type safety is the guarantee that the finitization is *meaningful* (it will not get stuck; it is not paradoxical). This is the positive side of the boundary: decidable ${}={}$ finitizable.

**What the chapter has prepared.**  Typed evaluation has been presented as one more face of the positive side: preservation ${}+{}$ progress ${}+{}$ fuel ${}={}$ a safe finite run; everything is by machine and 0-axiom (the result is standard; our angle is P4 finitization). Next comes Chapter 15.6: *complexity as a price*—when computation is possible and safe, its *cost* remains; and the finale, 15.7, will bring both master structures together: *diagonal $\oplus$ discriminant—one finitization boundary*.

---

[^1]: Machine-checked, **0 axioms**: `src/Expressions.v` (the type `Expr`, the typing judgment), `src/Reduction.v` (the relation `step`, its determinism `step_deterministic`, and `multi_step`).
[^2]: Machine-checked, **0 axioms**: `src/SubjectReduction.subject_reduction` (preservation of the type under a step); `src/Progress.progress` (a value or a step) with `is_benign_stuck` (benign stuck states) and `no_unexpected_stuck`.
[^3]: Machine-checked, **0 axioms**: `src/Reduction.v`—`eval_fuel`, `eval_fuel_terminates`; `src/SubjectReduction.eval_fuel_preservation` (preservation along a run); `src/TypeSafety.v`—`type_safety` and `P4_ evaluation_ terminates` (the run with fuel terminates via `eval_fuel_terminates`—P4); `safety_ implies_ no_paradox` in the current file is a *bridging formulation of type preservation* under `eval_fuel` (a separate “no paradox” predicate is not introduced); `src/Evaluator.v`—`safe_eval` / `safe_eval_sound` and the end-to-end `verified_pipeline` (typing ${}+{}$ evaluation).

---

Part: [[15 Computation and the Finitization Boundary|Part XV. Computation and the Finitization Boundary]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/04 One Discriminant Reduction Atlas and the Decidable Side|Chapter 4. One Discriminant: The Reduction Atlas and the Decidable Side]] · [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/06 Complexity as the Price of Finitization|Chapter 6. Complexity as the Price of Finitization]] →
