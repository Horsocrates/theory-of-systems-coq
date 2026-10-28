---
title: "Chapter 1. The Cauchy Problem and the Solution as a Process"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/08 Обыкновенные дифференциальные уравнения/01 Задача Коши и решение как процесс.md"
sourceBlob: a969438a92840586592a02783955176eb81d4a31
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Opening of Part VIII

Part VII brought harmonic analysis to the rational Walsh–Hadamard transform—“Fourier without transcendentals.” The apparatus accumulated so far—processes over ℚ, the inner product, the integral as a process of accumulation, the Banach fixed point—is enough to take up the equations that lie at the foundation of all mathematical physics: *ordinary differential equations*, the equations of *change*.

The classical theory of ODEs takes the solution as a *completed object*: a function $y(t)$ on an interval, existing by the Picard–Lindelöf (or Peano) theorem as a ready element of the function space $C([a,b])$. Existence itself is formulated as a statement about the presence of such an object: “there exists a function satisfying the equation and the initial condition.” ToS applies here the same device that has guided the whole volume. For us the solution is not a completed function but a *process*: a sequence of Euler approximations or Picard iterates, $y_0, y_1, y_2, …$, each of which is a finite rational object. And existence is not the presence of a ready function in $C([a,b])$ but a *property of this process*: its approximations form a *Cauchy process*. The completed solution function on the interval is a role-limit: the process converges to it, but it need not be actualized as an object for the theory to be carried on.

The present chapter sets the ontological framework of the whole of Part VIII: *the solution is a process*, *existence is the presence of a Cauchy process of approximations*. The concrete methods (Euler on a grid—Chapter 8.2), the full Picard–Lindelöf theorem as a contraction on a function space (the center of the Part, Chapter 8.3), stability and uniqueness (Chapter 8.4), and the exponential and linear equations (Chapter 8.5) unfold this framework in detail. Here we establish the shift of viewpoint itself and check that it carries honest constructive content.

### What This Chapter Claims—and What It Does Not

Honesty from the very start. The chapter works with the Cauchy problem for a scalar first-order equation

$$
y'(t) \;=\; f\bigl(t, y(t)\bigr), \quad y(t_0) = y_0,
$$

with a right-hand side $f$ satisfying the Lipschitz condition in $y$, and it reformulates the notion of a solution as a process of approximations over ℚ. The proved core is concrete: the Euler trajectory and the (scalar) Euler–Picard iteration are rational processes; under the Lipschitz condition and for a sufficiently small step, the iteration is a *contraction*, and hence a Cauchy process (the Banach fixed point).[^1]

What the chapter does *not* do: it does not present the completed solution function on the interval as a ready object, does not prove global-in-time continuation, and does not call the exact limit into existence otherwise than as a role-limit. In the current formal layer, the very passage from the geometric decrease of the iterates to their *Cauchy convergence* and to a completed limit inherits the Law of Excluded Middle (L3); this is honestly marked where it is used and is not disguised as a construction.[^2]

To keep the boundary in view, we distinguish three levels of rigor. The *first* is the concrete processes over ℚ: the Euler trajectory, the scalar Euler–Picard iteration, its contraction and Cauchy property—proved exactly, without axioms. The *second* is the process *readings*: the solution as the role-limit of the Cauchy process of iterates, existence as the Cauchy property of the approximations, the right-hand side $f$ as the law of velocity. The *third* is the completed solution function on the interval as a ready object, global continuation, and the exact limit—role-limits and a direction, not a built theory. The chapter treats the first two levels as proved (with an explicit mark where the limit requires L3), and the third as an honestly marked boundary.

### The E/R/R Framework of the Chapter

We set out the framework of the system in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis with a table and a check of correctness is in § “Analysis in the Generating Order.” The chapter introduces the system of *the solution of the Cauchy problem as a process*.

**Rules ($\leftrightarrow$ L5).** The equation itself,
$y' = f(t,y)$, is the law of change linking the value and the velocity. Above it is the rule for generating approximations: the Euler step $y_{n+1} = y_n + h f(t_n, y_n)$ or the Picard operator $\Phi(y)(t) = y_0 + \int_{t_0}^{t} f(s, y(s)) ds$. And the crowning rule of existence: under the Lipschitz condition the iteration is a contraction, so the process of approximations is a Cauchy process; the solution is its limit (the fixed point of the operator).

**Roles ($\leftrightarrow$ L4).** The approximation $y_n$ is the role-stage of the process; the right-hand side $f$ is the role-velocity-field (the law by which the state changes); the initial condition $y_0$ is the role-anchor; “existence” is a role-property (whether the process converges); and the solution itself is the *role-limit* of the Cauchy process of approximations, not actualized as a completed function.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The rational
values of the approximations $y_n$, the grid nodes $t_n$, the finite stage number $n$, the step $h$. Under P4 the completed solution function on the interval lies outside the elements: only the finite stages of the process are actual.

## The Cauchy Problem

### The Equation of Change

A differential equation links the state of a system with the rate of its change. The Cauchy problem is the equation plus an *initial condition*:

$$
y'(t) = f\bigl(t, y(t)\bigr), \quad y(t_0) = y_0 .
$$

Here $f$ is a known rule that says *how fast* the state changes depending on the current moment and the current value; $y_0$ is the state at the initial moment. The question is: what is a *solution* of this problem?

The classical answer: a solution is a function $y(t)$, differentiable everywhere on some interval and turning the equation into an identity. The existence of such an object is guaranteed by the Picard–Lindelöf theorem, provided that $f$ is continuous and Lipschitz in $y$. In this formulation the solution is a *completed function*, an element of the space $C^1([a,b])$, and existence is a statement about the *presence* of such an element.

ToS accepts the equation and the initial condition without reservation: they are finite, rational data. What is called into question is not the problem but the *ontology of the answer*: in order to speak meaningfully of a solution, must we hold in our hands a completed function on the whole interval? The whole volume answers: no. Just as an irrational number is a process of approximations rather than a completed infinite decimal fraction (Part III),[^3] so the solution of a differential equation is a process of approximations rather than a completed trajectory.

### The Shift of the Question

The shift of viewpoint changes the question itself. Instead of “does a function $y(t)$ exist?” we ask: *does the process of approximations converge*, the process that the equation generates from the initial condition? This is not a weakening but a refinement: the classical existence of a function and the process convergence of approximations are two readings of one and the same fact, but the second is *constructive* to the extent that the first is not. The process of approximations can be *presented* and *computed* at any finite stage; the completed function can only be conceived as a limit.

*The solution of the Cauchy problem is not a completed object that “is” or “is not” in a function space but a role: the place toward which the process of approximations, generated by the equation from the initial condition, tends. To ask “does a solution exist” is to ask “does this process converge”—a question about the Cauchy property of a rational sequence, not about the membership of an object in a completed space.*

## The Solution as a Process of Approximations

### The Euler Trajectory

The simplest process generated by the Cauchy problem is *Euler’s method*. We divide the interval with step $h$ and move step by step along the tangent that the right-hand side sets at each point:

$$
y_{n+1} \;=\; y_n + h  f(t_n, y_n), \quad t_n = t_0 + n h .
$$

This is an explicit recurrent process: from the initial value $y_0$ it generates the rational sequence $y_0, y_1, y_2, …$, and each $y_n$ is a finite rational object computable in $n$ steps. There is no passage to the limit in the construction itself: the Euler trajectory is a *process* in the exact sense of the volume, a map from the stage number to a rational approximation.[^4] Chapter 8.2 will analyze it in detail; here it matters only that the Cauchy problem *immediately* generates a process, not an object.

### Picard Iteration

The second, subtler process is *Picard iteration*. We rewrite the Cauchy problem in integral form (by the grid-process fundamental theorem of calculus of Part V, where the integral is a process of accumulation):

$$
y(t) \;=\; y_0 + \int_{t_0}^{t} f\bigl(s, y(s)\bigr) ds .
$$

The right-hand side is an *operator* $\Phi$ acting on functions: $\Phi(y)(t) = y_0 + \int_{t_0}^{t} f(s, y(s)) ds$. The solution is a fixed point of this operator, $\Phi(y) = y$. Picard iteration builds it as a process: we start from the constant $y^{(0)}(t) \equiv y_0$ and apply the operator successively, $y^{(m+1)} = \Phi(y^{(m)})$. Each iterate is a function approximating the solution; the whole sequence is a process on the function space.[^5]

In both cases—for Euler and for Picard alike—the solution appears as a *process*: a sequence of approximations indexed by the stage number. The methods differ in what a stage approximates (a point of the trajectory or a whole function) and in how fast the process converges. But the ontology is one: *the stage is actual, the limit is a role*.

*The approximation $y_n$ (or $y^{(m)}$) is a role-stage: a finite rational snapshot of a process not yet completed. The right-hand side $f$ is the role-velocity-field: the law by which the process takes its next step. The solution itself is the role-limit, the direction of the convergence of the stages, not one of its snapshots.*

## Existence as the Presence of a Cauchy Process

### Contraction Generates Convergence

What does “the process of approximations converges” mean? Exactly that it is a *Cauchy process*: its stages eventually come arbitrarily close to one another. And here the Lipschitz condition on the right-hand side plays the decisive role. If $f$ is Lipschitz in $y$ with constant $L$, then for a sufficiently small step the Euler–Picard iteration is a *contraction*: the distance between the images of two approximations is strictly smaller than the distance between the approximations themselves, with coefficient $r < 1$. And a contraction, by the Banach scheme, generates a Cauchy process: successive approximations draw together geometrically.[^6]

Thus the existence of a solution is rewritten *without* appeal to a completed function: *the approximations generated by the equation form a Cauchy process*. This is a statement about a rational sequence: it can be formulated and proved without calling a single infinite object into existence. The constructive core of the Picard–Lindelöf theorem is exactly this: not “there is a function” but “the process contracts.”

### Where the Boundary Appears

The boundary lies exactly where a *completed limit* as an object is demanded of the Cauchy process. “A Cauchy process converges to a limit” is a step that over ℚ (without a completed ℝ) relies on the Law of Excluded Middle: the limit exists as a role that the stages approach, but its actualization as a ready function is no longer a construction but a postulate of L3.[^7] In just the same way, the global-in-time continuation of the solution, its behavior on an infinite interval, and the completed trajectory as a single object are role-limits, not built entities.

What is proved is the finite and the process-level: the equation generates a process of approximations, and under the Lipschitz condition this process is Cauchy. This is enough to carry on the whole theory of ODEs as a theory of *solution processes*—grid trajectories (Chapter 8.2), the contracting Picard operator (Chapter 8.3), the stability of approximations (Chapter 8.4)—without calling the completed solution function into existence.

*The existence of a solution is a role-property of the process: whether it converges. Proved constructively (0 axioms) are the algebra of contraction and the geometric gap between the iterates (Chapter 8.3, `picard_iter_gap`); the Cauchy convergence itself and the completed limit, in the current formal layer, inherit L3 through `Qpow_vanish` and are honestly marked according to `Print Assumptions`. The completed limit is a role-limit, not actualized as a function-object.*

## E/R/R Analysis: The Solution as the Role-Limit of a Process

### Setup

Let us analyze the constructed system—the solution of the Cauchy problem as a process—in terms of E/R/R. A reservation about the level: the “system of the solution” here is a substantive *interpretation* of the construction (the equation plus the rule for generating approximations plus convergence), not an object literally declared in the code as `System`. The analysis is an ontological comprehension of the structure of the chapter and a reading of the author’s E/R/R headers of the supporting files,[^8] not an attribution of new formal claims to the code.

Recall the distinction adopted in the volume: the abbreviation E/R/R sets the *epistemic* order (Elements $\to$ Roles $\to$ Rules, from the observable to the deep), while the generating (*ontological*) order is the reverse: Rules $\to$ Roles $\to$ Elements. Epistemically we went from the observable approximations to the law of their generation and convergence; we conduct the analysis in the generating order.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the equation itself, $y' = f(t,y)$: the law linking the state and the velocity of its change. Above it is the rule for generating approximations: the discrete Euler step $y_{n+1} = y_n + h f(t_n,y_n)$ or the integral Picard operator $\Phi$. The construction is crowned by the rule of existence: when $f$ is Lipschitz, the iteration is a contraction, so the process of approximations is a Cauchy process, and the solution is the fixed point of the operator (its role-limit). The universal layer of these rules is the laws L1–L5 (in particular L3, which makes the completed limit an object); the concrete layer is the formula of the step and the condition $Lh<1$.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The approximation $y_n$ is a role-stage: a finite snapshot of the process at index $n$. The right-hand side $f$ is the role-velocity-field: the law of the next step. The initial condition $y_0$ is the role-anchor. “Existence” is a role-property (whether the process converges). And the solution itself is the *role-limit*: the place toward which the stages tend, not actualized as a completed function-object.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The roles select
bearers, and the bearers here are finite at every stage: the rational approximations $y_n$, the grid nodes $t_n$, the stage number $n \in ℕ$, the step $h \in ℚ$. Under P4 no element is a completed infinity: only the finite stages are actual; the completed solution function is not actualized as an element—what is actualized is the process of approximations to it.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| $y'=f(t,y)$; Euler step $y_{n+1}=y_n+hf$; Picard operator $\Phi$; contraction$ \Rightarrow $Cauchy | HOW the approximations are generated and why they converge | Rules ($L5$) |
| stage $y_n$; velocity field $f$; anchor $y_0$; existence; the solution as a limit | WHAT FOR the bearers are significant: places in the process | Roles ($L4$) |
| $y_n\inℚ$; nodes $t_n$; index $n\inℕ$; step $h\inℚ$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is what is *absent* here: the solution process does *not* take as its element “the completed trajectory on the whole interval” or “the solution function as a ready object.” The system is finite at every stage, and existence is checked as the *Cauchy property* of the generated process, not as the membership of an object in a completed function space. It is precisely the absence of such self-reference that explains why the theory of ODEs needs here neither a completed function nor a postulate of its existence beyond the convergence of the process: everything substantive is expressed by finite approximations and the criterion of their drawing together.

What the analysis yields. It translates the results of the chapter into the language of structure: *the solution is a Role* (the limit of the process of approximations), *existence is a Rule-criterion* (contraction, which entails the Cauchy property), and the approximations $y_n$ and nodes $t_n$ themselves are *Elements* (finite at every stage). To take “the solution” as a completed function-object is to put the role-limit in the place of an Element—a confusion of categories of the same kind as “number as an object” instead of the role-quantity (Part II), “a point as an object” instead of a class (Chapter 4.3), and “a Fourier series as a completed sum” instead of a family of truncations (Chapter 7.1). The solution of an ODE begins here as a *process* of finite approximations; its convergence is the Cauchy property of this process, and as a completed object the solution is neither needed nor built.

The next chapter presents the simplest of these processes in full concreteness—Euler’s method on a rational grid: the trajectory as a generating process, the strict distinction between the stage number and the grid step, and explicit rational approximations to the exponential, linear, and quadratic solutions.

---

[^1]: The supporting files are `ProcessODE.v` and `ProcessPicard.v` (directory `src/process/` of the ToS Rocq repository), plus `stdlib/ODE.v` (the record `ODE` with the Euler step as a `GenProcess`, 22 proved statements, 0 `Admitted`). The scalar Euler–Picard contraction and its Cauchy property are `euler_picard_contraction` and `euler_picard_cauchy` in `ProcessPicard.v`; the Banach layer is `iterate_is_cauchy` in `FixedPoint.v`.
[^2]: The Banach fixed-point theorem (`banach_fixed_point`) and the Cauchy convergence of the iterates (`iterate_is_cauchy`) in `FixedPoint.v` inherit `classic` through the lemma on the decay of $c^n$ (`Qpow_vanish`); the header of the file notes this directly, and the file contains `Print Assumptions` for both. What is *constructive (0 axioms)* here is something else: the algebraic estimate of the *contraction* (`euler_picard_contraction`, `ProcessPicard.v`) and, in the extended layer of Chapter 8.3, the *geometric gap* between the iterates and the *uniqueness* of the solution on the grid (`picard_iter_gap`, `picard_unique` in `ProcessPicardOperator.v`, checked with `Print Assumptions`: “closed under the global context”). The backbone of the chapter is precisely this distinction: the algebra of contraction and the gap are built without axioms; the passage to the completed limit is the L3 layer.
[^3]: See Part III, Chapter 4: in ToS the irrational is an $ℝ$-process (a full E/R/R object), not a “number” and not a “rule that excludes an element.” The solution of an ODE inherits exactly this ontology: a process whose terminus is a role-limit.
[^4]: The Euler step and the method are `euler_step` and `euler_method` in `ProcessODE.v`; the Euler trajectory on a rational grid is `euler_traj` in `analysis/PicardLindelof.v`; in `stdlib/ODE.v` the Euler step is set up as a `GenProcess`, the generating process of the volume, a map $ℕ \to ℚ$. That the solution *is* a process, not its limit, is recorded in `ode_is_process` (`ProcessODE.v`): the pair “solution process / error process,” where the solution process coincides with the Euler–Picard iteration.
[^5]: The integral Picard step `picard_step` is defined in `ProcessPicard.v`; the integral in it is the process of accumulation of Part V. The full theorem on the contraction of the Picard operator *on the function space* (not only of the scalar step) is the center of the Part, Chapter 8.3 (`ProcessPicardOperator.v`).
[^6]: In the scalar layer: `euler_picard_contraction` (`ProcessPicard.v`) proves that the map $y \mapsto y_0 + f(y) h$ is a contraction (`is_contraction`) with coefficient $Lh$ for $Lh<1$; this is constructive, 0 axioms. The passage from contraction to the *Cauchy convergence* of the iterates itself (`euler_picard_cauchy` in the same file; `iterate_is_cauchy` in `FixedPoint.v`) goes through the lemma on the decay of $c^n$ (`Qpow_vanish`) and therefore inherits `classic`. In other words, “the approximations form a Cauchy process” splits into the constructive algebra of contraction and the L3-dependent passage to the limit, which is exactly what `Print Assumptions` checks.
[^7]: The full Banach theorem in the form “a fixed point *exists*” (`banach_fixed_point`) inherits `classic`; see also `ProcessPicardOperator.v` (Chapter 8.3), where the *contraction on the function space*, the *uniqueness* of the solution on the grid, and the *geometric gap* between the iterates are proved without axioms, while the explicit wrapper “iterates $\to$ completed solution” is honestly assigned to this L3 layer.
[^8]: The headers give the labeling directly: `ProcessODE.v` and `ProcessPicard.v`—Elements: rational approximations, grid nodes, the step $h$; Roles: the approximation is a stage, the solution is a limit, $f$ is the velocity field; Rules: the Euler step / the Picard operator, contraction under the Lipschitz condition. The header of `ProcessPicardOperator.v` (Chapter 8.3) explicitly marks the completed solution function as a role-limit.

---

Part: [[08 Ordinary Differential Equations|Part VIII. Ordinary Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/07 Harmonic Analysis/05 Compression Fast Transform Convolution|Chapter 5. Compression, Fast Transform, Convolution—Part VII]] · [[Library/Branches/Mathematics/Volume/08 Ordinary Differential Equations/02 Euler Method Solution on a Grid|Chapter 2. Euler’s Method: The Solution on a Grid]] →
