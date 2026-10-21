---
title: "Chapter 7. Fubini’s Theorem on Processes"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/05 Топология и анализ процессов/07 Теорема Фубини на процессах.md"
sourceBlob: 5b1c0a137e379c4c51885f5db985fc8f2e9cde4f
translated: 2026-10-20
status: draft
---

## What This Chapter Needs Fubini For

### Where the Chapter Stands

Part V has gone through one-dimensional analysis on processes: the metric (Chapter 5.1), topology and compactness (5.2), continuity (5.3), the derivative as a process of refining the slope (5.4), the integral as a process of accumulation (5.5), and the fundamental theorem of calculus that linked them (5.6). The one-dimensional picture is closed. One step remains—into *multidimensional* integration—and its first law is Fubini’s theorem: the connection of the *double* integral with the *iterated* one-dimensional ones.

### What Exactly This Chapter Proves—and What It Does Not

Honesty is needed here from the very beginning, for the subject is deceptive. Formally, what is proved in this chapter is a finite *step* level: lists of rectangular contributions with exact rational arithmetic—*not* a process of refining two-dimensional partitions. The supporting file has neither the type `RealProcess`, nor a function `nat` $\to$ ℚ, nor a sequence of ever finer 2D grids; it has a finite list of rectangles and finite sums of their contributions.[^1]

But it is precisely this modest level that shows *the first law of the order of observation*—that the result does not depend on the order in which the contributions are added—and shows *where* this law turns from trivial into hard. “The double integral as a process over 2D partitions” will remain in this chapter a *philosophical frame* and a program, not a proved object; what is proved is a finite prototype, which this process must in the future lift to the limit.

### The Plan of the Chapter

The chapter proceeds as follows. First, the finite double integral over rectangular contributions (§ 7.2) and Fubini’s theorem for step functions proved on it (§ 7.3), with concrete computations. Then the methodological summit: *why* the interchange of limits is nontrivial and what legitimizes it (§ 7.4). Then the honest boundary: the continuous case as a program, not a theorem, with its bricks named (§ 7.5). Then generalizations and applications as a perspective (§ 7.6), the E/R/R analysis (§ 7.7), and the summary of the chapter and of the whole of Part V (§ 7.8).

## The Finite Double Integral over Rectangular Contributions

### From One Dimension to Two

The one-dimensional integral of a step function (Chapter 5.5) is a sum of contributions $c_i\cdot(b_i-a_i)$—the value on a piece multiplied by the length of the piece. The two-dimensional analogue takes the value on a *rectangle* and multiplies it by its *area*: $c\cdot(x_2-x_1)\cdot(y_2-y_1)$. This is the bearer of the present chapter.

### The Rectangle and Its Integral

ToS records a rectangular contribution with the type `Rectangle`: a constant rational value on a rational rectangle, with a condition that the bounds are well-formed.

```coq
Record Rectangle := mkRect {
  rect_val : Q;
  rect_x1 : Q;  rect_x2 : Q;
  rect_y1 : Q;  rect_y2 : Q;
  rect_x_valid : rect_x1 <= rect_x2;
  rect_y_valid : rect_y1 <= rect_y2 }.

Definition rect_integral (r : Rectangle) : Q :=
  rect_val r * (rect_x2 r - rect_x1 r) * (rect_y2 r - rect_y1 r).
```

A two-dimensional step function is a finite list of such rectangles, `StepFun2D := list Rectangle`, and its double integral `integral_2d` is the sum of the contributions `rect_integral` over the list. All the arithmetic is exact, in ℚ; there are no limits at this level.

### A Caveat: A List of Contributions, Not a Partition

{
Precision is needed here; otherwise a modest object will sound stronger than it is. `StepFun2D` is a *formal finite sum of rectangular contributions*—*not* necessarily a partition of the domain and *not* necessarily a disjoint set of rectangles. The file defines the sum of the contributions and proves its properties; it builds no theory of covers of the domain and does not require the rectangles to tile $[a,b]\times[c,d]$ without gaps and overlaps. This suffices to see the law of order, but it is not the general double integral of an arbitrary function.}

## Fubini for Step Functions: What Is Proved

### One Rectangle: The Order Does Not Matter

The iterated integral over one rectangle can be taken in two orders: first in $x$, then in $y$—or the other way round. ToS records both and proves their equality.

```coq
Definition iterated_xy (r : Rectangle) : Q :=
  rect_val r * (rect_x2 r - rect_x1 r) * (rect_y2 r - rect_y1 r).
Definition iterated_yx (r : Rectangle) : Q :=
  rect_val r * (rect_y2 r - rect_y1 r) * (rect_x2 r - rect_x1 r).

Lemma fubini_rectangle : forall r : Rectangle,
  iterated_xy r == iterated_yx r.
Proof. intros r. unfold iterated_xy, iterated_yx. ring. Qed.
```

The proof is the single word `ring`: the equality is exactly the commutativity of multiplication, $c\cdot\Delta x\cdot\Delta y = c\cdot\Delta y\cdot\Delta x$. And both iterated quantities equal the double integral of the rectangle (`iterated_eq_double`, `iterated_yx_eq_double`).

### A List of Rectangles: Induction

{
For a finite list of contributions Fubini’s theorem is proved by induction on the list: on the empty list, an identity; on the step, the equality for the head rectangle (`fubini_rectangle`) plus the induction hypothesis.}

```coq
Theorem fubini_step : forall f : StepFun2D,
  iterated_xy_list f == iterated_yx_list f.
Proof.
  intros f. induction f as [| r rest IH].
  - simpl. ring.
  - simpl. rewrite fubini_rectangle. rewrite IH. ring.
Qed.
```

{
And both iterated integrals of the list equal the double one (`iterated_xy_eq_2d`, `iterated_yx_eq_2d`): the order of adding the contributions and the order of integration inside a contribution are both immaterial.}

### Concrete Computations

{
In the spirit of Part V—not only a construction but a working computation. Take $f=3$ on $[0,1]\times[0,2]$: the double integral is $3\cdot1\cdot2=6$, and both orders give the same (`example_rect_integral`, `example_fubini_concrete`). For two rectangles—$f=2$ on $[0,1]\times[0,1]$ and $f=3$ on $[1,2]\times[0,1]$—the double integral is $2+3=5$ (`example_two_rects`). Rocq checks all this by exact rational arithmetic: in these examples the proofs reduce to `ring` or a direct application of `fubini_rectangle`—process analysis here is computation, not abstraction.}

### Trivial at the Step, Hard at the Limit

*At the step level Fubini’s theorem is **trivial**: it is the commutativity of multiplication, proved by a single `ring`. The whole substantive weight of the theorem lies **not here** but at the level of the limit—where the finite list of contributions must give way to a process of refining partitions. The proved `fubini_step` is a finite **prototype** of the law of order; the real Fubini begins beyond it.*

## Why the Interchange of Limits Is Nontrivial

### The Double Limit

Let us pass from the step to the real subject. The double integral of a continuous function is a *process*—a process of Riemann sums over ever finer two-dimensional grids. The iterated integral is a *process of processes*: first the process of one-dimensional integration in $y$, giving a function of $x$, then the process of integrating this function. Fubini’s statement is therefore a *change in the order of a double limit process*: first the limit in $y$, then in $x$—or the other way round.

### In General, Limits Cannot Be Interchanged

And changing the order of two limits is a delicate operation, *invalid* in general. The quantities $\lim_n \lim_m a_{nm}$ and $\lim_m \lim_n a_{nm}$ may give different values, or even fail to exist at all. This is a well-known fact of analysis, and Fubini’s theorem is exactly the statement that for the integrand *here* the interchange is legitimate. Without justification this statement is false: there exist functions for which the iterated integrals in different orders give different numbers.

It is worth saying precisely *what* the familiar classical exposition hides when it presents Fubini as a technical result. What it hides is less a single act of choice than the *conditions* under which changing the order of limits *is permitted*: the completeness of $L^1$, the integrability of the integrand, dominated convergence, the Fubini–Tonelli machinery. In a constructive reading it is precisely these places that require explicit processes and moduli of convergence rather than a silent passage to the limit.

### What Legitimizes the Interchange: Uniformity

What, then, makes the interchange legitimate for a *continuous* function on a compact rectangle? *Uniform* continuity (Chapter 5.3). When $f(x,y)$ is continuous on the compact set $[a,b]\times[c,d]$, its modulus of continuity $\omega(\varepsilon)$ depends *neither* on $x$ nor on $y$. Hence the rate of convergence of the Riemann sums is estimated by one common function $\varepsilon\mapsto\delta(\varepsilon)$ for all points of the rectangle—and the refinement of the partition in $x$ and in $y$ can be *synchronized*: for any precision $\varepsilon$, a sufficiently fine grid can be chosen in both coordinates at once. This simultaneity is exactly what makes the double limit correct.

### Three Conditions

So the interchange of limits in Fubini on a compact rectangle rests on three conditions:

| Condition | What it gives |
|---|---|
| continuity of $f$ | local moduli of continuity at each point |
| compactness of the domain (Heine–Borel, 5.2) | uniformity—a single modulus on the whole rectangle |
| the Archimedean property of ℚ\ (3.4) | coordination of the partition levels in the two coordinates by one $N$ |

Without any one of the three the theorem in general form breaks down: for discontinuous functions or on noncompact domains there are classical counterexamples in which the iterated integrals disagree. With the three conditions a framework of the future justification appears: they give the synchronization of grids and control of the approximations. But—and this is the subject of the next section—the proof itself of the interchange of two limit processes requires the $L^1$ layer and dominated convergence, and in the repository it has not yet been assembled into a machine theorem.

## The Continuous Case: A Program, Not a Theorem

### A Framework, Not a Proof

The three conditions of § 7.4 are the correct and standard path to the continuous Fubini. But by themselves they do *not prove* the theorem: they give an engineering framework for building synchronized two-dimensional grids. The interchange of two limit processes requires, beyond this framework, a separate layer—the approximation of a continuous function by step functions and control of the convergence of the integrals (of the dominated-convergence type). *This layer is not assembled here.* The repository has no single machine theorem “Fubini for continuous functions.”[^2]

### The Bricks—and What Exactly They Are

{
The bricks for the future continuous case exist in the repository, and it is important to name each one *precisely*, without attributing to it a strength that belongs to something else.
}

*The exact step integral.* The file `StepIntegral.v` (20 Qed, 0 axioms) gives the exact integral of step functions over ℚ—the foundation of the Bishop–Cheng approach, on which everything else is the $L^1$ completion. This is the future *bearer* of the approximation; the theorem itself on approximating a continuous function by step functions is *not proved* in this chapter.

*The skeleton of dominated convergence.* The file `DominatedConvergence.v` (20 Qed, 0 axioms) gives the foundations at the *step* level: domination, $L^1$ convergence, convergence of integrals, the skeleton of the dominated convergence theorem. The file itself honestly notes that at the step level this theorem is almost trivial, and that the deep content arises in the passage to the $L^1$ completion. This is *not yet* the dominated convergence that proves the continuous Fubini.

*Compactness—with the ℚ limitation.* The file `HeineBorelComplete.v` (22 Qed, 0 axioms) gives the total boundedness of ℚ-intervals and uniform continuity *from the Lipschitz property*, plus the theory of $\varepsilon$-nets. But it also notes directly: the full Heine–Borel theorem and the passage “continuity $\Rightarrow$ uniformity” in general form over ℚ are *not available in the current layer*—only the Lipschitz special case or the assumption of a Lebesgue number is used. This is an honest boundary of the compactness instrument itself.

### What Remains a Frontier

So the continuous Fubini is a *program*, not a theorem: the framework of three conditions is correct and the bricks are named, but all of them are of the step level, and the decisive step (the $L^1$ completion and dominated convergence on it, with a careful way around the ℚ limitation on uniformity) remains a frontier of process analysis. In the working map of the formalization (see the summary of the volume) this task stands as an explicit item.

## Generalizations and Applications

What follows are directions for which the step Fubini is the first finite prototype—*not* results of the current file.

*The n-dimensional generalization.* Fubini generalizes to integrals over $n$-dimensional domains; the constructive path is induction on dimension, reducing the $n$-dimensional integral to a one-dimensional one step by step. The code does not contain this generalization—it is sketched as a program.

*Applications.* The continuous Fubini, once it is assembled, is relied on by: the computation of volumes of multidimensional bodies; the reduction of multidimensional equations (in particular PDEs) to one-dimensional ones; the Laplace and Fourier transforms (Part VII); the construction of product measure (Part VI). All this is a perspective lying beyond the present chapter, not its consequences.

## E/R/R Analysis: The Fubini Interchange as a System

Let us consolidate what has been proved with an E/R/R analysis (Part I); the header of the supporting file gives the labeling directly. We proceed in the ontological order Rules $\to$ Roles $\to$ Elements.

*Rules*—the constitution: the order of integration does not affect the result (`fubini_step`); at the step level this is the commutativity of multiplication. *Roles*—the significant positions: the double integral, the iterated integral, the exchange of order. *Elements*—the bearers: rectangles and finite lists of rectangular contributions; by $P4$ every such list is finite, and the integral is computed exactly.

*Well-formedness and diagnosis.* The labeling is unambiguous: rectangles are elements, the integrals and the exchange are roles, the law of order is a rule. And here the analysis turns into a diagnosis important for the whole chapter: at the finite step level the rule of interchange is *proved* (commutativity); at the level of the *limit* it becomes a hard theorem. To mix the two levels—to take what is proved at the step for what is proved at the limit—is exactly the constructive trap into which a naive reading of Fubini falls. What the classical exposition hides here is the *conditions for interchanging limits* (§ 7.4), not “choice in general”; an honest labeling brings these conditions out into the open.

## Summary of the Chapter. Summary of Part V. Transition to Part VI

### Summary of the Chapter

The chapter has gone through Fubini’s theorem at the honest depth at which it is formalized today. Proved—exactly and without axioms—is the step case: the double integral of a finite list of rectangular contributions does not depend on the order of integration (`fubini_step`). It has been shown that at this level the theorem is trivial, and that its real weight lies in the interchange of *limits*: for the continuous case, uniform continuity on a compact set gives a framework for synchronizing grids, while full justification requires the $L^1$ layer and dominated convergence. And it has been honestly outlined that the continuous case remains a program: the framework of three conditions is correct and the bricks are named, but the $L^1$ layer is not assembled.

### Summary of Part V

With the present chapter Part V closes. Let us compress its path. The metric turned out to be a process of differences (5.1). Topology and compactness turned out to be modes of consideration of families of processes: compactness was taken through constructive and conditionally classical forms—$\varepsilon$-nets, the uniform variant of Heine–Borel, and the Cauchy version of Bolzano–Weierstrass, with explicit marking of $L3$/$L4$ where it is needed (5.2). Continuity came with $\varepsilon$-versions of the intermediate value and extreme value theorems (5.3). The derivative turned out to be a process of refining the slope (5.4); the integral, a process of accumulation (5.5). The fundamental theorem of calculus linked the derivative and the integral (5.6). And Fubini opened the door to the multidimensional, showing the law of order on a finite prototype and naming where its depth begins (5.7). The through-line has been sustained: *an analytic object is built as a process*—in some places as a genuine process of approximation, in others (Fubini) as a finite step prototype of a future process limit.

### Transition to Part VI

Next come measure and Lebesgue integration. The step integral, which served here as the bearer, is the foundation of measure in the Bishop–Cheng approach; the $L^1$ completion, left as a frontier in § 7.5, is precisely the subject of Part VI. There ToS will build integration *without an external set-theoretic axiom of choice*, with explicit local marking of $L3$ and $L4$ where they are needed—and then the continuous Fubini, the program of this chapter, will receive its full proof.

{
*The summary—in three parts. First: what is proved. Fubini’s theorem for finite lists of rectangular contributions: the double integral does not depend on the order of integration (`fubini_step`)—exactly, without axioms, as the commutativity of multiplication. Second: what this rests on and what is not here. A step prototype is proved; the continuous case is a program on three conditions (uniform continuity, compactness, the Archimedean property) with named bricks (`StepIntegral`, `DominatedConvergence`, `HeineBorelComplete`), but without an assembled $L^1$ layer. Third: where it leads. The interchange of limits is the heart of multidimensional analysis, not a triviality; the step Fubini is its finite prototype, and the full proof awaits the measure of Part VI. With this Part V is completed: the whole of basic analysis has received a process-compatible infrastructure—some results are already given as processes, some as finite step prototypes of future process limits—and the strength of each step has been honestly labeled.*}

---

[^1]: The supporting file is `FubiniProcess.v` of the ToS Rocq repository (directory `src/analysis/`), 20 proved statements, 0 `Admitted`, 0 axioms. The names given below are from it.
[^2]: In the preliminary plan of the chapter the proof of the continuous case was mistakenly attributed to a nonexistent file `Fubini.v`; the file that exists, `FubiniProcess.v`, proves the step case. This has been corrected here.

---

Part: [[05 Topology and Analysis of Processes|Part V. Topology and Analysis of Processes]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/06 Fundamental Theorem of Calculus|Chapter 6. The Fundamental Theorem of Calculus]] · [[Library/Branches/Mathematics/Volume/06 Measure and Integration/01 Measure as a Process of Assignment|Chapter 1. Measure as a Process of Assignment—Part VI]] →
