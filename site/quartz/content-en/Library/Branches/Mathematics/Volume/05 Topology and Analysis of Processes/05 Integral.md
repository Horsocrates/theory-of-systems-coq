---
title: "Chapter 5. The Integral"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/05 Топология и анализ процессов/05 Интеграл.md"
sourceBlob: 4c4558a5a1d8322d47e5311eeef70bb6eceb104d
translated: 2026-10-20
status: draft
---

## The Integral as a Process of Accumulation

### What the Previous Chapters Built

Part V builds analysis layer by layer. Chapter 5.1 introduced distance; 5.2, topology and compactness; 5.3, continuity; 5.4, the derivative: the division-free criterion $o(h)$, the derivative-process `deriv_process`, and the grid mean value theorem via walk points. The integral is the next layer, and it is dual to the derivative: there we measured the rate of change, here we measure an accumulated quantity—the area under the graph.

The connection with the previous chapter is direct and technical. The Riemann sum by which the integral is built is defined on the same *walk points* as the mean value theorem of § 5.4: the grid $x, x+s, x+2s,…$ sets the nodes at which the values of the function are taken. That is, the chapter on the integral stands directly on the grid built by the chapter on the derivative. And the uniform differentiability `udiff_on` of § 5.4 will turn out to be exactly the condition under which the sums of the derivative converge to the increment of the function.

### Area and the Limit as a Problem

Classically the integral is the limit of Riemann sums as the partition is refined:

$$
\int_a^b f \;=\; \lim_{\text{partition}\to 0} \sum_i f(x_i) \Delta x_i.
$$

As with the derivative, it is worth understanding precisely what *constitutes* the difficulty here and what does not.

A *finite* Riemann sum constitutes no difficulty. If the grid is fixed—say, $n$ equal intervals—then $\sum_i
f(x_i) \Delta x_i$ is a finite sum of products of rational numbers, that is, a rational number computed exactly. It needs no limit at all.

The difficulty lies in the limit. First, $\lim$ under refinement is a completed object, and under $P4$ there are no completed limits. Second, “a partition as fine as one likes” refers to a potential infinity of levels of refinement. What is needed is a formulation in which the limit of the sums does *not* stand in the place of the primary definition—exactly as with the derivative, where the limit of the quotient was not primary.

### The Finite Riemann Sum on a Grid

The first layer of the integral is a *finite* sum. On a uniform grid of walk points with step `step`, the left Riemann sum is defined by recursion on the number of nodes:

```coq
Fixpoint riemann_sum (f : Q -> Q) (a step : Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => f (walk_point a step n') * step + riemann_sum f a step n'
  end.
```

That is, $`riemann_sum` f a `step` n = \sum_{k=0}^{n-1}
f(`walk_point` a `step` k)\cdot`step`$—the sum of the areas of $n$ rectangles with height $f$ at a node and width `step`. At each fixed $n$ this is a rational number, exact, with no approximation whatsoever.

{ Let us note the level of the type (the Part V safeguard): $f:ℚ\toℚ$, and the sum is a rational number. And at once a warning about names (safeguard C4). The repository has *three different* definitions named `riemann_sum`: this one, the main one, from `RiemannIntegration.v` (the left sum over `walk_point`); a separate `riemann_sum_01` on the interval $[0,1]$ in `ProcessIntegration.v`; and one more, a demonstration one, in `ProcessAnalysis.v`. The names coincide, the definitions differ; below, by `riemann_sum` we always mean the first, and we will turn to the other two separately in § 5.7, naming the file each time.}

### The Integral-Process: `integral_process`{The integral-process: integral_process}

The second layer is a *process*. To obtain the integral, the finite sum has to be refined. Let us fix a sequence of ever finer grids: at level $n$ we take $n+1$ subintervals with the step

$$
`integral_step`\;a\;b\;n \;=\; \frac{b-a}{n+1}
$$

and compute the Riemann sum on this grid. We obtain a process—at level $n$, a rational number:

```coq
Definition integral_step (a b : Q) (n : nat) : Q :=
  (b - a) / inject_Z (Z.of_nat (S n)).

Definition integral_process (f : Q -> Q) (a b : Q) : RealProcess :=
  fun n => riemann_sum f a (integral_step a b n) (S n).
```

Under $P4$ the integral is conceived as the process itself of rational approximations of the area, not as the limit of this process—exactly as in § 5.4 the derivative was a process of approximations of the slope. The step is positive for $a<b$ (`integral_step_pos`), and refinement works: `integral_step_vanishes` states that for every $\delta>0$ there is a level $N$ with a step smaller than $\delta$ (through the Archimedean lemma `nat_above_Q` from § 5.4). The type of the process is `RealProcess`, that is, $ℕ\toℚ$.

The same *safeguard* is needed here as for the derivative-process in § 5.4. The process `integral_process` $f a b$ is defined for *any* function $f:ℚ\toℚ$—but its existence alone does *not* yet make $f$ integrable. `integral_process` is the canonical *candidate*, a representative of the integral; its analytic legitimacy requires the process of sums to *converge* (to have the Cauchy property). For constants this is seen at once (§ 5.2.1); for broader classes of functions the Cauchy property is assembled from grid estimates and the grid form of the fundamental theorem (§ 5.5). The theorem `integral_is_process_construction`, which presents the process of sums as a construction, is *not* a theorem of integrability, and the one should not be passed off as the other.

### E/R/R Analysis: The Integral as a System

The integral is a system, and the E/R/R methodology (Part I) applies to it. The analysis unfolds the labeling from the headers of the supporting files: *elements—partial Riemann sums; role—a Cauchy process converging to the value of the integral; rules—linearity, monotonicity, nonnegativity*.[^1] We conduct the analysis in the ontological order Rules $\to$ Roles $\to$ Elements. The caveat on status is the same as in Chapters 5.1–5.4: we are dealing with functions $ℚ \to ℚ$, not with an integral on quotient classes; the “system” is a substantive ontological interpretation, not an object `System` $L$.

*Rules* (the law $L5$). The constitution of the integral is *accumulation*: the Riemann sum on the walk grid (§ 5.1.3) plus refinement (`integral_process`, § 5.1.4). Adjoining it is a concrete layer—linearity (§ 5.3), monotonicity and *nonnegativity* (motif M4, § 5.4): it is precisely these order rules that make the integral the foundation of measure. The legitimacy of the process as an integral is given by one more rule-condition—*integrability* as the Cauchy property of the process of sums (through grid-FTC, § 5.5). An honest boundary: the core has no separate predicate of integrability; the Cauchy property is assembled from grid estimates for a particular class of functions (§ 5.5.3).

*Roles—the significance of positions* (the law $L4$). The central role is the *accumulated quantity*, the area under the graph, which integration assigns to a function on an interval. The computational side of the role is carried by the *process* of Riemann sums—a Cauchy process converging to the value of the integral (this is how the role is named in the file header). In the exact step line the same role appears as *integration* and the $L^1$-*norm* (§ 5.2.3). By $L4$ the role is grounded: the area is structurally given by a sum of values with widths as weights, not from outside.

*Elements—the bearers* (the law $L1$ and the principle $P4$). The elements are integrand functions $ℚ \to ℚ$ and *partial Riemann sums* $`RS`_n$ (and in the step line, records `Step`). By $L1$ each sum is identical to itself. By $P4$ the bearers are finite at each level: $`RS`_n$ is a finite sum of rationals, exact and surveyable; the integral is actual as a process of accumulation, and there is no completed limit of the sums.

 Let us gather the analysis into a table.

| Component | What it determines | E/R/R |
|---|---|---|
| functions $ℚ \to ℚ$; sums $`RS`_n$; `Step` records | bearers | Element |
| area; the process converging to the value of the integral | roles | Role |
| the Riemann sum on the grid $+$ refinement | constitution as accumulation | Rule (constr.) |
| linearity, monotonicity, nonnegativity (M4) | order rules | Rule (constr.) |
| integrability $=$ the Cauchy property (grid-FTC) | condition of legitimacy | Rule |
| the laws $L1$–$L5$ | universal layer | Rule (univ.) |

*Well-formedness.* The labeling is unambiguous: functions and sums are elements, the area is a role, accumulation and the order laws are rules. There is no self-reference: the sum works *on* the values of the function and stands above them—by $L5$ the operation stands above its operands. The two constructions—the exact step line and the process of Riemann sums—are two agreed representations of one role-integral (§ 5.2.5); they do not compete. The integral is well-formed.

 The analysis clarifies the place of the integral in Part V. It is *dual* to the derivative (§ 5.4): both systems have one role pattern—a process converging to a value (the slope there, the area here)—and dual rules (differentiation versus accumulation); the fundamental theorem (Chapter 5.6) will link the two processes into one. Motif M4—nonnegativity—is the rule by which the integral becomes a *positive functional*, the foundation of measure (Part VI). And the two constructions, the exact and the process one, are two intensional representations of one integral—the same multiplicity of representations ($P3$) as with the three levels of the intermediate value theorem in Chapter 5.3. The same analysis also sets the pattern for Part V: every analytic concept is read as a system with its own E/R/R structure.

### The Plan of the Chapter

From here the chapter proceeds as follows. § 5.2: the integral of simple functions—the constant, the width of the grid, exact step functions. § 5.3: linearity. § 5.4: monotonicity and nonnegativity (motif M4). § 5.5: estimates and convergence—integrability as the Cauchy property of the process of sums. § 5.6: the boundary of the chapter—what the integral prepares for the fundamental theorem of calculus (the telescope, grid-FTC as a bridge, a brief survey of the rules that Chapter 5.6 will unfold). § 5.7: computational examples. § 5.8: the summary.

{ The supporting files have two anchors: `RiemannIntegration.v`, the core of finite Riemann sums, and `ProcessIntegral.v`, the process built from these sums. Additional layers: `StepIntegral.v` (the exact integral of piecewise constant functions) and demonstration files with examples; `IntegralApplications.v`, with the rules of the integral, we will only name in § 5.6, leaving its analysis to Chapter 5.6. The caveat on the status of axioms—with the important case of `ProcessArithmetic.v`, where the header diverges from the fact—the chapter gives in § 5.8.}

## The Integral of Simple Functions

### The Integral of a Constant

Let us test the definition on the simplest case—a constant function. Formally, the lemma `integral_process_const` states an equivalence of processes:

$$
`integral_process`\;(\lambda_. c)\;a\;b
\;\sim\;
`const_process`\;\bigl(c\cdot(b-a)\bigr),
$$

that is, the process of the integral of the constant $c$ is equivalent to the constant process with value $c\cdot(b-a)$. It is worth stating precisely: the result is expressed through the equivalence of processes (`process_equiv`), although the proof shows even a *pointwise zero* gap at each level. Indeed, at level $n$ the Riemann sum of the constant is $c\cdot(n+1)\cdot`step`$ (by `riemann_sum_const`), and the product $(n+1)\cdot`step`$ equals exactly $b-a$ (by `grid_width_eq`); therefore the difference from $c\cdot(b-a)$ is zero at every $n$, and not only in the limit.

In substance this is the familiar area under a horizontal line: height $c$ times width $b-a$, exactly and at once. And this is the only class where integrability in the sense of § 5.1.4 is visible immediately—without any grid estimates: the process is already constant.

### The Width of the Grid

The fact on which the previous subsection relied deserves a line of its own. The integral of the unit function is the total width of the grid:

$$
`riemann_sum`\;(\lambda_. 1)\;a\;`step`\;n
\;=\; n\cdot`step`
$$

(the lemma `riemann_sum_width`), and on a grid of $n+1$ subintervals with step $(b-a)/(n+1)$ this gives exactly $b-a$ (`grid_width_eq`). That is, the total width of the grid is exactly equal to the length of the interval, *independently* of the level of refinement. This is the “normalization” on which all the estimates of § 5.4 and § 5.5 later rest: however many rectangles we take, their total width is one and the same.

### The Exact Integral of Piecewise Constant Functions: Step Functions

There is also an entirely different construction of the integral, requiring neither a grid nor refinement—the integral of *piecewise constant* functions. It lives in the file `StepIntegral.v`. A step function is a finite sum $f=\sum_i c_i\cdot\chi_{[a_i,b_i]}$; in the code its element is given by a record with a value field and two endpoints:

```coq
Record Step := mkStep {
  step_val : Q;
  step_left : Q;
  step_right : Q;
  step_valid : step_left <= step_right
}.

Definition step_integral (s : Step) : Q :=
  step_val s * (step_right s - step_left s).
```

The integral of a step function, `step_fun_integral`, is the sum $\sum_i c_i (b_i-a_i)$ over a finite list of steps. It is an *exact* rational number, with no limit or refinement at all: a finite sum over a finite list. The examples from the file are direct: the integral of the constant $c$ on the interval is $c$ (`integral_constant`); the integral of the indicator $\chi_{[0,1/2]}$ is $1/2$; the integral of the function “$2$ on $[0,1/2]$ and $3$ on $[1/2,1]$” is $5/2$ (`integral_two_step`).

Let us name the role precisely (safeguards C1 and C4). This is an *exact* construction—neither a process nor a grid limit; and it uses its own record `Step`, separate from the Riemann sums—a parallel line. The file header calls it a “P4-compatible measure theory: integration first, measure derived” and “the foundation of Bishop–Cheng measure theory.” This is worth speaking of as a *bridge*, not as a built measure: step functions are the foundation of a future measure; the integration of piecewise constant functions is already built, but general measure itself and the $L^1$ completion are the subject of the following parts. Here we only note the exact line and do not mix it with the process.

### Two Constructions of the Integral

So we have two constructions before us. Step functions give an *exact* integral where the function is piecewise constant: a finite sum, without approximation. Riemann sums give a *process* of approximations for an arbitrary $ℚ$-function: a grid being refined.

The connection between them is simple and instructive. The Riemann sum at level $n$ is exactly the integral of a step function approximating $f$ on the grid: each rectangle of the sum is a step of constant height. That is, the process `integral_process` is a sequence of exact integrals of ever denser step approximations of the function $f$. The exact line and the process line are two sides of one thing rather than rivals: at each level the process *is* an exact step integral, and the integral of $f$ itself is the process of these exact values. In the analysis of § 5.1.5 these are two representations of one role-integral: the exact one (step) and the process one (Riemann sums).

Let us add a caveat on the status of this connection (an honest remark). In the repository it is set out as a *mathematical reading*, not as a proved lemma: the supporting files of the chapter have no separate theorem identifying `riemann_sum` with the `step_fun_integral` of a specially built step function, and `StepIntegral.v` and `RiemannIntegration.v` exist as two parallel lines (one over lists of `Step`, the other over `walk_point` grids). Such a lemma would be a natural future bridge between them. We will return to the convergence of the process of sums in § 5.5.

## The Linearity of the Integral

### Additivity and the Scalar

The first substantive property of the integral is linearity. At the level of the finite Riemann sum these are two identities, true on *every* grid. A sum of functions gives a sum of sums:

$$
`riemann_sum`\;(\lambda x. f x + g x)\;a\;`step`\;n
\;=\;
`riemann_sum`\;f\;a\;`step`\;n
+ `riemann_sum`\;g\;a\;`step`\;n
$$

(the lemma `riemann_sum_add`); a scalar multiple can be pulled out: $`riemann_sum` (\lambda x. c\cdot f x) = c\cdot
`riemann_sum` f$ (the lemma `riemann_sum_scale`). Both are proved by a short induction on the number of nodes: at each step a ring identity for rational numbers does the work.

At the level of the process these identities are lifted verbatim: `integral_process_add` and `integral_process_scale` give additivity and homogeneity pointwise at each level, and `integral_linearity_process` joins them into one: $\int(c\cdot f + g) = c\cdot\int f + \int g$. Safeguard C1: on the finite sum this is an *exact* identity; on the process, a pointwise equality at each level. In substance the integral is linear for the same reason that a sum is linear: the Riemann sum is a linear combination of the values of the function with widths as weights.

### The Difference

{ The difference is derived from the sum and the scalar rather than proved anew. The lemma `riemann_sum_negate_fn` gives $`RS`(-f) =
-`RS`(f)$, and `riemann_sum_sub` gives $`RS`(f-g) =
`RS`(f) - `RS`(g)$. Both are obtained by rewriting through `riemann_sum_ext`—the extensionality lemma: if $f$ and $g$ coincide at the nodes of the grid, their Riemann sums are equal. This is the same economy of means as with the difference rule of the derivative in § 5.4: each next identity is set on top of those already proved. Safeguard C4, on sources: `riemann_sum_sub` and `riemann_sum_negate_fn` belong to the FTC layer of the repository—the file `analysis/FTC.v`; the extensionality lemma `riemann_sum_ext` lives in `IntegralApplications.v`. What matters for the chapter in substance is this: the difference is derived from additivity and scaling rather than proved anew.}

### What the Linearity of the Integral Means

Linearity reflects the fact that the Riemann sum is a linear combination of the values of the integrand; it is no accident. And it is *dual* to the linearity of the derivative from § 5.4: differentiation carried linear operations on functions into linear operations on slopes, integration carries them into linear operations on areas. Both operations of analysis are linear, and the fundamental theorem (Chapter 5.6) will link them into one. For now this is the first bridge forward: that the integral and the derivative behave alike with respect to addition and the scalar is a sign of their coming kinship, not a coincidence. In the terms of § 5.1.5 this is an E/R/R duality: the integral and the derivative share a role pattern (a process converging to a value) under dual rules.

## Monotonicity and Nonnegativity

### Monotonicity

{ The integral preserves order. The lemma `riemann_sum_monotone` states: if $f\le g$ at all nodes of the grid and the step is nonnegative, then $`riemann_sum` f \le `riemann_sum` g$. At the level of the process this is `integral_monotone`: from $f\le g$ on the grid follows $`integral_process` f \le `integral_process` g$ pointwise. The proof is induction on the number of nodes: at each step $f(x_k)\cdot`step`\le g(x_k)\cdot`step`$, since the factor `step` is nonnegative. Safeguard C1: on the finite sum, an exact inequality; on the process, a pointwise one. In substance: a larger integrand covers a larger area.}

### Nonnegativity: Motif M4

{ A special case of monotonicity is the key motif of the whole of Part V. The lemma `riemann_sum_nonneg`: if $f\ge 0$ at all nodes of the grid and the step is nonnegative, then $`riemann_sum` f\ge 0$. This is the *fourth* recurring motif of Part V (M4): the integral of a nonnegative function is nonnegative. It follows from monotonicity with $g=f$, $f=0$, or is proved by direct induction.}

In substance the motif is simple: the area under a nonnegative graph is nonnegative. But it is precisely the basis for the integral’s defining a *measure*: a positive linear functional taking nonnegative functions to nonnegative numbers. This is a bridge to Part VI, where general measure will grow out of the integral of piecewise constant functions. M4 here is the order law for the sake of which the integral is fit to be the foundation of measure at all, not a technical detail. In the analysis of § 5.1.5, M4 is the rule (Rule) by which the integral is a positive functional.

### The Nonnegativity of the Norm of Step Functions

The same motif M4 also shows itself in the exact step line. The $L^1$-norm of a step function is defined as the integral of its absolute value, $\lVert f\rVert_1 = I(|f|)$, and the lemma `norm_nonneg` states $\lVert f\rVert_1\ge 0$. Together with `step_integral_nonneg` (the integral of a nonnegative step is nonnegative) this shows: the law M4 is one for both lines—the process-grid line (`riemann_sum_nonneg`) and the exact step line (`norm_nonneg`). One and the same order law of the integral shows itself twice, on two different constructions—as befits a fundamental property.

### Upper and Lower Estimates

Order also gives quantitative estimates. The lemma `riemann_sum_abs_bound`: if $|f|\le M$ at the nodes, then $|`riemann_sum` f a `step` n|\le M\cdot
n\cdot`step`$. The lemma `riemann_sum_global_bound`: for $\mathrm{lo}\le f\le \mathrm{hi}$ at the nodes, the sum of $n$ terms is squeezed between $\mathrm{lo}\cdot n\cdot`step`$ and $\mathrm{hi}\cdot
n\cdot`step`$. These are estimates of an arbitrary finite sum with $n$ subintervals. In the integral process at level $n$ the number of subintervals equals $S n$ (that is, $n+1$), and the normalization is this: $(S n)\cdot`integral_step` a b n = b-a$ (`grid_width_eq`). Substituting, we obtain for the finite sum of the process $`RS`_n$:

$$
|`RS`_n(f)| \le M\cdot(b-a),
\quad
\mathrm{lo}\cdot(b-a) \le `RS`_n(f) \le \mathrm{hi}\cdot(b-a).
$$

They are worth formulating *exactly so*—as estimates of the *finite sum* $`RS`_n$, theorems about a particular level, not about the limiting integral. As estimates of the integral—$|\int f|\le M\cdot(b-a)$ and so on—they are read *after* the process of sums has been accepted as the integral’s representative in the Cauchy sense (§ 5.1.4, § 5.5). Safeguard C1: the estimates on the finite sum are exact and unconditional; the integral reading is secondary and conditional. These estimates prepare the convergence estimate of § 5.5.

## Convergence: Integrability as the Cauchy Property

### The Telescope and the Connection with the Derivative

{ To understand when the process of sums converges, let us begin with a construction that connects the sums with the increment of the function—the telescoping sum. Let us define $`tele_sum` f a `step` n =
\sum_{k=0}^{n-1}\bigl[f(y_{k+1})-f(y_k)\bigr]$, the sum of the increments of $f$ over consecutive nodes $y_k=`walk_point` a `step` k$. The lemma `telescope_collapse` collapses it exactly:

$$
`tele_sum`\;f\;a\;`step`\;n \;=\;
f(y_n) - f(a).
$$

The sum of the increments over the nodes equals the total increment from $a$ to the end of the grid—and this coincidence is *Leibniz-exact*, because the nodes are given by the recursive `walk_point` of § 5.4 rather than by the formula $a+ks$ (the same honest detail that was examined in the chapter on the derivative).}

The connection with the derivative is given by the lemma `rs_tele_error_bound`: if $f$ is uniformly differentiable on $[a,b]$ with derivative $f'$ (`udiff_on` from § 5.4), then the difference between the Riemann sum of $f'$ and the telescoping sum of $f$ is small—there is a level $N$ at which it does not exceed $\varepsilon\cdot(b-a)$. Safeguard C1: this is an estimate with a choice of level, an $\varepsilon$-grid form. The proof is an inner induction on the number of steps of the grid; at each step the bound from uniform differentiability does the work.

### grid-FTC: The Riemann Sum of the Derivative Approximates the Increment{grid-FTC: the Riemann sum of the derivative approximates the increment}

Joining the telescope with its collapse, we obtain the grid form of the fundamental theorem of calculus—the lemma `ftc_grid`. If $f$ is uniformly differentiable on $[a,b]$ with derivative $f'$, then for every $\varepsilon>0$ there is a level $N$ at which

$$
\bigl| `riemann_sum`\;f'\;a\;`step`\;(N{+}1)
\;-\; \bigl(f(y_{N+1}) - f(a)\bigr) \bigr|
\;\le\; \varepsilon\cdot(b-a).
$$

{ Here $N{+}1$ corresponds to `S N` in the code. In substance: the sum of the values of the derivative over the grid approximates the total increment of the function. The proof is direct: `rs_tele_error_bound` estimates the distance from the telescope, and `telescope_collapse` identifies the telescope with the increment $f(y_{N+1})-f(a)$.}

Let us name the status honestly (safeguard C1). This is the *grid, approximate* form of the classical equality $\int_a^b f' = f(b)-f(a)$, *not* that equality itself: for a fine enough grid the sum of the derivative is arbitrarily close to the increment. The fully unfolded fundamental theorem of calculus—its exact grid-process formulation and its corollaries—is the subject of Chapter 5.6; here `ftc_grid` serves as a *bridge*, showing that refinement really does bring the sum closer to the increment.

### Integrability as the Cauchy Property of the Process{Integrability as the Cauchy property of the process}

Now we can say what “the function is integrable” means in the process sense. It means that the process `integral_process` is a *Cauchy* process: its values at different levels draw closer as the grid is refined. Then the candidate process of § 5.1.4 becomes a legitimate integral—a converging process with a stable value. For some sufficiently regular classes this behavior is already supported by grid estimates. In particular, `ftc_grid` controls the Riemann sums of the derivative of a uniformly differentiable function through the increment of the function itself (§ 5.5.2). A more general statement—about the Cauchy convergence of `integral_process` for *all* Lipschitz or *all* continuous functions—would require a separate theorem, which the supporting files do not have.

Here a terminological safeguard is needed. We use the word “integrability” as a *process reading* of the infrastructure, not as a predicate already introduced in the repository. The core has *no* separate predicate `is_riemann_integrable` with proved general properties, and *no* single theorem “the process `integral_process` is Cauchy for all continuous functions.” What it has is grid estimates for particular classes, from which the Cauchy property is assembled for a particular function. Such a predicate could be introduced later as a generalization of the current infrastructure—but the reader should not look in the code for a central predicate of integrability: it is not there, and this is an honest boundary. (Here also `ProcessArithmetic.v` comes into play, with the preservation of the Cauchy property under operations—and its caveat about `classic`, to which § 5.8.3 will return.)

### Refinement without Completed Infinity

One last brick remains—that refinement really reaches any precision. The lemma `integral_step_vanishes`: for every $\delta>0$ there is a level $N$ at which the step of the grid is smaller than $\delta$. It relies on the Archimedean property—specifically on the lemma `nat_above_Q` from the process layer of the derivative (§ 5.4). A kindred Archimedean lemma `q_archimedean` exists in `ProcessArithmetic.v`, but it is a different technical route (monotone bounded processes), and `integral_step_vanishes` does not use it. In a *finite* number of subdivisions the step becomes as small as desired.

{ This is the same intonation as in § 5.1 (the scale of processes is arbitrarily fine) and § 5.4 (`walk_step_small`). Under $P4$ “refinement to infinity” is a process, not a completed infinity: each level is finite, at each level the grid has a finite number of nodes, and the limit is not taken as a separate object. The integral *is* a process of ever finer finite partitions; it does not wait for an “infinitely fine partition.”}

## The Boundary of the Chapter: What the Integral Prepares for the FTC

### The Telescoping Sum as a Bridge to the Derivative

This chapter builds the integral and its basic properties; the fully unfolded fundamental theorem of calculus and its corollaries are the subject of the next chapter. Here we only outline the boundary: what is already ready and what will unfold further.

The constructive kernel of the future theorem is already in hand—the telescope of § 5.5.1. The lemma `telescope_collapse` collapses the sum of the increments of a function over the nodes of the grid into the difference of the endpoints, $f(y_n)-f(a)$. This is the idea of the fundamental theorem in embryo: the accumulation of the increments of a function equals its total change. The integral of the derivative and the increment of the function are connected by the telescope—it remains to turn this connection into a theorem, which Chapter 5.6 will do.

### grid-FTC as a Preliminary Form

The second ready brick is `ftc_grid` from § 5.5.2. Let us stress its status once more: it is the *preliminary*, grid form of the fundamental theorem—the inequality $| `RS`(f') - (f(\text{end})-f(a)) |\le\varepsilon\cdot(b-a)$, not the exact equality $\int f' = f(b)-f(a)$. Safeguard C1: an $\varepsilon$-grid form. Chapter 5.5 does *not* prove the unfolded theorem and its corollaries—it only carries matters as far as the grid bridge, on which the next chapter will build the exact connection.

### The Rules the Next Chapter Will Unfold

Let us name—precisely name, without analyzing—what Chapter 5.6 will build on top of grid-FTC. The file `IntegralApplications.v` contains the product rule for the integral (`udiff_product`, with the same $\varepsilon/3$-decomposition `product_decomp` as the product rule of the derivative in § 5.4), integration by parts (`integration_by_parts` and its special case `ibp_self`), and the uniqueness of the antiderivative (`antiderivative_unique`: two functions with one derivative have equal increments—a grid parallel to the fact that a zero derivative means near-constancy, § 5.4). All these theorems have been checked and exist in the repository—but their natural place is the chapter on the fundamental theorem of calculus. Here it suffices to note that the infrastructure for them is ready: grid-FTC, the linearity of the sums, and uniform differentiability are already in place.

### Why the General Change of Variables Is Not Yet Built

{ One boundary deserves special mention—the change of variables. The core has no general chain rule, as already noted in § 5.4; it has only the *affine* case: `udiff_chain_affine` for the inner function $g=c\cdot x+d$, and on it the affine substitution in the integral (`ftc_u_substitution_affine`). That is, substitution is formalized only for a linear change of variables; the general substitution $u=g(x)$ with an arbitrary smooth $g$ is not. This is an honest boundary, outlined concretely: Chapter 5.6 will unfold the rules of the integral within the proved limits, without attributing to the theory more than it contains.}

## Computational Examples

### The Integral on the Interval [0,1]: The Process in Numbers

The process integral is good in that at each level it gives a concrete rational number that can be computed. The file `ProcessIntegration.v` does this explicitly on the interval $[0,1]$: its own sum `riemann_sum_01` with $K+1$ nodes and the integral `process_integral_01` $f K$ at level $K$. The examples are proved by direct computation (`vm_compute`): the integral of one, $\int_0^1 1$, equals $1$ at the levels $K=0,1,2$; the integral of zero equals zero; the integral of two equals $2$. At each level there is an exact rational value, machine-checkable.

{ Safeguard C4: this is a *separate* `riemann_sum_01` on $[0,1]$, distinct from the main `riemann_sum` over `walk_point` of § 5.1.3. The file is a demonstration; we use it as an illustration that “the integral computes,” not as the main theory.}

### Calculus as a Process: A Demonstration

The file `ProcessAnalysis.v` goes further still—an unfolded demonstration of “calculus as a process over $ℚ$” without any $\varepsilon$-$\delta$, on rational computations alone. The derivative of the square there is the process `process_derivative` $f_square$, equal to $2x+1/(K+1)$; at the point $x=1$ it gives $3,\ 5/2,\ 21/10,\ 201/100$ at the levels $K=0,1,9,99$—one can see how the values approach $2$. The integral $\int_0^1 1$ equals $1$ at every level. The concluding `process_analysis_foundation` gathers these examples into one statement.

Here safeguard C4 is especially important. The file `ProcessAnalysis.v` contains *its own* `process_derivative`, `riemann_sum`, and `process_integral`—definitions *different* from those in `ProcessDerivative.v` and `RiemannIntegration.v`, although the names coincide. It is a self-standing demonstration file; its `process_integral` should not be confused with the main integral of the chapter. We cite it as a vivid illustration, not as an anchor of the theory.

### What the Examples Show

The examples confirm the main thesis of the chapter vividly. The integral and the derivative under $P4$ are processes, and each level of such a process is an exact rational computation, checkable by machine, without recourse to completed infinity. The values approach the classical ones—$2$ for the derivative of the square at one, $1$ for $\int_0^1 1$—but the approximation itself is the object: the process, not its limit. Where classical analysis says “the limit equals two,” the Theory of Systems says “the process $3, 5/2, 21/10, 201/100,…$”—and this is enough, because under $P4$ a number *is represented* by such a process, and a point-number in the strict sense is read as a class of equivalent processes (as was specified in Chapters IV.3–IV.4).

## What Has Been Built and What Is Being Prepared. Summary of the Chapter

### The Summary in Three Columns

Let us gather what has been done in infrastructure mode.

**Built and checked:**

- the integral as a *process* of accumulation `integral_process` (step $(b-a)/(n+1)$); the finite Riemann sum `riemann_sum` on the walk grid; `integral_is_process_construction`;
- the *exact* integral of step functions `step_fun_integral`—the foundation of a future measure;
- linearity (addition, scalar, difference)—on the finite sum and on the process;
- monotonicity; nonnegativity—motif M4 (`riemann_sum_nonneg`, `norm_nonneg`);
- estimates of the sums (`abs_bound`, `global_bound`); the telescope (`telescope_collapse`); the grid bridge grid-FTC (`ftc_grid`);
- computational examples ($\int_0^1$ at different levels).

**Not built in this chapter:**

- a more developed formulation of the fundamental theorem of calculus $\int_a^b f' = f(b)-f(a)$ and its corollaries—only the grid form `ftc_grid` is proved here; the rest is Chapter 5.6 (which, judging by the supporting files, also works in the grid walk-point framework rather than reaching at once the exact equality on classes);
- the product rule, integration by parts, and the uniqueness of the antiderivative as unfolded theorems—they exist in `IntegralApplications.v`, but their place is Chapter 5.6;
- the integral of a function on the classes `RealPoint`—here only $ℚ$-functions (safeguard C2);
- the general change of variables—only the affine case is formalized;
- the Lebesgue integral and general measure—step functions are only the foundation (Part VI);
- the improper integral as a process of extending the domain—a natural future extension, not the subject of this chapter.

**Prepares next:**

- the fundamental theorem of calculus (Chapter 5.6): the unfolded grid-process connection of the derivative and the integral through `ftc_grid`, `udiff_product`, integration by parts;
- Fubini (Chapter 5.7): 2D step functions;
- measure (Part VI): step functions as the Bishop–Cheng $L^1$ foundation.

### What Would Remain for the Integral on Classes

The chapter has honestly confined itself to functions $ℚ\toℚ$. Let us name concretely which step is missing for an integral on the quotient classes `RealPoint`—just as § 4.8 named the missing link for the derivative. It would be necessary, first, to prove that `integral_process` is well defined with respect to the equivalence of processes—that the integral does not change when the integrand is replaced by an equivalent one; second, to lift the definition from $ℚ$-functions to functions of quotient classes. The supporting files do not contain this—an honest boundary, outlined concretely.

### A Caveat on the Status of Axioms

{ The Part V safeguard requires precision about axioms. The cores—`ProcessIntegral.v`, `RiemannIntegration.v`, `IntegralApplications.v`—declare “none” or “0 axioms” in their headers, but they import layers in which classical logic occurs: `EVT_idx.v` (with a local `classic`, from § 5.3) and `ProcessArithmetic.v` (see below). `Differentiation.v` and `MeanValueTheorem.v` themselves also declare the absence of axioms in their headers—so the matter lies not in them as such but in the fact that transitive imports may pass through files with classical logic. This does not mean that every integral lemma depends on `classic`; it means that the status of each particular theorem has to be checked with the command `Print Assumptions`.}

A special case deserves direct mention. The file `ProcessArithmetic.v` declares “AXIOMS: none” in its header, but imports `Stdlib.Classical` and *uses* `classic` in the proof of `monotone_bounded_Cauchy`—the header directly diverges from the fact. And the main anchor `ProcessIntegral.v` imports `ProcessArithmetic.v`. The precise—and not wholesale—formula is this: the fact of the import by itself does *not* yet mean that every integral theorem depends on `classic` (many may not), but the file header “0 axioms” is *not* a sufficient audit—the status of a particular theorem is established only by the command `Print Assumptions` for that theorem itself. This is the strongest argument for the recurring rule C3. No wholesale statement should be made in either direction.

{ `Print Assumptions` is written out at the end of `RiemannIntegration.v` for `ftc_grid`, `udiff_add`, `ftc_comparison`. For files without such a final block, the status of a particular theorem is checked separately when needed. Genuinely constructive (importing only the Rocq stdlib or `ProcessCore`, without the classical layer) are `StepIntegral.v`, `ProcessIntegration.v`, and `ProcessAnalysis.v`; `StepIntegral.v`, moreover, is short and declares “20 Qed, 0 Admitted, 0 axioms.” And one more honest fact for completeness: the name `riemann_sum` is borne by three different definitions in three files.}

### Summary of the Chapter

The chapter has built the integral—the analytic layer dual to the derivative of § 5.4. The main turn lies in how the concept itself is arranged. The integral is a *process of accumulation* of Riemann sums, not a completed limit: the finite sum at each level is exact and rational, and the process gathers the refinement of the grid. The process itself exists for any $ℚ$-function and serves as a *representative* of the integral; its legitimacy as an integral is given by convergence—the Cauchy property, which for particular regular classes of functions is assembled from grid estimates. The main caution: grid-FTC is a grid form; the unfolded connection of the derivative and the integral will be the subject of Chapter 5.6; step functions are the foundation of measure, not measure itself.

*Built: the integral-process `integral_process` and the finite Riemann sum; the exact integral of step functions; linearity, monotonicity, nonnegativity (M4); estimates, the telescope, and the grid bridge grid-FTC; computational examples.*

*What it stands on: the walk points and uniform differentiability of § 5.4, the Archimedean property as the fuel of refinement, and the process ontology of $P4$, in which the integral is a process of accumulation of sums, not a completed limit of them.*

*Next: the fundamental theorem of calculus (Chapter 5.6), linking the derivative and the integral; Fubini for 2D step functions (Chapter 5.7); general measure on the foundation of the step integral (Part VI).*

---

[^1]: The E/R/R labeling is in the headers of the files `ProcessIntegral.v` (elements, role) and `StepIntegral.v` (rules); here it is unfolded on the pattern of Part I.

---

Part: [[05 Topology and Analysis of Processes|Part V. Topology and Analysis of Processes]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/04 Derivative|Chapter 4. The Derivative]] · [[Library/Branches/Mathematics/Volume/05 Topology and Analysis of Processes/06 Fundamental Theorem of Calculus|Chapter 6. The Fundamental Theorem of Calculus]] →
