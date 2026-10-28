---
title: "Chapter 2. Euler’s Method: The Solution on a Grid"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/08 Обыкновенные дифференциальные уравнения/02 Метод Эйлера решение на сетке.md"
sourceBlob: 54039b13cae916d1814560207ad5ca1cd813fd4b
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### From the Framework to the First Process

Chapter 8.1 set the ontological framework: the solution of the Cauchy problem is a process of approximations, and existence is the property of this process to converge, not the presence of a completed function. The present chapter presents the *simplest* such process in full concreteness: Euler’s method on a rational grid. There is not a single passage to the limit here: everything that is built consists of finite rational numbers, computable by exact arithmetic over ℚ.

Euler’s method is the most direct way to make the equation $y' = f(t,y)$ *work*. We divide the interval into $N$ equal steps and at each node take a step along the tangent whose slope the right-hand side sets. The result is a polygonal line approximating the solution; its nodes are rational numbers, and the whole polygonal line is a process indexed by the step number. This chapter will show how the method behaves on three reference equations (linear, quadratic, exponential) and, what matters most conceptually, will *strictly separate two different indices* that classical analysis merges in a single passage to the limit.

### What This Chapter Claims—and What It Does Not

The proved core is concrete and arithmetic. The Euler trajectory is defined as a recursion over ℚ; its values on the reference equations are computed exactly: for the linear equation the method is *exact*, for the quadratic one it gives an explicit rational error, and for the exponential one it gives the sequence $(1+1/N)^N$ of rational approximations, bounded below by two and above by three.[^1]

What the chapter does *not* do: it does not take the limit $N\to\infty$ as a completed object, does not claim that Euler *converges* to the exact solution as to a ready function, and does not present $e$ as a completed transcendental. The refinement of the grid is a direction of the process, not a finished object; the exact solution and the number $e$ are role-limits.

Three levels of rigor, as in Chapter 8.1. The *first* is the concrete rational trajectories and their exact values over ℚ: proved without axioms. The *second* is the process *readings*: the grid as resolution, the step number as stage, the polygonal line as the solution process, refinement as an increase in precision. The *third*—the exact solution and $e$ as completed objects—is role-limits. The chapter treats the first two as proved, and the third as an honestly marked boundary.

### The E/R/R Framework of the Chapter

The framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.” The chapter introduces the system of *Euler grid approximation*.

**Rules ($\leftrightarrow$ L5).** The grid $t_k = k/N$ divides the interval into $N$ equal parts; the Euler step $y_{k+1} = y_k + h f(t_k, y_k)$ with $h = 1/N$ builds the polygonal line from the initial value; refining the grid ($N$ grows) decreases the step. For equations without curvature (linear ones) the method is exact; the curvature of the right-hand side generates a rational error at each step.

**Roles ($\leftrightarrow$ L4).** The grid resolution $N$ is the role-resolution (how fine the grid is); the step number $k$ is the role-stage (how far in time); the step $h = 1/N$ is the role-increment; the polygonal line is the role-process (an approximation of the solution); the error is the role-defect (the curvature left unaccounted for over a step); the exact solution and $e$ are the role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The rational nodes
$t_k$, the values of the trajectory $y_k$, the finite resolution $N$, the finite index $k$. Under P4 neither the limit of refinement nor $e$ is an element: only finite grids and finite stages are actual.

## The Rational Grid and the Euler Step

We fix the resolution, a natural number $N \ge 1$, and divide the unit interval into $N$ equal parts. The grid nodes are rational:

$$
t_k \;=\; \frac{k}{N}, \quad k = 0, 1, …, N,
$$

and the step between neighboring nodes is $h = 1/N$.[^2] Euler’s method turns the equation into a *recurrence rule*: knowing the value at a node, we take a step along the tangent that the right-hand side sets at this point,

$$
y_{k+1} \;=\; y_k + h  f(t_k, y_k),
$$

starting from $y_0$, the given initial condition.[^3] This definition is a literal *recursion* over ℚ: each next value is obtained from the previous one by a single rational step, and the whole sequence $y_0, y_1, y_2,
…$ is a process in the exact sense of the volume: a map from the stage number to a rational approximation.

*The Euler trajectory is not a table of values of a ready function but a role-process: a rule that unfolds the initial condition into a sequence of rational stages. Each stage is a finite snapshot; the whole polygonal line is an unfolding process, not a completed object.*

## Two Indices: Grid Resolution and Stage Number

Here is the conceptual heart of the chapter. *Two* natural indices take part in the definition of the trajectory $y_k$, and they play *different* roles:

- $N$ is the *grid resolution*: into how many parts the interval is divided. It sets the step $h = 1/N$. The larger $N$, the finer the grid and the more closely the polygonal line follows the true slope.
- $k$ is the *stage number*: at which grid node we are, that is, how far we have advanced in time, $t_k = k/N$.

Classical analysis takes the limit $N \to \infty$ and in this limit *merges* both indices: one simply says “the solution at the point $t$,” forgetting through which grid and in how many steps it was obtained. The process viewpoint keeps the indices separate, because they are *different roles*. Advancing in $k$ with $N$ fixed is movement *in time* along a given grid. Growth of $N$ is the *refinement* of the grid itself. These are two independent directions, and they can be mixed only at the cost of losing constructive meaning.

The distinction is not pedantry: it is written directly into the definition of the trajectory. The call `euler_traj f y0 N k` takes both indices separately, and the step $h = 1/N$ depends on the resolution, not on the stage number.[^4] The two reference regimes below show this clearly: for the exponential we grow $N$ (we refine the grid while holding the final time $t=1$, that is, $k = N$); for the linear and quadratic equations we advance $k$ along the fixed grid $N = 4$.

*The resolution $N$ and the stage number $k$ are two different roles: $N$ is the role-resolution (how fine the step is), $k$ is the role-stage (how far in time). The completed solution of classical analysis merges them in the limit; the process keeps them separate, and it is precisely this that makes every approximation finite and computable.*

## Three Trajectories

### The Linear Equation: Euler Is Exact

Take $y' = 1$, $y_0 = 0$. The exact solution is $y(t) = t$. Euler’s method on the grid $N = 4$ gives values that coincide *exactly* with the solution at the nodes: $y_1 = 1/4$, $y_2 = 1/2$, $y_4 = 1$.[^5] The reason for the exactness is simple: the slope is constant, the tangent *coincides* with the graph, and a step along the tangent accumulates no error. For equations without curvature Euler’s method does not approximate the solution but *reproduces* it.

### The Quadratic Equation: An Explicit Rational Error

Now $y' = 2t$, $y_0 = 0$, with the exact solution $y(t) = t^2$. Here the right-hand side *changes* along the step, and Euler’s method, which freezes the slope at the start of the step, lags behind. On the grid $N = 4$ at the final moment $t = 1$ the method gives $3/4$, whereas the exact value is $1$; the error is exactly $1/4$.[^6] What is essential is that the error is a *finite rational number*, not a vague “tends to zero.” The method underestimates the solution (a convex curve outruns its tangents), and the measure of this lag on each concrete grid is computed exactly. Reducing the error means *refining the grid*, growing $N$: the next direction of the process, not a finished limit.

### The Exponential Equation: The Path to $e$

Finally, $y' = y$, $y_0 = 1$, with the exact solution $y(t) = e^t$. The Euler step is especially transparent here: since $f(t,y) = y$, each step multiplies the value by $(1 + h)$,

$$
y_{k+1} = y_k + h y_k = y_k (1 + h),
$$

so that after $N$ steps of size $h = 1/N$ the value at the moment $t = 1$ is $(1 + 1/N)^N$.[^7] Growing the resolution, we obtain a sequence of rational approximations:

$$
N = 1:\ 2; \quad N = 2:\ \tfrac{9}{4} = 2.25; \quad
  N = 4:\ \tfrac{625}{256} \approx 2.441,
$$

growing toward $e$; for the stages shown both the exact values and the bounds are checked, in particular $2 < 625/256 < 3$.[^8] This is the famous path to the number $e \approx 2.718$—but a path, not a destination: each $(1+1/N)^N$ is a rational Element, computable exactly, and $e$ is the role-limit toward which the process of refinement is directed.

## The Sequence $(1+1/N)^N$ as a Process toward $e$

The exponential regime deserves a separate word, because in it the process ontology of the volume is seen with particular sharpness. The sequence $(1+1/N)^N$ is *not* the completed number $e$ with a “tail of approximations” but the process itself, whose stages are the rational numbers $2, 9/4, 64/27, 625/256, …$ Each stage is finite and presentable; none equals $e$; and convergence is a property of the process (monotone growth, boundedness above), not a finished object at its end.

This is exactly the same device as for the $e$-process as the solution of $y' = y$ (Chapter 8.5): the sequence there, $(1+1/(N{+}1))^{N+1}$, is the same ladder of rational stages, and it is proved that it *is* the Euler trajectory of the equation $y' = y$ at $t = 1$ and is bounded below by two *for all* $N$ (by Bernoulli’s inequality); the growth is checked at concrete stages.[^9] Full monotonicity for all $N$ and the bound $< 3$ for all $N$ (via the binomial theorem) are not proved in our formalization: this is the honest boundary of the present layer; the explicit number $e$ as a completed transcendental is a role-limit. What is proved is concrete: individual rational stages, the lower bound ${}\ge 2$ for all $N$, and checkable upper bounds for the stages shown; the completed $e$ is not built.

*The number $e$ is not a completed object to which a convergent sequence is “glued” but the role-limit of a rational process. To ask “what does $e$ equal” is to ask “what process sets it”; the answer is the Euler trajectory of the equation $y' = y$, the ladder $(1+1/N)^N$ of rational stages. The stage is actual; $e$ is a direction.*

## E/R/R Analysis: The Euler Polygon as a Role-Process

### Setup

Let us analyze the constructed system—the Euler grid approximation—in terms of E/R/R. A reservation about the level: the “system of approximation” here is a substantive *interpretation* of the construction (the grid plus the recurrent step plus refinement), not an object literally declared in the code as `System`. The analysis is an ontological comprehension of the structure of the chapter and a reading of the author’s E/R/R header of the supporting file,[^10] not an attribution of new formal claims to the code.

As before, the abbreviation E/R/R sets the epistemic order (Elements $\to$ Roles $\to$ Rules, from the observable to the deep), while the generating order is the reverse: Rules $\to$ Roles $\to$ Elements. Epistemically we went from observable rational values to the rule of their generation; we conduct the analysis in the generating order.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation are the grid $t_k = k/N$ and the recurrent Euler step $y_{k+1} = y_k + h f(t_k, y_k)$ with $h = 1/N$, which unfolds the initial condition into the polygonal line. Above it is the rule of refinement: growth of the resolution $N$ decreases the step and brings the polygonal line closer to the true slope. The behavior of the method is governed by the curvature of the right-hand side: in its absence (the linear equation) the method is exact; in its presence the method generates a rational error whose measure is computable on each grid. The universal layer of these rules is the laws L1–L5; the concrete layer is the formula of the step and the dependence $h = 1/N$.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The resolution $N$ is the role-resolution: how fine the grid is. The stage number $k$ is the role-stage: how far in time. The step $h = 1/N$ is the role-increment. The polygonal line is the role-process: an approximation of the solution, unfolded stage by stage. The error between Euler and the exact value is the role-defect: the curvature left unaccounted for over a step. And the exact solution and the number $e$ are the role-limit: the direction of refinement, not actualized as a completed object.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The roles select
bearers, and the bearers here are finite: the rational nodes $t_k = k/N$, the values $y_k$, the finite resolution $N \in ℕ$, the finite index $k \in ℕ$. Under P4 neither the limit of refinement nor $e$ is an element: only finite grids and stages are actual; what is actualized is the process of refinement, not its completed limit.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| grid $t_k=k/N$; step $y_{k+1}=y_k+hf(t_k,y_k)$, $h=1/N$; refinement $N{\uparrow}$ | HOW the polygonal line is built and refined | Rules ($L5$) |
| resolution $N$; stage $k$; increment $h$; polygonal-line process; error; solution/$e$ as a limit | WHAT FOR the bearers are significant: roles in the approximation | Roles ($L4$) |
| $t_k\inℚ$; $y_k\inℚ$; $N\inℕ$; $k\inℕ$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). Essential is the distinction of the two indices, the resolution $N$ and the stage $k$: to mix them (as the classical limit “the solution at the point $t$,” which forgets the grid, does) would be to confuse the role-resolution with the role-stage. Here they are separated and fall into Roles separately, and their bearers—two different natural numbers—are likewise separately Elements. It is precisely this separateness that explains why Euler’s method remains finite and computable at every stage: the limit $N \to \infty$ does not enter the construction.

What the analysis yields. It translates the results of the chapter into the language of structure: *the Euler polygon is a Role-process* (an approximation of the solution), *resolution and stage are two different Roles* (the fineness of the grid and the position in time), *the error is a Role-defect* (unaccounted curvature), and the nodes $t_k$, values $y_k$, and indices $N, k$ are *Elements* (finite at every stage). To take “the exact solution” or $e$ as a completed object-Element is to put the role-limit in the place of an Element—the same confusion of categories as “number as an object” instead of the role-quantity (Part II) or “a Fourier series as a completed sum” instead of a family of truncations (Chapter 7.1). The solution on a grid begins here as a *finite polygonal line*; making it more precise is a process of refinement, and the completed solution function is neither needed nor built.

The next chapter raises the approximation one level higher: from the Euler trajectory to the Picard operator acting on whole functions, and to the proved theorem that this operator is a *contraction on a function space*—on a finite grid, in the sup metric over $ℚ^{N+1}$. There the process of approximations acquires a guarantee of convergence, the central result of Part VIII.

---

[^1]: The supporting file is `analysis/PicardLindelof.v` (the ToS Rocq repository): `grid`, `euler_step`, `euler_traj`, and theorems on concrete trajectories (`euler_traj_linear_4`, `euler_quadratic_error`, `euler_traj_exp_4`, and others). All are exact rational arithmetic (`vm_compute` or `ring`), 0 axioms. For the exponential as a process, see `ProcessExpProcess.v` (Chapter 8.5, batch C).
[^2]: `grid N k` ${}= \texttt{inject\_Z(Z.of\_nat k)} / \texttt{inject\_Z(Z.of\_nat N)}$ in `PicardLindelof.v` is $k/N$ over ℚ. The step $h = 1/N$ is built into the definition of the trajectory.
[^3]: `euler_step f h t y` ${}= y + h \cdot f t y$ and `euler_traj f y0 N k` (a recursion on $k$ with step $1/N$ and nodes `grid N k'`) in `PicardLindelof.v`. The base case `euler_traj_0`: `euler_traj f y0 N 0 == y0`.
[^4]: This is exactly why in `euler_traj` the resolution $N$ and the index $k$ are different arguments, and the step $1/\texttt{inject\_Z(Z.of\_nat N)}$ is taken from $N$. The convergence $(1+1/N)^N \to e$ is the growth of $N$ *with* $k = N$ (fixed final time $t = 1$); movement along the linear trajectory is the growth of $k$ with $N$ fixed.
[^5]: `euler_traj_linear_1`, `_2`, `_4` in `PicardLindelof.v`: `euler_traj f_const_one 0 4 k` gives $1/4, 1/2, 1$ for $k = 1, 2, 4$. The exactness is a consequence of the absence of curvature: the right-hand side is constant. `lipschitz_const`: the field $f \equiv 1$ is Lipschitz with $L = 0$.
[^6]: `euler_traj_quadratic_4`: `euler_traj f_two_t 0 4 4 == 3#4`; `euler_quadratic_error`: $1 - 3/4 = 1/4$. Both in `PicardLindelof.v`, exact arithmetic.
[^7]: `euler_step_concrete`: `euler_step f_identity h t y == y*(1+h)` in `PicardLindelof.v`. `lipschitz_identity`: the field $f(t,y)=y$ is Lipschitz with $L = 1$.
[^8]: `euler_traj_exp_1`, `_2`, `_4`: the values $2,\ 9/4,\ 625/256$; `euler_traj_exp_lower` ($2 < 625/256$) and `euler_traj_exp_converges` ($625/256 < 3$). All in `PicardLindelof.v`.
[^9]: `exp1_is_euler` (the identity “$e$-process ${}={}$ Euler trajectory for $y'=y$ at $t=1$”) and `exp1_lower` ($e$-process ${}\ge 2$ *for all* $N$, via Bernoulli) are general; `exp1_climb` (growth at the first stages) and the stages $2, 9/4, 64/27$ (`exp1_0`, `_1`, `_2`) are concrete. All in `ProcessExpProcess.v` (Chapter 8.5, batch C), 0 axioms (checked with `Print Assumptions`).
[^10]: The header of `PicardLindelof.v` gives the labeling directly: Elements—the right-hand side $f$, the grid nodes $t_k$, the values of the trajectory $y_k$; Roles—the step as approximation, the trajectory as the solution process; Rules—$y_{k+1} = y_k + h f(t_k,y_k)$.

---

Part: [[08 Ordinary Differential Equations|Part VIII. Ordinary Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/08 Ordinary Differential Equations/01 Cauchy Problem and Solution as Process|Chapter 1. The Cauchy Problem and the Solution as a Process]] · [[Library/Branches/Mathematics/Volume/08 Ordinary Differential Equations/03 Picard Lindelof Contraction on Function Space|Chapter 3. Picard–Lindelöf: A Contraction Operator on a Function Space]] →
