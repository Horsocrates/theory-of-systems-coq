---
title: "Chapter 3. Picard–Lindelöf: A Contraction Operator on a Function Space"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/08 Обыкновенные дифференциальные уравнения/03 Пикар–Линделёф оператор-сжатие на пространстве функций.md"
sourceBlob: b9b00ff0c9762c28b8d1b4340d7cedd30d6d8bd7
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### A Guarantee of Convergence

Chapter 8.1 established that the solution of the Cauchy problem is a process of approximations; Chapter 8.2 presented the simplest such process, the Euler polygon, and computed it on the reference equations. But one question remained open: *why* does the process of approximations converge? The Euler polygon is a sequence of rational stages; what guarantees that they draw together rather than scatter? The present chapter gives the guarantee, and it is the central result of Part VIII.

The guarantee is given by the *Picard–Lindelöf theorem* in its process reading. Its classical form runs as follows: the Picard operator

$$
\Phi(y)(t) \;=\; y_0 + \int_{t_0}^{t} f\bigl(s, y(s)\bigr) ds
$$

is a *contraction on the space of functions* $y(\cdot)$, and a contraction, by the Banach scheme, has a unique fixed point: the solution. The essential words here are *function space*: $\Phi$ acts not on a number but on a whole candidate function, and it contracts the distance between functions. It is precisely this formulation—contraction *on functions*—that is the genuine Picard–Lindelöf theorem.

### What This Chapter Claims—and What It Does Not

An honest reservation about what is *new* here. The previous layer of the volume’s formalization proved contraction for the *scalar* Euler–Picard iteration, the map $y \mapsto y_0 + f(y) h$ of one rational value into another, with coefficient $L h$.[^1] This is an important result, but *not* the same one: the genuine theorem requires the contraction of the operator $\Phi$ on *whole functions* $t\mapsto y(t)$, not on individual values. The present chapter presents precisely the function-space theorem—and it is proved.[^2]

The key that makes the infinite-dimensional theorem finite over ℚ: the *function space* on the grid $[0,T]$ is $ℚ^{N+1}$, the set of values at $N{+}1$ nodes. The distance between two candidate functions is a uniform bound on their discrepancy over the nodes (the sup metric). Over such a *finite* space, contraction, the geometric gap, and uniqueness are exact algebraic facts without a single axiom.

What the chapter does *not* do: the *geometric gap* between the iterates is proved algebraically, but its *reading* as $\varepsilon$-Cauchy convergence (“for every $\varepsilon$ there is an index”) uses the decay $(LT)^n\to 0$, and the completed limit function is one more role-limit; these two steps inherit the Law of Excluded Middle (L3) and are not actualized in this chapter.[^3] And the global-in-time continuation of the solution is a separate boundary (§ “Local Existence and Its Boundary”).

Three levels of rigor. The *first* is the contraction of the Picard operator on grid functions, the geometric gap between the iterates, and the uniqueness of the solution on the grid: proved over ℚ without axioms. The *second* is the process readings: the function space as $ℚ^{N+1}$, the solution as the role-limit of the Cauchy process of iterates, existence as geometric drawing-together. The *third*—the completed limit and the global solution—is role-limits and the L3 layer.

### The E/R/R Framework of the Chapter

The framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.” We rely on the author’s E/R/R header of the file `ProcessPicardOperator.v`.[^4] The chapter introduces the system of *the Picard operator as a contraction*.

**Rules ($\leftrightarrow$ L5).** The Picard operator on the grid,
$\Phi(y)_k = y_0 + h\sum_{j<k} f(t_j, y_j)$; when $f$ is Lipschitz, it is a contraction in the sup metric with coefficient $L\cdot T$ (where $T = N h$ is the length of the interval); the iterates $\Phi^n$ have the geometric gap $(LT)^n$; for $LT<1$ the fixed point is unique.

**Roles ($\leftrightarrow$ L4).** The operator $\Phi$ is the role-map of functions; the uniform bound over the nodes is the role-metric; the iterate $\Phi^n$ is the role-approximation; the fixed point is the role-solution; the condition $LT<1$ is the role-mode (where the process contracts).

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Grid functions
$y:\{0,…,N\}\toℚ$, their values $y_k$, finite sums $\sum_{j<k}$, the node index $k\le N$. Under P4 the completed limit function lies outside the elements: finite grid functions and iterates are actual.

## The Picard Operator and the Function Space over a Grid

The integral form of the Cauchy problem (Chapter 8.1) sets an operator that transforms a candidate function $y(\cdot)$ into a new function:

$$
\Phi(y)(t) \;=\; y_0 + \int_{t_0}^{t} f\bigl(s, y(s)\bigr) ds .
$$

On the rational grid $t_k = k h$ the integral becomes the process of accumulation of Part V—a left sum over the nodes—and the operator becomes a finite formula:

$$
\Phi(y)_k \;=\; y_0 + h\sum_{j<k} f(t_j, y_j).
$$

Here $y = (y_0, y_1, …, y_N)$ is a grid function, a set of values at the nodes, and $\Phi(y)$ is a grid function of the same kind.[^5] Thus the classically infinite-dimensional *function space* $C([0,T])$ turns into the *finite* space $ℚ^{N+1}$: the values at $N{+}1$ nodes.

The distance between two candidates $y$ and $z$ is their maximal discrepancy over the nodes, the *sup metric*:

$$
\supnorm{y - z} \;=\; \max_{k\le N} \lvert y_k - z_k\rvert .
$$

On a finite grid this maximum is simply the largest of $N{+}1$ rational numbers, without any limit.

*The Picard operator $\Phi$ is a role-map: it transforms the whole candidate function at once, not an individual value. The “function space” on which it acts is a role-arena, and over ℚ on a grid it is finite: $ℚ^{N+1}$. The solution is the function that $\Phi$ leaves in place.*

## The Picard Operator Is a Contraction

The central theorem of the chapter: *when the right-hand side is Lipschitz, the Picard operator is a contraction in the sup metric with coefficient $L\cdot T$*. Spelled out: for any two grid functions $y, z$ that differ by at most $D$ at all nodes, the images $\Phi(y), \Phi(z)$ differ by at most $(L\cdot T) D$:

$$
\bigl(\forall k\le N:\ \lvert y_k - z_k\rvert \le D\bigr)
  \quad\Longrightarrow\quad
  \forall k\le N:\ \bigl\lvert \Phi(y)_k - \Phi(z)_k\bigr\rvert \le (L\cdot T) D .
$$

The mechanism is transparent. The difference of the images is the summed difference of the slopes:

$$
\Phi(y)_k - \Phi(z)_k \;=\; h\sum_{j<k}\bigl[f(t_j, y_j) - f(t_j, z_j)\bigr].
$$

Each term obeys the Lipschitz bound: $\lvert f(t_j, y_j) - f(t_j, z_j)\rvert \le L \lvert y_j -
z_j\rvert \le L D$. There are exactly $k$ terms, and since $k\le N$, there are at most $N$ of them; therefore the absolute value of the sum does not exceed $N\cdot L D$, and multiplication by the step gives

$$
\bigl\lvert \Phi(y)_k - \Phi(z)_k\bigr\rvert
  \;\le\; h\cdot N\cdot L D \;=\; (L\cdot N h) D \;=\; (L\cdot T) D .
$$

This is precisely contraction with coefficient $L\cdot T$.[^6] Contraction in the proper sense is when the coefficient is less than one: $L\cdot T < 1$, that is, the interval is short enough ($T < 1/L$).

Let us compare with the scalar layer. The scalar Euler–Picard iteration contracted the distance between *numbers* with coefficient $Lh$ (the step); here the distance between *functions* is contracted with coefficient $LT$ (the whole length of the interval). The first concerns a single step; the second concerns the *whole* operator on the space of candidates. The genuine Picard–Lindelöf theorem is precisely the second, and its process core—contraction on the space of grid functions—is now proved, finitely and over ℚ.

*Contraction is a role-rule: it says that applying the operator *draws together* any two candidate functions by a fixed factor. The coefficient $L\cdot T$ is the role-rate of this drawing-together; the condition $LT<1$ is the role-mode in which the process of iterations is guaranteed to converge.*

## Consequences: The Geometric Gap and Uniqueness

### The Iterates Draw Together Geometrically

From contraction it follows that successive iterations of the operator draw together *geometrically*. We start the process from the constant function $y^{(0)} \equiv y_0$ and apply $\Phi$ repeatedly; then the gap between neighboring iterations decreases as a power of the coefficient:

$$
\supnorm{\Phi^{n+1} - \Phi^{n}} \;\le\; (L\cdot T)^{n}\;\supnorm{\Phi^{1} - \Phi^{0}} .
$$

For $LT<1$ the powers $(LT)^n$ decrease and the gaps shrink—this is precisely the *Cauchy content* of the process: the iterations eventually come arbitrarily close to one another.[^7] Let us stress honestly: the *geometric gap* is proved without axioms; the passage from it to Cauchy convergence itself in the form “for every $\varepsilon$ there is an index” and to the completed limit uses the decay $(LT)^n\to 0$, which inherits L3.

### The Solution Is Unique—without Axioms

Contraction also gives *uniqueness*, and, remarkably, it does so constructively, without the Law of Excluded Middle. Let $y$ and $z$ be two fixed points of the operator on the grid ($\Phi(y) = y$ and $\Phi(z) = z$ at all nodes). Take their maximal discrepancy $D^{*} = \max_{k\le N}\lvert y_k - z_k\rvert$, the largest of $N{+}1$ rational numbers. Since both functions are fixed, contraction gives for each node

$$
\lvert y_k - z_k\rvert = \bigl\lvert \Phi(y)_k - \Phi(z)_k\bigr\rvert \le (L\cdot T) D^{*},
$$

and hence the maximum obeys the same bound: $D^{*} \le (L\cdot T) D^{*}$. For $LT<1$ this is possible only if $D^{*} = 0$, that is, if $y$ and $z$ coincide at all nodes.[^8] What is essential is that the maximum is taken over a *finite* grid: it is a rational number, not a limit, and therefore uniqueness does not require L3—unlike the *existence* of a completed limit.

*Uniqueness is a role-rigidity: a contraction cannot have two different fixed points. Proved constructively through a finite maximum, it shows that the role-solution is determined uniquely even before we ask about its completed limit. Existence (the Cauchy gap) and uniqueness are two sides of one contraction.*

## Local Existence and Its Boundary

The theorem of the chapter is *local*. The contraction coefficient is $L\cdot T$, and the regime of guaranteed convergence is $L\cdot T < 1$, that is, an interval shorter than $1/L$. On such an interval the process of Picard iterations is Cauchy (the geometric gap), and the solution is unique. This is *local* existence and uniqueness: on a sufficiently short interval.

Classically, a *global* solution is built from here: having reached the end of the interval, one takes the value obtained as a new initial condition and continues onto the next interval, and so on. This is *continuation*. But the global picture—continuation for all time, the analysis of a possible blow-up (the solution going to infinity in finite time), the maximal interval of existence—is *not* proved in our formalization. This is an honest P4 boundary: the completed solution on an unbounded interval is a role-limit, and the continuation theorem is a direction, not a built result.

*Locality is not a defect but the exact content over ℚ: the guarantee concerns the regime $LT<1$. The global solution is the role-limit of the process of continuations, toward which the repeated application of the local theorem leads; as a completed object over all time it is not built.*

## E/R/R Analysis: The Picard Operator as a Role-Contraction

### Setup

Let us analyze the constructed system—the Picard operator as a contraction—in terms of E/R/R, reading the author’s E/R/R header of the file `ProcessPicardOperator.v`.[^9] This is an ontological comprehension and a reading of the header, not an attribution of new claims to the code. As before, the abbreviation sets the epistemic order (Elements $\to$ Roles $\to$ Rules); we conduct the analysis in the generating one, Rules $\to$ Roles $\to$ Elements.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the Picard operator
$\Phi(y)_k = y_0 + h\sum_{j<k} f(t_j, y_j)$, which transforms a grid function into a grid function. Above it is the rule of contraction: when $f$ is Lipschitz, the operator draws any two candidates together in the sup metric with coefficient $L\cdot T$. From contraction follow the geometric gap between the iterates $(LT)^n$ (the Cauchy content) and the uniqueness of the fixed point. The universal layer includes L3 where we wish to read the geometric gap as $\varepsilon$-convergence and a completed limit; the finite contraction itself and uniqueness, as algebraic facts, do not require it. The concrete layer is the formula of the operator and the condition $LT<1$.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The operator
$\Phi$ is the role-map of functions. The uniform bound over the nodes ($\supnorm{\cdot}$) is the role-metric on the space of candidates. The iterate $\Phi^n$ is the role-approximation. The condition $LT<1$ is the role-mode (where contraction works). The fixed point is the role-solution, and its completed limit is the role-limit: that toward which the Cauchy process contracts, not actualized as a function-object.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite:
grid functions $y:\{0,…,N\}\toℚ$, their values $y_k\inℚ$, finite sums $\sum_{j<k}$, the node index $k\le N$, the coefficient $L\cdot T\inℚ$. Under P4 “the space of all functions” and the completed limit are not elements: the arena on the grid is the finite $ℚ^{N+1}$; grid functions and iterates are actual.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| operator $\Phi(y)_k=y_0+h\sum f$; contraction rate $LT$; gap $(LT)^n$; uniqueness | HOW the operator contracts and why the process converges | Rules ($L5$) |
| $\Phi$ as role-operator; sup metric; iterate $\Phi^n$; regime $LT<1$; solution/limit | WHAT FOR the bearers are significant: roles in the contraction | Roles ($L4$) |
| grid functions $y_k\inℚ$; sums $\sum_{j<k}$; node $k\le N$; $LT\inℚ$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is what is *absent* here: the Picard operator does *not* take as its arena “the space of all functions” as a completed infinite-dimensional object. The arena on the grid is the finite $ℚ^{N+1}$, the metric is a maximum over a finite set of nodes, and uniqueness is proved through this finite maximum *without* a passage to the limit. It is precisely this finiteness of the arena that separates what is proved (contraction, gap, uniqueness—0 axioms) from the boundary (the completed limit—the L3 layer).

What the analysis yields. It translates the central result into the language of structure: *the Picard operator is a Role-map* of functions, *contraction is a Rule* of drawing together, *the fixed point is a Role-solution*, and grid functions and their values are *Elements* (finite at every stage). To take “the function space” as a completed infinite-dimensional object or “the solution” as a ready limit function is to put the role-arena or the role-limit in the place of an Element—the same confusion of categories as “a point as an object” instead of a class (Chapter 4.3) or “a series as a completed sum” instead of a family of truncations (Chapter 7.1). The process core of the Picard–Lindelöf theorem *is* here, and it is finite: contraction on $ℚ^{N+1}$, the geometric drawing-together of the iterates, and the uniqueness of the fixed point on the grid. The passage to the completed solution function remains a role-limit.

Having the guarantee of convergence, the next chapter turns to *stability*: how solutions with different initial data diverge, how Grönwall’s inequality controls this divergence, and in what sense the classical factor $e^{Lt}$ is the role-limit of a process of growth, not a pregiven exponential.

---

[^1]: `euler_picard_contraction` in `ProcessPicard.v`: the contraction of a map $ℚ\toℚ$ with coefficient $Lh$ for $Lh<1$. This is a *scalar* iteration: what contracts is the distance between numbers, not between functions.
[^2]: The supporting file is `ProcessPicardOperator.v` (the ToS Rocq repository): the Picard operator on grid functions, the theorem on contraction in the sup metric (`picard_op_contraction`), the geometric gap between the iterates (`picard_iter_gap`), and the uniqueness of the solution on the grid (`picard_unique`). The key theorems have 0 axioms (`Print Assumptions`: “closed under the global context”).
[^3]: The wrapper “the iterates converge to a limit” goes through `iterate_is_cauchy` / `Qpow_vanish` in `FixedPoint.v`, which inherit `classic`. Contraction, the gap, and uniqueness have 0 axioms; the limit is the L3 layer.
[^4]: The header labels directly: Rules—$\Phi(y)_k=y_0+h\sum_{j<k}f(t_j,y_j)$, Lipschitz $\Rightarrow$ $\Phi$ is a contraction, rate $L\cdot T$; Roles—$\Phi$ is the role-operator, the uniform bound is the role-metric; Elements—grid functions, values $y_k$, finite sums.
[^5]: `picard_sum` ${}= \texttt{q\_sum} (\lambda j. f(t_j, y_j)) k$ and `picard_op`${}(y)_k = y_0 + h\cdot \texttt{picard\_sum} y k$ in `ProcessPicardOperator.v`; the nodes $t_j = \texttt{tgrid} j = j\cdot h$, the length $T = \texttt{Tlen} = N\cdot h$.
[^6]: `picard_diff_bound` (the bound on the difference of Picard sums, by induction on $k$) and `picard_op_contraction` (contraction with coefficient $L\cdot\texttt{Tlen}$) in `ProcessPicardOperator.v`, 0 axioms. The coefficient is $L\cdot T = L\cdot N h$.
[^7]: `picard_iter_gap` in `ProcessPicardOperator.v`: $\supnorm{\Phi^{n+1}-\Phi^n}\le (L\cdot T)^n C_0$, where $C_0$ is a bound on the first gap; proved by induction on $n$ through the contraction theorem. 0 axioms.
[^8]: `picard_unique` in `ProcessPicardOperator.v`: the uniqueness of the fixed point on the grid. The maximum over the finite grid is implemented as `gmax`, the largest of $N{+}1$ rational values; hence $D^*\le(LT)D^*$ and $LT<1$ give $D^*=0$ *without* appeal to a limit. 0 axioms.
[^9]: The header of the file conducts the analysis directly: Rules—$\Phi(y)_k=y_0+h\sum_{j<k}f(t_j,y_j)$, Lipschitz $\Rightarrow$ contraction, rate $L\cdot T$, iterates with the gap $(LT)^n$, uniqueness of the fixed point; Roles—$\Phi$ is the role-operator, the uniform bound is the role-metric, $\Phi^n$ is the role-approximation, the fixed point is the role-solution; Elements—grid functions, values $y_k$, finite sums, $k\le N$.

---

Part: [[08 Ordinary Differential Equations|Part VIII. Ordinary Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/08 Ordinary Differential Equations/02 Euler Method Solution on a Grid|Chapter 2. Euler’s Method: The Solution on a Grid]] · [[Library/Branches/Mathematics/Volume/08 Ordinary Differential Equations/04 Stability Uniqueness Gronwall Inequality|Chapter 4. Stability, Uniqueness, Grönwall’s Inequality]] →
