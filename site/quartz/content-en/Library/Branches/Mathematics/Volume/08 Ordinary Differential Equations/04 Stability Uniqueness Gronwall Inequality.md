---
title: "Chapter 4. Stability, Uniqueness, Grönwall’s Inequality"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/08 Обыкновенные дифференциальные уравнения/04 Устойчивость, единственность, неравенство Гронуолла.md"
sourceBlob: dfc5ddb314846361726c3074cd2485e25f72d701
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### From Existence to Sensitivity

Chapter 8.3 gave a guarantee: when the right-hand side is Lipschitz, the Picard operator contracts, and hence the process of approximations converges and the solution is unique. But the Cauchy problem has one more question, no less important for applications: how *sensitive* is the solution to the initial condition? If $y_0$ is shifted slightly, how far will the trajectories diverge? The answer is *stability*, or continuous dependence on the initial data, and the instrument for it is *Grönwall’s inequality*.

These three topics—uniqueness, stability, Grönwall—are one geometry read from three angles. Uniqueness is the extreme case: zero perturbation, the trajectories coincide. Stability is the general case: the perturbation $\Delta_0 = y_0 -
\tilde y_0$ generates a divergence, and this divergence is *controllable*: it does not exceed a geometric factor multiplied by the initial perturbation. Grönwall is the general principle behind this factor: if a quantity grows at a rate bounded by a multiple of itself, then it is bounded by a geometric (in the limit, exponential) estimate.

### What This Chapter Claims—and What It Does Not

The proved core is concrete process estimates over ℚ. The divergence of two Euler trajectories with different initial conditions grows at each step by a factor of at most $(1+Lh)$, and over $n$ steps by at most $(1+Lh)^n$; the homogeneous Grönwall iteration gives the same geometric form $u_0 (1+\alpha h)^n$, and, with a factor not greater than one, decay.[^1] These estimates are exact rational inequalities over ℚ, and their 0-axiom status is checked with `Print Assumptions`; the passage to the $\varepsilon$-convergence of the factor to the completed $e^{Lt}$ belongs to the L3 layer (as in Chapter 8.3).

What the chapter does *not* do: it does not present the classical factor $e^{Lt}$ as a completed exponential, does not assert an unconditional estimate on an infinite interval, and does not prove the global continuation of the solution.
The factor $(1+Lh)^n$ is a rational process; its limit $e^{Lt}$ is a role-limit, and the $\varepsilon$-convergence to it inherits L3 (as in Chapter 8.3 as well).

Three levels. The *first* is the rational estimates of divergence and growth: proved over ℚ without axioms. The *second* is the process readings: divergence as sensitivity, the factor as the role-of-growth, stability as controllability. The *third*—$e^{Lt}$ as a completed exponential and the estimate on an infinite interval—is role-limits.

### The E/R/R Framework of the Chapter

The framework in the generating order; the full analysis is in § “Analysis in the Generating Order.” We rely on the E/R/R header of `ProcessODEStability.v`. The chapter introduces the system of *control of the divergence of solutions*.

**Rules ($\leftrightarrow$ L5).** The Lipschitz condition gives the stepwise estimate $\lvert\Delta_{n+1}\rvert \le (1+Lh)\lvert\Delta_n\rvert$, whence the geometric one, $\lvert\Delta_n\rvert \le (1+Lh)^n\lvert\Delta_0\rvert$; Grönwall’s inequality generalizes: growth bounded by a multiple of itself entails the geometric estimate $u_0(1+\alpha h)^n$; the factor $(1+Lh)^n$ is a stage of the process for $e^{Lt}$.

**Roles ($\leftrightarrow$ L4).** The divergence $\lvert\Delta_n\rvert$ is the role-sensitivity; the factor $(1+Lh)^n$ is the role-of-growth; the Lipschitz constant $L$ is the role-rate of error growth; the perturbation $\Delta_0$ is the role-cause; stability is a role-property (the controllability of the divergence); $e^{Lt}$ is the role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational
divergences $\lvert\Delta_n\rvert$, factors $(1+Lh)^n$, Grönwall iterates $u_n$, the finite index $n$. Under P4 the completed $e^{Lt}$ and the estimate on an infinite interval lie outside the elements.

## Uniqueness as Zero Perturbation

The uniqueness of the solution is an already proved fact (Chapter 8.3): the contracting Picard operator has at most one fixed point on the grid, and this uniqueness is established constructively, through a finite maximum, without the Law of Excluded Middle.[^2] In the context of stability it acquires a vivid reading: *uniqueness is stability under zero perturbation*. If the initial conditions coincide, $\Delta_0 = 0$, then the divergence estimate $\lvert\Delta_n\rvert \le
(1+Lh)^n\cdot 0 = 0$ makes the trajectories coincide at every step. One and the same beginning, under one and the same law, generates one and the same trajectory.

*Uniqueness is role-rigidity read as the limiting case of stability: zero perturbation gives zero divergence. The solution is determined by its beginning uniquely—not because “it is so postulated,” but because the process of contraction leaves no room for a second trajectory.*

## The Divergence of Trajectories: Continuous Dependence

Take two Euler trajectories $y$ and $\tilde y$ of one equation, starting from different points, and denote their divergence by $\Delta_n = y_n - \tilde y_n$. One Euler step changes the divergence predictably: the new values differ by the old divergence plus the difference of the slopes, and the Lipschitz condition bounds this difference,

$$
\lvert\Delta_{n+1}\rvert \;\le\; \lvert\Delta_n\rvert + h L \lvert\Delta_n\rvert
  \;=\; (1 + L h) \lvert\Delta_n\rvert .
$$

Each step stretches the divergence by a factor of at most $(1+Lh)$.[^3] Accumulating over $n$ steps, we obtain *continuous dependence on the initial data*:

$$
\lvert\Delta_n\rvert \;\le\; (1+Lh)^n \lvert\Delta_0\rvert .
$$

The divergence at any moment is bounded by the initial perturbation multiplied by a geometric factor.[^4] On a *finite* interval the factor is finite, and therefore a small perturbation gives a small divergence: this is the substantive stability over ℚ, the discrete process form of continuous dependence (a small initial divergence gives a small divergence over any finite number of steps).

*The divergence $\lvert\Delta_n\rvert$ is the role-sensitivity: the measure of how the solution responds to a shift of the beginning. The factor $(1+Lh)^n$ is the role-of-growth of this sensitivity. Stability is not the absence of divergence but its *controllability*: a finite factor on a finite interval.*

## Grönwall’s Inequality

The geometric factor $(1+Lh)^n$ is a special case of a general principle that the theory of ODEs calls *Grönwall’s inequality*. The principle is this: if a quantity grows at a rate bounded by a multiple of itself (plus, possibly, an external inflow), then it is bounded by a geometric estimate. In discrete process form the recurrent Grönwall step is

$$
u_{n+1} \;=\; u_n + h (\alpha  u_n + \beta) \;=\; (1+\alpha h) u_n + \beta h,
$$

where $\alpha$ is the rate of self-action and $\beta$ is the external inflow.[^5] In the homogeneous case ($\beta = 0$) the iteration is solved explicitly and gives exactly geometric growth:

$$
u_n \;=\; u_0 (1+\alpha h)^n .
$$

This is the process form of Grönwall, and for $\alpha = L$, $u_0 = \lvert\Delta_0\rvert$ it coincides with the divergence estimate of the previous section: stability is Grönwall for the divergence.[^6] And if the factor does not exceed one ($r = 1+\alpha h$ in the range $0 \le r \le 1$, the damped regime), the iteration does not grow but *decreases*: $u_n \le u_0$.[^7]

*Grönwall is the role-rule of control: it turns local information about the rate of growth (“no faster than a multiple of itself”) into a global estimate of the whole trajectory. The geometric factor $(1+\alpha h)^n$ is the role-of-growth; stability and decay are its two regimes ($\alpha$ positive or negative.)*

## The Growth Factor and $e^{Lt}${e^(Lt)} as a Role-Limit

The classical theory of stability writes the estimate of continuous dependence in *exponential* form:

$$
\lvert y(t) - \tilde y(t)\rvert \;\le\; \lvert y_0 - \tilde y_0\rvert \; e^{L t} .
$$

Where does the exponential come from here? It is the role-limit of our geometric factor. If we take the step $h = t/n$ (that is, reach the moment $t$ in $n$ steps), the factor becomes $(1 + L t/n)^n$—and this is exactly a stage of the process for $e^{Lt}$, the very $e$-process analyzed in Chapters 8.2 and 8.5.[^8] Thus the classical form $e^{Lt}$ turns out to be not a pregiven exponential but the *role-limit* of the rational process $(1+Lt/n)^n$—a ladder of factors, each of which is rational and computable.

What is proved is concrete and process-level: the stepwise and geometric estimates of divergence, their coincidence with homogeneous Grönwall, and the identity of the factor with a stage of the $e^{Lt}$-process. The $\varepsilon$-convergence of the factor to the completed $e^{Lt}$ and the unconditional estimate on an infinite interval are a role-limit and a boundary that inherit L3 (as in Chapter 8.3).

*The classical factor $e^{Lt}$ is the role-limit of a process of growth, not a pregiven exponential. The stability estimate $\lvert\Delta(t)\rvert \le \lvert\Delta_0\rvert e^{Lt}$ reads as the direction toward which the rational estimate $\lvert\Delta_n\rvert \le (1+Lh)^n\lvert\Delta_0\rvert$ tends; the finite estimate is actual, and $e^{Lt}$ is its role-limit.*

## E/R/R Analysis: Divergence as a Role-Sensitivity

### Setup

Let us analyze the constructed system—the control of the divergence of solutions—in terms of E/R/R, reading the E/R/R header of `ProcessODEStability.v`.[^9] This is an ontological comprehension and a reading of the header. The abbreviation sets the epistemic order (Elements $\to$ Roles $\to$ Rules); we conduct the analysis in the generating one.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the stepwise divergence estimate $\lvert\Delta_{n+1}\rvert \le (1+Lh)\lvert\Delta_n\rvert$ from the Lipschitz condition. Above it are the geometric estimate $\lvert\Delta_n\rvert \le (1+Lh)^n\lvert\Delta_0\rvert$ and its generalization, Grönwall’s inequality ($u_n = u_0(1+\alpha h)^n$ in the homogeneous case, decay for a factor $\le 1$). Crowning it is the identity of the factor $(1+Lt/n)^n$ with a stage of the $e^{Lt}$-process. The universal layer includes L3 only where the factor is read as $\varepsilon$-convergence to $e^{Lt}$; the rational estimates themselves do not require it.

**Roles ($\leftrightarrow$ L4).** The divergence $\lvert\Delta_n\rvert$ is the role-sensitivity (how the solution responds to a shift of the beginning). The factor $(1+Lh)^n$ is the role-of-growth. The Lipschitz constant $L$ is the role-rate of error growth. The perturbation $\Delta_0$ is the role-cause. Stability is a role-property (the controllability of the divergence by a finite factor). $e^{Lt}$ is the role-limit of the process of growth.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite:
rational divergences $\lvert\Delta_n\rvert \in ℚ$, factors $(1+Lh)^n \in ℚ$, Grönwall iterates $u_n \in ℚ$, constants $L, h \in ℚ$, the index $n \in ℕ$. Under P4 the completed $e^{Lt}$ and the estimate on an infinite interval are not elements: finite estimates on finite intervals are actual.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| $\lvert\Delta_{n+1}\rvert\le(1+Lh)\lvert\Delta_n\rvert$; Grönwall $u_0(1+\alpha h)^n$; factor ${}={}$ stage of $e^{Lt}$ | HOW the growth of divergence is controlled | Rules ($L5$) |
| divergence $\lvert\Delta_n\rvert$; factor $(1+Lh)^n$; $L$; perturbation $\Delta_0$; stability; $e^{Lt}$ | WHAT FOR the bearers are significant: roles in control | Roles ($L4$) |
| $\lvert\Delta_n\rvert,(1+Lh)^n,u_n\inℚ$; $L,h\inℚ$; $n\inℕ$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

{
The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is that stability is taken as the *controllability* of the divergence by a finite factor, not as a statement about completed behavior on an infinite interval. The factor $(1+Lh)^n$ is an Element (a rational number at each stage), while its limit $e^{Lt}$ is a role-limit; to mix them would be to put a completed exponential in the place of a rational factor.}

What the analysis yields. It translates the results of the chapter into the language of structure: *divergence is a Role-sensitivity*, *the growth factor is a Role-of-growth*, *stability is a Role-property of controllability*, and the numbers $\lvert\Delta_n\rvert$, $(1+Lh)^n$, $u_n$ themselves are *Elements*. Uniqueness fits in as the limiting case (zero perturbation), and Grönwall as the general Rule of which the divergence estimate is a special case. To take $e^{Lt}$ as a completed exponential is to put the role-limit in the place of an Element—the same confusion as “number as an object” (Part II) or “the solution as a ready function” (Chapter 8.1).

The final chapter of the Part will gather the threads together: the exponential as a process (the solution of $y'=y$), linear equations and decay, systems and the harmonic oscillator, applications—and will sum up the ontology “the solution is a process,” marking the transition to partial differential equations.

---

[^1]: The supporting files are `ProcessODEStability.v` (continuous dependence: `euler_step_diff`, `euler_diff_bound`; 0 axioms, `Print Assumptions` “closed under the global context”) and `ProcessGronwall.v` (`gronwall_step`, `gronwall_iterate`, `gronwall_beta_zero`: $u_0(1+\alpha h)^n$; `gronwall_decay_factor`: decay for a factor $\le 1$). Uniqueness is `picard_unique` (`ProcessPicardOperator.v`, Chapter 8.3).
[^2]: `picard_unique` in `ProcessPicardOperator.v`: if two grid functions are fixed under the Picard operator, they coincide at all nodes. 0 axioms (Chapter 8.3).
[^3]: `euler_step_diff` in `ProcessODEStability.v`: $\lvert\Delta_{k+1}\rvert \le (1+Lh)\lvert\Delta_k\rvert$, via the triangle inequality and the Lipschitz condition. 0 axioms.
[^4]: `euler_diff_bound` in `ProcessODEStability.v`: $\lvert\Delta_n\rvert \le (1+Lh)^n\lvert\Delta_0\rvert$, by induction on $n$ via `euler_step_diff`. 0 axioms.
[^5]: `gronwall_step` and `gronwall_iterate` in `ProcessGronwall.v`; `gronwall_process` is the corresponding `RealProcess`.
[^6]: `gronwall_beta_zero` in `ProcessGronwall.v`: `gronwall_iterate alpha 0 h u0 n == u0 * Qpow (1+alpha*h) n`. 0 axioms. For $\alpha=L$ this is the right-hand side of `euler_diff_bound`.
[^7]: `gronwall_decay_factor` in `ProcessGronwall.v`: for $0 \le r \le 1$ we have $u_0 r^n \le u_0$. 0 axioms.
[^8]: `euler_growth_is_expt_process` in `ProcessODEStability.v`: the factor $(1+s/(k{+}1))^{k+1}$ *is* the stage $`expt_process` s k$ from `ProcessExpProcess.v` (batch C). 0 axioms. For $s = Lt$ this is $(1+Lt/n)^n$.
[^9]: The header labels directly: Rules—Lipschitz $\Rightarrow$ $\lvert\Delta_{n+1}\rvert\le(1+Lh)\lvert\Delta_n\rvert$ $\Rightarrow$ $\lvert\Delta_n\rvert\le(1+Lh)^n\lvert\Delta_0\rvert$; Roles—$\lvert\Delta_n\rvert$ is the role-divergence, $(1+Lh)^n$ the role-of-growth, $e^{Lt}$ the role-limit; Elements—rational $\lvert\Delta_n\rvert$, $(1+Lh)^n$, finite $n$.

---

Part: [[08 Ordinary Differential Equations|Part VIII. Ordinary Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/08 Ordinary Differential Equations/03 Picard Lindelof Contraction on Function Space|Chapter 3. Picard–Lindelöf: A Contraction Operator on a Function Space]] · [[Library/Branches/Mathematics/Volume/08 Ordinary Differential Equations/05 Exponential Linear Equations Applications|Chapter 5. The Exponential, Linear Equations, Applications]] →
