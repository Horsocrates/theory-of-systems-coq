---
title: "Chapter 2. The Heat Equation: Diffusion as Smoothing"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/09 Уравнения в частных производных/02 Уравнение теплопроводности диффузия как сглаживание.md"
sourceBlob: 2bdbfdd0f6486e501570d769c846e5bb08aafcd0
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Canonical Parabolic Process

Chapter 9.1 set the framework: the solution of a partial differential equation is a process of grid functions, and the spatial derivative is a finite difference. The present chapter is the center of Part IX: the first and most telling of these processes, the heat equation

$$
\partial_t u \;=\; \partial_x^2 u .
$$

It describes how a distribution of heat (or of concentration, or of probability) is *smoothed* over time: peaks settle, troughs fill in, and the profile tends toward uniformity. ToS presents this as a process on a grid—and shows that all the substantive physics of heat conduction (the maximum principle, the dissipation of energy) is finite rational mathematics, without appeal to a completed solution.

The key to the whole chapter is a single observation about the structure of the explicit scheme: when the stability condition holds, the new value at a node is a *convex average* of neighboring values. From this one fact follow smoothing, the maximum principle, and the decrease of energy.

### What This Chapter Claims—and What It Does Not

The proved core is concrete and over ℚ. The explicit heat scheme is defined as a recursion over grid functions; for $0\le r\le \tfrac12$ the *maximum principle* (values do not leave their initial bounds) and the *dissipation of energy* (the norm does not grow) are proved, and the smoothing of an impulse is computed exactly.[^1]

What the chapter does *not* do: it does not build the completed solution function $u(x,t)$, does not prove the continuum limit (refinement of the grid down to zero), does not introduce the heat kernel (the Gaussian) as a ready object, and does not prove convergence to equilibrium as $t\to\infty$. These limits are role-limits.

Three levels. The *first* is the finite scheme over ℚ: the convex combination, the maximum principle, the dissipation of energy, the concrete smoothing—proved without axioms. The *second* is the process *readings*: heat conduction as a process of smoothing, $r$ as the rate of diffusion, the uniform profile as a role-limit. The *third*—the completed solution, the continuum limit, and the heat kernel—is role-limits and a direction.

### The E/R/R Framework of the Chapter

The framework in the generating order; the full analysis is in § “Analysis in the Generating Order.” We rely on the E/R/R header of `ProcessHeatEquation.v`. The chapter introduces the system of *diffusion as a process of smoothing*.

**Rules ($\leftrightarrow$ L5).** The explicit scheme $u^{n+1}_j = r u_{j-1} + (1-2r) u_j + r u_{j+1}$; for $0\le r\le\tfrac12$ the coefficients are nonnegative and sum to one (a convex combination); hence the maximum principle and the dissipation of the energy $\sum_j u_j^2$; the stability condition (CFL) $r\le\tfrac12$.

**Roles ($\leftrightarrow$ L4).** The profile $u^n$ is the role-state (the distribution of heat at moment $n$); $r$ is the role-rate of diffusion; the interval of values $[ \min,\max ]$ is the role-invariant (the maximum principle preserves it); energy is the role-dissipating quantity; the uniform limit is the role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational values
at the nodes $u^n_j$, a finite grid, a finite step number. Under P4 the completed solution and the heat kernel lie outside the elements.

## The Explicit Scheme: A Step as a Convex Average

We discretize heat conduction by Euler’s method in time and a centered difference in space. The Laplacian at a node is the centered second difference $u_{j+1}-2u_j+u_{j-1}$,[^2] and the step of the scheme is

$$
u^{n+1}_j \;=\; u^n_j + r \bigl(u^n_{j+1} - 2u^n_j + u^n_{j-1}\bigr),
  \quad r = \frac{\Delta t}{\Delta x^2}.
$$

Let us regroup this expression—and here is the whole essence of the chapter:

$$
u^{n+1}_j \;=\; r u^n_{j-1} \;+\; (1-2r) u^n_j \;+\; r u^n_{j+1}.
$$

For $0\le r\le\tfrac12$ the three coefficients $r,\ 1-2r,\ r$ are nonnegative and sum to one. Hence the new value is a *convex average* (weighted, with weights that are fractions) of the old value and its two neighbors.[^3] The stability condition $r\le\tfrac12$ is exactly the requirement that the weights be fractions (nonnegative): then the step *averages*.

*The heat step is a role-averaging: it replaces a value by a weighted average of its neighbors. The rate of diffusion $r$ is the role-weight of mixing. The condition $r\le\tfrac12$ is the role-mode in which the weights remain fractions and the step remains a genuine averaging. Everything further comes from this one structure.*

## The Maximum Principle

The first and principal consequence of averaging is the *maximum principle*. An average of several numbers is no greater than the largest of them and no less than the smallest. Therefore, if all the values of a profile lie in the interval $[ m,M ]$, then any convex average also lies in $[ m,M ]$—and hence so does the whole next profile:

$$
m \le u^n_j \le M \ (\forall j)
  \quad\Longrightarrow\quad
  m \le u^{n+1}_j \le M \ (\forall j).
$$

This is proved directly from the convexity of the combination, for $0\le r\le\tfrac12$.[^4] By induction the principle holds *over the whole process*: however many steps have passed, the values do not leave their initial bounds.[^5]

The physical meaning is exact: heat conduction *creates no* new extrema. No value will exceed the initial upper barrier $M$ or fall below the lower one $m$; in the temperature picture this means that no point will arise hotter than the hottest initial one or colder than the coldest—heat is only redistributed. This is the discrete maximum principle, and over ℚ it is a finite fact about convex combinations, not a limit theorem.

*The interval of values $[ m,M ]$ is a role-invariant: averaging cannot carry a value beyond its bounds. The maximum principle is the role-rule of preserving this invariant; it is primary (it follows directly from convexity) and requires neither energy nor a passage to the limit.*

## The Dissipation of Energy

The second consequence of averaging is the *dissipation of energy*. By energy we mean here the discrete $L^2$ energy $E = \sum_j u_j^2$, a simple measure of the magnitude (concentration) of the profile; with mass preserved, its decrease corresponds to smoothing. Averaging smooths, so the energy should not grow—and it does not:

$$
E(u^{n+1}) \;\le\; E(u^n) \quad (0\le r\le\tfrac12,\ \text{periodic grid}).
$$

The mechanism is Jensen’s inequality: the square of a convex average does not exceed the same average of the squares (geometrically, this is the nonnegativity of the variance). Applying it node by node and summing, we obtain

$$
\sum_j (u^{n+1}_j)^2
  \;\le\; \sum_j \bigl[ r u_{j-1}^2 + (1-2r) u_j^2 + r u_{j+1}^2 \bigr],
$$

and on a periodic grid the sums of the shifted squares equal the unshifted one (a cyclic permutation of the nodes does not change the sum), so the right-hand side equals $[ r+(1-2r)+r ]\sum_j u_j^2 = \sum_j u_j^2$.[^6] The energy dissipates: with each step the profile becomes “smoother” in this exact rational measure. The periodic grid is used essentially here: the left and right shifts are permutations of a finite set of nodes; for other boundaries (Dirichlet, Neumann) separate boundary terms would appear.

This is a secondary layer relative to the maximum principle: it is stronger (it gives a quantitative measure of smoothing) but also more technical (it relies on convexity and shifts of sums). Both together are finite facts over ℚ.

*The $L^2$ energy $\sum u_j^2$ is a role-dissipating quantity: a measure of the concentration of the profile that averaging monotonically decreases. Dissipation is a role-rule (quantitative smoothing) built on top of the maximum principle (qualitative confinement to the box).*

## The Smoothing of an Impulse and the Boundary

Let us make the process tangible. Take a sharp impulse on a grid of four nodes—the value $1$ at one node, $0$ at the others—and take one step with $r=\tfrac14$. The peak settles from $1$ to $\tfrac12$, and the neighbors rise to $\tfrac14$: the profile $(1,0,0,0)$ passes into $(\tfrac12,\tfrac14,0,\tfrac14)$.[^7] The energy falls from $1$ to $\tfrac38$,[^8] in agreement both with the maximum principle (the peak did not grow) and with dissipation (the energy fell). This is smoothing in the flesh: a sharp peak spreads out over its neighbors.

*Where the boundary lies.* What is proved is the finite: one grid, a finite number of steps, exact rational values. The completed continuous solution $u(x,t)$, the limit of grid refinement ($\Delta x,\Delta t\to0$), the heat kernel (the Gaussian $\tfrac1{\sqrt{4\pi t}}
e^{-x^2/4t}$) as a ready object, and convergence to equilibrium as $t\to\infty$ are all role-limits. The process of smoothing is *directed* toward them, but ToS does not actualize them as objects: a finite process with the maximum principle and dissipation is enough.

## E/R/R Analysis: Diffusion as a Role-Averaging

### Setup

Let us analyze the constructed system—heat conduction as a process of smoothing—in terms of E/R/R, reading the E/R/R header of `ProcessHeatEquation.v`.[^9] This is an ontological comprehension and a reading of the header. The abbreviation sets the epistemic order (Elements $\to$ Roles $\to$ Rules); we conduct the analysis in the generating one.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the explicit scheme $u^{n+1}_j = r u_{j-1} + (1-2r) u_j + r u_{j+1}$, which for $0\le r\le\tfrac12$ is a convex averaging. Above it are two consequences: the maximum principle (a convex average does not leave the interval of values) and the dissipation of energy (Jensen plus cyclic shifts of sums). Crowning it is the stability condition $r\le\tfrac12$, which is also the nonnegativity of the weights. The universal E/R/R layer sets roles and rules; the concrete formal layer is the formula of the step, CFL, and finite rational inequalities.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The profile $u^n$ is the role-state (the distribution of heat in time). The rate $r$ is the role-weights of mixing. The interval $[ m,M ]$ is the role-invariant preserved by the maximum principle. Energy is the role-dissipating quantity. The condition $r\le\tfrac12$ is the role-mode (the weights are fractions). And the uniform profile toward which diffusion tends is the role-limit, not actualized as a completed solution.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite:
rational values at the nodes $u^n_j\inℚ$, the weights $r,1-2r\inℚ$, a finite grid, a finite step number. Under P4 neither the completed solution nor the heat kernel is an element: finite profiles at finite stages are actual.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| scheme $u^{n+1}_j=r u_{j-1}+(1-2r)u_j+r u_{j+1}$; maximum principle; dissipation; CFL $r\le\tfrac12$ | HOW the averaging is arranged and what it preserves | Rules ($L5$) |
| profile $u^n$; rate $r$; box invariant; energy; uniform limit | WHAT FOR the bearers are significant: roles in smoothing | Roles ($L4$) |
| $u^n_j\inℚ$; weights $r,1-2r$; finite grid; step number | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

{
The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is that the maximum principle is expressed as the preservation of an *interval-invariant*, not through the construction of the maximum and minimum as separate objects; and dissipation, as the monotonicity of a finite sum. Neither “the completed solution” nor “the limiting profile” enters as an element: averaging acts on a finite profile and produces a finite profile. That is precisely why heat conduction here needs neither the Gaussian nor the continuum limit.}

What the analysis yields. It translates the chapter into the language of structure: *diffusion is a Role-averaging*, *the maximum principle is a Rule of preserving the interval-invariant*, *dissipation is a Rule of monotone smoothing*, and the values $u^n_j$ and weights $r$ are *Elements*. To take the heat kernel or $u(x,t)$ as a completed object-Element is to put the role-limit in the place of an Element—the same confusion as “the solution of an ODE as a ready function” (Chapter 8.1). Heat conduction is a process of averaging; its limit is a direction, not a built entity.

The next chapter changes the role of the spatial operator: from smoothing diffusion to *propagation*. The wave equation does not average but transmits a disturbance with finite speed; its process core is causality.

---

[^1]: The supporting file is `ProcessHeatEquation.v` (directory `process/` of the ToS Rocq repository): `heat_step`, the maximum principle `heat_step_box`/`heat_iter_box`, dissipation `heat_step_energy`, the concrete smoothing `heat_peak_drops` and `heat_energy_decreased`. 8 proved statements, 0 axioms (`Print Assumptions`: “closed under the global context”). The instruments of dissipation come from `ProcessPDEGreen.v` (Chapter 9.1).
[^2]: Here, as was cautioned in Chapter 9.1, the *centered* Laplacian is used (not the repeated forward difference `dd`); the left neighbor on the periodic grid is the cyclic predecessor `ppred`.
[^3]: `heat_step` in `ProcessHeatEquation.v`; linearity is `heat_step_linear`. The condition $0\le r\le\tfrac12$ is exactly the nonnegativity of the weights: it is *also* the CFL stability condition.
[^4]: `heat_step_box` in `ProcessHeatEquation.v`: for $0\le r$ and $2r\le1$, `in_box u lo hi` implies `in_box (heat_step r N u) lo hi`. The proof is the nonnegativity of the weights plus the fact that they sum to one; there is no need to build the maximum or the minimum as separate objects—we work with the interval invariant. 0 axioms.
[^5]: `heat_iter_box`: for any number of steps, `in_box` is preserved. 0 axioms.
[^6]: `heat_step_energy` in `ProcessHeatEquation.v`: the nodewise Jensen `jensen3` (the nonnegativity of the variance of a three-point convex combination) plus the lemmas on the cyclic shift of a sum (`sum_pred_shift_periodic`, `sum_ns_shift_periodic` from `ProcessPDEGreen.v`, Chapter 9.1). 0 axioms.
[^7]: `heat_peak_drops`: `heat_step (1#4) 4 u_imp 0 == 1#2`. Exact rational arithmetic (`vm_compute`).
[^8]: `heat_energy_value` ($E = 3/8$) and `heat_energy_decreased` ($3/8 < 1$) in `ProcessHeatEquation.v`.
[^9]: The header labels directly: Rules—`heat_step` as a convex combination for $r\le\tfrac12$, the maximum principle, dissipation; Roles—$u^n$ the role-state, $r$ the role-rate, the box the role-invariant, energy the role-dissipating quantity; Elements—rational $u_j$, a finite grid, a step.

---

Part: [[09 Partial Differential Equations|Part IX. Partial Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/01 Solution as Process on a Space Time Grid|Chapter 1. The Solution as a Process on a Space-Time Grid]] · [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/03 Wave Equation Propagation|Chapter 3. The Wave Equation: Propagation]] →
