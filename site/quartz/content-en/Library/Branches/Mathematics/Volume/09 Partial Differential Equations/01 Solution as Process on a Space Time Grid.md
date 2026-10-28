---
title: "Chapter 1. The Solution as a Process on a Space-Time Grid"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/09 Уравнения в частных производных/01 Решение как процесс на пространственно-временной сетке.md"
sourceBlob: fd32eb938e9c70eca37e5576e44bf01a2107327c
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Opening of Part IX

Part VIII solved ordinary differential equations: the evolution of a quantity in time, where the state is a single rational number $y_n$. Part IX takes the next step: *partial differential equations*, describing the evolution of a function that depends on both time and space. This is the language of all continuum physics—heat conduction, waves, transport, fluid flows.

The classical theory takes the solution of a partial differential equation as a *completed function* $u(x,t)$ on a domain, an element of the space $C^2$ or of a Sobolev space. ToS applies here the device that Part VIII carried as far as guarantees of convergence. For us the solution is a *process*, but now the state at step $n$ is no longer a number but a *grid function* $u^n$, which assigns a rational value to each node of the spatial grid (an instantaneous profile). The evolution is given by a finite-difference scheme

$$
u^{n+1}_j \;=\; u^n_j \;+\; \Delta t\cdot\bigl(\text{discrete spatial operator}\bigr)_j ,
$$

and the spatial derivative is replaced by a *finite difference*. Where Part VIII had a ladder of numbers $(1+1/N)^N$, Part IX has a ladder of *grid functions*; Euler’s method in time remains, and the discretization of space is added.

The present chapter is the framework of the whole Part. It introduces grid functions and finite differences, the discrete analogue of integration by parts (Green’s formula), and—what sets the structure of Chapters 9.2–9.4—*three types* of equations as *three roles* of the spatial operator.

### What This Chapter Claims—and What It Does Not

The proved core is finite discrete mathematics over ℚ. A grid function is a map $ℕ\toℚ$; the forward difference is the discrete gradient, and the second difference is the discrete Laplacian; summation by parts (Abel’s formula) and the discrete Green’s formula link energy with the gradient; the norm of the Laplacian is bounded by the norm of the gradient.[^1] All this consists of finite rational identities and inequalities.

What the chapter does *not* do: it does not build the completed solution function $u(x,t)$ as an object, does not prove the continuum limit (refinement of the grid down to zero), and does not introduce completed Sobolev spaces. These limits are role-limits; their process representatives and finite energy analogues (the discrete energy, the $L^2$ cores of Parts VI–VII) are compatible with P4, but as *completed objects* they remain a boundary.

Three levels of rigor, as in Part VIII. The *first* is finite discrete mathematics over ℚ: grid functions, finite differences, summation by parts, Green’s formula—proved without axioms. The *second* is the process *readings*: the solution as a process of grid functions, the spatial derivative as a difference, conservation laws as finite sums, stability as the Courant condition. The *third*—the completed continuous solution, the continuum limit, and Sobolev spaces—is role-limits and a direction. The chapter treats the first two as proved, and the third as an honestly marked boundary.

### The E/R/R Framework of the Chapter

The framework in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis is in § “Analysis in the Generating Order.” The chapter introduces the system of *the solution of a partial differential equation as a process on a space-time grid*.

**Rules ($\leftrightarrow$ L5).** The space-time grid ($x_j = j \Delta x$, $t_n = n \Delta t$); the finite-difference scheme $u^{n+1}_j = u^n_j + \Delta t\cdot(\mathcal L_h u^n)_j$, where $\mathcal L_h$ is the discrete spatial operator; finite laws (energy, mass, the maximum principle) as finite sums over the nodes; stability as the Courant condition (CFL).

**Roles ($\leftrightarrow$ L4).** The profile $u^n$ is the role-state (an instantaneous snapshot in time); the discrete operator $\mathcal L_h$ is the role-spatial-law (how the profile changes across space); the Courant number is the role-condition of stability; the completed $u(x,t)$ is the role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Grid functions
$u^n:\{0,…,N{-}1\}\toℚ$, the rational values at the nodes $u^n_j$, a finite spatial grid, a finite step number. Under P4 the completed solution function and the continuum limit lie outside the elements: finite grid functions at finite stages are actual.

## From ODE to PDE: The State Becomes a Function

An ordinary equation $y' = f(t,y)$ describes the evolution of a *number*: the state $y$ is a single quantity, and Euler’s method moves it in time, $y_{n+1} = y_n + h f(t_n,y_n)$. A partial differential equation $\partial_t u = \mathcal L u$ describes the evolution of a *function*: the state $u(\cdot,t)$ is a whole profile across space, and $\mathcal L$ is a spatial differential operator (the first derivative $\partial_x$, the Laplacian $\partial_x^2$, and so on).

The process device is the same on both levels, with one addition: not only time but also space is discretized. We divide space by a grid of nodes $x_j = j \Delta x$; the state $u^n$ becomes a grid function (values at the nodes); the operator $\mathcal L$ is replaced by a *discrete* operator $\mathcal L_h$ (a finite difference); and the scheme

$$
u^{n+1} \;=\; u^n + \Delta t\cdot \mathcal L_h  u^n
$$

is exactly Euler’s method in time, but *on the space of grid functions*. The whole apparatus of Part VIII—the Euler step, contraction, stability, Grönwall—carries over here; the only novelty is that the quantity moved by time is itself a function of space.

*The profile $u^n$ is the role-state: an instantaneous snapshot of the field in time. The solution of a partial differential equation is the role-limit of the process of such profiles $u^0, u^1, u^2,
…$, not a completed function $u(x,t)$. The stage-profile is actual; the continuous solution is a direction.*

## Finite Differences: The Derivative as a Difference

On a grid the spatial derivative becomes a *finite difference*. The forward difference is the discrete gradient:

$$
(\nabla_h u)_j \;=\; u_{j+1} - u_j ,
$$

and its repeated application is the discrete Laplacian (the second difference):

$$
(\Delta_h u)_j \;=\; u_{j+2} - 2u_{j+1} + u_j \;=\; (\nabla_h\nabla_h u)_j .
$$

These are finite rational operations on a grid function, without a passage to the limit.[^2] A technical caveat: this second difference is the *repeated forward* one ($u_{j+2}-2u_{j+1}+u_j$); for the classical scheme of heat conduction (Chapter 9.2) the *centered* form $u_{j+1}-2u_j+u_{j-1}$ is more convenient, and it is introduced there locally with an explicit caveat about indexing.

The key instrument of analysis is the discrete analogue of *integration by parts*. On a finite grid the role of the integral is played by the finite sum $\sum_{j} u_j$, and *summation by parts* (Abel’s formula) holds for it: the pairing of the difference of one function with another is transferred to the second with boundary terms, and on a periodic grid the boundary terms cancel.[^3] Hence the discrete *Green’s formula*, an energy identity linking the Laplacian with the gradient:

$$
\sum_j u_{j+1} (\Delta_h u)_j \;=\; -\norm{\nabla_h u}^2
  \quad\text{(periodic grid),}
$$

and the accompanying estimate $\norm{\Delta_h u}^2 \le 4 \norm{\nabla_h u}^2$.[^4] These identities are finite sums over ℚ; the continuous Green’s formula $\int u \Delta u = -\int|\nabla u|^2$ is their role-limit.

*A finite difference is a role-derivative: the place that the derivative occupies on a discrete grid. Green’s formula is a role-instrument: a rule that translates the spatial operator into an energy quantity. They are finite and rational; the continuous derivative and integral are their role-limits.*

## Three Types of Equations—Three Roles

The partial differential equations that Part IX analyzes differ in *what role* the spatial operator plays in the process. Three canonical types set a systematic triptych: the next three chapters.

**Parabolic—heat conduction** ($\partial_t u = \partial_x^2 u$, Chapter 9.2). The spatial operator is the Laplacian; the process *smooths*: each step replaces a value by a weighted average with its neighbors, and the profile spreads out. The role of the operator is *dissipation*: the energy decreases, and the maximum principle holds (values do not leave their initial bounds).

**Hyperbolic—the wave** ($\partial_t^2 u = c^2\partial_x^2 u$, Chapter 9.3). An equation of second order in time; the process *propagates*: a disturbance runs along the grid. The role of the operator is *finite speed*: causality, the front advances by at most one node per step.

**Transport—advection** ($\partial_t u + a \partial_x u = 0$, Chapter 9.4). The spatial operator is the first derivative; the process *moves* the profile without changing its shape. The role of the operator is *conservation*: the total mass does not change, and the profile only shifts.

All three are processes of grid functions on one space-time grid; the difference lies in the role of the spatial operator (smoothing, propagation, transport). The culmination is the Navier–Stokes equations (Chapter 9.5), a nonlinear system in which the same energy methods give dissipation and conditional regularity.

*The type of a partial differential equation is the role of the spatial operator in the process: the parabolic one smooths (dissipation), the hyperbolic one propagates (finite speed), the transport one carries (conservation). One process framework, three roles—and this is the structure of the whole Part.*

## E/R/R Analysis: The Solution as a Role-Process on a Grid

### Setup

Let us analyze the constructed system—the solution of a partial differential equation as a process on a space-time grid—in terms of E/R/R. A reservation about the level: the “system of the solution” here is a substantive *interpretation* of the construction (the grid plus the finite-difference scheme plus the discrete laws), not an object literally declared in the code as `System`. The analysis is an ontological comprehension of the structure of the Part and a reading of the author’s E/R/R headers of the supporting files,[^5] not an attribution of new formal claims to the code. As before, the abbreviation sets the epistemic order (Elements $\to$ Roles $\to$ Rules); we conduct the analysis in the generating one.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation are the space-time grid and the finite-difference scheme $u^{n+1} = u^n + \Delta t\cdot\mathcal L_h u^n$, where $\mathcal L_h$ is the discrete spatial operator (gradient, Laplacian). Above it is the discrete calculus: summation by parts and Green’s formula, which translate the operator into energy quantities. The construction is crowned by the finite laws—dissipation of energy, conservation of mass, the maximum principle—and the stability condition (CFL). The universal layer is the laws L1–L5; the concrete layer is the formulas of the differences and the scheme.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The profile $u^n$ is the role-state (a snapshot of the field in time). The discrete operator $\mathcal L_h$ is the role-spatial-law, and its concrete form decides the type: smoothing, propagation, or transport. The Courant number is the role-condition of stability. The discrete energy and mass are role-conserved (or role-dissipating) quantities. And the completed $u(x,t)$ and the continuum limit are the role-limit.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite:
grid functions $u^n:\{0,…,N{-}1\}\toℚ$, the values at the nodes $u^n_j\inℚ$, finite sums $\sum_{j<N}$, a finite grid, and a finite step number. Under P4 neither the completed solution function nor the continuum limit is an element: finite profiles at finite stages are actual; what is actualized is the process of refinement, not its limit.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| grid $x_j,t_n$; scheme $u^{n+1}=u^n+\Delta t \mathcal L_h u^n$; Green’s formula; laws; CFL | HOW the profile evolves and is controlled | Rules ($L5$) |
| profile $u^n$; operator $\mathcal L_h$ (type); Courant number; energy/mass; $u(x,t)$ as a limit | WHAT FOR the bearers are significant: roles in the process | Roles ($L4$) |
| grid functions $u^n_j\inℚ$; finite sums; grid; step number | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is what is *absent* here: the solution process does *not* take as its element “the function $u(x,t)$ as a completed object” or “the continuous domain.” Space is discretized by a finite grid, the derivative is a finite difference, and the laws (energy, mass, maximum) are checked as finite sums. It is precisely this finiteness of every stage that separates what is proved (the discrete calculus over ℚ, without axioms; the laws and stability of concrete schemes—in the following chapters, likewise as finite rational facts) from the boundary (the continuous solution and the limit—a role-limit).

What the analysis yields. It translates the design of the Part into the language of structure: *the solution is a Role-process* of grid functions; *the type of the equation is a Role* of the spatial operator; *a finite difference is a Role-derivative*; and the profiles $u^n_j$ and sums themselves are *Elements* (finite at every stage). To take “the solution” or a continuous function as a completed object-Element is to put the role-limit in the place of an Element—the same confusion of categories as “the solution of an ODE as a ready function” (Chapter 8.1) or “a point as an object” instead of a class (Chapter 4.3). A partial differential equation is solved not by extracting a ready function but by unfolding a process of profiles on a grid.

The next chapter presents the first and canonical process of this kind, the heat equation: diffusion as a process of smoothing, with the maximum principle and the dissipation of energy proved over ℚ.

---

[^1]: The supporting infrastructure is `GridFunction.v` and `FiniteDifference.v` (directory `navier_stokes/` of the ToS Rocq repository; grid functions, sums, norms, `fd`, `dd`, summation by parts `abel_summation`; ${\sim}45$ proved statements, 0 axioms), plus the new file `ProcessPDEGreen.v` (`process/`: the discrete Green’s formula and the estimate $\norm{\Delta u}^2\le 4\norm{\nabla u}^2$; 8 statements, 0 axioms, `Print Assumptions`: “closed under the global context”).
[^2]: `fd` (the forward difference) and `dd` (the second difference) in `FiniteDifference.v`; the identity `dd_eq_fd_fd`: the second difference is the composition of first differences. The linearity of both operators is in the same file, 0 axioms.
[^3]: `abel_summation` and `abel_periodic` in `FiniteDifference.v`: $\sum (\nabla_h f)_i  g_i + \sum f_{i+1}(\nabla_h g)_i = f_N g_N - f_0 g_0$, and for periodic functions the right-hand side is zero. 0 axioms.
[^4]: `green_dirichlet_periodic` and `lap_norm_bound` in `ProcessPDEGreen.v` (a new file of Part IX, checked with `Print Assumptions`: “closed under the global context”), 0 axioms, for the forward Laplacian. The energy estimate for heat conduction (Chapter 9.2) is given not by this identity directly but by convexity (Jensen’s inequality) together with the lemmas on the cyclic shift of a sum (`sum_ns_shift_periodic`, `sum_pred_shift_periodic`, in the same file); Green’s formula is a canonical discrete instrument in its own right.
[^5]: The headers label directly: `ProcessPDEGreen.v`—Elements: grid functions, finite sums; Roles: `fd` is the role-gradient, `dd` the role-Laplacian, Green’s formula the role-instrument; Rules: summation by parts, $\norm{\Delta u}^2\le4\norm{\nabla u}^2$.

---

Part: [[09 Partial Differential Equations|Part IX. Partial Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/08 Ordinary Differential Equations/05 Exponential Linear Equations Applications|Chapter 5. The Exponential, Linear Equations, Applications—Part VIII]] · [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/02 Heat Equation Diffusion as Smoothing|Chapter 2. The Heat Equation: Diffusion as Smoothing]] →
