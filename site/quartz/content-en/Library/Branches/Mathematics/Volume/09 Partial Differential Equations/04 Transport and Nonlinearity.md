---
title: "Chapter 4. Transport and Nonlinearity"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/09 Уравнения в частных производных/04 Перенос и нелинейность.md"
sourceBlob: 3b0aa8e46fa3600f68c12c98f3b8b8b44156ffc2
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Third Role: Pure Motion

The triptych of Part IX closes with the third role of the spatial operator. Heat *smoothed*, the wave *propagated* a disturbance—while the transport (advection) equation

$$
\partial_t u + a \partial_x u = 0
$$

simply *moves* the profile as a whole, with constant speed $a$, without changing its shape. This is the simplest of the partial differential equations: its exact solution is the shifted initial data, $u(x,t) = u_0(x - at)$, the profile carried to the right.

Despite its simplicity, transport matters twice over. First, it demonstrates *conservation* in pure form: in transport nothing is created and nothing disappears; the total mass is unchanged. Second, it is the gateway to *nonlinearity*: as soon as the speed $a$ itself depends on the solution, linear transport turns into Burgers’ equation, in which shock waves arise, and from there a direct road leads to Navier–Stokes (Chapter 9.5).

### What This Chapter Claims—and What It Does Not

The proved core is over ℚ and concrete. The “upwind” transport scheme is defined on grid functions; for a Courant number $0\le\nu\le1$, the preservation of the box and of nonnegativity, the *conservation of total mass* on a periodic grid, and the exact shift of the profile at $\nu=1$ are proved.[^1]

What the chapter does *not* do: it does not formalize *nonlinear* transport (Burgers’ equation), shock waves, and weak (entropy) solutions. A discontinuous solution is a completed jump-object lying beyond the smooth process; here nonlinearity is an honestly marked boundary (§ “The Boundary of Nonlinearity: Burgers and Shock Waves”). Nor is the completed continuous solution $u(x-at)$ built: it is a role-limit.

Three levels. The *first* is the finite scheme over ℚ: upwind, conservation of mass, the box, the shift—proved without axioms. The *second* is the process *readings*: transport as a process of moving the profile, $\nu$ as the Courant number, mass as a conserved quantity. The *third*—nonlinear transport, shock waves, the completed solution—is a boundary and role-limits.

### The E/R/R Framework of the Chapter

The framework in the generating order; the full analysis is in § “Analysis in the Generating Order.” We rely on the E/R/R header of `ProcessTransport.v`. The chapter introduces the system of *transport as a process of moving the profile with conservation of mass*.

**Rules ($\leftrightarrow$ L5).** The upwind scheme $u^{n+1}_j = (1-\nu) u_j + \nu u_{j-1}$, where $\nu = a \Delta t/\Delta x$ is the Courant number; for $0\le\nu\le1$ this is a convex combination (preservation of the box and of nonnegativity); the total mass $\sum_j u_j$ is conserved; at $\nu=1$, an exact shift by one node; the CFL condition $\nu\le1$ (in this chapter it shows itself as the nonnegativity of the weights and the preservation of the box, not as a separate spectral estimate).

**Roles ($\leftrightarrow$ L4).** The profile $u^n$ is the role-state; $\nu$ is the role-Courant-number (by what fraction of a node the profile shifts in a step); the total mass is the role-conserved quantity; the shift is the role-transport; the speed $a$ is the role-velocity of motion.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational values
at the nodes $u^n_j$, a finite grid, a finite step. Under P4 the completed solution $u(x-at)$ and discontinuous (shock) objects lie outside the elements.

## The Upwind Scheme: A Step as a Shift-Averaging

Transport is directed (the speed $a>0$ moves the profile to the right), so a sensible scheme looks *upwind*—at the node on the left, from which the value comes:

$$
u^{n+1}_j \;=\; u^n_j - \nu (u^n_j - u^n_{j-1})
            \;=\; (1-\nu) u^n_j + \nu u^n_{j-1},
  \quad \nu = a \frac{\Delta t}{\Delta x}.
$$

As with heat, regrouping lays bare the structure: for $0\le\nu\le1$ the new value is a *convex average* of the current node and its left neighbor (the weights $1-\nu$ and $\nu$ are fractions).[^2] The stability condition $\nu\le1$ is again the requirement that the weights be nonnegative: the profile cannot shift by more than one node in a single step (information does not outrun the grid).

Two extreme cases are instructive. At $\nu=0$ (no motion) the profile stands still. At $\nu=1$ the weights become $(0,1)$, and the step is an *exact shift*: $u^{n+1}_j = u^n_{j-1}$—the whole profile moves exactly one node to the right, without distortion.[^3] For intermediate $\nu$ the profile moves and blurs slightly (numerical diffusion), but it always remains a convex average—hence all its properties.

*The transport step is a role-displacement: it shifts the profile by the fraction $\nu$ of a node, taking a weighted average with the upwind (upstream) neighbor—the node from which the flow comes (the value from node $j-1$ moves into node $j$). The Courant number $\nu$ is the role-fraction of displacement; the condition $\nu\le1$ is the role-mode in which information does not outrun the grid. At $\nu=1$ the displacement is exactly one node.*

## Conservation of Mass and Positivity

The principal property of transport is *conservation of mass*. The total mass $\sum_j u_j$ does not change with time: transport creates nothing and destroys nothing; it only moves. On a nonempty periodic grid this is proved directly:

$$
\sum_j u^{n+1}_j = (1-\nu)\sum_j u_j + \nu\sum_j u_{j-1} = (1-\nu)\sum_j u_j + \nu\sum_j u_j = \sum_j u_j,
$$

where we have used that the sum over the shifted nodes equals the sum over the original ones (a cyclic permutation of the nodes).[^4] It is essential that conservation of mass does not even require $\nu\le1$: mass is conserved for any Courant number, because transport is a redistribution.

And the convex structure (for $0\le\nu\le1$) gives two more properties. *Nonnegativity*: if the profile is nonnegative everywhere (a density, for example), it will remain so.[^5] And *box preservation*: the values do not leave their initial bounds—over the whole process.[^6]

*The total mass is a role-conserved quantity: transport does not change it, since it only moves the profile. Nonnegativity and the box are role-invariants of the convex step. This is a conservation law in its purest form: the quantity is fixed; only the position changes.*

## A Concrete Run

Take the profile $(5, 3, 0, 0)$ on a four-node grid: the total mass is $8$. A half step ($\nu=\tfrac12$) shifts and slightly blurs it, but the mass remains $8$.[^7] And a full step ($\nu=1$) carries the profile exactly one node: the value that was at node $0$ (equal to $5$) ends up at node $1$.[^8] Transport in the flesh: the same quantity, a new position.

## The Boundary of Nonlinearity: Burgers and Shock Waves

Linear transport is transparent because the speed $a$ is constant. But what if *the speed depends on the solution*? Replacing $a$ by $u$ itself, we obtain Burgers’ equation

$$
\partial_t u + u \partial_x u = 0 ,
$$

the simplest model of nonlinear transport. Here high values move faster than low ones, and the profile *steepens*: a smooth hump topples forward over time until the front becomes vertical. At this moment a *shock wave* is born—a discontinuity, a jump.

And here is the honest boundary. A discontinuity *is not a smooth stage* of the current linear process of transport: its correct description requires *weak* (entropy) solutions and selection conditions—a layer that ToS does not build here (process shock-capturing schemes are possible in principle, but that is a separate task). Nonlinear transport, shock waves, and entropy solutions are the boundary of the formalization of this Part.

But it is precisely this boundary that sets the road to the final chapter. The Navier–Stokes equations combine *all three* roles of the triptych: viscosity is diffusion (heat), pressure couples distant parts of the field through the incompressibility constraint, and the convective term $u\cdot\nabla u$ is exactly the Burgers nonlinearity carried over to three dimensions and vector form. The difficulty of Navier–Stokes is the difficulty of this nonlinear transport; and it is precisely energy methods (dissipation, as in heat) that give what is provable. Chapter 9.5 turns to them.

*Nonlinear transport is the boundary of the smooth process: when the speed becomes the solution itself, the profile steepens into a discontinuity, and the discontinuity is an object of the weak (entropy) limiting layer, not an element of the smooth grid scheme. Here ToS honestly stops at linear transport; nonlinearity is the direction toward Navier–Stokes, where dissipation tames it.*

## E/R/R Analysis: Transport as a Role-Motion

### Setup

Let us analyze the constructed system—transport as a process of moving the profile—in terms of E/R/R, reading the E/R/R header of `ProcessTransport.v`.[^9] This is an ontological comprehension and a reading of the header. The abbreviation sets the epistemic order (Elements $\to$ Roles $\to$ Rules); we conduct the analysis in the generating one.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the upwind scheme $u^{n+1}_j = (1-\nu)u_j + \nu u_{j-1}$, convex for $0\le\nu\le1$. Above it are conservation of mass (the cyclic shift of a sum), nonnegativity, and box preservation; at $\nu=1$, the exact shift. Crowning it is the stability condition $\nu\le1$ (the nonnegativity of the weights). Nonlinear transport (Burgers, shock waves) is a rule that goes beyond the smooth process and is left as a boundary. The universal E/R/R layer sets roles and rules; the concrete formal layer is the formula of the step, conservation of mass, the box, and CFL.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The profile $u^n$ is the role-state. The Courant number $\nu$ is the role-fraction of displacement per step. The total mass is the role-conserved quantity. The shift is the role-transport. The speed $a$ is the role-velocity of motion. And the completed solution $u(x-at)$ and the shock wave are the role-limit (and a boundary for the nonlinear case).

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite:
rational values at the nodes $u^n_j\inℚ$, the weights $1-\nu,\nu\inℚ$, a finite grid, a finite step. Under P4 neither the completed solution nor the discontinuity is an element: finite profiles at finite stages are actual.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| upwind $u^{n+1}_j=(1-\nu)u_j+\nu u_{j-1}$; conservation of mass; box; shift at $\nu=1$; CFL $\nu\le1$ | HOW the profile moves while conserving mass | Rules ($L5$) |
| profile $u^n$; Courant number $\nu$; mass; shift; speed $a$; solution $u(x-at)$ as a limit | WHAT FOR the bearers are significant: roles in motion | Roles ($L4$) |
| $u^n_j\inℚ$; weights $1-\nu,\nu$; finite grid; step | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

{
The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). It is essential that conservation of mass is expressed as an equality of finite sums (through a cyclic shift), not through an integral over a completed domain; that motion is the shift of a finite profile, not the evolution of a ready function $u(x-at)$; and that the discontinuity (the shock wave) is deliberately *not* taken as an element—it goes beyond the smooth process and is marked as a boundary. That is precisely why linear transport here is fully finite and rational, while nonlinear transport is honestly deferred.}

What the analysis yields. It translates the chapter into the language of structure: *transport is a Role-motion* of the profile; *conservation of mass is a Rule* (the quantity is fixed, the position changes); *the Courant number is a Role-fraction of displacement*; and the values $u^n_j$ are *Elements*. To take the completed solution or the shock wave as an object-Element is to put the role-limit (or an extra-process discontinuity) in the place of an Element. Linear transport is a finite process of motion with conservation of mass; nonlinearity is the direction toward Navier–Stokes.

The final chapter of the Part turns to this direction: the Navier–Stokes equations, where all three roles of the triptych converge—diffusion, transport, coupling—and where energy methods give dissipation and conditional regularity, while unconditional three-dimensional regularity remains an honest “wall.”

---

[^1]: The supporting file is `ProcessTransport.v` (`process/` in the ToS Rocq repository): `transport_step`, box preservation `transport_step_box`/`transport_iter_box`, nonnegativity `transport_step_nonneg`, conservation of mass `transport_mass`, the exact shift `transport_shift`, the concrete run `transport_mass_concrete` and `transport_full_shift`. 8 proved statements, 0 axioms (`Print Assumptions`: “closed under the global context”).
[^2]: `transport_step` in `ProcessTransport.v`; linearity is `transport_step_linear`. The left neighbor on the periodic grid is the cyclic predecessor `ppred`.
[^3]: `transport_shift`: `transport_step 1 N u j == u (ppred N j)`. The exact shift is the maximal motion per step that CFL admits.
[^4]: `transport_mass` in `ProcessTransport.v`: `sum_Q_ns (transport_step nu N u) N == sum_Q_ns u N`. It relies on `sum_pred_shift_periodic` (Chapter 9.1); it requires only $N>0$ (the cyclic shift of a sum) and does not depend on $\nu$. 0 axioms.
[^5]: `transport_step_nonneg`: for $0\le\nu\le1$, nonnegativity implies nonnegativity at the next step.
[^6]: `transport_step_box` and `transport_iter_box`: a convex combination keeps the values in $[ m,M ]$, as with heat.
[^7]: `transport_mass_concrete`: `sum_Q_ns (transport_step (1#2) 4 p_prof) 4 == 8`. Exact rational arithmetic.
[^8]: `transport_full_shift`: `transport_step 1 4 p_prof 1 == 5`.
[^9]: The header labels directly: Rules—the upwind step, a convex combination for $\nu\le1$, conservation of mass, the shift at $\nu=1$, CFL; Roles—$u^n$ the role-profile, $\nu$ the role-Courant, mass the role-conserved, the shift the role-transport; Elements—rational $u_j$, a finite grid.

---

Part: [[09 Partial Differential Equations|Part IX. Partial Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/03 Wave Equation Propagation|Chapter 3. The Wave Equation: Propagation]] · [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/05 Navier Stokes and Synthesis|Chapter 5. Navier–Stokes and Synthesis]] →
