---
title: "Chapter 3. The Wave Equation: Propagation"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/09 Уравнения в частных производных/03 Волновое уравнение распространение.md"
sourceBlob: 690f263f9c1c412901a83002a7f76bdc0f2b5a64
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### From Smoothing to Propagation

The heat equation (Chapter 9.2) *smoothed*: the spatial operator played the role of averaging, and the process damped out inhomogeneities. The wave equation

$$
\partial_t^2 u \;=\; c^2 \partial_x^2 u
$$

changes the role of the same Laplacian: now it does not dissipate but *propagates*. A disturbance does not settle but runs through the medium with finite speed $c$. This is the hyperbolic type, the second of the triptych of Part IX.

The key difference from heat is the *second order in time*. To take a step, one must know not one but *two* previous states: the current $u^n$ and the past $u^{n-1}$ (the analogue of position and velocity). And the principal process content of the wave is neither the maximum principle nor dissipation but *causality*: a disturbance at a node can come only from its nearest neighbors, so the front propagates by at most one node per step.

### What This Chapter Claims—and What It Does Not

The proved core is causality over ℚ. The leapfrog scheme is defined on pairs of grid functions; *local causality* (a finite domain of dependence) and the *finite speed of propagation* (a quiet region stays quiet in its interior) are proved, and the propagation of an impulse is computed exactly.[^1]

What the chapter does *not* do: it does not prove the *conservation of energy* of the wave. For the leapfrog scheme the discrete energy has a nonobvious form (depending on two levels), and its conservation is a technically delicate, design-sensitive result; here it is honestly left as a boundary (see § “Energy and the Boundary”), and causality serves as the proved core. Nor are the completed continuous wave, dispersion analysis, and the behavior as $t\to\infty$ built: these are role-limits.

Three levels. The *first* is the finite scheme over ℚ: leapfrog, local causality, finite speed, concrete propagation—proved without axioms. The *second* is the process *readings*: the wave as a process of propagation, finite speed as causality, the pair of levels as the state. The *third*—conservation of energy, the completed wave, and dispersion—is a boundary and role-limits.

### The E/R/R Framework of the Chapter

The framework in the generating order; the full analysis is in § “Analysis in the Generating Order.” We rely on the E/R/R header of `ProcessWaveEnergy.v`. The chapter introduces the system of *the wave as a process of propagation with finite speed*.

**Rules ($\leftrightarrow$ L5).** The leapfrog scheme
$u^{n+1}_j = 2u^n_j - u^{n-1}_j + s (u^n_{j+1} - 2u^n_j + u^n_{j-1})$, where $s =
c^2(\Delta t/\Delta x)^2$; a finite domain of dependence (a value depends only on three neighbors and its own past); hence finite speed—at most one node per step. The stability condition (CFL) $c^2\le1$ is needed for the energy layer (the boundary of the chapter), not for causality itself.

**Roles ($\leftrightarrow$ L4).** The pair $(u^n, u^{n-1})$ is the role-state (two levels are needed: second order in time); $s$ is the role-Courant-number (squared); the front of the disturbance is the role-boundary of propagation; finite speed is the role-causality.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** Rational values
at the nodes on two time levels, a finite grid. Under P4 the completed wave and the dispersion limit lie outside the elements.

## Leapfrog: The Wave as a Distributed Oscillation

We discretize the wave equation by centered differences in time and in space. The second difference in time, $(u^{n+1}_j - 2u^n_j + u^{n-1}_j)/\Delta t^2$, is set equal to $c^2$ times the spatial Laplacian; solving for the new level, we obtain the *leapfrog* scheme:

$$
u^{n+1}_j \;=\; 2u^n_j - u^{n-1}_j + s \bigl(u^n_{j+1} - 2u^n_j + u^n_{j-1}\bigr),
  \quad s = c^2\Bigl(\tfrac{\Delta t}{\Delta x}\Bigr)^2 .
$$

Unlike heat, here *two* previous levels are needed: the current profile $u^n$ and the past one $u^{n-1}$. This is a direct consequence of the second order in time—just as an ordinary oscillator needs both position and velocity.[^2]

The connection with Part VIII is literal here. The harmonic oscillator $y'' = -y$ (Chapter 8.5) was *one* oscillating point. The wave equation is a *chain* of such oscillators coupled by the Laplacian: each node oscillates, pushed by its neighbors, $u''_j = c^2(u_{j+1} - 2u_j + u_{j-1})$. A wave is a *distributed oscillation*, and propagation is the transmission of a disturbance along a chain of couplings. (The hierarchy “oscillation $\to$ vibration $\to$ wave” is traced in the acoustics layer of the repository.)

*The pair $(u^n, u^{n-1})$ is the role-state of the wave: the second order in time requires two levels, as an oscillator requires position and velocity. The Laplacian here plays the role-coupling between neighboring oscillators, not the role-averaging, as in heat. The wave is a role-process of propagation along this coupling.*

## Causality: A Finite Domain of Dependence

The principal process content of the wave is *causality*. Look at the scheme: the new value $u^{n+1}_j$ is expressed only through $u^n$ at the nodes $j-1, j, j+1$ and through $u^{n-1}$ at the node $j$ itself. No distant nodes enter the formula. This is a *finite domain of dependence*: the value at a node is determined only by its immediate neighborhood.

Hence, immediately, local causality: if the wave is “silent” at a node and its neighbors (and was silent there at the previous step), it will remain silent at this node further on:

$$
u^n_{j-1} = u^n_j = u^n_{j+1} = 0,\quad u^{n-1}_j = 0
  \quad\Longrightarrow\quad u^{n+1}_j = 0 .
$$

A disturbance cannot arise from nothing—it can only come from a neighbor.[^3]

*The finite domain of dependence is the role-rule of causality: the future of a node is determined only by its present neighborhood and its own past. This is the primary content of the wave—not smoothing and not dissipation, but the *locality* of propagation.*

## The Finite Speed of Propagation

Local causality, applied across the whole quiet region, gives *finite speed*. If both levels of the wave are zero on an interval of nodes $[a,b]$, then after a step the wave is still zero on its *interior* $[a+1, b-1]$: a disturbance penetrates the quiet region by at most one node from each edge.[^4] In $n$ steps the front advances by at most $n$ nodes—this is the finite speed of propagation (no faster than one node per step), the discrete analogue of the cone of influence.

Let us make this tangible. Place a sharp impulse at node $2$ of a five-node grid (zero initial “velocity”: the past level is zero) and take a step with $s=\tfrac12$. The peak at node $2$ becomes equal to $1$; the *neighboring* nodes $1$ and $3$ receive the value $\tfrac12$—the disturbance has reached them; and nodes $0$ and $4$, which are *two* steps away, remain zero—the front has not yet reached them.[^5] This is finite speed in the flesh: in one step the disturbance spreads by exactly one node in each direction.

*The front of the disturbance is the role-boundary of propagation, and it moves with finite speed: at most one node per step. The finiteness of the speed is a role-consequence of the finite domain of dependence; unlike heat, where the local step plays the role of averaging, here the local step plays the role of transmitting the front.*

## Energy and the Boundary

The continuous wave conserves *energy*, the sum of kinetic and potential energy, $E = \tfrac12\int\bigl[(\partial_t u)^2 + c^2(\partial_x u)^2\bigr]$. For the leapfrog scheme there exists a discrete conserved analogue, but its form is *nonobvious*: the stable discrete energy links *two neighboring time levels* by a cross term, and its conservation is a technically delicate result, sensitive to the choice of energy. Honestly: in the present exposition it is *not* proved; causality (finite speed) serves as the proved core, and the discrete conservation of the wave’s energy is left as a boundary—the natural next increment of the formalization.

Thus the boundary of the chapter is wider than for heat. Besides the completed continuous wave $u(x,t)$, the continuum limit, and dispersion analysis (how the speed changes with the wavelength), the *conservation of energy* is here also an honestly marked frontier, not a proved fact. What is proved is the finite and the robust: causality and the finite speed of propagation over ℚ. This is enough to carry on the wave as a process with a finite cone of influence, without calling into existence either the completed wave or its energy as a ready invariant.

*Conservation of energy is an invariant classically expected for the continuous wave; for the leapfrog scheme it requires a special discrete energy and is left here as a boundary of the formalization (it can be proved without passing to the limit as well—it simply has not been done here). The robust process content of the wave is causality: the finite domain of dependence and finite speed, proved over ℚ.*

## E/R/R Analysis: The Wave as a Role-Propagation

### Setup

Let us analyze the constructed system—the wave as a process of propagation—in terms of E/R/R, reading the E/R/R header of `ProcessWaveEnergy.v`.[^6] This is an ontological comprehension and a reading of the header. The abbreviation sets the epistemic order (Elements $\to$ Roles $\to$ Rules); we conduct the analysis in the generating one.

### Analysis in the Generating Order

**Rules ($\leftrightarrow$ L5).** At the foundation is the leapfrog scheme $u^{n+1} = 2u^n - u^{n-1} + s \Delta_h u^n$ with a finite domain of dependence. Above it is causality: local (zeros in a neighborhood give zero) and global (a quiet region stays quiet in its interior), whence finite speed. The stability condition $c^2\le1$ (CFL) and the conservation of energy belong to the energy layer, left as a boundary; the proved core is causality and finite speed. The universal E/R/R layer sets roles and rules; the concrete formal layer is the leapfrog formula and causality.

**Roles ($\leftrightarrow$ L4).** The rules set the roles. The pair $(u^n, u^{n-1})$ is the role-state (the second order requires two levels). The Laplacian is the role-coupling between neighboring oscillators. The Courant number $s$ is the role-mode of stability. The front of the disturbance is the role-boundary of propagation, moving with finite speed. And the completed wave is the role-limit; the discrete conservation of energy is a boundary of the formalization.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite:
rational values at the nodes on two time levels, a finite grid, the Courant number $s\inℚ$. Under P4 neither the completed wave nor the dispersion limit is an element: finite profiles at finite stages are actual.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| leapfrog $u^{n+1}=2u^n-u^{n-1}+s\Delta_h u^n$; finite domain of dependence; finite speed (CFL/energy—a boundary) | HOW a disturbance propagates | Rules ($L5$) |
| pair $(u^n,u^{n-1})$; Laplacian-coupling; Courant number; front; energy as a limit | WHAT FOR the bearers are significant: roles in propagation | Roles ($L4$) |
| rational values on two levels; finite grid; $s\inℚ$ | WHAT exists at each stage (finite, P4) | Elements ($L1$, P4) |

### Well-Formedness Check and What the Analysis Yields

The system is well-formed: each component falls into exactly one E/R/R category, and there is no self-reference (P1). What is essential is that the state of the wave is a *pair* of levels, not a single profile: an attempt to make do with one level would confuse the second-order role-state with the first-order one. And it is essential that causality is expressed through the finite domain of dependence—a finite fact about the formula of the step—not through a completed cone of influence as an object. That is precisely why the wave here needs neither a completed energy nor the continuum limit: propagation is a process with finite speed.

What the analysis yields. It translates the chapter into the language of structure: *the wave is a Role-propagation*; *the Laplacian is a Role-coupling* (not averaging); *finite speed is a Role-consequence* of locality; and the values on two levels are *Elements*. To take the completed wave or its energy as an object-Element is to put the role-limit in the place of an Element. The wave is a process of propagation with finite speed; its energy and the continuum limit are a direction, not built entities.

The next chapter closes the triptych with the third role of the spatial operator, *transport*: the advection equation neither smooths nor propagates an oscillation but *moves the profile* as a whole, preserving mass.

---

[^1]: The supporting file is `ProcessWaveEnergy.v` (`process/` in the ToS Rocq repository): `wave_step`, local causality `wave_step_local_zero`, finite speed `wave_step_interior_zero`, concrete propagation `wave_reaches_neighbor` and `wave_finite_speed_concrete`. 6 proved statements, 0 axioms (`Print Assumptions`: “closed under the global context”). A related earlier file is `acoustics/WavePropagation.v`.
[^2]: `wave_step` and its linearity `wave_step_linear` in `ProcessWaveEnergy.v`.
[^3]: `wave_step_local_zero` in `ProcessWaveEnergy.v`: if the three neighboring current values and the node’s own past are zero, the next value is zero. The proof is the substitution of zeros into the formula of the step. 0 axioms.
[^4]: `wave_step_interior_zero` in `ProcessWaveEnergy.v`: the vanishing of both levels on $[a,b]$ implies the vanishing of the next level on $[a+1,b-1]$. 0 axioms.
[^5]: `wave_reaches_neighbor`: `wave_step (1#2) 5 wzero wimp 1 == 1#2` (the neighbor is reached); `wave_finite_speed_concrete`: `wave_step (1#2) 5 wzero wimp 0 == 0` (the node at distance 2 is not reached); `wave_peak_value`: the peak $=1$. Exact rational arithmetic.
[^6]: The header labels directly: Rules—leapfrog, the finite domain of dependence, finite speed, CFL $c^2\le1$; Roles—$(u^n,u^{n-1})$ the role-pair, $s$ the role-Courant, the front the role-boundary, finite speed the role-causality; Elements—rational values on two levels, a finite grid.

---

Part: [[09 Partial Differential Equations|Part IX. Partial Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/02 Heat Equation Diffusion as Smoothing|Chapter 2. The Heat Equation: Diffusion as Smoothing]] · [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/04 Transport and Nonlinearity|Chapter 4. Transport and Nonlinearity]] →
