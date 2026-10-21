---
title: "Chapter 5. Navier–Stokes and Synthesis"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/09 Уравнения в частных производных/05 Навье–Стокс и синтез.md"
sourceBlob: 104eb55db15c637f56a63450388c9d8d794d7721
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Culmination of the Triptych

The three preceding chapters analyzed the three roles of the spatial operator separately: heat conduction *smoothed*, the wave *propagated*, transport *moved* the profile. The Navier–Stokes equations—the equations of motion of a viscous incompressible fluid—combine *all three* in one system:

$$
\partial_t u + (u\cdot\nabla)u = -\nabla p + \nu \Delta u, \quad \nabla\cdot u = 0 .
$$

Here $\nu \Delta u$ is viscosity, the same diffusion as in heat; $(u\cdot\nabla)u$ is convection, nonlinear transport (the analogue of the Burgers nonlinearity in a vector field, Chapter 9.4); $-\nabla p$ and the condition $\nabla\cdot u = 0$ are the pressure, which couples the field through incompressibility. This is the crown of Part IX and one of the Millennium Prize Problems.

The chapter differs from the preceding ones in its status of honesty, and this must be said directly. First, the supporting NS cluster of ToS is a large formal layer, but it is *not* 0-axiom: it carries a domain axiom on the antisymmetry of the nonlinear term (plus `classic`). Second, three-dimensional regularity is proved only *conditionally*; unconditional regularity is an open problem, an honest “wall.” The chapter presents what is proved and outlines precisely what is not.

### What This Chapter Claims—and What It Does Not

The proved core is energetic, on the modal (Galerkin) process. *Unconditionally*: the energy dissipates and is bounded by the initial energy; two-dimensional flow is regular (there is no vortex stretching). *Conditionally* (in an invariant region, with subcritical enstrophy): three-dimensional regularity.[^1]

What the chapter does *not* do: it does not prove *unconditional* three-dimensional regularity (the Millennium Problem is open), does not build the completed continuous solution, and does not claim that the NS layer is 0-axiom. These frontiers are marked directly.

Three levels. The *first* is what is proved (with a domain axiom): the dissipation of energy, two-dimensional regularity unconditionally, three-dimensional regularity conditionally. The *second* is the process *readings*: NS as a combined process (diffusion ${}+{}$ convection ${}+{}$ coupling), regularity as a property of the process. The *third*—unconditional three-dimensional regularity, the completed solution—is an open boundary and a role-limit.

## Navier–Stokes as the Combination of the Triptych

Let us decompose the right-hand side into three familiar roles. *Viscosity* $\nu \Delta u$ is the diffusion of Chapter 9.2: the Laplacian smooths the velocity field, damping small scales; it is precisely viscosity that *dissipates* energy. *Convection* $(u\cdot\nabla)u$ is the transport of Chapter 9.4, but nonlinear: the field transports itself, and here lives the whole difficulty—the very Burgers nonlinearity that gave birth to shock waves. *Pressure* $-\nabla p$ with the condition $\nabla\cdot u = 0$ is a coupling that globally reconciles the field through the incompressibility condition (an elliptic constraint/projection, not wave transport).

ToS carries this as a process, a Galerkin (modal) one: the field is expanded over a finite number of modes, and the evolution of each amplitude is given by a system of ordinary equations with a *triadic* interaction $B(k,l,m)$ between the modes. The key property of the nonlinearity is expressed by a single structural axiom: the coefficient is antisymmetric, $B(k,l,m) = -B(k,m,l)$.[^2] Antisymmetry means that the nonlinearity only *redistributes* energy, as linear transport redistributed mass (Chapter 9.4). Then the only sink of energy is viscous diffusion.

*Navier–Stokes is the role-combination of the triptych: viscosity plays the role of diffusion, convection the role of nonlinear transport, pressure the role of coupling. The triadic coefficient with its antisymmetry is the role-rule of the conservation of energy by the nonlinearity; only diffusion dissipates.*

## The Energy Method and Dissipation

From the antisymmetry of the nonlinearity follows the *energy identity*: the rate of change of energy equals minus twice the viscosity times the enstrophy,

$$
\frac{dE}{dt} = -2 \nu \Omega \le 0 .
$$

In the modal (Galerkin) layer this is written as an evolution identity for the rate of energy (`energy_rate_formula`, over rational processes); the classical notation $dE/dt$ is its continuous reading. Here $\Omega$ is the enstrophy (the norm of the gradient/vorticity). Convection does not enter this equation (antisymmetry has removed it), nor does pressure; only the viscous sink remains. Therefore the energy *decreases monotonically* and is bounded by the initial energy, $E(t)\le E(0)$—and this is an *unconditional* result.[^3] It is a direct relative of the dissipation of heat (Chapter 9.2): there the $L^2$ energy of the profile decreased, here the kinetic energy of the flow, and for the same reason—because of the Laplacian.

The energy method is the principal instrument of NS theory. It gives unconditional control over the energy; the question of regularity is the question of control over *higher* norms (the enstrophy and beyond), and here the two-dimensional and three-dimensional cases diverge.

*The energy of the flow is a role-dissipating quantity, as in heat: its only sink is viscous diffusion. The energy identity $dE/dt=-2\nu\Omega$ is a role-rule; it is unconditional and is the foundation of everything proved about NS.*

## Two Dimensions, Three Dimensions, and the “Wall”

The difference between the dimensions lies in *vortex stretching*. In two dimensions vorticity is a scalar transported by the flow; there is no mechanism for its amplification, and the stretching is identically zero. Therefore the enstrophy remains under control, and in the formal Galerkin (modal) layer of the cluster two-dimensional flow is *unconditionally regular*.[^4]

In three dimensions vorticity is a vector, and the flow can *stretch* it, amplifying the enstrophy. The energy method controls the energy but not the enstrophy: a gap arises. In the same modal layer regularity is proved *conditionally*: if the field remains in an invariant region (the enstrophy is subcritical relative to $\nu$), it is regular; but that the system gets there and stays there *unconditionally* is not proved.[^5]

Here stands the honest “wall.” Unconditional three-dimensional regularity is an open Millennium Problem; in ToS it is marked precisely: between two exponents (the quadratic nonlinearity and what would be needed for unconditional control) lies a gap that no known technique closes.[^6] ToS does not claim to solve it—it formalizes *what exactly* is provable (dissipation, two-dimensional regularity, conditional three-dimensional regularity) and *where* the boundary runs.

*Regularity is a role-property of the process (whether the higher norms remain under control). In two dimensions it is unconditional; in three it is conditional, and unconditional three-dimensional regularity is an open boundary, an honest “wall.” ToS outlines the frontier rather than passing off the desired as proved.*

## The Synthesis of Part IX

Part IX carried one system—*a partial differential equation as a process of grid functions on a space-time grid*—through four roles of the spatial operator. Let us gather its E/R/R structure and the map of boundaries.

**The unified structure.** *Rules*: at all levels, the grid, the finite-difference scheme $u^{n+1}=u^n+\Delta t \mathcal L_h u^n$, and the finite laws (energy, mass, causality, maximum). *Roles*: the profile $u^n$ is the role-state; the spatial operator $\mathcal L_h$ is a role, and its form sets the type (smoothing / propagation / transport / their combination in NS); stability is the role-mode (CFL). *Elements*: rational values at the nodes, finite grids and steps; completed solutions lie outside the elements (P4).

**The map of boundaries of Part IX.** What is proved falls into three honest layers:

| **Chapter** | **Proved core** | **Status** |
|---|---|---|
| 9.2 Heat | maximum principle, dissipation of energy, CFL | 0 axioms |
| 9.3 Wave | causality, finite speed | 0 axioms |
| 9.4 Transport | conservation of mass, box, shift | 0 axioms |
| 9.5 Navier–Stokes | dissipation, 2D regular, 3D conditionally | 1 domain axiom (+ L3) |
| Boundary of the whole Part | continuum limit, weak solutions in $L^2$/Sobolev, shock waves, unconditional 3D regularity | role-limits / open |

The triptych (heat, wave, transport) is 0-axiom over ℚ; Navier–Stokes is richer in proofs but honestly carries one domain axiom and runs up against the open three-dimensional wall. The continuum limit, weak solutions, and completed equations are the single role-limit boundary of the whole Part.

*A partial differential equation is a role-process of grid functions; the type of the equation is a role of the spatial operator; conservation laws and estimates are finite sums; stability is CFL; the completed solution is a role-limit. Navier–Stokes combines all the roles and leads up to the honest boundary of knowledge, an open Millennium Problem.*

## Closing

From numbers to processes, from processes to equations of change—such was the path. Part II showed number as a role-quantity; the Parts on analysis, the limit as a process rather than a completed object; Part VIII, the solution of an ordinary equation as a Cauchy process of approximations; Part IX, the solution of a partial differential equation as a process of grid functions on a space-time grid. One ontology held everything: the finite is actual, rational at every stage; infinity and continuity are role-limits toward which processes are directed, but which in many key finite layers need not be actualized as a completed foundation in order to carry on mathematics.

Partial differential equations are the ultimate test of this view, for it is precisely here that the continuum seems ineliminable. Part IX has shown that here too the substantive core is finite and rational: heat smooths, the wave propagates, transport moves, and Navier–Stokes combines them and leads up to the honest boundary of open knowledge. The completed continuum remains a direction, not a foundation.

*The solution of a partial differential equation is a process of finite rational profiles, not a completed function of the continuum; the types of equations are roles of the spatial operator; and the boundary of the provable—from the continuum limit to three-dimensional regularity—is outlined honestly. Such is the outcome of Part IX and the image of the whole volume: mathematics as a process whose limits are roles, not things.*

---

[^1]: The supporting cluster is the directory `navier_stokes/` of the ToS Rocq repository: `energy_bounded_by_initial` (`EnergyEstimate.v`, $E(t)\le E(0)$ unconditionally), `unconditional_2d` (`AttackSynthesis.v`, two-dimensional stretching is zero), `conditional_regularity_theorem` (three-dimensional regularity under a condition), `millennium_gap_precise` (the precise formulation of the open gap). *Axioms:* the cluster carries `B_antisym` (the antisymmetry of the triadic coefficient, `GalerkinSystem.v`—exactly one domain axiom) and `classic` (L3); this is *not* a 0-axiom layer, unlike the triptych of Chapters 9.2–9.4. Exact names and counts follow the repository’s `README`/`CLAUDE`.
[^2]: `B_antisym` in `GalerkinSystem.v` is the only axiom of the file. It formalizes that convection *conserves* energy (it only transfers it between modes), neither creating nor destroying it—the discrete analogue of $\int (u\cdot\nabla u)\cdot u = 0$.
[^3]: `energy_rate_formula` (`GalerkinSystem.v`: $dE/dt=-2\nu\Omega$; the nonlinear contribution is zero—`nonlinear_energy_zero`) and `energy_bounded_by_initial`, `energy_monotone` (`EnergyEstimate.v`): $E$ is monotone and bounded by the initial energy, unconditionally. They rely on `B_antisym`.
[^4]: `unconditional_2d`: `stretching_2d == 0` (`AttackSynthesis.v`). The absence of stretching is the reason for unconditional two-dimensional regularity.
[^5]: `conditional_regularity_theorem` and the invariant region (`ConcentrationBound.v`, `EnergyEstimate.v`): with subcritical enstrophy, regularity is preserved. There is no unconditional passage into this region—this is the gap.
[^6]: `millennium_gap_precise` (`AttackSynthesis.v`): the precise formulation of the gap, $\alpha=2$ versus $\alpha=1$; it is accompanied by an honest assessment (`HonestAssessment.v`) that the problem remains open.

---

Part: [[09 Partial Differential Equations|Part IX. Partial Differential Equations]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/09 Partial Differential Equations/04 Transport and Nonlinearity|Chapter 4. Transport and Nonlinearity]] · [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/01 Set as a System Not an Object|Chapter 1. Set as a System, Not an Object—Part X]] →
