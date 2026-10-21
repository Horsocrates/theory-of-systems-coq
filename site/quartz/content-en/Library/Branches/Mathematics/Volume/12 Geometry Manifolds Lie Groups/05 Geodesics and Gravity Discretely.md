---
title: "Chapter 5. Geodesics and Gravity, Discretely"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/12 Геометрия, многообразия, группы Ли/05 Геодезические и гравитация дискретно.md"
sourceBlob: cf68fd2945659ff4c4e1429c37c4f31ddb77517c
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapters 12.3–12.4 built the symmetries of geometry—rotation groups and their Lie algebra. Now Part XII passes to *motion through geometry*: to *geodesics* (the straightest paths) and to the way curvature (12.2) manifests itself as *gravity*. The classical theory takes a geodesic as the solution of a differential equation on a smooth manifold, and gravity as the continuous Einstein equation for the curvature tensor. ToS makes a discrete move:

- a “geodesic” is a *role-extremal*—the shortest *discrete* path (the limit of discrete paths), or a rational orbital extremal;
- “gravity” is *curvature-as-defect* (12.2): the Regge angular defect *is* gravitational curvature, and the Regge action is the discrete analogue of Einstein–Hilbert;
- “tides” are *geodesic deviation*: the divergence of neighboring paths *is* curvature—the Element side of the identity “gravity ${}={}$ curvature”;
- the smooth geodesic equation, the continuous Einstein equation, and the curvature tensor over $ℝ$ are *role-limits* (the continuum price of Part X), whose map is given in 12.6.

*A reservation about the boundary of the volume.* The dynamics of gravity is the subject of a separate volume on physics. Here Part XII only *closes the geometric thread*: the geodesic as an extremal and the identity “curvature-defect ${}={}$ gravity,” over $ℚ$ and with reference to the already built Regge layer; the full physics is not duplicated.

*A geodesic is a role-extremal (the shortest discrete path); gravity is curvature-defect (Regge); tides are geodesic deviation. The smooth Einstein equation is a role-limit; the dynamics is in the volume on physics.*

## The Geodesic as a Role-Extremal

A geodesic is an *extremal*: the shortest (or straightest) path between points. ToS holds it *discretely*, and it has two faces.

*The first is the shortest discrete path.* A path is a finite list of rational points; its length is the sum of the distances (rational, in the $\ell^1$ metric, without roots). Then it is provable that *every* path is at least as long as the straight distance between its endpoints, that the two-point path (the one-step realization of the distance) *attains* this minimum, and that inserting a point *on* a segment does not change the length. The proved finite core is precisely this *minimality* and *invariance under refinement*; “the limit of discrete paths” is a role-reading of this core (in $\ell^1$ the minimum is attained already at every finite stage).[^1] Straightness ceases to be a differential condition and becomes a *rule*: the triangle inequality rules out any shortcut by way of a detour.

*The second is the rational orbital extremal.* A geodesic in a gravitational field is an orbit, an extremal of the effective potential. ToS computes it over $ℚ$ on concrete examples: the effective potential, the radius of the innermost stable circular orbit (ISCO), Kepler’s law $T^2/r^3$—all in rational quantities.[^2] Both faces are one role: a geodesic is an *extremal*, realized over $ℚ$ as the shortest discrete path or as a rational orbit, not as the solution of a continuum equation.

*A geodesic is a role-extremal: the shortest discrete path (every path $\geq$ the straight one, invariance under refinement—the limit of discrete paths) or a rational orbit (ISCO, Kepler $T^2/r^3$). Straightness is a rule (the triangle inequality), not a differential condition.*

## Deviation and Tides: Curvature as Force

How does a geodesic “know” about curvature? From *deviation*: two neighboring geodesics in a curved space approach or diverge, and the rate of their divergence *is* curvature. This is the geometric name of the *tidal force*: gravity is felt not as an absolute acceleration (free fall removes it—the equivalence principle) but as the *relative* acceleration of neighboring paths.

ToS holds this too discretely and rationally. On a flat patch neighboring paths do not deviate (zero deviation); curvature changes their relative length—in the rational model of the file this is expressed as shortening (a closed path in curvature is shorter than a flat one); locally, free fall is indistinguishable from inertia (the equivalence principle); and the difference of curvature at the source and at the receiver gives the *gravitational redshift*—all in finite rational quantities.[^3] Curvature is not an independent force on top of geometry but a *rule of deviation* of paths; in this geometric P4 frame, “the force of gravity” is read first of all as a role of divergence, not as a primary Newtonian force field.

*Curvature is felt as geodesic deviation (tides): on a plane there is no divergence, curvature shortens, a fall is locally indistinguishable from inertia, the difference of curvature gives the redshift. The force of gravity is a geometric role of the divergence of paths, not an independent Newtonian force.*

## Regge Curvature as Discrete Gravity

Let us gather the thread together. Curvature in ToS (12.2) is an *angular defect*; gravity is curvature; therefore *gravity is an angular defect*. This thesis is formalized by the Regge calculus. On a triangulated space each “hinge” carries a defect $\delta$, and the gravitational *action* is the sum of the defects weighted by the areas of the hinges,

$$
S_{\text{Regge}} \;=\; \sum_{\text{hinges}} \delta \cdot (\text{area}),
$$

—the discrete analogue of the Einstein–Hilbert action $\int R \sqrt{g}$. A flat lattice has zero defect and zero action; curving gives a nonzero rational defect.[^4] Thus gravity over $ℚ$ is presented *as geometry*: a rational defect on the hinges, whose variation gives the discrete field equation.

Here the geometric thread of Part XII joins physics—and here, too, runs the boundary of the volume. The *dynamics* of gravity (evolution, solutions, observables) is developed by a separate volume on physics; for Part XII only the *geometric identity* matters: curvature-defect *is* gravity, and it is finite and rational at every stage. The continuous Einstein equation for a smooth tensor is a role-limit (12.6).

*Gravity ${}={}$ curvature-defect: the Regge action $\sum\delta\cdot$ area is the discrete Einstein–Hilbert, flat ${}\Rightarrow{}$ zero. The geometric identity is finite and rational; the dynamics is in the volume on physics, and the continuous Einstein equation is a role-limit.*

## E/R/R Analysis

Let us assemble the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | geodesic ${}={}$ the rule of the extremal (the triangle inequality; the shortest path); the orbital extremal (the effective potential); the deviation of neighboring paths ${}={}$ curvature; the Regge action $\sum\delta\cdot$ area ${}={}$ the discrete Einstein–Hilbert |
| *Roles* (L4) | geodesic ${}={}$ role-extremal (the limit of discrete paths); gravity ${}={}$ the role of curvature-defect; tides ${}={}$ the role of deviation; “the force of gravity” ${}={}$ the role of the divergence of paths |
| *Elements* (L1${}+{}$P4) | finite data over $ℚ$: lists of path points and their $\ell^1$ lengths; rational ISCO/Kepler/free fall; Regge defects (in units of $\pi$) and the areas of the hinges; the smooth geodesic equation and the continuous Einstein equation over $ℝ$ are *not* Elements |

**Well-formedness.** The geodesic is well-formed as an extremal: every path $\geq$ the straight one (the triangle inequality), the straight path attains the minimum, and refinement does not change it. Gravity is well-formed as a defect: a flat lattice ${}\Rightarrow{}$ zero Regge action.

**What it yields.** The geodesic: the shortest discrete path (0 axioms) and a rational orbit (ISCO, Kepler); deviation: curvature as tides (shortening, redshift, equivalence); Regge: gravity as a defect ($\sum\delta\cdot$ area ${}={}$ the discrete Einstein–Hilbert).

**Diagnosis.** The root error is the reification of *the geodesic as the solution of a continuum equation* and of *gravity as a continuous tensor field*. ToS returns them to their category: the geodesic is a role-extremal (the rule of the shortest path), gravity is curvature-defect (a rule).

**Honest boundaries.** The smooth geodesic equation, parallel transport and the connection, and the continuous Einstein equation over $ℝ$ are role-limits (the continuum price of Part X). The dynamics of gravity belongs to a separate volume on physics. The full map is in 12.6.

*The geodesic is a role-extremal (the shortest path ${}+{}$ the orbit), curvature is felt as deviation (tides), gravity ${}={}$ the Regge defect. The Element side is finite and rational; the smooth equations and the dynamics are role-limits and the volume on physics.*

## Summary and Transition

The chapter has closed the geometric thread of motion. The *geodesic* has become a role-extremal—the shortest discrete path (every path is at least as long as the straight one; refinement does not change the length—the limit of discrete paths) or a rational orbit (ISCO, Kepler $T^2/r^3$). *Curvature* has manifested itself as the *deviation* of neighboring geodesics—the geometric name of the tidal force; “gravity” has turned out to be not a field but a role of the divergence of paths. And the identity has closed: curvature-defect (12.2) *is* gravity—the Regge action $\sum\delta\cdot$ area as the discrete Einstein–Hilbert. The dynamics is developed by a separate volume on physics; what matters here is the geometric core, finite and rational at every stage.

Next comes the last chapter of Part XII. Chapter 12.6 assembles the synthesis and draws the *honest map of boundaries*: what geometry-in-ToS realizes over $ℚ$ (the rational/lattice structure, curvature-defect, symmetry groups, the Lie algebra, geodesics) and where its *boundary* lies—the continuum: the smooth manifold, the Lie group over $ℝ$, the continuous curvature tensor, and the Einstein equation, the same continuum price as the one named in Part X.

*The geodesic is a role-extremal, gravity is curvature-defect, tides are the deviation of paths—all finite and rational over $ℚ$. The smooth equations and the dynamics of gravity are a role-limit and the subject of the volume on physics; their map will be closed by 12.6.*

---

[^1]: `DiscreteGeodesic.v` (0 axioms): `d1_triangle` (the triangle inequality—the rule of the geodesic), `plen_ge` (every path $\geq$ the straight distance), `straight_is_shortest` (the straight path is the shortest), `geodesic_insert` (invariance under refinement). The $\ell^1$ metric is chosen because it is rational; in it geodesics are not unique (any monotone “staircase”)—an honest peculiarity, and the Euclidean geodesic is a continuum role-limit.
[^2]: `ProcessGeodesic.v`: `effective_potential`, `isco_radius` (the innermost stable orbit—radius $30$ in Schwarzschild units with $M{=}5$), `kepler_T_sq_over_r3` and `kepler_ratio` ($T^2/r^3$ as a rational ratio), `freefall_velocity_sq` (the free-fall velocity at different shells).
[^3]: `gravity/GeodesicDeviation.v`: `metric_deviation` and `curvature_shortens` (in the model of the file, curvature shortens the model length), `zero_deviation_flat` (on a plane there is no deviation), `equivalence_principle_local` (the local indistinguishability of a fall from inertia), `gravitational_redshift` (the frequency shift from the difference of curvature).
[^4]: `ProcessRegge.v`: `deficit_angle` (the valence defect; `deficit_flat`${}=0$ at valence $6$, positive at a smaller one), `Record ReggeLattice`, `regge_action` ($\sum\delta\cdot$ area), `flat_lattice_zero_action`, and the capstone `regge_is_discrete_gr` (Regge as the discrete geometric analogue of the Einstein–Hilbert action; the dynamics is in the volume on physics). The discrete variational reading of the field equation is `process/ProcessDiscreteEinstein.v`.

---

Part: [[12 Geometry Manifolds Lie Groups|Part XII. Geometry, Manifolds, Lie Groups]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/04 Lie Algebra and Infinitesimal Structure|Chapter 4. The Lie Algebra and Infinitesimal Structure]] · [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/06 Synthesis and Map of Boundaries|Chapter 6. Synthesis and the Map of Boundaries]] →
