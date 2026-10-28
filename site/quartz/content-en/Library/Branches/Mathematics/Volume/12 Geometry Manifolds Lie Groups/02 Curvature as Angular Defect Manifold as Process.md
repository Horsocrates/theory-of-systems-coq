---
title: "Chapter 2. Curvature as Angular Defect; Manifold as Process"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/12 Геометрия, многообразия, группы Ли/02 Кривизна как угловой дефект; многообразие как процесс.md"
sourceBlob: 3c2a2bb75cfc3d35d4ad6a5c513318460f0c4503
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 12.1 laid the foundation: geometry in ToS is a rational and lattice structure, a point is a coordinate, a figure a locus under a rule, measure a finite quantity. Two concepts remain that the classical theory holds most firmly as completed continuum objects: *curvature* (a tensor on a smooth manifold) and the *manifold* itself. This chapter is the flagship of the part: it rethinks both.

The move is the same one that runs through the whole volume. *Within the P4 ontology of ToS*:

- *curvature* is presented first of all as an *angular DEFECT*—a local, discrete, rational (in units of $\pi$) deviation from flatness (the Regge calculus); the continuous curvature tensor is its smooth role-limit;
- the *manifold* is not a continuum given in advance but a *PROCESS*—a refining triangulation whose smooth limit is a role-limit.

The second is a direct geometric analogue of two moves already familiar. In Part IV a real number turned out to be a Cauchy *process* $ℕ\toℚ$, not a point of a ready continuum. In Part XI the algebraic closure $\overline{ℚ}$ turned out to be a *tower* of finite extensions without a maximal rung, not a completed wall. Here the *manifold* turns out to be a *refining triangulation*: what the classical theory takes as a completed smooth body, ToS reads as a never-completing process of approximation that has no last stage.

*Curvature is an angular defect, not a tensor; a manifold is a process of refinement, not a ready continuum. This is the geometric analogue of $ℝ=$ Cauchy process and $\overline{ℚ}=$ tower: the completed object of the classical theory becomes a process of ToS.*

## Curvature as Angular Defect

Take a vertex of a polyhedron at which $m$ faces with interior angles $\alpha$ meet. If the neighborhood were flat, the angles would add up to a full turn, $2\pi$. The *angular defect*

$$
\delta \;=\; 2\pi - \sum_{\text{faces at the vertex}} \alpha
$$

measures how *non-flat* the vertex is—and this is precisely curvature concentrated at a point (Regge’s idea). In this layer curvature is presented not as a smeared-out continuous field but as *localized* at the vertices and *discrete*; the continuous tensor is its smooth role-limit.

The observation decisive for ToS: *in units of $\pi$ the defect is rational*. The interior angles of regular faces are rational multiples of $\pi$ (the triangle $\pi/3$, the square $\pi/2$, the pentagon $3\pi/5$), and therefore

$$
\frac{\delta}{\pi} \;=\; 2 - m\cdot\frac{\alpha}{\pi} \;\in\; ℚ .
$$

The magnitude of the angle itself, through $\arccos$, is a role-limit; but *the defect divided by* $\pi$ is a finite rational number, the Element side of curvature. For the tetrahedron, $3$ triangles meet at each of the $4$ vertices, and $\delta/\pi = 2 - 3\cdot\tfrac13 = 1$; for the cube, $2 - 3\cdot\tfrac12 = \tfrac12$; and so on for all five regular solids.[^1]

Curvature-defect also has a purely *combinatorial* face—discrete Ricci curvature on a graph. The Forman curvature of an edge $e=(u,v)$ is assembled from the degrees of its endpoints and their common neighbors; on a chain it is zero (flat), on a triangle and on a complete graph it is positive.[^2] In both cases curvature is a *rule* over finite data (angles, degrees), not a continuous field.

*Curvature is localized and discrete: the angular defect $\delta=2\pi-\sum\alpha$ (Regge) or Forman’s combinatorial Ricci curvature. In units of $\pi$ the defect is rational—the Element side; the angle itself, through $\arccos$, is a role-limit.*

## Gauss–Bonnet: Defect Equals Topology

Local defects add up to a *global invariant*. Descartes’s theorem (the discrete Gauss–Bonnet) states: the sum of the angular defects over all vertices of a closed polyhedron equals $4\pi$—that is, $2\pi\cdot\chi$ with the Euler characteristic $\chi=V-E+F=2$ for spherical topology. In units of $\pi$ this is

$$
\sum_v \frac{\delta_v}{\pi} \;=\; 2\chi .
$$

For all five Platonic solids the left-hand side equals $4$, and $\chi=2$—and the equality holds identically.[^3] What is essential is this: *a rational sum of defects equals an integer topological invariant*—and this equality does not depend on the (role-limit) value of $\pi$ itself. Curvature on the Element side (rational, in units of $\pi$) *is* topology (the integer $2\chi$).[^4]

The same invariant also has a smooth-simplicial face: a chain complex with boundary $\partial$, the Betti numbers, the Euler characteristic obtained from them, and the Gauss–Bonnet form $\sum\delta=4\pi\chi$.[^5] The two records meet in topology: the *global sum* of discrete defects and the smooth *integral* of the total curvature have one and the same topological invariant $2\chi$. A local discrete defect is not equal to the smooth tensor field at a point—what coincides is precisely the global total curvature.

*The sum of the angular defects ${}={}2\pi\chi$ (Descartes/Gauss–Bonnet): rational (in units of $\pi$) curvature equals the integer topological invariant $2\chi$, independently of the value of $\pi$. The global invariants of discrete and smooth curvature coincide (both ${}={}2\chi$).*

## Manifold as Process

Now to the heart of the chapter. What is the *manifold* itself? The classical answer: a smooth body, given in its entirety, with a continuous map of curvature. ToS answers otherwise: a manifold is a *process* of refining triangulation—a sequence of piecewise-flat approximations for which the smooth body is only a *role-limit*.

The most transparent case is the circle. It need not be taken as a ready continuum; it can be *generated* by inscribed rational polygons. The inscribed square with vertices $(\pm1,0),(0,\pm1)$ has area $2$; the rational $12$-gon with vertices $(\pm1,0),(0,\pm1),(\pm\tfrac35,\pm\tfrac45),(\pm\tfrac45,\pm\tfrac35)$ has area $74/25=2{,}96$. The area *strictly increases* under refinement and stays bounded above by the area of the circumscribed square $[-1,1]^2$, equal to $4$. This is a *monotone bounded rational process* $ℕ\toℚ$, and its limit—the area of the unit disk, $\pi$—*is reached by no finite stage*.[^6]

This is what the flagship rethinking consists in. *“The circle” is the name of a process, not of a completed object.* Each stage is finite rational data (a list of vertices, a rational area); the totality is a monotone bounded process with the limit $\pi$, which is not among the stages. This is literally the same move as $ℝ=$ Cauchy process (Part IV) and $\overline{ℚ}=$ ascending tower (Part XI): what the classical theory reifies into a ready continuum, ToS holds as a never-completing process of approximation.

The same image works in higher dimension and abstractly. A *process-manifold* is a sequence of nested triangulations with a refining mesh, along which the *curvature stabilizes* as the refinement proceeds; the flat and spherical manifolds are described as such processes.[^7] And the general form of “the continuum as the limit of stages” is the *projective limit*: a tower with projections and compatible threads over it, Cauchy stage by stage.[^8] The smooth manifold is the role-limit of this tower, not its maximal rung (there is none), exactly as $\overline{ℚ}$ is the limit of the tower of extensions.

*A manifold is a process of refining triangulation, not a ready continuum. The circle is a monotone bounded process of inscribed rational polygons without a last stage; its area $\pi$ is a role-limit. The same move as $ℝ=$ process and $\overline{ℚ}=$ tower.*

## E/R/R Analysis

Let us assemble the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the defect $\delta=2\pi-\sum\alpha$ (Regge’s rule); Gauss–Bonnet $\sum\delta=2\pi\chi$ (Descartes); the rule of refinement (inscribed polygons, nested triangulations); $\partial^2=0$ (the chain complex); Forman curvature as a rule on a graph |
| *Roles* (L4) | curvature ${}={}$ role-measure (angular defect); manifold ${}={}$ the role-limit of a refining process; “smoothness” ${}={}$ a process, not an object; $\chi={}$ topological role-invariant; “circle” ${}={}$ the name of a process |
| *Elements* (L1${}+{}$P4) | at each stage, finite data: the numbers $V,E,F$; defects in units of $\pi$ (rational); lists of polygon vertices and their rational areas; degrees of graph vertices; the smooth manifold and the continuous curvature tensor as objects are *not* Elements |

**Well-formedness.** Curvature is well-formed as a defect: the sum of the defects equals the integer invariant $2\chi$ (Gauss–Bonnet). The process-manifold is well-formed: refinement is monotone, bounded, and stabilizes curvature. Each component falls into exactly one E/R/R category.

**What it yields.** Curvature is a rational defect (in units of $\pi$) equal to the integer $2\chi$. The manifold is a concrete monotone process (the circle from polygons), 0 axioms, plus the abstract process-manifold and projective limit.

**Diagnosis.** The root error that the chapter removes is the reification of *curvature as a continuous tensor* and of *the manifold as a ready smooth body*. ToS returns them to their category: curvature is a defect (a rule-measure), the manifold is a process (a role-limit).

**Honest boundaries.** The smooth manifold as a completed continuum, the continuous curvature tensor and the connection, the Riemannian metric are role-limits (the continuum price of Part X). The full map is in 12.6.

*Curvature is a defect (a rule-measure) equal to topology; a manifold is a process (a role-limit). The Element side is rational defects and finite stages; the smooth tensor and the completed continuum are role-limits.*

## Summary and Transition

The chapter has rethought the two most “continuum-bound” concepts of geometry. *Curvature* has ceased to be a continuous tensor and has become an *angular defect*—local, discrete, rational in units of $\pi$; and its global sum has turned out to equal the integer topological invariant $2\chi$ (Gauss–Bonnet), independently of the value of $\pi$. The *manifold* has ceased to be a ready smooth body and has become a *process* of refining triangulation: the circle is a monotone bounded process of inscribed rational polygons without a last stage, whose area $\pi$ is a role-limit. This is the same move as $ℝ=$ Cauchy process and $\overline{ℚ}=$ tower—now in geometry.

Next, Part XII descends from measure and shape to *symmetry*. Chapter 12.3 builds rotation groups over $ℚ$—the rational circle $SO(2,ℚ)$, quaternions and the double cover $SU(2)\to SO(3)$, finite subgroups, and the crystallographic restriction. Chapter 12.4 gives the infinitesimal side—the Lie algebra $so(3)$ over $ℚ$ and the rational Cayley map in place of the exponential.

*Curvature is a defect, a manifold is a process: what the classical theory takes as a completed smooth body with continuous curvature, ToS reads as a rational defect equal to topology and as a never-completing refinement whose smooth limit is a role-limit, not an object.*

---

[^1]: `DiscreteGaussBonnet.v`: `vertex_defect_pi`${}=2-m\cdot a$ and `total_defect_pi`; `tetra_defect`, `cube_defect`, `octa_defect`, `dodeca_defect`, `icosa_defect`—the sum of the defects of each solid equals $4$ (in units of $\pi$). Machine-checked, 0 axioms.
[^2]: `GraphCurvature.v`: `forman_curvature` $=4-\deg u-\deg v+3 |\text{common neighbors}|$; `chain_flat` (the chain is flat), positive curvature on a triangle and on a complete graph.
[^3]: `DiscreteGaussBonnet.v`: `platonic_euler` ($\chi=2$ for the tetrahedron/cube/octahedron/dodecahedron/icosahedron), `gauss_bonnet_general` (if $\sum\delta/\pi=4$ and $\chi=2$, then $\sum\delta/\pi=2\chi$), and `gauss_bonnet_tetra`.
[^4]: `foundation/EulerCharProtectedInteger.v` (4 Qed, 0 axioms): the Euler characteristic is a *protected integer*, reached by four independent paths ($\chi(S^2)=2$—`sphere_chi_four_ways`; the torus $\chi=0$—`torus_chi_zero`; all Platonic solids $\chi=2$—`all_platonic_chi_2`; the capstone `euler_char_protected_integer`). An observation about the stability of an integer invariant, not a new theorem; machine-checked, 0 axioms.
[^5]: `SimplicialHomology.v`: `triangle_boundary_verified` ($\partial^2=0$), the Betti numbers (`betti_S2/T2/g2`), $\chi$ through the Betti numbers (`euler_from_betti`, `euler_S2`${}=2$), and Gauss–Bonnet $\sum\delta=4\pi\chi$ (`gauss_bonnet_predict`). This is a smooth-topological record of the same invariant; the Element form “$\sum\delta/\pi=2\chi$ for the Platonic solids” is in `DiscreteGaussBonnet.v`.
[^6]: `ManifoldAsLimit.v` (0 axioms): `shoelace` (rational area from the vertices), `square_area`${}=2$, `dodeca_area`${}=74/25$, `refinement_grows_area` (refinement strictly increases the area), `approx` (a strictly increasing bounded process), and `no_maximal_stage` (there is no last stage), the capstone `manifold_is_a_process`.
[^7]: `ProcessManifold.v`: the record `ProcessManifold` (vertices, edges, edge length, the defect at stage $K$), `pm_refining`, `pm_curvature_stable`; the flat and spherical manifolds as processes.
[^8]: `ProjectiveSystem.v`/`ProjectiveLimit.v`: the projective system `ProjSys` with projections, a compatible element as a thread, the stagewise Cauchy property (the metric projective limit).

---

Part: [[12 Geometry Manifolds Lie Groups|Part XII. Geometry, Manifolds, Lie Groups]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/01 Geometry as Rational and Lattice Structure|Chapter 1. Geometry as a Rational and Lattice Structure]] · [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/03 Rotation Groups over Q So2 Quaternions Su2|Chapter 3. Rotation Groups over Q: SO(2), Quaternions, SU(2)]] →
