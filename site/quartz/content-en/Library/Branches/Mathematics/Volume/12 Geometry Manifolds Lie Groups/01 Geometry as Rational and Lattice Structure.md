---
title: "Chapter 1. Geometry as a Rational and Lattice Structure"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/12 Геометрия, многообразия, группы Ли/01 Геометрия как рациональная и решёточная структура.md"
sourceBlob: 8759041c4acdc998d26dda1cf3d8e0d6ffacb30d
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Opening of Part XII

Part XI reread algebra: a field turned out to be a *role-extension*, a degree a *tier of a role*, and the symmetry of the roots a *concrete encoding* rather than a completed functor. Part XII makes the same move one storey up—in *geometry*: the point, the figure, distance, area, curvature, the manifold, the symmetry group.

Classical differential geometry takes as its primary objects the *smooth manifold*, the continuous *Lie group*, the tangent space, the *curvature tensor*, and the Riemannian metric—all of them as completed things of the continuum. ToS makes the same reverse move as in Part X with set theory and in Part XI with algebra:

- a “point” is a *role-position*—a rational coordinate or a lattice point, given by finite data, and *not* a point of a preexisting continuum;
- a “figure” (a conic, a sphere, a polygon) is *the role of a set of rational points under a defining rule*, enumerable as finite data, not a ready continuous totality;
- “area” and “curvature” are *role-measures*—rational (Pick’s formula, the shoelace formula) or the *angular defect* (Regge), not the limit of Riemann sums and not a continuous tensor;
- a “manifold” is a *process*—a refining triangulation whose smooth limit is a role-limit (like $ℝ=$ the Cauchy process in Part IV and $\overline{ℚ}=$ the tower in Part XI), not a completed object;
- completed continuum objects—the smooth manifold, the Lie group over $ℝ$, the analytic exponential, the continuous curvature tensor—are either *built concretely over $ℚ$* (rational rotations, the Lie algebra, the Cayley map) or honestly remain the *boundary of the system* (a role-limit), whose map is given in 12.6.

The central thesis of Part XII. *Within the P4 ontology of ToS* the substantive core of geometry is a *rational, lattice, simplicial structure together with a symmetry group and curvature-as-defect*. Continuity is not primary: the smooth manifold is a process of refinement, curvature is an angular defect, the exponential is the rational Cayley map. The geometric layer of ToS is, moreover, constructive and does without axioms.[^1]

### What This Part Claims—and What It Does Not

A short formula from the first page: ToS does *not* “formalize smooth differential geometry.” ToS realizes its *discrete, rational, simplicial shadow over $ℚ$* together with symmetry groups and curvature-defect—and in doing so goes further than one might expect of a “shadow”:

- rotation groups live over $ℚ$ concretely: the rational circle $SO(2,ℚ)$, rational quaternions with the *double cover* $SU(2)\to SO(3)$, and the *crystallographic restriction*—only the orders $1,2,3,4,6$ are admissible (Chapter 12.3);[^2]
- infinitesimal symmetry receives a *genuine Lie algebra over $ℚ$*: $so(3)$ as the cross product, the structure constants $[e_i,e_j]=\varepsilon_{ijk}e_k$, and the Jacobi identity (Chapter 12.4);[^3]
- curvature receives an *Element side*: the angular defect, and for all five Platonic solids the sum of the defects equals $2\chi$ (rationally, in units of $\pi$); and the manifold turns out to be a *process*—the circle is the limit of inscribed rational polygons (Chapter 12.2);[^4]
- the exponential $\exp\colon\mathfrak{g}\to G$ is replaced by the rational *Cayley map* (for $SO(2)$ and for $SO(3)$), and the geodesic by the *shortest discrete path* (Chapters 12.4–12.5).[^5]

What ToS does *not* do: it does not reify the smooth manifold as a completed continuum, nor the Lie group over $ℝ$ with the analytic exponential, nor the continuous curvature tensor and the connection as ready objects. This is the *boundary of the system*—but, as in Part XI, a boundary of the same kind as the one named in Part X: the *continuum* (embedding into $ℝ$/$ℂ$, the role-limit of a Cauchy process). It is not a “hole” in the construction but the honest edge of the rational optics, and its place is at the end of the part, in the map of boundaries (12.6), not on every page.

*Part XII is the geometric tier of the same optics: a point is a rational coordinate, a figure a set of rational points under a rule, curvature a defect, a manifold a process. The substantive core of geometry-in-ToS is a rational and lattice structure, not a completed continuum.*

## Point and Figure: Geometry from Rational Coordinates

The basis of geometry-in-ToS is the *rational coordinate*. A point of the plane is a pair $(a,b)\inℚ^2$: finite data, not a mysterious position in a continuum. A figure—a conic, a sphere, a polygon—is not a preexisting continuous set but a *role*: “the points satisfying the defining rule.” Here the generating order of ToS is at work: *Rule* (the equation of the figure) $\to$ *Role* (the locus as a set-under-a-rule) $\to$ *Elements* (actual rational coordinates, enumerated one by one).

The decisive fact: there are *enough* rational points, and they are *generated by a rule*. The unit circle $x^2+y^2=1$ carries infinitely many rational points—exactly the Pythagorean triples. In the mathematical reading, Barning’s ternary tree enumerates all primitive triples from the root $(3,4,5)$; formally checked are the generating steps (the Barning matrices preserve the Pythagorean property), the root, the first descendants, the growth of the hypotenuse, and the impossibility of an isosceles primitive triple. Thus the locus of rational points of the circle is a *rule-generated family of finite data*, not a continuum given in advance.[^6] The same device rises in dimension: *stereographic projection* takes a rational point of the plane to a rational point of the sphere $x^2+y^2+z^2=1$, giving a large parametrized family (in the classical reading it covers all rational points of the sphere except the pole). Formally the forward direction is used: every rational pair gives a point of the sphere.[^7]

Behind both examples stands one classical mechanism—*Diophantus’s chord method*: if through a known rational point of a conic one draws a line with rational slope, the second intersection is again rational. The rational slope is the *rule* that enumerates the *elements* of the locus.[^8] The geometric figure, then, does not precede its points as an object; it is *constituted* by the rule and realized by finite rational coordinates at every stage of the enumeration.

*A point is a rational coordinate (finite data); a figure is the role of a set of rational points under a defining rule, enumerable (the Pythagorean tree, stereography, Diophantus’s chord), not a continuum given in advance.*

## The Lattice and Integer Measure: Pick’s Area

Narrowing the coordinates to integers, we obtain the *lattice* $ℤ^2$—the purest case of finitely actual geometry. Here even *measure* ceases to be a limit. Pick’s classical *formula*

$$
A \;=\; I + \tfrac{B}{2} - 1,
$$

($I$ is the number of interior lattice points, $B$ the number of boundary lattice points) sets the meaning of this layer: area *is counted from finite data* (two integers), not by exhausting infinitely small rectangles. Formally checked are the shoelace-via-determinant and the basic/representative cases: the rectangle, the unit and unimodular triangle.[^9]

The same shift is visible in the *shoelace formula*: the area of a polygon with rational vertices is a *rational* number—an alternating sum of products of coordinates, with no root and no limit. Area belongs to the Element side: a finite rational (and on the lattice, integer) quantity. The classical *completed* integral over a continuum body is a role-limit, deferred to the map of boundaries; but the process integral as finite accumulation has already been built in Part V, and rational area is actual and computable right now. The same shoelace formula will return in 12.2, where the area of inscribed rational polygons will define the circle as a monotone bounded *process* whose limit—the measure of the disk—is reached by no finite stage.

*On the lattice, area is controlled finitely and in integers: Pick’s formula is checked in the basic cases, and the shoelace formula gives rational area. Measure is an Element quantity; the completed integral over a continuum body is a role-limit (12.6), whereas the process integral as finite accumulation has already been built in Part V.*

## Where the Rational Reaches Its Edge: $\sqrt{\phantom{x}}$-Obstructions

Rational and lattice geometry has bounds—and its *edges are themselves theorems*. The cleanest example: *no equilateral triangle has all three vertices in $ℤ^2$*. The proof brings two measures of area together. On the one hand, the area of a lattice triangle is rational (the shoelace formula). On the other, the area of an equilateral triangle with side $s$ equals $\tfrac{\sqrt3}{4}s^2$, and $s^2$ for a lattice side is an integer. The equality of a rational number and $\tfrac{\sqrt3}{4}\cdot(\text{integer})$ would force $\sqrt3$ to be rational—which it is not. Algebraically this is Lagrange’s identity, forcing $3$ to be the square of a rational number.[^10]

The boundary goes further. In the confirmed layer: the square is realized on $ℤ^2$; the equilateral triangle and the hexagon are blocked by $\sqrt3$, and the regular pentagon by $\sqrt5$ (it would require the golden ratio $\varphi$ to be rational). The full formula “only the square” also relies on the crystallographic restriction (the trace argument, Chapter 12.3).[^11] This is precisely the *geometric face* of the structure of degrees and irrationalities of Part XI: “no equilateral triangle on $ℤ^2$” is $\sqrt3\notinℚ$, “no regular pentagon” is $\sqrt5\notinℚ$, and the exclusion of a *fivefold symmetry axis* (the crystallographic restriction of Chapter 12.3) is the same $\sqrt5$ barrier that keeps the pentagon out of the lattice. Rational geometry and the algebraic tier are one structure seen twice.

At the same time, $60^\circ$ geometry is *not lost*—it simply lives on a *different* lattice. The equilateral triangle is impossible on the square lattice $ℤ^2$ but natural on the triangular (hexagonal) lattice, and its rational triples are the *Eisenstein triples*, satisfying $a^2-ab+b^2=c^2$: the exact $60^\circ$ analogue of the Pythagorean triples.[^12] The choice of a lattice is the choice of a *rule*, and it decides which symmetries are actual. Beyond all these edges lies the irrational—a role-limit—and the full continuum is the boundary of the system, to which the part will return in 12.6.

*The edges of rational geometry are theorems: no equilateral triangle on $ℤ^2$ ($\sqrt3$), no regular pentagon ($\sqrt5$, which also rules out the fivefold axis); but $60^\circ$ is rational on the hexagonal lattice (Eisenstein). The lattice is a rule; the irrational beyond its edge is a role-limit.*

## Where the Part Leads

Having laid the rational and lattice foundation, Part XII unfolds it tier by tier.

- **12.2—curvature as angular defect; manifold as process** (the flagship): curvature ceases to be a tensor and becomes an *angular defect* (Regge), and the manifold a *process* of refining triangulation; the circle is the limit of inscribed rational polygons, one that *has no last stage*.
- **12.3—rotation groups over $ℚ$**: $SO(2,ℚ)$, rational quaternions and the double cover $SU(2)\to SO(3)$, finite subgroups and the crystallographic restriction (orders $1,2,3,4,6$).
- **12.4—the Lie algebra and infinitesimal structure**: $so(3)$ over $ℚ$ with the Jacobi identity; the exponential replaced by the rational Cayley map.
- **12.5—geodesics discretely**: the geodesic as the shortest discrete path and as a role-extremal; discrete curvature as gravity (Regge).
- **12.6—synthesis and the map of boundaries**: where geometry-in-ToS runs up against the *continuum* (the smooth manifold, the Lie group over $ℝ$, the analytic exponential, the continuous curvature tensor)—the same price as the one named in Part X.

The map of boundaries stands at the *end* of the part for a reason: the volume describes a *system*, and the honest edge of a system is its property, not a reservation attached to every step.

## E/R/R Analysis

Let us assemble the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the defining equation of the figure ($x^2+y^2=1$, the incidence of lattice points); Diophantus’s chord rule and the stereographic parametrization; Pick’s formula $I+B/2-1$ and the shoelace formula as the rule of area; the squared distance as a rational form |
| *Roles* (L4) | point ${}={}$ role-position (rational coordinate / lattice point); figure ${}={}$ the role of a set of rational points under a rule; area ${}={}$ role-measure (rational/integer); geometry ${}={}$ the role of a rational/lattice structure (preview: manifold ${}={}$ process, curvature ${}={}$ defect) |
| *Elements* (L1${}+{}$P4) | at each stage, finite data over $ℚ$: pairs $(a,b)\inℚ^2$, lattice points of $ℤ^2$, lists of vertices, triples $(a,b,c)$ (Pythagoras/Eisenstein), the numbers $I,B$; the smooth continuum locus and the curvature tensor as an object are *not* Elements |

**Well-formedness.** The figure is well-formed as a rational locus: the points are closed under the rule (the parametrization again gives a rational point); area is well-formed as a rational/integer quantity (Pick/shoelace); the lattice is well-formed as a rule of incidence. Each component falls into exactly one E/R/R category.

**What it yields.** The rational geometry of conics/spheres: enumerable loci, 0 axioms. Lattice measure: Pick’s area, in integers. The edges of the rational structure are theorems ($\sqrt3$-, $\sqrt5$-obstructions), not a “shortage of tools.”

**Diagnosis.** The root error that the chapter removes is the reification of *the geometric figure and its measure as a completed continuum*. ToS returns them to their category: a figure is the role of a set of rational points under a rule, area is a rational measure; the irrational and the continuum are role-limits.

**Honest boundaries.** The continuum locus as a ready uncountable set, the Riemann integral as a limit, the smooth curve/surface are not built here (these are the role-limits of Part X). The full map is in 12.6.

*A point is a rational coordinate; a figure is the role of a locus under a rule; area is a rational/integer measure; the lattice is a rule of incidence. The substantive core is a rational structure, not a completed continuum.*

## Summary and Transition

The chapter has laid the foundation of Part XII: geometry in ToS is a rational and lattice structure. A point is a rational coordinate, a figure is the role of a set of rational points under a defining rule (the Pythagorean tree, stereography, Diophantus’s chord), and measure is a finite quantity (Pick’s area on the lattice, the shoelace formula for rational vertices), not a limit of sums. The edges of this structure are themselves theorems: on the square lattice there is neither an equilateral triangle ($\sqrt3$) nor a regular pentagon ($\sqrt5$), but the angle $60^\circ$ is rational on the hexagonal lattice (Eisenstein). The geometric edge coincides with the algebraic tier of Part XI—this is one structure seen twice.

Next, Part XII climbs tier by tier. Chapter 12.2 turns curvature into an angular defect and the manifold into a process of refining triangulation (the flagship of the part). Chapter 12.3 builds rotation groups over $ℚ$—quaternions and the double cover $SU(2)\to SO(3)$, the crystallographic restriction. Chapter 12.4 gives the Lie algebra $so(3)$ over $ℚ$ with the Jacobi identity and the rational Cayley map in place of the exponential. Chapter 12.5 treats geodesics discretely and curvature as gravity. Chapter 12.6 is the synthesis and the honest map of boundaries, where geometry-in-ToS runs up against the continuum—the same price that was already named in Part X.

*Geometry is a rational and lattice structure, not a continuum given in advance: a point is a coordinate, a figure a locus under a rule, and measure is finite. Such is the frame in which Part XII rereads geometry—not as a smooth object but as a rational structure, a symmetry group, and curvature-defect over finitely actual $ℚ$.*

---

[^1]: The key theorems of the geometric layer—the Jacobi identity of the Lie algebra $so(3)$ (`LieAlgebraSO3.v`), the double cover $SU(2)\to SO(3)$ (`QuaternionRotation.v`), the orthogonality of the Cayley transform (`CayleySO3.v`), the absence of a maximal stage in the manifold process (`ManifoldAsLimit.v`), and the length estimate for a discrete path (`DiscreteGeodesic.v`)—have been checked with `Print Assumptions` as “Closed under the global context” (0 axioms).
[^2]: `QuaternionRotation.v`: `double_cover` ($q$ and $-q$ define the same rotation); the crystallographic restriction and the exclusion of the fivefold axis over the lattice are in `CrystallographicRestriction.v`.
[^3]: `LieAlgebraSO3.v`: `jacobi`, `bracket_e1_e2`, and bilinearity—a full Lie algebra over $ℚ$.
[^4]: `DiscreteGaussBonnet.v`: $\sum\delta/\pi=2\chi$ for the Platonic solids. `ManifoldAsLimit.v`: `no_maximal_stage`—the process has no last stage.
[^5]: `CayleySO3.v`: $N^{\mathsf T}N=(1+\lvert v\rvert^2)^2 I$. `DiscreteGeodesic.v`: `plen_ge`—every path is at least as long as the straight-line distance.
[^6]: `PythagoreanTree.v`: the three Barning matrices preserving the Pythagorean property, the root $(3,4,5)$, the first descendants, the growth of the hypotenuse, `no_isosceles_pyth` ($a\neq b$). The full *coverage* by the tree is a mathematical reading.
[^7]: `RationalSphere.v`: `stereographic_on_sphere` (the image lies on the sphere—a Pythagorean quadruple), concrete points, and `no_integer_diagonal_sphere` (there is no point with $x=y=z$).
[^8]: `ConicDuality.v`: `diophantus_circle`, `param_on_hyperbola`—the rational parametrization of conics.
[^9]: `PickTheorem.v`: `tarea_det` (area via the determinant ${}={}$ the shoelace formula), `pick_rectangle`, `unimodular_triangle_doubled_one`, translation invariance. The full inductive Pick’s theorem for an arbitrary polygon is the next layer.
[^10]: `LatticeEquilateral.v`: `equilateral_forces_3sq` ($(pt-rq)^2=3(pr+qt)^2$) and `no_lattice_equilateral` (integer edges do not form an equilateral triangle): $3$ would turn out to be a square, which is impossible (the irrationality of $\sqrt3$). Machine-checked.
[^11]: `LatticePolygons.v`: `square_on_lattice`, `no_lattice_pentagon`, `phi_sq_no_rational` ($\varphi^2=d^2/s^2$ is irrational); the equilateral triangle and the hexagon go through `no_lattice_equilateral`.
[^12]: `EisensteinTriples.v`: `enorm`${}=a^2-ab+b^2$, `eisenstein_triples`, `eisenstein_norm_mult`—integer sides with an angle of $60^\circ$ (the $60^\circ$ analogue of the Pythagorean triples).

---

Part: [[12 Geometry Manifolds Lie Groups|Part XII. Geometry, Manifolds, Lie Groups]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/06 Synthesis and Map of Boundaries|Chapter 6. Synthesis and the Map of Boundaries—Part XI]] · [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/02 Curvature as Angular Defect Manifold as Process|Chapter 2. Curvature as Angular Defect; Manifold as Process]] →
