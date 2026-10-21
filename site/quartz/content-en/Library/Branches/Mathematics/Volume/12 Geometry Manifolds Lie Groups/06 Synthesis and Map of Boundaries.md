---
title: "Chapter 6. Synthesis and the Map of Boundaries"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/12 Геометрия, многообразия, группы Ли/06 Синтез и карта границ.md"
sourceBlob: 2c0da0335ae577bb6c7acf324c134a5c7f69211f
translated: 2026-10-20
status: draft
---

## What the Part Has Assembled

Part XII has reread geometry through the same optics through which Part X reread set theory and Part XI algebra: it has changed the category of the primary objects and held to the finitely actual. Let us gather what has been covered.

- **12.1—geometry as a rational/lattice structure.** A point is a rational coordinate, a figure a locus under a rule (the Pythagorean tree, stereography, Diophantus’s chord), measure a finite quantity (Pick’s area, the shoelace formula). The edges are $\sqrt{}$-obstructions.
- **12.2—curvature as angular defect; manifold as process.** Curvature is a local defect ($\sum\delta/\pi=2\chi$), the manifold a refining triangulation; the circle is a monotone process of inscribed polygons without a last stage.
- **12.3—rotation groups over $ℚ$.** $\SO(2,ℚ)$ (the multiplicative norm), quaternions and the double cover $\SU(2)\to\SO(3)$, the crystallographic restriction ($1,2,3,4,6$).
- **12.4—the Lie algebra.** $\so(3)\cong\su(2)$ over $ℚ$ as $(ℚ^3,\times)$: the structure constants, the Jacobi identity; the exponential replaced by the rational Cayley map.
- **12.5—geodesics and gravity.** The geodesic is a role-extremal (the shortest discrete path / an orbit); curvature-defect expresses gravity (a geometric reading; the Regge action).

The unified formula of the part. *Within the P4 ontology of ToS* the substantive core of geometry is *a rational and lattice structure, discrete curvature-defect, symmetry groups and a Lie algebra over $ℚ$, and the manifold is a process* (a refining triangulation). All of this is finite rational data at every stage, and the geometric layer of ToS (`src/geometry/`) has been checked as 0-axiom.[^1]

*Geometry-in-ToS is a rational/lattice structure, curvature-defect, symmetry groups, and a Lie algebra over $ℚ$; the manifold is a process. Finitely actual and without axioms.*

## The Map of Boundaries of Part XII

An honest boundary describes *the system itself*: what it encompasses and where it runs up against its edge. For Part XII there are two tiers.

| **Layer** | **Content** | **Price** |
|---|---|---|
| The system of ToS geometry *covers* (0 axioms) | rational/lattice geometry (incl. the shoelace formula and the basic cases of Pick); symmetry groups over $ℚ$—$\SO(2,ℚ)$, quaternions ${}+{}$ the double cover $\SU(2)\to\SO(3)$, the crystallographic restriction ($1,2,3,4,6$), finite subgroups; the Lie algebra $\so(3)\cong\su(2)$; curvature ${}={}$ angular defect (Descartes/Gauss–Bonnet, Forman, Regge); manifold ${}={}$ process (refinement / the circle as a limit / the projective limit); $\exp$ replaced by Cayley (2D and 3D); geodesics discretely (the shortest path; ISCO/Kepler orbits) | none |
| The *boundary* of the system ${}={}$ the continuum (role-limit) | the smooth manifold as a completed continuum; the Lie algebra over $ℝ$ and the analytic exponential; the continuous curvature tensor, the connection, and the Einstein equation; the continuous Gauss–Bonnet; the smooth Riemannian metric | continuum |

The upper tier is what the system *is*: finite rational geometry, 0 axioms. The lower is its *edge*: the smooth continuum. The main boundary of the lower tier is precisely the continuum; and the separate unfinished places of the upper layer (Pick’s theorem in full for arbitrary polygons, the full classification of regular lattice polygons, the general parametrization of the rational sphere) are a *work backlog* over $ℚ$, not a new kind of ontological exclusion.

*The map of boundaries of Part XII: the system covers rational geometry, curvature-defect, symmetry groups, the Lie algebra, and the process-manifold (0 axioms); the main boundary is the continuum as a role-limit, and separate unfinished results are a work backlog, not an exclusion.*

## The Continuum Is the Price of Part X, Not a New Exclusion

The key point about the lower tier: it is *not a new* P4 exclusion but an *already named* price. The smooth manifold, the Lie algebra over $ℝ$, the analytic exponential, the continuous curvature tensor—all of them run up against one and the same thing: the *continuum*. And ToS has already analyzed the continuum in Part IV ($ℝ$ is a Cauchy process) and priced it in Part X (uncountability, the price of choice). Geometry adds no *new* barrier here; it inherits *the same* price.

Moreover, on closer inspection most of the “wall” *resolves*:

- the smooth manifold is not a wall but a *process* (a refining triangulation, 12.2): the continuum object becomes a never-completing tower of approximations, like $\overline{ℚ}$ in Part XI;
- the exponential $\exp\colon\g\to G$ is not a wall but the *rational replacement* by Cayley (12.4), which lands exactly on rational rotations;
- continuous curvature is not a wall but a *discrete defect* (12.2, 12.5), whose sum equals an integer topological invariant.

What remains is a narrow honest residue—the *smooth continuum limit* proper (the unique Euclidean geodesic, the continuous tensor, the analytic $\exp$, rotations by irrational angles). It is real, but it is *the same* continuum as in Part X, and Part XII introduces not a single *new* P4 exclusion—unlike, say, the Axiom of Choice in its completed-object form, which Part X directly rejects.

*The boundary of Part XII is the continuum, the same price as the one named in Parts IV and X, not a new exclusion. Much resolves into a process (the manifold), a rational replacement (Cayley), and a defect (curvature); only the smooth continuum limit remains.*

## Unity across the Book

Part XII is not a separate island—it joins what has already been covered at three points.

*One barrier, seen three times.* $\sqrt3$ and $\sqrt5$ surfaced in Part XII more than once: $\sqrt3$ rules out the equilateral triangle on $ℤ^2$ (12.1) and the rotation by $60^\circ$ as a rational point (12.3); $\sqrt5$ rules out the regular pentagon (12.1) and the fifth axis of symmetry (12.3). And in Part XI this is *the same* irreducible quadratic tier: $x^2+x-1=0$ with no rational root. Lattice geometry, symmetry, and the algebraic tier are one structure seen from three angles.

*One move, “object ${}\to{}$ process.”* A real number turned out to be a Cauchy process (Part IV), the algebraic closure an ascending tower (Part XI), and the manifold a refining triangulation (12.2). Each time, what the classical theory takes as a completed continuum object, ToS reads as a never-completing process. This is *one* move on three storeys of the book.

*One identity, “defect ${}\to{}$ curvature ${}\to{}$ gravity.”* The angular defect (12.2) is curvature, and curvature in the geometric reading of general relativity expresses gravity (12.5); the sum of the defects is topology (Gauss–Bonnet). Geometry, topology, and gravity meet in one finite rational invariant.

*Part XII is one with the book: the $\sqrt3/\sqrt5$ barrier (lattice/symmetry/algebra) is one; the move “object ${}\to{}$ process” ($ℝ$, $\overline{ℚ}$, the manifold) is one; the identity “defect ${}\to{}$ curvature ${}\to{}$ the geometric reading of gravity” is one.*

## E/R/R Analysis of the Part

Let us assemble the whole of Part XII in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the defining equations of figures and Pick’s formula; the defect $2\pi-\sum\alpha$ and Gauss–Bonnet $\sum\delta=2\pi\chi$; the multiplicative norm (two/four squares) and the group axioms; the bracket $[e_i,e_j]=\varepsilon_{ijk}e_k$ with Jacobi; Cayley $(I-K)(I+K)^{-1}$; the extremal of a path (the triangle inequality); the Regge action |
| *Roles* (L4) | figure ${}={}$ locus under a rule; curvature ${}={}$ role-measure (defect); manifold ${}={}$ the role-limit of a refining process; rotation group ${}={}$ role-symmetry; Lie algebra ${}={}$ role-infinitesimal; geodesic ${}={}$ role-extremal; gravity ${}={}$ the role of curvature-defect |
| *Elements* (L1${}+{}$P4) | finite data over $ℚ$: coordinates, lattice points, defects in units of $\pi$, rational points/quaternions/rotation matrices, structure constants, Cayley numerators, discrete paths; the smooth manifold, the continuous curvature tensor, and the analytic $\exp$ over $ℝ$ are *not* Elements |

**Diagnosis of the part.** The root error that Part XII removes is the reification of *the smooth manifold, the continuous Lie group, and the curvature tensor as completed continuum objects*. ToS returns them to their category: geometry is a rational structure, curvature a defect, symmetry a concrete group, the Lie algebra an infinitesimal rule, the manifold a process; the smooth continuum is a role-limit.

*The whole of Part XII is one optics: rules (equations, defect, norm, bracket, Cayley, extremal), roles (locus, measure, symmetry, infinitesimal, limit), and Elements (finite rational data); the smooth continuum is a role-limit, not an Element.*

## Summary of Part XII

Part XII has completed the geometric tier of the same program. Geometry in ToS is not a smooth body given in advance but a *rational and lattice structure* with discrete curvature-defect, symmetry groups over $ℚ$, and the Lie algebra as an infinitesimal rule; the manifold is a *process* of refining triangulation; the geodesic is a role-extremal; gravity is curvature-defect. All of this is finitely actual and does without axioms, and the only boundary is the *continuum*: the smooth limit that ToS has already named and priced in Parts IV and X, not a new P4 exclusion.

Thus geometry takes its place alongside set theory (Part X) and algebra (Part XI): the *category* of the primary objects changes—from the completed continuum to the finitely actual rule, role, and Element—and behind the change of category what opens up is not poverty but *precision*: one sees what is rational and lattice-based, what is symmetric and infinitesimal, what is a process, and what is the honest price of the continuum.

*Geometry-in-ToS is a rational/lattice structure, curvature-defect, symmetry groups and a Lie algebra over $ℚ$, the manifold-as-process; finitely actual, without axioms. The boundary is the continuum, the price of Parts IV and X, not a new exclusion. Having changed its category, geometry has become not poorer but precise.*

---

[^1]: The geometric layer of ToS: `LieAlgebraSO3.v` (`jacobi`), `QuaternionRotation.v` (`double_cover`), `CayleySO3.v` (`cay_orthogonal_scaled`), `RationalSO3.v`, `DiscreteGaussBonnet.v` (`total_defect_pi`), `ManifoldAsLimit.v` (`no_maximal_stage`, `manifold_is_a_process`), `DiscreteGeodesic.v` (`plen_ge`)—“Closed under the global context” (0 axioms) by `Print Assumptions`. They rest on the existing corpus: `RationalRotationGroup`, `RationalQuaternions`, `SU2Group`, `CrystallographicRestriction`, `PickTheorem`, `ProcessManifold`, `SimplicialHomology`, `ProcessRegge`, `ProcessGeodesic`, `GeodesicDeviation` (their status is given separately by their headers/`Print Assumptions`).

---

Part: [[12 Geometry Manifolds Lie Groups|Part XII. Geometry, Manifolds, Lie Groups]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/05 Geodesics and Gravity Discretely|Chapter 5. Geodesics and Gravity, Discretely]] · [[Library/Branches/Mathematics/Volume/13 Zeta Function and Number Theory/01 Primes in Operational Ontology|Chapter 1. Prime Numbers in the Operational Ontology—Part XIII]] →
