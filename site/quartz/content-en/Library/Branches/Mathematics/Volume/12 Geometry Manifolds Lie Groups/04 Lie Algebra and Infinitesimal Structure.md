---
title: "Chapter 4. The Lie Algebra and Infinitesimal Structure"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/12 Геометрия, многообразия, группы Ли/04 Алгебра Ли и инфинитезимальная структура.md"
sourceBlob: 2d78d58aec44f23617738ceb0a092b6a717fb939
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 12.3 built rotation groups over $ℚ$ and their double cover $\SU(2)\to\SO(3)$. Every rotation group has an *infinitesimal* shadow—the Lie algebra: the tangent structure at the identity, encoding how symmetries *begin* to move. The classical theory obtains it through the *derivative* of a one-parameter group—a limit that needs $ℝ$. ToS obtains it otherwise.

*Within the P4 ontology of ToS*:

- the “Lie algebra” is an *infinitesimal RULE*—the bracket $[X,Y]$, given *directly* as a finite operation over $ℚ$, not as the limit of a derivative;
- for rotations this is $\so(3)\cong\su(2)$, realized as $(ℚ^3,\ \text{cross product})$ with the *structure constants* $[e_i,e_j]=\varepsilon_{ijk}e_k$;
- the “exponential” $\exp\colon\g\to G$, which takes the algebra to the group, is a *role-limit* (it needs $\cos/\sin$ or a series); its rational replacement is the *Cayley map*;
- the full smooth analytic exponential and the Lie correspondence over $ℝ$ are a *role-limit* (the continuum price of Part X), whose map is given in 12.6.

The central thesis of the chapter. Infinitesimal symmetry in ToS is a *finite rule* (a bracket over $ℚ$ with the Jacobi identity), not a limit object of analysis. The group is recovered from the algebra by the rational Cayley map; the analytic exponential is a smooth role-limit.

*The Lie algebra is an infinitesimal rule (a bracket over $ℚ$), not the limit of a derivative; $\so(3)\cong\su(2)$ is concrete; the exponential is a role-limit, and its rational replacement is Cayley.*

## The Bracket as an Infinitesimal Rule: $\so(3)${so(3)} over $ℚ${Q}

Classically an element of a Lie algebra is a tangent vector at the identity of the group: the derivative $\tfrac{d}{dt}\big|_{0}R(t)$ of a one-parameter family of rotations. To take the derivative in the classical form is to take a limit, relying on the layer over $ℝ$. ToS makes the reverse move: it gives the algebra *directly* as a finite operation. The algebra $\so(3)$ is simply $ℚ^3$ with the *bracket* equal to the *cross product*:

$$
[a,b] \;=\; a\times b \;=\;
  (a_2 b_3 - a_3 b_2,\; a_3 b_1 - a_1 b_3,\; a_1 b_2 - a_2 b_1).
$$

No limit at all: the bracket is a finite rational rule over triples of coordinates.[^1]

The content of the algebra lies in the *structure constants*. On the basis $e_1,e_2,e_3$ the bracket is closed and cyclic:

$$
[e_1,e_2]=e_3,\quad [e_2,e_3]=e_1,\quad [e_3,e_1]=e_2
$$

(that is, $[e_i,e_j]=\varepsilon_{ijk}e_k$ with the Levi-Civita symbol). This is the *rule* from which the whole rotation group grows; it is integer-valued and is checked by ring arithmetic.[^2]

The bracket satisfies the axioms of a Lie algebra—and all of them are proved over $ℚ$ without axioms of the theory: *antisymmetry* $[a,b]=-[b,a]$ (and $[a,a]=0$); *bilinearity* in both arguments; and, most importantly, the *Jacobi identity*

$$
[a,[b,c]] + [b,[c,a]] + [c,[a,b]] \;=\; 0,
$$

which replaces associativity in the world of brackets. The algebra is *non-abelian*: $[e_1,e_2]=e_3\neq -e_3=[e_2,e_1]$.[^3] Before us is the *full set of axioms* of a Lie algebra for this concrete rational example—the infinitesimal rule of symmetry, entirely on finite rational data.

*$\so(3)$ over $ℚ$ is $(ℚ^3,\times)$: the bracket as a finite rule, the structure constants $[e_i,e_j]=\varepsilon_{ijk}e_k$, antisymmetry, bilinearity, Jacobi, the non-abelian character—without a limit and without axioms.*

## $\so(3)\cong\su(2)${so(3) = su(2)}: The Cover Is Invisible Infinitesimally

The algebra of §12.4.2 has a second name—$\su(2)$. The generators of $\su(2)$ (the anti-Hermitian matrices $T_k=-\tfrac{i}{2}\sigma_k$ on the Pauli basis) obey *the same* structure constants $[T_i,T_j]=\varepsilon_{ijk}T_k$. The cross product on $ℚ^3$ is their common rational realization: one and the same table of brackets $\varepsilon_{ijk}$ is both $\so(3)$ and $\su(2)$.[^4]

This clarifies the double cover of Chapter 12.3 from another side. At the *group* level $\SU(2)\to\SO(3)$ is a $2{:}1$ map ($q$ and $-q$ are one rotation). But at the *infinitesimal* level the cover *disappears*: $\SU(2)$ and $\SO(3)$ have *one and the same* Lie algebra. The cover is a global (topological) phenomenon; the bracket does not see it. The algebra is a local rule common to the group and its cover; what distinguishes them is only the global gluing, to which the bracket is insensitive.

*$\so(3)\cong\su(2)$ is one rational bracket $\varepsilon_{ijk}$. The double cover $\SU(2)\to\SO(3)$ is global (topological) and infinitesimally invisible: the group and its cover have one Lie algebra.*

## The Exponential as a Role-Limit; the Cayley Map

The algebra is an infinitesimal rule; the group is its *integral*. The classical bridge is the *exponential* $\exp\colon\g\to G$: for $\so(2)$ it is $\exp(\theta J)=\cos\theta\cdot I +
\sin\theta\cdot J$—the rotation by the angle $\theta$. But $\cos\theta,\sin\theta$ for rational $\theta$ are almost always irrational (§12.3): the analytic exponential *goes out into the continuum*—it is a *role-limit*, like the Cauchy process in Part IV.

ToS holds the bridge by a *rational* map—*Cayley’s*. In two dimensions this is the already familiar map $t\mapsto\bigl(\tfrac{1-t^2}{1+t^2},\tfrac{2t}{1+t^2}\bigr)$ of §12.3.2, which lands exactly on the rational points of $\SO(2,ℚ)$. In three dimensions, for a skew-symmetric matrix $K=\hat v$ (the image of a vector $v\inℚ^3$, an element of $\so(3)$), the Cayley transform

$$
R \;=\; (I-K)(I+K)^{-1}
$$

gives a *rational* rotation matrix. To stay within ring arithmetic (without inverting matrices), we work with the numerator $N=(1+\norm{v}^2) R$ and prove the *ring identity*

$$
N^{\mathsf T} N \;=\; (1+\norm{v}^2)^2  I,\quad \det N = (1+\norm{v}^2)^3,
$$

whence $R=N/(1+\norm{v}^2)\in\SO(3,ℚ)$: it is orthogonal with determinant $+1$. The normalization is the rational denominator $1+\norm{v}^2>0$; for $v=(1,0,0)$ the result is the rotation by $90^\circ$ about the $x$-axis.[^5] Thus the Lie algebra of §12.4.2 is *joined* to the rotation group of 12.3 by the rational Cayley bridge—without any exponential.[^6]

*The honest boundary.* Cayley is not the whole exponential: it misses the rotations by $\pi$ (the antipodal points, where $\norm{v}^2\to\infty$), and the analytic $\exp$ over $ℝ$ remains a role-limit. The Lie correspondence “algebra ${}\leftrightarrow{}$ group” in full smooth generality is the continuum price, to which the part will return in 12.6.

*The exponential $\exp\colon\g\to G$ needs $\cos/\sin$—a role-limit; the rational replacement is Cayley: in 2D the map of the circle, in 3D $R=(I-K)(I+K)^{-1}$ with the ring identity $N^{\mathsf T}N=(1+\norm{v}^2)^2 I$. The bridge algebra ${}\to{}$ group is rational; the full $\exp$ over $ℝ$ is a role-limit.*

## E/R/R Analysis

Let us assemble the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the bracket $[a,b]=a\times b$ and the structure constants $[e_i,e_j]=\varepsilon_{ijk}e_k$; the axioms of a Lie algebra (antisymmetry, bilinearity, Jacobi); the Cayley transform $R=(I-K)(I+K)^{-1}$ as the rule of transition algebra ${}\to{}$ group |
| *Roles* (L4) | Lie algebra ${}={}$ role-infinitesimal (the tangent rule at the identity); bracket ${}={}$ the rule of infinitesimal symmetry; $\exp$ ${}={}$ role-limit (the bridge to the group); Cayley ${}={}$ its rational replacement; $\so(3)\cong\su(2)$ ${}={}$ the common role of the group and its cover |
| *Elements* (L1${}+{}$P4) | finite data over $ℚ$: vectors $(x,y,z)\inℚ^3$, the integer structure constants $\varepsilon_{ijk}$, the rational Cayley numerator $N$; the analytic $\exp$ and the smooth Lie correspondence over $ℝ$ are *not* Elements |

**Well-formedness.** The algebra is well-formed by the axioms: antisymmetry $[a,b]=-[b,a]$ and the Jacobi identity (which replaces associativity). The transition is well-formed: $N^{\mathsf T}N=(1+\norm{v}^2)^2 I$ and $\det N=(1+\norm{v}^2)^3$ give, after normalization, $R\in\SO(3,ℚ)$.

**What it yields.** $\so(3)\cong\su(2)$ over $ℚ$ is a full Lie algebra (structure constants, Jacobi), 0 axioms, the only one in the library. The Cayley map is a rational bridge algebra ${}\to{}$ group in 2D and 3D, 0 axioms.

**Diagnosis.** The root error is the reification of *the Lie algebra as a limit object of analysis* (the tangent space of a smooth manifold). ToS returns it to its category: the bracket is a finite infinitesimal rule; the exponential is a role-limit.

**Honest boundaries.** The analytic $\exp$ (the series, $\cos/\sin$), the rotations by $\pi$ for Cayley, and the smooth Lie correspondence “algebra ${}\leftrightarrow{}$ group” over $ℝ$ are role-limits (the continuum price of Part X). The full map is in 12.6.

*The Lie algebra is an infinitesimal rule (a bracket over $ℚ$, Jacobi); $\so(3)\cong\su(2)$ is concrete; the bridge to the group is the rational Cayley map. The analytic exponential and the smooth correspondence are role-limits.*

## Summary and Transition

The chapter has given the *infinitesimal* side of symmetry. The Lie algebra $\so(3)\cong\su(2)$ is built over $ℚ$ *directly*, as a finite rule: $ℚ^3$ with the bracket-as-cross-product, the structure constants $[e_i,e_j]=\varepsilon_{ijk}e_k$, antisymmetry, bilinearity, and the Jacobi identity—a full Lie algebra without a limit and without axioms. The double cover $\SU(2)\to\SO(3)$ of 12.3 has turned out here to be *infinitesimally invisible*: the group and its cover have one algebra. And the bridge from the algebra to the group—classically the exponential, which requires $\cos/\sin$ (a role-limit)—ToS has built *rationally*, by the Cayley map: in 2D by the map of the circle, in 3D by $R=(I-K)(I+K)^{-1}$ with the ring identity $N^{\mathsf T}N=(1+\norm{v}^2)^2 I$.

Next, Part XII passes from symmetry to *motion through geometry*. Chapter 12.5 builds *geodesics* discretely—as the shortest rational path and as a role-extremal—and shows discrete curvature as gravity (Regge), joining the geometry of the part with physics.

*Infinitesimal symmetry is a finite rule: the bracket $\so(3)\cong\su(2)$ over $ℚ$ with the Jacobi identity, and the bridge to the group is the rational Cayley map, not the analytic exponential. The cover of Chapter 12.3 is infinitesimally invisible; the smooth Lie correspondence is a role-limit.*

---

[^1]: `LieAlgebraSO3.v` (0 axioms): `Record V3` ($ℚ^3$), `bracket` (the cross product), the generators `e1`,`e2`,`e3`.
[^2]: `LieAlgebraSO3.v`: `bracket_e1_e2`, `bracket_e2_e3`, `bracket_e3_e1`—the structure constants $\varepsilon_{ijk}$.
[^3]: `LieAlgebraSO3.v`: `bracket_antisym`, `bracket_self_zero`, `bracket_add_l`/`bracket_scale_l` (and the right-hand versions), `jacobi` (the Jacobi identity), and `so3_nonabelian`. In the geometric layer of ToS this is the basic Lie algebra with a bracket and Jacobi.
[^4]: `LieAlgebraSO3.v`: the basis brackets `bracket_e1_e2` and so on are the structure constants common to $\so(3)$ and $\su(2)$ (the definition `structure_constant_123`). What is formalized is the rational $\so(3)$ model ($ℚ^3$ with the bracket); the coincidence with $\su(2)$ is a mathematical reading of the same structure constants, not a separate formalization of the Pauli matrices over $ℂ$.
[^5]: `CayleySO3.v` (0 axioms): `cay_num` (the Cayley numerator), `cay_orthogonal_scaled` ($N^{\mathsf T}N=(1+\norm{v}^2)^2 I$—the ring identity), `cay_det_scaled`, `cay_identity` ($v=0\mapsto I$), and the concrete `rot90x`. The two-dimensional map is `cayley_on_circle` (`RationalRotationGroup.v`).
[^6]: The same rational Cayley bridge on $\SO(2,ℚ)$ recurs in cross-links beyond geometry: `foundation/CayleyGeometrySpectralBridge.v` (6 Qed, 0 axioms)—the Cayley spectral point lies on $\SO(2,ℚ)$ and composes there (`spectral_composes_in_SO2Q`, `mass_4_is_rotation`); `CayleyFourierMassBridge.v` (9 Qed) links Cayley $\leftrightarrow$ Fourier $\leftrightarrow$ lattice mass (`cayley_fourier_is_mass`, `lattice_masses_pythagorean`); `ThreeFifthsUnification.v` (5 Qed) brings together the value $3/5$ in the Born/Schrödinger/Cayley readings (`three_fifths_unification`). All are 0 axioms, machine-checked; these are observational cross-bridges (some of them gravitate toward the physics volume), not new theorems.

---

Part: [[12 Geometry Manifolds Lie Groups|Part XII. Geometry, Manifolds, Lie Groups]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/03 Rotation Groups over Q So2 Quaternions Su2|Chapter 3. Rotation Groups over Q: SO(2), Quaternions, SU(2)]] · [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/05 Geodesics and Gravity Discretely|Chapter 5. Geodesics and Gravity, Discretely]] →
