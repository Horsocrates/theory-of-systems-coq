---
title: "Chapter 3. Rotation Groups over Q: SO(2), Quaternions, SU(2)"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/12 Геометрия, многообразия, группы Ли/03 Группы вращений над Q SO(2), кватернионы, SU(2).md"
sourceBlob: 3150c9c268b6dcac4ac5d67483d5c369180fe0e1
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 12.2 rethought measure and shape: curvature became a defect, the manifold a process. Now Part XII descends to *symmetry*—to the groups that preserve geometry. The classical theory takes as its primary objects the continuous *Lie groups* $\SO(2)$, $\SO(3)$, $\SU(2)$—as smooth manifolds with coordinates $\cos\theta,\sin\theta$. ToS makes the same move as in Parts X and XI and in Chapters 12.1–12.2:

- a “rotation” is a *role-symmetry*, and its bearer is a *rational point*: $\SO(2,ℚ)$ is the rational points of the circle; quaternions are rational quadruples; $\SU(2)$ is a record with axioms;
- a “rotation group” is constituted by the *rule of the norm*: $c^2+s^2=1$, $\norm{q}^2=1$, and by the *multiplicativity* of this norm (the two-square and four-square identities), which is what makes composition closed;
- the “double cover” $\SU(2)\to\SO(3)$ is a concrete $2{:}1$ role-map: a unit quaternion and its opposite define *one* rotation;
- an “admissible order of symmetry” is a *role-restriction*: only rotations of orders $1,2,3,4,6$ preserve a lattice—the axis $5$ is ruled out (the crystallographic restriction);
- the continuous Lie group over $ℝ$ (with $\cos/\sin$ and the analytic exponential) is a *role-limit* (the continuum price of Part X), whose map is given in 12.6.

The central thesis of the chapter. *Within the P4 ontology of ToS* a rotation group is not a smooth body but a *rational structure of symmetries*: rational points closed under the multiplicative norm, a concrete double cover, and finite subgroups with an honest restriction on the order. The continuous Lie group is the smooth role-limit of this structure.

*A rotation is a role-symmetry with a rational bearer; a group is closure under the multiplicative norm; the cover is a concrete $2{:}1$ map; an admissible order is a role-restriction. The smooth Lie group is a role-limit.*

## Rotation as a Rational Point: The Group $\SO(2,ℚ)$

A rotation of the plane is given by a pair $(c,s)$ with $c^2+s^2=1$—the cosine and sine of the angle. ToS takes *rational* pairs of this kind: $\SO(2,ℚ)$ is the rational points of the unit circle (Chapter 12.1 has already enumerated them by the Pythagorean tree). The composition of rotations is a rule on pairs

$$
(c_1,s_1)\cdot(c_2,s_2) \;=\; (c_1c_2-s_1s_2,\; c_1s_2+s_1c_2),
$$

and it is *closed*: the product of two rational points of the circle is again on the circle. The reason is the *multiplicativity of the norm*, the two-square identity (Brahmagupta–Fibonacci)

$$
(c_1^2+s_1^2)(c_2^2+s_2^2) = (c_1c_2-s_1s_2)^2 + (c_1s_2+s_1c_2)^2 .
$$

The identity is $(1,0)$; the inverse of $(c,s)$ is the conjugate $(c,-s)$. Thus rational rotations have the group operations—closure, identity, and inverse—without recourse to $ℝ$ (the full `Record Group` for $\SO(2,ℚ)$ is assembled as a separate framework).[^1]

This structure has a subtlety important for ToS. Its points lie on the circle *densely* (the mathematical reading), but the “nice” angles are *not* rational points: neither $60^\circ$ (it needs $\tfrac{\sqrt3}{2}$) nor $45^\circ$ (it needs $\tfrac{\sqrt2}{2}$). The rotation by $60^\circ$ is not a rational point—exactly the same $\sqrt3$ barrier that in 12.1 kept the equilateral triangle off the lattice.[^2] Rational points carry symmetry *not* where the classical theory expects it—and this already foreshadows the restriction on finite orders (§12.3.4).

*$\SO(2,ℚ)$ is the group of rational points of the circle (closure under the multiplicative norm, inverse ${}=$ conjugate). It is dense, but $60^\circ/45^\circ$ are not its points ($\sqrt3,\sqrt2$): the same barrier as in 12.1.*

## Quaternions and the Double Cover $\SU(2)\to\SO(3)$

In three dimensions rotations are encoded by *quaternions*—quadruples $q=(w,x,y,z)\inℚ^4$ with the Hamilton product. ToS keeps them over $ℚ$: they are *finite data*, not points of a smooth group. The norm $\norm{q}^2=w^2+x^2+y^2+z^2$ is *multiplicative*—this is *Euler’s four-square identity*, a direct analogue of the two squares of §12.3.2:

$$
\norm{q_1}^2 \norm{q_2}^2 \;=\; \norm{q_1 q_2}^2 .
$$

Therefore the unit quaternions ($\norm{q}^2=1$) are closed under multiplication—they form $\SU(2)\cong\Spin(3)$, set up in ToS as a *record* with proved group axioms.[^3]

How does a unit quaternion *rotate*? By conjugation. A pure quaternion $v=(0,a,b,c)$ is a vector of $ℚ^3$, and the map $v\mapsto q v \bar q$ takes a vector to a vector of the same length: the multiplicativity of the norm gives $\norm{q v\bar q}^2=\norm{q}^4\norm{v}^2=\norm{v}^2$ for $\norm{q}^2=1$. This is precisely a rotation—an Element proof, without matrices and without $\cos/\sin$.[^4]

And here is the key point: $q$ and $-q$ define *one and the same* rotation, since $(-q) v \overline{(-q)} =
q v \bar q$. This is the *double cover* $\SU(2)\to\SO(3)$—exactly $2{:}1$.[^5] A concrete witness is the unit quaternion $(\tfrac12,\tfrac12,\tfrac12,\tfrac12)$: its cube equals $-1$, and conjugation by it is the rotation by $120^\circ$ about the axis $(1,1,1)$—an element *of order 3* of the group $\SO(3,ℚ)$. On the matrix side this is the cyclic permutation matrix: orthogonal, with determinant $1$ and cube $=I$.[^6]

*Quaternions over $ℚ$: the norm is multiplicative (four squares), and the unit ones form $\SU(2)$; conjugation $q v\bar q$ rotates (an isometry); $q$ and $-q$ give one rotation—the double cover $\SU(2)\to\SO(3)$. $(\tfrac12,\tfrac12,\tfrac12,\tfrac12)$ is a rotation of order 3.*

## Finite Symmetries and the Crystallographic Restriction

The group $\SO(2,ℚ)$ is dense, but almost all of its elements are of *infinite* order: the $3$-$4$-$5$ rotation never returns to the start (its angle is incommensurable with $\pi$).[^7] The question is: what *finite* orders are possible at all for a rotation that preserves a *lattice*? The answer is the famous *crystallographic restriction*: only $1,2,3,4,6$. The general trace (Niven) mechanism excludes all other orders; the exclusion of the axis $5$ is singled out separately as the “golden” obstruction.

The proof rests on the trace. A rotation preserving a lattice has, in an integer basis, an *integer trace*; and in the two-dimensional case the trace of a rotation by the angle $\theta$ equals $2\cos\theta$. Hence $2\cos\theta\inℤ\cap[-2,2]=\{-2,-1,0,1,2\}$, whence $\theta\in\{180^\circ,120^\circ,90^\circ,
60^\circ,0^\circ\}$—the orders $2,3,4,6,1$. The axis $5$ needs the trace $2\cos72^\circ=\tfrac{\sqrt5-1}{2}$—a root of the equation $x^2+x-1=0$, which has *no rational solution*. Therefore the fifth axis is incompatible with the lattice.[^8]

There is no contradiction here with §12.3.2: in $\SO(2,ℚ)$ *both* coordinates $(\cos\theta,\sin\theta)$ are rational, whereas a lattice is preserved by a matrix with a rational *trace* $1+2\cos\theta$—the irrational sine is absorbed by the choice of axis. That is why the rotation *of order 3* lives in $\SO(3,ℚ)$ (the matrix `cyc` is rational) even though $\sin120^\circ$ is irrational.

This is *the same* $\sqrt5$ that in 12.1 ruled out the regular pentagon on $ℤ^2$. The exclusion of the fifth axis, the absence of a rational pentagon, and the irrationality of the golden ratio are three faces of one fact: $x^2+x-1=0$ has no rational root (in Part XI this is the irreducible quadratic tier). The geometry of symmetry, lattice geometry, and the algebraic tier meet at one point.

*Only rotations of orders $1,2,3,4,6$ preserve a lattice: the integer trace ${}=2\cos\theta\in\{-2,…,2\}$; the axis $5$ requires $2\cos72^\circ$—a root of $x^2+x-1$ with no rational solution. The same $\sqrt5$ that rules out the pentagon (12.1).*

## E/R/R Analysis

Let us assemble the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the norm $c^2+s^2=1$, $\norm{q}^2=1$ and its multiplicativity (the two-/four-square identities); the group axioms (`Record Quaternion`); the rule of conjugation $v\mapsto q v\bar q$; the trace rule $2\cos\theta\inℤ$ (the crystallographic restriction) |
| *Roles* (L4) | rotation ${}={}$ role-symmetry; rotation group ${}={}$ role-symmetry ($\SO(2,ℚ)$, $\SU(2)$, quaternions); double cover ${}={}$ role-map $2{:}1$; admissible order ${}={}$ role-restriction ($1,2,3,4,6$) |
| *Elements* (L1${}+{}$P4) | finite data over $ℚ$: rational points $(c,s)$, quaternions $(w,x,y,z)$, matrices of $\SO(3,ℚ)$, elements and orders of finite groups; the continuous $\SO(2)/\SO(3)/\SU(2)$ over $ℝ$ are *not* Elements |

**Well-formedness.** The group is well-formed by the axioms (closure through the multiplicativity of the norm, identity, inverse-as-conjugate; `Record Quaternion` with associativity). The cover is well-formed as a $2{:}1$ map. The restriction on the order is well-formed: an integer trace admits only $\{-2,…,2\}$.

**What it yields.** $\SO(2,ℚ)$ is a group of rational points; $\SU(2)$/quaternions give a record and the double cover $\SU(2)\to\SO(3)$ (0 axioms in the geometric layer); the crystallographic restriction gives the orders $1,2,3,4,6$ and the exclusion of the axis $5$ ($\sqrt5$).

**Diagnosis.** The root error is the reification of *the rotation group as a smooth continuum body*. ToS returns it to its category: the group is a rational structure of symmetries (points ${}+{}$ the rule of the norm), and the smooth Lie group is a role-limit.

**Honest boundaries.** The continuous $\SO(2)/\SO(3)/\SU(2)$ as smooth manifolds, rotations by an arbitrary angle ($\cos\theta,\sin\theta$ irrational), and the analytic exponential are role-limits (the continuum price of Part X). The full map is in 12.6.

*A rotation group is a role-symmetry with a rational bearer, closed under the multiplicative norm; the $2{:}1$ cover and the orders $1,2,3,4,6$ are concrete. The smooth Lie group is a role-limit.*

## Summary and Transition

The chapter has presented the symmetry of geometry as a *rational structure*. The rotations of the plane are the group $\SO(2,ℚ)$ of rational points of the circle, closed by the multiplicativity of the norm (two squares); the rotations of space are quaternions over $ℚ$ with the four-square norm, whose unit elements form $\SU(2)$ and cover $\SO(3)$ *twice* ($q$ and $-q$ are one rotation). The finite symmetries of a lattice are restricted to the orders $1,2,3,4,6$: the fifth axis is ruled out by the same $\sqrt5$ that in 12.1 kept out the regular pentagon—one obstacle, seen in the lattice, in symmetry, and in the algebraic tier.

Next comes the *infinitesimal* side of symmetry. Chapter 12.4 builds the *Lie algebra* $so(3)
\cong su(2)$ over $ℚ$—the tangent structure of the rotation group at the identity, with the bracket $[e_i,e_j]=\varepsilon_{ijk}e_k$ and the Jacobi identity; and the exponential $\exp\colon\mathfrak g\to G$, which needs $\cos/\sin$, will be replaced by the rational *Cayley map*. The double cover of this chapter will receive its infinitesimal shadow there: $so(3)$ and $su(2)$ are one and the same rational algebra.

*A rotation group over $ℚ$ is rational points closed under the multiplicative norm, with the concrete double cover $\SU(2)\to\SO(3)$ and the crystallographic restriction $1,2,3,4,6$. The smooth Lie group is a role-limit; its infinitesimal shadow is the Lie algebra of Chapter 12.4.*

---

[^1]: `RationalRotationGroup.v`: `rotation_compose_closed` (closure through the two squares), `rotation_identity`, `rotation_inverse`; the Cayley map $\bigl(\tfrac{1-t^2}{1+t^2},\tfrac{2t}{1+t^2}\bigr)$ gives an explicit rational family (`cayley_on_circle`—the integer subfamily $t\inℤ$ is machine-checked; the full $t\inℚ$ is a mathematical reading).
[^2]: `RationalRotationGroup.v`: `no_rational_60` ($\nexists y\inℚ:\ (\tfrac12)^2+y^2=1$). `CircleRotation.v`: `sqrt2_rotation_role_limit` ($45^\circ$ is not rational); on the other hand, `rotation_third`/`rotation_quarter`—rotations by $1/3$ and $1/4$ of a turn return after a finite number of steps.
[^3]: The scalar identity is `euler_four_square` (`RationalQuaternions.v`). The group as a record is `SU2Group.v`: `Record Quaternion`, `qmul_assoc`, `qconj_involutive`, `is_unit`, `qnorm_mul` (the norm is multiplicative), and `unit_closed` (the unit quaternions are closed under multiplication).
[^4]: `QuaternionRotation.v` (0 axioms): `rotation_scales_norm` ($\norm{q v\bar q}^2=\norm{q}^2(\norm{q}^2\norm{v}^2)$) and `rotation_preserves_norm` (an isometry for $\norm{q}^2=1$); `conjugate_action_pure` (the image of a pure quaternion is pure). The imaginary units: `qi_squared` ($i^2=-1$), `qij` ($ij=k$), and so on.
[^5]: `QuaternionRotation.v`: `double_cover` ($\mathrm{Heq} ((-q) v \overline{(-q)})  (q v \bar q)$). This is the geometric side of the same $2{:}1$ feature with which, in physics, the spinor sign is connected: a turn by $2\pi$ changes the sign of the quaternion, a turn by $4\pi$ restores it.
[^6]: `QuaternionRotation.v`: `qhalf_cube` ($q^3=-1$), `rotation_order3`. The matrix side is `RationalSO3.v` (0 axioms): `cyc` (the permutation matrix), `cyc_orthogonal`, `cyc_det`${}=1$, `cyc_order3` ($\mathrm{cyc}^3=I$); the family `rot_z` embeds $\SO(2,ℚ)\subset\SO(3,ℚ)$.
[^7]: `NivenRationalCosine.v`: `infinite_order_345`, `orbit_never_returns`—the orbit of $(3,4,5)$ does not return to $(1,0)$ (through a mod-$5$ invariant).
[^8]: `CrystallographicRestriction.v`: the trace recursion `tau_rec`, `order5_forces_golden`, `no_rational_golden` ($\nexists x\inℚ:\ x^2+x-1=0$), `no_rational_order5`, and `realizable_orders` ($1,2,3,4,6$ are realizable). See also `NivenGeneral.v`: $\cos(r\pi)\inℚ\Rightarrow \cos\in\{0,\pm\tfrac12,\pm1\}$.

---

Part: [[12 Geometry Manifolds Lie Groups|Part XII. Geometry, Manifolds, Lie Groups]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/02 Curvature as Angular Defect Manifold as Process|Chapter 2. Curvature as Angular Defect; Manifold as Process]] · [[Library/Branches/Mathematics/Volume/12 Geometry Manifolds Lie Groups/04 Lie Algebra and Infinitesimal Structure|Chapter 4. The Lie Algebra and Infinitesimal Structure]] →
