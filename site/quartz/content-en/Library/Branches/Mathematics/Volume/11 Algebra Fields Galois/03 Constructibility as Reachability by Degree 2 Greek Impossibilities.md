---
title: "Chapter 3. Constructibility as Reachability by Degree 2; Greek Impossibilities"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/11 Алгебра, поля, Галуа/03 Конструктивность как достижимость степенью 2; греческие невозможности.md"
sourceBlob: 205fffd768068df962787bda7c41bc9d12b38db5
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapters 11.1 and 11.2 gave two notions. Degree is a *tier*: the height of an extension over $ℚ$ (11.1). The minimal polynomial is a *rule* that tames a process of approximation and fixes the tier; the rational root test decides by divisibility whether the process will close in $ℚ$ (11.2). The present chapter unfolds these two notions into *geometry*.

The millennia-old “Greek impossibilities”—doubling the cube, trisecting the angle, constructing the regular heptagon—are presented by the classical tradition as problems that “could not be solved with compass and straightedge.” ToS redescribes them in the same optics that Part X applied to the strong axioms: this is *not a shortage of tools* but *theorems about the tier*. Compass and straightedge reach exactly the *tier-2 tower*; problems requiring *tier 3* lie outside it *structurally*. Impossibility here is a positive fact about the ceiling of the quadratic tower, not a missing skill.

*Constructibility is the role of reachability by tier 2 (the quadratic tower). The Greek impossibilities are not a shortage of tools but theorems about the tier: they require tier 3, which is structurally outside the quadratic tower.*

## Constructibility as Reachability by Degree 2

What can compass and straightedge do? Intersect lines with lines, lines with circles, circles with circles. Algebraically this means solving linear and *quadratic* equations: each newly constructed segment is obtained by extracting a *square* root from what has already been constructed. Hence each step of a construction raises the tier by exactly a factor of $2$, and the whole accessible domain is a *quadratic tower*

$$
ℚ = K_0 \subset K_1 \subset … \subset K_m, \quad [K_{i+1}:K_i]=2 .
$$

A number is constructible *if and only if* it lies in such a tower; and hence a necessary condition: its degree over $ℚ$ is a *power of two* $2^k$. This is the classical Gauss–Wantzel criterion; ToS reads it as the definition of a *role*: “constructible” means “reachable by tier $2^k$.”[^1]

The positive side: the regular *pentagon* can be constructed. The needed quantity—$2\cos72^\circ=\tfrac{\sqrt5-1}{2}$—lies in $ℚ[\sqrt5]$, that is, at tier 2, reachable by a single quadratic step. It is not rational (it requires $\sqrt5$), but neither is it above tier 2.[^2] The pentagon is the limiting “easy” case: the quadratic tower reaches it.

*Compass and straightedge solve quadratic equations—each step doubles the tier, and the domain is the quadratic tower ($2^k$). “Constructible” ${}={}$ the role of reachability by tier $2^k$. The pentagon ($ℚ[\sqrt5]$, tier 2) is reachable.*

## The Greek Impossibilities as Theorems about the Tier

The three famous problems break against one and the same ceiling: they require *tier 3*, while the quadratic tower gives only tiers of the form $2^k$.

**Doubling the cube (the Delian problem).** The edge of a cube of twice the volume is $\sqrt[3]{2}$—tier 3. Already the first quadratic step does not reach it: it is proved that $\sqrt[3]2\notinℚ[\sqrt2]$.[^3] Any constructible quantity has a degree over $ℚ$ dividing some power of two $2^n$; degree $3$ cannot be such—hence $\sqrt[3]2$ lies outside any quadratic tower. The cube is not doubled.

**Trisecting the angle.** To divide $60^\circ$ into three is to construct $2\cos20^\circ$, a root of the cubic equation $q^3=3q+1$ (from $\cos60^\circ=4\cos^3 20^\circ-3\cos20^\circ$). This cubic *has no rational root*; and a cubic without a rational root is irreducible over $ℚ$, so $2\cos20^\circ$ is tier 3, outside the quadratic tower.[^4] Already $60^\circ$ cannot be trisected with compass and straightedge—hence there is no general procedure for an arbitrary angle (individual angles, say $90^\circ$, can be trisected).

**The regular heptagon.** It requires $2\cos\tfrac{2\pi}{7}$—a root of the cubic equation $q^3=-q^2+2q+1$, again *without a rational root*, again tier 3.[^5] The heptagon cannot be constructed with compass and straightedge.

A single diagnosis[^6]: all three are attempts to close a *cubic* process by *quadratic* means. Impossibility here is not “the Greeks failed to find something” but a *theorem about the tier*: tier 3 is structurally unreachable by the quadratic tower. The very rational root test of 11.2 works here as a geometric exclusion.

*Doubling the cube ($\sqrt[3]2$), trisection ($2\cos20^\circ$), the heptagon
($2\cos\tfrac{2\pi}7$)—all require tier 3 (an irreducible cubic), outside the quadratic tower. Impossibility is a theorem about the tier, not a shortage of tools.*

## The Crystallographic Restriction: The Same Rule in Symmetry

The same type of rule—*an algebraic characteristic rules out a configuration*—governs the symmetries of lattices. A rotation of order $n$ preserving a plane lattice has, in the integer basis of the lattice, a matrix with *trace* $2\cos\tfrac{2\pi}{n}$; but the trace of an integer matrix is an *integer*. Hence $2\cos\tfrac{2\pi}{n}\inℤ$, which holds only for
$n\in\{1,2,3,4,6\}$.[^7] Lattice symmetry has no orders $5$ and $\geq7$—the famous exclusion of the fivefold axis.

And again the witness of the exclusion is the algebra of tier 2. For order $5$ the quantity $2\cos72^\circ=\tfrac{\sqrt5-1}{2}$ is *irrational* (golden), and therefore it cannot be the trace of an integer matrix.[^8] The same $\sqrt5$ that *permitted* the pentagon (tier 2 is reachable with compass) *rules out* the fivefold axis of a lattice (an irrational trace). One and the same algebraic fact—one geometry lets it in, the other rules it out, depending on which rule-criterion is applied (power of two versus integer trace).

*The crystallographic restriction is the same type of rule: the integrality of the trace admits only the orders $\{1,2,3,4,6\}$. Order 5 is ruled out by the irrationality of $2\cos72^\circ$ (golden). The algebraic fact about $\sqrt5$ permits the pentagon and rules out the fivefold axis.*

## E/R/R Analysis

Let us gather the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the criterion of constructibility (each step is degree $2$; constructible $\Leftrightarrow$ tier $2^k$; Gauss–Wantzel); the rational root test (irreducible cubic $\Rightarrow$ tier 3, outside the tower); the rule of integrality of the trace ($2\cos\tfrac{2\pi}{n}\inℤ \Rightarrow n\in\{1,2,3,4,6\}$) |
| *Roles* (L4) | “constructible” ${}={}$ the role of reachability by tier $2^k$; Greek impossibility ${}={}$ a role requiring tier 3 (outside the tower); the order of a symmetry ${}={}$ a role under the rule of integer trace |
| *Elements* (L1${}+{}$P4) | at each stage, finite data: the constructed points/coordinates of a step, the coordinates of the pentagon in $ℚ[\sqrt5]$, the coefficients of the cubics, the integer traces of rotation matrices; “the set of all constructible numbers” as a completed object is *not* an Element |

**Well-formedness.** A construction is well-formed when each step is an extension of degree $2$ (an intersection of lines/circles); an impossibility is well-formed as a theorem about the tier (tier $3$ does not divide $2^k$); the exclusion of a symmetry is well-formed as a violation of the integrality of the trace. Each component belongs to exactly one E/R/R category.

**What it yields.** The pentagon: reachability of tier 2 ($ℚ[\sqrt5]$). Doubling the cube, trisection, the heptagon: nonconstructibility as tier 3 (irreducible cubics). The exclusion of the fivefold axis: the irrationality of $2\cos72^\circ$. A single mechanism: *the algebraic tier (or integrality) admits or rules out geometry*.

**Diagnosis.** The root error is “the Greek problems as unsolved constructions” (a lack of skill). ToS returns them to their category: these are *theorems about the tier*—a rule about the reachable degree, not a deficit of tools.

**Honest boundaries.** The full Gauss–Wantzel criterion (constructible $\Leftrightarrow$ $2^k$) and the theory of constructions in general form are not formalized here—what is formalized are *concrete* reachability (the pentagon in $ℚ[\sqrt5]$) and obstructions (cubics without a rational root; $\sqrt[3]2\notinℚ[\sqrt2]$), as well as the crystallographic restriction. These are concrete shadows of the general criterion, not the criterion itself.

*Constructibility is the role of reachability by tier $2^k$; a Greek impossibility is a theorem about the required tier 3; the crystallographic exclusion is the same rule in symmetry. The substantive core is the algebraic tier as that which permits and rules out geometry.*

## Summary and Transition

The chapter has unfolded degree-as-tier into geometry. Compass and straightedge reach exactly the quadratic tower (tiers $2^k$); the pentagon lies in it, while doubling the cube, trisection, and the heptagon do not, since they require an irreducible cubic (tier 3). The Greek impossibilities have turned out to be not unsolved problems but *theorems about the tier*—a direct consequence of the rational root test of 11.2. The crystallographic restriction has shown the same type of rule in symmetry: the integrality of the trace admits only the orders $\{1,2,3,4,6\}$, and $\sqrt5$, by one and the same fact, permits the pentagon and rules out the fivefold axis.

Next comes Chapter 11.4: from the *exclusions* of tiers to *positive* structures of finite order. Symmetry groups over $ℚ$ (the orders $\{1,2,3,4,6\}$ as crystallographically admissible), norm forms and the Hurwitz tower ($1,2,4,8$—the dimensions with a multiplicative norm), Element-roles of finite order ($i,\omega$), and the finite fields $\mathbb{F}_p$. From “which tier is unreachable” we will pass to “which finite structure is multiplicatively stable.”

*Compass and straightedge ${}={}$ the quadratic tower; constructible ${}={}$ tier $2^k$; the Greek impossibilities ${}={}$ theorems about tier 3; the crystallographic exclusion ${}={}$ the integrality of the trace. The algebraic tier governs geometry—permitting the pentagon and ruling out doubling the cube, trisection, the heptagon, and the fivefold axis. Such is the frame before the passage to finite groups and norm forms.*

---

[^1]: The full Gauss–Wantzel criterion (constructible $\Leftrightarrow$ the degree is $2^k$, via a tower of quadratic extensions) is not formalized in the repository as a general theorem; what is formalized are *concrete* cases of reachability and obstruction (below). This agrees with the discipline of the volume: the theory leads, the repository confirms concrete cases.
[^2]: `stdlib/ConstructiblePolygons.v`: $ℚ[\sqrt5]$ is modeled by pairs, `pentagon_in_Qsqrt5` places the pentagon quantity in $ℚ[\sqrt5]$, and `pentagon_no_rational` ($\lnot\exists q\inℚ,\ q^2+q-1=0$) shows that it is not reachable rationally—exactly tier 2 is needed.
[^3]: `cbrt2_not_in_Qsqrt2` (`stdlib/CubicRoleLimit.v`): no $a+b\sqrt2$ gives $2$ when cubed. `ext_degree_cbrt2_is_3` (`FieldExtension.v`) fixes the degree of the *supporting* polynomial $x^3-2$; the degree $3$ of the number $\sqrt[3]2$ proper is read together with the absence of a rational root (a cubic without one is irreducible; see 11.2).
[^4]: `trisection_no_rational` (`stdlib/AngleTrisection.v`): $\lnot\exists q\inℚ,\ q^3=3q+1$. The chain “a cubic without a rational root $\Rightarrow$ irreducible $\Rightarrow$ tier 3” (see 11.2) gives nonconstructibility.
[^5]: `heptagon_no_rational` (`stdlib/AngleTrisection.v`): $\lnot\exists q\inℚ,\ q^3=-q^2+2q+1$.
[^6]: `greek_impossibilities` (`stdlib/AngleTrisection.v`)—a synthesis: all three impossibilities as facts about the absence of a rational root of the corresponding cubics.
[^7]: `stdlib/CrystallographicRestriction.v`: `crystallographic_restriction` (the condition of integrality of the trace) and `realizable_orders` (exactly $\{1,2,3,4,6\}$).
[^8]: `order5_forces_golden` and `no_rational_order5` (`stdlib/CrystallographicRestriction.v`): order $5$ forces a golden (irrational) value of the trace.

---

Part: [[11 Algebra Fields Galois|Part XI. Algebra, Fields, Galois]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/02 Algebraic Number as Role Limit Minimal Polynomial|Chapter 2. Algebraic Number as Role-Limit; Minimal Polynomial]] · [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/04 Symmetry Groups over Q Norm Forms Finite Fields|Chapter 4. Symmetry Groups over Q; Norm Forms; Finite Fields]] →
