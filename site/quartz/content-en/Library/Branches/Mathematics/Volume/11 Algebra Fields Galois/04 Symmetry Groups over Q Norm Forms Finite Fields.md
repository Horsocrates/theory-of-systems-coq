---
title: "Chapter 4. Symmetry Groups over Q; Norm Forms; Finite Fields"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/11 Алгебра, поля, Галуа/04 Группы симметрии над Q; норменные формы; конечные поля.md"
sourceBlob: 0b21144c0bbf561ee1eb4f1520fce46ccbf5d444
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 11.3 spoke of *exclusions*: tier 3 is unreachable with compass and straightedge, and the fivefold axis is ruled out for a lattice. This is the negative side—what the algebraic tier does *not* let in. The present chapter turns to the *positive* side: which finite structures are *multiplicatively stable*—closed under multiplication, carrying a norm, having finite order.

The through-line of the chapter is *finite order*. The roots of unity $i,\omega$ have finite multiplicative order ($i^4=1$, $\omega^3=1$)—they are Element-roles, not role-limits. The norm form gives the rule $\norm{z\cdot w}=\norm z\cdot\norm w$, and the elements of unit norm form a group—but only in the dimensions $1,2,4,8$ (the Hurwitz tower). The finite field $\FF_p$ has a finite multiplicative group in which every nonzero element has finite order (Fermat’s little theorem). All three subjects concern one thing: *a finite, closed, multiplicatively stable structure*, maximally P4-actual.

*From the exclusions of the tier (11.3) to positive finite structures: roots of unity as Element-roles of finite order, norm forms (Hurwitz $1,2,4,8$), finite fields $\FF_p$. The through-line is finite multiplicative order.*

## Symmetries and Element-Roles of Finite Order

The crystallographically admissible orders $\{1,2,3,4,6\}$ of 11.3 are the orders of the finite *rotation groups* of a lattice: the cyclic $C_n$ for $n\in\{1,2,3,4,6\}$. The rotations themselves are symmetry-roles, and their order is the finite number of steps until the return to the initial state.

Among algebraic numbers, those that play such symmetries are special: they are the *roots of unity*. Here ToS draws the sharp boundary outlined in 11.1. The number $i$ has *finite multiplicative order* ($i^4=1$)—an Element-role of the cyclic group $ℤ_4$; the number $\omega$ ($\omega^3=1$) is an Element-role of $ℤ_3$.[^1] Roots of unity are finite in order but require a finite algebraic extension as their carrier—unlike the rational elements of $\FF_p$. At the same time they *terminate* (a finite cycle, finite data), unlike $\sqrt2,\varphi$—role-limits of nonterminating processes of infinite multiplicative order.

This finite stability is seen in quaternions too. There exists a *rational* unit quaternion with coordinates $(\tfrac12,\tfrac12,\tfrac12,\tfrac12)$ whose norm equals $1$.[^2] In this geometric reading it realizes a rotation of finite order 3. And in the standard (icosahedral) reading, order 5 is rationally *unreachable*: it forces the golden quantity $x^2=x+1$, that is, a role-limit, not a finite rational Element.[^3]
The same demarcation as everywhere in Part XI: finite order is an Element; irrational necessity is a role-limit.

*Roots of unity ($i$: $ℤ_4$, $\omega$: $ℤ_3$) are Element-roles of finite multiplicative order, finitely actual, unlike the role-limits $\sqrt2,\varphi$. Order 3 is rationally realizable (a unit quaternion), order 5 is a role-limit (golden).*

## Norm Forms and the Hurwitz Tower

A norm form is a rule of finite order in another sense: the *multiplicativity of the norm*. If each tuple of coordinates is assigned a norm $\norm{\cdot}$ such that $\norm{z\cdot w}=\norm z\cdot\norm w$, then the product of unit elements is again a unit—the unit sphere is closed under multiplication. ToS reads this as a *role-measure of finite order*: which dimensions admit such a multiplicatively stable multiplication.

The answer is the famous tower $1,2,4,8$, and in each storey multiplicativity is a concrete *identity* over $ℚ$:

- dimension $1$: $(ab)^2=a^2b^2$—the trivial norm;[^4]
- dimension $2$ (complex numbers): the two-square identity (Brahmagupta–Fibonacci), $\norm{z}=a^2+b^2$ is multiplicative;[^5]
- dimension $4$ (quaternions): Euler’s *four*-square identity, $\norm{z}=a^2+b^2+c^2+d^2$;[^6]
- dimension $8$ (octonions): Degen’s *eight*-square identity.[^7]

Multiplicativity immediately implies that the unit elements are *closed* under multiplication. In dimension $4$ (quaternions) they form a *group*; in dimension $8$ (octonions), where multiplication is nonassociative, they form a closed nonassociative structure—a *Moufang loop*, not a group.[^8] The classical Hurwitz theorem states that there are *no other* dimensions with a multiplicative norm over $ℚ$—only $1,2,4,8$.[^9]

An honest reservation about the tiers of formalization. The repository proves that the tower *exists*—the four identities and the closure of the units in $1,2,4,8$. *Exceptionality* (that the dimensions $3,5,6,7,…$ admit no norm) is the content of the Hurwitz theorem proper and is not formalized here as a general theorem; it is cited as a mathematical frame.[^10]

*A norm form is a rule-measure of finite order: the multiplicativity $\norm{z\cdot
w}=\norm z\cdot\norm w$. The identities $1,2,4,8$ (Brahmagupta, Euler, Degen) give the closure of the units; the exceptionality of these dimensions (Hurwitz) is a mathematical frame.*

## Finite Fields $\FF_p${Fp}

The third positive structure is the *finite field*. Take $ℤ/pℤ$ for a prime $p$: $\{0,1,…,p-1\}$ with addition and multiplication modulo $p$. This is a *field*—every nonzero element is invertible. ToS reads $\FF_p$ as a *role-field of finite order*: the whole structure is finite, actual, without any role-limit.

Invertibility is not an abstract postulate but a *computable* fact. For $p=5$ and $p=7$ the inverses are presented by an explicit function, and it is checked that every nonzero element has an inverse.[^11]

Finite order is seen in the multiplicative group $\FF_p^{\times}$. Classically it is cyclic of order $p-1$; the formal layer, however, proves a more modest but sufficient fact: every nonzero element returns to one in a number of steps dividing $p-1$—this is *Fermat’s little theorem*. For $p=5$ this is $a^4\equiv1$, for $p=7$, $a^6\equiv1$.[^12] This closes the gap that an earlier layer of Part XI honestly noted:
$\FF_p$ as a field is now built.

An honest reservation about the tiers: the “field” here is represented through the key field role—*the invertibility of the nonzero elements* (and the absence of an inverse for zero); the full set of field axioms and the general $\FF_p$ for an arbitrary prime are not formalized as a theorem. What is formalized are concrete primes ($p=5,7$) with explicit inverses and Fermat—samples of the same finite computable structure.

*$\FF_p=ℤ/pℤ$ is a role-field of finite order: the nonzero elements are invertible (built for $p=5,7$), and every nonzero element has finite order dividing $p-1$ (Fermat; the cyclicity of $\FF_p^{\times}$ is a classical frame). A finite, actual structure without a role-limit.*

## E/R/R Analysis

Let us gather the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the multiplicativity of the norm as a rule of finite order (the identities $1,2,4,8$); the group axioms of rotations; arithmetic modulo $p$ and invertibility as the rule of a field |
| *Roles* (L4) | norm form ${}={}$ role-measure of finite order; $i,\omega$ ${}={}$ Element-roles of finite order ($ℤ_4,ℤ_3$); $\FF_p$ ${}={}$ role-field of finite order; order of a symmetry ${}={}$ a role ($C_n$, $n\in\{1,2,3,4,6\}$) |
| *Elements* (L1${}+{}$P4) | finite data: the coordinates of quaternions/octonions in $ℚ$, the identities of squares, the elements $\{0,…,p-1\}$ and their inverses, roots of unity; “all dimensions with a norm” / “all $\FF_p$” as a completed object is *not* an Element |

**Well-formedness.** A structure is well-formed when it is closed and finite: the unit sphere is closed under multiplication (the multiplicativity of the norm); $\FF_p$ has inverses for all nonzero elements; a rotation group returns to the identity in a finite number of steps. Finite order is the common criterion of well-formedness.

**What it yields.** Roots of unity are finite Element-roles ($i^4=1$, $\omega^3=1$). Norm forms give the closure of the units in $1,2,4,8$ (Brahmagupta/Euler/Degen; in dimension 8 this is a Moufang loop). $\FF_p$: the invertibility of the nonzero elements and Fermat for $p=5,7$ (the cyclicity of $\FF_p^\times$ is a classical frame). All are finitely actual and multiplicatively stable.

**Diagnosis.** Unlike 11.3 (exclusions of the tier), the error here would be a different one—to take norm forms or $\FF_p$ for *infinite* objects. ToS stresses their *finite order*: these are the most “earthly” algebraic roles—terminating and closed.

**Honest boundaries.** The exceptionality of the Hurwitz tower (*only* $1,2,4,8$) and the general $\FF_p$ for all primes are mathematical frames; what is formalized are *positive* samples (the identities $1,2,4,8$ and closure; $\FF_5,\FF_7$ with Fermat). The roots of unity $i,\omega$ are taken as roles of finite order, developing 11.1.

*Finite multiplicative order is the common thread: roots of unity (Element-roles), norm forms ($1,2,4,8$), $\FF_p$ (the invertibility of the nonzero elements and Fermat for $p=5,7$). The substantive core is a finite, closed, multiplicatively stable structure, not an infinite object.*

## Summary and Transition

The chapter has gathered the positive side of algebra over $ℚ$—finite multiplicatively stable structures. The roots of unity $i,\omega$ have turned out to be Element-roles of finite order ($ℤ_4,ℤ_3$), in sharp contrast with the role-limits $\sqrt2,\varphi$. Norm forms have given the Hurwitz tower $1,2,4,8$ with concrete identities (Brahmagupta, Euler, Degen) and the closure of the units. The finite fields $\FF_p$ ($p=5,7$ built explicitly) have shown a finite multiplicative group with Fermat’s little theorem—closing the previously noted gap “there is no $\FF_p$.”

Next comes Chapter 11.5, the center of Part XI: the *Galois group*. The finite symmetries of this chapter will become there the symmetries of *roots*: for $ℚ[\sqrt2,\sqrt3]$ a genuine Galois correspondence will be presented (four automorphisms, the Klein group $V_4$, fixed subfields), and then the unsolvability of the quintic through a genuine engine of the derived series. From finite structures we will pass to finite *symmetries* organizing the roots of an equation.

*Roots of unity are finite Element-roles; norm forms are the tower $1,2,4,8$; $\FF_p$ is the invertibility of the nonzero elements and Fermat (for $p=5,7$). Finite order is the thread of positive algebra. Such is the frame before the central chapter on the Galois group and the symmetries of roots.*

---

[^1]: Here $i,\omega$ are taken as the standard roles of finite order, developing 11.1; their carrier fields are built in a separate layer ($ℚ[i]$—e.g., `stdlib/CliffordField.v`; $\omega$ lives in $ℚ(\sqrt{-3})$). The machine-confirmed positive layer of *this* chapter is quaternions, the norm identities, and finite fields (below).
[^2]: `order3_rational_quaternion` (`stdlib/RationalQuaternions.v`) formally proves $\mathrm{qnorm4}(\tfrac12,\tfrac12,\tfrac12,\tfrac12)=1$—rationality and unit norm; the reading as a rotation of order 3 ($120^\circ$) uses the standard interpretation of unit quaternions as the double cover of $SO(3)$.
[^3]: `order5_rotation_role_limit` (ibid.) formally proves the golden obstruction $\lnot\exists q\inℚ,\ q^2=q+1$—an echo of the crystallographic exclusion of the fivefold axis from 11.3; the full geometric classification of rational quaternions of order 5 is not built here.
[^4]: `one_square` (`stdlib/HurwitzTower.v`).
[^5]: `two_square` (ibid.).
[^6]: `four_square` and `euler_four_square` (`HurwitzTower.v`, `RationalQuaternions.v`).
[^7]: `eight_square` (`HurwitzTower.v`).
[^8]: `unit_quaternion_closed` (`RationalQuaternions.v`), `unit_octonion_closed` (`HurwitzTower.v`): the product of units is again a unit. `HurwitzTower.v` itself notes that the octonion unit structure is a Moufang loop, not a group.
[^9]: The bridge to rotation groups: `foundation/NormFormTowerBridge.v` (5 Qed, 0 axioms)—the dimension-2 storey of the norm tower *is* the rational circle $\mathrm{SO}(2,ℚ)$ (`n2_rung_is_SO2Q_closure`), with the concrete triple $3{:}4{:}5$ ($(\tfrac35)^2+(\tfrac45)^2=1$, `unit_345_n2`) and the closure of the unit quaternions of storey 4 (`unit_quaternion_closed`). The algebraic *gate* for landing on this circle is `foundation/GapPythagoreanBoundary.v` (11 Qed, 0 axioms): the rationality of an eigenvalue $\Leftrightarrow$ the Pythagorean property $\Leftrightarrow$ the discriminant is a perfect square (`gap_element_iff_pythagorean`, `gap_element_iff_disc_square`), decidable over $ℤ$ (`gap_element_decidable_Z`); the same triple $3{:}4{:}5$ (`bcs_345_element`). Machine-checked, 0 axioms.
[^10]: That is, the formal layer is *positive* (the identities $1,2,4,8$ and closure); the impossibility of the other dimensions is a classical result, not reformalized.
[^11]: `F5_field` ($\mathtt{has_inverses}\ 5\ \mathtt{inv5}$) and `F7_field` ($\mathtt{has_inverses}\ 7\ \mathtt{inv7}$) in `algebra/FiniteFieldFp.v` (0 axioms): the inverses are given by the functions `inv5`, `inv7`, and zero has no inverse (`zero_no_inverse_F7`).
[^12]: `fermat5` ($a^4\bmod5=1$ for $1\le a\le4$) and `fermat7` ($a^6\bmod7=1$ for $1\le a\le6$) in `FiniteFieldFp.v`. Thus every nonzero element has finite order dividing $p-1$.

---

Part: [[11 Algebra Fields Galois|Part XI. Algebra, Fields, Galois]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/03 Constructibility as Reachability by Degree 2 Greek Impossibilities|Chapter 3. Constructibility as Reachability by Degree 2; Greek Impossibilities]] · [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/05 Galois Group Concrete Correspondence and Unsolvability of the Quintic|Chapter 5. Galois Group: Concrete Correspondence and Unsolvability of the Quintic]] →
