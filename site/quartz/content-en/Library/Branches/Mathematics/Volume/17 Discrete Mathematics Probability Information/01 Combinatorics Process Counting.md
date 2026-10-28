---
title: "Chapter 1. Combinatorics—Process Counting"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/17 Дискретная математика, вероятность, информация/01 Комбинаторика — процессный счёт.md"
sourceBlob: 870c8e4e5de3dc506a842c530f7294d00ed1b9cd
translated: 2026-10-20
status: draft
---

## Where the Part Stands

After the metatheory (Part XIV) and the parts on computation and on function-as-process (XV–XVI), the volume comes to *applied* mathematics. The three disciplines of the present part—combinatorics, probability theory, and information theory—are united by one property: they are *ontologically concrete*. They work with finite lists and algorithmic processes, require neither the Axiom of Choice nor completed uncountable spaces, and therefore fit into the P4 ontology almost without a gap. This is the most thoroughly 0-axiom part of the volume.

The through-line of the part is *information as the number of acts of distinction*: combinatorics *counts* distinctions, probability *distributes* them, entropy *measures* them. And beneath all three runs the already familiar finitization boundary, which here takes an especially sharp form.

*The flagship of the part (its combinatorial face): finite combinatorics is an
**Element**—it is decidable *by enumeration*; infinite combinatorics is a
**role-limit**.*

The present chapter is about counting. Its thesis: combinatorial quantities are *values of computable processes over finite lists*, not ready numbers over ready sets; and where counting goes off into the infinite, it crosses the finitization boundary onto the role-limit side.

## Counting as a Process

The factorial, the binomial coefficients, and the numbers of combinations are *computable functions*, not “existing” quantities: processes that yield a finite result on a finite input[^1]. A permutation is taken here in the *computational mode*—as a *list without repetitions*; the list is primary, and the group (symmetric) structure appears later as an additional role-organization of these lists. “The set of permutations” is only a mode of considering the list. A combination is also a mode: one and the same finite carrier is counted now as ordered (a list), now as unordered (a multiset-role).

The basic identities confirm the process character of counting. Pascal’s identity is a *step of recursion* (the value of a row of the triangle through the previous one), and the sum of a row gives a power of two:

$$
\sum_{k} \binom{n}{k} = 2^{ n},
$$

and this is a *proved* equality, not an observation[^2]. The symmetry $\binom{n}{k}=\binom{n}{n-k}$ is the identity of *two ways* of counting one and the same thing—exactly operational divisibility: the quantity does not depend on which role (the chosen / the discarded) we count it by.

## Dirichlet’s Principle—the Common Finite Engine

At the foundation of discrete mathematics lies one modest but universal engine—*Dirichlet’s principle* (the “pigeonhole” principle): if $n+1$ objects are distributed among $n$ boxes, some box receives two. In our ontology it is *constructive*: on a finite carrier the coincidence is found *by enumeration*—a pure Element operation, without any recourse to infinity[^3].

What is essential is that this is *the same* engine that works in the pumping of automata and in the Chinese remainder theorem: one finite combinatorial principle manifesting itself in different domains. Its infinite relative (some box holds infinitely many objects) lives already on the role-limit side—we will return to it in the flagship of the chapter.

## Generating Functions as Processes

A generating function is a bridge between counting and analysis, and in our ontology it is a *process*: a sequence of coefficients unfolded on demand, not a completed analytic object (exactly the “function as process” of Part XVI). The brightest example is the Catalan numbers.

The Catalan numbers admit a closed form through binomial coefficients,

$$
C_n = \binom{2n}{n} - \binom{2n}{n+1}
$$

(equivalent to the classical form $C_n = \tfrac{1}{n+1}\binom{2n}{n}$), giving $C_0,… = 1,1,2,5,14,42,132,…$—and this is *computed*, step by step[^4]. But deeper lies the *recurrence* as a process rule,

$$
C_{n+1} = \sum_{i=0}^{n} C_i   C_{n-i},
$$

which corresponds to the *formal* generating equation $C(x) = 1 + x C(x)^2$ (at the level of coefficient processes, not of an analytic equality) and is proved by the *first-return bijection* on Dyck paths—a structural argument, not a formulaic one[^5]. The Motzkin numbers obtain their closed form by the same device[^6].

The lesson is a process one: a generating function does not “exist” somewhere as a whole—it *generates* its coefficients by a rule, and a combinatorial identity is a proved property of this rule, not a coincidence of ready series.

## The Flagship: The Finite Is an Element, the Infinite a Role-Limit

The finitization boundary in combinatorics is seen most sharply in Ramsey theory. The Ramsey number $R(3,3)$ is the least $N$ for which every two-coloring of the edges of the complete graph on $N$ vertices contains a monochromatic triangle.

**$R(3,3)=6$—and this is an Element.** The upper bound is proved *by enumeration*: checking *all* colorings of the $15$ edges of the complete graph on six vertices reveals that a monochromatic triangle *always* arises[^7]. The lower bound is a *witness*: a coloring of the pentagon (the five-vertex cycle) without a monochromatic triangle[^8]. Together they give $R(3,3)=6$—*decidably*, without any completed infinity.

*Finite Ramsey theory is an Element: the number $R(3,3)$ is found by enumeration, on the side of the terminating process.*

**Infinite Ramsey theory is a role-limit.** The infinite Ramsey theorem (in every two-coloring of the infinite complete graph there is an infinite monochromatic subset) requires surveying a *completed* infinite object and is proved through Kőnig’s lemma / compactness—the role-limit side[^9]. Formally, the infinite Ramsey theorem itself is *not* proved here—the classification is fixed: the finite version is an Element (exhaustive search and a witness), the infinite one requires the limit / compactness tier. And here Dirichlet’s principle is at work again—but its *infinite* version, which is what carries counting across the boundary.

*One and the same Ramsey theory is cut by the finitization boundary: the finite number $R(3,3)$ is enumerable (Element), the infinite analogue is a role-limit. One engine (Dirichlet), two sides.*

## E/R/R Analysis: Combinatorics as a System

Let us analyze combinatorics by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rules are the rules of counting: the product of independent choices, the sum of incompatible ones, Pascal’s recursion, the Catalan recurrence $C_{n+1}=\sum C_i C_{n-i}$. Above them stands the common finite engine, Dirichlet’s principle. These rules stand one level above the counted objects and give the quantities.

**Roles (L4).** Quantity is a *role-measure* of a finite carrier. “The set of combinations” and “the set of permutations” are *modes* (different roles) of one list, not different objects (operational divisibility). The generating function plays the role of a *process-thread* that generates the coefficients; on the infinite side counting plays the role of a *limit* (infinite Ramsey).

**Elements (L1 + P4).** The bearers are finite lists: permutations (lists without repetitions), edge colorings, lattice paths. Under P4 it is precisely they that are actual; “the set of all colorings” of a finite graph is finite and enumerable (Element), whereas the infinite complete graph is a role-limit, not a completed object.

**Well-formedness check.** The rules of counting are Rules; quantity-as-measure and the modes are Roles; finite lists are Elements; there are no overlaps. There is no self-application: the rule of counting stands above the lists and is not one of them.

**What the analysis yields.** It shows why discrete mathematics fits so comfortably into P4: its bearers are *finite* and *enumerable* by construction, and quantity is the value of a process, not a property of a completed set. And it names its only boundary: the passage to the *completed* infinite (infinite Ramsey, the infinite Dirichlet principle) is the role-limit side—exactly the same finitization boundary that the whole volume carries, not an exclusion.

Counting is in place; in the next chapter the same finite structures acquire edges—we pass to graph theory: connectivity, cycles, and discrete curvature, still on the 0-axiom Element side.

---

[^1]: The factorial, the binomial coefficients, and Pascal’s identity are formalized as computable functions with proved recurrence properties; machine-checked, 0 axioms.
[^2]: `row_sum_pow2`: the sum of the $n$-th row of Pascal’s triangle equals $2^n$; `binomial_sym`: $\binom{n}{k}=\binom{n}{n-k}$. Machine-checked, 0 axioms.
[^3]: `finite_pigeonhole_engine` (in `CombinatoricsExt`); the same finite engine as the pumping lemma for regular languages (Part XV) and the Chinese remainder theorem (Part XIII). Machine-checked, 0 axioms.
[^4]: `catalan` (in `CombinatoricsExt`) with the concrete values `catalan_0..6` ($1,1,2,5,14,42,132$); zero-indexing is a technical convention of Rocq. Machine-checked, 0 axioms.
[^5]: The recurrence $C_{n+1}=\sum C_i C_{n-i}$ is proved via the “first-return” bijection on lattice paths; André’s reflection gives an independent cross-verification of the closed form. Machine-checked, 0 axioms.
[^6]: $M_n=\sum_k \binom{n}{2k}C_k$ is obtained by F-extraction with a binomial transform and the collapse of the odd terms; machine-checked, 0 axioms.
[^7]: `enum_forces_triangle`: `forallb mono15 (all_vectors 15) = true`—all $2^{15}$ colorings are checked by `vm_compute`; hence `R33_upper`: every coloring yields a triangle. A pure Element operation: decidable by finite exhaustive search, 0 axioms.
[^8]: `R33_lower`: `hasmono5 c5 = false`—an explicit coloring $c_5$ of the pentagon without a monochromatic triangle. Together with the upper bound: `ramsey_3_3` ($R(3,3)=6$) and `ramsey_decidable`.
[^9]: `ramsey_boundary` fixes the cut: finite Ramsey is decidable by enumeration (Element), infinite Ramsey is a role-limit (via König). Machine-checked, 0 axioms: what is asserted is the *cut*, not the infinite theorem.

---

Part: [[17 Discrete Mathematics Probability Information|Part XVII. Discrete Mathematics, Probability, Information]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/16 Function as Process/06 Reification Ladder Number Function Functional|Chapter 6. The Reification Ladder: Number → Function → Functional—Part XVI]] · [[Library/Branches/Mathematics/Volume/17 Discrete Mathematics Probability Information/02 Graph Theory Connectivity Cycles Curvature|Chapter 2. Graph Theory—Connectivity, Cycles, Curvature]] →
